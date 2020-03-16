(defpackage #:scheme-vm
  (:use #:cl)
  (:export #:interpret)
  (:export #:*trace* #:display-code)
  (:export #:igo #:set-link #:save-link #:load-link
           #:closure-alloc #:closure-ip #:closure-vec
           #:closure-get #:closure-set
           #:save-closure #:load-closure #:rotatef-closure
           #:alloc-escape #:escape-frame #:escape-ip
           #:slice-continuation #:extend
           #:save-frame #:load-frame))

(in-package #:scheme-vm)

(defclass closure ()
  ((%ip :initarg :ip :reader closure-ip)
   (%vec :initarg :vec :reader closure-vector :type simple-vector)))

(defun closure (ip size)
  (make-instance 'closure :ip ip :vec (make-array size)))

(defclass escape ()
  ((%ip :initarg :ip :reader escape-ip)
   (%frame :initarg :frame :reader escape-frame)
   ;; Indices into the destination frame used with delimited continuations.
   (%ripi :initarg :ripi :reader ripi)
   (%rframei :initarg :rframei :reader rframei)))

(defun make-escape (ip frame ripi rframei)
  (make-instance 'escape :ip ip :frame frame
                 :rframei rframei :ripi ripi))

(defclass continuation ()
  ((%ip :initarg :ip :reader continuation-ip)
   (%stack :initarg :stack :reader continuation-stack)
   ;; address, within stack, of the deepest frame.
   ;; could be obtained by iteration but that's boring.
   (%deep :initarg :deep :reader continuation-deep)
   ;; frame-relative index of spot containing IP let/ec will jump to.
   (%ripi :initarg :ripi :reader ripi)
   ;; frame-relative index of spot containing SP let/ec will restore.
   (%rframei :initarg :rframei :reader rframei)))

(defun continuation (ip stack deep ripi rframei)
  (make-instance 'continuation :ip ip :stack stack :deep deep
                 :rframei rframei :ripi ripi))

;; For debug: split up the frames
(defun display-stack (stack top)
  (loop for prev-sp = top then sp
        for sp = (aref stack prev-sp)
        until (zerop prev-sp)
        do (format t "~&~d: ~a~%"
                   sp (subseq stack (1+ sp) (1+ prev-sp)))))

;;; Edit all the saved stack pointers to point to
;;; the correct places by incrementing them by the offset.
(defun recontextualize-stack (cstack offset limit)
  (loop with addr-of-sp = (1- (length cstack))
        until (= limit addr-of-sp)
        do (setf addr-of-sp
                 (incf (aref cstack addr-of-sp) offset)))
  cstack)

(defun copy-slice (stack shallow deep)
  ;; (display-stack stack shallow)
  ;; Remember the stack frame layout:
  ;; The previous SP is stored at SP. So we get deep's previous SP.
  (let* ((prev-sp (aref stack deep))
         (start (1+ prev-sp))
         (end (1+ shallow)))
    (values
     (recontextualize-stack (subseq stack start end)
                            ;; limit is -1 because it's before the
                            ;; beginning of the stack slice.
                            ;; this value will be altered, anyway.
                            (- start) -1)
     (- deep start))))

(defvar *trace* nil)

(defun nice-instruction-print (ip opcode args)
  (format t "~&~d: ~a~{~^ ~a~}~%" ip opcode args))

(defun display-code (code)
  (loop for (opcode . args) across code
        for i from 0
        do (nice-instruction-print i opcode args)))

(defun interpret (code &key arg (stack (make-array 200)))
  (loop with sp = 0 ; stack pointer
        with accum = arg ; general purpose, argument, return value
        with link = nil ; return address in a call
        with closure = nil ; closure vector
        for ip = 0 then (1+ ip)
        for (opcode . data) = (svref code ip)
        when *trace*
          do (nice-instruction-print ip opcode data)
        do (flet ((fv (i) ; frame value
                    (svref stack (- sp i)))
                  ((setf fv) (v i)
                    (setf (svref stack (- sp i)) v)))
             (declare (inline fv (setf fv)))
             (ecase opcode
               ;; registers and the stack
               ((get) ; %accum = (%sp,-$i)
                (destructuring-bind (i) data
                  (setf accum (fv i))))
               ((set) ; (%sp,-$i) = %accum
                (destructuring-bind (i) data
                  (setf (fv i) accum)))
               ((load-closure) ; closure = (%sp,-$cindex)
                (destructuring-bind (cindex) data
                  (setf closure (fv cindex))))
               ((save-closure) ; (%sp,-$cindex) = closure
                (destructuring-bind (cindex) data
                  (setf (fv cindex) closure)))
               ((rotatef-closure) ; swap em (this is me being lazy)
                (destructuring-bind (cindex) data
                  (rotatef closure (fv cindex))))
               ((save-link) ; (%sp,-$i) = %link
                (destructuring-bind (i) data
                  (setf (fv i) link)))
               ((load-link) ; %link = (%sp,-$i)
                (destructuring-bind (i) data
                  (setf link (fv i))))
               ((save-frame) ; (%sp,-$i) = %sp
                (destructuring-bind (i) data
                  (setf (fv i) sp)))
               ((load-frame) ; %sp = (%sp,-$i)
                (destructuring-bind (i) data
                  (setf sp (fv i))))
               ((push) ; %sp = %sp + $nvals; (%sp) = %sp - nvals
                ;; i.e., increments the stack pointer
                ;; and puts the old stack pointer at ($sp)
                (destructuring-bind (nvals) data
                  (let ((prev sp))
                    (incf sp nvals)
                    (setf (fv 0) prev))))
               ((pop); %sp = (%sp)
                (destructuring-bind () data
                  (setf sp (fv 0))))
               ;; control flow (messing with ip)
               ;; These subtract one because the loop adds one.
               ;; We could store the IP pre subtracted, but then
               ;; it's more confusing to read.
               ((go) ; %ip = $i
                (destructuring-bind (new-ip) data
                  (setf ip (1- new-ip))))
               ((igo); %ip = (%sp,-$i) "indirect go"
                (destructuring-bind (i) data
                  (setf ip (1- (fv i)))))
               ((return) ; %ip = %link, or terminate program
                (destructuring-bind () data
                  (if (null link)
                      (return accum)
                      (setf ip (1- link)))))
               ((set-link) ; %link = $i FIXME: remove this, use quote load-link
                (destructuring-bind (link-ip) data
                  (setf link link-ip)))
               ;; lists - mostly for argument production and parsing
               ((car) ; (%sp,-$i) = car[%accum]
                (unless (consp accum) (error "Bad CAR"))
                (destructuring-bind (i) data
                  (setf (fv i) (car accum))))
               ((cdr) ; %accum = cdr[%accum]
                (unless (consp accum) (error "Bad CDR"))
                (destructuring-bind () data
                  (setf accum (cdr accum))))
               ((cons) ; (%sp,-$i) = cons[%accum, (%sp,-$i)]
                (destructuring-bind (i) data
                  (setf (fv i)
                        (cons accum (fv i)))))
               ;; closures: a pair of an IP and a vector
               ((closure-alloc) ; %accum = closure_alloc[$ip, $size]
                (destructuring-bind (function-start size) data
                  (setf accum (closure function-start size))))
               ((closure-ip) ; (%sp,-$i) = closure_ip[%accum]
                (destructuring-bind (i) data
                  (setf (fv i) (closure-ip accum))))
               ((closure-vec) ; (%sp,-$i) = closure_vector[%accum]
                (destructuring-bind (i) data
                  (setf (fv i) (closure-vector accum))))
               ((closure-get) ; %accum = svref[%closure, $vector_index]
                (destructuring-bind (vector-index) data
                  (setf accum (svref closure vector-index))))
               ((closure-set)
                ;; svref[closure_vector(%sp,-$i), $vector_index] = %accum
                (destructuring-bind (cindex vector-index) data
                  (let* ((closure (fv cindex))
                         (vector (closure-vector closure)))
                    (setf (svref vector vector-index) accum))))
               ;; escapes: a pair of an IP and a frame, plus continuation info
               ;; NOTE/TODO?: With flow analysis, we could cut out various
               ;; parts: the frame if it's in the same function, the IP if
               ;; the flow is tracked, and the ripi and rframei if we know
               ;; it's not the basis for a let/dc.
               ((alloc-escape)
                (destructuring-bind (next-ip ripi rframei) data
                  (setf accum (make-escape next-ip sp ripi rframei))))
               ((escape-frame)
                (destructuring-bind (i) data
                  (setf sp (escape-frame (fv i)))))
               ((escape-ip)
                (destructuring-bind (i) data
                  (setf link (escape-ip (fv i)))))
               ;; delimited continuations: An IP and a list of frames.
               ;; NOTE that in the more realistic case, these instructions
               ;; would be functions in the runtime probably.
               ((slice-continuation)
                ;; read an escape from accum.
                ;; make a slice with the given IP and all frames up to escape.
                ;; since at the moment frames contain their next link,
                ;; we only need to actually store the most recent and least
                ;; recent frames (and doing the latter is an optimization)
                (destructuring-bind (next-ip) data
                  (multiple-value-bind (slice deep)
                      (copy-slice stack sp (escape-frame accum))
                    (setf accum (continuation next-ip slice deep
                                              (ripi accum)
                                              (rframei accum))))))
               ((extend)
                ;; Throw a ton more frames on the stack.
                (destructuring-bind (next-ip i) data
                  (let* ((continuation (fv i))
                         (cstack (continuation-stack continuation))
                         (deep (continuation-deep continuation))
                         (ripi (ripi continuation))
                         (rframei (rframei continuation)))
                    ;; Append the saved slice onto the stack.
                    (replace stack cstack :start1 sp)
                    ;; Fix the let/ec next-sp and next-ip.
                    ;; NOTE that we do this AFTER copying the thing,
                    ;; in case multiple threads could use the same
                    ;; delimited continuation. (Not that this system
                    ;; actually has threads, but I might as well do
                    ;; this right.)
                    (setf (svref stack (+ sp deep (- ripi))) next-ip
                          (svref stack (+ sp deep (- rframei))) sp)
                    ;; Fix up.
                    (recontextualize-stack stack sp (1- sp))
                    ;; Set SP
                    (setf sp (+ sp (length cstack) -1)))))
               ;; misc
               ((quote) ; %accum = $object
                (destructuring-bind (object) data
                  (setf accum object)))
               ((funcall) ; %accum = cl_apply[$function, %accum, $...]
                (destructuring-bind (function &rest constants) data
                  (setf accum (apply function accum constants))))))))
