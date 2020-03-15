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
   (%shallow :initarg :shallow :reader continuation-shallow)
   (%deep :initarg :deep :reader continuation-deep)
   (%ripi :initarg :ripi :reader ripi)
   (%rframei :initarg :rframei :reader rframei)))

(defun continuation (ip shallow deep ripi rframei)
  (make-instance 'continuation :ip ip :shallow shallow :deep deep
                 :rframei rframei :ripi ripi))

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
               #+(or)
               ((slice-continuation)
                ;; read an escape from accum.
                ;; make a slice with the given IP and all frames up to escape.
                ;; since at the moment frames contain their next link,
                ;; we only need to actually store the most recent and least
                ;; recent frames (and doing the latter is an optimization)
                (destructuring-bind (next-ip) data
                  (multiple-value-bind (shallow deep)
                      (copy-slice frame (escape-frame accum))
                    (setf accum (continuation next-ip shallow deep
                                              (ripi accum)
                                              (rframei accum))))))
               #+(or)
               ((extend)
                ;; Throw a ton more frames on the stack.
                (destructuring-bind (next-ip i) data
                  (let* ((continuation (frame-value frame i))
                         (dest-ip (continuation-ip continuation))
                         (dest-shallow (continuation-shallow continuation))
                         (dest-deep (continuation-deep continuation))
                         (ripi (ripi continuation))
                         (rframei (rframei continuation)))
                    ;; Fix up the end frame so it returns to here.
                    (setf (frame-value dest-deep ripi) next-ip
                          (frame-value dest-deep rframei) frame
                          frame dest-shallow
                          ip (1- dest-ip)))))
               ;; misc
               ((quote) ; %accum = $object
                (destructuring-bind (object) data
                  (setf accum object)))
               ((funcall) ; %accum = cl_apply[$function, %accum, $...]
                (destructuring-bind (function &rest constants) data
                  (setf accum (apply function accum constants))))))))
