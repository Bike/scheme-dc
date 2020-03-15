(defpackage #:scheme-vm
  (:use #:cl)
  (:export #:interpret)
  (:export #:*trace* #:display-code)
  (:export #:igo #:set-link #:save-link #:restore-link
           #:closure-alloc #:closure-ip #:closure-vec
           #:closure-get #:closure-set
           #:save-closure #:load-closure #:rotatef-closure
           #:alloc-escape #:escape-frame #:escape-ip
           #:slice-continuation #:extend
           #:save-frame #:load-frame))

(in-package #:scheme-vm)

(defclass frame ()
  ((%next :initarg :next :accessor next :type (or frame null))))

(defclass variable-frame (frame)
  ((%vals :initarg :vals :reader vals :type simple-vector)))

(defun make-variable-frame (nvals next)
  (check-type nvals (integer 0))
  (check-type next (or frame null))
  (make-instance 'variable-frame
    :vals (make-array nvals) :next next))

(defun copy-variable-frame (frame)
  (make-instance 'variable-frame :vals (copy-seq (vals frame)) :next nil))

(defun frame-value (frame i)
  (svref (vals frame) i))
(defun (setf frame-value) (value frame i)
  (setf (svref (vals frame) i) value))

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

(defun copy-slice (shallow deep)
  (assert (typep shallow 'variable-frame))
  (assert (typep deep 'variable-frame))
  (when (eq shallow deep)
    (let ((copy (copy-variable-frame shallow)))
      (return-from copy-slice (values copy copy))))
  (loop with shallow-copy = (copy-variable-frame shallow)
        with frame = (next shallow) with prev = shallow-copy
        if (eq frame deep)
          do (return (values shallow-copy prev))
        when (null frame)
          do (error "Cannot copy slice from exited escape")
        do (let ((new (copy-variable-frame frame)))
             (psetf frame (next frame)
                    (next prev) new
                    prev new))))

(defvar *trace* nil)

(defun nice-instruction-print (ip opcode args)
  (format t "~&~d: ~a~{~^ ~a~}~%" ip opcode args))

(defun display-code (code)
  (loop for (opcode . args) across code
        for i from 0
        do (nice-instruction-print i opcode args)))

(defun interpret (code &optional arg)
  (declare (optimize debug))
  (loop with frame = nil ; holds frame
        with accum = arg ; general purpose + argument
        with link = nil ; holds return address upon entry
        with closure = nil ; holds closure vector
        for ip = 0 then (1+ ip)
        for (opcode . data) = (svref code ip)
        when *trace*
          do (nice-instruction-print ip opcode data)
        do (ecase opcode
             ((quote)
              (destructuring-bind (object) data
                (setf accum object)))
             ((go)
              (destructuring-bind (new-ip) data
                (setf ip (1- new-ip))))
             ((igo)
              (destructuring-bind (i) data
                (setf ip (1- (frame-value frame i)))))
             ((return)
              (destructuring-bind () data
                (if (null link)
                    (return accum)
                    (setf ip (1- link)))))
             ((funcall)
              (destructuring-bind (function &rest constants) data
                (setf accum (apply function accum constants))))
             ((set-link)
              (destructuring-bind (link-ip) data
                (setf link link-ip)))
             ((save-link)
              (destructuring-bind (i) data
                (setf (frame-value frame i) link)))
             ((restore-link)
              (destructuring-bind (i) data
                (setf link (frame-value frame i))))
             ;; for argument parsing
             ((car)
              (unless (consp accum) (error "Bad CAR"))
              (destructuring-bind (i) data
                (setf (frame-value frame i) (car accum))))
             ((cdr)
              (unless (consp accum) (error "Bad CDR"))
              (destructuring-bind () data
                (setf accum (cdr accum))))
             ;; and for calls...
             ((cons)
              (destructuring-bind (i) data
                (setf (frame-value frame i)
                      (cons accum (frame-value frame i)))))
             ;; ok normal stuff again
             ((push)
              (destructuring-bind (nvals) data
                (setf frame (make-variable-frame nvals frame))))
             ((pop)
              (destructuring-bind () data
                (if (null frame)
                    (error "No frame to pop")
                    (setf frame (next frame)))))
             ((get)
              (destructuring-bind (i) data
                (setf accum (frame-value frame i))))
             ((set)
              (destructuring-bind (i) data
                (setf (frame-value frame i) accum)))
             ((getf) ; get frame
              (destructuring-bind (framei datai) data
                (let ((f (frame-value frame framei)))
                  (setf accum (frame-value f datai)))))
             ((setf) ; set frame
              (destructuring-bind (framei datai) data
                (let ((f (frame-value frame framei)))
                  (setf (frame-value f datai) accum))))
             ;; closures: a pair of an IP and a vector
             ((closure-alloc)
              (destructuring-bind (function-start size) data
                (setf accum (closure function-start size))))
             ((closure-ip)
              (destructuring-bind (i) data
                (setf (frame-value frame i) (closure-ip accum))))
             ((closure-vec)
              (destructuring-bind (i) data
                (setf (frame-value frame i) (closure-vector accum))))
             ((closure-get)
              (destructuring-bind (vector-index) data
                (setf accum (svref closure vector-index))))
             ((closure-set)
              (destructuring-bind (cindex vector-index) data
                (let* ((closure (frame-value frame cindex))
                       (vector (closure-vector closure)))
                  (setf (svref vector vector-index) accum))))
             ((save-closure)
              (destructuring-bind (cindex) data
                (setf (frame-value frame cindex) closure)))
             ((load-closure)
              (destructuring-bind (cindex) data
                (setf closure (frame-value frame cindex))))
             ((rotatef-closure)
              (destructuring-bind (i) data
                (rotatef closure (frame-value frame i))))
             ;; escapes: a pair of an IP and a frame
             ;; NOTE/TODO?: With flow analysis, the IP can often
             ;; sometimes be known statically, but we don't
             ;; optimize this.
             ((alloc-escape)
              (destructuring-bind (next-ip ripi rframei) data
                (setf accum (make-escape next-ip frame ripi rframei))))
             ((escape-frame)
              (destructuring-bind (i) data
                (setf frame (escape-frame (frame-value frame i)))))
             ((escape-ip)
              (destructuring-bind (i) data
                (setf link (escape-ip (frame-value frame i)))))
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
                (multiple-value-bind (shallow deep)
                    (copy-slice frame (escape-frame accum))
                  (setf accum (continuation next-ip shallow deep
                                            (ripi accum)
                                            (rframei accum))))))
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
             ;; we use these for let/dc but in a real impl
             ;; they'd be used in the implementations of
             ;; escape and extend and stuff.
             ((save-frame)
              (destructuring-bind (i) data
                (setf (frame-value frame i) frame)))
             ((load-frame)
              (destructuring-bind (i) data
                (setf frame (frame-value frame i)))))))
