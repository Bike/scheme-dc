(defpackage #:scheme-vm
  (:use #:cl)
  (:export #:igo #:set-link #:make-variable-frame
           #:closure-alloc #:closure-ip #:closure-vec
           #:rotatef-closure))

(in-package #:scheme-vm)

(defclass frame ()
  ((%next :initarg :next :reader next :type (or frame null))))

(defclass variable-frame (frame)
  ((%vals :initarg :vals :reader vals :type simple-vector)))

(defun make-variable-frame (nvals next)
  (check-type nvals (integer 0))
  (check-type next frame)
  (make-instance 'variable-frame
    :vals (make-array nvals) :next next))

(defun frame-value (frame i)
  (svref (vals frame) i))
(defun (setf frame-value) (value frame i)
  (setf (svref (vals frame) i) value))

(defclass closure ()
  ((%ip :initarg :ip :reader closure-ip)
   (%vec :initarg :vec :reader closure-vector)))

(defun closure (ip size)
  (make-instance 'closure :ip ip :vec (make-array size)))

(defun interpret (code)
  (loop with frame = nil ; holds frame
        with accum = nil ; general purpose + argument
        with link = nil ; holds return address upon entry
        with closure = nil ; holds closure vector
        for ip = 0 then (1+ ip)
        for (opcode . data) = (svref code ip)
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
                (setf ip (1- link))))
             ((set-link)
              (destructuring-bind (link-ip) data
                (setf link link-ip)))
             ((make-variable-frame)
              (destructuring-bind (nvals) data
                (setf accum (make-variable-frame nvals frame))))
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
              (destructuring-bind () data
                (setf frame accum)))
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
             ((rotatef-closure)
              (destructuring-bind (i) data
                (rotatef closure (frame-value frame i)))))))