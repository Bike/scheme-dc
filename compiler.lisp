(in-package #:scheme)

(defun gen (code opcode &rest data)
  (vector-push-extend (cons opcode data) code))

(defun next-ip (code) (length code))

(defun fixup (code to-fix new-val)
  (setf (second (aref code to-fix)) new-val))

(defvar *fixups*)
(defvar *nvals*)

(defun new-value-index ()
  (prog1 *nvals* (incf *nvals*)))

(defun compile-function (params body env)
  (let* ((code (make-array 0 :fill-pointer 0 :adjustable t))
         (*fixups* nil)
         (*nvals* 0)
         (to-fix (gen code 'scheme-vm:make-variable-frame 0))
         (env (append (gen-arg-parse params code) env)))
    ;; Get goin
    (compile-form body env code)
    (gen code 'return)
    (fixup code to-fix *nvals*) ; frame size now known
    (values code *fixups*)))

(defun gen-arg-parse (params code)
  (etypecase params
    (null nil) ; todo: check arg count
    (symbol
     (let ((new-index (new-value-index)))
       (gen code 'set new-index)
       (list (list params :local new-index))))
    (cons
     (unless (symbolp (car params))
       (error "TODO, maybe, later"))
     (let ((new-index (new-value-index)))
       (gen code 'car new-index)
       (gen code 'cdr)
       (list* (list (car params) :local new-index)
              (gen-arg-parse (cdr params) code))))))

(defun compile-form (form env code)
  (typecase form
    (null (gen code 'quote form))
    (symbol
     (let ((pair (assoc form env)))
       (if pair
           (destructuring-bind (location i) (cdr pair)
             (ecase location
               ((:local) (gen code 'get i))
               ((:closure) (gen code 'getf i))))
           (error "Unbound variable: ~a" form))))
    (cons
     (case (first form)
       ((quote)
        (destructuring-bind (object) (rest form)
          (gen code 'quote object)))
       ((progn)
        (if (null (rest form))
            (gen code 'quote nil)
            (loop for subform in (rest form)
                  do (compile-form subform env code))))
       ((lambda)
        (destructuring-bind (params body) (rest form)
          (let ((free (free body (flatten params))))
            (unless (null free) (error "no closures yet"))
            (let ((cenv (remove :local env :key #'second)))
              (multiple-value-bind (fcode ffixups)
                  (compile-function params body cenv)
                (let ((to-fix
                        (gen code 'scheme-vm:closure-alloc
                             0 0)))
                  (push (list* fcode to-fix ffixups) *fixups*)))))))
       (otherwise
        (destructuring-bind (function &rest argforms) form
          (gen-call function argforms env code)))))
    (t (gen code 'quote form))))

(defun flatten (params)
  (etypecase params
    (null nil)
    (symbol (list params))
    (cons (append (flatten (car params)) (flatten (cdr params))))))

(defun free (form bound)
  (typecase form
    (null nil)
    (symbol (if (member form bound) nil (list form)))
    (cons
     (case (first form)
       ((quote) nil)
       ((lambda)
        (destructuring-bind (params body) (rest form)
          (free body (append (flatten params) bound))))
       ((if)
        (destructuring-bind (test then else) (rest form)
          (append (free test bound)
                  (free then bound) (free else bound))))
       ((progn)
        (loop for subform in (rest form)
              appending (free subform bound)))
       ((let/ec)
        (destructuring-bind (var body) (rest form)
          (free body (list* var bound))))
       ((escape)
        (destructuring-bind (escape body) (rest form)
          (append (free escape bound) (free body bound))))
       ((let/dc)
        (destructuring-bind ((var escape) body) (rest form)
          (append (free escape bound)
                  (free body (list* var bound)))))
       ((extend)
        (destructuring-bind (continuation body) (rest form)
          (append (free continuation bound) (free body bound))))
       (t (loop for subform in form
                appending (free subform bound)))))
    (t nil)))

(defun gen-call (fform aforms env code)
  (let ((findex (new-value-index)) ; function and then ip go here
        ;; note: nested calls could use the same position for this.
        (cindex (new-value-index)) ; old closure vector
        (aindex (new-value-index))) ; arguments
    (compile-form fform env code) ; accum = <function>
    (gen code 'set findex) ; [findex] = accum
    ;; Now codegen the arguments
    (gen code 'quote nil) ; accum = {NIL}
    (gen code 'set aindex) ; [aindex] = accum
    (loop for argform in (reverse aforms)
          do (compile-form argform env code) ; accum = <arg>
             (gen code 'cons aindex)) ; [aindex] = cons(accum, [aindex])
    ;; Call
    (gen code 'get findex) ; accum = [findex]
    (gen code 'scheme-vm:closure-vec cindex) ; [cindex] = vec(accum)
    (gen code 'scheme-vm:closure-ip findex) ; [findex] = ip(accum)
    (gen code 'scheme-vm:rotatef-closure cindex) ; closure <> [cindex]
    (gen code 'get aindex) ; accum = [aindex]
    (let ((to-fix
            (gen code 'scheme-vm:set-link 0))) ; link = 0 (will be fixed up)
      (gen code 'scheme-vm:igo findex) ; ip = [findex]
      (let ((next-ip (next-ip code)))
        (fixup code to-fix next-ip)
        (push (cons (aref code to-fix) next-ip) *fixups*)))
    (gen code 'scheme-vm:rotatef-closure cindex)))
