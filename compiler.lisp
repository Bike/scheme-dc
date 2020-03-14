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
         (*nvals* 1) ; unconditionally store link register
         (to-fix (gen code 'push 0))
         (env (append (gen-arg-parse params code) env)))
    (gen code 'scheme-vm:save-link 0)
    ;; Get goin
    (compile-form body env code)
    ;; aaaaand return.
    (gen code 'scheme-vm:restore-link 0)
    (gen code 'pop)
    (gen code 'return)
    (fixup code to-fix *nvals*) ; frame size now known
    (values code *fixups*)))

;;; Compile a function and any sub functions, putting everything
;;; in one vector.
;;; This is very ugly so some more explanation.
;;; A fixup is something where we need to fiddle with an immediate
;;; because it refers to a literal instruction pointer.
;;; We have two kinds of fixups. One is just an instruction, i.e.
;;; an (opcode . args) list as defined in vm.lisp. These we should
;;; probably actually remove with relative addressing (FIXME)
;;; except for closure-alloc.
;;; The other kind is an entire sub function, or inner function.
;;; These we have as lists (code-vector allocation-fixup . other-fixups).
;;; We paste all functions together cos you know, turing machine shite.
(defun compile-function-and (params body env)
  (declare (optimize debug))
  (multiple-value-bind (code fixups)
      (compile-function params body env)
    (loop for fixup in fixups
          for thing = (first fixup)
          when (vectorp thing) ; sub function
            collect fixup into subs
            and collect (second fixup) into boring ; in case this is recursive
          else collect fixup into boring
          finally
             (return
               (let* ((code-length (length code))
                      (new-code-length
                        (+ code-length
                           (loop for (subcode) in subs
                                 summing (length subcode))))
                      (new-code (make-array new-code-length)))
                 (replace new-code code)
                 (loop for (subcode closure-alloc . more-fixups)
                         in subs
                       for ip = code-length
                         then (+ ip subcode-length) ; sc-length from prev iter
                       for subcode-length = (length subcode)
                       do (setf (second closure-alloc) ip)
                          (loop for fixup in more-fixups
                                do (incf (second fixup) ip))
                          (replace new-code subcode :start1 ip)
                       append more-fixups into all-fixups
                       finally (return
                                 (values new-code
                                         (append boring all-fixups)))))))))

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
               ((:closure) (gen code 'scheme-vm:closure-get i))))
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
          (let* ((free (free body (flatten params)))
                 ;; TODO: globals
                 (cenv (loop for f in free
                             for i from 0
                             collecting (list f :closure i)))
                 ;; NOTE: We only need one of these per function,
                 ;; since closed over variables don't require
                 ;; further evaluation
                 (cindex (new-value-index)))
              (multiple-value-bind (fcode ffixups)
                  (compile-function-and params body cenv)
                (let ((to-fix
                        (gen code 'scheme-vm:closure-alloc
                             0 (length free))))
                  (push (list* fcode (aref code to-fix) ffixups) *fixups*)
                  (gen code 'set cindex)
                  (loop for f in free
                        for i from 0
                        do (assert (symbolp f)) ; sanity check
                        do (compile-form f env code)
                           (gen code 'scheme-vm:closure-set cindex i))
                  (gen code 'get cindex))))))
       ((funcall) ; yes this is a dumb hack.
        (destructuring-bind (function form &rest args) (rest form)
          (compile-form form env code)
          (apply #'gen code 'funcall function args)))
       ((let/ec)
        (destructuring-bind (var body) (rest form)
          (unless (symbolp var)
            (error "Syntax error in let/ec"))
          (gen-let/ec var body env code)))
       ((escape)
        (destructuring-bind (escape form) (rest form)
          (gen-escape escape form env code)))
       ((let/dc)
        (destructuring-bind ((var escape) body) (rest form)
          (unless (symbolp var)
            (error "Syntax error in let/dc"))
          (gen-let/dc var escape body env code)))
       ((extend)
        (destructuring-bind (continuation form) (rest form)
          (gen-extend continuation form env code)))
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
       ((funcall)
        (destructuring-bind (function form &rest constants) (rest form)
          (declare (ignore function constants))
          (free form bound)))
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
        (push (aref code to-fix) *fixups*)))
    (gen code 'scheme-vm:rotatef-closure cindex)))

(defun gen-let/ec (var form env code)
  ;; 1) Allocate the escape and store it in the frame.
  ;; 2) The closure register is caller-save, so do that.
  ;; 3) Execute the form.
  ;; 4) We need to do some processing upon abnormal return, so jump.
  ;; 5) For abnormal return, restore the closure, then meet up with normal.
  (let* ((cindex (new-value-index)) ; TODO: only need one per function
         (eindex (new-value-index))
         (e-to-fix (gen code 'scheme-vm:alloc-escape 0)))
    (push (aref code e-to-fix) *fixups*)
    (gen code 'set eindex)
    ;; 2
    (gen code 'scheme-vm:save-closure cindex)
    ;; 3
    (let ((env (cons (list var :local eindex) env)))
      (compile-form form env code))
    ;; 4
    (let ((g-to-fix (gen code 'go 0)))
      (push (aref code g-to-fix) *fixups*)
      (fixup code e-to-fix (next-ip code))
      ;; 5
      (gen code 'scheme-vm:load-closure cindex)
      (fixup code g-to-fix (next-ip code)))))

(defun gen-escape (escape value env code)
  ;; 1) Evaluate the escape and store it in the frame.
  ;; 2) Evaluate the value (into alloc).
  ;; 3) Set the link register from the escape.
  ;; 4) Set the frame register from the escape.
  ;; 5) Return.
  (let (;; fyi we need more than one of these cos of (escape ... (escape ...))
        ;; probably. I don't know why I bother mentioning sharing oppors,
        ;; this is just for learning anyway. Guess I'm learning that?
        ;; To do this right we'd want, like, a register allocator and shit.
        (eindex (new-value-index)))
    (compile-form escape env code) ; 1
    (gen code 'set eindex)
    (compile-form value env code) ; 2
    (gen code 'scheme-vm:escape-ip eindex) ; 3
    (gen code 'scheme-vm:escape-frame eindex) ; 4
    (gen code 'return))) ; 5

(defun gen-let/dc (var escape body env code)
  ;; 1) Evaluate the escape into accum.
  ;; 2) Copy the partial continuation into accum.
  ;; 3) Move it to the frame.
  ;; 4) Evaluate the body.
  (compile-form escape env code) ; 1
  (let ((to-fix (gen code 'scheme-vm:slice-continuation 0)) ; 2
        (cont-index (new-value-index)))
    (push (aref code to-fix) *fixups*)
    (gen code 'set cont-index) ; 3
    (let ((env (cons (list var :local cont-index) env)))
      (compile-form body env code)) ; 4
    (fixup code to-fix (next-ip code))))

(defun gen-extend (continuation value env code)
  ;; This works kind of like a call, so:
  ;; 1) Evaluate the continuation and stuff it in the frame.
  ;; 2) Evaluate the value form into accum.
  ;; 3) Save the closure register into the frame.
  ;; 4) Do the extension (change frame and return).
  ;;    This is a complicated operation that would probably be
  ;;    a function call in the real world, but we have an instruction.
  ;; 5) Restore the closure register.
  (let ((cont-index (new-value-index))
        (cindex (new-value-index)))
    (compile-form continuation env code)
    (gen code 'set cont-index)
    (compile-form value env code)
    (gen code 'scheme-vm:save-closure cindex)
    (let ((to-fix (gen code 'scheme-vm:extend 0 cont-index)))
      (fixup code to-fix (next-ip code))
      (push (aref code to-fix) *fixups*))
    (gen code 'scheme-vm:load-closure cindex)))
