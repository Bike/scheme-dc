;;;; This is a small Scheme-oid language with delimited continuations.

;;;; There are four relevant operators: let/ec, escape, let/dc, extend.
;;;; (let/ec [var] [body]) binds var to a one shot escape continuation
;;;;  for the evaluation of body.
;;;; (escape [value] [form]) evalutes value, which must be an escape
;;;;  bound by let/ec, and then evaluates form. The let/ec that bound the
;;;;  escape then exits immediately, returning the value of form.
;;;; A let/ec cannot be exited more than once - ESCAPE will signal an
;;;;  error if this is attempted.
;;;; (let/dc ([var] [escape]) [body]) evaluates escape to a let/ec
;;;;  escape continuation. Then it evalutes the body with var bound to
;;;;  a continuation delimited on one end by the escape, and on the
;;;;  other by the let/dc.
;;;; (extend [continuation] [form]) evaluates continuation to a let/dc
;;;;  continuation, then evalutes form. It then extends the current
;;;;  continuation with the provided continuation, passing it the value
;;;;  of the form.
;;;; Note that extending a continuation means entering a "new" let/ec,
;;;;  so it can be returned from again.
;;;; These operators are intended to closely resemble how a call stack
;;;; is actually manipulated. When I tried to figure out delimited
;;;; continuations before, this aspect was not obvious to me.
;;;; This is also why continuations are not functions like in Scheme.
;;;; Making continuations functions is an oversimplification.
;;;; These operators are sufficient to implement reset/shift as follows:
;;;; (reset form) = (let/ec [sym] form) where sym is unique to a
;;;;  reset/shift pair.
;;;; (shift var form) = (let/dc (var [sym]) (escape [sym] form))
;;;;  where, again, [sym] should match that of the reset.
;;;; (k form) = (extend k form), k being a continuation bound by shift
;;;;  or by let/dc respectively.

;;;; The implementation is half-remembered from  "Functional Derivation
;;;; of a Virtual Machine for Delimited Continuations", by Asai & Kitani.
;;;; In short, you have the basic design of an
;;;; interpreter for Scheme with call/cc - eval takes a form, an
;;;; environment, and a continuation. But instead of continuations being
;;;; functions, they are call stacks: here, actual lists, with elements
;;;; being instances of a FRAME class. The stack still describes the
;;;; remainder of the computation in the same way, but because it's made
;;;; up of discrete elements, it can be manipulated in ways other than
;;;; replacing the entire stack at once (like call/cc).

;;;; Interaction between let/dc and distinct let/ecs might be a little
;;;; weird. Not sure yet. Like having resets with different names, and
;;;; interleaved. FIXME: Yeah see note in escape-frame. If that's fixed,
;;;; imminent escapes will be on the stack, and if that stack is copied
;;;; those probably need to be fixed up.

;;;; There are weird cases. Consider
;;;; (let/ec outer (... (let/ec inner ... (escape outer ... (let/dc (s inner) ...)))))
;;;; Now if you try to extend with s, what happens?
;;;; I would say extend ought to exit to outer instead of returning like usual.
;;;; But then "extend" is a misnomer. Worse, if unwind-protect exists, cleanups
;;;; between outer and inner somehow need to be saved.
;;;; So maybe this is actually an error - since the continuation of the let/dc is
;;;; not actually an extension of inner!
;;;; But then we're back to where we were with escapes not being on the stack.
;;;; Maybe dynamic-extent and continuation extension are not actually the same...?

(defpackage #:scheme
  (:use #:cl)
  (:shadow #:eval #:continue)
  (:export #:eval)
  (:export #:let/ec #:escape)
  (:export #:let/dc #:extend)
  (:export #:backtrace)
  (:export #:base-env))

(in-package #:scheme)

(defun base-env ()
  (macrolet ((alias (name params)
               `(cons ',name (lambda (stack ,@params)
                               (ret stack (,name ,@params)))))
             (aliasr (name)
               `(cons ',name (lambda (stack &rest args)
                               (ret stack (apply #',name args))))))
    (list
     (alias print (object))
     (alias cons (o1 o2))
     (alias car (cons))
     (alias cdr (cons))
     (aliasr *)
     (aliasr +)
     (cons 'backtrace (lambda (stack) stack)))))

(defun augment-environment (params args env)
  (etypecase params
    (cons
     (if (consp args)
         (augment-environment (car params) (car args)
                              (augment-environment (cdr params) (cdr args)
                                                   env))
         (error "Not enough arguments")))
    (null
     (if (null args)
         env
         (error "Too many arguments")))
    (symbol (acons params args env))))

(defclass frame ()
  ((%env :initarg :env :reader env)))

(defclass if-frame (frame)
  ((%then :initarg :then :reader then)
   (%else :initarg :else :reader else)))

(defun if-frame (then else env)
  (make-instance 'if-frame :then then :else else :env env))

(defclass escape-frame (frame)
  ((%body :initarg :body :reader body)))

(defun escape-frame (body env)
  (make-instance 'escape-frame :body body :env env))

(defclass evlis-frame (frame)
  ((%argforms :initarg :argforms :reader argforms)
   ;; A list argn...arg1 arg0 function
   (%vals :initarg :vals :reader vals)))

(defun evlis-frame (argforms vals env)
  (make-instance 'evlis-frame :argforms argforms :vals vals :env env))

(defclass apply-frame (frame) ())

(defun apply-frame () (make-instance 'apply-frame))

(defclass let/dc-frame (frame)
  ((%var :initarg :var :reader var)
   (%body :initarg :body :reader body)))

(defun let/dc-frame (var body env)
  (make-instance 'let/dc-frame :var var :body body :env env))

(defclass extend-frame (frame)
  ((%body :initarg :body :reader body)))

(defun extend-frame (body env)
  (make-instance 'extend-frame :body body :env env))

;;; This is a Scheme escape continuation, which is just a copy of the
;;; stack, but wrapped up so it's not confused with a list.
(defclass rstack ()
  ((%stack :reader dereify-stack :initarg :stack)))

(defun reify-stack (stack)
  (make-instance 'rstack :stack stack))

;;; This is a Scheme delimited continuation, which is a slice of part
;;; of a stack.
(defclass continuation ()
  ((%slice :reader slice :initarg :slice)))

(defun continuation (above below)
  (unless (tailp above below)
    (error "Cannot make a delimited continuation with an escape that has already exited"))
  (make-instance 'continuation :slice (ldiff below above)))

(defun eval (form env &optional stack)
  (typecase form
    (symbol
     (let ((pair (assoc form env)))
       (if pair
           (ret stack (cdr pair))
           (error "Unbound variable: ~a" form))))
    (cons
     (case (first form)
       ((quote)
        (destructuring-bind (object) (rest form)
          (ret stack object)))
       ((lambda)
        (destructuring-bind (params body) (rest form)
          (ret stack (lambda (stack &rest args)
                       (eval body
                             (augment-environment params args env)
                             stack)))))
       ((if)
        (destructuring-bind (test then else) (rest form)
          (eval test env
                (cons (if-frame then else env) stack))))
       ((let/ec)
        ;; NOTE: Could maybe escape more efficiently by having a
        ;; let/ec-cleanup frame in here that marks the escape
        ;; as out of extent?
        (destructuring-bind (var body) (rest form)
          (unless (symbolp var)
            (error "Syntax error in let/ec"))
          (eval body
                (acons var (reify-stack stack) env)
                stack)))
       ((escape)
        (destructuring-bind (escape body) (rest form)
          (eval escape env
                (cons (escape-frame body env) stack))))
       ((let/dc)
        (destructuring-bind ((var escape) body) (rest form)
          (eval escape env
                (cons (let/dc-frame var body env) stack))))
       ((extend)
        (destructuring-bind (continuation body) (rest form)
          (eval continuation env
                (cons (extend-frame body env) stack))))
       #+dynamic-wind
       ((unwind-protect)
        (destructuring-bind (protected cleanup) (rest form)
          (eval protected env
                (cons (unwind-protect-frame cleanup env) stack))))
       #+dynamic-wind
       ((rewind-protect)
        (destructuring-bind (cleanup protected) (rest form)
          (eval cleanup env
                (cons (rewind-protect-frame cleanup protected env) stack))))
       (otherwise
        (destructuring-bind (function &rest argforms) form
          (eval function env
                (list* (evlis-frame argforms nil env)
                       (apply-frame)
                       stack))))))
    (t (ret stack form))))

(defun ret (stack value)
  (if (null stack)
      value
      (deframe (first stack) value (rest stack))))

(defgeneric deframe (frame value stack))

(defmethod deframe ((frame if-frame) bool stack)
  (ecase bool
    ((t) (eval (then frame) (env frame) stack))
    ((nil) (eval (else frame) (env frame) stack))))

(defmethod deframe ((frame escape-frame) escape stack)
  ;; FIXME: This is not correct.
  ;; The unwinding occurs, essentially, before the return form is evaluated,
  ;; meaning that the return form can't execute its own closer nonlocal exits.
  ;; This is also unrealistic for a stack, since the stack frames need to
  ;; be around for the form to be evaluated.
  (let ((escape-stack (dereify-stack escape)))
    (if (tailp escape-stack stack)
        (eval (body frame) (env frame) escape-stack)
        (error "Out of extent return"))))

(defmethod deframe ((frame evlis-frame) thing stack)
  ;; This is kind of ugly.
  ;; An evlis frame has a list of argument forms to evaluate,
  ;; a list of argument values and the function, already evaluated,
  ;; and the environment.
  ;; The first evlis frame, direct from eval, adds the function it's
  ;; passed (as thing) to the values.
  ;; The last evlis frame, which may also be the first, finds that
  ;; there is nothing left to evaluate, and passes the whole list
  ;; on to the next frame, which is an apply-frame or something.
  ;; Frames that find something to evaluate do so with a new
  ;; evlis-frame on the stack.
  (let ((vals (cons thing (vals frame)))
        (argforms (argforms frame)))
    (if (null argforms)
        (ret stack (reverse vals))
        (let ((env (env frame)))
          (eval (first argforms) env
                (cons (evlis-frame (rest argforms) vals env)
                      stack))))))

(defmethod deframe ((frame apply-frame) fn-args stack)
  (apply (first fn-args) stack (rest fn-args)))

(defmethod deframe ((frame let/dc-frame) escape stack)
  (eval (body frame)
        (acons (var frame) (continuation (dereify-stack escape) stack) (env frame))
        stack))

(defmethod deframe ((frame extend-frame) continuation stack)
  (eval (body frame) (env frame)
        (append (slice continuation) stack)))
