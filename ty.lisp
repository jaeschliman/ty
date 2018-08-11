(ql:quickload :alexandria)
(defpackage :ty (:use :cl :alexandria))
(in-package :ty)

(defun alist-get (sym alist &key (test 'eq))
  (cdr (assoc sym alist :test test)))

(defun rev-alist-get (value alist &key (test 'equalp))
  (loop for (key . val) in alist do
       (when (funcall test value val)
         (return key))))

(defstruct (ty (:constructor nil)) name)
(defmethod print-object ((self ty) stream)
  (format stream "[~A]" (ty-name self)))

(defmacro defty (name print-name &rest members)
  (let ((args (mapcar #'ensure-car members)))
    `(defstruct (,name (:include ty (name ',print-name)) (:constructor ,name ,args))
       ,@members)))

(defty -empty empty)

(defty -int int)
(defty -lit lit (value nil :type symbol))
(defmethod print-object ((self -lit) stream)
  (format stream "[~A ~S]" (ty-name self) (-lit-value self)))

(defty -or or (a nil :type symbol) (b nil :type symbol)) ;; a and by are ty-names
(defmethod print-object ((self -or) stream)
  (format stream "[~A ~A ~A]" (ty-name self) (-or-a self) (-or-b self)))

(defty -obj object
  (rows nil :type list)) ;;rows is an alist of (sym . ty-name)
(defmethod print-object ((self -obj) stream)
  (format stream "[~A (~{~A~})]" (ty-name self) (-obj-rows self)))

(defty -prop prop
  (ty nil :type symbol)
  (prop nil :type symbol))
(defmethod print-object ((self -prop) stream)
  (format stream "[~A ~A.~A]" (ty-name self) (-prop-ty self) (-prop-prop self)))


#|

goal:

;; given
(type a (obj type 'a value 'a-val))
(type b (obj type 'b value 'b-val))
(type c (or a b))
(declare it c) ;; a thing 'it' has type c

(let ((type (get it 'type))
      (value (get it 'value)))
  (refine! type 'a) ;;hack for testing
  value)

;; want this to type as [lit a-val]

so... the refine! on a prop type has to reach into the or type,
the object type, and reduce it by matching against the ref'd prop...

so, narrowing the or...
there may be issues with too much narrowing...
say:
a = (foo)
b = (foo)
(refine! a y)
where foo returns x | y,
a should now be y, but b should retain x | y
so I guess that means we need to intro for every 'complex' function type...
or maybe just always? yeesh
anyway...

|#

#|

second goal:

(do
 (type combined (or 'foo 'bar))
 (declare x combined)
 (declare y combined)
 (refine! x 'foo)
 (tuple x y))

;; => [TUPLE [LIT FOO] [OR [LIT FOO] [LIT BAR]]

this.... will be hard...
refine! effectively performs assignment
now we get into all the mess that mutable state has to offer.
do we deep copy? what do we do?

|#


(defun make-type-name (&optional param)
  (declare (ignore param))
  (gensym))

(defstruct env
  vars types)

(defparameter *base-env*
  (make-env :vars nil
            :types `((int . ,(-int)))))

(defmethod extend ((env env) (vars null) (types null)) env)
(defmethod extend ((env env) vars types)
  (make-env :vars (append vars (env-vars env))
            :types (append types (env-types env))))

(defun env (&key (vars nil) (types nil))
  (extend *base-env* vars types))

(defun apply-effects (env fx)
  (if (null fx)
      env
      (extend env (car fx) (cdr fx))))

;; for debugging?
;; but can't resolve an or type, because it uses refs >.<
;; introduce yet another representation for a resolved type?
(defmethod resolve ((ty ty) (env env))
  ty)
(defmethod resolve ((name symbol) (env env))
  (alist-get name (env-types env)))
(defmethod resolve ((repr list) (env env))
  (ecase (car repr)
    (or repr))) ;; should already be resolved...
(defmethod resolve ((ty -or) (env env))
  `(or ,(resolve (-or-a ty) env)
       ,(resolve (-or-b ty) env)))
(defmethod resolve ((ty -prop) (env env))
  (let ((prop-name (-prop-prop ty))
        (ref-ty (alist-get (-prop-ty ty) (env-types env))))
    (labels ((lookup-in (ty)
               (typecase ty
                 (-prop
                  (lookup-in (resolve ty env)))
                 (-obj
                  (resolve (alist-get prop-name (-obj-rows ty)) env))
                 (t nil))))
      (cond
        ((typep ref-ty '-obj)
         (lookup-in ref-ty))
        ((typep ref-ty '-prop)
         (lookup-in ref-ty))
        ((typep ref-ty '-or)
         (destructuring-bind (_ a b) (resolve ref-ty env)
           (declare (ignore _))
           (if-let ((a-ty (lookup-in a))
                    (b-ty (lookup-in b)))
             `(or ,a-ty ,b-ty)
             ;; give up otherwise
             ty)))
        ;; can't resolve
        (t ty)))))

;; ty-of applies to code in the env, returns 3 values,
;; the ty of the thing,
;; the ty-name of the type,
;; a list of side effects ((sym . ty-name) (ty-name . type)),
;; note that this requires a ty-name for fucking everything
;; is it required that ty-name be bound before applying side-effects?
;; I would think not. need a way to introduce types from an expression...
;; but why?
;; try typing a nested get
;; TODO: another value for refinements?
(defgeneric ty-of (thing env))
(defmethod  applied-ty (thing env)
  (multiple-value-bind (ty ty-name side-effects) (ty-of thing env)
    (values ty ty-name (apply-effects env side-effects))))

(defmethod ty-of ((var symbol) env)
  (let* ((ty-name (alist-get var (env-vars env)))
         (ty      (alist-get ty-name (env-types env))))
    (values ty ty-name nil)))

(defmethod ty-of ((num integer) env)
  (values (alist-get 'int (env-types env)) 'int nil))

(defun introduce (ty fx env)
  (declare (ignore env)) ;; may use it to optimize later
  (let ((nm (make-type-name)))
    (values ty nm (cons (car fx) (acons nm ty (cdr fx))))))

(defun combine-effects (a b)
  (when (or a b)
        (cons (append (car a) (car b))
              (append (cdr a) (cdr b)))))

;; welcome to the evaluator
(defmethod ty-of ((form list) env)
  (ecase (car form)
    (do
     (loop
        with env = env
        with fx = nil
        with next-fx = nil
        with ty = (-empty)
        with ty-name = nil
        for form in (cdr form) do
          (multiple-value-setq (ty ty-name next-fx) (ty-of form env))
          (setf env (apply-effects env next-fx)
                fx (combine-effects next-fx fx))
        finally (return-from ty-of (values ty ty-name fx))))
    ;; this should not directly exist in 'user' code
    (refine!
     (destructuring-bind (var ty-name) (cdr form)
       (multiple-value-bind (gen-ty gen-ty-name) (ty-of var env)
         (let* ((nar-ty (alist-get ty-name (env-types env)))
                (fx (refine gen-ty-name gen-ty nar-ty env)))
           (values (-empty) nil fx)))))
    (get
     (destructuring-bind (obj prop) (cdr form)
       (multiple-value-bind (_ ty-name fx) (ty-of obj env)
         (declare (ignore _))
         (let ((ty (-prop ty-name prop)))
           (introduce ty fx env)))))))

(defmethod ty-equal ((a ty) (b ty) env)
  (declare (ignore env))
  (equalp a b))

(defmethod ty-equal ((a -or) (b -or) env)
  (let ((a1 (lookup-type (-or-a a) env))
        (a2 (lookup-type (-or-b a) env))
        (b1 (lookup-type (-or-a b) env))
        (b2 (lookup-type (-or-b b) env)))
    (or (and (type-equal a1 b1) (type-equal a2 b2))
        (and (type-equal a2 b1) (type-equal a1 b2)))))

(defmethod lookup-type (ty-name env)
  (alist-get ty-name (env-types env)))

(defun ! (it) (print it) it)

(defmethod make-intersection-type :around ((a ty) (b ty) env)
  (if (ty-equal a b env)
      a
      (call-next-method)))

(defmethod make-intersection-type ((a ty) (b ty) env)
  (declare (ignore a b env))
  (-empty))

(defmethod make-intersection-type ((a -or) (b -or) env)
  (declare (ignore env))
  (error "unimplemented"))

(defmethod make-intersection-type ((gen -or) (nar ty) env)
  (let* ((ty-a (lookup-type (-or-a gen) env))
         (ty-b (lookup-type (-or-b gen) env))
         (a (make-intersection-type ty-a nar env))
         (b (make-intersection-type ty-b nar env))
         (no-a (-empty-p a))
         (no-b (-empty-p b)))
    (cond
      ((and no-a no-b) (-empty))
      (no-a b)
      (no-b a)
      ((ty-equal a b env) a)
      (t (error "unimplemented")))))

(defmethod make-intersection-type ((nar ty) (gen -or) env)
  (make-intersection-type gen nar env))

(defmethod refineable? ((gen ty) (nar ty) env)
  (ty-equal gen nar env))

(defmethod refineable? ((gen -or) (nar ty) env)
  (or
   (ty-equal gen nar env)
   (refineable? (lookup-type (-or-a gen) env) nar env)
   (refineable? (lookup-type (-or-b gen) env) nar env)))

;; refine: named general type + narrow type -> maybe side effects
(defmethod refine (name (gen ty) (narrow ty) env)
  (unless (ty-equal gen narrow env)
    (cons nil `((,name . ,(-empty))))))

(defun combine-new-types (a b env)
  (if (ty-equal a b env)
      (cons nil `((,(make-type-name) . ,a)))
      (let ((an (make-type-name))
            (bn (make-type-name))
            (cn (make-type-name)))
        (cons nil `((,an a)
                    (,bn b)
                    (,cn ,(-or an bn)))))))

(defmethod refine (name (gen -or) (narrow ty) env)
  ;; incomplete: multi-valued ors
  (let* ((ty-a (lookup-type (-or-a gen) env))
         (ty-b (lookup-type (-or-b gen) env))
         (a? (refineable? ty-a narrow env))
         (b? (refineable? ty-b narrow env)))
    (if (and a? b?)
        (let ((a-inter (make-intersection-type ty-a narrow env))
              (b-inter (make-intersection-type ty-b narrow env)))
          (combine-new-types a-inter b-inter env))
        (if a?
            (cons nil `((,name . ,(make-intersection-type ty-a narrow env))))
            (if b?
                (cons nil `((,name . ,(make-intersection-type ty-b narrow env))))
                (cons nil `((,name . ,(-empty)))))))))


(defun extract-prop-type (prop env)
  (let ((target (lookup-type (-prop-ty prop) env))
        (key  (-prop-name prop)))
    (flet ((get-row (obj)
             (lookup-type (alist-get key (-obj-rows obj)) env)))
      (typecase target
        (-obj (values (get-row target) nil))
        (-or
         (let ((a (lookup-type (-or-a target) env))
               (b (lookup-type (-or-b target) env)))
           ;; FIXME: need to handle nested ors etc
           ;; FIXME: requires both a and b are object types
           (if (and (-obj-p a) (-obj-p a))
               (combine-new-types (get-row a) (get-row b) env)
               (values (-empty) nil))))
        (t (values (-empty) nil))))))

(defmethod refineable? ((gen -prop) (nar ty) env)
  ;; need to extract the specific type of the referenced property,
  ;; and then possibly check whether /that/ is refineable against nar.
  (refineable? (extract-prop-type gen env) nar env))

(defmethod refine (name (gen -prop) (nar ty) env)
  (let* ((target-type (-prop-ty gen))
         (target (lookup-type target-type env))
         (key (-prop-prop gen)))
    (flet ((get-row (obj)
             (lookup-type (alist-get key (-obj-rows obj)) env)))
      (typecase target
        (-obj
         (let* ((row-type (get-row target))
                (update (refine name row-type nar env)))
           (or update (cons nil `((,name . ,nar))))))
        (-or
         (let* ((a (lookup-type (-or-a target) env))
                (b (lookup-type (-or-b target) env))
                (row-a (get-row a))
                (row-b (get-row b))
                (a? (refineable? row-a nar env))
                (b? (refineable? row-b nar env)))
           (cond
             ((and a? b?) (error "unimplemented"))
             (a?
              (combine-effects
               (or (refine name row-a nar env)
                   (cons nil `((,name . ,nar))))
               (combine-effects
                (cons nil `((,target-type . ,a)))
                (refine (-or-a target) target a env))))
             (b?
              (combine-effects
               (or (refine name row-b nar env)
                   (cons nil `((,name . ,nar))))
               (combine-effects
                (cons nil `((,target-type . ,b)))
                (refine (-or-b target) target b env))))
             (t (error "should not happen")))))
        (t (cons nil `((,name . ,(-empty)))))))))
