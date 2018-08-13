(ql:quickload :alexandria)
(ql:quickload :fiveAM)
(defpackage :ty (:use :cl :alexandria :5am))
(in-package :ty)

(defmacro ! (&rest it)
  (with-gensyms (result)
    `(let ((,result ,it))
       (format t "~A = ~A~%" ',it ,result)
       ,result)))

(defun alist-get (sym alist &key (test 'eq))
  (cdr (assoc sym alist :test test)))

(defun rev-assoc (value alist &key (test 'equalp))
  (loop for (key . val) in alist do
       (when (funcall test value val)
         (return (cons key val)))))

(defun rev-alist-get (value alist &key (test 'equalp))
  (car (rev-assoc value alist :test test)))

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

(defty -var var
  (ref nil :type symbol))
(defmethod print-object ((self -var) stream)
  (format stream "<~A : ~A>" (ty-name self) (-var-ref self)))

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

what about an alias type?
wraps a ref to a type, and interposes itself when needed...
what a hack...
call it 'var' for every variable will have one.

|#

#|
 third goal:
  function application
 fourth goal:
  something like generics?
|#



(defun make-type-name (&optional param)
  (declare (ignore param))
  (gensym))

(defstruct env
  vars types errors)
(defstruct effects
  vars types errors)

(defun lookup-type (ty-name env)
  (or
   (alist-get ty-name (env-types env))
   (break)))

(defun rev-lookup-type (ty env)
  (if-let (pair (rev-assoc ty (env-types env)))
    (values (cdr pair) (car pair))
    (values nil nil)))

(defparameter *base-env*
  (make-env :vars nil
            :types `((int . ,(-int)))
            :errors nil))

(defun extend (env &key vars types errors)
  (if (or vars types errors)
      (make-env :vars (append vars (env-vars env))
                :types (append types (env-types env))
                :errors (append errors (env-errors env)))
      env))

(defun env (&key (vars nil) (types nil) (errors nil))
  (extend *base-env* :vars vars :types types :errors errors))

(defun vfx (&rest keys-and-values)
  (make-effects :vars (plist-alist keys-and-values)))
(defun tfx (&rest keys-and-values)
  (make-effects :types (plist-alist keys-and-values)))
(defun efx (&rest messages)
  (make-effects :errors messages))

(defun combine-effects (a b &rest more)
  (if more
      (apply 'combine-effects (combine-effects a b) more)
      (cond
        ((and a b)
         (make-effects
          :vars (append (effects-vars a) (effects-vars b))
          :types (append (effects-types a) (effects-types b))
          :errors (append (effects-errors a) (effects-errors b))))
        (a a)
        (b b))))

(defun apply-effects (env fx)
  (if (null fx)
      env
      (extend
       env
       :vars (effects-vars fx)
       :types (effects-types fx)
       :errors (effects-errors fx))))

;; for debugging?
;; but can't resolve an or type, because it uses refs >.<
;; introduce yet another representation for a resolved type?
(defmethod resolve ((null null) (env env))
  (assert nil))
(defmethod resolve ((ty ty) (env env))
  ty)
(defmethod resolve ((ty -var) (env env))
  (resolve (-var-ref ty) env))

(defmethod resolve ((name symbol) (env env))
  (resolve (alist-get name (env-types env)) env))

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
                 (-obj
                  (let ((prop-type (alist-get prop-name (-obj-rows ty))))
                    (assert prop-type)
                    (resolve prop-type env)))
                 (-or
                  `(or
                    ,(lookup-in (resolve (-or-a ty) env))
                    ,(lookup-in (resolve (-or-b ty) env))))
                 (-var
                  (lookup-in (resolve ty env)))
                 (-prop
                  (lookup-in (resolve ty env)))
                 (list
                  (assert (eq (car ty) 'or))
                  `(or ,(lookup-in (second ty))
                       ,(lookup-in (third ty))))
                 (t (error "resolve internal error")))))
      (cond
        ((typep ref-ty '-var)
         (lookup-in ref-ty))
        ((typep ref-ty '-obj)
         (lookup-in ref-ty))
        ((typep ref-ty '-prop)
         (lookup-in ref-ty))
        ((typep ref-ty '-or)
         (lookup-in ref-ty))
        ;; can't resolve
        (t ty)))))



(defmethod expand-or-type ((ty -or) env)
  (let (expanded)
    (flet ((expand (tyname)
             (let ((it (lookup-type-through-vars tyname env)))
               (typecase it
                 (-or (setf expanded (append (expand-or-type it env) expanded)))
                 (t (push it expanded)))))
           (teq (a b)
             (ty-equal a b env)))
      (expand (-or-a ty))
      (expand (-or-b ty))
      (remove-duplicates expanded :test #'teq))))

(defun create-named-list-of-or-types (named-list-of-types env)
  (labels ((ensure-named (it)
             (if (consp it) it))
           (combine1 (a b)
             (let* ((na (or (car a) (make-type-name)))
                    (nb (or (car b) (make-type-name)))
                    (ty (-or na nb)))
               (values (cons nil ty) (tfx na (cdr a) nb (cdr b)))))
           (combine (a b &rest more)
             (if more
                 (multiple-value-bind (ty fx) (combine1 a b)
                   (multiple-value-bind (ty2 fx2) (apply #'combine ty more)
                     (values ty2 (combine-effects fx2 fx))))
                 (combine1 a b)))
           (teq (a b) (ty-equal a b env)))
    (let ((named-types (remove-duplicates named-list-of-types
                                          :test #'teq :key #'cdr)))
      (if (= 1 (length named-types))
          (values (cdr (first named-types)) nil)
          (multiple-value-bind (named-ty fx) (apply #'combine named-types)
            (values (cdr named-ty) fx))))))

(defun create-or-type (list-of-types env)
  (create-named-list-of-or-types (mapcar (lambda (it) (cons nil it)) list-of-types)
                                 env))

(defun parse-type (it env)
  (cond
    ((symbolp it)
     (lookup-type it env))
    ((eq (car it) 'or)
     (destructuring-bind (types . effects)
         (reduce (lambda (acc unparsed)
                   (multiple-value-bind (ty fx) (parse-type unparsed env)
                     (let ((name (and (symbolp unparsed) unparsed)))
                       (cons (cons (cons name ty) (car acc))
                             (combine-effects fx (cdr acc))))))
                 (cdr it)
                 :initial-value (cons nil nil))
       (multiple-value-bind (ty fx)
           (create-named-list-of-or-types (reverse types) env)
         (values ty (combine-effects fx effects)))))
    ((eq (car it) 'quote)
     (-lit (second it)))
    ((eq (car it) 'obj)
     (-obj 
      (plist-alist (cdr it))))
    ((eq (car it) 'prop)
     (-prop (second it) (third it)))
    (t (error "unimplemented"))))

;;; ---- ty-equal

(defmethod ty-equal ((a ty) (b ty) env)
  (declare (ignore env))
  (equalp a b))

(defmethod ty-equal ((a -var) (b -var) env)
  (ty-equal (lookup-type (-var-ref a) env)
            (lookup-type (-var-ref b) env)
            env))

(defmethod ty-equal ((a -var) (b ty) env)
  (ty-equal (lookup-type (-var-ref a) env) b env))

(defmethod ty-equal ((a ty) (b -var) env)
  (ty-equal b a env))

(defun expanded-or-types-equal (exp-a exp-b env)
  (flet ((teq (a b) (ty-equal a b env)))
    (and (= (length exp-a) (length exp-b))
         (null (set-difference exp-a exp-b :test #'teq)))))

(defmethod ty-equal ((a -or) (b -or) env)
  (let* ((exp-a (expand-or-type a env))
         (exp-b (expand-or-type b env)))
    (expanded-or-types-equal exp-a exp-b env)))

;;; ---- ty-of
;; ty-of applies to code in the env, returns 3 values,
;; the ty of the thing,
;; the ty-name of the type,
;; an optional side effects struct,
;; note that this requires a ty-name for fucking everything
;; is it required that ty-name be bound before applying side-effects?
;; I would think not. need a way to introduce types from an expression...
;; but why?
;; try typing a nested get
;; TODO: another value for refinements?

(defgeneric ty-of (thing env))

(defun introduce (ty fx env)
  ;; FIXME: rev-lookup-type has horrible performance...
  (multiple-value-bind (existing-ty name) (rev-lookup-type ty env)
    (if existing-ty
        (values existing-ty name fx)
        (let ((nm (make-type-name)))
          (values ty nm (combine-effects fx (tfx nm ty)))))))

(defmethod  applied-ty (thing env)
  (multiple-value-bind (ty ty-name side-effects) (ty-of thing env)
    (values ty ty-name (apply-effects env side-effects))))

(defmethod ty-of ((var symbol) env)
  (let* ((ty-name (alist-get var (env-vars env)))
         (ty      (alist-get ty-name (env-types env))))
    (values ty ty-name nil)))

(defmethod ty-of ((num integer) env)
  (values (alist-get 'int (env-types env)) 'int nil))

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
           (introduce ty fx env)))))
    (type
     (destructuring-bind (tyname unparsed) (cdr form)
       (multiple-value-bind (type fx) (parse-type unparsed env)
         (values (-empty) nil (combine-effects (tfx tyname type) fx)))))
    (declare
     (destructuring-bind (varname typename) (cdr form)
       (let ((name (make-type-name)))
         (values (-empty) nil
                 (combine-effects
                  (vfx varname name)
                  (tfx name (-var typename)))))))
    (def!
     (destructuring-bind (varname subform) (cdr form)
       (multiple-value-bind (ty typename fx) (ty-of subform env)
         (assert (not (-empty-p ty)))
         (values (-empty) nil
                 (combine-effects (vfx varname typename) fx)))))
    (def
     (destructuring-bind (varname subform) (cdr form)
       (multiple-value-bind (ty type-name fx) (ty-of subform env)
         (assert (not (-empty-p ty)))
         (let ((var-type (make-type-name)))
           (values (-empty) nil
                   (combine-effects
                    (vfx varname var-type)
                    (tfx var-type (-var type-name))
                    fx)))))))) 

;;well, this was buggy!
(defun combine-new-types (a b env)
  (if (ty-equal a b env)
      (values a (make-effects :types (acons (make-type-name) a nil)))
      (let* ((an (make-type-name))
             (bn (make-type-name))
             (cn (make-type-name))
             (ty (-or an bn)))
        (values ty
                (make-effects
                 :types (list (cons an a)
                              (cons bn b)
                              (cons cn ty)))))))

(defmethod lookup-type-through-vars (name env)
  (loop
     for ty-name = name then (-var-ref ty)
     for ty = (lookup-type ty-name env)
     while (-var-p ty)
     finally (return ty)))

(defun extract-prop-type (prop env)
  (let ((target (lookup-type (-prop-ty prop) env))
        (key  (-prop-prop prop)))
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

(defmethod make-intersection-type :around ((a ty) (b ty) env)
  (if (ty-equal a b env)
      a
      (call-next-method)))

(defmethod make-intersection-type ((a ty) (b ty) env)
  (declare (ignore a b env))
  (values (-empty) nil))

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
      ((and no-a no-b) (values (-empty) nil))
      (no-a (values b nil))
      (no-b (values a nil))
      ((ty-equal a b env) (values a nil))
      (t (error "unimplemented")))))

(defmethod make-intersection-type ((gen -prop) (nar ty) env)
  (make-intersection-type (extract-prop-type gen env) nar env))

(defmethod make-intersection-type ((nar ty) (gen -or) env)
  (make-intersection-type gen nar env))

(defmethod refineable? ((gen ty) (nar ty) env)
  (ty-equal gen nar env))

(defmethod refineable? ((var -var) (nar ty) env)
  (refineable? (lookup-type (-var-ref var) env) nar env))

(defmethod refineable? ((gen -or) (nar ty) env)
  (or
   (ty-equal gen nar env)
   (refineable? (lookup-type (-or-a gen) env) nar env)
   (refineable? (lookup-type (-or-b gen) env) nar env)))

;; refine: named general type + narrow type -> maybe side effects
(defmethod refine :around (name (gen ty) (narrow ty) env)
  (declare (ignore name env))
  ;; (print (list (type-of gen) '=> (type-of narrow)))
  (call-next-method))

(defmethod refine (name (gen ty) (narrow ty) env)
  (unless (ty-equal gen narrow env)
    (make-effects
     :types (acons name (-empty) nil)
     :errors (list (format nil "Cannot narrow ~A to ~A" gen narrow)))))

(defmethod refine :around (name (gen -var) (narrow ty) env)
  (let ((changes (refine name (lookup-type (-var-ref gen) env) narrow env)))
    (when changes
      (let ((replacer (make-type-name))) 
        (make-effects
         :vars (effects-vars changes)
         :types (cons 
                 (cons name (-var replacer))
                 (mapcar (lambda (update)
                           (if (eq (car update) name)
                               (cons replacer (cdr update))
                               update))
                         (effects-types changes)))
         :errors (effects-errors changes))))))

(defmethod refine (name (gen -or) (narrow ty) env)
  ;; incomplete: multi-valued ors
  (let* ((ty-a (lookup-type (-or-a gen) env))
         (ty-b (lookup-type (-or-b gen) env))
         (a? (refineable? ty-a narrow env))
         (b? (refineable? ty-b narrow env)))
    (if (and a? b?)
        (multiple-value-bind (a-type a-fx)
            (make-intersection-type ty-a narrow env)
          (multiple-value-bind (b-type b-fx)
              (make-intersection-type ty-b narrow env)
            (combine-effects a-fx b-fx
                             (combine-new-types a-type b-type env))))
        (if a?
            (multiple-value-bind (a-type a-fx)
                (make-intersection-type ty-a narrow env)
              (combine-effects (tfx name a-type) a-fx))
            (if b?
                (multiple-value-bind (b-type b-fx)
                    (make-intersection-type ty-b narrow env)
                  (combine-effects (tfx name b-type) b-fx))
                (combine-effects
                 (tfx name (-empty))
                 (efx (format nil "Cannot refine ~A to ~A" gen narrow))))))))

(defmethod refineable? ((gen -prop) (nar ty) env)
  ;; need to extract the specific type of the referenced property,
  ;; and then possibly check whether /that/ is refineable against nar.
  (refineable? (extract-prop-type gen env) nar env))

(defmethod refine (name (gen -prop) (nar ty) env)
  (let* ((target-type (-prop-ty gen))
         (target (lookup-type-through-vars target-type env))
         (key (-prop-prop gen)))
    (flet ((get-row (obj)
             (lookup-type (alist-get key (-obj-rows obj)) env)))
      (labels ((recur (target)
                 (typecase target
                   (-var
                    (let ((new-target (lookup-type (-var-ref target) env)))
                      (recur new-target)))
                   (-obj
                    (let* ((row-type (get-row target))
                           (update (refine name row-type nar env)))
                      (or update (tfx name nar))))
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
                          (or (refine name row-a nar env) (tfx name nar))
                          (tfx target-type a)
                          (refine (-or-a target) target a env)))
                        (b?
                         (combine-effects
                          (or (refine name row-b nar env) (tfx name nar))
                          (tfx target-type b) 
                          (refine (-or-b target) target b env)))
                        (t (error "should not happen")))))
                   (-prop
                    (let* ((sub-target (lookup-type-through-vars
                                        (-prop-ty target) env))
                           (new-type (progn
                                       (check-type sub-target -obj)
                                       (alist-get (-prop-prop target)
                                                  (-obj-rows sub-target))))
                           (new-target (lookup-type new-type env)))
                      (recur new-target)))
                   (t
                    (combine-effects
                     (tfx name (-empty))
                     (efx (format nil "Could not refine ~A to ~A" gen nar)))))))
        (recur target)))))
