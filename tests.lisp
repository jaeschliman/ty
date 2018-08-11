(in-package :ty)

(defmacro print-values (form)
  `(print (multiple-value-list ,form)))


(print-values
 (ty-of 'x
        (env :vars `((x . a))
             :types `((a . ,(-int))))))
(print-values
 (ty-of 'x
        (env :vars `((x . a))
             :types `((a . ,(-obj '((a . row-a))))
                      (row-a . ,(-int))))))
(print-values
 (ty-of 'x
        (env :vars `((x . ref-row-a))
             :types `((a . ,(-obj '((a . row-a))))
                      (row-a . ,(-int))
                      (ref-row-a . ,(-prop 'a 'a))))))

(let ((env (env :vars `((x . ref-row-a))
                :types `((a . ,(-obj '((a . row-a))))
                         (row-a . ,(-int))
                         (ref-row-a . ,(-prop 'a 'a))))))
  (print-values
   (resolve (ty-of 'x env) env)))

(let ((env (env :vars `((x . x))
                :types `((lit . ,(-lit 'foo))
                         (x . ,(-or 'int 'lit))))))
  (print-values
   (resolve (ty-of 'x env) env)))

(print-values (resolve (ty-of 5 *base-env*) *base-env*))

(let ((env (env :vars `((x . x))
                :types `((x . ,(-obj '((a . int))))))))
  (print-values
   (resolve (ty-of 'x env) env)))

(let ((env (env :vars `((x . x))
                :types `((x . ,(-obj '((a . int))))))))
  (print-values
   (ty-of '(get x a) env)))

(let ((env (env :vars `((x . x))
                :types `((x . ,(-obj '((a . int))))))))
  (print-values
   (resolve (ty-of '(get x a) env) env)))

(let ((env (env :vars `((x . x))
                :types `((a . ,(-obj `((a . ,(-lit 'a-prop)))))
                         (b . ,(-obj `((a . ,(-lit 'b-prop)))))
                         (x . ,(-or 'a 'b))))))
  (print-values
   (resolve (ty-of '(get x a) env) env)))

(let ((env (env :vars `((x . a)
                        (y . a-prop))
                :types `((a . ,(-obj `((a . b))))
                         (a-prop . ,(-prop 'a 'a))
                         (b . ,(-obj `((b . ,(-lit 'b-prop)))))))))
  (print-values
   (resolve (ty-of '(get y b) env) env)))

(defun chk (expr &optional (env *base-env*))
  (print-values
   (multiple-value-bind
         (ty ty-name env) (applied-ty expr env)
     (declare (ignore ty-name))
     ;; (pprint env)
     (values ty ":" (resolve ty env)))))

(let ((env (env :vars `((x . a))
                :types `((a . ,(-obj `((a . b))))
                         (b . ,(-obj `((b . ,(-lit 'b-prop)))))))))
  (print-values
   (multiple-value-bind
         (ty ty-name env) (applied-ty '(get (get x a) b) env)
     (declare (ignore ty-name))
     (resolve ty env))))

(print-values
 (ty-of '(do x x)
        (env :vars `((x . int)))))

(print-values
 (ty-of '(do (refine! x int) x)
        (env :vars `((x . int)))))

(chk
 '(do (refine! x int) x)
 (env :vars `((x . x))
      :types `((x . ,(-int)))))

(chk
 '(do (refine! x foo) x)
 (env :vars `((x . x))
      :types `((foo . ,(-lit 'foo))
               (x . ,(-int)))))

(chk
 '(do (refine! x foo) x)
 (env :vars `((x . x))
      :types `((foo . ,(-lit 'foo))
               (x . ,(-or 'foo 'int)))))
(chk
 '(do (refine! x foo) x)
 (env :vars `((x . x))
      :types `((foo . ,(-lit 'foo))
               (bar . ,(-lit 'bar))
               (baz . ,(-lit 'baz))
               (a . ,(-or 'foo 'bar))
               (b . ,(-or 'foo 'baz))
               (x . ,(-or 'a 'b)))))

(chk
 '(do (refine! x b) x)
 (env :vars `((x . x))
      :types `((foo . ,(-lit 'foo))
               (bar . ,(-lit 'bar))
               (baz . ,(-lit 'baz))
               (a . ,(-or 'foo 'bar))
               (b . ,(-or 'foo 'baz))
               (x . ,(-or 'a 'b)))))

(defparameter *type-value-ref-env
  (env :vars `((type . type-ref)
               (value . value-ref)
               (simple-ref . foo-ref)
               (alias-ref  . foo-ref))
       :types
       `((foo . ,(-lit 'foo))
         (bar . ,(-lit 'bar))
         (baz . ,(-lit 'baz))
         (quux . ,(-lit 'quux))
         (obj-foo . ,(-obj '((type . foo)
                             (value . baz))))
         (obj-bar . ,(-obj '((type . bar)
                             (value . quux))))
         (my-obj . ,(-or 'obj-foo 'obj-bar))
         (foo-ref . ,(-prop 'obj-foo 'type))
         (type-ref . ,(-prop 'my-obj 'type))
         (value-ref . ,(-prop 'my-obj 'value)))))

;;; check a simple prop ref...
(chk
 'simple-ref *type-value-ref-env)

;;;; refine a simple prop ref...
(chk
 '(do (refine! simple-ref foo) simple-ref)
 *type-value-ref-env)

;;;; refine a not-so-simple prop ref...
(chk
 '(do (refine! simple-ref foo) alias-ref)
 *type-value-ref-env)

;;;; ref through an or...
(chk '(do type) *type-value-ref-env)

;;;; refine a prop ref into an or...
(chk
 '(do (refine! type foo) type)
 *type-value-ref-env)

;;;;; and eventually, propogate it correctly:
(chk
 '(do (refine! type foo) value)
 *type-value-ref-env)

;;;;; and eventually, propogate it correctly:
(chk
 '(do (refine! type foo) (refine! value baz) value)
 *type-value-ref-env)

;;;;; and eventually, propogate it correctly (and confirm it does!):
(chk
 '(do (refine! type foo) (refine! value quux) value) ;; should be empty
 *type-value-ref-env)


;; and uh, someday, even nest them!

;; ---------------------------------------------------------------------------
;;;;; and now....... VAR types!


(defparameter *var-env-0
  (env :vars nil
       :types
       `((foo . ,(-lit 'foo))
         (bar . ,(-lit 'bar))
         (baz . ,(-lit 'baz))
         (quux . ,(-lit 'quux))
         (obj-foo . ,(-obj '((type . foo)
                             (value . baz))))
         (obj-bar . ,(-obj '((type . bar)
                             (value . quux))))
         (type-ref . ,(-prop 'my-obj 'type))
         (value-ref . ,(-prop 'my-obj 'value)))))

(chk '(do (declare x foo) x) *var-env-0)

(chk '(do
       (declare x foo)
       (refine! x foo)
       x)
     *var-env-0)

(chk '(do
       (declare x foo)
       (declare y foo)
       (refine! x bar)
       x)
     *var-env-0)

(chk '(do
       (declare x foo)
       (declare y foo)
       (refine! x bar)
       y)
     *var-env-0)
 
(chk '(do
       (type t (or foo bar))
       (declare x t)
       (refine! x bar)
       x)
     *var-env-0)

(chk '(do
       (type t (or foo bar))
       (declare x t)
       (declare y t)
       (refine! x bar)
       y)
     *var-env-0)

(chk '(do
       (type foo 'foo)
       (type a (obj type foo))
       (type p (prop a type))
       (declare x p)
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type p-a (prop a type))
       (type p-b (prop b type))
       (type p (or p-a p-b))
       (declare x p)
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type p-a (prop a type))
       (type p-b (prop b type))
       (type p (or p-a p-b))
       (declare x p)
       (refine! x foo)
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type p-a (prop a type))
       (type p-b (prop b type))
       (type p (or p-a p-b))
       (declare x p)
       (declare y p)
       (refine! x foo)
       y))
