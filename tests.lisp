(in-package :ty)

(def-suite initial-inferences)
(in-suite initial-inferences)

(defmacro print-values (form)
  `(print (multiple-value-list ,form)))

(defmacro ty-full-assert (type name effects form &body env)
  `(is (equalp (list ,type ,name ,effects) (multiple-value-list (ty-of ,form ,@env)))))

(defun ty-assert-unresolved (unresolved-ty expr &optional (env *base-env*))
  (is (equalp unresolved-ty
              (multiple-value-bind
                    (ty ty-name env) (applied-ty expr env)
                (declare (ignore ty-name env))
                ty))))

(defun ty-assert (resolved-ty expr &optional (env *base-env*))
  (is (equalp resolved-ty
              (multiple-value-bind
                    (ty ty-name env) (applied-ty expr env)
                (declare (ignore ty-name))
                ;; (pprint env)
                ;;(values ty ":" (resolve ty env))
                (resolve ty env)))))

(defun -ty-assert (resolved-ty expr &optional (env *base-env*))
  (equalp resolved-ty
          (multiple-value-bind
                (ty ty-name env) (applied-ty expr env)
            (declare (ignore ty-name))
            ;; (pprint env)
            ;;(values ty ":" (resolve ty env))
            (resolve ty env))))

(defmacro envq (&key vars types)
  (flet ((list->qalist (list)
           `(list
             ,@(loop for (key value) in list collect
                  `(cons (quote ,key) ,value)))))
    `(env :vars ,(list->qalist vars) :types ,(list->qalist types))))

(defmacro -objq (&rest rows)
  (flet ((list->qqalist (list)
           `(list
             ,@(loop for (key value) in list collect
                    (progn
                      (assert (symbolp key))
                      (assert (symbolp value))
                      `(cons (quote ,key) (quote ,value)))))))
    `(-obj ,(list->qqalist rows))))

(test basic-checks-0
  (ty-full-assert (-int) 'a nil
      'x
    (env :vars `((x . a))
         :types `((a . ,(-int)))))

  (ty-full-assert (-obj `((a . row-a))) 'a nil
      'x
    (env :vars `((x . a))
         :types `((a . ,(-obj '((a . row-a))))
                  (row-a . ,(-int)))))

  (ty-assert (-int) 'x
             (envq :vars ((x 'ref-row-a))
                   :types ((a (-obj '((a . row-a))))
                           (row-a (-int))
                           (ref-row-a (-prop 'a 'a)))))

  (ty-assert `(or ,(-int) ,(-lit 'foo)) 'x
             (envq :vars ((x 'x))
                   :types ((lit (-lit 'foo))
                           (x (-or 'int 'lit)))))

  (ty-assert (-int) 5)

  (ty-assert (-objq (a int)) 'x
             (envq :vars ((x 'x))
                   :types ((x (-objq (a int))))))

  (ty-assert-unresolved (-prop 'x 'a) '(get x a)
                        (envq :vars ((x 'x))
                              :types ((x (-objq (a int))))))

  (ty-assert (-int) '(get x a)
             (envq :vars ((x 'x))
                   :types ((x (-objq (a int))))))

  (ty-assert `(or ,(-lit 'a-prop)
                  ,(-lit 'b-prop))
             '(get x a)
             (envq :vars ((x 'x))
                   :types ((a-prop (-lit 'a-prop))
                           (b-prop (-lit 'b-prop))
                           (a (-objq (a a-prop)))
                           (b (-objq (a b-prop)))
                           (x (-or 'a 'b)))))
  
  (ty-assert (-lit 'b-prop)
             `(get y b)
             (envq :vars ((y 'a-prop))
                   :types
                   ((a (-objq (a b)))
                    (b (-objq (b lit-b-prop)))
                    (lit-b-prop (-lit 'b-prop))
                    (a-prop (-prop 'a 'a))
                    (b-prop (-prop 'b 'b)))))

  (ty-assert (-lit 'b-prop)
             `(get (get x a) b)
             (envq :vars ((x 'a))
                   :types
                   ((a (-objq (a b)))
                    (b (-objq (b lit-b-prop)))
                    (lit-b-prop (-lit 'b-prop)))))
  )

(test basic-checks-1
  (ty-assert (-int) '(do x x)
             (envq :vars ((x 'int))))

  (ty-assert (-int) '(do (refine! x int) x)
             (envq :vars ((x 'int))))

  (ty-assert (-int) '(do (refine! x int) x)
             (envq :vars ((x 'x))
                   :types ((x (-int)))))

  (ty-assert (-empty) '(do (refine! x foo) x)
             (envq :vars ((x 'x))
                   :types ((foo (-lit 'foo))
                           (x   (-int)))))

  (ty-assert (-lit 'foo) '(do (refine! x foo) x)
             (envq :vars ((x 'x))
                   :types ((foo (-lit 'foo))
                           (x   (-or 'foo 'int)))))

  (ty-assert `(or ,(-lit 'foo) ,(-lit 'baz)) '(do (refine! x b) x)
             (envq :vars ((x 'x))
                   :types ((foo (-lit 'foo))
                           (bar (-lit 'bar))
                           (baz (-lit 'baz))
                           (a   (-or 'foo 'bar))
                           (b   (-or 'foo 'baz))
                           (x   (-or 'a 'b))))))


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

(test ref-checks-0
  ;; check a simple prop ref...
  (ty-assert (-lit 'foo) 'simple-ref *type-value-ref-env)
  ;; refine a simple prop ref...
  (ty-assert (-lit 'foo) '(do (refine! simple-ref foo) simple-ref)
             *type-value-ref-env)
  ;; refine a not-so-simple prop ref...
  (ty-assert (-lit 'foo) '(do (refine! simple-ref foo) alias-ref)
             *type-value-ref-env)
  ;; ref through an or...
  (ty-assert `(or ,(-lit 'foo) ,(-lit 'bar)) 'type
             *type-value-ref-env)
  ;; refine a prop ref into an or...
  (ty-assert (-lit 'foo) '(do (refine! type foo) type)
             *type-value-ref-env)
  ;; and eventually, propogate it correctly:
  (ty-assert (-lit 'baz) '(do (refine! type foo) value)
             *type-value-ref-env)
  (ty-assert (-lit 'baz) '(do (refine! type foo) (refine! value baz) value)
             *type-value-ref-env)
  (ty-assert (-empty) '(do (refine! type foo) (refine! value quux) value)
             *type-value-ref-env)
  )

(run! 'initial-inferences)


(defun chk (expr &optional (env *base-env*))
  (print-values
   (multiple-value-bind
         (ty ty-name env) (applied-ty expr env)
     (declare (ignore ty-name))
     ;; (pprint env)
     (values ty ":" (resolve ty env)))))

(defun chk2 (expr &optional (env *base-env*))
  (print-values
   (multiple-value-bind
         (ty ty-name env) (applied-ty expr env)
     (declare (ignore ty-name env))
     ;; (pprint env)
     (values ty))))

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

(chk '(do
       (type foo 'foo)
       (type a (obj type foo))
       (declare object a)
       (def x (get object type))
       x))

(chk '(do
       (type foo 'foo)
       (type a (obj type foo))
       (declare object a)
       (def x (get object type))
       (refine! x foo)
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type c (or a b))
       (declare object c)
       (def x (get object type))
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type c (or a b))
       (declare object c)
       (def x (get object type))
       (refine! x foo)
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type c (or a b))
       (declare object c)
       (def x (get object type))
       (def y (get object type))
       (refine! x foo)
       y))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type a (obj type foo))
       (type b (obj type bar))
       (type c (or a b))
       (declare object c)
       (declare object2 c)
       (def x (get object type))
       (def y (get object2 type))
       (refine! x foo)
       y))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (declare object c)
       (def x (get object type))
       (def y (get object data))
       (refine! x foo)
       y))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (def x (get (get object nested) type))
       (refine! x foo)
       x))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (def x (get (get object nested) type))
       (def y (get (get object nested) data))
       (refine! x foo)
       y))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (declare object2 d)
       (def x (get (get object nested) type))
       (def y (get (get object nested) data))
       (def z (get (get object2 nested) data))
       (refine! x foo)
       z))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (def nest (get object nested))
       (refine! nest a)
       (get nest type)))

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (def nest (get object nested))
       (def x (get nest type))
       (def y (get nest data))
       (refine! nest a)
       y)) ;;sigh....

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (def! nest (get object nested)) ;;sigh....
       (def x (get (get object nested) type))
       (def y (get (get object nested) data))
       (refine! nest a)
       y)) 

(chk '(do
       (type foo 'foo)
       (type bar 'bar)
       (type data-foo 'data-foo)
       (type data-bar 'data-bar)
       (type a (obj type foo data data-foo))
       (type b (obj type bar data data-bar))
       (type c (or a b))
       (type d (obj nested c))
       (declare object d)
       (declare object2 d)
       (def! nest (get object nested)) ;;sigh...
       (def x (get (get object nested) data))
       (def y (get (get object2 nested) data))
       (refine! nest a)
       y)) 
