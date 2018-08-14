(in-package :ty)
(setf *print-circle* t)

(def-suite initial-inferences)
(in-suite initial-inferences)

(defmacro print-values (form)
  `(let ((*print-circle* t))
    (print (multiple-value-list ,form))))

(defmacro ty-full-assert (type name effects form &body env)
  `(is (equalp (list ,type ,name ,effects) (multiple-value-list (ty-of ,form ,@env)))))

(defun ty-assert-unresolved (unresolved-ty expr &optional (env *base-env*))
  (is (equalp unresolved-ty
              (multiple-value-bind
                    (ty ty-name env) (applied-ty expr env)
                (declare (ignore ty-name env))
                ty))))

(defun resolved-ty-equalp (a b)
  (let (seen)
    (labels
        ((car-cdr-eq (a b)
           (and (eq (car a) (car b))
                (eq (cdr a) (cdr b))))
         (compared? (a b)
           (member (cons a b) seen :test #'car-cdr-eq))
         (row-equal (a b)
           (and (eq (car a) (car b))
                (ty-equalp (cdr a) (cdr b))))
         (ty-equalp (a b)
           (when (eq (type-of a) (type-of b))
             (typecase a
               (list
                (when (eq (car a) (car b))
                  (if (compared? a b)
                      ;; I'm too tired to figure out if this is correct lol
                      (progn
                        ;; (format t "compared.")
                        t)
                      (progn
                        (push (cons a b) seen)
                        (ecase (car a)
                          (or  (unordered-list-equal (cdr a) (cdr b)
                                                     :test #'ty-equalp))
                          (obj (unordered-list-equal (second a) (second b)
                                                     :test #'row-equal)))))))
               (t (equalp a b))))))
      (ty-equalp a b))))

(defun ty-assert (resolved-ty expr &optional (env *base-env*))
  (is (resolved-ty-equalp resolved-ty
                          (multiple-value-bind
                                (ty ty-name env) (applied-ty expr env)
                            (declare (ignore ty-name))
                            ;; (pprint env)
                            ;;(values ty ":" (resolve ty env))
                            (concretize ty env)))))

(defun ty-assert-safe (resolved-ty expr &optional (env *base-env*))
  ;; the not not is to keep 5am from barfing on circular structures
  (is (not (not (resolved-ty-equalp resolved-ty
                                    (multiple-value-bind
                                          (ty ty-name env) (applied-ty expr env)
                                      (declare (ignore ty-name))
                                      ;; (pprint env)
                                      ;;(values ty ":" (resolve ty env))
                                      (concretize ty env)))))))

(defun ty-assert-not (resolved-ty expr &optional (env *base-env*))
  (is (not (resolved-ty-equalp resolved-ty
                               (multiple-value-bind
                                     (ty ty-name env) (applied-ty expr env)
                                 (declare (ignore ty-name))
                                 ;; (pprint env)
                                 ;;(values ty ":" (resolve ty env))
                                 (concretize ty env))))))

(defun -ty-assert (resolved-ty expr &optional (env *base-env*))
  (resolved-ty-equalp resolved-ty
          (multiple-value-bind
                (ty ty-name env) (applied-ty expr env)
            (declare (ignore ty-name))
            ;; (pprint env)
            ;;(values ty ":" (resolve ty env))
            (concretize ty env))))

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

  (ty-assert `(obj ((a . ,(-int))))
             'x
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



(defun chk (expr &optional (env *base-env*))
  (print-values
   (multiple-value-bind
         (ty ty-name env) (applied-ty expr env)
     (declare (ignore ty-name))
     ;; (pprint env)
     (concretize ty env))))

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

(test var-tests-0

  (ty-assert (-lit 'foo) '(do (declare x foo) x) *var-env-0)

  (ty-assert (-lit 'foo )
             '(do
               (declare x foo)
               (refine! x foo)
               x)
             *var-env-0)

  (ty-assert (-empty)
             '(do
               (declare x foo)
               (declare y foo)
               (refine! x bar)
               x)
             *var-env-0)

  (ty-assert (-lit 'foo)
             '(do
               (declare x foo)
               (declare y foo)
               (refine! x bar)
               y)
             *var-env-0)
  
  (ty-assert (-lit 'bar)
             '(do
               (type t (or foo bar))
               (declare x t)
               (refine! x bar)
               x)
             *var-env-0)

  (ty-assert `(or ,(-lit 'foo) ,(-lit 'bar))
             '(do
               (type t (or foo bar))
               (declare x t)
               (declare y t)
               (refine! x bar)
               y)
             *var-env-0))


(test var-tests-1
  (ty-assert
   (-lit 'foo)
   '(do
     (type foo 'foo)
     (type a (obj type foo))
     (type p (prop a type))
     (declare x p)
     x))

  (ty-assert
   `(or ,(-lit 'foo) ,(-lit 'bar))
   '(do
     (type foo 'foo)
     (type bar 'bar)
     (type a (obj type foo))
     (type b (obj type bar))
     (type p-a (prop a type))
     (type p-b (prop b type))
     (type p (or p-a p-b))
     (declare x p)
     x))

  (ty-assert
   (-lit 'foo)
   '(do
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

  (ty-assert
   `(or ,(-lit 'foo) ,(-lit 'bar))
   '(do
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

  (ty-assert
   (-lit 'foo)
   '(do
     (type foo 'foo)
     (type a (obj type foo))
     (declare object a)
     (def x (get object type))
     x))

  (ty-assert
   (-lit 'foo)
   '(do
     (type foo 'foo)
     (type a (obj type foo))
     (declare object a)
     (def x (get object type))
     (refine! x foo)
     x))

  (ty-assert
   `(or ,(-lit 'foo) ,(-lit 'bar))
   '(do
     (type foo 'foo)
     (type bar 'bar)
     (type a (obj type foo))
     (type b (obj type bar))
     (type c (or a b))
     (declare object c)
     (def x (get object type))
     x))

  (ty-assert
   (-lit 'foo)
   '(do
     (type foo 'foo)
     (type bar 'bar)
     (type a (obj type foo))
     (type b (obj type bar))
     (type c (or a b))
     (declare object c)
     (def x (get object type))
     (refine! x foo)
     x))

  (ty-assert
   (-lit 'foo)
   '(do
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

  (ty-assert
   `(or ,(-lit 'foo) ,(-lit 'bar))
   '(do
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

  (ty-assert
   (-lit 'data-foo)
   '(do
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

  (ty-assert
   (-lit 'foo)
   '(do
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

  (ty-assert
   (-lit 'data-foo)
   '(do
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

  (ty-assert
   `(or ,(-lit 'data-foo) ,(-lit 'data-bar))
   '(do
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

  (ty-assert
   (-lit 'foo)
   '(do
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

  (ty-assert
   (-lit 'data-foo)
   '(do
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
     y)))

(defparameter *expand-or-types-env
  (envq :vars ((x 'x))
        :types ((foo (-lit 'foo))
                (bar (-lit 'bar))
                (baz (-lit 'baz))
                (a   (-or 'foo 'bar))
                (b   (-or 'foo 'baz))
                (c   (-or 'baz 'foo))
                (x   (-or 'a 'b)))) )

(test expand-or-types-0
  (let* ((env *expand-or-types-env)
        (expected (list (-lit 'baz) (-lit 'bar) (-lit 'foo)))
        (result (expand-or-type (-or 'a 'b) env)))
    (is (equalp expected result)))

  (is (ty-equal (-or 'foo 'bar) (-or 'bar 'foo) *expand-or-types-env))
  (is (ty-equal (-or 'a 'baz) (-or 'b 'bar) *expand-or-types-env)))

(test contract-or-types-0
  (flet ((test-or-type-creation (&rest types)
           (multiple-value-bind (ty fx) (create-or-type types *base-env*)
             (let* ((env (apply-effects *base-env* fx))
                    (expansion
                     (typecase ty
                       (-or (expand-or-type ty env))
                       (t   (list ty)))))
               (flet ((teq (a b) (ty-equal a b env)))
                 (expanded-or-types-equal expansion
                                          (remove-duplicates types :test #'teq)
                                          env))))))
    (is (test-or-type-creation (-lit 'a)))
    (is (test-or-type-creation (-lit 'a) (-lit 'b)))
    (is (test-or-type-creation (-lit 'a) (-lit 'b) (-lit 'c)))
    (is (test-or-type-creation (-lit 'a) (-lit 'b) (-lit 'c) (-lit 'd)))

    (is (test-or-type-creation (-lit 'a) (-lit 'b) (-lit 'a) (-lit 'b)))
    (is (test-or-type-creation (-lit 'a) (-lit 'a)))
    )
  )

(defparameter *recursive-cons-type-env
  (envq :types ((null (-lit 'null))
                (next-type (-or 'intlist 'null))
                (intlist (-objq (values int) (next next-type)))
                (foo (-lit 'foo))
                (bar (-lit 'bar)))))

(defun replace-1s (self)
  (labels ((walk (list)
             (loop for cons on list do
                  (when (listp (car cons)) (walk (car cons)))
                  (when (eq (car cons) :1) (setf (car cons) self))
                  (when (eq (cdr cons) :1) (setf (cdr cons) self)))))
    (walk self)
    self))

(defun circ (template)
  (replace-1s (copy-tree template)))

(test recursive-types-0
  (setf *print-circle* t)

  (bb a (circ `(or ,(-lit 'a) :1))
      b (circ `(or ,(-lit 'a) :1))
      (is (resolved-ty-equalp a b)))

  (bb a  (circ `(obj ((values . ,(-int))
                      (next . (or :1 ,(-lit 'null))))))
      b  (circ `(obj ((values . ,(-int))
                      (next . (or :1 ,(-lit 'null))))))
      (is (resolved-ty-equalp a b)))
  (bb
    a (circ `(or ,(-lit 'bar) (or ,(-lit 'foo) :1)))
    b (circ `(or ,(-lit 'bar) (or ,(-lit 'foo) :1)))
    (is (resolved-ty-equalp a b)))

  (bb
    a (circ `(or ,(-lit 'bar) (or ,(-lit 'foo) :1)))
    b (circ `(or ,(-lit 'bar) (or ,(-lit 'foo) :1)))
    (is (resolved-ty-equalp a b)))

  (is (not (resolved-ty-equalp
            (circ `(or ,(-lit 'bar) (or (-lit 'foo) :1)))
            (circ `(or ,(-lit 'bar) (or ,(-lit 'foo) :1))))))

  (is (resolved-ty-equalp
       (circ `(or ,(-lit 'bar) ,(-lit 'foo) :1))
       (circ `(or ,(-lit 'bar) ,(-lit 'foo) :1))))
  
  (ty-assert (circ `(obj ((values . ,(-int))
                          (next . (or :1 ,(-lit 'null))))))
             '(do
               (declare x intlist)
               x)
             *recursive-cons-type-env)

  (ty-assert (circ `(obj ((next . (or :1 ,(-lit 'null)))
                          (values . ,(-int)))))
             '(do
               (declare x intlist)
               x)
             *recursive-cons-type-env)

  (ty-assert (circ `(or ,(-lit 'bar) ,(-lit 'foo) :1))
                  '(do
                    (type obj-or-foo (or foo obj-or-bar))
                    (type obj-or-bar (or bar obj-or-foo))
                    (declare x obj-or-bar)
                    x)
                  *recursive-cons-type-env))

;; (run! 'recursive-types-0)
(run! 'initial-inferences)

;; #1=(OR [LIT BAR] [LIT FOO] #1#)
(chk '(do
       (type obj-or-foo (or foo obj-or-bar))
       (type obj-or-bar (or bar obj-or-foo))
       (declare x obj-or-bar)
       x) 
     *recursive-cons-type-env)

(chk '(do
       (declare x intlist)
       x)
     *recursive-cons-type-env)

(chk '(do
       (type foo (or 'a 'b))
       (declare x foo)
       x))

(chk '(do
       (type foo (or 'a 'b))
       (declare x foo)
       x))

(chk '(do
        (type foo 'foo)
        (type bar 'bar)
        (type data-foo 'data-foo)
        (type data-bar 'data-bar)
        (type a (obj type foo data data-foo))
        (type b (obj type bar data data-bar))
        (type c (or a b))
        (declare x a)
        x
        ))



(chk '(do
       (declare x intlist)
       x)
     *recursive-cons-type-env)

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
       ;; (def! nest (get object nested)) ;;sigh....
       (def nest (get object nested)) ;;sigh....
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
