(in-package :ty)
(setf *print-circle* t)

(def-suite initial-inferences)
(in-suite initial-inferences)

(defmacro print-values (form)
  `(let ((*print-circle* t))
    (pprint (multiple-value-list ,form))))

(defmacro ty-full-assert (type name effects form &body env)
  `(is (equalp (list ,type ,name ,effects) (multiple-value-list (ty-of ,form ,@env)))))

(defun env-do (&rest pairs)
  (bb env *base-env*
      alist (plist-alist pairs)
      (loop for (name . unparsed) in alist do
           (bb
             :mv (ty fx) (parse-type unparsed env)
             (setf env (apply-effects env (combine-effects (tfx name ty) fx)))))
      env))

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

(defmacro ty-assert (resolved-ty expr &optional (env '*base-env*))
  `(flet ((conc (expr)
            (multiple-value-bind
                  (ty ty-name env) (applied-ty expr ,env)
              (declare (ignore ty-name))
              ;; (pprint env)
              ;;(values ty ":" (resolve ty env))
              (concretize ty env))))
     (is (resolved-ty-equalp ,resolved-ty (conc ,expr)))))

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
  (ty-full-assert 'a nil nil
      'x
    (env :vars `((x . a))
         :types `((a . ,(-int)))))

  (ty-full-assert (-int) nil nil
      'x
    (env :vars `((x . ,(-int)))))

  ;; (ty-full-assert (-obj `((a . row-a))) 'a nil
  ;;     'x
  ;;   (env :vars `((x . a))
  ;;        :types `((a . ,(-obj '((a . row-a))))
  ;;                 (row-a . ,(-int)))))

  ;; (ty-assert (-int) 'x
  ;;            (envq :vars ((x 'ref-row-a))
  ;;                  :types ((a (-obj '((a . row-a))))
  ;;                          (row-a (-int))
  ;;                          (ref-row-a (-prop 'a 'a)))))

  ;; (ty-assert `(or ,(-int) ,(-lit 'foo)) 'x
  ;;            (envq :vars ((x 'x))
  ;;                  :types ((lit (-lit 'foo))
  ;;                          (x (-or 'int 'lit)))))

  (ty-assert (-int) 5)

  ;; (ty-assert `(obj ((a . ,(-int))))
  ;;            'x
  ;;            (envq :vars ((x 'x))
  ;;                  :types ((x (-objq (a int))))))

  ;; (ty-assert-unresolved (-prop 'x 'a) '(get x a)
  ;;                       (envq :vars ((x 'x))
  ;;                             :types ((x (-objq (a int))))))

  ;; (ty-assert (-int) '(get x a)
  ;;            (envq :vars ((x 'x))
  ;;                  :types ((x (-objq (a int))))))

  ;; (ty-assert `(or ,(-lit 'a-prop)
  ;;                 ,(-lit 'b-prop))
  ;;            '(get x a)
  ;;            (envq :vars ((x 'x))
  ;;                  :types ((a-prop (-lit 'a-prop))
  ;;                          (b-prop (-lit 'b-prop))
  ;;                          (a (-objq (a a-prop)))
  ;;                          (b (-objq (a b-prop)))
  ;;                          (x (-or 'a 'b)))))
  
  ;; (ty-assert (-lit 'b-prop)
  ;;            `(get y b)
  ;;            (envq :vars ((y 'a-prop))
  ;;                  :types
  ;;                  ((a (-objq (a b)))
  ;;                   (b (-objq (b lit-b-prop)))
  ;;                   (lit-b-prop (-lit 'b-prop))
  ;;                   (a-prop (-prop 'a 'a))
  ;;                   (b-prop (-prop 'b 'b)))))

  ;; (ty-assert (-lit 'b-prop)
  ;;            `(get (get x a) b)
  ;;            (envq :vars ((x 'a))
  ;;                  :types
  ;;                  ((a (-objq (a b)))
  ;;                   (b (-objq (b lit-b-prop)))
  ;;                   (lit-b-prop (-lit 'b-prop)))))

  )


(test basic-checks-1
  (ty-assert (-int) '(do x x)
             (envq :vars ((x 'int))))

  (when nil
    (ty-assert (-int) '(do (refine! x int) x)
               (envq :vars ((x 'int)))))

  (when nil
    (ty-assert (-int) '(do (refine! x int) x)
               (envq :vars ((x 'x))
                     :types ((x (-int))))))

  (when nil
    (ty-assert (-empty) '(do (refine! x foo) x)
               (envq :vars ((x 'x))
                     :types ((foo (-lit 'foo))
                             (x   (-int))))))

  (when nil
    (ty-assert (-lit 'foo) '(do (refine! x foo) x)
               (envq :vars ((x 'x))
                     :types ((foo (-lit 'foo))
                             (x   (-or (-lit 'foo) (-int) *base-env*))))))

  (when nil
    (ty-assert `(or ,(-lit 'foo) ,(-lit 'baz))
               '(do
                 (type a (or 'foo 'bar))
                 (type b (or 'foo 'baz))
                 (type x (or a b))
                 (declare x x)
                 (refine! x b) x)))

  )


;; (defparameter *type-value-ref-env
;;   (env :vars `((type . type-ref)
;;                (value . value-ref)
;;                (simple-ref . foo-ref)
;;                (alias-ref  . foo-ref))
;;        :types
;;        `((foo . ,(-lit 'foo))
;;          (bar . ,(-lit 'bar))
;;          (baz . ,(-lit 'baz))
;;          (quux . ,(-lit 'quux))
;;          (obj-foo . ,(-obj '((type . foo)
;;                              (value . baz))))
;;          (obj-bar . ,(-obj '((type . bar)
;;                              (value . quux))))
;;          (my-obj . ,(-or 'obj-foo 'obj-bar))
;;          (foo-ref . ,(-prop 'obj-foo 'type))
;;          (type-ref . ,(-prop 'my-obj 'type))
;;          (value-ref . ,(-prop 'my-obj 'value)))))



;; (test ref-checks-0
;;   ;; check a simple prop ref...
;;   (ty-assert (-lit 'foo) 'simple-ref *type-value-ref-env)
;;   ;; refine a simple prop ref...
;;   (ty-assert (-lit 'foo) '(do (refine! simple-ref foo) simple-ref)
;;              *type-value-ref-env)
;;   ;; refine a not-so-simple prop ref...
;;   (ty-assert (-lit 'foo) '(do (refine! simple-ref foo) alias-ref)
;;              *type-value-ref-env)
;;   ;; ref through an or...
;;   (ty-assert `(or ,(-lit 'foo) ,(-lit 'bar)) 'type
;;              *type-value-ref-env)
;;   ;; refine a prop ref into an or...
;;   (ty-assert (-lit 'foo) '(do (refine! type foo) type)
;;              *type-value-ref-env)
;;   ;; and eventually, propogate it correctly:
;;   (ty-assert (-lit 'baz) '(do (refine! type foo) value)
;;              *type-value-ref-env)
;;   (ty-assert (-lit 'baz) '(do (refine! type foo) (refine! value baz) value)
;;              *type-value-ref-env)
;;   (ty-assert (-empty) '(do (refine! type foo) (refine! value quux) value)
;;              *type-value-ref-env)
;;   )



(defun chk (expr &optional (env *base-env*))
  (print-values
   (multiple-value-bind
         (ty ty-name env) (applied-ty expr env)
     (declare (ignore ty-name))
     ;; (pprint env)
     (concretize ty env))))

(defun see (expr &optional (env *base-env*))
  (multiple-value-list (applied-ty expr env)))

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


(when nil
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
           (value-ref . ,(-prop 'my-obj 'value))))))

(defparameter *var-env-0
  (env-do
   'foo ''foo 'bar ''bar 'baz ''baz 'quux ''quux
   'obj-foo '(obj type foo value baz)
   'obj-bar '(obj type bar value quux)
  ))

(test var-tests-0

  (ty-assert (-lit 'foo) '(do (declare x foo) x) *var-env-0)

  (when nil
    (ty-assert (-lit 'foo )
               '(do
                 (declare x foo)
                 (refine! x foo)
                 x)
               *var-env-0))

  (when nil
    (ty-assert (-empty)
               '(do
                 (declare x foo)
                 (declare y foo)
                 (refine! x bar)
                 x)
               *var-env-0))

  (when nil
    (ty-assert (-lit 'foo)
               '(do
                 (declare x foo)
                 (declare y foo)
                 (refine! x bar)
                 y)
               *var-env-0))
  
  (when nil
    (ty-assert (-lit 'bar)
               '(do
                 (type t (or foo bar))
                 (declare x t)
                 (refine! x bar)
                 x)
               *var-env-0))

  (when nil
    (ty-assert `(or ,(-lit 'foo) ,(-lit 'bar))
               '(do
                 (type t (or foo bar))
                 (declare x t)
                 (declare y t)
                 (refine! x bar)
                 y)
               *var-env-0)))


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

  (when nil
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
       x)))

  (when nil
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
       y)))

  (ty-assert
   (-lit 'foo)
   '(do
     (type foo 'foo)
     (type a (obj type foo))
     (declare object a)
     (def x (get object type))
     x))

  (when nil
    (ty-assert
     (-lit 'foo)
     '(do
       (type foo 'foo)
       (type a (obj type foo))
       (declare object a)
       (def x (get object type))
       (refine! x foo)
       x)))

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

  (when nil
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
       x)))

  (when nil ;;; FIXME
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
       y)))

  (when nil
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
       y)))

  (when nil ;; FIXME
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
       y)))

  (when nil
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
       x)))

  (when nil ;; FIXME
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
       y)))

  (when nil
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
       z)))

  (when nil
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
       (get nest type))))

  (when nil ;;FIXME
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
       y))))

(when nil
  (defparameter *expand-or-types-env
    (envq :vars ((x 'x))
          :types ((foo (-lit 'foo))
                  (bar (-lit 'bar))
                  (baz (-lit 'baz))
                  (a   (-or 'foo 'bar))
                  (b   (-or 'foo 'baz))
                  (c   (-or 'baz 'foo))
                  (x   (-or 'a 'b)))) ))

(when nil
  (test expand-or-types-0
    (let* ((env *expand-or-types-env)
           (expected (list (-lit 'baz) (-lit 'bar) (-lit 'foo)))
           (result (expand-or-type (-or 'a 'b) env)))
      (is (equalp expected result)))

    (is (ty-equal (-or 'foo 'bar) (-or 'bar 'foo) *expand-or-types-env))
    (is (ty-equal (-or 'a 'baz) (-or 'b 'bar) *expand-or-types-env))))

(when nil
  (test contract-or-types-0
    (flet ((test-or-type-creation (&rest types)
             (multiple-value-bind (ty fx) (create-or-type types *base-env*)
               (let* ((env (apply-effects *base-env* fx))
                      (expansion
                       (typecase ty
                         (-or (expand-or-type ty env))
                         (t   (list ty)))))
                 (flet ((teq (a b) (ty-equal a b env)))
                   (unordered-list-equal expansion
                                         (remove-duplicates types :test #'teq)
                                         :test #'teq))))))
      (is (test-or-type-creation (-lit 'a)))
      (is (test-or-type-creation (-lit 'a) (-lit 'b)))
      (is (test-or-type-creation (-lit 'a) (-lit 'b) (-lit 'c)))
      (is (test-or-type-creation (-lit 'a) (-lit 'b) (-lit 'c) (-lit 'd)))

      (is (test-or-type-creation (-lit 'a) (-lit 'b) (-lit 'a) (-lit 'b)))
      (is (test-or-type-creation (-lit 'a) (-lit 'a)))
      )
    ))

(when nil
  (defparameter *recursive-cons-type-env
    (envq :types ((null (-lit 'null))
                  (next-type (-or 'intlist 'null))
                  (intlist (-objq (values int) (next next-type)))
                  (foo (-lit 'foo))
                  (bar (-lit 'bar))))))

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

(when t
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
    
    (when nil
      (ty-assert (circ `(obj ((values . ,(-int))
                              (next . (or :1 ,(-lit 'null))))))
                 '(do
                   (declare x intlist)
                   x)
                 *recursive-cons-type-env))

    (when nil
      (ty-assert (circ `(obj ((next . (or :1 ,(-lit 'null)))
                              (values . ,(-int)))))
                 '(do
                   (declare x intlist)
                   x)
                 *recursive-cons-type-env))

    (when nil
      (ty-assert (circ `(or ,(-lit 'bar) ,(-lit 'foo) :1))
                 '(do
                   (type obj-or-foo (or foo obj-or-bar))
                   (type obj-or-bar (or bar obj-or-foo))
                   (declare x obj-or-bar)
                   x)
                 *recursive-cons-type-env))

    (when nil
      (ty-assert (circ `(obj ((next . (or :1 ,(-lit 'null)))
                              (val . ,(-int)))))
                 '(do
                   (type intlist (obj val int next (or intlist 'null)))
                   (declare x intlist)
                   x)))
    ))

;; (run! 'recursive-types-0)
;; (run! 'var-tests-1)
(run! 'initial-inferences)

;; #1=(OR [LIT BAR] [LIT FOO] #1#)
;; (chk '(do
;;        (type obj-or-foo (or foo obj-or-bar))
;;        (type obj-or-bar (or bar obj-or-foo))
;;        (declare x obj-or-bar)
;;        x) 
;;      *recursive-cons-type-env)

;; (chk '(do
;;        (declare x intlist)
;;        x)
;;      *recursive-cons-type-env)

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



(when nil
  (chk '(do
         (declare x intlist)
         x)
       *recursive-cons-type-env))

(when nil
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
         y))) 

(when nil
  (chk '(do
         (when nil)
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
         y))) 

(chk '(do
       (type foo 'foo)
       (type a (obj type foo))
       (type p (prop a type))
       (declare x p)
       x))


(chk '(do
       (type intlist (obj val int next (or intlist 'null)))
       (declare x intlist)
       x))

(when nil
  (chk '(do
         (type a (obj type 'a next (or b 'null)))
         (type b (obj type 'b next (or b 'null)))
         (declare x b)
         x)))

(when nil
  (chk '(do
         (type a (obj type 'a next (or b 'null)))
         (type b (obj type 'b next (or a 'null)))
         (type c (or a b))
         (declare x c)
         x)))

;;; need to assert that this even runs...
(chk '(do
       (type a1 (obj type 'a next (or a1 'null)))
       (type a2 (obj type 'a next (or a2 'null)))
       (type b (or a1 a2))
       (declare x b)
       x))

(chk '(do
       (type a1 (obj type 'a next (or (obj type 'end)
                                      (obj type 'link next a1))))
       (type a2 (obj type 'a next (or (obj type 'end)
                                      (obj type 'link next a2))))
       (type b (or a1 a2))
       (declare x b)
       x))

(chk '(do
       (type a1 (obj type 'a next (or (obj type 'end)
                                      (obj type 'link next a1))))
       (type a2 (obj type 'a next (or (obj type 'link next a2)
                                      (obj type 'end))))
       (type b (or a1 a2))
       (declare x b)
       x))

(when nil
  (chk '(do
         (type a1 (obj type 'a next (or (obj type 'end)
                                        (obj type 'link next a2))))
         (type a2 (obj type 'a next (or (obj type 'link next a1)
                                        (obj type 'end))))
         (type b (or a1 a2))
         (declare x b)
         x)))

(when nil
  (chk '(do
         (type a1 (obj type 'a next (or (obj type 'end)
                                        (obj type 'link next a2))))
         (type a2 (obj type 'a next (or (obj type 'link next a1)
                                        (obj type 'end))))
         (type b (or a1 a2))
         (declare x b)
         (refine! x a2)
         x)))

(see '(do
       (type a (or 'a 'b))
       (declare x a)
       x))

(when nil
  (chk '(do
         (type a1 (obj type 'a next (or (obj type 'end)
                                        (obj type 'link next a2))))
         (type a2 (obj type 'a next (or (obj type 'link next a1)
                                        (obj type 'end))))
         (type-equal? a1 a2))))

(chk
 '(do
   (type intlist (obj val int next (or intlist 'null)))
   (declare x intlist)
   x))

(see '(do
       (type a (obj a 'a b 'b))
       (declare x a)
       (def y (get x a))
       (def z (get x b))
       z))

(print (ty-of '(do
                (type a (or 'a 'b 'c))
                (declare x a)
                (refine (x 'b) x))
              *base-env*))

(print (ty-of '(do
                (type a (obj type 'a data 'a-data))
                (type b (obj type 'b data 'b-data))
                (type c (or a b))
                (declare x c)
                (def y (get x type))
                (def z (get x data))
                (refine (x 'a) y))
              *base-env*))

(ty-of '(do
         (type a (obj type 'a data 'a-data))
         (type b (obj type 'b data 'b-data))
         (type c (or a b))
         (declare x c)
         (def y (get x type))
         (def z (get x data))
         (refine (y 'a) z))
       *base-env*)
