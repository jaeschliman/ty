(ql:quickload :alexandria)
(ql:quickload :fiveAM)
(defpackage :ty (:use :cl :alexandria :5am))
(in-package :ty)

(defmacro fn (args &body body) `(lambda ,args ,@body))

(defun %bb-thread-clauses (clauses)
  (let (threads)
    (loop while clauses do
         (let ((it (pop clauses)))
           (cond
             ((and (eq it :db) clauses)
              (let* ((vals (pop clauses))
                     (form (pop clauses)))
                (push (list 'destructuring-bind vals form) threads)))
             ((and (eq it :mv) clauses)
              (let* ((vals (pop clauses))
                     (form (pop clauses))
                     (ignore (when (member '_ vals)
                               (list '(declare (ignore _))))))
                (push (list* 'multiple-value-bind vals form ignore) threads)))
             ((and (symbolp it) clauses)
              (let ((var it)
                    (val (pop clauses)))
                (push (list 'let `((,var ,val))) threads)))
             (t (push (list 'progn it) threads)))))
    (reduce (lambda (acc next)
              (setf (cdr (last next)) (list acc))
              next)
            threads)))

;; inspired by ron garret's ergolib
(defmacro bb (&body clauses)
  (%bb-thread-clauses (copy-tree clauses)))

(defun alist-get (sym alist &key (test 'eq))
  (cdr (assoc sym alist :test test)))

(defun rev-assoc (value alist &key (test 'equalp))
  (loop for (key . val) in alist do
       (when (funcall test value val)
         (return (cons key val)))))

(defun rev-alist-get (value alist &key (test 'equalp))
  (car (rev-assoc value alist :test test)))

(defun unordered-list-equal (a b &key (test 'equalp))
  (and (= (length a) (length b))
       (null (set-difference a b :test test))))

(defstruct env
  vars types errors)

(defstruct (ty (:constructor nil)) name)
(defmethod print-object ((self ty) stream)
  (format stream "[~A]" (ty-name self)))

(deftype tyref () '(or ty symbol))

(defmacro defty (name print-name &rest members)
  (bb
    name-and-super (ensure-list name)
    name (first name-and-super)
    super (or (second name-and-super) 'ty)
    args (mapcar #'ensure-car members)
    `(defstruct (,name (:include ,super (name ',print-name))
                       (:constructor ,name ,args))
       ,@members)))

(defty -empty empty)

(defty -int int)
(defty -sym sym)
(defty (-lit -sym) lit (value nil :type symbol))
(defmethod print-object ((self -lit) stream)
  (format stream "[~A ~S]" (ty-name self) (-lit-value self)))

(defty -bool bool)
(defty (-true -bool) true)
(defty (-false -bool) false)

(defty -or or
  (a nil :type tyref)
  (b nil :type tyref)
  (env nil :type env)) 

(defmethod print-object ((self -or) stream)
  (format stream "[~A ~A ~A]" (ty-name self) (-or-a self) (-or-b self)))

(defty -obj object
  (rows nil :type list) ;;rows is an alist of (sym . tyref)
  (env nil :type env)) 

(defmethod print-object ((self -obj) stream)
  (format stream "[~A (~{~A~})]" (ty-name self) (-obj-rows self)))

(defty -prop prop
  (var nil :type symbol) ;;TODO: change to VAR
  (prop nil :type symbol)
  (env nil :type env))
(defun -prop-ty (prop)
  (alist-get (-prop-var prop) (env-vars (-prop-env prop))))

(defmethod print-object ((self -prop) stream)
  (format stream "[~A ~A.~A]" (ty-name self) (-prop-var self) (-prop-prop self)))

(defty -var var ;;TODO: delete me
  (ref nil :type tyref))

(defmethod print-object ((self -var) stream)
  (format stream "<~A : ~A>" (ty-name self) (-var-ref self)))

(defty -name name
  (print-name nil :type symbol)
  (ty nil :type tyref)
  (env nil :type env))
(defmethod print-object ((self -name) stream)
  (format stream "[~A : ~A]" (-name-print-name self) (-name-ty self)))


(defty -unknown unknown)

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

;; self-referential/recursive types?
(type intlist (obj value int next (or intlist null)))

;; difficulty here will be that `or` eagerly evaluates its types...
;; and what about mutually recursive types?

;; could have the `lookup` of an unkown type return a special new
;; type `unknown` that is never ty-equal to any other type,
;; since the eager evaluation of `or` is to simplify the form, this
;; could work. it would, however, introduce the possibility that
;; that an or could contain duplicate types... although this should
;; be alleviated when it is again expanded later on...
;; seems like like a good solution at first glance.

;; and what about `resolve`ing them lol

;; also eventually, parameterized types:
(type (listof x) (obj value x next (or (listof x) null)))

;; also, what about resolving objects, haha
;; ....and.... comparing them!
;; object time.

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
second-and-half goal...
if! with refinements!
(do
 (type foo (or (obj type 'a data 'foo)
               (obj type 'b data 'bar)))
 (declare x foo)
 (if (eq (get x type) 'a)
     (get x data)
     (get x type)))
;; => (or 'foo 'b)

this will be tough, how do we combine the fx of the two branches?
we could disallow rebinding side effects, but how then do we refine?
also, how to do the refine-not (the else branch)

time to revisit how refine! works...

ok... maybe this whole -prop -var tangle is due to a mistake...
-prop takes a typename and an object key...
I guess this makes sense....
if you want to have, like, $Prop<Foo, 'x'> like flow does...
but then we end up narrowing types... what we should be doing is
narrowing the types of variable bindings, not types themselves...
that is, introducing new narrow types and rebinding vars appropriately.
I mean I guess this is what the -var type was attempting to mix in to things...
ok, fair sized amount of work to correct this, I guess...
at least I'll able to get rid of the -var nonsense.

so perhaps it should be illegal to rebind type names.
however having types (-prop refs) dependent on variable bindings, which can change,
means that the /meaning/ of a type name can change, which is bad...
but also kind of how this whole things is designed lol...

so perhaps -prop remains pointed at a type name, but refine works over variable
bindings, so refining a -prop will mean introducing a new -prop type...
how then will this propagate to other -prop refs?

I guess maybe type-level $Prop<Foo, 'x'> should be saved for another time
and have different semantics...

so perhaps we /should/ have a variable name in the type system?
now things get really tangled...
e.g. how do you handle shadowing? (start numbering scopes as we go inward?)

also this doesnt remove the need for answering the big open question here, which is
how do we combine the effects of the two if branches?
how do we extract the final type of each branch without pulling in mutations?
this will be a question when it comes to function definitions as well...

perhaps there can be some sort of 'simplify this type given this list
of variable bindings', where we search through any prop refs, and if
they are found to match a given variable name, then we must 'realize'
or 'concretize' that prop type to allow passing it up to the parent scope

that could work, I think...
now there is the question what about prop-refs to expressions?
do we introduce unique var names?

so I guess the plan is, we should be able to combine the type effects
of both if branches without worry, since re-binding type names will now
be disallowed. however, since the meaning of a -prop type can change when
a variable is rebound, when propagating the type effects out of a scope,
we will need to check whether a: there are any variable bindings in the fx,
and b: whether there are any references to those variable bindings in the fresh types
of those fx. if both a and b are true, then we will need to substitute all types in
the fx which transitively refer to the given variable bindings with new types
containing the 'realized' type of that prop ref given the new variable bindings.
this ensures that var 'mutations' will not escape the given scope i.e. will only
propagate inwards...

this does not, however solve the problem of a potentially useless mass of type
introductions escaping the branch. perhaps we also need some sort of garbage
collector for the effects, that walks from the 'primary' return type and only
pulls in effects which are referenced along the way... ugh...
this smells like a design problem...
time to review ty-of... perhaps we are introducing too many types from ty-of...
I mean it would be nice, for example, to allow lexical type definitions without
fear of them escaping when we apply the needed introductions for a given type...
I guess that's partially the shadowing problem again (mentioned above) and then
partially the garbage collection problem...
it would be nice if there were just fewer type names floating around...
I guess we could have some sort of canonical mapping of type representation to names...
I mean I guess it would be nice if we could stop naming types so much anyway...
but how then recursive types? 
I mean, I guess the point is that if we could return types as /values/
instead of a sequence of name/value pairs, that would simplify things alot...
but would then need some sort of -ref type... I'm not sure that really simplifies
things too much... 

upon further reflection, for v2 of this,
/a type is like a closure/
it should carry within it a link to its definition environment if needed,
so that it can be 'evaluated'


now the annoying part: refining vars.
so while a type is a like a closure, we need a dynamic binding environment
for vars to handle /refining/.
so it looks like `refine!' should have been a form more like `let',
e.g.
(refine (x int)
  y)

where within the body of `refine' we bind some special var that overrides
variable type lookups e.g. `*refinements*'

any type which will then escape the body of refine (its final form) will
then (if needed) be annotated with the new (-refine alist ty) type, who's
definition is such that when extracting the inner type, it is evaluated
under the refinement bindings in alist.

possible issues:
- what about variable shadowing?
  this will have to be addressed eventually
  by no longer using symbols to represent a binding. we'll need some sort of
  object, be it a cons or whatever.
- what about `concretize', which uses a queue instead of recursion?
  will have to wrap calls to enqueue to preserve dynamic environment :P
- what about nesting refinements to the same binding?
  rather than simply consing onto the front of `*refinements*', want to
  `and' the existing types together

further thoughts:
how does this address propagation, which is the real goal?
so:
  a = {type:foo, data:bar } | {type: baz, data:quux};
  {type, data} = a;
  refine (type = foo) {
    data; //should eq bar
  } 
here, type := (prop a type)
  where a = (or {type foo} {type baz})
so we seek to refine (prop a type) to type 'foo having determined that it is possible,
which means a must be one of (ignoring -var and -name):
  an -obj type (we are done)
  a -prop type which resolves to one of these cases
  an -or type which contains multiple of these cases
ignoring the -prop case, which seems a little complicated for now,
we have both the var name and the -or to which it refers. we can therefore
simply narrow the -or type, and return a cons of (var . narrowed-ty)
what about the -prop case? I'll need an example to work from...
instinct says it may be enough to simply recurse in that case


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

(defstruct effects
  vars types errors)

(defmethod lookup-var ((var symbol) env)
  (bb it (ensure-car (alist-get var (env-vars env)))
      (assert it)
      it))

(defmethod lookup-var-meta ((var symbol) env)
  (cdr (ensure-list (alist-get var (env-vars env)))))

(defmethod lookup-type ((ty ty) env &key allow-unknowns)
  (declare (ignore env allow-unknowns))
  ty)

(defmethod lookup-type ((ty-name symbol) env &key allow-unknowns)
  (or
   (alist-get ty-name (env-types env))
   (if allow-unknowns
       (-unknown)
       (assert nil))))

(defun rev-lookup-type (ty env)
  (if-let (pair (rev-assoc ty (env-types env)))
    (values (cdr pair) (car pair))
    (values nil nil)))

(defparameter *base-env*
  (make-env :vars `((true . ,(-true))
                    (false . ,(-false)))
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
(defun v-metafx (var ty meta)
  (make-effects :vars (list (cons var (cons ty meta)))))
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

;;; --- or types

(defmethod shallow-expand-or-type ((ty -or) env)
  (let (expanded)
    (flet ((expand (tyname)
             (let ((it (lookup-type-through-vars tyname env)))
               (typecase it
                 (-or (setf expanded
                            (append (shallow-expand-or-type it env) expanded)))
                 (t (push tyname expanded))))))
      (expand (-or-a ty))
      (expand (-or-b ty))
      (remove-duplicates expanded :test 'eq))))

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

(defun ensure-type-names (named-list-of-types env &key (key #'identity))
  (declare (ignore env))
  (bb fx nil
      names (loop for entry in named-list-of-types
               for (name . ty) = (funcall key entry)
               collect
                 (progn
                   (unless name
                     (bb tyname (make-type-name)
                         (setf fx (combine-effects (tfx tyname ty) fx)
                               name tyname)))
                   name))
      (values names fx)))

(defun create-named-list-of-or-types (named-list-of-types env)
  (labels ((ensure-named (it)
             (if (consp it) it (cons nil it)))
           (combine1 (a b)
             (bb
               ty (-or (cdr a) (cdr b) env)
               (values (cons nil ty) nil)))
           (combine (a b &rest more)
             (if more
                 (bb :mv (ty fx)   (combine1 a b)
                     :mv (ty2 fx2) (apply #'combine ty more)
                     (values ty2 (combine-effects fx2 fx))) 
                 (combine1 a b)))
           (teq (a b)
             (unless (or (symbolp a) (symbolp b))
               (ty-equal a b env))))
    (let ((named-types (remove-duplicates named-list-of-types
                                          :test #'teq :key #'cdr)))
      (if (= 1 (length named-types))
          (values (cdr (first named-types)) nil)
          (bb :mv (named-ty fx) (apply #'combine named-types)
              (values (cdr named-ty) fx))))))

(defun create-or-type (list-of-types env)
  (create-named-list-of-or-types (mapcar (lambda (it) (cons nil it)) list-of-types)
                                 env))

(defun parse-type (it env)
  (cond
    ((symbolp it)
     (bb parsed (lookup-type it env :allow-unknowns t)
         (if (-unknown-p parsed)
             it
             parsed)))
    ((listp it)
     (ecase (car it)
       (or
        ;; TODO clean up / simplify here
        (bb
          :db (types . effects)
          (reduce (lambda (acc unparsed)
                    (bb :mv (ty fx) (parse-type unparsed env)
                        name (and (symbolp unparsed) unparsed)
                        (cons (cons (cons name ty) (car acc))
                              (combine-effects fx (cdr acc)))))
                  (cdr it)
                  :initial-value (cons nil nil))
          new-env (apply-effects env effects)
          :mv (ty fx) (create-named-list-of-or-types (reverse types) new-env)
          (values ty (combine-effects fx effects))))
       (quote (-lit (second it)))
       (obj
        ;; TODO clean up / simplify here
        (bb alist (plist-alist (cdr it))
            :db (parsed-alist . fx)
            (reduce (lambda (acc pair)
                      (bb :db (alist . fx) acc
                          :db (key . unparsed) pair
                          ;; tyname (and (symbolp unparsed) unparsed)
                          :mv (ty nfx) (parse-type unparsed env)
                          (cons (acons key ty alist) 
                                (combine-effects nfx fx))))

                    alist
                    :initial-value (cons nil nil))
            ;; :mv (names name-fx) (ensure-type-names named-alist env :key #'cdr)
            ;; new-alist (mapcar (lambda (name pair)
            ;;                     (cons (car pair) name))
            ;;                   names
            ;;                   named-alist)
            (values (-obj parsed-alist env) fx)))
       (prop
        (bb anon-var (gensym "var")
            new-env (apply-effects env (vfx anon-var (second it)))  
            (values (-prop anon-var (third it) new-env))))))
    (t (error "unimplemented"))))

;;; ---- equalp representations for complex types

(defun pr-table (tbl)
  (maphash (fn (k v) (format t "~A = ~A~%" k v)) tbl))

(defun list-to-hashset (list &key (test 'equalp))
  (bb result (make-hash-table :test test)
      (dolist (item list result)
        (setf (gethash item result) t))))

;; TODO: exclude 'simple' ( int, lit ) types from permutation
;;       just put them in aux... but that might have complications

(defmacro with-tabling-state (supername &body body)
  `(bb
     counter 0
     name-table (make-hash-table :size 15 :test 'eq)
     graph-table (make-hash-table :size 15 :test 'equal)
     (labels
         ((super (tyname)
            (bb exist (funcall ,supername tyname)
                (and exist (cons 'super exist))))
          (id (tyname)
            (or (super tyname)
                (ensure-gethash tyname name-table (incf counter))))
          (lookup (tyname)
            (or (gethash tyname name-table) (super tyname))))
       ,@body)))


(defun simple-type-p (tyname env)
  (bb
    it (lookup-type-through-vars tyname env :allow-unknowns t)
    (typecase it
      ((or -sym -int -bool) it)
      (t nil))))

(defun or-to-table (or &optional (super (constantly nil)))
  (bb
    env (-or-env or)
    results nil
    tynames (shallow-expand-or-type or env)
    ready-already (fn (tyname)
                    (or (simple-type-p tyname env)
                        (funcall super tyname)))
    to-permute (remove-if ready-already tynames)
    no-permute (mapcar ready-already (remove-if-not ready-already tynames))
    aux (and no-permute (list-to-hashset no-permute))
    (map-permutations
     (fn (tys)
       (with-tabling-state super
         (labels
             ((represent (tyname)
                (if-let (simple-repr (simple-type-p tyname env))
                  simple-repr
                  (bb id (id tyname)
                      (unless (gethash id graph-table)
                        (setf (gethash id graph-table)
                              (bb
                                it (lookup-type-through-vars
                                    tyname env :allow-unknowns t)
                                (etypecase it
                                  (-empty (gensym))
                                  (-unknown id)
                                  (-obj (obj-to-table it #'lookup))))))))))
           (dolist (ty tys)
             (represent ty)))
         (push graph-table results)))
     to-permute :copy nil)
    final-result (if results
                     (list-to-hashset (cons aux results))
                     aux)
    final-result))

;; TODO: sort rows by key
(defun obj-to-table (obj &optional (super (constantly nil)))
  (bb
    ors nil
    (with-tabling-state super
      (labels
          ((represent (tyname env)
             (if-let (simple-repr (simple-type-p tyname env))
               simple-repr
               (bb id (id tyname)
                   (if (not #1=(gethash id graph-table))
                       (setf #1# t
                             #1# (bb
                                   it (lookup-type-through-vars
                                       tyname env :allow-unknowns t)
                                   (etypecase it
                                     (-empty (gensym))
                                     (-unknown id)
                                     (-or (or-to-table it #'lookup))
                                     (-obj (table it)))))
                       id))))
           (table (obj)
             (bb
               env (-obj-env obj)
               id (id obj)
               (unless #2=(gethash id graph-table)
                       (setf #2# t)
                       (loop for (row . tyname) in (-obj-rows obj) do
                            (setf (gethash (cons id row) graph-table)
                                  (represent tyname env))))
               id)))
        (table obj)
        (values graph-table ors counter)))))

;;; ---- ty-equal

(defmethod ty-equal ((a ty) (b ty) env)
  (declare (ignore env))
  (equalp a b))

(defmethod ty-equal ((a -name) (b -name) env)
  (ty-equal
   (lookup-type (-name-ty a) (-name-env a) :allow-unknowns t)
   (lookup-type (-name-ty b) (-name-env b) :allow-unknowns t)
   env))

(defmethod ty-equal ((a ty) (b -name) env)
  (ty-equal a (lookup-type (-name-ty b) (-name-env b) :allow-unknowns t) env))

(defmethod ty-equal ((a -name) (b ty) env)
  (ty-equal (lookup-type (-name-ty a) (-name-env a) :allow-unknowns t) b env))

(defmethod ty-equal ((a -unknown) (b -unknown) env)
  (declare (ignore a b env))
  nil)

(defmethod ty-equal ((a -var) (b -var) env)
  (ty-equal (lookup-type (-var-ref a) env)
            (lookup-type (-var-ref b) env)
            env))

(defmethod ty-equal ((a -var) (b ty) env)
  (ty-equal (lookup-type (-var-ref a) env) b env))

(defmethod ty-equal ((a ty) (b -var) env)
  (ty-equal b a env))

(defmethod ty-equal ((a -or) (b -or) env)
  (declare (ignore env))
  (bb atbl (or-to-table a)
      btbl (or-to-table b)
      (equalp atbl btbl)))

(defmethod ty-equal ((a -obj) (b -obj) env)
  (declare (ignore env))
  (bb :mv (atbl aors acounter) (obj-to-table a)
      :mv (btbl bors bcounter) (obj-to-table b)
      (when (and (= acounter bcounter)
                 (= (length aors)
                    (length bors)))
        ;; (pprint aors)
        ;; (pr-table atbl)
        ;; (format t "-----------------------------~%")
        ;; (bb perms (mapcar (fn (list)
        ;;                     (bb perms nil
        ;;                         (map-permutations (lambda (perm) (push perm perms))
        ;;                                           list :copy t)
        ;;                         perms))
        ;;                   aors)
        ;;     combos nil
        ;;     (map-combinations (fn (combo) (push combo combos))
        ;;                       perms :copy t)
        ;;     (format t "~A combos~%" combos)
        ;;     (pprint perms))
      
      
        ;; (format t "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~%")
        ;; (pprint bors)
        ;; (pr-table btbl)
        (bb result (equalp atbl btbl)
        ;; (format t "=============================~%")
        ;;     (print result)
            result))))

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
  (bb :mv (existing-ty name) (rev-lookup-type ty env)
    (if existing-ty
        (values existing-ty name fx)
        (let ((nm (make-type-name)))
          (values ty nm (combine-effects fx (tfx nm ty)))))))

(defmethod  applied-ty (thing env)
  (bb :mv (ty ty-name side-effects) (ty-of thing env)
    (values ty ty-name (apply-effects env side-effects))))

(defmethod ty-of ((var symbol) env)
  (values (lookup-var var env) nil nil))

(defmethod ty-of ((num integer) env)
  (values (alist-get 'int (env-types env)) 'int nil))

(defun ty-of-forms (forms env)
  (loop
     with env = env
     with fx = nil
     with next-fx = nil
     with ty = (-empty)
     with ty-name = nil
     for form in forms do
       (multiple-value-setq (ty ty-name next-fx) (ty-of form env))
       (setf env (apply-effects env next-fx)
             fx (combine-effects next-fx fx))
     finally (return (values ty ty-name fx))))

(defun add-meta-ref (var-name current-ty ref-ty env)
  (bb
    meta (lookup-var-meta var-name env)
    existing-refs (alist-get :refs meta)
    new-meta (acons :refs (cons ref-ty existing-refs) meta)
    (v-metafx var-name current-ty new-meta)))

;; welcome to the evaluator
(defmethod ty-of ((form list) env)
  (ecase (car form)
    (do (ty-of-forms (cdr form) env))
    ;; this should not directly exist in 'user' code
    (refine!
     (bb
       :db (var ty-name) (cdr form)
       :mv (gen-ty gen-ty-name) (ty-of var env)
       nar-ty (alist-get ty-name (env-types env))
       fx (refine gen-ty-name gen-ty nar-ty env)
       (values (-empty) nil fx)))
    (get
     (bb
       :db (obj prop) (cdr form)
       :mv (ty _ fx) (ty-of obj env)
       (assert ty)
       simple-ref? (symbolp obj)
       var-name (if simple-ref? obj (gensym "var"))
       new-ty (-prop var-name prop env)
       new-fx (combine-effects fx (add-meta-ref var-name ty new-ty env))
       new-env (apply-effects env new-fx)
       (setf (-prop-env new-ty) new-env)
       (values new-ty nil new-fx)))
    (type
     (bb
       :db (tyname unparsed) (cdr form)
       namety (-name tyname nil env)
       namefx (tfx tyname namety)
       new-env (apply-effects env namefx)
       :mv (type fx) (parse-type unparsed new-env)
       (setf (-name-ty namety) type)
       (values (-empty) nil (combine-effects (tfx tyname type) namefx fx))))
    (declare
     (bb :db (varname typename) (cdr form)
         name (make-type-name)
         (values (-empty) nil
                 (combine-effects
                  (vfx varname name)
                  (tfx name (-var typename))))))
    (def!
     (bb
       :db (varname subform) (cdr form)
       :mv (ty typename fx) (ty-of subform env)
       (assert (not (-empty-p ty)))
       (values (-empty) nil
               (combine-effects (vfx varname typename) fx))))
    (def
     (bb
       :db (varname subform) (cdr form)
       :mv (ty _ fx) (ty-of subform env)
       (assert (not (-empty-p ty)))
       (values (-empty) nil
               (combine-effects
                (vfx varname (-var ty))
                fx))))
    (type-equal?
     (bb
       :db (a b) (cdr form)
       tya (lookup-type-through-vars a env :allow-unknowns t)
       tyb (lookup-type-through-vars b env :allow-unknowns t)
       (if (ty-equal tya tyb env)
           (-true)
           (-false)))))) 

(defun combine-new-types (a b env)
  (if (ty-equal a b env)
      (values a (make-effects :types (acons (make-type-name) a nil)))
      (bb an (make-type-name)
          bn (make-type-name)
          cn (make-type-name)
          ty (-or an bn env)
        (values ty
                (make-effects
                 :types (list (cons an a)
                              (cons bn b)
                              (cons cn ty)))))))

(defun reference-ty-p (ty)
  (typecase ty
    ((or -name -var) t)
    (t nil)))


(defmethod lookup-type-through-vars (name env &key allow-unknowns)
  (flet ((deref (ty)
           (typecase ty
             (-var (-var-ref ty))
             (-name (-name-ty ty)))))
    (loop
       for ty-name = name then (deref ty)
       for ty = (lookup-type ty-name env :allow-unknowns allow-unknowns)
       while (reference-ty-p ty)
       finally (return ty))))

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

;; this is not being used as named at the moment.
;; (refer to usage)
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
  (bb
    ty-a (lookup-type (-or-a gen) env)
    ty-b (lookup-type (-or-b gen) env)
    a (make-intersection-type ty-a nar env)
    b (make-intersection-type ty-b nar env)
    no-a (-empty-p a)
    no-b (-empty-p b)
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

(defmethod refineable? ((name -name) (nar ty) env)
  (refineable? (lookup-type (-name-ty name) (-name-env name))
               nar env))

(defmethod refineable? ((a -name) (b -name) env)
  (refineable? (lookup-type (-name-ty a) (-name-env a))
               (lookup-type (-name-ty b) (-name-env b))
               env))

(defmethod refineable? ((nar ty) (name -name) env)
  (refineable? nar (lookup-type (-name-ty name) (-name-env name)) env))

(defmethod refineable? ((gen -or) (nar ty) env)
  (or
   (ty-equal gen nar env)
   (refineable? (lookup-type (-or-a gen) env) nar env)
   (refineable? (lookup-type (-or-b gen) env) nar env)))

;; TODO: the narrow type should be assignable to the general type
;; refine: named general type + narrow type -> maybe side effects
(defmethod refine :around (name (gen ty) (narrow ty) env)
  (declare (ignore name env))
  ;; (print (list (type-of gen) '=> (type-of narrow)))
  (call-next-method))

(defmethod refine (name (a -name) (b -name) env)
  (refine name
          (lookup-type (-name-ty a) (-name-env a))
          (lookup-type (-name-ty b) (-name-env b))
          env))

(defmethod refine (name (a ty) (b -name) env)
  (refine name a
          (lookup-type (-name-ty b) (-name-env b))
          env))

(defmethod refine (name (a -name) (b ty) env)
  (refine name
          (lookup-type (-name-ty a) (-name-env a))
          b env))

(defmethod refine (name (gen ty) (narrow ty) env)
  (unless (ty-equal gen narrow env)
    (make-effects
     :types (acons name (-empty) nil)
     :errors (list (format nil "Cannot narrow ~A to ~A" gen narrow)))))

(defmethod refine :around (name (gen -var) (narrow ty) env)
  (let ((changes (refine name (lookup-type-through-vars (-var-ref gen) env) narrow env)))
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
  (bb
    ty-a (lookup-type (-or-a gen) env)
    ty-b (lookup-type (-or-b gen) env)
    a? (refineable? ty-a narrow env)
    b? (refineable? ty-b narrow env)
    (if (and a? b?)
        (bb :mv (a-type a-fx) (make-intersection-type ty-a narrow env)
            :mv (b-type b-fx) (make-intersection-type ty-b narrow env)
            new-fx (combine-new-types a-type b-type env)
            (combine-effects a-fx b-fx new-fx))
        (if a?
            (bb :mv (a-type a-fx)
                (make-intersection-type ty-a narrow env)
                (combine-effects (tfx name a-type) a-fx))
            (if b?
                (bb :mv (b-type b-fx)
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
                          (tfx target-type a)))
                        (b?
                         (combine-effects
                          (or (refine name row-b nar env) (tfx name nar))
                          (tfx target-type b)))
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
