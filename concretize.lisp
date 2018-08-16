(in-package :ty)
;; --- resolve
;; for debugging?
;; but can't resolve an or type, because it uses refs >.<
;; introduce yet another representation for a resolved type?


(defvar *current-resolutions* nil)
(defvar *currently-resolving-name* nil)
(defvar *active-resolutions* nil)
(defvar *resolution-queue* nil)

(defmacro resolve-enqueue (&body body)
  `(let ((thunk (lambda () ,@body)))
     (if *resolution-queue*
         (setf (cdr (last *resolution-queue*)) (list thunk))
         (push thunk *resolution-queue*))))


(defun concretize (ty env)
  (let ((*current-resolutions* nil)
        (*resolution-queue* nil)
        (*active-resolutions* nil))
    (resolve ty env (fn (result) (return-from concretize result)))
    (loop for thunk = (pop *resolution-queue*) while thunk
       do (funcall thunk))))

(defmacro def-resolver (((name type)) &body body)
  `(defmethod resolve ((,name ,type) (env env) cont)
     (flet
         ((cont (result) (funcall cont result))
          (forward-ref (partial-result)
            (push (cons *currently-resolving-name* partial-result)
                  *current-resolutions*)
            partial-result))
       (macrolet
           ((enqueue (&body body) `(resolve-enqueue ,@body))
            (resolve-> (ty res-name &body body)
              `(resolve ,ty env (fn (,res-name) ,@body))))
         (progn
           ,@body
           (values))))))

(def-resolver ((null null))
  (assert nil)
  (cont (-empty)))

(def-resolver ((name symbol))
  (let ((*currently-resolving-name* name))
    (if-let (resolved (alist-get name *current-resolutions*))
      (cont resolved)
      (if (member name *active-resolutions*)
          ;; Yield somehow?
          (assert nil)
          (bb
            lookup (alist-get name (env-types env))
            (push name *active-resolutions*)
            (resolve-> lookup found
                       (push (cons name found) *current-resolutions*)
                       (setf *active-resolutions* (delete name *active-resolutions*))
                       (cont found)))))))

(def-resolver ((ty ty))
  (enqueue (cont ty)))

(def-resolver ((ty -var))
  (enqueue (resolve (-var-ref ty) env #'cont)))

(def-resolver ((ty -obj))
  (bb
    rows (-obj-rows ty)
    acc nil
    result (list 'obj nil)
    (forward-ref result)
    (labels ((recur ()
               (enqueue
                (if-let (next (pop rows))
                  (bb :db (key . tyname) next
                      (resolve-> tyname ty
                                 (push (cons key ty) acc)
                                 (recur)))
                  (progn
                    (setf (second result) (reverse acc))
                    (cont result))))))
      (recur))))


(def-resolver ((repr list))
  (ecase (car repr) ;; should already be resolved...
    (or (cont repr))
    (obj (cont repr))))

(defun resolved-flattened-or-members (or &optional existing &key preserve-empty)
  ;; preserve empty for partially-resolved results
  (bb
    seen existing
    (labels
        ((recur (or)
           (let (result)
             (dolist (it (cdr or) result)
               (if (and (listp it) (eq (car it) 'or))
                   (if (member it seen :test 'eq)
                       (push it result)
                       (progn
                         (push it seen)
                         (if (and (null (cdr it)) preserve-empty)
                             (push it result)
                             (setf result (append (recur it) result)))))
                   (push it result))))))
      (reverse (recur or)))))

(def-resolver ((ty -or))
  (bb
    result (list 'or)
    acc nil
    (forward-ref result)
    (enqueue (resolve->
              (-or-a ty) a
              (push a acc)
              (enqueue (resolve->
                        (-or-b ty) b
                        (push b acc)
                        (bb
                          members (reverse acc)
                          (setf (cdr result) members)
                          (setf (cdr result)
                                (resolved-flattened-or-members (list* 'or members)
                                                               (list result)
                                                               :preserve-empty t)))
                        (enqueue (cont result))))))))


(def-resolver ((ty -prop))
  (let ((prop-name (-prop-prop ty))
        (ref-ty (alist-get (-prop-ty ty) (env-types env))))
    (flet ((get-prop (from)
             (if (and (listp from)
                      (eq (car from) 'obj))
                 (alist-get prop-name (second from))
                 (-empty))))
      (resolve->
       ref-ty rez
       (etypecase rez
         (-empty (cont rez))
         (list
          (ecase (car rez)
            (or
             (bb tys (resolved-flattened-or-members rez)
                 (cont (cons 'or (mapcar #'get-prop tys)))))
            (obj
             (cont (get-prop rez))))))))))

