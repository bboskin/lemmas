#|A framework for performing contract completion|#
(load "~/lemmas/with-acl2.lisp")







;;;;;;;;;;;;;;;;;;;;;

(acl2s-query '(defun fn-append (a b) (append a b)))
(acl2s-query '(defun fn-reverse (a) (reverse a)))
(acl2s-query '(defun fn-car (a) (car a)))
(acl2s-query '(defun fn-cdr (a) (cdr a)))
(acl2s-query '(defun fn-+ (a b) (+ a b)))
(acl2s-query '(defun fn-- (a b) (- a b)))
(acl2s-query '(defun fn-* (a b) (* a b)))

(defun fn-names ()
  '((append  acl2s::fn-append)
    (reverse acl2s::fn-reverse)
    (car     acl2s::fn-car)
    (cdr     acl2s::fn-cdr)
    (+       fn-+)
    (-       fn--)
    (*       fn-*)))

(defun replace-function (f)
  (let ((g (assoc f (fn-names))))
    (if (consp g) (cadr g) f)))

(defun convert-to-functions (f)
  (cond
    ((booleanp f) f)
    ((numberp f) f)
    ((symbolp f) (replace-function f))
    ((and (consp f)
	  (equal (car f) 'quote))
     f)
    (t
     (cons (convert-to-functions (car f))
	   (convert-to-functions (cdr f))))))



;;;;;;;;;;;;;


(defun make-or (e)
  (if (> (length e) 1) `(or . ,e) (car e)))

(defun get-hyps (form)
  (mv-let
   (cx? e state)
   (acl2s-query `(acl2s::guard-obligation
		  ',form
		  nil nil
		  'top-level
		  state))
   (let* ((res (cadr (cadr (cadr cx?))))
	  (ors (mapcar #'make-or res)))
     (if (> (length ors) 1)
	 `(and . ,ors)
       (car ors)))))

#|
(acl2s-query '(acl2s::defun foo44 (e)
			    (declare (xargs :guard (consp e)))
			     (car e)))

(get-hyps '(append (foo44 e) 4))
|#
