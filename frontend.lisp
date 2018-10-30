(load "~/lemmas/interp-acl2.lisp")



;;; cleaning input expressions to conform to internal representations:


;;;;;;;;;;;;;;;;;;;;;;
;; Forms to create valid expressions

;; add tags to quoted values, creating valid expressions
(defun values->expressions (e)
  (cond
   ((booleanp e) e)
   ((symbolp e) (build-sym e))
   ((numberp e) (build-num e))
   ((consp e)
    `(cons ,(fix-values (car e))
	   ,(fix-values (cdr e))))))

;; take input expressions, find quoted terms (and numbers), and fix.
;; uses values->expressions under quote, and otherwise only changes numbers
(defun clean-expr (e)
  (cond
   ((numberp e) (build-num e))
   ((symbolp e) e)
   ((equal (car e) 'quote)
    (fix-values (cadr e)))
   (t (cons (clean-expr (car e))
	    (clean-expr (cdr e))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; forms to create valid values from test cases (for environment)
(defun clean-val (exp)
  (cond
   ((numberp exp) (build-num exp))
   ((booleanp exp) exp)
   ((symbolp exp) (build-sym exp))
   ((consp exp)
    (list 'INTERNAL-CONS (clean-val (car exp))
	  (clean-val (cdr exp))))))

(defun clean-tests (alist)
  (cond
   ((endp alist) nil)
   (t (let* ((v (car alist))
	     (x (car v))
	     (val (cadr v)))
	(cons (list x (clean-val val))
	      (clean-tests (cdr alist)))))))

;;; Takes synthesized expressions, and removes evidence
;; of internal values
(defun read-back (v)
  (cond
   ((symbolp v) v)
   ((consp v)
    (let ((tag (car v)))
      (cond
       ((equal tag 'INTERNAL-SYMBOL) (cadr v))
       ((equal tag 'INTERNAL-NUMBER) (read-back-num v))
       ((equal tag 'INTERNAL-CONS)
	(cons (read-back (cadr v))
	      (read-back (caddr v))))
       (t (cons (read-back tag)
		(read-back (cdr v)))))))))




;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;
;; user forms
;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defun2 (name vars body)
  `(progn
     (defun ,name ,vars ,body)
     (gen-mk ,name ,vars ,body)
     (add-to-interpreter ',name
			 (get-rel-name ',name)
			 (len ',vars))))


;; suggest-lemma


#|(defun do-lemma (start tests forms results)
  (eval `(car (run 1 q (find-equivalent ',start ',forms q ',tests
					',results)))))|#


(defun subs (x v e)
  (cond
   ((equal e x) `',v)
   ((consp e) (cons (subs x v (car e))
		    (subs x v (cdr e))))
   (t e)))

(defun evaluate-in-substitution (form args)
  (cond
   ((endp args) (eval form))
   (t (let* ((var (caar args))
	     (v (cadar args))
	     (new-form (subs var v form)))
	(evaluate-in-substitution new-form (cdr args))))))
(defun eval-all (start tests)
  (mapcar #'(lambda (e) (evaluate-in-substitution start e)) tests))

(defmacro suggest-lemma (start forms tests)
  `(let* ((new-forms (clean-expr ',forms))
	  (new-tests (mapcar #'clean-tests ',tests))
	  (results (mapcar #'clean-val (eval-all ',start ',tests))))
     (read-back
      (eval `(car (run 1 q (find-equivalent ',new-forms
					    q
					    ',new-tests
					    ',results))))
      ;(do-lemma new-start new-tests new-forms results)
      )))

#|
(defmacro do-run (n q form)
  (let ((v (clean-expression form)))
     `(read-back (run ,n ,q ,v))))


(do-lemma '(cons t nil) '(cons t nil) '() '(()))


(run 1 q (find-equivalent '(cons t nil) '(cons t nil) q '(())
					'((internal-cons t nil))))
|#
