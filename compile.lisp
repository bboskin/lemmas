(load "helpers.lisp")

#|
This file implements a compiler from functional programs
to relational programs. The grammar of the language supported is:

Expr := Number | t | nil
     | (cons Expr Expr) | (car Expr) | (cdr Expr)
     | (append Expr Expr) | (reverse Expr)
     | (+ Expr Expr) | (- Expr Expr) | (* Expr Expr) | (/ Expr Expr) | (exp Expr Expr)
     | (endp Expr) | (booleanp Expr) | (numberp Expr) | (varp Expr)
     | (consp Expr) | (true-listp Expr) | (listp Expr)
     | (cond (Expr Expr)*) | (if Expr Expr Expr)
     | (and Expr Expr) | (or Expr Expr) | (not Expr)
     | (let ((symbol Expr)) Expr)
     | (symbol Expr*) ;; <- calls to user-defined-fns + recursion
|#
;; Just a function for a common idiom
(defun has-form (s e)
  (and (consp e) (equal (car e) s)))

;; Go: a guard to decide if recursion is necessary.
(defun miniKanrenize-go (e)
  (cond
   ((symbolp e) (list nil e))
   ((numberp e) (list nil (build-num e)))
   (t (let ((v (next-var)))
	(list t v (miniKanrenize e v))))))

;; compile-recur: takes the inputs which may or may not have required
;; recursion, and introduce the necessary fresh variables
;; for miniKanrenize-bool, dest is nil (and otherwise guaranteed to be non-nil)
(defun complete-recursion-inner (form vars dest es work)
  (cond
   ((endp es)
    (if dest
	(if vars `(fresh ,vars ,@work (,@form ,dest))
	  `(,@form ,dest))
      (if vars `(fresh ,vars ,@work ,form) form)))
   (t (let ((curr (car es)))
	(if (car curr)
	    (complete-recursion-inner `(,@form ,(cadr curr))
				(cons (cadr curr) vars)
				dest (cdr es)
				(cons (caddr curr) work))
	  (complete-recursion-inner `(,@form ,(cadr curr))
			      vars dest (cdr es) work))))))


(defun complete-recursion (form dest es)
  (complete-recursion-inner form nil dest es nil))
(defun complete-recursion-bool (form es)
  (complete-recursion-inner form nil nil es nil))

;; The main function to create miniKanren expressions.
;; These forms are expected to return a value.
;; cond and if call the recursive function miniKanrenize-bool, which
;; creates dest-less expressions not expected to generate output
(defun miniKanrenize (expr dest)
  (cond
   ;; base cases
   ((booleanp expr) `(== ,expr ,dest))
   ((numberp expr) `(== ,(build-num expr) ,dest))
   ((symbolp expr) `(== ,expr ,dest))
   ((has-form 'quote expr) `(== ,(build-sym expr) ,dest))
   ;; cons, car, cdr
   ((has-form 'cons expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(conso) dest (list e1 e2))))
   ((has-form 'car expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion '(caro) dest (list e))))
   ((has-form 'cdr expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion '(cdro) dest (list e))))
   ;; list ops
   ((has-form 'append expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(appendo) dest (list e1 e2))))
   ((has-form 'reverse expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion '(reverso) dest (list e))))
   ;; arithmetic ops
   ((has-form '+ expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-pluso) dest (list e1 e2))))
   ((has-form '- expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-minuso) dest (list e1 e2))))
   ((has-form '* expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-timeso) dest (list e1 e2))))
   ((has-form 'exp expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-expo) dest (list e1 e2))))
   ((has-form '< expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-less-than-o-fn) dest (list e1 e2))))
   ((has-form '<= expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-less-than-equal-o-fn) dest (list e1 e2))))
   ((has-form '> expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-less-than-o-fn) dest (list e2 e1))))
   ((has-form '>= expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion '(do-less-than-equal-o-fn) dest (list e2 e1))))
   ;; let
   ((has-form 'let expr)
    (let ((body (miniKanrenize (caddr expr) dest)))
      (miniKanrenize-let (cadr expr) nil nil body)))
   ((has-form 'let* expr)
    (let ((body (miniKanrenize (caddr expr) dest)))
      (miniKanrenize-let* (cadr expr) body)))
   ;; control flow
   ((has-form 'cond expr)
    `(conde . ,(miniKanrenize-cond (cdr expr) dest)))
   ((has-form 'if expr)
    (let ((test (cadr expr))
	  (then (caddr expr))
	  (alt (cadddr expr)))
      `(conde . ,(miniKanrenize-cond (list (list test then)
					   (list `(not ,test) alt))
				     dest))))
   ;; boolean expressions
   ((has-form 'and expr)
    (let ((results (mapcar #'miniKanrenize-go (cdr expr))))
      (complete-recursion '(ando) dest results)))
   ((has-form 'or expr)
    (let ((results (mapcar #'miniKanrenize-go (cdr expr))))
      (complete-recursion '(oro) dest results)))
   ((has-form 'not expr)
    (let ((res (miniKanrenize-go (cadr expr))))
      (complete-recursion '(noto) dest (list res))))
   ;; type recognizers
   ((has-form 'booleanp expr)
    (let ((res (miniKanrenize-go (cadr expr))))
      (complete-recursion '(booleanpo-fn) dest (list res))))
   ((has-form 'numberp expr)
    (let ((res (miniKanrenize-go (cadr expr))))
      (complete-recursion '(numberpo-fn) dest (list res))))
   ((has-form 'varp expr)
    (let ((res (miniKanrenize-go (cadr expr))))
      (complete-recursion '(varpo-fn) dest (list res))))
   ((has-form 'consp expr)
    (let ((res (miniKanrenize-go (cadr expr))))
      (complete-recursion '(conspo-fn) dest (list res))))
   ;; predicates
   ((has-form 'endp expr)
    (let ((res (miniKanrenize-go (cadr expr))))
      (complete-recursion '(endpo-fn) dest (list res))))
   ((has-form 'zerop expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion '(zeropo-fn)  dest (list e))))
   ;; recursion, user-defined functions
   ((consp expr)
    (let ((new-name (get-rel-name (car expr)))
	  (results (mapcar #'miniKanrenize-go (cdr expr))))
      (complete-recursion `(,new-name) dest results)))
   (t `(fail))))


;;;;;;;;;;;;;;;
;; miniKanrenize helpers for special cases

;; conditionals
(defun miniKanrenize-cond (lines dest)
  (cond
   ((endp lines) `(((fail))))
   (t (let ((line1 (car lines))
	    (rst (cdr lines)))
	(if line1
	    (let ((test (car line1))
		  (conseq (cadr line1)))
	      (cons
	       `(,(miniKanrenize-bool test)
		 ,(miniKanrenize conseq dest))
	       (miniKanrenize-cond
		rst dest)))
	  `(((fail))))))))

;; let statements
(defun miniKanrenize-let (lines vars work body)
  (cond
   ((endp lines) `(fresh ,vars ,@work ,body))
   (t (let ((x (caar lines))
	    (e (cadar lines)))
	(miniKanrenize-let (cdr lines) `(,@vars ,x)
			   `(,@work ,(miniKanrenize e x)) body)))))

(defun miniKanrenize-let* (lines body)
  (cond
   ((endp lines) body)
   (t (let ((x (caar lines))
	    (e (cadar lines)))
	`(fresh (,x)
		,(miniKanrenize e x)
		,(miniKanrenize-let* (cdr lines) body))))))

;; booleans
(defun miniKanrenize-bool (expr)
  (cond
   ;; base cases
   ((equal expr 't) '(succeed))
   ((equal expr 'nil) '(fail))
   ((numberp expr) '(succeed))
   ((symbolp expr) '(succeed))
   ;; equality
   ((has-form 'equal expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion-bool '(==) (list e1 e2))))
   ;; type recognizers
   ((has-form 'varp expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion-bool '(varpo) (list e))))
   ((has-form 'numberp expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion-bool '(numberpo) (list e))))
   ((has-form 'booleanp expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion-bool '(booleanpo) (list e))))
   ((has-form 'consp expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion-bool '(conspo) (list e))))
   ;; predicates
   ((has-form 'endp expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion-bool '(endpo) (list e))))
   ((has-form 'zerop expr)
    (let ((e (miniKanrenize-go (cadr expr))))
      (complete-recursion-bool '(zeropo) (list e))))
   ;; arithmetic
   ((has-form '< expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion-bool '(do-less-than-o) (list e1 e2))))
   ((has-form '<= expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion-bool '(do-less-than-equal-o) (list e1 e2))))
   ((has-form '> expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion-bool '(do-less-than-o) (list e2 e1))))
   ((has-form '>= expr)
    (let ((e1 (miniKanrenize-go (cadr expr)))
	  (e2 (miniKanrenize-go (caddr expr))))
      (complete-recursion-bool '(do-less-than-equal-o) (list e2 e1))))
   ;; boolean connectors
   ((has-form 'and expr)
    `(conj . ,(mapcar #'miniKanrenize-bool (cdr expr))))
   ((has-form 'or expr)
    `(disj . ,(mapcar #'miniKanrenize-bool (cdr expr))))
   ((has-form 'not expr)
    (miniKanrenize (cadr expr) nil))
   (t (let ((x (next-var)))
	`(fresh (,x)
		(non-nilo ,x)
		,(miniKanrenize expr x))))))
