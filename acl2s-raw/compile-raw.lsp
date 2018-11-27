(in-package "ACL2S")

;; Go: a guard to decide if recursion is necessary.
(defun miniKanrenize-go (e)
  (cond
   ((symbolp e) `(nil ,e))
   ((numberp e) `(nil ',(build-num e)))
   ((stringp e) `(nil ',(build-string e)))
   ((characterp e) `(nil ',(build-char e)))
   (t (let ((v (next-var)))
	(list t v (miniKanrenize e v))))))

;; compile-recur: takes the inputs which may or may not have required
;; recursion, and introduce the necessary fresh variables
;; for miniKanrenize-bool, dest is nil (and otherwise guaranteed to be non-nil)
(defun complete-recursion-inner (form vars dest es work has-dest?)
  (cond
   ((endp es)
    (if has-dest?
	(if vars `(fresh ,vars ,@work (,@form ,dest))
	  `(,@form ,dest))
      (if vars `(fresh ,vars ,@work ,form) form)))
   (t (let ((curr (car es)))
	(if (car curr)
	    (complete-recursion-inner `(,@form ,(cadr curr))
				(cons (cadr curr) vars)
				dest (cdr es)
				(cons (caddr curr) work)
				has-dest?)
	  (complete-recursion-inner `(,@form ,(cadr curr))
				    vars dest (cdr es) work
				    has-dest?))))))

(defun complete-recursion-inner-nary (form id dest es)
  (cond
   ((endp es) `(== ,id ,dest))
   ((endp (cdr es))
    (let ((curr (car es)))
      (if (car curr)
	  `(conj2 (== ,(cadr curr) ,dest) ,(caddr curr))
	`(== ,(cadr curr) ,dest))))
   ((endp (cddr es))
    (let ((e1 (car es)) (e2 (cadr es)))
      `(conj
	(,@(append (cddr e1) (cddr e2))
	 (,form ,(cadr e1) ,(cadr e2) ,dest)))))
   (t (let* ((e1 (car es))
	     (name-for-e1 (cadr e1))
	     (work-for-e1 (cddr e1))
	     (int (next-var)))
	`(fresh (,int)
		,(complete-recursion-inner-nary form id int (cdr es))
		,@work-for-e1
		(,form ,name-for-e1 ,int ,dest))))))

(defun complete-recursion (form dest es)
  (complete-recursion-inner form nil dest es nil t))
(defun complete-recursion-bool (form es)
  (complete-recursion-inner form nil nil es nil nil))

;; The main function to create miniKanren expressions.
;; These forms are expected to return a value.
;; cond and if call the recursive function miniKanrenize-bool, which
;; creates dest-less expressions not expected to generate output

(defun compiler-knows-function? (form)
  (cond
   ((equal form 'cons) '(2 conso))
   ((equal form 'car) '(1 caro))
   ((equal form 'cdr) '(1 cdro))
   (t (function-is-known? form))))

(defun gather-names (es)
  (cond
   ((endp es) nil)
   (t (let ((e (car es)))
	(if (car e)
	    (cons (cadr e) (gather-names (cdr es)))
	  (gather-names (cdr es)))))))

(defun do-rec (form es dest)
  (let ((es (mapcar #'miniKanrenize-go es))
	(v (compiler-knows-function? form)))
    (let* ((arity (car v))
	   (identity (cadr v))
	   (rel-name (if arity (cdr v) (cddr v))))
      (cond
       ((not arity)
	(let ((names (gather-names es)))
	  `(fresh ,names
		  ,(complete-recursion-inner-nary (car rel-name) identity dest es))))
       ((equal arity (length es)) (complete-recursion rel-name dest es))
       (t (error "Wrong number of args given to ~a" form))))))

#|(defun do-rec (form es dest)
  (let ((es (mapcar #'miniKanrenize-go es))
	(v (assoc form built-ins)))
    (if v
	(if (or (not (cadr v)) (equal (length es) (cadr v)))
	    (complete-recursion (cddr v) dest es)
	  (error "Wrong number of args given to ~a" form))
      (let ((name (get-rel-name form)))
	(complete-recursion `(,name) dest es)))))
|#
(defun miniKanrenize (expr dest)
  (cond
   ;; base cases
   ((booleanp expr) `(== ,expr ,dest))
   ((numberp expr) `(== ',(build-num expr) ,dest))
   ((stringp expr) `(== ',(build-string expr) ,dest))
   ((characterp expr) `(== ',(build-char expr) ,dest))
   ((symbolp expr) `(== ,expr ,dest))
   ((has-form 'quote expr) `(== ',(clean-val expr) ,dest))
   ;; Since interp handles these separately, so does compile
   ((has-form 'cons expr) (do-rec 'cons (cdr expr) dest))
   ((has-form 'car expr) (do-rec 'car (cdr expr) dest))
   ((has-form 'cdr expr) (do-rec 'cdr (cdr expr) dest))
   ((has-form 'first expr) (do-rec 'car (cdr expr) dest))
   ((has-form 'rest expr) (do-rec 'cdr (cdr expr) dest))
   ;; Special cases: let, control flow
   ((has-form 'let expr) (miniKanrenize-let expr dest))
   ((has-form 'let* expr) (miniKanrenize-let* expr dest))
   ;; control flow
   ((has-form 'cond expr)
    `(conde . ,(miniKanrenize-cond (cdr expr) nil dest)))
   ((has-form 'if expr) (miniKanrenize-if expr dest))
   ((has-form 'or expr)
    `(conde . ,(mapcar #'(lambda (x) (list (miniKanrenize x dest))) (cdr expr))))
   ;; subseq – since it 
   ;; the majority of forms can be handled equivalently
   ((consp expr) (do-rec (car expr) (cdr expr) dest))
   ;; anything else fails
   (t `(fail))))

;;;;;;;;;;;;;;;
;; miniKanrenize helpers for special cases

;; conditionals

(defun miniKanrenize-cond (lines negations dest)
  (cond
   ((endp lines) `(((fail))))
   (t (let* ((line1 (car lines))
	     (test (miniKanrenize-bool (car line1)))
	     (test-neg (miniKanrenize-bool `(not ,(car line1)))))
	(if line1
	    (cons
	     `(,test ,@negations ,(miniKanrenize (cadr line1) dest))
	     (miniKanrenize-cond (cdr lines) (cons test-neg negations) dest))
	  `(((fail))))))))

(defun miniKanrenize-if (expr dest)
  (let ((test (cadr expr))
	(then (caddr expr))
	(alt (cadddr expr)))
    `(conde . ,(miniKanrenize-cond (list (list test then)
					 (list t alt))
				   nil
				   dest))))
;; let statements

(defun miniKanrenize-let (expr dest)
  (let ((body (miniKanrenize (caddr expr) dest)))
    (miniKanrenize-let- (cadr expr) nil nil body)))

(defun miniKanrenize-let- (lines vars work body)
  (cond
   ((endp lines) `(fresh ,vars ,@work ,body))
   (t (let ((x (caar lines))
	    (e (cadar lines)))
	(miniKanrenize-let- (cdr lines) `(,@vars ,x)
			    `(,@work ,(miniKanrenize e x)) body)))))

(defun miniKanrenize-let* (expr dest)
  (let ((body (miniKanrenize (caddr expr) dest)))
    (miniKanrenize-let*- (cadr expr) body)))

(defun miniKanrenize-let*- (lines body)
  (cond
   ((endp lines) body)
   (t (let ((x (caar lines))
	    (e (cadar lines)))
	`(fresh (,x)
		,(miniKanrenize e x)
		,(miniKanrenize-let*- (cdr lines) body))))))


;; booleans

(defun do-rec-bool (form es)
  (let ((es (mapcar #'miniKanrenize-go es))
	(v (function-is-known-bool? form)))
    (let* ((arity (car v))
	   (identity (cadr v))
	   (rel-name (if arity (cdr v) (cddr v))))
      (cond
       ((not arity)
	(complete-recursion-inner-nary (car rel-name) identity (next-var) es))
       ((equal arity (length es)) (complete-recursion-bool rel-name es))
       (t (error "Wrong number of args given to ~a" form))))))

(defun miniKanrenize-bool (expr)
  (cond
   ;; base cases
   ((equal expr 't) '(succeed))
   ((equal expr 'nil) '(fail))
   ((numberp expr) '(succeed))
   ((symbolp expr) '(succeed))
   ((has-form 'quote expr) '(succeed))
   ;; standard ops with boolean versions
   ((and (consp expr)
	 (assoc (car expr) built-ins-bool))
    (do-rec-bool (car expr) (cdr expr)))
   ;; boolean connectors
   ((has-form 'and expr)
    `(conj ,(mapcar #'miniKanrenize-bool (cdr expr))))
   ((has-form 'or expr)
    `(disj ,(mapcar #'miniKanrenize-bool (cdr expr))))
   ((has-form 'not expr) (miniKanrenize (cadr expr) nil))
   ;; anything else just needs to return something non-nil
   (t (let ((x (next-var)))
	`(fresh (,x) (non-nilo ,x) ,(miniKanrenize expr x))))))
