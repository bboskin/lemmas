(in-package "ACL2S")

(load "compile-raw.lsp")
(load "to-acl2-raw.lsp")
#|
(load "helpers-raw.lsp")
(load "interp-raw.lsp")
|#
(defun gen-mk (name vars definition)
  (let ((new-output (next-var))
	(new-name (get-rel-name name)))
    (let ((a (miniKanrenize definition new-output)))
      (eval `(defrel ,new-name ,(append vars (list new-output))
	       ,a)))))

(defun all-lines ()
  '(var
    boolean symbol number cons
    + - * exp < <= > >=
    car cdr append reverse
    let))

(defun gen-rel-inner (name vars body state)
  (progn
    (add-to-interpreter name (get-rel-name name) (len vars))
    (gen-mk name vars body)
    (mv nil nil state)))

;;;;; Creating new clauses for relational ACL2s interpreter

(defun new-clause (num-args vars pmatch recursive-calls final)
  (cond
   ((= num-args 0)
    `((fresh ,vars
	     (== expr ,pmatch)
	     ,@recursive-calls
	     (,@final o))))
   (t (let ((subexpr (next-var))
	    (subres (next-var)))
	(let ((new-vars `(,@vars ,subexpr ,subres))
	      (new-pmatch `(,@pmatch ,subexpr))
	      (new-rec-calls
	       `(,@recursive-calls (value-of ,subexpr ρ ,subres)))
	      (new-final `(,@final ,subres)))
	  (new-clause
	   (- num-args 1) new-vars new-pmatch new-rec-calls new-final))))))

(defun has-arity-clause (name n)
  `((== form ',name) (== n ,n)))

(defun add-to-interpreter (name rel-name num-args)
  (let ((new-clause
	 (new-clause num-args nil `(list ',name) nil `(,rel-name)))
	(new-arity-clause (has-arity-clause name num-args))
	(current-interp (expr-for-value-of))
	(current-lines (all-lines))
	(current-arities (expr-for-has-arity)))
    (progn
      (defun expr-for-value-of ()
	(append current-interp (list new-clause)))
      (defun all-lines ()
	(append current-lines (list name)))
      (defun expr-for-has-arity ()
	(append current-arities (list new-arity-clause)))
      (eval `(defrel value-of (expr ρ o)
	       ,(expr-for-value-of)))
      (eval `(defrel has-arity (form n)
	       ,(expr-for-has-arity))))))


#|
(defunc2 rev-acc (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract t
  (cond
   ((endp ls) acc)
   (t (rev-acc (cdr ls) (cons (car ls) acc)))))
|#


#|
(acl2s-query
 '(defun rev-acc (ls acc)
    (declare (xargs :guard (and (true-listp ls)
				(true-listp acc))))
    (cond
     ((endp ls) acc)
     (t (rev-acc (cdr ls) (cons (car ls) acc))))))

(acl2s-query '(progn (defun foo14 (e acc)
		       (declare (xargs :mode :program))
		       (if e (foo14 nil (cons e acc)) acc))))

(acl2s-query '(verify-guards foo13))

(acl2s-query '(defthm foo (implies (natp n) (integerp n))))
|#
