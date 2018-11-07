(load "compile.lisp")
(load "to-acl2.lisp")

(defmacro gen-mk (name vars definition)
  (let ((new-output (next-var))
	(new-name (get-rel-name name)))
    (let ((a (miniKanrenize definition new-output)))
      `(defrel ,new-name (,@vars ,new-output)
	 ,a))))


(defmacro defunc2 (name vars ic-ig ic oc-ig oc body)
  `(if (not (and (equal ',ic-ig ':input-contract)
		 (equal ',oc-ig ':output-contract)))
       (error "Expected an input and output contract")
       (progn
	 (acl2s-query `(defun ,',name ,',vars
			 (declare (xargs :guard ,',ic))
			 ,',body))
	 (defun ,name ,vars ,body)
	 (gen-mk ,name ,vars ,body)
	 (add-to-interpreter ',name
			     (get-rel-name ',name)
			     (len ',vars)))))

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

(defun add-to-interpreter (name rel-name num-args)
  (let ((new-clause
	 (new-clause num-args nil `(list ',name) nil `(,rel-name)))
	(current-interp (expr-for-value-of))
	(current-lines (all-lines)))
    (progn
      (defun expr-for-value-of ()
	(append current-interp (list new-clause)))
      (defun all-lines ()
	(append current-lines (list name)))
      (eval `(defrel value-of (expr ρ o)
	      ,(expr-for-value-of))))))
