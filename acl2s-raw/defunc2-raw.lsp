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

(defun gen-rel-inner (name vars body state)
  (progn
    (add-to-interpreter name (get-rel-name name) (len vars))
    (gen-mk name vars body)
    (mv nil nil state)))

;;;;; Creating new clauses for relational ACL2s interpreter

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
((FRESH (|fresh-var13| |fresh-var14| |fresh-var15| |fresh-var16| |fresh-var17| |fresh-var18|)
	(== EXPR (LIST 'NOT-LESS-THAN |fresh-var13| |fresh-var15| |fresh-var17|))
	(VALUE-OF |fresh-var13| ρ |fresh-var14|)
	(VALUE-OF |fresh-var15| ρ |fresh-var16|)
	(VALUE-OF |fresh-var17| ρ |fresh-var18|)
	(NOT-LESS-THAN-REL |fresh-var14| |fresh-var16| |fresh-var18| O)))|#
