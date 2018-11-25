(in-package "ACL2S")

;(load "compile-raw.lsp")
;(load "to-acl2-raw.lsp")
#|
(load "helpers-raw.lsp")
(load "interp-raw.lsp")
(load "compile-defdata-raw.lsp")
|#

;; defun core functions
(defun gen-mk (name vars definition)
  (let ((new-output (next-var))
	(new-name (get-rel-name name)))
    (let ((a (miniKanrenize definition new-output)))
      (eval `(defrel ,new-name ,(append vars (list new-output))
	       ,a)))))

(defun defunc2- (name vars body state)
  (progn
    (add-to-interpreter name (get-rel-name name) (len vars))
    (gen-mk name vars body)
    (mv nil nil state)))

(defun add-all-to-built-ins (forms rel rel-fn)
  (cond
   ((endp forms) (progn (defparameter built-ins-bool (append rel built-ins-bool))
			(defparameter built-ins (append rel-fn built-ins))))
   (t (let* ((f (car forms))
	     (pf (get-pred-name f))
	     (pf-rel (get-rel-name pf))
	     (pf-fn (get-rel-fn-name pf)))
	(add-to-interpreter pf pf-fn 1)
	(add-all-to-built-ins (cdr forms)
			      (cons `(,f 1 ,pf-rel) rel)
			      (cons `(,f 1 ,pf-fn) rel-fn))))))
#|
(defdata2 
  (expr (oneof integer 
               symbol 
               inc-expr
               sq-expr
               +-expr
               *-expr))
  (inc-expr (list 'inc expr))
  (sq-expr  (list 'sq expr))
  (+-expr   (list expr '+ expr))
  (*-expr   (list expr '* expr)))
|#
;; defdata core functions
(defun defdata2- (exprs)
  (cond
   ((endp exprs) (error "Defdata2 expected to receive arguments, received nothing"))
   ;; single defs
   ((symbolp (car exprs))
    (let* ((name (car exprs))
	   (pred-name (get-pred-name name))
	   (rel-name (get-rel-name pred-name))
	   (rel-fn-name (get-rel-fn-name pred-name)))
      (progn
	;; new type exists
	(update-types (list name))
	;; interpreter knows about fn-version
	(add-to-interpreter pred-name rel-fn-name 1)
	(defparameter built-ins-bool (cons `(,pred-name 1 ,rel-name) built-ins-bool))
	(eval (defdata2-- (car exprs) (cadr exprs)))
	;(eval (make-fn-version pred-name))
	)))
   ;; mutually recursive defs
   (t (progn
	(update-types (mapcar #'car exprs))
	(add-all-to-built-ins (mapcar #'car exprs) nil nil)
	(eval `(progn . ,(mapcar #'(lambda (a) (defdata2-- (car a) (cadr a)))
				 exprs)))))))

;;;;; Creating new clauses for relational ACL2s interpreter

;; has arity helps make better forms
(defun has-arity-clause (name n)
  `((== form ',name) (== n ,n)))

(defun add-to-interpreter (name rel-name num-args)
  (let ((new-clause (new-clause num-args nil `(list ',name) nil `(,rel-name)))
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
      (defparameter lemma-built-ins (cons `(,name ,num-args ,rel-name) lemma-built-ins))
      (eval `(defrel value-of (expr ρ o)
	       ,(expr-for-value-of)))
      (eval `(defrel has-arity (form n)
	       ,(expr-for-has-arity))))))

;; for some reason I keep needing to redefine this
(defun all-lines ()
  (append 
   '(var boolean symbol number string char cons car cdr let if cond)
   (mapcar #'car lemma-built-ins)))
