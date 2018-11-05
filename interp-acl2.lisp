(load "~/lemmas/mk.lisp")
(load "~/lemmas/numbers.lisp")
(load "~/lemmas/helpers.lisp")
(load "~/lemmas/compile.lisp")
(load "~/lemmas/relational-primitives.lisp")



#|
(add-include-book-dir :acl2s-modes "~/books/acl2s/")
(ld "acl2s-mode.lsp" :dir :acl2s-modes)
(acl2s-defaults :set verbosity-level 1)
(reset-prehistory t)
(in-package "ACL2S")
|#


;; Environments

(defrel lookupo (y ρ o)
  (conde
   ((fresh (d)
	   (== ρ `((,y ,o) . ,d))))
   ((fresh (x v d)
	   (== ρ `((,x ,v) . ,d))
	   (lookupo y d o)))))

(defrel extend-env (ρ y v o)
  (== o `((,y ,v) . ,ρ)))

;; The Interpreter with helpers


;; let actually has the semantics of let*
;; for proposed expressions. This is OK for now.
(defrel do-let (es ρ new-ρ)
  (conde
   ((== es '()) (== ρ new-ρ))
   ((fresh (x a d v rho)
	   (== es `((,x ,a) . ,d))
	   (value-of a ρ v)
	   (extend-env ρ x v rho)
	   (do-let es rho new-ρ)))))

(defun all-lines ()
  '(var
    boolean symbol number cons
    + - * exp < <= > >=
    car cdr append reverse
    let))

(defun expr-for-value-of ()
  '(conde
    ;; environment lookup
    ((lookupo expr ρ o))
    ;; constants
    ((booleanpo expr) (== o expr))
    ((varpo expr) (== o expr))
    ((numberpo expr) (== o expr))
    ((fresh (a d res1 res2)
	    (== expr `(cons ,a ,d))
	    (conso res1 res2 o)
	    (value-of a ρ res1)
	    (value-of d ρ res2)))
    ;; Arithmetic
    ((fresh (n m n-res m-res)
	    (== expr `(+ ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-pluso n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(- ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-minuso n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(* ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-timeso n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(exp ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-expo n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(< ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-o-fn n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(<= ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-equal-o-fn n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(> ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-o-fn m-res n-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(<= ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-equal-o-fn m-res n-res o)))
    ;; list stuff
    ((fresh (pr res)
	    (== expr `(car ,pr))
	    (caro res o)
	    (value-of pr ρ res)))
    ((fresh (pr res)
	    (== expr `(cdr ,pr))
	    (cdro res o)
	    (value-of pr ρ res)))
    ((fresh (l1 l2 res1 res2)
	    (== expr `(append ,l1 ,l2))
	    (value-of l1 ρ res1)
	    (value-of l2 ρ res2)
	    (appendo res1 res2 o)))
    ((fresh (l1 res1)
	    (== expr `(reverse ,l1))
	    (value-of l1 ρ res1)
	    (reverso res1 o)))
    ((fresh (es b new-ρ)
	    (== expr `(let ,es ,b))
	    (do-let es ρ new-ρ)
	    (value-of b new-ρ o)))))

(defmacro reset-interp ()
  `(progn
     (defrel value-of (expr ρ o)
       ,(expr-for-value-of))
     (defun all-lines ()
       ,(all-lines))))

(reset-interp)
;;;;; Creating new clauses for relational ACL2s interpreter


(defun new-clause (num-args vars pmatch recursive-calls final)
  (cond
   ((= num-args 0) `((fresh ,vars (== expr ,pmatch) ,@recursive-calls (,@final o))))
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

;;;;;;;;;;

;; Constraints on expressions

(defrel contains-form (form e)
  (conde
   ((== form e))
   ((fresh (op e1)
	   (== e `(,op ,e1))
	   (conde
	    ((== op form))
	    ((contains-form form e1)))))
   ((fresh (op e1 e2)
	   (== e `(,op ,e1 ,e2))
	   (conde
	    ((== op form))
	    ((contains-form form e1))
	    ((contains-form form e2)))))))

(defrel contains-forms (fms e)
  (conde
   ((== '() fms))
   ((fresh (a d)
	   (== fms `(,a . ,d))
	   (contains-form a e)
	   (contains-forms d e)))))

(defrel passes-tests (e2 tests results)
     (conde
      ((== tests '()))
      ((fresh (a d v r1 rs)
	      (== tests `(,a . ,d))
	      (== results `(,r1 . ,rs))
	      (value-of e2 a r1)
	      (passes-tests e2 d rs)))))

(defrel find-equivalent (forms e tests results)
  (contains-forms forms e)
  (passes-tests e tests results))

(defmacro gen-mk (name vars definition)
  (let ((new-output (next-var))
	(new-name (get-rel-name name)))
    (let ((a (miniKanrenize definition new-output)))
      `(defrel ,new-name (,@vars ,new-output)
	 ,a))))



