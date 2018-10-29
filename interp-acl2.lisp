(load "~/lemmas/mk.lisp")
(load "~/lemmas/numbers.lisp")
(load "~/lemmas/helpers.lisp")
(load "~/lemmas/compile-acl2.lisp")
#|
The supported language, for now, is just:

endp, equal, cons, car, cdr
cond t nil
append reverse

constants, +, -, *, /, exp
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

;; The Interpreter with helpers
(defrel appendo (l1 l2 o)
  (conde
   ((== l1 '()) (== l2 o))
   ((fresh (a d res)
	   (== l1 `(,a . ,d))
	   (== o `(,a . ,res))
	   (appendo d l2 res)))))

(defrel snoco (x l o)
  (conde
   ((== l '()) (== o `(,x)))
   ((fresh (a d res)
	   (== l `(,a . ,d))
	   (== o `(,a . ,res))
	   (snoco x d res)))))

(defrel reverso (l o)
  (conde
   ((== l '()) (== o '()))
   ((fresh (a d res)
	   (== l `(,a . ,d))
	   (snoco a res o)
	   (reverso d res)))))

(defrel conso (a d o)
  (== o `(,a . ,d)))

(defrel caro (pr a)
  (fresh (d) (conso a d pr)))

(defrel cdro (pr d)
  (fresh (a) (conso a d pr)))

(defun expr-for-value-of ()
  '(conde
    ((lookupo expr ρ o))
    ((== expr 't) (== o 't))
    ((== expr 'nil) (== o 'nil))
    ;; Numbers
    ((fresh (d)
	    (== expr `(MK-NUMBER . ,d))
	    (== expr o)))
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
    ((fresh (pr res)
	    (== expr `(car ,pr))
	    (caro res o)
	    (value-of pr ρ res)))
    ((fresh (pr res)
	    (== expr `(cdr ,pr))
	    (cdro res o)
	    (value-of pr ρ res)))
    ((fresh (a d res1 res2)
	    (== expr `(cons ,a ,d))
	    (conso res1 res2 o)
	    (value-of a ρ res1)
	    (value-of d ρ res2)))
    ((fresh (l1 l2 res1 res2)
	    (== expr `(append ,l1 ,l2))
	    (value-of l1 ρ res1)
	    (value-of l2 ρ res2)
	    (appendo res1 res2 o)))
    ((fresh (l1 res1)
	    (== expr `(reverse ,l1))
	    (value-of l1 ρ res1)
	    (reverso res1 o)))))

(defmacro redefine-interp ()
  `(defrel value-of (expr ρ o)
     ,(expr-for-value-of)))

(redefine-interp)

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
	(current-interp (expr-for-value-of)))
    (progn
      (defun expr-for-value-of ()
	(append current-interp (list new-clause)))
      (eval `(defrel value-of (expr ρ o)
	      ,(expr-for-value-of))))))

;;;;;;;;;;


(defrel passes-tests (e1 e2 tests results)
     (conde
      ((== tests '()))
      ((fresh (a d v r1 rs)
	      (== tests `(,a . ,d))
	      (== results `(,r1 . ,rs))
	      (value-of e1 a r1)
	      (value-of e2 a r1)
	      (passes-tests e1 e2 d rs)))))

(defrel find-equivalent (start forms e tests results)
  (contains-forms forms e)
  (passes-tests start e tests results))

(defmacro gen-mk (name vars definition)
  (let ((new-output (next-var))
	(new-name (get-rel-name name)))
    (let ((a (miniKanrenize definition new-output)))
      `(defrel ,new-name (,@vars ,new-output)
	 ,a))))

(defun clean-numbers (exp)
  (cond
    ((numberp exp) (build-num exp))
    ((symbolp exp) exp)
    (t (cons (clean-numbers (car exp))
	     (clean-numbers (cdr exp))))))

(defun do-lemma (start tests forms results)
  (eval `(car (run 1 q (find-equivalent ',start ',forms q ',tests
					',results)))))

;; user forms
(defmacro defun2 (name vars body)
  `(progn
     (defun ,name ,vars ,body)
     (gen-mk ,name ,vars ,body)
     (add-to-interpreter ',name (get-rel-name ',name) (len ',vars))))


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

(defun eval-ls (start tests)
  (cond
    ((endp tests) nil)
    (t (cons (evaluate-in-substitution start (car tests))
	     (eval-ls start (cdr tests))))))


(defmacro suggest-lemma (start forms tests)
  `(let* ((new-start (clean-numbers ',start))
	  (new-tests (clean-numbers ',tests))
	  (new-forms (clean-numbers ',forms))
 	  (results (clean-numbers (eval-ls ',start ',tests))))
     (do-lemma new-start new-tests new-forms results)
     ))

