(in-package "ACL2S")


(load "interp-raw.lsp")
(load "to-acl2-raw.lsp")

;(load "itest-cgen.lisp")
;(load "itest-ithm.lisp")
;;;;;;;;;;;;;;;;;;;;;;
;; Forms to create valid expressions

;; creating numbers. All numbers are coerced into being natural numbers,
;; and in addition all non-number, non-symbol, non-boolean atoms are coerced
;; into being natural numbers. This may change later, but may not.

(defun fix-atom (e)
  (cond
   ((symbolp e) e)
   ((integerp e) (build-num (abs e)))
   ((rationalp e) (build-num (denominator e)))
   ;; strings, chars, and complex numbers become random numbers
   (t (build-num (random 10)))))


;; add tags to quoted values, creating valid expressions
(defun fix-values (e)
  (cond
   ((consp e)
    `(cons ,(fix-values (car e))
	   ,(fix-values (cdr e))))
   ((booleanp e) e)
   ((symbolp e) (build-sym e))
   (t (fix-atom e))))

;; take input expressions, find quoted terms (and numbers), and fix.
;; uses values->expressions under quote, and otherwise only changes numbers
(defun clean-expr (e)
  (cond
   ((not (consp e)) (fix-atom e))
   ((equal (car e) 'quote) (fix-values (cadr e)))
   (t (cons (clean-expr (car e))
	    (clean-expr (cdr e))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; forms to create valid values from test cases (for environment)

(defun elim-bad-atoms-and-quote (exp)
  (cond
   ((symbolp exp) exp)
   ((integerp exp) (abs exp))
   ((rationalp exp) (abs (+ (numerator exp) (denominator exp))))
   ((not (consp exp)) (random 10))
   ((equal (car exp) 'quote) (elim-bad-atoms-and-quote (cadr exp)))
   (t (cons (elim-bad-atoms-and-quote (car exp))
	    (elim-bad-atoms-and-quote (cdr exp))))))

(defun coerce-val (pr)
  (list (car pr) (elim-bad-atoms-and-quote (cadr pr))))
(defun coerce-tests (tests) (mapcar #'coerce-val tests))

(defun clean-val (exp)
  (cond
   ((booleanp exp) exp)
   ((symbolp exp) (build-sym exp))
   ((natp exp) (build-num exp))
   ((not (consp exp)) (error "What is this? ~a" exp))
   ((equal (car exp) 'quote)
    (clean-val (cadr exp)))
   ((consp exp)
    (list 'INTERNAL-CONS (clean-val (car exp))
	  (clean-val (cdr exp))))))

(defun clean-pr (pr)
  (list (car pr) (clean-val (cadr pr))))
(defun clean-tests (alist) (mapcar #'clean-pr alist))

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

;; suggest-lemma

(defun subs (x v e)
  (cond
   ((equal e x) `',v)
   ((consp e)
    (if (equal (car e) 'quote) e
      (cons (subs x v (car e))
	    (subs x v (cdr e)))))
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

(defun select-lns (keepers all ths)
  (cond
   ((endp ths) nil)
   ((member (car all) keepers)
    (cons (car ths) (select-lns keepers (cdr all) (cdr ths))))
   (t (select-lns keepers (cdr all) (cdr ths)))))

(defun gg (gs)
  (reduce #'append
	  (mapcar #'(lambda (e) (apply e ())) gs)
	  :initial-value nil))

(defun split-incs (all-lns all-gs ls lns gs exprs)
  (cond
   ((endp ls) (list lns gs exprs))
   ((member (car ls) all-lns)
    (split-incs all-lns all-gs (cdr ls) (cons (car ls) lns) gs exprs))
   ((member (car ls) all-gs)
    (split-incs all-lns all-gs (cdr ls) lns (cons (car ls) gs) exprs))
   (t (split-incs all-lns all-gs (cdr ls) lns gs (cons (car ls) exprs)))))

(defun expr-symbols (ls)
  (cond
   ((symbolp ls) '(var))
   ((booleanp ls) '(boolean))
   ((equal (car ls) 'INTERNAL-NUMBER) '(number))
   ((equal (car ls) 'INTERNAL-SYMBOL) '(symbol))
   ((equal (car ls) 'INTERNAL-CONS) '(cons))
   (t (cons (car ls)
	    (reduce #'append (mapcar #'expr-symbols (cdr ls))
		    :initial-value nil)))))

(defun get-lines (forms all gps)
  (let ((v (split-incs all gps forms nil nil nil)))
    (let ((lines (car v))
	  (group-lines (gg (cadr v)))
	  (exprs (reduce #'append (mapcar #'expr-symbols (caddr v))
			 :initial-value nil)))
      (append lines group-lines exprs))))

(defun new-val-of (keep expr all)
  (cond
   ((endp expr) nil)
   ((member (car all) keep)
    (cons (car expr)
	  (new-val-of keep (cdr expr) (cdr all))))
   (t (new-val-of keep (cdr expr) (cdr all)))))

(defun keywords ()
  '(:required-expressions
    :exclude
    :with
    :hyps))
#|
The keywords for suggest-lemma are:

:required-forms <- These are the sub-expressions/forms that the 
                    returned expression must include

:exclude <- this tells the system to not 
             permit certain forms to be in the expressions 
             (can be forms and groups)

:with <- this tells the system which forms can appear (can be forms and groups)

:restrict (t/nil) <– default is nil. this says 
           that ONLY forms from required-forms
           can be used (if :with is also used, :restrict nil makes the :with pointless, and :restrict adds nothing to the :with clause|#

(defun get-args (e)
  (cond
   ((endp e) (list nil nil))
   ((member (car e) (keywords))
    (list nil e))
   (t (let ((v (get-args (cdr e))))
	(list (cons (car e) (car v))
	      (cadr v))))))

(defun parse-xargs (xargs req excl with hyps)
  (cond
   ((endp xargs) (values req excl with hyps))
   (t (let* ((kw (car xargs))
	     (v (get-args (cdr xargs)))
	     (args (car v))
	     (rst (cadr v)))
	(cond
	 ((equal kw ':required-expressions)
	  (if req (error "Two occurrences of :required-expressions")
	    (parse-xargs rst args excl with hyps)))
	 ((equal kw ':exclude)
	  (if excl (error "Two occurrences of :exclude")
	    (parse-xargs rst req args with hyps)))
	 ((equal kw ':hyps)
	  (if hyps (error "Two occurrences of :exclude")
	    (parse-xargs rst req excl with args)))
	 ((equal kw ':with)
	  (if with (error "Two occurrences of :with")
	    (parse-xargs rst req excl args hyps)))
	 (t (error "invalid keyword ~a" kw)))))))

(defun except (l1 l2)
  (cond
   ((endp l1) nil)
   ((member (car l1) l2)
    (except (cdr l1) l2))
   (t (cons (car l1) (except (cdr l1) l2)))))

;;;; To get hypotheses
(defun make-ex (e tag)
  (if (> (length e) 1) `(,tag . ,e) (car e)))

(defun find-hyps (form)
  (let ((state *the-live-state*))
    (declare (stobjs state))
    (progn!
     (acl2::ld `((mv-let
		  (v g)
		  (acl2s::guard-obligation ',form nil nil 'top-level state)
		  (declare (ignore v))
		  (assign result g))))
     (acl2::@ result))))

(defun free-vars (form)
  (cond
   ((symbolp form) (list form))
   ((consp form)
    (cond
     ((equal (car form) 'quote) nil)
     ((equal (car form) 'let)
      (append (mapcar #'free-vars (mapcar #'cadr (cadr form)))
	      (except
	       (free-vars (caddr form))
	       (mapcar #'car (cadr form)))))
     ((not (symbolp (car form)))
      (reduce #'append (mapcar #'free-vars form)
	      :initial-value nil))
     (t (reduce #'append (mapcar #'free-vars (cdr form))
		:initial-value nil))))
   (t nil)))

(defun include-all-vars (hyps vs)
  (cond
   ((endp vs) hyps)
   ((member (car vs) (free-vars hyps))
    (include-all-vars hyps (cdr vs)))
   (t (include-all-vars (cons `(allp ,(car vs)) hyps) (cdr vs)))))

(defun get-hyps (form)
  (find-hyps form)
  (mapcar #'(lambda (e) (make-ex e 'or))
	  (cadr (@ result))))


(defun subsumed? (e1 e2)
  (let ((state *the-live-state*))
    (declare (stobjs state))
    (progn!
     (acl2::ld `((mv-let
		  (cx? v state)
		  (acl2s::itest? (implies ,e2 ,e1))
		  (declare (ignore v))
		  (assign result (not cx?)))))
     (acl2::@ result))))

(defun simplify-hyps (hyps seen)
  (cond
   ((endp hyps) seen)
   (t (subsumed? (car hyps) `(and ,@(cdr hyps) ,@seen))
      (if (@ result)
	  (simplify-hyps (cdr hyps) seen)
	  (simplify-hyps (cdr hyps) (cons (car hyps) seen))))))

;; using itest?
(defun test-gen (hyps)
  (let ((state *the-live-state*))
    (progn!
     (acl2::ld `((mv-let
		  (cx? v state)
		  (acl2s::itest? (implies ,hyps nil))
		  (assign result (list cx? v)))))
     (acl2::@ result))))

(defun final-test (hyps from to)
  (let ((state *the-live-state*))
    (progn!
     (acl2::ld `((mv-let
		  (cx? v state)
		  (acl2s::itest? (implies ,hyps (equal ,from ,to)))
		  (assign result (list cx? v)))))
     (acl2::@ result))))

(defun get-tests (hyps)
  (test-gen `(and . ,hyps))
  (cdadr (@ result)))

(defun get-final (hyps from to)
  (final-test `(and . ,hyps) from to)
  (@ result))

(defun suggest-lemma-loop (i forms hyps start tests)
  (if (>= i 5)
      (list "COULDN'T FIND A SOLUTION!"
	    "Try adding more hypotheses, or giving extra hints")
    (let* ((cleaned-tests (mapcar #'coerce-tests tests))
	   (new-tests (mapcar #'clean-tests cleaned-tests))
	   (results (mapcar #'clean-val
			    (eval-all start cleaned-tests))))
      (let ((form
	     (read-back
	      (eval `(car (run 1 q (find-equivalent ',forms
						    q
						    ',new-tests
						    ',results)))))))
	(get-final hyps start form)
	(let ((res (@ result)))
	  (if (not (car (@ result)))
	      (list "FOUND" `(implies (and . ,hyps) (equal ,start ,form)) "IN" i "TRIES!")
	    (suggest-lemma-loop (+ i 1) forms hyps start
				(append (cdadr (@ result)) tests))))))))

(defun suggest-lemma-inner (start xargs)
  (multiple-value-bind
   (forms excl with hyps)
   (parse-xargs xargs nil nil nil nil)
   (let* (;;setting up the evaluator
	  (new-forms (clean-expr forms))
	  (req (get-lines new-forms (all-lines) (all-groups)))
	  (incs (if (not with) (cons 'var req)
		  (cons 'var (get-lines with (all-lines) (all-groups)))))
	  (excs (if (not excl) nil
		  (get-lines excl (all-lines) (all-groups))))
	  (lns (append req (except incs excs)))
	  (new-e (new-val-of lns
			     (cdr (expr-for-value-of))
			     (all-lines)))
	  ;; setting up hypotheses
	  (contract-hyps (get-hyps start))
	  (hyps (include-all-vars (simplify-hyps (append contract-hyps hyps) nil)
				  (free-vars start))))
     (eval `(defrel value-of (expr ρ o)
	      (conde . ,new-e)))
     (get-tests hyps)
     (suggest-lemma-loop 1 new-forms hyps start (cdadr (@ result))))))

(defun all-lines ()
  (list 'var
    'boolean 'symbol 'number 'cons
    '+ '- '* 'exp '< '<= '> '>=
    'car 'cdr 'append 'reverse
    'let))

(defun all-groups () '(all-lines))
      
;; organizing expression forms into groups

(defun defgroup-inner (name expressions)
  (progn
    (eval `(defun ,name () ',expressions))
    (let ((gs (all-groups)))
      (defun all-groups ()
	(cons name gs)))))

(defun add-to-group-inner (name expressions)
  (let ((e (apply name ())))
    (eval `(defun ,name ()
	    (append ',expressions ',e)))))


