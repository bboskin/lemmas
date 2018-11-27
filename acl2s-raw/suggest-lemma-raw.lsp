(in-package "ACL2S")

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
   ((equal (car ls) 'INTERNAL-STRING) '(string))
   ((equal (car ls) 'INTERNAL-CHAR) '(char))
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
    :with
    :hyps
    :exclude
    :complete-hyps
    :num-trials))
#|
The keywords for suggest-lemma are:

:required-forms <- These are the sub-expressions/forms that the 
                    returned expression must include

:complete-hyps <- when set to nil, this tells the 
                  system that all desired hyps are included 

:with <- this tells the system which forms can appear (can be forms and groups)

:exclude <- tells the system for forms to exclude

:num-trials <- overrides the max # of iterations from 5 to whatever is set

|#

(defun get-args (e)
  (cond
   ((endp e) (list nil nil))
   ((member (car e) (keywords))
    (list nil e))
   (t (let ((v (get-args (cdr e))))
	(list (cons (car e) (car v))
	      (cadr v))))))

(defun parse-xargs (xargs req excl with hyps complete? trials)
  (cond
   ((endp xargs) (values req excl with hyps complete? trials))
   (t (let* ((kw (car xargs))
	     (v (get-args (cdr xargs)))
	     (args (car v))
	     (rst (cadr v)))
	(cond
	 ((equal kw ':required-expressions)
	  (if req (error "Two occurrences of :required-expressions")
	    (parse-xargs rst args excl with hyps complete? trials)))
	 ((equal kw ':complete-hyps)
	  (if excl (error "Two occurrences of :complete-hyps")
	    (if (not (and (equal (length args) 1) (booleanp (car args))))
		(error "Expected one boolean in :complete-hyps")
	      (parse-xargs rst req excl with hyps (car args) trials))))
	 ((equal kw ':num-trials)
	  (if excl (error "Two occurrences of :num-trials")
	    (if (not (and (equal (length args) 1) (natp (car args))))
		(error "Expected one nat in :num-trials")
	      (parse-xargs rst req excl with hyps complete? (car args)))))
	 ((equal kw ':exclude)
	  (if excl (error "Two occurrences of :exclude")
	    (parse-xargs rst req args with hyps complete? trials)))
	 ((equal kw ':hyps)
	  (if hyps (error "Two occurrences of :hyps")
	    (parse-xargs rst req excl with args complete? trials)))
	 ((equal kw ':with)
	  (if with (error "Two occurrences of :with")
	    (parse-xargs rst req excl args hyps complete? trials)))
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

(defun find-hyps (form complete?)
  (let ((state *the-live-state*))
    (declare (stobjs state))
    (progn!
     (acl2::ld `((mv-let
		  (v g)
		  (if ,complete?
		      (acl2s::guard-obligation ',form nil nil 'top-level state)
		    (mv nil '(nil nil)))
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

(defun get-hyps (form compl?)
  (cond
   ((symbolp form) nil)
   (t (find-hyps form compl?)
      (mapcar #'(lambda (e) (make-ex e 'or))
	      (cadr (@ result))))))

(defun subsumed? (e1 e2)
  (let ((state *the-live-state*))
    (declare (stobjs state))
    (progn!
     (acl2::ld `((mv-let
		  (cx? v state)
		  (acl2s::thm (implies ,e2 ,e1))
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


(defun remove-allp-hyps (hyps)
  (remove-if-not
   #'(lambda (e)
       (not (and (consp e) (equal (car e) 'allp))))
		 hyps))

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

(defun final-statement (hyps start form)
  (let* ((hyps (remove-allp-hyps hyps))
	 (expr (if (equal start t) form `(equal ,start ,form)))
	 (msg (if (equal start form)
		  "Please provide more constraints on the expression you would like me to find. The best I can do is:"
		"We found the following potential theorem:"))
	 (res (cond
	       ((endp hyps) expr)
	       ((equal (length hyps) 1)
		`(implies ,(car hyps) ,expr))
	       (t `(implies (and . ,hyps) ,expr)))))
    (cw "***********Beginning of Synthesis Output*****************")
    (print msg)
    (print "")
    res))


(defun final-statement/no-print (hyps start form)
  (let* ((hyps (remove-allp-hyps hyps))
	 (expr (if (equal start t) form `(equal ,start ,form)))
	 (res (cond
	       ((endp hyps) expr)
	       ((equal (length hyps) 1)
		`(implies ,(car hyps) ,expr))
	       (t `(implies (and . ,hyps) ,expr)))))
    res))


(defun suggest-lemma-loop (i max forms hyps start tests old-v-of)
  (if (>= i max)
      (progn
	(eval `(defrel value-of (expr ρ o) ,old-v-of))
	(list "COULDN'T FIND A SOLUTION!"
	      "Try adding more hypotheses, or giving extra hints"))
    (let* ((cleaned-tests (mapcar #'coerce-tests tests))
	   (new-tests (mapcar #'clean-tests cleaned-tests))
	   (results (mapcar #'clean-val
			    (eval-all start cleaned-tests))))
      (print "Beginning another round of synthesis. If this takes a long time, consider adding more :required-expressions or hypotheses!")
      (let ((form
	     (read-back
	      (eval `(car (run 1 q (find-equivalent ',forms
						    q
						    ',new-tests
						    ',results)))))))
	(get-final hyps start form)
	(let ((res (@ result)))
	  (cond
	   ((not (car (@ result)))
	    (progn
	      (eval `(defrel value-of (expr ρ o) ,old-v-of))
	      (final-statement hyps start form)))
	   ((= i max)
	    (progn
	      (eval `(defrel value-of (expr ρ o) ,old-v-of))
	      (cw "***********Beginning of Synthesis Output*****************")
	      (list "COULDN'T FIND A SOLUTION!"
		    "Try adding more hypotheses, or giving extra hints"
		    "Here's the best thing I could find:")
	      (final-statement/no-print hyps start form)))
	   (t (print "Our best answer so far is:")
	      (print `(implies ,hyps (equal ,start ,form)))
	      (suggest-lemma-loop (+ i 1) max forms hyps start
				  (append (cdadr (@ result)) tests) old-v-of))))))))

(defun suggest-lemma-inner (start xargs)
  (let ((start (preprocess start)))
    (multiple-value-bind
     (forms excl with hyps compl? max)
     (parse-xargs xargs nil nil nil nil t 5)
     (let* (;;setting up the evaluator
	    (new-forms (clean-expr forms))
	    (req (get-lines new-forms (all-forms) (all-groups)))
	    (incs (if (not with) (cons 'var (cons 'boolean req))
		    (cons 'var (get-lines with (all-forms)
					  (all-groups)))))
	    (excs (if (not excl) nil
		    (get-lines excl (all-forms) (all-groups))))
	    (lns (append req (except incs excs)))
	    (old-v-of (expr-for-value-of))
	    (new-e (new-val-of lns
			       (cdr old-v-of)
			       (all-forms)))
	    ;; setting up hypotheses
	    (contract-hyps (get-hyps start compl?))
	    (hyps (include-all-vars (append contract-hyps hyps)
				    (free-vars start))))
       (eval `(defrel value-of (expr ρ o)
		(conde . ,new-e)))
       (get-tests hyps)
       (suggest-lemma-loop 1 max new-forms hyps start (cdadr (@ result)) old-v-of)))))

(defun all-forms ()
  (append 
   '(var boolean symbol number string char cons car cdr let if cond)
   (mapcar #'car lemma-built-ins)))

(defun all-groups () '(all-forms))
      
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


