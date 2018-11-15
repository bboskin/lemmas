(defttag t)

(include-book "top" :uncertified-okp t)

(defdata2 loi (listof integer))


(defunc2 find-max (ls)
  :input-contract (loip ls)
  :output-contract (integerp (find-max ls))
  (cond
   ((endp ls) -100)
   ((loip ls)
    (let ((res (find-max (cdr ls)))
	  (a (car ls)))
      (if (> a res)
	  a res)))))


(suggest-lemma -100 :with find-max boolean)


(defdata2
  (inc-expr (list 'inc expr))
  (let-expr (list 'let var expr expr))
  (expr (oneof var nat inc-expr let-expr)))

(defdata2 asst (alistof var nat))

(defthm inc-cadr
  (implies (inc-exprp e)
	   (exprp (cadr e))))

(defthm inc-cons (implies (inc-exprp e) (consp (cdr e))))

(defthm let-cadr
  (implies (let-exprp e)
	   (exprp (cadr e))))

(defthm let-caddr
  (implies (let-exprp e)
	   (exprp (caddr e))))

(defthm let-cons
  (implies (let-exprp e) (consp (cdr e))))

(defthm let-cons2
  (implies (let-exprp e) (consp (cddr e))))

(defdata-disjoint inc-expr let-expr)



(defunc2 assv (x ls)
  :input-contract (and (varp x) (asstp ls))
  :output-contract (or (equal (assv x ls) nil)
		       (consp (assv x ls)))
  (cond
   ((endp ls) nil)
   ((equal x (car (car ls))) (car ls))
   (t (assv x (cdr ls)))))


(suggest-lemma (assv x ls) :with assv)


(defunc2 closedp (exp vars)
  :input-contract (and (exprp exp) (asstp vars))
  :output-contract (booleanp (closedp exp vars))
  (cond
   ((natp exp) t)
   ((varp exp) (if (assv exp vars) t nil))
   ((inc-exprp exp) (closedp (car (cdr exp)) vars))
   ((let-exprp exp)
    (let ((x (car (cdr exp)))
	  (a (car (cdr (cdr exp))))
	  (body (car (cdr (cdr (cdr exp))))))
      (let ((new-vars (cons (cons x 0) vars)))
	(and (closedp a vars)
	     (closedp body new-vars)))))))

(defthm inc-all
  (implies (inc-exprp x)
	   (and (consp x)
		(consp (cdr x))
		(exprp (cadr x)))))

(defthm nat-exp
  (implies (natp e) (exprp e)))

(defthm destruct-expr
  (equal (exprp e)
	 (or (natp e)
	     (varp e)
	     (inc-exprp e)
	     (let-exprp e))))

(in-theory (disable exprp))

(defunc2 eval-expr (exp rho)
  :input-contract (and (exprp exp) (asstp rho))
  :output-contract (natp (eval-expr exp rho))
  (cond
   ((natp exp) exp)
   ((varp exp)
    (let ((v (assv exp rho)))
      (if v (cdr v) 0)))
   ((inc-exprp exp)
    (+ 1 (eval-expr 0 rho)))
   #|((let-exprp exp)
   (let* ((x (car (cdr exp)))
   (a (car (cdr (cdr exp))))
   (b (car (cdr (cdr (cdr exp))))))
   (let ((a-v (eval-expr a rho)))
   (let ((new-rho (cons (cons x a-v) rho)))
      (eval-expr b new-rho)))))|#
   (t 0)))


(suggest-lemma 4
	       :required-expressions eval-expr
	       :with number)
