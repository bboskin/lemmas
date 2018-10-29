(defun add-constraint (name c vars)
  (cond
   ((equal (caar vars) name)
    (cons (list (cons name (cons c (cadar vars))))
	  (cdr vars)))
   (t (cons (car vars) (add-constraint name c (cdr vars))))))

(defun decide-cons-type-car (p? l? e)
  (cond
   (p? (cadr e))
   (l? (cadr e))
   (t 'any)))

(defun decide-cons-type-cdr (p? l? e)
  (cond
   (p? (cadr e))
   (l? (caddr e))
   (t 'any)))

(defun collect-constraints (expr vars ty-req)
  (cond
   ((numberp expr) vars)
   ((equal expr 't) vars)
   ((equal expr 'nil) vars)
   ((assoc expr vars)
    (if (equal ty-req 'any) vars
      (add-constraint expr ty-req vars)))
   ((equal (car expr) 'cons)
    (let* ((pair? (and (consp ty-req) (equal (car ty-req) 'pair)))
	   (list? (and (consp ty-req) (equal (car ty-req) 'listof)))
	   (res1-req (decide-cons-type-car pair? list? ty-req))
	   (res2-req (decide-cons-type-cdr pair? list? ty-req)))
      (let ((res1 (collect-constraints (cadr expr) vars res1-req)))
	(collect-constraints (caddr expr) res1 res2-req))))
   ((equal (car expr) 'car)
    (collect-constraints (cadr expr) vars `(pair ,ty-req any)))
   ((equal (car expr) 'cdr)
    (collect-constraints (cadr expr) vars `(pair any ,ty-req)))
   ((equal (car expr) 'append)
    (let ((res1 (collect-constraints (cadr expr) vars '(listof any))))
      (collect-constraints (caddr expr) res1 'any)))
   ((equal (car expr) 'reverse)
    (collect-constraints (cadr expr) vars '(listof any)))
   ((or (equal (car expr) '+) (equal (car expr) '*))
    (and (equal ty-req 'nat)
	 (let ((res1 (collect-constraints (cadr expr) vars 'nat)))
	   (collect-constraints (caddr expr) res1 'nat))))))













(defrel membero (x ls)
  (fresh (a d)
	 (== ls `(,a . ,d))
	 (conde
	  ((== x a))
	  ((membero x d)))))



#|
Cons, Car, Cdr, Append, Reverse
And, Or
Cond
|#

(defrel typeo (ty)
  (conde
   ((== ty 'All))
   ((== ty 'Nat))
   ((== ty 'Boolean))
   ((fresh (a d)
	   (== ty `(Pair ,a ,d))
	   (typeo a)
	   (typeo d)))
   ((fresh (a)
	   (== ty '(Listof ,a))
	   (typeo a)))))

;;;;;;;;;;;;;;;;;;;;;;
;; Type inference

(defrel ty-is-tlp? (ty)
  (conde
   ((== ty 'List))
   ((fresh (a d)
	   (== ty `(Pair ,a ,d))
	   (ty-is-tlp d)))))

(defrel type-of (e var ty)
  (conde
   ((== e var))
   ((== e 't) (== ty 'Boolean))
   ((== e 'nil)
    (conde
     ((== ty 'Boolean)
      (fresh (e) (== ty 'List)))))
   ((fresh (a d ty-a ty-d ty-a ty-b)
	   (== e `(cons ,a ,d))
	   (== ty `(Pair ,ty-a ,ty-b))
	   (type-of a ty-a)
	   (type-of a ty-d)))
   ((fresh (pr ty-cdr)
	   (== e `(car ,pr))
	   (type-of pr `(Pair ,ty ,ty-cdr))))
   ((fresh (pr ty-car)
	   (== e `(cdr ,pr))
	   (type-of pr `(Pair ,ty-car ,ty))))
   ((fresh (== e '(cond))
	   (type-of 'nil vars ty)))))
