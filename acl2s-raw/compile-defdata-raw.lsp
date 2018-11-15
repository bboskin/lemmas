(in-package "ACL2S")

#|
(load "helpers-raw.lsp")
(load "mk-raw.lsp")
(load "numbers-raw.lsp")
(load "primitives-raw.lsp")
|#
(defun all-types ()
  '((nat natpo natpo-fn)
    (pos pospo pospo-fn)
    (neg negpo negpo-fn)
    (integer integerpo integerpo-fn)
    (rational rationalpo rationalpo-fn)
    (number numberpo numberpo-fn)
    (symbol symbolpo symbolpo-fn)
    (var varpo varpo-fn)
    (string stringpo stringpo-fn)
    (character charpo charpo-fn)
    (cons conspo conspo-fn)
    (list listpo listpo-fn)
    (true-list true-listpo true-listpo-fn)))

(defun defdata-make-val (exp)
  (cond
   ((booleanp exp) exp)
   ((symbolp exp) (build-sym exp))
   ((characterp exp) (build-char exp))
   ((stringp exp) (build-string exp))
   ((rationalp exp) (build-num exp))
   ((consp exp)
    (list 'INTERNAL-CONS (defdata-make-val (car exp))
	  (defdata-make-val (cdr exp))))))

(defun desugar-list (es)
  (cond
   ((endp es) nil)
   (t `(cons ,(car es)
	     ,(desugar-list (cdr es))))))

(defun desugar-list* (es)
  (cond
   ((endp es) nil)
   ((endp (cdr es)) (car es))
   (t `(cons ,(car es)
	     ,(desugar-list* (cdr es))))))


(defun clean-range (n)
  (cond
   ((numberp n) (build-num n))
   (t (let ((_ (ld `((assign result ,n)))))
	(build-num (@ result))))))

(defun finish-range (input lt lte gt gte)
  (let ((gt-exp (mapcar #'(lambda (e)`(do-less-than-o ',e ,input)) gt))
	(gte-exp (mapcar #'(lambda (e) `(do-less-than-equal-o ',e ,input)) gte))
	(lt-exp (mapcar #'(lambda (e) `(do-less-than-o ,input ',e)) lt))
	(lte-exp (mapcar #'(lambda (e) `(do-less-than-equal-o ,input ',e)) lte)))
    `(conj ,(append lt-exp lte-exp gt-exp gte-exp))))


(defun compile-range-3 (v1 v2 cmp input)
  (cond
   ((and (equal v1 '_) (equal cmp '<))
    (finish-range input (list (clean-range v2)) nil nil nil))
   ((and (equal v1 '_) (equal cmp '<=))
    (finish-range input nil (list (clean-range v2)) nil nil))
   ((and (equal v2 '_) (equal cmp '<))
    (finish-range input nil nil (list (clean-range v1)) nil))
   ((and (equal v2 '_) (equal cmp '<=))
    (finish-range input nil nil nil (list (clean-range v1))))))

(defun compile-range-5 (v1 v2 cmp1 cmp2 input)
  (cond
   ((and (equal cmp1 '<) (equal cmp2 '<))
    (finish-range input (list (clean-range v2)) nil
		  (list (clean-range v1)) nil))
   ((and (equal cmp1 '<) (equal cmp2 '<=))
    (finish-range input nil (list (clean-range v2))
		  (list (clean-range v1)) nil))
   ((and (equal cmp1 '<=) (equal cmp2 '<))
    (finish-range input (list (clean-range v2)) nil
		  nil (list (clean-range v1))))
   ((and (equal cmp1 '<=) (equal cmp2 '<=))
    (finish-range input nil (list (clean-range v2))
		  nil (list (clean-range v1))))))

(defun compile-range (e input)
  (cond
   ;; if there is only one comparator
   ((equal (len e) 3)
    (let ((v1 (car e)) (cmp (cadr e)) (v2 (caddr e)))
      (compile-range-3 v1 v2 cmp input)))
   ((equal (len e) 5)
    (let ((v1 (car e)) (v2 (cadddr (cdr e)))
	  (cmp1 (cadr e)) (cmp2 (cadddr e)))
      (if (not (equal (caddr e) '_))
	  (error "Range expected the middle term to be '_")
	(compile-range-5 v1 v2 cmp1 cmp2 input))))))

(defun compile-defdata (expr input self)
  (cond
   ;; constants
   ((booleanp expr) `(== ,expr ,input))
   ((numberp expr) `(== ',(build-num expr) ,input))
   ((characterp expr) `(== ',(build-char expr) ,input))
   ((stringp expr) `(== ',(build-string expr) ,input))
   ;; other type symbols (the type being made has been added to this list)
   ((symbolp expr)
    (let ((p (assoc expr (all-types))))
      (if p `(,(cadr p) ,input)
	(error "Unknown symbol ~s" expr))))
   ((consp expr)
    (cond
     ;; constants under quote
     ((equal (car expr) 'quote)
      `(== ,input ',(defdata-make-val (cadr expr))))
     ;; oneof -> disjunction
     ((equal (car expr) 'oneof)
      `(disj ,(mapcar #'(lambda (e)
			  (compile-defdata e input self))
		      (cdr expr))))
     ((equal (car expr) 'cons)
      (let ((e1 (next-var))
	    (e2 (next-var)))
	`(fresh (,e1 ,e2)
		(conso ,e1 ,e2 ,input)
		,(compile-defdata (cadr expr) e1 self)
		,(compile-defdata (caddr expr) e2 self))))
     ;; listof, list, and list*, and alistof can all just be desugared
     ((equal (car expr) 'listof)
      (let ((elem-type (cadr expr)))
	`(disj2 (== ,input nil)
		,(compile-defdata `(cons ,elem-type ,self) input self))))
     ((equal (car expr) 'alistof)
      (let ((key-type (cadr expr))
	    (val-type (cadr expr)))
	(compile-defdata `(listof (cons ,key-type ,val-type)) input self)))
     ((equal (car expr) 'list)
      (compile-defdata (desugar-list (cdr expr)) input self))
     ((equal (car expr) 'list*)
      (compile-defdata (desugar-list* (cdr expr)) input self))
     ((equal (car expr) 'range)
      (let ((type (cadr expr))
	    (range (caddr expr)))
	(let* ((v (assoc type (all-types)))
	       (vp (if v (cadr v) (error "Unknown range type ~s" type))))
	  `(conj2 (,vp ,input)
		  ,(compile-range range input)))))
     ((equal (car expr) 'enum)
      (let* ((_ (ld `((assign result ,(cadr expr)))))
	     (ls (defdata-make-val (@ result))))
	`(membero-fn ,input ',ls t)))
     ;; Otherwise, it is some expression to be evaluated
     (t (let ((_ (ld `((assign result ,expr)))))
	  (compile-defdata `',(@ result) input self)))))
   (t (error "Invalid datatype ~s" expr))))

(defun defdata2-- (name expr)
  (let* ((pred-name (get-pred-name name))
	 (rel-name (get-rel-name pred-name)))
    (let* ((input (next-var))
	   (expr (compile-defdata expr input name)))
      `(defrel ,rel-name (,input) ,expr))))

(defun update-types (es)
  (let ((ts (all-types))
	(new (mapcar #'(lambda (x)
			 (let ((p (get-pred-name x)))
			   (list x (get-rel-name p) (get-rel-fn-name p))))
		     es)))
    (defun all-types ()
      (append ts new))))


(defun make-fn-version-clause (name)
  `((,name e) (== o nil)))

(defun make-fn-version (form)
  (let* ((form-rel (get-rel-name form))
	 (form-rel-fn (get-rel-fn-name form)))
    `(defrel ,form-rel-fn (e o)
       (conde
	((,form-rel e) (== o t))
	. ,(mapcar #'make-fn-version-clause
		   (mapcar #'cadr (all-types)))))))


#|
(defun defdata2- (exprs)
  (cond
   ((endp exprs) (error "Defdata2 expected to receive arguments, received nothing"))
   ;; single defs
   ((symbolp (car exprs))
    (progn
      (update-types (list (car exprs)))
      (defdata2-- (car exprs) (cadr exprs))))
   ;; mutually recursive defs
   (t (progn
	(update-types (mapcar #'car exprs))
	`(progn . ,(mapcar #'(lambda (a) (defdata2-- (car a) (cadr a)))
			   exprs))))))
|#
#|
(defdata2 '(foo (listof nat)))

(defdata2 '(bar (oneof 0 1/2 (listof character))))


(defdata2 '(expr
	    (oneof (list 'load nat var)
		    (list 'mult nat nat)
		    (list 'add nat nat)
		    (list 'pop var))))

(defdata2
  '((foo (oneof t nil))
    (bar (oneof foo nat))))

(defdata2 '(quo (oneof cons (append '(1 2) '(2 3)))))

(defdata2 '(foo (range integer (3 < _ <= 7))))

(defdata2 '(foo (range integer (3 <= _ < 5))))

(defdata2 '(bar (range rational (_ <= 4/5))))

(defdata2 '(bar (range nat (44 < _))))

(defdata2 '(enum1 (enum '(1 2 3))))

(defdata2 '(enum2 (enum (append nil nil nil nil nil))))
|#
