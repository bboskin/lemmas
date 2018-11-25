(in-package "ACL2S")

;; Just a function for a common idiom
(defun has-form (s e)
  (and (consp e) (equal (car e) s)))

; Creating new variable names
(defun next-index () 0)
(defun next-var ()
  (let ((i (next-index)))
    (progn
      (defun next-index () (+ 1 i))
      (intern (concatenate 'string
			   "fresh-var"
			   (get-name i))))))

(defun get-name (n)
  (cond
   ((equal n 0) "0")
   ((equal n 1) "1")
   ((equal n 2) "2")
   ((equal n 3) "3")
   ((equal n 4) "4")
   ((equal n 5) "5")
   ((equal n 6) "6")
   ((equal n 7) "7")
   ((equal n 8) "8")
   ((equal n 9) "9")
   (t (concatenate 'string
		   (get-name (floor n 10))
		   (get-name (mod n 10))))))

;; The name of a miniKanrenized function
(defun get-rel-name (name)
  (intern-in-package-of-symbol
   (concatenate 'string (string name) "-REL")
   'acl2s::allp))

(defun get-rel-fn-name (name)
  (intern-in-package-of-symbol
   (concatenate 'string (string name) "-REL-FN")
   'acl2s::allp))

(defun get-pred-name (name)
  (intern-in-package-of-symbol (concatenate 'string (string name) "P")
			       'acl2s::allp))
;; functions for converting ACL2S values to MK values

(defun fix-atom (e)
  (cond
   ((symbolp e) e)
   ((characterp e) (build-char e))
   ((stringp e) (build-string e))
   ((rationalp e) (build-num e))
   ;; complex numbers become nil
   (t nil)))


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

(defun elim-quote (exp)
  (cond
   ((symbolp exp) exp)
   ((not (consp exp)) exp)
   ((equal (car exp) 'quote) (elim-quote (cadr exp)))
   (t (cons (elim-quote (car exp))
	    (elim-quote (cdr exp))))))

(defun coerce-val (pr)
  (list (car pr) (elim-quote (cadr pr))))

(defun coerce-tests (tests)
  (mapcar #'coerce-val tests))

(defun clean-val (exp)
  (cond
   ((booleanp exp) exp)
   ((symbolp exp) (build-sym exp))
   ((not (consp exp)) (fix-atom exp))
   ((equal (car exp) 'quote) (clean-val (cadr exp)))
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
       ((equal tag 'INTERNAL-VARSYMBOL) (cadr v))
       ((equal tag 'INTERNAL-CHAR) (cadr v))
       ((equal tag 'INTERNAL-NUMBER) (read-back-num v))
       ((equal tag 'INTERNAL-STRING) (read-back-string (cdr v)))
       ((equal tag 'INTERNAL-CONS)
	(cons (read-back (cadr v))
	      (read-back (caddr v))))
       (t (cons (read-back tag)
		(read-back (cdr v)))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Global tables to keep track of
;; all function symbols, 'boolean' function symbols,
;; and their relational counterparts and arities

(defparameter lemma-built-ins
  '((append nil nil appendo) (reverse 1 reverso) (len 1 leno) (member 2 membero-fn)
    (+ nil 0 do-pluso) (- 2 do-minuso) (* nil 1 do-timeso)
    (sqr 1 do-sqro) (expt 2 do-expto)
    (< 2 do-less-than-o-fn) (<= 2 do-less-than-equal-o-fn)
    (> 2 do-greater-than-o-fn) (>= 2 do-greater-than-equal-o-fn)
    (and nil t ando) (or nil nil oro) (not 1 noto)
    (booleanp 1 booleanpo-fn) (symbolp 1 symbolpo-fn)
    (varp 1 varpo-fn) (consp 1 conspo-fn) (symbolp 1 symbolpo-fn)
    (endp 1 endpo-fn) (equal 2 ==-fn) (atom 1 atomo-fn)
    (listp 1 listpo-fn) (true-listp 1 true-listpo-fn)
    (zerop 1 zeropo-fn) (numberp 1 numberpo-fn)
    (natp 1 natpo-fn) (integerp 1 integerpo-fn) (posp 1 pospo-fn)
    (negp 1 negpo-fn) (rationalp 1 rationalpo-fn)
    (numerator 1 numeratoro) (denominator 1 denominatoro)
    (stringp 1 stringpo-fn) (characterp 1 charpo-fn)
    (string-append nil nil concato) (length 1 str-leno)
    (subseq 3 subseqo)))


;; if a function is known, this returns the expected arity and relation symbol,
;; otherwise errors.
(defun function-is-known? (fn)
  (let ((v (assoc fn lemma-built-ins)))
    (if v (cdr v)
      (error "Unknown function symbol ~s" fn))))

;; the same thing but for booleans
(defparameter built-ins-bool
  '((equal 2 ==)
    (varp 1 varpo) (booleanp 1 booleanpo) (symbolp 1 symbolpo) (endp 1 endpo)
    (consp 1 conspo) (stringp 1 stringpo) (characterp 1 charpo) (atom 1 atomo)
    (listp 1 listpo) (true-listp 1 true-listpo)
    (< 2 do-less-than-o) (<= 2 do-less-than-equal-o)
    (> 2 do-greater-than-o) (>= 2 do-greater-than-equal-o)
    (zerop 1 zeropo) (numberp 1 numberpo)
    (natp 1 natpo) (integerp 1 integerpo) (posp 1 pospo)
    (negp 1 negpo) (rationalp 1 rationalpo)))

(defun function-is-known-bool? (fn)
  (let ((v (assoc fn built-ins-bool)))
    (if v (cdr v)
      (error "Unknown boolean function symbol ~s" fn))))

;; to desugar some forms that would be nice
(defun do-list (es term)
  (cond
   ((endp es) nil)
   ((endp (cdr es))
    (let ((e (preprocess (car es))))
      (if term e `(cons ,e nil))))
   (t (let ((e (preprocess (car es))))
	`(cons ,e ,(do-list (cdr es) term))))))

(defun preprocess (exp)
  (cond
   ((not (consp exp)) exp)
   ((equal (car exp) 'quote) exp)
   ((equal (car exp) 'first) `(car ,(preprocess (cadr exp))))
   ((equal (car exp) 'second) `(car (cdr ,(preprocess (cadr exp)))))
   ((equal (car exp) 'third) `(car (cdr (cdr ,(preprocess (cadr exp))))))
   ((equal (car exp) 'fourth) `(car (cdr (cdr (cdr ,(preprocess (cadr exp)))))))
   ((equal (car exp) 'rest) `(cdr ,(preprocess (cadr exp))))
   ((equal (car exp) 'caar) `(car (car ,(preprocess (cadr exp)))))
   ((equal (car exp) 'cadr) `(car (cdr ,(preprocess (cadr exp)))))
   ((equal (car exp) 'cdar) `(cdr (car ,(preprocess (cadr exp)))))
   ((equal (car exp) 'cddr) `(cdr (cdr ,(preprocess (cadr exp)))))
   ((equal (car exp) 'caaar) `(car (car (car ,(preprocess (cadr exp))))))
   ((equal (car exp) 'caadr) `(car (car (cdr ,(preprocess (cadr exp))))))
   ((equal (car exp) 'cadar) `(car (cdr (car ,(preprocess (cadr exp))))))
   ((equal (car exp) 'caddr) `(car (cdr (cdr ,(preprocess (cadr exp))))))
   ((equal (car exp) 'cdaar) `(cdr (car (car ,(preprocess (cadr exp))))))
   ((equal (car exp) 'cdadr) `(cdr (car (cdr ,(preprocess (cadr exp))))))
   ((equal (car exp) 'cddar) `(cdr (cdr (car ,(preprocess (cadr exp))))))
   ((equal (car exp) 'cdddr) `(cdr (cdr (cdr ,(preprocess (cadr exp))))))
   ((equal (car exp) 'list) (do-list (cdr exp) nil))
   ((equal (car exp) 'list*) (do-list (cdr exp) t))
   ((symbolp (car exp)) (cons (car exp) (mapcar #'preprocess (cdr exp))))
   (t (cons (mapcar #'preprocess (car exp))
	    (mapcar #'preprocess (cdr exp))))))
