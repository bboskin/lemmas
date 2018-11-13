;(load "helpers-raw.lsp")

;; Just a function for a common idiom
(defun has-form (s e)
  (and (consp e) (equal (car e) s)))

;; Go: a guard to decide if recursion is necessary.
(defun miniKanrenize-go (e)
  (cond
   ((symbolp e) `(nil ,e))
   ((numberp e) `(nil ',(build-num e)))
   (t (let ((v (next-var)))
	(list t v (miniKanrenize e v))))))

;; compile-recur: takes the inputs which may or may not have required
;; recursion, and introduce the necessary fresh variables
;; for miniKanrenize-bool, dest is nil (and otherwise guaranteed to be non-nil)
(defun complete-recursion-inner (form vars dest es work has-dest?)
  (cond
   ((endp es)
    (if has-dest?
	(if vars `(fresh ,vars ,@work (,@form ,dest))
	  `(,@form ,dest))
      (if vars `(fresh ,vars ,@work ,form) form)))
   (t (let ((curr (car es)))
	(if (car curr)
	    (complete-recursion-inner `(,@form ,(cadr curr))
				(cons (cadr curr) vars)
				dest (cdr es)
				(cons (caddr curr) work)
				has-dest?)
	  (complete-recursion-inner `(,@form ,(cadr curr))
				    vars dest (cdr es) work
				    has-dest?))))))

(defun complete-recursion (form dest es)
  (complete-recursion-inner form nil dest es nil t))
(defun complete-recursion-bool (form es)
  (complete-recursion-inner form nil nil es nil nil))

;; The main function to create miniKanren expressions.
;; These forms are expected to return a value.
;; cond and if call the recursive function miniKanrenize-bool, which
;; creates dest-less expressions not expected to generate output

(defparameter built-ins
  '((cons 2 conso) (car 1 caro) (cdr 1 cdro)
    (append 2 appendo) (reverse 1 reverso) (len 1 leno)
    (+ 2 do-pluso) (- 2 do-minuso) (* 2 do-timeso) (sqr 1 do-sqro)
    (< 2 do-less-than-o-fn) (<= 2 do-less-than-equal-o-fn)
    (> 2 do-greater-than-o-fn) (>= 2 do-greater-than-equal-o-fn)
    (and nil ando) (or nil oro) (not 1 noto)
    (booleanp 1 booleanpo-fn) (symbolp 1 symbolpo-fn)
    (varp 1 varpo-fn) (consp 1 conspo-fn) (symbolp 1 symbolpo-fn)
    (endp 1 endpo-fn)
    ;; numbers (has changed)
    (zerop 1 zeropo-fn) (numberp 1 numberpo-fn)
    (natp 1 natpo-fn) (integerp 1 integerpo-fn) (posp 1 pospo-fn)
    (negp 1 negpo-fn) (rationalp 1 rationalpo-fn)
    (numerator 1 numeratoro) (denominator 1 denominatoro)
    ;; strings and chars
    (stringp 1 stringpo-fn) (characterp 1 charpo-fn)
    (concat 2 concato) (length 1 str-leno)
    (subseq 2 subseqo)))

(defun do-rec (form es dest)
  (let ((es (mapcar #'miniKanrenize-go es))
	(v (assoc form built-ins)))
    (if v
	(if (or (not (cadr v)) (equal (length es) (cadr v)))
	    (complete-recursion (cddr v) dest es)
	  (error "Wrong number of args given to ~a" form))
      (let ((name (get-rel-name form)))
	(complete-recursion `(,name) dest es)))))

(defun miniKanrenize (expr dest)
  (cond
   ;; base cases
   ((booleanp expr) `(== ,expr ,dest))
   ((numberp expr) `(== ',(build-num expr) ,dest))
   ((symbolp expr) `(== ,expr ,dest))
   ((has-form 'quote expr) `(== ',(build-sym expr) ,dest))
   ;; Special cases: let, control flow
   ((has-form 'let expr) (miniKanrenize-let expr dest))
   ((has-form 'let* expr) (miniKanrenize-let* expr dest))
   ;; control flow
   ((has-form 'cond expr)
    `(conde . ,(miniKanrenize-cond (cdr expr) dest)))
   ((has-form 'if expr) (miniKanrenize-if expr dest))
   ;; subseq – since it 
   ;; the majority of forms can be handled equivalently
   ((consp expr) (do-rec (car expr) (cdr expr) dest))
   ;; anything else fails
   (t `(fail))))

;;;;;;;;;;;;;;;
;; miniKanrenize helpers for special cases

;; conditionals
(defun miniKanrenize-cond (lines dest)
  (cond
   ((endp lines) '(((fail))))
   (t (let ((line1 (car lines)))
	(if line1
	    (cons
	     `(,(miniKanrenize-bool (car line1))
	       ,(miniKanrenize (cadr line1) dest))
	     (miniKanrenize-cond (cdr lines) dest))
	  `(((fail))))))))

(defun miniKanrenize-if (expr dest)
  (let ((test (cadr expr))
	(then (caddr expr))
	(alt (cadddr expr)))
    `(conde . ,(miniKanrenize-cond (list (list test then)
					 (list `(not ,test) alt))
				   dest))))

;; let statements

(defun miniKanrenize-let (expr dest)
  (let ((body (miniKanrenize (caddr expr) dest)))
    (miniKanrenize-let- (cadr expr) nil nil body)))

(defun miniKanrenize-let- (lines vars work body)
  (cond
   ((endp lines) `(fresh ,vars ,@work ,body))
   (t (let ((x (caar lines))
	    (e (cadar lines)))
	(miniKanrenize-let- (cdr lines) `(,@vars ,x)
			    `(,@work ,(miniKanrenize e x)) body)))))

(defun miniKanrenize-let* (expr dest)
  (let ((body (miniKanrenize (caddr expr) dest)))
    (miniKanrenize-let*- (cadr expr) body)))

(defun miniKanrenize-let*- (lines body)
  (cond
   ((endp lines) body)
   (t (let ((x (caar lines))
	    (e (cadar lines)))
	`(fresh (,x)
		,(miniKanrenize e x)
		,(miniKanrenize-let*- (cdr lines) body))))))

;; booleans
(defparameter built-ins-bool
  '((equal 2 ==)
    (varp 1 varpo) (booleanp 1 booleanpo) (symbolp 1 symbolpo) (endp 1 endpo)
    (consp 1 conspo) (stringp 1 stringpo) (characterp 1 charpo)
    (< 2 do-less-than-o) (<= 2 do-less-than-equal-o)
    (> 2 do-greater-than-o) (>= 2 do-greater-than-equal-o)
    ;; numbers (has changed)
    (zerop 1 zeropo) (numberp 1 numberpo)
    (natp 1 natpo) (integerp 1 integerpo) (posp 1 pospo)
    (negp 1 negpo) (rationalp 1 rationalpo)))

(defun do-rec-bool (form es)
  (let ((es (mapcar #'miniKanrenize-go es))
	(v (assoc form built-ins-bool)))
    (if v
	(if (or (not (cadr v)) (equal (length es) (cadr v)))
	    (complete-recursion-bool (cddr v) es)
	  (error "Wrong number of args given to ~a" form))
      (let ((name (get-rel-name form)))
	(complete-recursion-bool `(,name) es)))))

(defun miniKanrenize-bool (expr)
  (cond
   ;; base cases
   ((equal expr 't) '(succeed))
   ((equal expr 'nil) '(fail))
   ((numberp expr) '(succeed))
   ((symbolp expr) '(succeed))
   ;; standard ops with boolean versions
   ((and (consp expr)
	 (assoc (car expr) built-ins-bool))
    (do-rec-bool (car expr) (cdr expr)))
   ;; boolean connectors
   ((has-form 'and expr)
    `(conj . ,(mapcar #'miniKanrenize-bool (cdr expr))))
   ((has-form 'or expr)
    `(disj . ,(mapcar #'miniKanrenize-bool (cdr expr))))
   ((has-form 'not expr) (miniKanrenize (cadr expr) nil))
   ;; anything else just needs to return something non-nil
   (t (let ((x (next-var)))
	`(fresh (,x) (non-nilo ,x) ,(miniKanrenize expr x))))))
