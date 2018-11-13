#|
(add-include-book-dir :acl2s-modes "~/acl2/books/acl2s/")
(ld "acl2s-mode.lsp" :dir :acl2s-modes)
(acl2s-defaults :set verbosity-level 1)
(reset-prehistory t)
(in-package "ACL2S")
|#


(defttag t)

(include-book "top" :uncertified-okp t)

;;; really basic tests

(suggest-lemma x :hyps (natp x))

(defunc2 not-test (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (booleanp (not-test a b))
  (not (< a b)))

(suggest-lemma (not-test a b)
	       :required-expressions not
	       :with <)

(defunc2 if-test (a)
  :input-contract (booleanp a)
  :output-contract (integerp (if-test a))
  (if a 0 1))

(suggest-lemma a
	       :required-expressions (zerop (if-test a))
	       :hyps (booleanp a))

(suggest-lemma a
	       :required-expressions if-test
	       :with zerop
	       :hyps (booleanp a))

(defunc2 if-test2 (a)
  :input-contract (booleanp a)
  :output-contract (booleanp (if-test2 a))
  (if a nil t))

(suggest-lemma a
	       :required-expressions not if-test2
	       :with not
	       :hyps (booleanp a))

(suggest-lemma (if-test2 a)
	       :required-expressions if-test2)

;; testing
(defunc2 bar5 (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (booleanp (bar5 a b))
  (if (<= a b) nil t))

(suggest-lemma (bar5 a b)
	       :required-expressions <= not)

(suggest-lemma (bar5 a b)
	       :required-expressions bar5)

(suggest-lemma (<= a b)
	       :required-expressions bar5
	       :with not
	       :hyps (integerp a) (integerp b))

(defunc2 eta-cons (a b)
  :input-contract (true-listp b)
  :output-contract (true-listp (eta-cons a b))
  (cons a b))

(suggest-lemma (cons a b)
	       :with eta-cons
	       :hyps (true-listp b))

(suggest-lemma (eta-cons a b)
	       :with cons)

(defunc2 reverse-acc (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (true-listp (reverse-acc ls acc))
  (cond
   ((endp ls) acc)
   (t (reverse-acc (cdr ls) (cons (car ls) acc)))))


(suggest-lemma (reverse-acc ls acc)
	       :with append reverse)

(suggest-lemma (reverse ls)
	       :with reverse-acc boolean
	       :hyps (true-listp ls))

(defgroup list-ops append reverse)

(suggest-lemma (reverse-acc ls acc)
	       :with list-ops)

;;using the examples from the exam

(defunc2 in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(suggest-lemma (in x ls)
	       :required-expressions (append ls l2)
	       :with boolean in
	       :hyps (true-listp l2) (not (in x l2)))

(suggest-lemma t
	       :required-expressions (in x (cons x ls))
	       :hyps (and (natp x) (true-listp ls)))

(defunc2 nodups (ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (nodups ls))
  (cond
   ((endp ls) t)
   ((in (car ls) (cdr ls)) nil)
   (t (nodups (cdr ls)))))

(defunc2 remdups (ls)
  :input-contract (true-listp ls)
  :output-contract (true-listp ls)
  (cond
   ((endp ls) nil)
   ((in (car ls) (cdr ls))
    (remdups (cdr ls)))
   (t (cons (car ls) (remdups (cdr ls))))))

(suggest-lemma t
	       :required-expressions nodups remdups append
	       :hyps (true-listp l1) (true-listp l2))


(defunc2 remdupst (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (true-listp (remdupst ls acc))
  (cond
   ((endp ls) acc)
   ((in (car ls) acc)
    (remdupst (cdr ls) acc))
   (t (remdupst (cdr ls) (cons (car ls) acc)))))

(suggest-lemma (in x (remdups l1))
	       :required-expressions (remdupst l1 nil) in
	       :with boolean
	       :hyps (true-listp l1))

(add-to-group list-ops remdups)

(suggest-lemma (remdupst ls acc)
	       :required-expressions remdups append reverse
	       :hyps (nodups acc))

(suggest-lemma (in x (remdups ls))
	       :required-expressions in x (remdupst ls nil)
	       :with list-ops boolean )

(defunc2 remdups-fast (ls)
  :input-contract (true-listp ls)
  :output-contract (true-listp (remdups-fast ls))
  (remdupst ls nil))

(suggest-lemma (in x ls)
	       :required-expressions remdups-fast ls
	       :with in)

;; to walk through the world, look up finding all function definitions
;; in the world
;; use trans-eval

;; get rid of simplification of hyps

;; add list predicates

;; sorting

(defdata loi (listof integer))

(defunc2 orderedp (ls)
  :input-contract (loip ls)
  :output-contract (booleanp (orderedp ls))
  (cond
   ((endp ls) t)
   ((endp (cdr ls)) t)
   ((< (car ls) (car (cdr ls)))
    (orderedp (cdr ls)))
   (t nil)))

(defunc2 insert (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (insert x ls))
  (cond
   ((equal ls nil) (cons x nil))
   ((<= x (car ls)) (cons x ls))
   (t (cons (car ls) (insert x (cdr ls))))))

(defunc2 isort (ls)
  :input-contract (loip ls)
  :output-contract (loip (isort ls))
  (cond
   ((endp ls) nil)
   (t (insert (car ls)
	      (isort (cdr ls))))))

(suggest-lemma (isort ls)
	       :hyps (orderedp ls))

(suggest-lemma ls
	       :required-expressions (isort ls)
	       :hyps (orderedp ls) (loip ls))


(defunc2 my-lte (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (booleanp (my-lte a b))
  (<= a b))

(suggest-lemma (>= a b) :required-expressions my-lte)

(defunc2 less (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (less x ls))
  (cond
   ((endp ls) nil)
   ((not (my-lte x (car ls)))
    (cons (car ls) (less x (cdr ls))))	  
   (t (less x (cdr ls)))))

(suggest-lemma (less x ls) :with less)


;; first key quicksort-isort lemma
(suggest-lemma (isort (less x ls))
	       :required-expressions less (isort ls)
	       :with all-lines
	       )

(defunc2 notless (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (notless x ls))
  (cond
   ((endp ls) nil)
   ((my-lte x (car ls))
    (cons (car ls) (notless x (cdr ls))))	  
   (t (notless x (cdr ls)))))


(IMPLIES (AND (LOIP (CDR LS))
              (INTEGERP (CAR LS)))
         (EQUAL (APPEND (LESS (CAR LS) (ISORT (CDR LS)))
                        (CONS (CAR LS)
                              (NOTLESS (CAR LS) (ISORT (CDR LS)))))
                (INSERT (CAR LS) (ISORT (CDR LS)))))

(test? (IMPLIES (AND (ORDEREDP LS) (INTEGERP A))
	      (EQUAL (APPEND (LESS A LS)
			     (CONS A (NOTLESS A LS)))
		     (INSERT A LS))))


(thm (implies (orderedp ls) (loip ls)))


;; second key quicksort-isort lemma
(suggest-lemma (isort (notless x ls))
	       :required-expressions (isort ls)
	       :with notless)


;; final key qsort lemma
(suggest-lemma (append (less a ls) (cons a (notless a ls)))
	       :required-expressions insert
	       :hyps (orderedp ls))

;; same lemma, written in a more naive way
(suggest-lemma (append (less (car ls)
			     (isort (cdr ls)))
		       (cons (car ls)
			     (notless (car ls)
				      (isort (cdr ls)))))
	       :required-expressions (isort (cdr ls))
	       :with car cdr insert
	       :hyps (consp ls))

(defunc2 qsort (ls)
  :input-contract (loip ls)
  :output-contract (loip (qsort ls))
  (cond
   ((endp ls) nil)
   (t (let ((pivot (car ls)))
	(append (qsort (less pivot (cdr ls)))
		(cons pivot (qsort (notless pivot (cdr ls)))))))))

(suggest-lemma (qsort ls)
	       :required-expressions qsort)

(suggest-lemma (qsort ls)
	       :required-expressions isort)

;;; testing eta-expansions of all the primitives

;; number stuff
(defunc2 my-+ (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (integerp (my-+ a b))
  (+ a b))

(suggest-lemma (my-+ a b)
	       :required-expressions +)

(defunc2 my-- (a b)
     :input-contract (and (integerp a) (integerp b))
     :output-contract (integerp (my-- a b))
     (- a b))

(suggest-lemma (my-- a b)
	       :required-expressions -
	       :hyps (natp a) (natp b))

(defunc2 my-* (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (integerp (my-* a b))
  (* a b))

(suggest-lemma (my-* a b) :required-expressions *)

(defunc2 my-gt (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (booleanp (my-gt a b))
  (> a b))

(suggest-lemma (my-gt a b) :required-expressions >)

(defunc2 my-lt (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (booleanp (my-lt a b))
  (< a b))

(suggest-lemma (my-lt a b) :required-expressions <)

(suggest-lemma (my-lte a b) :required-expressions <=
	       :hyps (integerp a) (integerp b))

(defunc my-gte (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (booleanp (my-gte a b))
  (>= a b))

(defunc my-gte2 (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (booleanp (my-gte2 a b))
  (>= a b))

(suggest-lemma (my-gte2 a b) :required-expressions >=)

(suggest-lemma (my-gte2 a b)
	       :required-expressions my-lt
	       :with not)
