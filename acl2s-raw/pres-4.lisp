(defttag t)
(include-book "lemma-synth" :uncertified-okp t)

(defunc2 foo (x)
  :input-contract (natp x)
  :output-contract (natp (foo x))
  (cond
   ((equal x 0) 13)
   (t (+ 2 (foo (- x 1))))))

(defgroup arith + - * expt number)

(suggest-lemma (foo x) :with arith)

(thm (IMPLIES (NATP X)
	      (EQUAL (FOO X)
		     (+ 13 (+ X X)))))

(defdata2 loi (listof integer))

(defunc2 sum-ls (l)
  :input-contract (loip l)
  :output-contract (integerp (sum-ls l))
  (cond
   ((endp l) 0)
   (t (+ (car l) (sum-ls (cdr l))))))

(defunc2 bad-sum (l)
  :input-contract (loip l)
  :output-contract (integerp (bad-sum l))
  (cond
   ((endp l) 11)
   (t (+ (car l) (bad-sum (cdr l))))))

(add-to-group arith sum-ls)

(suggest-lemma (bad-sum l)
	       :required-expressions sum-ls
	       :with arith)

(thm (IMPLIES (LOIP L)
	      (EQUAL (BAD-SUM L)
		     (+ (SUM-LS L) 11))))


(defunc2 strange (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (symbolp (strange ls acc))
  (cond
   ((atom ls) 'terminated)
   ((consp ls)
    (strange (cdr ls) (append (list (first ls)) (reverse acc))))))

(suggest-lemma (strange ls acc)
	       :with all-lines)

(thm
 (IMPLIES (AND (TRUE-LISTP LS) (TRUE-LISTP ACC))
         (EQUAL (STRANGE LS ACC) 'TERMINATED)))
