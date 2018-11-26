#|

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will NOT need to use ACL2s. However, you could
use the Eclipse/ACL2s text editor to write up your solution and
you may want to use ACL2s to help you check your answers.

PROVING ADMISSIBILITY

For each definition below, prove that it is admissible, i.e., it
satisfies all rules of the definitional principle. Recall:

Definitional Principle:

The definition

(defunc f (x1 ... xn)
  :input-contract ic
  :output-contract oc 
  body)

is *admissible* provided:

1. f is a new function symbol, i.e., there are no other axioms
about it; (note that this happens in the context of a history)

2. The xi are distinct variable symbols;

3. body is a term, possibly using f recursively as a function
symbol, mentioning no variables freely other than the xi; 

4. the function is terminating;

5. ic => oc is a theorem; 

6. the body contracts hold under the assumption that ic holds.

You can assume that Rule 1 is met: the symbol used in the defunc is a
new function symbol in each case.

You only have to prove the following two things (in this order).

1. The function terminates. To do this, construct a measure function
   and prove that it decreases. The proof may involve equational
   reasoning, but it may also require lemmas that you have to prove by
   induction.

2. The function contract. For this proof, you can use the definitional
   axiom of the function (but not the function contract!). These
   proofs typically require induction.

Recall that a measure function, m, for f, has to satisfy the following
conditions.

Condition 1. m has the same arguments and the same input contract as f.
Condition 2. m's output contract is (natp (m ...))
Condition 3. m is admissible.
Condition 4. On every recursive call of f, given the input contract and 
   the conditions that lead to that call, m applied to the arguments in
   the call is less than m applied to the original inputs.

You should do this proof as shown in class (which is also the way we will
expect you to prove termination on exams):

- Write down formalization of Condition 4.
- Use equational reasoning to conclude the formula is valid.
  If you need lemmas, identify and prove them.

Unless clearly stated otherwise, you need to follow these steps for EACH
recursive call separately.

Here is an example.

(defunc f (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (natp (f x y))
  (if (endp x)
    (if (equal y 0) 
      0
      (+ 1 (f x (- y 1))))
    (+ 1 (f (rest x) y))))

A measure is
(defunc m (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (natp (m x y))
  (+ (len x) y))

For the first recursive call in f, the formalization 
for proving Condition 4 is:

(implies (and (listp x)
              (natp y)
              (endp x)
              (not (equal y 0)))
         (< (m x (- y 1)) (m x y)))

This can be rewritten as:

(implies (and (listp x) (natp y) (endp x) (> y 0))
         (< (m x (- y 1)) (m x y)))
         
Proof of Condition 4 for the first recursive call:
Context
C1. (listp x)
C2. (natp y)
C3. (endp x)
C4. y != 0

(m x (- y 1))
= { Def m, C3, Def len, Arithmetic }
(- y 1)
< { Arithmetic }
y
= { Def m, C3, Def. len, Arithmetic }
(m x y)

The formalization for Proof of Condition 4 for the 
second recursive call:

(implies (and (listp x)
              (natp y)
              (not (endp x)))
         (< (m (rest x) y) (m x y)))

Proof:
C1. (listp x)
C2. (natp y)
C3. (not (endp x))

(m (rest x) y)
= { Def m, C3 }
(+ (len (rest x)) y)
< { Arithmetic, Decreasing len axiom }
(+ (len x) y)
= { Def m }
(m x y)

Hence f terminates, and m is a measure function for it.

For the second part, the function contract 
theorem is:

T1: (implies (and (listp x) (natp y)) (natp (f x y)))

Since f is recursive, we will need to prove this 
by induction and we will use the induction scheme f
gives rise to.

Our proof obligations are

1. (not (and (listp x) (natp y))) => T1
2. (and (listp x) (natp y) (endp x) (equal y 0)) => T1
3. (and (listp x) (natp y) (endp x) (not (equal y 0)) T1|((y (- y 1))))
   => T1
4. (and (listp x) (natp y) (not (endp x)) T1|((x (rest x))))
   => T1

You have to prove all four proof obligations using equational
reasoning (not shown), something that you should know how to do in
your sleep now.


1a)
|#
(defttag t)
(include-book "top" :uncertified-okp t)


(defunc2 fa (x)
  :input-contract (natp x)
  :output-contract (rationalp (fa x))
  (if (<= x 11)
      (+ x 17)
    (- 1 (fa (- x 1)))))
#|
;;;;;;;
Part 1 -- measure for fa
;;;;;;;

|#
(defunc2 ma (x)
  :input-contract (natp x)
  :output-contract (natp (ma x))
  x)

;A formalization for Condition 4 is:

(suggest-lemma t 
	       :required-expressions (ma (- x 1)) (ma x)
	       :with <
	       :hyps (natp x) (not (equal x 0)))

(thm (IMPLIES (AND (NATP X) (NOT (EQUAL X 0)))
         (EQUAL T (< (MA (- X 1)) (MA X)))))
#|
And the proof is:

C1: (natp x)
C2: (not (equal x 0))
------------
(< (ma (- x 1)) (ma x))
= {Def ma, C1, C2}
(< (- x 1) x)
= {Arith, C1}
t

So, fa terminates, and ma is a measure for it.

;;;;;;;
Part 2 -- Contract theorem:
;;;;;;;


T1: (implies (natp x) (rationalp (fa x)))
|#
(thm (implies (natp x) (rationalp (fa x))))

#|
Broken up into separate proof obligations:

1. (not (natp x)) => T1
2. (and (natp x) (<= x 11)) => T1
3. (and (natp x) (> x 11) (T! | ((x (- x 1))))) => T1
  
---proof of 1:

C1. (not (natp x)) => T1
-----------

(implies (natp x) (rationalp (fa x)))
= {C1, PL}
(implies nil (rationalp (fa x)))
= {PL}
t
---proof of 2: (base case when contract is satisfied)

C1. (natp x)
C2. (<= x 11)
------------
(implies (natp x) (rationalp (fa x)))
= {MP, C1}
(rationalp (fa x))
= {Def fa, C2}
(rationalp (/ x 17))
= {Arith, C1}
t

C1. (natp x)
C2. (> x 11)
C3. (inplies (natp (- x 1)) (rationalp (fa (- x 1))))
-------------
C4. (not (<= x 11)) {Arith, C2}
C5. (natp (- x 1)) {C1, C2}
C6. (rationalp (fa (- x 1))) {MP, C5, C3}

(implies (natp x) (rationalp (fa x)))
= {MP C1}
(rationalp (fa x))
= {Def fa, C1, C4}
(rationalp (- 1 (fa (- x 1))))
= {Arith}
(rationalp (fa (- x 1)))
= {C6}
t

1b)
|#
(defunc2 lte (a b)
  :input-contract (and (natp a) (natp b))
  :output-contract (booleanp (lte a b))
  (<= a b))

(defunc2 fb (a b)
  :input-contract  (and (natp a) (natp b))
  :output-contract (integerp (fb a b))
  (cond ((equal a 0) 1)
        ((equal b 0) -1)
        ((lte a b) (fb (- a 1) (- b 1)))
        (t (fb b a))))
#|
a measure for fb
|#
(defunc2 mb (a b)
  :input-contract (and (natp a) (natp b))
  :output-contract (natp (mb a b))
  (if (natp b) a a))

;A formalization for Condition 4 is:

;; base case
(thm (implies (natp b)
              (< (mb 0 b) (mb 1 b))))

; recursive call #1
(thm (implies (and (natp a)
                   (natp b)
                   (not (equal a 0))
                   (not (equal b 0))
                   (<= a b))
              (< (mb (- a 1) (- b 1))
                 (mb a b))))

(suggest-lemma t
	       :required-expressions (mb a b) (mb (- a 1) (- b 1))
	       :with < <= > >=
	       :hyps (natp a) (natp b)
	       (not (equal a 0)) (not (equal b 0)))

(thm (IMPLIES (AND (NATP A)
              (NATP B)
              (NOT (EQUAL A 0))
              (NOT (EQUAL B 0)))
         (EQUAL T (> (MB A B) (MB (- A 1) (- B 1))))))

#|
Proof of Condition 4 for recursive call #1

C1: (natp a)
C2: (natp b)
C3: (not (equal a 0))
C4: (not (equal b 0))
C5: (<= a b)
--------------------
C6: (natp (- a 1))
C7: (natp (- b 1))

(< (mb (- a 1) (- b 1))
   (mb a b))
= {Def mb, C6, C7}
(< (- a 1) a)
= {Arith, C1, C6}
t

|#
; recursive call #2

(suggest-lemma t
	       :required-expressions (mb a b) (mb b a)
	       :with < <= > >=
	       :hyps (natp a) (natp b)
	       (not (equal a 0)) (not (equal b 0)))

(thm (IMPLIES (AND (NATP A)
		   (NATP B)
		   (NOT (EQUAL A 0))
		   (NOT (EQUAL B 0)))
	      (EQUAL T (<= (MB A B) (MB A (MB B A))))))

#|
Proof of Condition 4 for recursive call #1

C1: (natp a)
C2: (natp b)
C3: (not (equal a 0))
C4: (not (equal b 0))
C5: (< b a)
-----------


(< (mb b a) (mb a b))
= {Def mb, C6, C7}
(< b a)
= {C5}
t



Thus, fb terminates and mb is a measure for it.

;;;;;;;
Part 2 -- Contract theorem:
;;;;;;;

T1: (implies (and (natp a) (natp b)) (integerp (fb a b)))
|#
(thm (implies (and (natp a) (natp b)) (integerp (fb a b))))
#|
I'm using the induction scheme of (fb a b)
(Which is valid since we just proved termination)

Broken up into separate proof obligations:

1. (or (not (natp a))
       (not (natp b)) => T1
2. (and (natp a) (natp b) (equal a 0)) => T1
3. (and (natp a) (natp b) (not (equal a 0)) (equal b 0)) => T1
4. (and (natp a) (natp b) (not (equal a 0)) (not (equal b 0)) (<= a b) 
    (T1 | ((a (- a 1)) (b (- b 1)))))
    => T1
5. (and (natp a) (natp b) (not (equal a 0)) (not (equal b 0)) (< b a)
    (T1 | ((a b) (b a)))) => T1


Proof of part 1.

C1: (or (not (natp a)) (not (natp b)))
--------------------

(implies (and (natp a) (natp b)) (integerp (fb a b)))
= {PL, C1}
(implies nil (integerp (fb a b)))
= {PL}
t

Proof of part 2. 

C1: (natp a)
C2: (natp b)
C3: (equal a 0)
--------------

(implies (and (natp a) (natp b)) (integerp (fb a b)))
= {MP, C1, C2}
(integerp (fb a b))
= {Def fb, C3}
(integerp 1)
= {Arith}
t

Proof of part 3.
C1: (natp a)
C2: (natp b)
C3: (not (equal a 0))
C4: (equal b 0)
--------------

(implies (and (natp a) (natp b)) (integerp (fb a b)))
= {MP, C1, C2}
(integerp (fb a b))
= {Def fb, C3, C4}
(integerp -1)
= {Arith}
t

Parts 2 and 3 serve as the base cases for an inductive proof,
so now I can use an inductive hypothesis in the final two proofs


4. (and (natp a) (natp b) (not (equal a 0)) (not (equal b 0)) (<= a b) 
    (T1 | ((a (- a 1)) (b (- b 1)))))
    => T1
    
Proof of part 4.
C1: (natp a)
C2: (natp b)
C3: (not (equal a 0))
C4: (not (equal b 0))
C5: (<= a b)
C6: (implies (and (natp (- a 1)) (natp (- b 1))) (integerp (fb (- a 1) (- b 1))))
--------------
C7: (natp (- a 1)) {Arith, C1, C3}
C8: (natp (- b 1)) {Arith, C2, C4}
C9: (integerp (fb (- a 1) (- b 1))) {MP, C6, C7, C8}

(implies (and (natp a) (natp b)) (integerp (fb a b)))
= {MP, C1, C2}
(integerp (fb a b))
= {Def fb, C3, C4, C5}
(integerp (fb (- a 1) (- b 1)))
= {C9}
t

Proof of part 5.
C1: (natp a)
C2: (natp b)
C3: (not (equal a 0))
C4: (not (equal b 0))
C5: (< b a)
C6: (implies (and (natp b) (natp a)) (integerp (fb b a)))
--------------
C8: (integerp (fb b a)) {MP, C6, C2, C1}

(implies (and (natp a) (natp b)) (integerp (fb a b)))
= {MP, C1, C2}
(integerp (fb a b))
= {Def fb, C3, C4, C5}
(integerp (fb b a))
= {C8}
t

1c)

(defunc fc (x y)
  :input-contract (and (posp x) (natp y))
  :output-contract (natp (fc x y))
  (cond ((equal y 0) y)
        ((equal x 1) x)
        ((<= y x) (fc (- x 1) y))
        (t (fc y x))))


...

1d)

; A data definition for positive rationals
(defdata prational (range rational (0 < _)))

(defunc fd (x y z)
  :input-contract (and (rationalp x) (rationalp y) (prationalp z))
  :output-contract (rationalp (fd x y z))
  (if (>= y 0)
      (* x y)
    (+ (/ x z) (fd (- x 1) (+ y z) z))))

...

1e)

(defunc fe (x y)
  :input-contract (and (natp x) (natp y))
  :output-contract (integerp (fe x y))
  (cond
   ((equal x 0) y)
   ((equal y 0) x)
   ((<= x y) (fe (- y 1) x))
   ((> x y) (fe y (- x 2)))
   (t (fe (- x 3) (- y 3)))))  

...

1f)

(defunc ff (x y)
  :input-contract (and (natp x) (natp y))
  :output-contract (booleanp (ff x y))
  (cond ((equal x y) t)
        ((> x y) (ff (- x 1) (+ y 1)))
        (t (ff (+ y 1) x))))

...

1g)
|#
(defdata2 lor (listof rational))

(defunc2 insert (a x)
  :input-contract (and (rationalp a) (lorp x))
  :output-contract (lorp (insert a x))
  (if (consp x)
      (if (<= a (car x))
          (cons a x)
        (cons (car x) (insert a (cdr x))))
    (cons a nil)))

; a measure for insert

(defunc2 m-insert (a x)
  :input-contract (and (rationalp a) (lorp x))
  :output-contract (natp (m-insert a x))
  (if a (len x) (len x)))

; theorem for recursive call:

(suggest-lemma t
	       :required-expressions (m-insert a x) (m-insert a (cdr x))
	       :with < >
	       :hyps (rationalp a) (lorp x) (consp x) (> a (car x)))

(thm (IMPLIES (AND (RATIONALP A)
              (LORP X)
              (CONSP X)
              (> A (CAR X)))
         (EQUAL T
                (> (M-INSERT A X)
                   (M-INSERT A (CDR X)))))) 

#|
Proof for recursive call:

C1: (rationalp a)
C2: (lorp x)
C3: (consp x)
C4: (> a (first x))
-------------------
C5: (lorp (rest x)) {Def lorp, C2, C3}


(> (m-insert a x) (m-insert a (rest x)))
= {Def m-insert, C1, C2}
(> (len x) (m-insert a (rest x)))
= {Def m-insert, C1, C5}
(> (len x) (len (rest x)))
= {Def len, C2}
(> (+ 1 (len (rest x)) (len (rest x)))
= {Arith}
t

Proof of Contract theorem:
T1: 
|#
(thm (implies (and (rationalp a) (lorp x)) (lorp (insert a x))))
#|
Proof obligations:

1. (implies (or (not (rationalp a)) (not (lorp x))) (lorp (insert a x)))
2. (implies (and (rationalp a) (lorp x) (endp x)) (lorp (insert a x)))
3. (implies (and (rationalp a) (lorp x) (consp x) (<= a (first x))) (lorp (insert a x)))
4. (implies (and (rationalp a) (lorp x) (consp x) (not (<= a (first x)))
                 (T1 | ((a a) (x (rest x)))))
            (lorp (insert a x)))
            
Proof of 1:
C1: (or (not (rationalp a)) (not (lorp x)))
-------

(implies (and (rationalp a) (lorp x)) (lorp (insert a x))))
= {C1}
(implies nil (lorp (insert a x)))
= {PL}
t

Proof of 2:
C1: (rationalp a)
C2: (lorp x)
C3: (endp x)
------------

(implies (and (rationalp a) (lorp x)) (lorp (insert a x))))
= {MP, C1, C2}
(lorp (insert a x))
= {Def insert C1, C3}
(lorp (list a))
= {Def lorp, C1}
t

Proof of 3:
C1: (rationalp a)
C2: (lorp x)
C3: (consp x)
C4: (<= a (first x))
----------------

(implies (and (rationalp a) (lorp x)) (lorp (insert a x))))
= {MP, C1, C2}
(lorp (insert a x))
= {Def insert, C1, C3}
(lorp (cons a x))
= {Def lorp, C1, C2}
t

Proof of 4:
C1: (rationalp a)
C2: (lorp x)
C3: (consp x)
C4: (not (<= a (first x)))
C5: (implies (and (rationalp a) (lorp (rest x))) (lorp (insert a (rest x))))
----------------
C6: (lorp (rest x)) {C2, C3}
C7: (rationalp (first x)) {Def lorp, C2, C3}
C8: (lorp (insert a (rest x))) {MP, C5, C1, C6}

(implies (and (rationalp a) (lorp x)) (lorp (insert a x))))
= {MP, C1, C2}
(lorp (insert a x))
= {Def insert, C1, C3, C4}
(lorp (cons (first x) (insert a (rest x))))
= {Def lorp, C7, C8}
t


1h)
|#
(defunc2 isort (x)
  :input-contract (lorp x)
  :output-contract (lorp (isort x))
  (if (endp x)
      ()
    (insert (car x) (isort (cdr x)))))

;; a measure for isort
(defunc2 m-isort (x)
  :input-contract (lorp x)
  :output-contract (natp (m-isort x))
  (len x))


(suggest-lemma t
	       :with < >
	       :required-expressions (m-isort (cdr x))
	       :hyps (lorp x) (consp x))

(thm (IMPLIES (AND (LORP X) (CONSP X))
         (EQUAL T (< (M-ISORT (CDR X)) (M-ISORT X)))))
#|
Proof for recursive call:

(implies (and (lorp x) (consp x)) (< (m-isort (rest x)) (m-isort x)))

C1: (lorp x)
C2: (consp x)
-------------
C3: (lorp (rest x)) {Def lorp, C1, C2}

(implies (and (lorp x) (consp x)) (< (m-isort (rest x)) (m-isort x)))
= {MP, C1, C2}
(< (m-isort (rest x)) (m-isort x))
= {Def m-isort, C1}
(< (len (rest x)) (m-isort x))
= {Def m-isort, C3}
(< (len (rest x)) (len x))
= {Def len, C2}
(< (len (rest x)) (+ 1 (len (rest x))))
= {Arith}
t


Contract theorem for isort
T1:
|#

(suggest-lemma t
	       :required-expressions (isort x)
	       :with lorp booleanp
	       :hyps (lorp x))

(thm (IMPLIES (LORP X)
         (EQUAL T (LORP (ISORT X)))))
#|
Proof obligations:
1. (implies (not (lorp x)) (lorp (isort x)))
2. (implies (and (lorp x) (endp x)) (lorp (isort x)))
3. (implies (and (lorp x) (consp x) (T1 | ((x (rest x))))) (lorp (isort x)))


Proof of 1:

C1: (not (lorp x))
------------------

(implies (lorp x) (lorp (isort x)))
= {C1}
(implies nil (lorp (isort x)))
= {PL}
t

Proof of 2:

C1: (lorp x)
C2: (endp x)
------------

(implies (lorp x) (lorp (isort x)))
= {MP, C1}
(lorp (isort x))
= {Def isort, C2}
(lorp ())
= {Def lorp}
t

Proof of 3:

C1: (lorp x)
C2: (consp x)
C3: (implies (lorp (rest x)) (lorp (isort (rest x))))
------------
C4: (lorp (rest x)) {Def lorp, C1, C2}
C5: (lorp (isort (rest x))) {MP, C3, C4}
C6: (rationalp (first x)) {Def lorp, C1, C2}

(implies (lorp x) (lorp (isort x)))
= {MP, C1}
(lorp (isort x))
= {Def isort, C2}
(lorp (cons (first x) (isort (rest x))))
= {Def lorp, C5, C6}
t


1i)

(defunc drop-last (x)
  :input-contract (listp x)
  :output-contract (listp (drop-last x))
  (cond ((endp x) nil)
        ((endp (rest x)) nil)
        (t (cons (first x) (drop-last (rest x))))))

...

1j)

(defunc prefixes (l)
  :input-contract (listp l)
  :output-contract (listp (prefixes l))
  (cond ((endp l) '( () ))
        (t (cons l (prefixes (drop-last l))))))

HINT: To prove termination, you will need a lemma, which you can prove
by induction. The same holds for some of the following problems.

...

1k)

(defunc less (x lst)
  :input-contract (and (rationalp x) (lorp lst))
  :output-contract (lorp (less x lst))
  (cond ((endp lst) ())
        ((< (first lst) x)
         (cons (first lst) (less x (rest lst))))
        (t (less x (rest lst)))))

...

1l)

(defunc notless (x lst)
  :input-contract (and (rationalp x) (lorp lst))
  :output-contract (lorp (notless x lst))
  (cond ((endp lst) nil)
        ((>= (first lst) x)
         (cons (first lst) (notless x (rest lst))))
        (t (notless x (rest lst)))))

...

1m)

(defunc qsort (x)
  :input-contract (lorp x)
  :output-contract (lorp (qsort x))
  (if (endp x) 
      ()
    (append (qsort (less (first x) (rest x)))
            (append (list (first x))
                    (qsort (notless (first x) (rest x)))))))

...

|#

#|

Prove the following conjectures using induction. You may need
lemmas. You can freely use the definitional and function contract
theorems of the functions (all of which appear above or we have seen
in class).

2a)

(implies (lorp x)
         (equal (len (isort x))
                (len x)))

Proof obligations:
1. (implies (and (lorp x) (endp x)) (equal (len (isort x)) (len x)))
2. (implies (and (lorp x) 
                 (consp x) 
                 (implies (lorp (rest x)) (equal (len (isort (rest x))) (len (rest x))))) 
            (equal (len (isort x)) (len x)))

Proof of 1:

C1: (lorp x)
C2: (endp x)
-------------

(equal (len (isort x)) (len x))
= {Def len, C2}
(equal (len (isort x)) 0)
= {Def isort, C2}
(equal 0 0)
= {equal axiom}
t


Lemma 1: (used below)
|#
(thm (implies (and (rationalp y) (lorp x))
              (equal (len (insert y x)) (+ 1 (len x)))))
#|
Proof obligations:

1. (implies (and (rationalp y) (endp x)) (equal (len (insert y x)) (+ 1 (len x))))
2. (implies (and (rationalp y) (lorp x) (consp x) (<= y (first x)))
            (equal (len (insert y x)) (+ 1 (len x))))
3. (implies (and (rationalp y) (lorp x) (consp x) (not (<= y (first x)))
                 (implies (and (rationalp y) (lorp (rest x))) 
                          (equal (len (insert y (rest x))) (+ 1 (len (rest x)))))) 
            (equal (len (insert y x)) (+ 1 (len x))))            

Proof of 1:

C1: (rationalp y)
C2: (endp x)
------------

(equal (len (insert y x)) (+ 1 (len x)))
= {Def insert, C1, C2}
(equal (len (list y)) (+ 1 (len x)))
= {Def len, C2}
(equal (len (list y)) (+ 1 0))
= {Def len}
(equal 1 1)
= {equal axiom}
t

Proof of 2:
C1: (rationalp y) 
C2: (lorp x) 
C3: (consp x) 
C4: (<= y (first x))
----------------

(equal (len (insert y x)) (+ 1 (len x)))
= {Def insert, C3, C4}
(equal (len (cons y x)) (+ 1 (len x)))
= {Def len}
(equal (+ 1 (len x)) (+ 1 (len x)))
= {equal axiom}
t

Proof of 3:

C1: (rationalp y)
C2: (lorp x)
C3: (consp x)
C4: (not (<= y (first x)))
C5: (implies (and (rationalp y) (lorp (rest x))) 
             (equal (len (insert y (rest x))) (+ 1 (len (rest x)))))
------------
C6: (lorp (rest x)) {Def lorp, C2, C3}
C7: (equal (len (insert y (rest x))) (+ 1 (len (rest x)))) {MP, C5, C1, C6}

(equal (len (insert y x)) (+ 1 (len x)))
= {Def insert, C1, C3, C4}
(equal (len (cons (first x) (insert y (rest x)))) (+ 1 (len x)))
= {Def len}
(equal (+ 1 (len (insert y (rest x)))) (+ 1 (len x)))
= {C7}
(equal (+ 1 (+ 1 (len (rest x)))) (+ 1 (len x)))
= {C3}
(equal (+ 1 (+ 1 (len (rest x)))) (+ 1 (+ 1 (len (rest x)))))
= {equal axiom}
t



-------------------------------------

Proof of 2:

C1: (lorp x)
C2: (consp x)
C3: (implies (lorp (rest x)) (equal (len (isort (rest x))) (len (rest x))))
---------------
C4: (lorp (rest x)) {Def lorp, C1, C2}
C5: (equal (len (isort (rest x))) (len (rest x))) {MP, C3, C4}
C6: (rationalp (first x)) {Def lorp, C1, C2}
C7: (lorp (isort (rest x))) {Contract thm, isort, C4}

(equal (len (isort x)) (len x))
= {Def isort, C1, C2}
(equal (len (insert (first x) (isort (rest x)))) (len x))
= {Def len, C2}
(equal (len (insert (first x) (isort (rest x)))) (+ 1 (len (rest x))))
= {Lemma 1, C6, C7}
(equal (+ 1 (len (isort (rest x)))) (+ 1 (len (rest x))))
= {C5}
(equal (+ 1 (len (rest x))) (+ 1 (len (rest x))))
= {equal axiom}
t


2b)

(implies (listp x)
         (equal (len (prefixes x))
                (+ 1 (len x))))

2c) EXTRA CREDIT

(implies (lorp x)
         (equal (len (qsort x))
                (len x)))
|#


#|

Consider the following definition.  No one has been able to prove that
the function terminates and no one has been able to show that it
doesn't!

|#

:program

(defunc c (n)
  :input-contract (natp n)
  :output-contract (natp (c n))
  (cond ((< n 2) n)
        ((integerp  (/ n 2)) (c (/ n 2)))
        (t (c (+ 1 (* 3 n))))))


#|

Define a function c-trace that given a nat, n, returns a list that
includes, in order, all of the numbers that c is called on when given
n as input.  See the check='s below.

|#
(defdata lon (listof nat))
; 3a
(defunc c-trace (n)
  :input-contract (natp n)
  :output-contract (lonp (c-trace n))
  (cond ((< n 2) (list n))
        ((integerp  (/ n 2)) (cons n (c-trace (/ n 2))))
        (t (cons n (c-trace (+ 1 (* 3 n)))))))

(check= (c-trace 8) '(8 4 2 1))
(check= (c-trace 7) 
        '(7 22 11 34 17 52 26 13 40 20 10 5 16 8 4 2 1))


#|

Find a number max between 1 and 1,000,000 such that (len (c-trace
max)) is greater than or equal to (len (c-trace i)) for any i between
1 and 1,000,000.

max is ...
(len (c-trace max)) is ...

|#

(defun c-trace-count (n res)
  ;:input-contract (and (natp n) (natp res))
  ;:output-contract (natp (c-trace-count n res))
  (cond ((< n 2) (+ 1 res))
        ((integerp  (/ n 2)) (c-trace-count (/ n 2) (+ 1 res)))
        (t (c-trace-count (+ 1 (* 3 n)) (+ 1 res)))))

(defdata res (list nat nat))


(defun max-len (i res)
  ;:input-contract (and (natp i) (natp max) (<= i max) (resp res))
  ;:output-contract (resp (max-len i res max))
  (cond ((equal i 1000000) res)
        (t (let ((curr (c-trace-count i 0)))
             (if (> curr (second res))
               (max-len (+ i 1) (list i curr))
               (max-len (+ i 1) res))))))





(defconst *max* (max-len 1 (list 0 0)))#|ACL2s-ToDo-Line|#


; 3b
(check= (len (c-trace 837799)) 525)
(check= (c-trace 837799) 
        (list 837799 2513398 1256699
      3770098 1885049 5655148 2827574 1413787
      4241362 2120681 6362044 3181022 1590511
      4771534 2385767 7157302 3578651 10735954
      5367977 16103932 8051966 4025983
      12077950 6038975 18116926 9058463
      27175390 13587695 40763086 20381543
      61144630 30572315 91716946 45858473
      137575420 68787710 34393855 103181566
      51590783 154772350 77386175 232158526
      116079263 348237790 174118895 522356686
      261178343 783535030 391767515 1175302546
      587651273 1762953820 881476910 440738455
      1322215366 661107683 1983323050
      991661525 2974984576 1487492288
      743746144 371873072 185936536 92968268
      46484134 23242067 69726202 34863101
      104589304 52294652 26147326 13073663
      39220990 19610495 58831486 29415743
      88247230 44123615 132370846 66185423
      198556270 99278135 297834406 148917203
      446751610 223375805 670127416 335063708
      167531854 83765927 251297782 125648891
      376946674 188473337 565420012 282710006
      141355003 424065010 212032505 636097516
      318048758 159024379 477073138 238536569
      715609708 357804854 178902427 536707282
      268353641 805060924 402530462 201265231
      603795694 301897847 905693542 452846771
      1358540314 679270157 2037810472
      1018905236 509452618 254726309
      764178928 382089464 191044732 95522366
      47761183 143283550 71641775 214925326
      107462663 322387990 161193995 483581986
      241790993 725372980 362686490 181343245
      544029736 272014868 136007434 68003717
      204011152 102005576 51002788 25501394
      12750697 38252092 19126046 9563023
      28689070 14344535 43033606 21516803
      64550410 32275205 96825616 48412808
      24206404 12103202 6051601 18154804
      9077402 4538701 13616104 6808052 3404026
      1702013 5106040 2553020 1276510 638255
      1914766 957383 2872150 1436075 4308226
      2154113 6462340 3231170 1615585 4846756
      2423378 1211689 3635068 1817534 908767
      2726302 1363151 4089454 2044727 6134182
      3067091 9201274 4600637 13801912 6900956
      3450478 1725239 5175718 2587859 7763578
      3881789 11645368 5822684 2911342 1455671
      4367014 2183507 6550522 3275261 9825784
      4912892 2456446 1228223 3684670 1842335
      5527006 2763503 8290510 4145255 12435766
      6217883 18653650 9326825 27980476
      13990238 6995119 20985358 10492679
      31478038 15739019 47217058 23608529
      70825588 35412794 17706397 53119192
      26559596 13279798 6639899 19919698
      9959849 29879548 14939774 7469887
      22409662 11204831 33614494 16807247
      50421742 25210871 75632614 37816307
      113448922 56724461 170173384 85086692
      42543346 21271673 63815020 31907510
      15953755 47861266 23930633 71791900
      35895950 17947975 53843926 26921963
      80765890 40382945 121148836 60574418
      30287209 90861628 45430814 22715407
      68146222 34073111 102219334 51109667
      153329002 76664501 229993504 114996752
      57498376 28749188 14374594 7187297
      21561892 10780946 5390473 16171420
      8085710 4042855 12128566 6064283
      18192850 9096425 27289276 13644638
      6822319 20466958 10233479 30700438
      15350219 46050658 23025329 69075988
      34537994 17268997 51806992 25903496
      12951748 6475874 3237937 9713812
      4856906 2428453 7285360 3642680 1821340
      910670 455335 1366006 683003 2049010
      1024505 3073516 1536758 768379 2305138
      1152569 3457708 1728854 864427 2593282
      1296641 3889924 1944962 972481 2917444
      1458722 729361 2188084 1094042 547021
      1641064 820532 410266 205133 615400
      307700 153850 76925 230776 115388 57694
      28847 86542 43271 129814 64907 194722
      97361 292084 146042 73021 219064 109532
      54766 27383 82150 41075 123226 61613
      184840 92420 46210 23105 69316 34658
      17329 51988 25994 12997 38992 19496
      9748 4874 2437 7312 3656 1828 914 457
      1372 686 343 1030 515 1546 773 2320 1160
      580 290 145 436 218 109 328 164 82 41
      124 62 31 94 47 142 71 214 107 322 161
      484 242 121 364 182 91 274 137 412 206
      103 310 155 466 233 700 350 175 526 263
      790 395 1186 593 1780 890 445 1336 668
      334 167 502 251 754 377 1132 566 283 850
      425 1276 638 319 958 479 1438 719 2158
      1079 3238 1619 4858 2429 7288 3644 1822
      911 2734 1367 4102 2051 6154 3077 9232
      4616 2308 1154 577 1732 866 433 1300 650
      325 976 488 244 122 61 184 92 46 23 70
      35 106 53 160 80 40 20 10 5 16 8 4 2 1))

