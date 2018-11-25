#|
EQUATIONAL REASONING INSTRUCTIONS

The questions on equational reasoning ask for equational proofs about
ACL2s programs. You are given a set of function definitions you can
use.  Note in many cases the name has been slightly changed so you
can't simply use a theorem from class (ex. in2 instead of in).

The definitional axioms and contract theorems for defined functions
can be used in your proofs, unless we specifically prohibit you from
doing so.

You can use ACL2s to check the conjectures you come up with, but you are 
not required to do so. 

Here are some notes about equational proofs although additional
information can be found in the course notes on equational
reasoning. Remember the key consideration when grading your proofs
will be how well you communicate your ideas and justifications.

1. The context. Remember to use propositional logic to rewrite the
context so that it has as many hypotheses as possible.  See the
lecture notes for details. Label the facts in your context with C1,
C2, ... as in the lecture notes.

2. The derived context. Draw a dashed line (----) after the context
and add anything interesting that can be derived from the context.
Use the same labeling scheme as was used in the context. Each derived
fact needs a justification. Again, look at the lecture notes for more
information.

3. Use the proof format shown in class and in the lecture notes, which
requires that you justify each step.

4. When using an axiom, theorem or lemma, show the name of the axiom,
theorem or lemma. Starting with this homework, you do not have to
specify the substitution used.  You can use any "shortcut" we've used
in lab or in the lectures. For example, you do not need to cite the if
axioms when using a definitional axiom.  Look at the lecture notes for
examples.

5. When using the definitional axiom of a function, the justification
should say "Def. <function-name>".  When using the contract theorem of
a function, the justification should say
"Contract <function-name>".

6. Arithmetic facts such as commutativity of addition can be used. The
name for such facts is "Arithmetic" or "Arith".

7. You can refer to the axioms for cons, and consp as the "cons
axioms", Axioms for first and rest can be referred to as "first-rest
axioms".  The axioms for if are named "if axioms"

8. Any propositional reasoning used can be justified by "propositional
reasoning", "Prop logic", or "PL" except you should use "MP" to
explicitly identify when you use modus ponens.

9. For this homework, you can only use theorems we explicitly tell you
you can use or we have covered in class/lab.  You can, of course, use
the definitional axiom and contract theorem for any function used or
defined in this homework. You may also use theorems you've proven
earlier in the homework. 

10. For any given propositional expression, feel free to re-write it
in infix notation. 

For example, you can write A => (B ^ C) instead of (implies A (and B C))) 

The same hold for arithmetic expressions.

For example, you can write xy/2 instead of (/ (* x y) 2)

Leave the following for technical reasons. This is for those of you
that want to use ACL2s.

|#

#|

REASONING ABOUT TAIL-RECURSIVE FUNCTIONS

You can freely use the definitional and function contract theorems of
the functions we provide below or that we have covered in class. You
can also freely use any theorems we proved in class and in the lecture
notes.

Make sure you identify what induction scheme you are using.  For
example, suppose you were proving that app is associative:

(listp x) ^ (listp y) ^ (listp z) =>
(app (app x y) z) = (app x (app y z))

At the beggining of the proof you should say:

Proof by induction using (listp x).

You will be asked to define tail recursive versions of given
functions, using accumulators. This involves two function
definitions. 

For example, to define a tail recursive version of rev, we first
define rev-tl. rev-tl is recursive and has an extra argument, the
accumulator. Second, we define rev*, a non-recursive function that
calls rev-tl with the accumulater appropriately initialized and which
satisfies the theorem that rev* = rev, ie, :

(listp x) => (rev* x) = (rev x)

|#

(defttag t)
(include-book "top" :uncertified-okp t)

;; Tail-recursive version of rev (auxiliary function)
(defunc2 rev-tl (x acc)
  :input-contract (and (true-listp x) (true-listp acc))
  :output-contract (true-listp (rev-tl x acc))
  (if (endp x)
      acc
    (rev-tl (cdr x) (cons (car x) acc))))

;; Non-recursive version of rev that uses rev-tl
(defunc2 rev* (x)
  :input-contract (true-listp x) 
  :output-contract (true-listp (rev* x))
  (rev-tl x nil))

#|

You will also be asked to prove that the tail recursive version of a
function is equal to the original function.  For our
example, the theorem is

(implies (listp x)
         (equal (rev* x)
                (rev x)))

To do that you have to come up with lemmas; in particular you have to
come up with the right generalizations. If you choose to use ACL2s for
the proofs, here is how you would do that. Remember that you have to
make sure there are no nested inductions.

|#

(suggest-lemma (rev-tl x acc)
	       :required-expressions (reverse x)
	       :with append cons reverse)

(defthm rev-tl-help
  (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP ACC))
         (EQUAL (REV-TL X ACC)
                (APPEND (REVERSE X) ACC))))

(suggest-lemma (rev* l)
	       :with reverse)

; With the lemma above, the main theorem follows
(defthm rev*-rev
  (IMPLIES (TRUE-LISTP L)
         (EQUAL (REV* L) (REVERSE L))))

; The proofs were given in class.
#|

Q1. In this example, we will see how to speed up numeric functions.

Consider the following function. Notice it takes a long time to admit
because it takes a long time to run (so testing takes a long time).

|#

(defunc2 lt (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (booleanp (lt a b))
  (< a b))

(defunc2 f1 (n)
  :input-contract (natp n)
  :output-contract (natp (f1 n))
  (if (lt n 2)
      (+ n 4)
    (+ (f1 (- n 1))
       (f1 (- n 2)))))

#|
Q1a

Think about why f1 takes long. Consider

(f1 4) = (f1 3) + (f1 2)
       = (f1 2) + (f1 1) + (f1 1) + (f1 0)
       = (f1 1) + (f1 0) + (f1 1) + (f1 1) + (f1 0)

Notice that (f1 2) was computed multiple times, as was (f1 1) and 
(f1 0). This leads to an exponential number of calls to f1.

We can do better.

Define f1-t, a function that takes multiple arguments and can be used
to compute f1 quickly. f1-t should only lead to a linear (in n) number
of recursive calls.

Note that you can have as many arguments to f1-t as you like.

|#
#|
(defunc f1-t (p1 p2 i n)
  :input-contract (and (natp p1) (natp p2) (natp i) (natp n))
  :output-contract (natp (f1-t p1 p2 i n))
  (cond ((< n 2) (+ n 4))
        ((<= i n) (f1-t p2 (+ p1 p2) (+ i 1) n))
        (t (+ p1 p2))))
|#

(defunc2 f1-t (r1 r2 i n)
  :input-contract (and (natp r1) (natp r2) (natp i) (natp n)
		       (<= i n) (>= i 2) (>= n 2))
  :output-contract (natp (f1-t r1 r2 i n))
  (cond ((equal n i) r2)
        (t (f1-t r2 (+ r1 r2) (+ i 1) n))))
#|

Q1b

Define f1*, a non-recursive function that has the same signature as f1
and uses f1-t to efficiently compute f1. f1* should be equal to f1.

|#

(defunc2 f1* (n)
  :input-contract (natp n)
  :output-contract (natp (f1* n))
  (if (lt n 2)
    (+ n 4)
    (f1-t 5 9 2 n)))

(check= (f1 3) (f1-t 5 9 2 3))
(check= (f1 10) (f1-t 5 9 2 10))
(check= (f1 2) (f1-t 5 9 2 2))
(check= (f1 34) (f1-t 5 9 2 34))

(check= (f1 3) (f1* 3))
(check= (f1 10) (f1* 10))
(check= (f1 0) (f1* 0))
(check= (f1 1) (f1* 1))
(check= (f1 2) (f1* 2))
(check= (f1 27) (f1* 27))

;; This doesn't work, since f1 takes so long that itest? can't come up with
;; test cases

(suggest-lemma (f1 n)
	       :with f1-t
	       :hyps (natp n) (natp r1) (natp r2) (natp i)
	       (<= i n) (>= i 2) (>= n 2)
	       (equal r1 (f1 (- i 1)))
	       (equal r2 (f1 i))
	       ;; added for speed
	       (<= n 10)
	       )

(thm (IMPLIES (AND (NATP R1)
              (NATP R2)
              (NATP I)
              (NATP N)
              (NOT (< N I))
              (NOT (< I '2))
              (NOT (< N '2))
              (NATP N)
              (NATP R1)
              (NATP R2)
              (NATP I)
              (<= I N)
              (>= I 2)
              (>= N 2)
              (EQUAL R1 (F1 (- I 1)))
              (EQUAL R2 (F1 I)))
         (EQUAL (F1-T R1 R2 I N) ACL2::|_0|)))


#|
Q1c

(implies 
         (equal (f1-t r1 r2 i n) (f1 n)))

This will be proven using the induction scheme of (f1-t r1 r2 i n)

1. (implies (not (and (natp n) (natp r1) (natp r2) (natp i) (<= i n) (>= i 2) (>= n 2)
                      (equal r1 (f1 (- i 1)))
                      (equal r2 (f1 i)))) Q1c)
Reductio ad absurdum. Done.

2. (implies (and (natp n) (natp r1) (natp r2) (natp i) (<= i n) (>= i 2) (>= n 2)
                 (equal r1 (f1 (- i 1)))
                 (equal r2 (f1 i))
                 (equal i n)) Q1c)

C1. (natp n)
C2. (natp r1)
C3. (natp r2)
C4. (natp i)
C5. (<= i n)
C6. (>= i 2)
C7. (>= n 2)
C8. (equal r1 (f1 (- i 1)))
C9. (equal r2 (f1 i))
C10. (equal i n)
-------------------
C11. (equal r2 (f1 n)) {equal axiom, C9, C10}

(implies (and (natp n) (natp r1) (natp r2) (natp i) (<= i n) (>= i 2) (>= n 2)
              (equal r1 (f1 (- i 1)))
              (equal r2 (f1 i)))
         (equal (f1-t r1 r2 i n) (f1 n)))
={MP, C1 - C9}
(equal (f1-t r1 r2 i n) (f1 n))
={Def f1-t, C10}
(equal r2 (f1 n))
={C11}
t

3. (implies (and (natp n) (natp r1) (natp r2) (natp i) (<= i n) (>= i 2) (>= n 2)
                 (equal r1 (f1 (- i 1)))
                 (equal r2 (f1 i))
                 (not (equal i n))
                 (Q1c | ((r1 r2) (r2 (+ r1 r2)) (i (+ i 1))))) Q1c)
C1. (natp n)
C2. (natp r1)
C3. (natp r2)
C4. (natp i)
C5. (<= i n)
C6. (>= i 2)
C7. (>= n 2)
C8. (equal r1 (f1 (- i 1)))
C9. (equal r2 (f1 i))
C10. (not (equal i n))
C11. (implies (and (natp n) (natp r2) (natp (+ r1 r2)) (natp (+ i 1)) 
                   (>= (+ i 1) 2) (<= (+ i 1) n) (>= n 2)
                   (equal r2 (f1 (- (+ i 1) 1)))
                   (equal (+ r1 r2) (f1 (+ i 1))))
              (equal (f1-t r2 (+ r1 r2) (+ i 1) n) (f1 n)))     
-------------------
C12. (natp (+ r1 r2)) {Arith, C2, C3}
C13. (natp (+ i 1)) {Arith, C4}
C14. (>= (+ i 1) 2) {Arith, C6}
C15. (< i n) {Arith, C5, C10}
C16. (<= (+ i 1) n) {Arith, C15}
C17. (equal r2 (f1 (- (+ i 1) 1))) {Arith, C9}
C18. (equal (+ r1 r2) (+ (f1 (- i 1)) (f1 i))) {C8, C9}
C19. (equal (+ r1 r2) (f1 (+ i 1))) {C18, Def f1}
C20. (equal (f1-t r2 (+ r1 r2) (+ i 1) n) (f1 n))
     {MP, C11, C1, C3, C12, C13, C14, C16, C7, C17, C19}

(implies (and (natp n) (natp r1) (natp r2) 
              (natp i) (<= i n) (>= i 2) (>= n 2)
              (equal r1 (f1 (- i 1)))
              (equal r2 (f1 i)))
         (equal (f1-t r1 r2 i n) (f1 n)))
={MP, C1 - C9}
(equal (f1-t r1 r2 i n) (f1 n))
={Def f1-t, C10}
(equal (f1-t r2 (+ r1 r2) (+ i 1) n) (f1 n))
={C20}
t

|#

#|
Q1d

Use the theorem from Q1c to prove the following theorem.

(implies (natp n)
         (equal (f1* n) (f1 n)))

C1. (natp n)
------------
C2. (or (< n 2) (not (< n 2))) {Arith, C1}
C3. (implies (< n 2) (equal (f1* n) (+ n 4))) {Def f1*}
C4. (implies (< n 2) (equal (f1 n) (+ n 4))) {Def f1}
C5. (implies (< n 2) (equal (f1* n) (f1 n))) {equal, C3, C4}
C6. (implies (not (< n 2))
             (equal (f1* n) (f1-t 5 9 2 n))) {Def f1*}
C7. (equal (f1 1) 5) {Def f1}
C8. (equal (f1 2) 9) {Def f1}
C9. (implies (not (< n 2))
             (equal (f1-t 5 9 2 n) (f1 n))) {Q1c, C1, C7, C8}
C10. (implies (not (< n 2))
              (equal (f1* n) (f1-t 5 9 2 n))) {Def f1*}
C11. (implies (not (< n 2))
              (equal (f1* n) (f1 n))) {equal, C1, C10}
C12. (equal (f1* n) (f1 n)) {Or-elim, C2, C5, C11}

(implies (and (natp n) (natp r1) (natp r2) (natp i) (<= i n) (>= i 2) (>= n 2)
              (equal r1 (f1 (- i 1)))
              (equal r2 (f1 i)))
         (equal (f1-t r1 r2 i n) (f1 n)))             
(implies (natp n) (equal (f1* n) (f1 n)))
={MP, C1}
(equal (f1* n) (f1 n))
={C12}
t          

|#

#|
Q1e

If your definition of f* is correct and efficient, then the following
test should pass instantaniously.

|#

(check=
 (f1* 500)
 1041789289209443203629775163014695572134115556242730069618664428622224082577610824311621607087410395288629)


#|

Q2. Consider the following function definitions from hwk9.

|#

(defdata2 lor (listof rational))

(defunc2 insert (a x)
  :input-contract (and (rationalp a) (lorp x))
  :output-contract (lorp (insert a x))
  (cond ((endp x) (cons a nil))
        ((<= a (car x)) (cons a x))
        (t (cons (car x) (insert a (cdr x))))))

#|

Q2a. Define insert-t, a tail recursive version of insert.

|#

(defunc2 insert-t (a x acc)
  :input-contract (and (rationalp a) (lorp x) (lorp acc))
  :output-contract (lorp (insert-t a x acc))
  (cond ((endp x) (rev* (cons a acc)))
        ((<= a (car x)) (append (rev* acc) (cons a x)))
        (t (insert-t a (cdr x) (cons (car x) acc)))))

#|

Q2b. Define insert*, a non-recursive function that is
equivalent to insert and uses insert-t.

|#

(defunc2 insert* (a x)
  :input-contract (and (rationalp a) (lorp x))
  :output-contract (lorp (insert a x))
  (insert-t a x nil))

(check= (insert 3 '(2 3 4 5)) (insert* 3 '(2 3 4 5)))
(check= (insert 1 '(2 3 4 5)) (insert* 1 '(2 3 4 5)))
(check= (insert 6 '(2 3 4 5)) (insert* 6 '(2 3 4 5)))
(check= (insert 3 '()) (insert* 3 '()))


(suggest-lemma (insert-t a x acc)
	       :required-expressions (insert a x)
	       :with append reverse insert)

(thm
 (IMPLIES (AND (RATIONALP A) (LORP X) (LORP ACC))
	  (EQUAL (INSERT-T A X ACC)
		 (APPEND (REVERSE ACC) (INSERT A X)))))
#|
Q2c. Prove a theorem of this form

(implies (and (rationalp a) (lorp x) (lorp acc))
         (equal (insert-t a x acc)
                (app (rev acc) (insert a x))))

This will be proven using the induction scheme of insert-t

1. (implies (not (and (rationalp a) (lorp x) (lorp acc))) Q2c)
Reductio ad absurdum. Done.
                
2. (implies (and (rationalp a) (lorp x) (lorp acc) 
                 (endp x)) Q2c)

C1. (rationalp a)
C2. (lorp x)
C3. (lorp acc)
C4. (endp x)
--------------
C5. (lorp (cons a acc)) {Def lorp, C3}

(implies (and (rationalp a) (lorp x) (lorp acc))
         (equal (insert-t a x acc)
                (app (rev acc) (insert a x))))
={MP, C1, C2, C3}
(equal (insert-t a x acc) (app (rev acc) (insert a x)))
={Def insert-t, C4}
(equal (rev* (cons a acc)) (app (rev acc) (insert a x)))
={Def insert, C4}
(equal (rev* (cons a acc)) (app (rev acc) (list a)))
={rev*-rev, C5}
(equal (rev (cons a acc)) (app (rev acc) (list a)))
={Def rev}
(equal (app (rev acc) (list a)) (app (rev acc) (list a)))
={equal axiom}
t


3. (implies (and (rationalp a) (lorp x) (lorp acc) 
                 (not (endp x)) (<= a (first x))) Q2c)

C1. (rationalp a)
C2. (lorp x)
C3. (lorp acc)
C4. (not (endp x))
C5. (<= a (first x))
--------------
C6. (lorp (cons a acc)) {Def lorp, C3}

(implies (and (rationalp a) (lorp x) (lorp acc))
         (equal (insert-t a x acc)
                (app (rev acc) (insert a x))))
={MP, C1, C2, C3}
(equal (insert-t a x acc) (app (rev acc) (insert a x)))
={Def insert-t, C4, C5}
(equal (app (rev* acc) (cons a x)) (app (rev acc) (insert a x)))
={Def insert, C4, C5}
(equal (app (rev* acc) (cons a x)) (app (rev acc) (cons a x)))
={rev*-rev, C6}
(equal (app (rev acc) (cons a x)) (app (rev acc) (cons a x)))
={equal axiom}
t


4. (implies (and (rationalp a) (lorp x) (lorp acc) 
                 (not (endp x)) (not (<= a (first x)))
                 (Q2c | ((x (rest x)) (acc (cons (first x) acc))))) Q2c) 

C1. (rationalp a)
C2. (lorp x)
C3. (lorp acc)
C4. (not (endp x))
C5. (not (<= a (first x)))
C6. (implies (and (rationalp a) (lorp (rest x)) (lorp (cons (first x) acc)))
             (equal (insert-t a (rest x) (cons (first x) acc)) 
                    (app (rev (cons (first x) acc)) (insert a (rest x)))))
--------------     
C7. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C2, C4}
C8. (lorp (cons (first x) acc)) {Def lorp, C3}
C9. (equal (insert-t a (rest x) (cons (first x) acc)) 
           (app (rev (cons (first x) acc)) (insert a (rest x)))) {MP, C6, C1, C7, C8}


(implies (and (rationalp a) (lorp x) (lorp acc))
         (equal (insert-t a x acc)
                (app (rev acc) (insert a x))))
={MP, C1, C2, C3}
(equal (insert-t a x acc) (app (rev acc) (insert a x)))
={Def insert-t, C4, C5}
(equal (insert-t a (rest x) (cons (first x) acc)) (app (rev acc) (insert a x)))
={C9}
(equal (app (rev (cons (first x) acc)) (insert a (rest x))) 
       (app (rev acc) (insert a x)))
={Def insert, C4, C5}
(equal (app (rev (cons (first x) acc)) (insert a (rest x)))
       (app (rev acc) (cons (first x) (insert a (rest x)))))
={Def rev}
(equal (app (app (rev acc) (list (first x))) (insert a (rest x)))
       (app (rev acc) (cons (first x) (insert a (rest x)))))
={associativity of app}
(equal (app (rev acc) (app (list (first x)) (insert a (rest x))))
       (app (rev acc) (cons (first x) (insert a (rest x)))))
={Def app} 
(equal (app (rev acc) (cons (first x) (app nil (insert a (rest x)))))
       (app (rev acc) (cons (first x) (insert a (rest x)))))
={Def app} 
(equal (app (rev acc) (cons (first x) (insert a (rest x))))
       (app (rev acc) (cons (first x) (insert a (rest x)))))
={equal axiom}
t

|#

#|
Q2d. Use the theorem from Q2c to prove the following theorem.

(implies (and (rationalp a) (lorp x))
         (equal (insert* a x)
                (insert a x)))

C1. (rationalp a)
C2. (lorp x)
-------------

(implies (and (rationalp a) (lorp x))
         (equal (insert* a x)
                (insert a x)))
={MP, C1, C2}
(equal (insert* a x) (insert a x))
={Def insert*, C1, C2}
(equal (insert-t a x nil) (insert a x))
={Q1c, C1, C2}
(equal (app (rev* nil) (insert a x)) (insert a x))
={Def rev*, Def rev*-t}
(equal (app nil (insert a x)) (insert a x))
={Def app}
(equal (insert a x) (insert a x))
={equal axiom}
t

|#

#|

Q3. Consider the following function definition from hwk9.

|#

(defunc isort (x)
  :input-contract (lorp x)
  :output-contract (lorp (isort x))
  (if (endp x)
      ()
    (insert (first x) (isort (rest x)))))

#|

Here is a tail recursive version of isort.

|#

(defunc isort-t (x acc)
  :input-contract (and (lorp x) (lorp acc))
  :output-contract (lorp (isort-t x acc))
  (if (endp x)
      acc
    (isort-t (rest x) (insert (first x) acc))))

#|

Q3a. Define isort*, a non-recursive function that is
equivalent to isort and uses isort-t.

|#

(defunc isort* (x)
  :input-contract (lorp x)
  :output-contract (lorp (isort* x))
  (isort-t x nil))

#|

Q3b.

(implies (and (lorp x) (lorp acc))
         (perm (isort-t x acc)
                (append x acc)))

This will be proven using the induction scheme of (isort-t x acc).

Proof Obligations:

1. (implies (not (and (lorp x) (lorp acc))) Q3b)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp acc) (endp x)) Q3b)

C1. (lorp x)
C2. (lorp acc)
C3. (endp x)
---------------

(implies (and (lorp x) (lorp acc))
         (perm (isort-t x acc)
                (append x acc)))
={MP, C1, C2}
(perm (isort-t x acc) (append x acc))
={Def isort-t, C3}
(perm acc (append x acc))
={Def append, C3}
(perm acc acc)
={Hw9, perm reflexive, C2}
t

3. (implies (and (lorp x) (lorp acc) (not (endp x))
                 (Q3b | ((x (rest x)) (acc (insert (first x) acc))))) Q3b)

C1. (lorp x)
C2. (lorp acc)
C3. (not (endp x))
C4. (implies (and (lorp (rest x)) (lorp (insert (first x) acc)))
             (perm (isort-t (rest x) (insert (first x) acc))
                   (append (rest x) (insert (first x) acc))))
---------------
C5. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C3}
C6. (lorp (insert (first x) acc)) {Contract thm, insert, C5, C2}
C7. (perm (isort-t (rest x) (insert (first x) acc))
          (append (rest x) (insert (first x) acc))) {MP, C4, C5, C6}
C8. (in (first x) (insert (first x) acc)) {Lemma from Hw9, C5, C2}
C9. (perm acc acc) {reflexivity of perm, Hw9, C2}
C10. (equal acc (del (first x) (insert (first x) acc))) {Lemma from Hw9}
C11. (perm acc (del (first x) (insert (first x) acc))) {C9, C10}
C12. (perm (cons (first x) acc)
           (insert (first x) acc)) {Def perm, C11, C8}
C13. (perm (cons (first x) (append (rest x) acc))
           (append (rest x) (cons (first x) acc)) {L2, C5, C2}

C14. (perm (append (rest x) (cons (first x) acc))
           (append (rest x) (insert (first x) acc))) {Lemma from Hw9}
C15. (perm (append (rest x) (insert (first x) acc))
           (cons (first x) (append (rest x) acc))) {Trans. of perm}
           
(implies (and (lorp x) (lorp acc))
         (perm (isort-t x acc)
               (append x acc)))
={MP, C1, C2}
(perm (isort-t x acc) (append x acc))
={Def isort-t, C3}
(perm (isort-t (rest x) (insert (first x) acc))
      (append x acc))
={Transitivity + symmetricity of perm, C7}
(perm (append (rest x) (insert (first x) acc))
      (apend x acc))
={Def append, C3}
(perm (append (rest x) (insert (first x) acc))
      (cons (first x) (append (rest x) acc)))
={C15}
t

You can use any definitions and theorems we proved in hwk9.
You will most likely need a collection of lemmas.

Extra lemmas:

            
L1:
(implies (and (lorp x) (lorp acc) (orderedp acc))
         (orderedp (isort-t x acc)))

This will be proven using the induction scheme for (isort-t x acc)

1. (implies (not (and (lorp x) (lorp acc) (orderedp acc))) L1)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp acc) (orderedp acc) (endp x)) L1)
C1. (lorp x)
C2. (lorp acc)
C3. (orderedp acc)
C4. (endp x)
--------------

(implies (and (lorp x) (lorp acc) (orderedp acc))
         (orderedp (isort-t x acc)))
={MP, C1, C2, C3}
(orderedp (isort-t x acc))
={Def isort-t, C4}
(orderedp acc)
={C3}
t

3. (implies (and (lorp x) (lorp acc) (orderedp acc) (not (endp x))
                 (L1 | ((x (rest x)) (acc (insert (first x) acc))))) L1)
C1. (lorp x)
C2. (lorp acc)
C3. (orderedp acc)
C4. (not (endp x))
C5. (implies (and (lorp (rest x)) 
                  (lorp (insert (first x) acc)) 
                  (orderedp (insert (first x) acc)))
             (orderedp (isort-t (rest x) (insert (first x) acc))))
--------------
C6. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C4}
C7. (lorp (insert (first x) acc)) {Contract thm insert, C6, C2}
C8. (orderedp (insert (first x) acc)) {Lemma from hw9, C3, C6}
C9. (orderedp (isort-t (rest x) (insert (first x) acc))) {MP, C5, C6, C7, C8}

(implies (and (lorp x) (lorp acc) (orderedp acc))
         (orderedp (isort-t x acc)))
={MP, C1, C2, C3}
(orderedp (isort-t x acc))
={Def isort-t, C4}
(orderedp (isort-t (rest x) (insert (first x) acc)))
={C9}
t

L2. (implies (and (lorp x) (lorp y) (rationalp z))
             (perm (cons z (append x y))
                   (append x (cons z y))))

This will be proven using the induction scheme of (listp x).

1. (implies (not (and (lorp x) (lorp y) (rationalp z))) L2)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (rationalp z) (endp x)) L2)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (endp x)
--------------

(implies (and (lorp x) (lorp y) (rationalp z))
             (perm (cons z (append x y))
                   (append x (cons z y))))
={MP, C1, C2, C3}
(perm (cons z (append x y)) (append x (cons z y)))
={Def append, C4}
(perm (cons z y) (cons z y))
={Reflexivity of perm, Hw9}
t

3. (implies (and (lorp x) (lorp y) (rationalp z)
                 (not (endp x))
                 (L2 | ((x (rest x))))) L2)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (implies (and (lorp (rest x)) (lorp y) (rationalp z))
             (perm (cons z (append (rest x) y))
                   (append (rest x) (cons z y))))
--------------
C6. (perm (append x y) (del (append x (cons z y)))) {L4, C1, C2, C3}
C7. (in z (append x (cons z y))) {L5, C1, C2, C3}

(implies (and (lorp x) (lorp y) (rationalp z))
             (perm (cons z (append x y))
                   (append x (cons z y))))
={MP, C1, C2, C3}
(perm (cons z (append x y)) (append x (cons z y)))
={Def perm}
(and (in z (append x (cons z y)))
     (perm (append x y) (del z (append x (cons z y)))))
={C6, C7}
t


L4. (implies (and (lorp x) (lorp y) (rationalp z))
             (in z (append x (cons z y))))

This will be proven using the induction scheme of (listp x)

1. (implies (not (and (lorp x) (lorp y) (rationalp z))) L4)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (rationalp z) (endp x)) L4)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (endp x)
--------------

(implies (and (lorp x) (lorp y) (rationalp z))
         (in z (append x (cons z y))))
={MP, C1, C2, C3}
(in z (append x (cons z y)))
={Def append, C4}
(in z (cons z y))
={Def in, C3, C2}
t

3. (implies (and (lorp x) (lorp y) (rationalp z) (endp x)
                 (L4 | ((x (rest x))))) L4)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (implies (and (lorp (rest x)) (lorp y) (rationalp z))
             (in z (append (rest x) (cons z y))))
--------------
C6. (lorp (rest x)) {Def lorp, C1, C4}
C7. (in z (append (rest x) (cons z y))) {MP, C5, C6, C2, C3}


(implies (and (lorp x) (lorp y) (rationalp z))
         (in z (append x (cons z y))))
={MP, C1, C2, C3}
(in z (append x (cons z y)))
={Def append, C4}
(in z (cons (first x) (append (rest x) (cons z y))))
={Def in}
(or (equal z (first x))
    (in z (append (rest x) (cons z y))))
={PL, C7}
t

L5. (implies (and (lorp x) (lorp y) (rationalp z))
             (perm (append x y) (del z (append x (cons z y)))))

This will be proven using the induction scheme of (listp x).

1. (implies (not (and (lorp x) (lorp y) (rationalp z))) L5)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (rationalp z) (endp x)) L5)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (endp x)
------------

(implies (and (lorp x) (lorp y) (rationalp z))
             (perm (append x y) (del z (append x (cons z y)))))
={MP, C1, C2, C3}
(perm (append x y) (del z (append x (cons z y))))
={Def append, C4}
(perm y (del z (cons z y)))
={Def del}
(perm y y)
={equal axiom}
t

3. (implies (and (lorp x) (lorp y) (rationalp z) (not (endp x))
                 (L4 | ((x (rest x))))) L5)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (implies (and (lorp (rest x)) (lorp y) (rationalp z))
             (perm (append (rest x) y) (del z (append (rest x) (cons z y)))))
-----------------------
C6. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C4}
C7. (perm (append (rest x) y) (del z (append (rest x) (cons z y)))) {MP, C5, C6, C2, C3}
C8. (or (equal (first x) z) (not (equal (first x) z))) {Arith, C3, C6}
C9. (perm (cons (first x) (append (rest x) y)) 
          (cons (first x) (del z (append (rest x) (cons z y))))) {Def perm, in, C7}
C10. (implies (not (equal (first x) z))
             (equal (del z (cons (first x) (append (rest x) (cons z y))))
                    (cons (first x) (del z (append (rest x) (cons z y)))))) 
     {Def del, C6}
C11. (implies (not (equal (first x) z))
              (perm (cons (first x) (append (rest x) y))
                    (del z (cons (first x) (append (rest x) (cons z y)))))) -- case 1 done
     {C9, C7, C10}
C12. (implies (equal (first x) z)
              (equal (del z (cons (first x) (append (rest x) (cons z y))))
                     (append (rest x) (cons z y)))) {Def del, C6}
C13. (perm (cons z (append (rest x) y))
           (append (rest x) (cons z y))) {L2, C6, C2}
C14. (implies (equal (first x) z)
              (perm (cons z (append (rest x) y))
                    (del z (cons (first x) (append (rest x) (cons z y)))))) {C13, C12}
C15. (implies (equal (first x) z)
              (perm (cons (first x) (append (rest x) y))
                    (del z (cons (first x) (append (rest x) (cons z y)))))) -- case 2 done
     {trivial}                    

C16. (perm (cons (first x) (append (rest x) y))
           (del z (cons (first x) (append (rest x) (cons z y)))))
     {Or elimination, C8, C11, C15}
     
(implies (and (lorp x) (lorp y) (rationalp z))
             (perm (append x y) (del z (append x (cons z y)))))
={MP, C1, C2, C3}
(perm (append x y) (del z (append x (cons z y))))
={Def perm, C4}
(perm (cons (first x) (append (rest x) y)) 
      (del z (cons (first x) (append (rest x) (cons z y)))))
={C16}
t

|#


#|
Q3c. Use the theorem from Q3b to prove the following theorem.

(implies (lorp x)
         (equal (isort* x)
                (isort x)))

C1. (lorp x)
-------------
C2. (orderedp (isort-t x nil)) {L1, C1}
C3. (perm (isort-t x nil) (append x nil)) {Q3b, C1}
C4. (perm (isort-t x nil) x) {append axiom, C1}
C5. (perm (isort x) x) {from HW9, C1}
C6. (orderedp (isort x)) {from HW9, C1}
C7. (perm (isort-t x nil) (isort x)) {equiv. relation of perm, HW9}
C8. (equal (isort-t x nil) (isort x)) {unique ordered perms, HW9}

(implies (lorp x) (equal (isort* x) (isort x)))
={MP, C1}
(equal (isort* x) (isort x))
={Def isort*}
(equal (isort-t x nil) (isort x))
={C8}
t

|#

#|

Q4. Consider the following function definition.

|#

(defunc2 zip-list (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (zip-list x y))
  (if (or (endp x) (endp y))
    nil
    (cons (cons (car x) (cons (car y) nil))
          (zip-list (cdr x)
                    (cdr y)))))

#| 

Q4a. Define zip-list-t, a tail-recursive function corresponding to
zip-list.

|#

(defunc2 zip-list-t (x y acc)
  :input-contract (and (true-listp x) (true-listp y) (true-listp acc))
  :output-contract (true-listp (zip-list-t x y acc))
  (if (or (endp x) (endp y))
    (rev* acc)
    (zip-list-t (cdr x) (cdr y) (cons (cons (car x) (cons (car y) nil)) acc))))

#|

Q4b. Define zip-list*, a non-recursive function that is
equivalent to zip-list and uses zip-list-t.

|#

(defunc2 zip-list* (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (zip-list* x y))
  (zip-list-t x y nil))

(suggest-lemma (zip-list-t x y acc)
	       :required-expressions (zip-list x y)
	       :with reverse append zip-list)

(thm
 (IMPLIES (AND (TRUE-LISTP X)
	       (TRUE-LISTP Y)
	       (TRUE-LISTP ACC))
	  (EQUAL (ZIP-LIST-T X Y ACC)
		 (APPEND (REVERSE ACC) (ZIP-LIST X Y)))))
#|

Q4c. Prove a theorem of this form

(implies (and (lorp x) (lorp y) (listp acc))
         (equal (zip-list-t x y acc)
                (app (rev acc) (zip-list x y))))

This will be proven using the induction scheme of (zip-list-t x y acc)

Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (listp acc))) Q4c)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (listp acc) (or (endp x) (endp y))) Q4c)

C1. (lorp x)
C2. (lorp y)
C3. (listp acc)
C4. (or (endp x) (endp y))
--------------------------

(implies (and (lorp x) (lorp y) (listp acc))
         (equal (zip-list-t x y acc)
                (app (rev acc) (zip-list x y)))
={MP, C1, C2, C3}
(equal (zip-list-t x y acc) (app (rev acc) (zip-list x y)))
={Def zip-list-t, C4}
(equal (rev* acc) (app (rev acc) (zip-list x y)))
={Def zip-list, C4}
(equal (rev* acc) (app (rev acc) nil))
={rev*-rev, C3}
(equal (rev acc) (app (rev acc) nil))
={app-x-nil=x, C3}
(equal (rev acc) (rev acc))
={equal axiom}
t

3. (implies (and (lorp x) (lorp y) (listp acc) 
                 (not (or (endp x) (endp y)))
                 (Q4c | ((x (rest x)) 
                         (y (rest y)) 
                         (acc (cons (list (first x) (first y)) acc))))) Q4c)

C1. (lorp x)
C2. (lorp y)
C3. (listp acc)
C4. (not (or (endp x) (endp y)))
C5. (implies (and (lorp (rest x)) (lorp (rest y)) (lorp (cons (list (first x) (first y)) acc)))
             (equal (zip-list (rest x) (rest y) (cons (list (first x) (first y)) acc))
                    (app (rev (cons (list (first x) (first y)) acc)) (zip-list (rest x) (rest y)))))
--------------------------
C6. (lorp (rest x)) {Def lorp, C1, C4}
C7. (lorp (rest y)) {Def lorp, C2, C4}
C8. (listp (cons (list (first x) (first y)) acc)) = {Def listp, C3}
C9. (equal (zip-list (rest x) (rest y) 
                     (cons (list (first x) (first y)) acc))
           (app (rev (cons (list (first x) (first y)) acc)) 
                (zip-list (rest x) (rest y)))) {MP, C5, C6, C7, C8}

(implies (and (lorp x) (lorp y) (listp acc))
         (equal (zip-list-t x y acc)
                (app (rev acc) (zip-list x y))))
={MP, C1, C2, C3}
(equal (zip-list-t x y acc) (app (rev acc) (zip-list x y)))
={Def zip-list-t}
(equal (zip-list-t (rest x) (rest y) (cons (list (first x) (first y)) acc))
       (app (rev acc) (zip-list x y)))
={C9}
(equal (app (rev (cons (list (first x) (first y)) acc)) 
            (zip-list (rest x) (rest y)))
       (app (rev acc) (zip-list x y)))
={Def app}
(equal (app (app (rev acc) (list (list (first x) (first y))))
            (zip-list (rest x) (rest y)))
       (app (rev acc) (zip-list x y)))
={associativity of app}
(equal (app (rev acc) 
            (app (list (list (first x) (first y)))
                 (zip-list (rest x) (rest y))))
       (app (rev acc) (zip-list x y)))
={Def app}
(equal (app (rev acc) 
            (cons (list (first x) (first y)))
                  (zip-list (rest x) (rest y)))
       (app (rev acc) (zip-list x y)))
={Def zip-list}
(equal (app (rev acc) (zip-list x y))
       (app (rev acc) (zip-list x y)))
={equal axiom}
t

|#


#|
Q4d. Use the theorem from Q4c to prove the following theorem.

(implies (and (listp x) (listp y))
         (equal (zip-list* x y)
                (zip-list  x y)))
                
C1. (listp x)
C2. (listp y)
-------------

(implies (and (listp x) (listp y))
         (equal (zip-list* x y)
                (zip-list  x y)))
={MP, C1, C2}
(equal (zip-list* x y) (zip-list x y))
={Def zip-list*}
(equal (zip-list-t x y nil) (zip-list x y))
={Q4c, C1, C2}
(equal (app (rev nil) (zip-list x y)) (zip-list x y))
={Def rev}
(equal (app nil (zip-list x y)) (zip-list x y))
={Def app}
(equal (zip-list x y) (zip-list x y))
={equal axiom}
t
|#
