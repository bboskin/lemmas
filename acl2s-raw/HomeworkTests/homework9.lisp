#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will NOT need to use ACL2s. However, you could
use the Eclipse/ACL2s text editor to write up your solution and
you may want to use ACL2s to help you check your answers.

If you want to use ACL2s, then you can. This is entirely optional and
will require you understand how to steer the theorem prover, which
will require you read some lecture notes that are available on the
class Webpage, but which we will not cover in class and will not be on
the exam. If you still want to try, then if you submit a sequence of
defthms that include conjectures you are asked to prove below, then we
will give you full credit for any such conjectures, but none of the
defthms you submit can use nested induction proofs. You can tell that
a nested induction proof was used by looking at the output of the
theorem prover.  If you see the following:

"*1 is COMPLETED!"

then no nested inductions were performed. If you see something like:

"..., *1.1 and *1 are COMPLETED!"

Then nested inductions were performed. So, at that point you can look
at what *1.1 is, generalize it and submit it as a defthm, which should
allow ACL2s to not have to perform that nested induction.

You can use ACL2s for some of the conjectures and text proofs for the
rest. I do not recommend doing this unless you feel very confident in
doing paper and pencil proofs.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Technical instructions:
 
- Open this file in ACL2s as hwk9.lisp

- Make sure you are in BEGINNER mode. This is essential! Note that you
  can only change the mode when the session is not running, so set the
  correct mode before starting the session.

- Insert your solutions into this file where indicated (usually as "...")

- Only add to the file. Do not remove or comment out anything
  pre-existing.

- Make sure the entire file is accepted by ACL2s. In particular, there
  must be no "..." left in the code. If you don't finish all problems,
  comment the unfinished ones out. Comments should also be used for
  any English text that you may add. This file already contains many
  comments, so you can see what the syntax is.

- When done, save your file and submit it as hwk9.lisp

- Do not submit the session file (which shows your interaction with
  the theorem prover). This is not part of your solution. Only submit
  the lisp file.

PROGRAMMING INSTRUCTIONS

For each function you define, you must provide a purpose statement
(unless we have provided one for you), contracts (unless we have
provided one for you), a body, check= tests *and* test?
forms (property-based testing).  For each data definition you define,
you must provide a purpose statement, check= tests *and* test?
forms (property-based testing).  This is in addition to the tests
sometimes provided. Make sure you produce sufficiently many new test
cases and at least two interesting test? forms. If we provide a
purpose statement for you, you do not need to provide another one.

For function definitions, make sure to provide as many tests as the
data definitions dictate. For example, a function taking two lists
should have at least 4 tests: all combinations of each list being
empty and non-empty.  Beyond that, the number of tests should reflect
the difficulty of the function. For very simple ones, the above
coverage of the data definition cases may be sufficient. For complex
functions with numerical output, you want to test whether it produces
the correct output on a reasonable number of inputs.

Use good judgment. For example, if you are asked to define a function
with no arguments and we ask you to show the output it generates,
there is no need to add any check= or test? forms. For unreasonably
few test cases and properties we will deduct points. If you have any
questions at all, please ask on Piazza. It is better to be safe that
sorry.

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

|#


#|

PROOFS BY INDUCTION 

Prove the following conjectures using induction.  Almost all of these
conjectures will require lemmas. Some of them will require
generalization and some will require exploration and thought so give
yourselves plenty of time.  You can freely use the definitional and
function contract theorems of the functions we provide below or that
we have covered in class. You can also freely use any theorems we
proved in class and in the lecture notes.

Make sure you identify what induction scheme you are using.  For
example, suppose you were proving that app is associative:

(listp x) ^ (listp y) ^ (listp z) =>
(app (app x y) z) = (app x (app y z))

At the beggining of the proof you should say:

Proof by induction using (listp x).

Make sure you understand the algorithm provided in the lecture
notes for generating induction schemes.

For this homework, the goal is to define the beginnings of a verified
library for sorting lists of numbers. We provide you with simple
versions of insert sort and quicksort (functions that we also saw in
the last homework) and you will prove that they satisfy various
properties.

|#
(defttag t)

(include-book "top" :uncertified-okp t)

(defdata2 lor (listof rational))

(defunc2 lte (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (booleanp (lte a b))
  (<= a b))

(defunc2 lt (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (booleanp (lte a b))
  (< a b))

(defunc2 insert (a x)
  :input-contract (and (rationalp a) (lorp x))
  :output-contract (lorp (insert a x))
  (cond ((endp x) (cons a nil))
        ((lte a (car x)) (cons a x))
        (t (cons (car x) (insert a (cdr x))))))

(defunc2 isort (x)
  :input-contract (lorp x)
  :output-contract (lorp (isort x))
  (if (endp x)
      ()
    (insert (car x) (isort (cdr x)))))

(defunc2 less (x lst)
  :input-contract (and (rationalp x) (lorp lst))
  :output-contract (lorp (less x lst))
  (cond ((endp lst) ())
        ((lt (car lst) x)
         (cons (car lst) (less x (cdr lst))))
        (t (less x (cdr lst)))))

(defunc2 notless (x lst)
  :input-contract (and (rationalp x) (lorp lst))
  :output-contract (lorp (notless x lst))
  (cond ((endp lst) nil)
        ((lte x (car lst))
         (cons (car lst) (notless x (cdr lst))))
        (t (notless x (cdr lst)))))

(defunc2 qsort (x)
  :input-contract (lorp x)
  :output-contract (lorp (qsort x))
  (if (endp x) 
      ()
    (append (qsort (less (car x) (cdr x)))
            (append (cons (car x) nil)
                    (qsort (notless (car x) (cdr x)))))))

(defunc2 orderedp (x)
  :input-contract (lorp x)
  :output-contract (booleanp (orderedp x))
  (or (endp x)
      (endp (cdr x))
      (and (lte (car x) (car (cdr x)))
           (orderedp (cdr x)))))

(defunc2 del (e x)
  :input-contract (and (rationalp e) (lorp x))
  :output-contract (lorp (del e x))
  (cond ((endp x) nil)
        ((equal e (car x)) (cdr x))
        (t (cons (car x) (del e (cdr x))))))


(defunc2 in (e x)
  :input-contract (and (rationalp e) (lorp x))
  :output-contract (booleanp (in e x))
  (cond ((endp x) nil)
        ((equal e (car x)) t)
        (t (in e (cdr x)))))

(defunc2 perm (x y)
  :input-contract (and (lorp x) (lorp y))
  :output-contract (booleanp (perm x y))
  (if (endp x)
      (endp y)
    (and (in (car x) y)
         (perm (cdr x) (del (car x) y)))))

; Prove the following

; Q1
#|
(implies (lorp x)
         (orderedp (isort x)))
|#

(defgroup sorting qsort isort insert orderedp perm)

(suggest-lemma t
	       :required-expressions orderedp insert
	       :with sorting
	       :hyps (lorp ls) (orderedp ls) (rationalp x))

(defthm insert-ordered
  (IMPLIES (AND (LORP LS)
		(ORDEREDP LS)
		(RATIONALP X))
	   (ORDEREDP (INSERT X LS))))

(suggest-lemma t
	       :required-expressions orderedp isort 
	       :with sorting
	       :hyps (lorp ls))

(defthm isort-ordered
  (IMPLIES (LORP LS)
	   (ORDEREDP (ISORT LS))))

#|
; Q2
(implies (lorp x)
         (orderedp (qsort x)))

; Helper Functions for lemmas
|#

(defunc2 less-than-all (x xs)
  :input-contract (and (rationalp x) (lorp xs))
  :output-contract (booleanp (less-than-all x xs))
  (cond ((endp xs) t)
        ((lt x (car xs)) (less-than-all x (cdr xs)))
        (t nil)))

;; to say that every element of one list is less than or equal to 
;; every element in another
(defunc all-less-than (xs1 xs2)
  :input-contract (and (lorp xs1) (lorp xs2))
  :output-contract (booleanp (all-less-than xs1 xs2))
  (cond ((endp xs1) t)
        ((less-than-all (first xs1) xs2)
         (all-less-than (rest xs1) xs2))
        (t nil)))

(defunc greater-than-all (x xs)
  :input-contract (and (rationalp x) (lorp xs))
  :output-contract (booleanp (greater-than-all x xs))
  (cond ((endp xs) t)
        ((>= x (first xs)) (greater-than-all x (rest xs)))
        (t nil)))

;; to say that every element of one list is greater than 
;; every element in another
(defunc all-greater-than (xs1 xs2)
  :input-contract (and (lorp xs1) (lorp xs2))
  :output-contract (booleanp (all-greater-than xs1 xs2))
  (cond ((endp xs1) t)
        ((greater-than-all (first xs1) xs2)
         (all-greater-than (rest xs1) xs2))
        (t nil)))
#|

L0: (implies (and (rationalp pivot)
                  (lorp ls))
             (less-than-all pivot (notless pivot ls)))

This will be proved using the induction scheme of less-than-all:

Termination of less-than-all: 
a measure can be a function that returns the length of the first list, this
is clearly correct and satisfies the required properties.

Obligations for the conjecture, now that we have termination:

1. (implies (or (not (rationalp pivot)) (lorp ls)) L0)

C1: (or (not (rationalp pivot)) (lorp ls))
----------------

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
= {PL}
(implies nil (less-than-all pivot (notless pivot ls)))
= {PL}
L0

2. (implies (and (rationalp pivot) (endp ls)) L0)

C1: (rationalp pivot)
C2: (endp ls)
-------------

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
={MP, C1, C2}
(less-than-all pivot (notless pivot ls))
={Def notless, C1, C2}
(less-than-all pivot nil)
={Def less-than-all, C1}
t
         
3. (implies (and (rationalp pivot) (lorp ls) (consp ls) (< pivot (first ls))
                 (L0 | ((pivot pivot) (ls (rest ls))))) L0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (< pivot (first ls))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (less-than-all pivot (notless pivot (rest ls))))
----------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C7: (less-than-all pivot (notless pivot (rest ls))) {MP, C5, C1, C6}

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
={MP, C1, C2}
(less-than-all pivot (notless pivot ls))
={Def notless, C1, C2, C4}
(less-than-all pivot (notless pivot (rest lst)))
={C7}
t

4. (implies (and (rationalp pivot) (lorp ls) (consp ls) (not (< pivot (first ls)))
                 (L0 | ((pivot pivot) (ls (rest ls)))))
            L0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (not (< pivot (first ls)))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (less-than-all pivot (notless pivot (rest ls))))
-----------------------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C8: (lorp (notless pivot (rest ls))) {Contract thm, notless, C1, C5}
C9: (less-than-all pivot (notless pivot (rest ls))) {MP, C5, C1, C6}

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
= {C1, C2}
(less-than-all pivot (notless pivot ls))
={Def notless, C1, C3, C7}
(less-than-all pivot (cons (first ls) (notless pivot (rest ls))))
={Def less-than-all, C1, C7, C4, C8}
(less-than-all pivot (notless pivot (rest ls)))
= {C9}
t
       
L0.5: (implies (and (rationalp pivot) 
                    (lorp ls) 
                    (consp ls) 
                    (less-than-all pivot ls))
               (< pivot (first ls)))

Obligations:
1. (implies (or (not (rationalp pivot))
                (not (lorp ls))
                (not (consp ls))
                (not (less-than-all pivot ls)))
            L0.5)

MP -> (implies nil (< pivot (first ls))) -> t

2. (implies (and (rationalp pivot)
                 (lorp ls)
                 (endp ls)
                 (less-than-all pivot ls))
            L0.5)
MP -> (implies nil (< pivot (first ls))) -> t

3. (implies (and (rationalp pivot)
                 (lorp ls)
                 (consp ls)
                 (< pivot (first ls))
                 (L0.5 | ((pivot pivot) (ls (rest ls)))))
            L0.5)
C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (< pivot (first ls))
C5: (less-than-all pivot ls)
C6: (implies (and (rationalp pivot) (lorp (rest ls)) (consp (rest ls)) (less-than-all pivot (rest ls)))
                  (< pivot (first (rest ls))))
----------------------

(implies (and (rationalp pivot) (lorp ls) (consp ls) (less-than-all pivot ls))
         (< pivot (first ls)))
= {MP, C1, C2, C3, C5}
(< pivot (first ls))
= {C4}
t


L1: (implies (and (rationalp pivot)
                  (lorp ls))
             (greater-than-all pivot (less pivot ls)))

Essentially the same proof as L0.

L2: (implies (and (rationalp pivot)
                  (lorp ls))
             (all-less-than (less pivot ls) 
                            (notless pivot ls)))
This will be proved using the induction scheme of all-less-than.

Obligations:
1. (implies (or (not (rationalp pivot)) (not (lorp ls))) L2)
  
C1: (or (not (rationalp pivot)) (not (lorp ls)))
-----------------

(implies (and (rationalp pivot)
              (lorp ls))
         (all-less-than (less pivot ls) 
                        (notless pivot ls)))
= {C1, PL}                        
(implies nil
         (all-less-than (less pivot ls) 
                        (notless pivot ls)))
= {PL}
t
                        
2. (implies (and (rationalp pivot) (lorp ls) (endp ls)) L2)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (endp ls)
---------------

(implies (and (rationalp pivot)
              (lorp ls))
         (all-less-than (less pivot ls) 
                        (notless pivot ls)))
= {MP, C1, C2}
(all-less-than (less pivot ls) (notless pivot ls))
={Def less, C3}
(all-less-than nil (notless pivot ls))
={Def all-less-than}
t

3. (implies (and (rationalp pivot) 
                 (lorp ls) 
                 (not (endp ls))
                 (less-than-all (first ls) (notless pivot ls))
                 (L2 | ((ls (rest ls)))))
            L2)
C1: (rationalp pivot)
C2: (lorp ls)
C3: (not (endp ls))
C4: (less-than-all (first ls) (notless pivot ls))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (all-less-than (less pivot (rest ls)) 
                            (notless pivot (rest ls))))
----------------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C7: (all-less-than (less pivot (rest ls)) 
                   (notless pivot (rest ls))) {MP, C5, C1, C6}

(implies (and (rationalp pivot)
              (lorp ls))
         (all-less-than (less pivot ls) 
                        (notless pivot ls)))
={C1, C2}  
(all-less-than (less pivot ls) (notless pivot ls))
TODO: Case analysis on ls.

L3: (implies (and (lorp l1) 
                  (lorp l2)
                  (orderedp l1)
                  (orderedp l2)
                  (all-less-than l1 l2))
             (orderedp (app l1 l2)))      


Final proof for Q2:

(implies (lorp x)
         (orderedp (qsort x)))

1. (implies (endp x) Q2)

C1: (endp x)
------------

(implies (lorp x) (orderedp (qsort x)))
= {MP, C1}
(orderedp (qsort nil))
= {Def qsort}
(orderedp ())
= {Def orderedp}
t

2. (implies (and (lorp x) 
                 (consp x)
                 (Q2 | (x ((less (first x) (rest x)))))
                 (Q2 | (x ((notless (first x) (rest x))))))
            Q2)

C1: (lorp x)
C2: (consp x)
C3: (Q2 | (x ((less (first x) (rest x)))))
C4: (Q2 | (x ((notless (first x) (rest x)))))
-------------
C5: (lorp (rest x)) {Def lorp, C1, C2}
C6: (rationalp (first x)) {Def lorp, C1, C2}
C7: (lorp (less (first x) (rest x))) {Contract thm less, C6, C5}
C8: (lorp (notless (first x) (rest x))) {Contract thm notless, C6, C5}
C9: (orderedp (qsort (less (first x) (rest x)))) {MP, C3, C7}
C10: (orderedp (qsort (notless (first x) (rest x)))) {MP, C4, C8}
C11: (less-than-all (first x) (notless (first x) (rest x))) {L0, C6, C8}
C12: (greater-than-all (first x) (notless (first x) (rest x))) {L1, C6, C7}
C13: (


(implies (lorp x) (orderedp (qsort x)))
={MP, C1}
(orderedp (qsort x))
={Def qsort, C2}
(orderedp (append (qsort (less (first x) (rest x)))
                  (append (list (first x))
                          (qsort (notless (first x) (rest x))))))
={}
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Q3
(implies (and (lorp x) (lorp y) (perm x y))
         (equal (len x) (len y)))
;; This will be proven using the induction scheme of perm.

Proof obligations:

1. (implies (or (not (lorp x)) (not (lorp y)) (not (perm x y))) Q3)

; Q4
(implies (lorp x)
         (perm x x))

...

; Q5
(implies (and (lorp x) (lorp y) (perm x y))
         (perm y x))

...

; Q6
(implies (and (lorp x) (lorp y) (lorp z) (perm x y) (perm y z))
         (perm x z))

...

; Q7
(implies (lorp x)
         (perm (isort x) x))

...

; Q8
(implies (lorp x)
         (perm (qsort x) x))

...

; Q9 (extra credit)
(implies (lorp x)
         (equal (qsort x) (isort x)))
|#
; ...

#|

Extra credit:

Define a function, induction-scheme, that given a defunc function
definition and a conjecture as input generates the induction scheme
corresponding to the function definition and the conjecture.  You have
a lot of flexibility in how to go about doing this. This is on
purpose, so that you can identify and resolve the issues that come up
on your own.

Here is an example.

(induction-scheme
 '(defunc app (x y)
    :input-contract (and (listp x) (listp y))
    :output-contract (listp (app x y))
    (if (endp x)
        y
      (cons (first x) (app (rest x) y))))
 '(implies (and (listp x) (listp y) (listp z))
           (equal (app (app x y)) (app x (app y z)))))

should return something equivalent to:

(and 
 (implies (not (and (listp x) (listp y)))
          (implies (and (listp x) (listp y) (listp z))
                   (equal (app (app x y)) (app x (app y z)))))
 (implies (and (listp x) (listp y) (endp x)) 
          (implies (and (listp x) (listp y) (listp z))
                   (equal (app (app x y)) (app x (app y z)))))
 (implies (and (listp x) (listp y) (not (endp x)) 
               (implies (and (listp (rest x)) (listp y) (listp z))
                        (equal (app (app (rest x) y)) 
                               (app (rest x) (app y z)))))
          (implies (and (listp x) (listp y) (listp z))
                   (equal (app (app x y)) (app x (app y z))))))

The exact syntax is not important and it is OK for you to require that
cond is used instead of if, etc. Also, you don't have to worry about
whether the argument to induction-scheme corresponds to a terminating
function. You can assume that the function definition is admissible
and that the conjecture is well-formed.

I recommend that everyone at least try this because the attempt will
help you better understand induction.

|#

; ....

