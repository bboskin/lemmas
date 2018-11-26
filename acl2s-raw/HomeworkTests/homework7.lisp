(defttag t)
(include-book "top" :uncertified-okp t)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; no-dupes: list -> boolean
;; (no-dupes l) takes a list l and returns true
;; iff there are no duplicate elements in l

(defunc2 in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(defunc2 no-dupes (l)
  :input-contract (true-listp l)
  :output-contract (booleanp (no-dupes l))
  (or (endp l) 
      (and (not (in (car l) (cdr l)))
           (no-dupes (cdr l)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; num-unique: list -> natp
;; (num-unique l) takes a list and returns the number
;; of unique elements in it.
(defunc2 num-unique (l)
  :input-contract (true-listp l)
  :output-contract (natp (num-unique l))
  (cond ((endp l) 0)
        ((in (car l) (cdr l))
         (num-unique (cdr l)))
        (t (+ 1 (num-unique (cdr l))))))

#|
Prove the following conjectures are valid. 

1a) 

(implies (listp l)
         (implies (or (endp l)
                      (and (not (endp l))
                           (in (first l) (rest l))
                           (implies (listp (rest l))
                                    (<= (num-unique (rest l))
                                        (len (rest l)))))
                      (and (not (endp l))
                           (not (in (first l) (rest l)))
                           (implies (listp (rest l))
                                    (<= (num-unique (rest l))
                                        (len (rest l))))))
                  (<= (num-unique l)
                      (len l))))

EXPORTATION:
|#

(suggest-lemma (<= (num-unique l)
		   (len l))
	       :with all-lines
	       :hyps (true-listp l)
	       (or (endp l)
		   (and (not (endp l))
			(in (first l) (rest l))
			(implies (listp (rest l))
				 (<= (num-unique (rest l))
				     (len (rest l)))))
		   (and (not (endp l))
			(not (in (first l) (rest l)))
			(implies (listp (rest l))
				 (<= (num-unique (rest l))
				     (len (rest l)))))))

(thm
 (IMPLIES (AND (TRUE-LISTP L)
              (RATIONALP (NUM-UNIQUE L))
              (TRUE-LISTP L)
              (OR (ENDP L)
                  (AND (NOT (ENDP L))
                       (IN (FIRST L) (REST L))
                       (IMPLIES (LISTP (REST L))
                                (<= (NUM-UNIQUE (REST L))
                                    (LEN (REST L)))))
                  (AND (NOT (ENDP L))
                       (NOT (IN (FIRST L) (REST L)))
                       (IMPLIES (LISTP (REST L))
                                (<= (NUM-UNIQUE (REST L))
                                    (LEN (REST L)))))))
         (EQUAL (<= (NUM-UNIQUE L) (LEN L)) T)))
          
#|
PROOF:

C1: (listp l)
C2: (or (endp l)
        (and (not (endp l))
             (in (first l) (rest l))
             (implies (listp (rest l))
                      (<= (num-unique (rest l))
                          (len (rest l)))))
        (and (not (endp l))
             (not (in (first l) (rest l)))
             (implies (listp (rest l))
                      (<= (num-unique (rest l))
                          (len (rest l))))))
------------


(<= (num-unique l) (len l))
= {Def num-unique, C1}
(<= (cond ((endp l) 0)
        ((in (first l) (rest l))
         (num-unique (rest l)))
        (t (+ 1 (num-unique (rest l)))))
    (len l))
= {Case analysis, C2}
(implies (endp l)
         (<= 0 (len l)))                                 <-- Case 1
^
(implies (and (not (endp l))
              (in (first l) (rest l)))
         (implies (listp (rest l))
                  (<= (num-unique (rest l)) (len l))))     
                                                         <-- Case 2
^ 
(implies (and (not endp l)
              (not (in (first l) (rest l))))
         (implies (listp (rest l))
              (<= (num-unique (rest l)) (len l))))       <-- Case 3

Case 1:

--------
C3. (endp x)

(<= 0 (len l))
= {Def len, C3}
(<= 0 0)
= {Def <=}
t

Case 2:

------------
C3. (not (endp l)) {Case/C2}
C4. (in (first l) (rest l)) {Case/C2}
C5. (implies (listp (rest l)) (<= (num-unique (rest l)) (len (rest l)))) {C2}
C6. (listp (rest l))  {Def list, C1, C3}
C7. (<= (num-unique (rest l)) (len (rest l))) {MP C5, C6}


(<= (num-unique (rest l)) (len l))
= {C3, cons axiom}
(<= (num-unique (rest l)) (len (cons (first l) (rest l)))
= {Def len}
(<= (num-unique (rest l)) (+ 1 (len (rest l))))
= {Arith, C7}
t


Case 3:
------------
C3. (not (endp l)) {case/C2}
C4. (not (in (first l) (rest l))) {case/C2}
C5. (implies (listp (rest l)) (<= (num-unique (rest l)) (len (rest l)))) {C2}
C6. (listp (rest l))  {Def list, C1, C3}
C7. (<= (num-unique (rest l)) (len (rest l))) {MP C5, C6}

(<= (num-unique (rest l)) (len l))
= {C3, cons axiom}
(<= (1 + (num-unique (rest l))) (len (cons (first l) (rest l)))
= {Def len}
(<= (1 + (num-unique (rest l))) (+ 1 (len (rest l))))
= {Arith, C7}
t

1b) 

(implies (and (listp l)
              (no-dupes l)) 
         (and (implies (endp l)
                       (equal (num-unique l) (len l)))
              (implies (and (not (endp l))
                            (implies (and (listp (rest l))
                                          (no-dupes (rest l)))
                                     (equal (num-unique (rest l))
                                            (len (rest l)))))
                       (equal (num-unique l)
                              (len l)))))
EXPORTATION:
|#

(suggest-lemma (num-unique l)
	       :with no-dupes len
	       :hyps (listp l) (no-dupes l)
	       (or (endp l)
		   (and (not (endp l))
			(listp (rest l))
			(no-dupes (rest l))
			(equal (num-unique (rest l))
			       (len (rest l))))))

(thm (IMPLIES (AND (TRUE-LISTP L)
              (LISTP L)
              (NO-DUPES L)
              (OR (ENDP L)
                  (AND (NOT (ENDP L))
                       (LISTP (REST L))
                       (NO-DUPES (REST L))
                       (EQUAL (NUM-UNIQUE (REST L))
                              (LEN (REST L))))))
         (EQUAL (NUM-UNIQUE L) (LEN L))))
              
#|
PROOF:

C1: (listp l)
C2: (no-dupes l)
C3: (implies (or (endp l)
                 (and (not (endp l))
                      (listp (rest l))
                      (no-dupes (rest l))
                      (equal (num-unique (rest l))
                             (len (rest l)))))
              (equal (num-unique l) (len l)))
----------------

(equal (num-unique l) (len l))
= {Case C3}

Case 1:
------------
C4: (endp l) {C3}

(equal (num-unique l) (len l))
= {Def num-unique, C4}
(equal 0 (len l))
= {Def len, C4}
(equal 0 0)
= {equal axiom}
t

Case 2:
-----------------
C4: (not (endp l)) {C3}
C5: (listp (rest l)) {C3}
C6: (no-dupes (rest l)) {C3}
C7: (equal (num-unique (rest l))
           (len (rest l))) {C3}

(equal (num-unique l) (len l))
= {C4}
(equal (num-unique (cons (first l) (rest l)))
       (len (cons (first l) (rest l))))
= {Def num-unique, C5}
(equal (+ 1 (num-unique (rest l)))
       (len (cons (first l) (rest l))))
= {Def len, C5}
(equal (+ 1 (num-unique (rest l)))
       (+ 1 (len (rest l))))
= {C7}
(equal (+ 1 (len (rest l))) (+ 1 (len (rest l))))
= {equal axiom}
t




DEFINITIONAL PRINCIPLE

For each definition below, check whether it is admissible, i.e., it
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

If you claim admissibility, BRIEFLY

1. Explain in English why the body contracts hold.
2. Explain in English why the contract theorem holds.
3. Explain in English why the function terminates.

Otherwise, identify a rule in the Definitional Principle that is violated.

If you blame one of the purely syntactic rules (variable names,
non-wellformed body etc), explain the violation in English.

If you blame one of the semantic rules (body contract, contract theorem or
termination), you must provide an input that satisfies the input contract, but
causes a violation in the body or violates the output contract or causes
non-termination.

Remember that the rules are not independent: if you claim the function does
not terminate, you must provide an input on which the function runs forever
*without* causing a body contract violation: a body contract violation is
not a counterexample to termination. Similarly, if you claim the function
fails the contract theorem, you must provide an input on which it
terminates and produces a value, which then violates the output contract.

Your explanations should be brief but clear. We are not looking for a page 
of text per question but we also want to clearly see that you understand 
the function and if/what is wrong with it.

Note that there is a difference between a function being admissible,
as per the definitional principle, and ACL2s automatically proving
that it is admissible.  That is, there are many functions that are
admissible, but ACL2s will not admit them without help from the user,
so don't just try ACL2s and report what it reports.

2a)

(defunc fa (x)
  :input-contract (natp x)
  :output-contract (posp (fa x))
  (if (equal x 0)
    0
    (fa (- x 1))))
    
NOT ADMISSIBLE!

0 will satisfy the input contract, but break 
the output contract, since 0 (the output) is not a pos

2b)

(defunc fb (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (and (listp (fb x y)) (equal (len (fb x y)) 1))
  (if (equal y 0)
    (list y)
    (fb (cons (first x) x) (- y 1))))

NOT ADMISSIBLE!

when x is nil, it has no first.

Counterexample: x = nil, y = 2

|#

#|
2c)
|#
(defunc2 fc (x)
  :input-contract (posp x)
  :output-contract (integerp (fc x))
  (if (<= x 21)
      (- x 121)
    (- 1 (fc (- x 1)))))

#|

ADMISSIBLE:

body contracts:
 if we get to the else branch, then we know that x > 21, in which case x-1 is still a pos.
 Other x-1 this function just does recursion, and is fine.

contract thm
 If is a pos and x<=21, then x-121 is an integer. 
 Also, the -1 in tail position will not make a valid output no loger valid. Everything checks out.

termination:
 The base case is when x < 21. Since x is always decremented, 
 we know that eventually x will be <= to 21, given that it was initially a pos.
 So, we will arrive at the base case and terminate for all pos x.
 
2d)

(defunc fd (a b)
  :input-contract  (and (posp a) (posp b))
  :output-contract (posp (fd a b))
  (cond ((or (equal a 1) (equal b 1))
         1)
        ((< a b)
         (fd (- a 1) (- b 1)))
        (t
         (fd b a))))

NOT ADMISSIBLE:

It will not always terminate. 
example: a=2, b=2


2e)

(defunc fe (i)
  :input-contract (integerp i)
  :output-contract (integerp (fe i))
  (if (< i -11)
      i
    (fe (- fe i))))

NOT ADMISSIBLE! fe occurs free in the body in a non-function position


2f)

(defunc ff (i)
  :input-contract (integerp i)
  :output-contract (integerp (ff i))
  (if (< i 100)
      (- i 20)
    (ff (ff (+ i 21)))))

NOT ADMISSIBLE! it won't terminate. 

example of input that will cause it to infinite loop: i=100

2g)
|#
(defunc2 fg (x y)
  :input-contract (and (natp x) (posp y))
  :output-contract (natp (fg x y))
  (cond ((equal x 0) x)
        ((equal y 1) y)
        ((> x y) (fg y x))
        (t (fg x (- y 1)))))#|ACL2s-ToDo-Line|#

#|
ADMISSIBLE!
body contracts: 
 for the base cases, it's fine. 
 for the (< x y) case, it's also fine -- since x>=1 and y >1, (fg y x) is perfectly fine
 and for the last case, since y>1, this recursion is also fine
 
contract thm.
 the two base cases both return nats (0 and 1), and other than that it's just the recursion.
 tail recursion helps make it clear to see

termination. 
 This will terminate! the larger value (between x and y) is always the one decremented in 
 the last case, which means that they will both approach their respective base cases together.
 
 

2h)

(defunc fh (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (natp (fh x y))
  (cond ((endp x) 0)
        ((equal y 0) (len x))
        (t (fh (list x y) (len (rest x))))))

NOT ADMISSIBLE! This will not terminate:

Example inputs that cause it to fail
x = (list 4 3)
y = 2



2i)

(defunc fi (x y z)
  :input-contract (and (rationalp x) (rationalp y) (rationalp z) (< 0 z))
  :output-contract (rationalp (fi x y z))
  (if (>= x 0)
      (* x y)
    (+ (/ x y) (fi (+ x z) (- y 1) z))))

NOT ADMISSIBLE!

counterexample:
x= -3
y = 0
z = 1


2j)

(defunc fj (x y z)
  :input-contract (and (rationalp x) (rationalp y) (rationalp z) (< 0 z))
  :output-contract (rationalp (fj x y z))
  (if (>= x 0)
      (* x y)
    (+ (* x y) (fj (+ x z) (- y 1) z))))

ADMISSIBLE

body contracts: everything is a rational, and is fine (fj only occurs as a function symbol)

contract thm: 
 (* x y) can only make rationals, when x and y are rationals, so base case is OK
 (+ (* x y) *recursion*) is ok, since + can only make rationals from rationals.
 (+ x z), (- y 1) are both rationals as well, assuming x, y, and z are rationals

termination:
this will terminate (even though ACL2s says no)
since z > 0, (+ x z) > x, and since x needs to be > 0 for the function to terminate, 
this will definitely eventually happen if it is initially negative. x always grows.


2k)

(defunc fk (x y x)
  :input-contract (and (natp x) (listp y) (natp x))
  :output-contract (posp (fk x y x))
  (if (endp y)
    0
    (fk x (rest y) x)))
 
NOT ADMISSIBLE -- duplicate identifier (x) in argument list


2l)

(defunc fl (x y)
  :input-contract (and (listp x) (listp y))
  :output-contract (listp (fl x y))
  (if (endp y)
      x
    (fl (rest x) y)))

NOT ADMISSIBLE: problematic call with (rest x) in else branch.
counterexample: x=nil, y= (cons 1 nil)

2m)

(defunc fm (x)
  :input-contract (natp x)
  :output-contract (integerp (fm x))
  (if (equal x 0)
      12
    (fm (- 21 (fm (- x 1))))))

NOT ADMISSIBLE -- won't always terminate (in fact, will never terminate unless x=0 initially):
counterexample: x=1
|#
