#|

PART 1: SUBSTITUTIONS

Question 1.

Below you are given a set of ACL2s terms and substitutions. Recall
that a substitution is a list of pairs, where the first element of
each pair is a variable and the second is an expression. Also,
variables can appear only once as a left element of a pair in any
substitution. For example, the substitution ((y (cons a b)) (x m))
maps y to (cons a b) and x to m. 

For each term/substitution pair below, show what you get when you
apply the substitution to the term. If the substitution is not
well-formed (it does not satisfy the definition of a substitution),
indicate why.  If the substituion is well-formed you have to do is to
apply the substitution, so do not do anything else, e.g., do not
evaluate the expression you obtain after applying the substitution.

Example:
 (f (bar x y) 'f f)
|((x (list 3)) (bar zap) (y (cons 'l nil)) (f (+ 1 2)))

Answer:
 (f (bar (list 3) (cons 'l nil)) 'f (+ 1 2))

In class we wrote this as 

(f (bar x y) 'f f)|((x (list 3)) (bar zap) (y (cons 'l nil)) (f (+ 1 2)))

but the two line format will make it easier for you to read.  

Notice that we only substitute an occurrence of a symbol that
corresponds to a variable, which is why the occurrence of f in
function position (f ...) was not changed.  On the other hand the last
occurrence of in (f ... f) is a variable and was replaced by its
target in the substitution. Finally, 'f is *not* a variable. It is a
constant and it is not affected by any substitution. Replace
the "..."'s below with your answers.

1a. (foo foo 'foo)|
    ((foo (list a b)))
    
(foo (list a b) 'foo)

1b. (foo foo 'foo)|
    ((foo (list a b)) ('foo foo))

This substitution is not well-formed -- 'foo should not occur on the LHS

1c. (f (g x y) (h y x))|
    ((y x) (x (f (g y x))) (f g) (h f))

f (g (f (g y x)) x) (h x (f (g y x))))


1d. (* (* (len (app x y)) (len '(app x y))) (/ a b))|
    ((a 43) (b (* c d)) (y (app x z)) (x x))

    (* (* (len (app x (app x z))) (len '(app x y))) (/ 43 (* c d)))

1e. (list (app x y) z)|
    ((x (list y)) (y (list x)) (x (list z)))
    
    This substitution is not well-formed -- x has two associated terms.
   
Question 2.

For each pair of ACL2 terms, give a substitution that instantiates the 
first to the second. If no substitution exists write "None".

Example:
  (app x y)
  (app (list a x) nil)
  
  ((x (list a x)) (y nil))

Answer:
  ((x (list a x)) (y nil))

a. (app x y)
   (list x y)
   None

b. (foo y (app x y))
   (foo x y)
   None

c. (foo x y)
   (foo y (app x y))
   
   ((x y) (y (app x y)))

d. (foo (< (bar a b) (baz bar a)) (if if foo baz))
   (foo (< (bar (if bar baz foo) (baz 'a 'b)) (baz bar (if bar baz foo))) (if foo bar foo))
   
   ((a (if bar baz fo)) (b (baz 'a 'b)) (bar bar) (if foo) (foo bar) (baz foo))

e. (foo (< (bar a b) (baz 'a a)) (if a foo baz))
   (foo (< (bar (if nil bar foo) (baz 'a 'b)) (baz bar (if bar baz foo))) (if foo bar foo))
   
   None

|#


#|

PART II: EQUATIONAL REASONING

The questions in this part ask for equational proofs about ACL2s
programs. Below you are given a set of function definitions you can
use.  Note in many cases the name has been slightly changed so you
can't simply use a theorem from class (ex. in2 instead of in).

The definitional axioms and contract theorems for defined functions
can be used in your proofs.

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
theorem or lemma and then *show the substitution* you are using for
any definitional axiom, or theorem IF a substitution actually
occurs (no need to write (n n) for example).  Ex. Using the
definitional axiom for app to conclude (app2 nil l) = l you would
write {Def. app2|((x nil)(y l)), if axioms}. After this homework, we
will not require you to do this.

5. When using the definitional axiom of a function, the justification
should say "Def. <function-name>".  When using the contract theorem of
a function, the justification should say
"Contract <function-name>".

6. Arithmetic facts such as commutativity of addition can be used. The
name for such facts is "arithmetic".

7. You can refer to the axioms for cons, and consp as the "cons axioms", 
Axioms for first and rest can be referred to as "first-rest axioms".
The axioms for if are named "if axioms"

8. Any propositional reasoning used can be justified by "propositional
reasoning", "Prop logic", or "PL" except you should use "MP" to
explicitly identify when you use modus ponens.

9. For this homework, you can only use theorems we explicitly tell you
you can use or we have covered in class / lab.  You can, of course,
use the definitional axiom and contract theorem for any function used
or defined in this homework. You may also use theorems you've proven
earlier in the homework.  Here are the definitions used for the
remainder of the questions.

10. For any given propositional expression, feel free to re-write it
in infix notation (ex a => (B ^ C)).

;;; Function Definitions

(defunc listp (l)
  :input-contract t
  :output-contract (booleanp (listp l))
  (if (consp l)
      (listp (rest l))
    (equal l () )))

(defunc endp (l)
  :input-contract (listp l)
  :output-contract (booleanp (endp l))
  (not (consp l)))
|#

(defttag t)
(include-book "top" :uncertified-okp t)

(defunc2 len2 (x)
     :input-contract (true-listp x)
     :output-contract (natp (len2 x))
     (if (endp x)
	 0
       (+ 1 (len2 (cdr x)))))

(defunc2 in2 (a l)
  :input-contract (true-listp l)
  :output-contract (booleanp (in2 a l))
  (if (endp l)
      nil
    (or (equal a (car l)) (in2 a (cdr l)))))
    
(defunc2 app2 (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (app2 x y))
  (if (endp x)
      y
    (cons (car x) (app2 (cdr x) y))))
#|
;;; Instructions

For each of the conjectures below:

1. Perform conjecture contract checking, and add hypotheses if
   necessary. Contract completion is the process of adding the minimal
   set of hypotheses needed to guarantee that the input contracts for
   all functions used in the conjecture are satisfied. This is exactly
   what we did with test? and in class. See the lecture notes. Do not
   add anything else to the conjecture.

2. Determine if the resulting conjecture is valid or not.  If it is
   valid, provide a proof. If it is invalid, provide a
   counterexample. Make sure to follow the above instructions when
   giving proofs.


;; Question 2a.

(implies (endp x)
         (equal (len2 (app2 x (app2 y z)))
                (len2 (app2 (app2 x y) z))))

CONTRACT CHECKING:
|#

(defgroup list-ops len2 app2 cons car cdr)

(suggest-lemma (len2 (app2 x (app2 y z)))
	       :required-expressions len2 (app2 x y) z
	       :with list-ops
	       :complete-hyps nil
	       :hyps (true-listp x) (true-listp y) (true-listp z))


(thm (IMPLIES (AND (TRUE-LISTP Y)
              (TRUE-LISTP (APP2 X (APP2 Y Z)))
              (TRUE-LISTP X)
              (TRUE-LISTP Z)
              (TRUE-LISTP (APP2 Y Z)))
         (EQUAL (LEN2 (APP2 X (APP2 Y Z)))
                (LEN2 (APP2 (APP2 X Y) Z)))))

#|
(equal (len2 (app2 x (app2 y z)))
       (len2 (app2 (app2 x y) z)))
= {Def app2, C2}
(equal (len2 (app2 y z))
       (len2 (app2 y z)))
= {equal axiom}
t

;; Question 2b.

(implies (and (consp x)
              (implies (and (listp (rest x))
                            (listp y)
                            (listp z))
                       (equal (len2 (app2 (rest x) (app2 y z)))
                              (len2 (app2 (app2 (rest x) y) z)))))
         (equal (len2 (app2 x (app2 y z)))
                (len2 (app2 (app2 x y) z))))
CONTRACT CHECKING
|#


(thm (implies (and (consp x)
                   (listp (rest x))
                   (listp y)
                   (listp z)
                   (equal (len2 (app2 (rest x) (app2 y z)))
                          (len2 (app2 (app2 (rest x) y) z))))
              (equal (len2 (app2 x (app2 y z)))
                     (len2 (app2 (app2 x y) z)))))
#|
PROOF:

C1: (consp x)
C2: (listp (rest x))
C3: (listp y)
C4: (listp z)
C5: (equal (len2 (app2 (rest x) (app2 y z)))
           (len2 (app2 (app2 (rest x) y) z)))
-----------------
C6: (listp (app2 (rest x) (app2 y z))) {Contract app2, C2, C3, C4}

(equal (len2 (app2 x (app2 y z)))
       (len2 (app2 (app2 x y) z)))
= {Def app2, C1, C2}
(equal (len2 (cons (first x) (app2 (rest x) (app2 y z)))
       (len2 (app2 (app2 x y) z)))
= {Def len2}
(equal (+ 1 (len2 (app2 (rest x) (app2 y z)))
       (len2 (app2 (app2 x y) z)))
= {cons axiom, C1}
(equal (+ 1 (len2 (app2 (rest x) (app2 y z))))
       (len2 (app2 (app2 (cons (first x) (rest x)) y) z))))
= {def app2, C2}
(equal (+ 1 (len2 (app2 (rest x) (app2 y z))))
       (len2 (app2 (cons (first x) (app2 (rest x) y) z))))
= {def len2}       
       
;; Question 2c.

(implies (and (in2 a x) (in2 a y))
         (equal x y))
...

;; Question 2d.

(implies (equal x y)
         (equal (in2 a x) (in2 a y)))
...
|#
(suggest-lemma (in2 a x)
	       :with in2 app2 equal cons
	       :hyps (true-listp x) (true-listp y) (equal x y))

(thm (IMPLIES (AND (TRUE-LISTP X)
              (TRUE-LISTP X)
              (TRUE-LISTP Y)
              (EQUAL X Y))
         (EQUAL (IN2 A X) (IN2 A Y))))
#|

;; Question 2e.

(implies (endp x)
         (implies (in2 a (app2 x y))
                  (or (in2 a x) (in2 a y))))
|#
(suggest-lemma t
	       :required-expressions or (in2 a x)
	       :with list-ops
	       :hyps (in2 a (app2 x y)) (true-listp x) (true-listp y))

(thm (IMPLIES (AND (IN2 A (APP2 X Y))
              (TRUE-LISTP X)
              (TRUE-LISTP Y))
         (EQUAL T (OR (IN2 A X) (IN2 A Y)))))
#|

;; Question 2f.

(implies (and (consp x)
              (implies (and (listp (rest x))
                            (listp y))
                       (implies (in2 a (app2 (rest x) y))
                                (or (in2 a (rest x)) (in2 a y)))))
         (implies (in2 a (app2 x y))
                  (or (in2 a x) (in2 a y))))
...

;; Question 2g.

(implies (equal z (app2 x y))
         (implies (not (in2 a x))
                  (not (in2 a z))))
...


|#

#|

PART III: 

Fault tree analysis was created at Bell Labs in the 1960s for
analyzing system failures. It is used in numerous industries where
system failures can be extremely costly.

Fault tree analysis is used in the design of nuclear plants, in the
design of airplanes and to analyze the security of cyber-systems.
Consider a nuclear power plant: it consists of many different
components. What if one of them, say a temperature sensor, failed? If
that single failure can cause a catastrophic event, that would be a
bad design. So, how can we convince ourselves, and the government
agency that certifies the design, that this one failure does not lead
to a catastrophic event, and more generally, that the probability of a
catastrophic event is low enough for the system to be considered safe?
That's what fault tree analysis lets us do.

NASA uses fault tree analysis to predict the likelihood of mechanical
failures during a mission. The Nuclear Regulation Commission adopted
the use of fault trees after the incident at Three Mile Island. Attack
trees, a variant of fault trees, are used to analyze the security of
computer systems.

How do we construct a fault tree? First, we define basic events.  You
can think of basic events as component failures (e.g., the failure of
a sensor). The fault tree is a Boolean formula, using only & and
! (conjunction and disjunction) whose variables are the basic
events. The formula (tree) is used to model the conditions under which
the fault we care about (say a nuclear power plan meltdown) can occur
based on whether the basic events (component failures) have occurred.

Once we have a fault tree, there are various analyses we can
perform. One of the most important is cutset generation.  Given a
fault tree, a cutset is a set of basic event whose simultaneous
occurrence leads to the fault we are analyzing. We also require that
no proper subset of events is a cutset, i.e., cutsets should be
minimal. The cutsets of a fault tree is the set consisting of all the
tree's cutsets. Cutsets make clear exactly what needs to go wrong at
the component level for a system-level fault to happen.  How do we
generate cutsets? Well, they correspond to the minimal Disjunctive
Normal Form (DNF) of the fault tree! See section 3.5 of the course
lecture notes for a discussion about DNF.

Consider some examples.

Example 1:  Let's take the following formula

T1 = (A ! (B ! C)) & ((C ! A) & (C ! B)) 

where T1 models the following fault: the plane's landing gear
does not deploy correctly. The basic events are:

A = Landing gear door stuck
B = Mechanical failure of landing gear (reducing power)
C = Electronic short to gears

The cutsets for T1 are

C
A,B

because if C occurs (a short) then T1 occurs (landing gear does not
deploy). Also if A and B occur then T1 occurs. Finally, there is no
other way for T1 to occur that does not include one of the above
cutsets.  The cutsets are easier to understand than the tree. What
does this have to do with minimal DNF? Well as a formula, the cutsets
are:

C ! (A & B)

which is the minimal DNF for T1!
 
Example 2: Let's look at another example
T2 = (A ! B) & (A ! C) & (D ! B) & (D ! C)

T2: No flow to pad deluge nozzles 

A = Valve fails to close
B = Pump 1 fails
C = Pump 2 fails
D = No flow to pipe P
 
The minimal DNF is:
(A & D) ! (B & C)
  
Example 3: Pressure Tank Example

From the US Nuclear Regulatory Commission Handbook, Section VIII.
Imagine we are reasoning about a pressure regulator for a nuclear
reactor and we define the following variables to describe the ways the
regulator can fail (similar to the accident at the Three Mile Island
nuclear power plant):

    R = primary failure of timer relay
    S = primary failure of pressure switch
    S1 = primary failure of switch S1
    K1 = primary failure of relay K1
    K2 = primary failure of relay K2
    T1 = primary failure of pressure tank

Let E1 be the top event. We then have the following sets of equations.
E1 = T1 ! E2
E2 = E3 ! K2
E3 = S & E4
E4 = S1 ! E5
E5 = K1 ! R

Expanded: E1 = T1 ! (S & (S1 ! K1 ! R)) ! K2

The minimal DNF is:
  T1 ! (S & S1) ! (S & K1) ! (S & R) ! K2

Fault tree analysis also involves assigning probabilities to basic
events. These probabilities, along with the cutsets, are used to
determine the probability of the failure being modeled by the tree. We
will not concern ourselves with probabilities for this assignment.

For further references, see 
- https://en.wikipedia.org/wiki/Fault_tree_analysis
- The NASA Fault Tree Handbook
- https://www.schneier.com/academic/archives/1999/12/attack_trees.html 

We will develop an algorithm for generating cutsets and we will
use it to analyze a fault tree from the U.S. Nuclear Regulatory
Commission's Fault Tree Handbook. The fault tree is on page XI-3
(pg 169) and it is a fault tree for a pressure tank.  The example
includes a pressure tank, a pump-motor device and a control system
which regulates the operation of the pump, which pumps fluid from a
reservoir into the tank. When the tank is pressurized, a pressure
switch opens, deenergizing a coil, which leads to power being removed
from the pump. There is an emergency backup consisting of a timer that
starts when power is applied to the pump and which deenergized a relay
coil if power is maintained for more than 60 seconds, which is the
amount of time needed to pressurize the tank. The failure that the
fault tree captures is a tank rupture. Your final test of your
algorithm will be to determine if your algorithm generates the
same cutsets for this fault tree as those provided by the
Handbook.

The algorithm we will implement is the MOCUS (Method for Obtaining
Cut Sets) algorithm.

We explain it using an example, which is adapted from the Book "System
Reliability Theory, Models, Statistical Methods, and Applications",
2nd Edition by Shewhart and Wilks.

We use the following symbols to represent the Boolean connectives and
and or (we routinely change the symbols used to get you used to seeing
different notations).

  AND     &
  OR      !

Consider the following fault tree:

((E1 ! (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8)))) ! E2)

We want to determine the cutsets of the fault tree (formula).  This
will tell us all the ways in which the simultaneous occurrence of
basic events can lead to the fault we are analyzing. This will allows
to determine whether the failure of any individual component can lead
to a system failure.

The algorithm is going to operate on two lists.

The first is a list whose elements are lists of formulas.  This list
contains formulas we need to process.

The second list contains a list of atoms (basic events). Each list of
atoms corresponds to a conjunction of events that have to be
simultaneously true in order for the fault to occur.

The algorithm starts with the first list containing only one element,
a list containing the original formula. The second list is 
initially empty.

(
( ((E1 ! (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8)))) ! E2) )
)

(
)

The algorithm looks at the first list and selects the first element of
this list, which is also a list. Finally, it looks at the first
element of this. In our example, this is the original fault
tree (formula). Since it is an or, it is replaced by two lists, one
for each argument of the or. The intuition here is that each element
of the final list we return is going to correspond to a DNF formula,
so each element of the list corresponds to a conjunctive clause
(see Section 3.5 of the lecture notes).  So what the list below tells
us is that the fault can occur if any of the formulas in the list are
true.

(
( (E1 ! (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8)))) )
( E2 )
)

(
)

The algorithm will continue processing formulas until only basic
events (atoms) are left. The first element of the first element of the
first list is again an or, so we break it up into its arguments,
yielding the following lists.

(
( E1 )
( (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8))) )
( E2 )
)

(
)

Now, the first element of the first element of the first list has no
connectives, so there is nothing to do, because it corresponds to a
conjuction of atoms, and we transfer it to the second list to get the
following.

(
( (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8))) )
( E2 )
)

(
( E1 )
)

The first element of the first element of the first list is again an
or, so we break it up into its arguments, yielding the following list.

(
( ((E4 & E5) & (E6 ! E7)) )
( (E3 ! (E6 ! E8)) )
( E2 )
)

(
( E1 )
)

Now, the first element of the first element of the first list is an
and. When we see an and, we create a list of the arguments to the and
because both have to be true for the fault to occur.  We now have the
following, which shows why the first list is a list of formulas. Note
that no further nesting of lists is possible.

(
( (E4 & E5) (E6 ! E7) )
( (E3 ! (E6 ! E8)) )
( E2 )
)

(
( E1 )
)

Next, the first element of the first element of the first list is
again an and, which means that both arguments must be true,
so we generate the following.

(
( E4 E5 (E6 ! E7) )
( (E3 ! (E6 ! E8)) )
( E2 )
)

(
( E1 )
)

Now, something new happens. The first element of the first element of
the first list is an atom, i.e., a basic event, so we traverse the
list until we find a formula that contains an operator. We'll see what
happens if there is no such formula later. The first such formula is
the third element of the list and it is an or.  So, intuitively, for
the first element of the first list to be true, E4 and E5 have to be
true and one of E6 or E7 have to be true, so we wind up splitting the
list into two lists as follows.

(
( E4 E5 E6 )
( E4 E5 E7 )
( (E3 ! (E6 ! E8)) )
( E2 )
)

(
( E1 )
)

Next, the first element of the first element of the first list
is just a list of vars, or basic events, so it gets added
to the second list, giving us the following.

(
( E4 E5 E7 )
( (E3 ! (E6 ! E8)) )
( E2 )
)

(
( E4 E5 E6 )
( E1 )
)

Similarly, next we get the following.

(
( (E3 ! (E6 ! E8)) )
( E2 )
)

(
( E4 E5 E7 )
( E4 E5 E6 )
( E1 )
)

We have an or next, so we get the following.

(
( E3 )
( (E6 ! E8) )
( E2 )
)

(
( E4 E5 E7 )
( E4 E5 E6 )
( E1 )
)

We have a list of atoms, we get the following.

(
( (E6 ! E8) )
( E2 )
)

(
( E3 )
( E4 E5 E7 )
( E4 E5 E6 )
( E1 )
)

We have an or next, so we get the following.

(
( E6 )
( E8 )
( E2 )
)

(
( E3 )
( E4 E5 E7 )
( E4 E5 E6 )
( E1 )
)

We have a list of atoms, we we get the following.

(
( E8 )
( E2 )
)

(
( E6 )
( E3 )
( E4 E5 E7 )
( E4 E5 E6 )
( E1 )
)

But, notice something interesting.  The second list corresponds to the
or of the and of its elements. So that or is

E6 ! (E4 & E5 & E6) 

which is equal to

E6

so, we could check for *subsumption* when adding lists to the second
list. We say that x subsumes y iff every element of x is an element of
y. If we remove subsumed lists, when adding lists to our second list,
we wind up with the following.

(
( E8 )
( E2 )
)

(
( E6 )
( E3 )
( E4 E5 E7 )
( E1 )
)

Similarly, next we get the following (no subsumption).

(
( E2 )
)

(
( E8 )
( E6 )
( E3 )
( E4 E5 E7 )
( E1 )
)

Next we get the following.

(
)

(
( E2 )
( E8 )
( E6 )
( E3 )
( E4 E5 E7 )
( E1 )
)

Once our first list is empty, we are done and we return the final
list, but let's sort it so that variables in conjuctive clauses are
sorted, conjunctive clauses are sorted in terms of their length and
conjunctive clauses of the same length are sorted using the dictionary
order (so E1 comes before E2 and B1 comes before C and so on).

Therefore, we return the following.

(
( E1 )
( E2 )
( E3 )
( E6 )
( E8 )
( E4 E5 E7 )
)

We are left with just a list of lists containing only basic events.
What this tells us is that the original formula is equivalent to the
following DNF formula:

E1 ! E2 ! E3 ! E6 ! E8 ! (E4 & E5 & E7)

The formula above is actually the minimal DNF formula that is
equivalent to the orginal formula and it tells us that there are six
ways in which the simultaneous failure of components can lead to a
failure. In fact, five of these ways require only the failure of one
component.

|#

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

; This is the data definition for a list of lists. Make believe
; we wrote (listof list) instead of (listof acl2s::true-list)
(defdata llist (listof acl2s::true-list))

; To help you with debugging and to make it easier to test your
; functions, I provide you with sorting functions that we will use to
; sort lists of vars and lists of lists of vars.
(defunc insert (e l)
  :input-contract (listp l)
  :output-contract (listp (insert e l))
  (cond ((endp l) (list e))
        ((and (atom e)
              (atom (first l)))
         (if (acl2::<< e (first l))
             (cons e l)
           (cons (first l) (insert e (rest l)))))
        ((atom e)
         (cons e l))
        ((atom (first l))
         (cons (first l) (insert e (rest l))))
        ((< (len e) (len (first l)))
         (cons e l))
        ((equal (len e) (len (first l)))
         (if (acl2::<< e (first l))
             (cons e l)
           (cons (first l) (insert e (rest l)))))
        (t (cons (first l) (insert e (rest l))))))

(defunc isort (l)
  :input-contract (listp l)
  :output-contract (listp (isort l))
  (if (endp l)
      l
    (insert (first l) (isort (rest l)))))

; This function is given an llist and sorts each of its elements
; (which are lists).
(defunc sort-all (l)
  :input-contract (llistp l)
  :output-contract (llistp (sort-all l))
  (if (endp l)
      l
    (cons (isort (first l))
          (sort-all (rest l)))))

; This function is given an llist and sorts each of its elements
; (which are lists) and then sorts that.
(defunc isortll (l)
  :input-contract (llistp l)
  :output-contract (llistp (isortll l))
  (isort (sort-all l)))

; This is a data definition for variables.
(defdata var acl2s::var)

; Here are some examples. Just use a letter (A-Z) followed by
; any sequence of letters or numbers.
(check= (varp 'E) t)
(check= (varp 'E1) t)
(check= (varp 'S) t)
(check= (varp '+) nil)

; These are the operators we support (and/or).
(defdata bin-op (enum '(& !)))

; This just checks that operators and variables are distinct.
(defdata-disjoint bin-op var)

; This is a data definition for positive formulas, Boolean formulas
; using only and/or.
(defdata pform 
  (oneof var
         (list pform bin-op pform)))

; The formula we used in our example above is a positive formula.
(check= (pformp '((E1 ! (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8)))) ! E2)) t)

; A data definition for a list of formulas, which is the type of the
; elements in the first list of our example above.
(defdata lo-pform (listof pform))

; One of the elements appearing in a first list in our example above.
(check= (lo-pformp '( (E4 & E5) (E6 ! E7) )) t)

; A data definition for a list of lo-pforms, which is the type of the
; first list of our example above.
(defdata lo-lo-pform (listof lo-pform))

; One of the first lists in our example above.
(check= (lo-lo-pformp '(
                        ( ((E4 & E5) & (E6 ! E7)) )
                        ( (E3 ! (E6 ! E8)) )
                        ( E2 )
                        ))
        t)

; Conjunctive clauses will be represented by a list of vars.
(defdata lo-var (listof var))
(check= (lo-varp '(a b c d)) t)

; A DNF formula will be represented by a list of conjuctive clauses.
(defdata dnf (listof lo-var))
(check= (dnfp '((a b c d) (x))) t)

; Question 3a
;
; Define subsumesp, a function that given two lists, x and y returns t
; if every element in x is in y (in which case we say x subsumes y)
; and nil otherwise. Remember, in is a function that is available in
; beginner mode.
(defunc subsumesp (x y)
  :input-contract (and (listp x) (listp y))
  :output-contract (booleanp (subsumesp x y))
  (cond ((endp x) t)
        ((in (first x) y) (subsumesp (rest x) y))
        (t nil)))

(check= (subsumesp '(a b c) '(b a b c c)) t)
(check= (subsumesp '(a b c a b c) '(b a b c c)) t)
(check= (subsumesp '(a d) '(b a b c c)) nil)


; Question 3b
;
; Define add-subsume, a function that given c, a list, and d, an
; llist, recurs down d, and checks if the first element of d subsumes
; c, it returns d; if c subsumes the first element of d then it
; ignores the first element of d and recurs on the rest of the
; list; if neither of these cases holds, it conses the first element
; of d onto the result of calling add-subsume on the rest of d.
; If d is empty the list containing c is returned.
(defunc add-subsume (c d)
 :input-contract (and (lo-varp c) (dnfp d))
 :output-contract (dnfp (add-subsume c d))
 (cond ((endp d) (list c))
       ((subsumesp (first d) c) d)
       ((subsumesp c (first d)) (add-subsume c (rest d)))
       (t (cons (first d) (add-subsume c (rest d))))))

(check= (isortll (add-subsume '(a b) '((a b c) (d e b a) (c a d))))
        '((a b) (a c d)))

(check= (isortll (add-subsume '(a b c) '((a b) (d e a) (c a d))))
        '((a b) (a c d) (a d e)))

(check= (isortll (add-subsume '(a b) '((a d c) (c b e a) (a e g))))
        '((a b) (a c d) (a e g)))

(check= (isortll (add-subsume '(a b c) '((a d) (f b e a) (a b) (a e g))))
        '((a b) (a d) (a e g) (a b e f)))

; Question 3c
;
; Define app-subsume, a function that given x, an llist and y, an
; llist, adds each element in x to y using add-subsume. It returns an
; llist.  So, app-subsume is similar to app, but uses add-subsume
; instead of cons.
(defunc app-subsume (x y)
  :input-contract (and (dnfp x) (dnfp y))
  :output-contract (dnfp (app-subsume x y))
  (cond ((endp x) y)
        (t (add-subsume (first x) (app-subsume (rest x) y)))))

(check= (isortll (app-subsume '((a b) (a g e)) '((a d b) (f b e a) (a b) (e g))))
        '((a b) (e g)))

; Question 3d
;
; Define add-no-dup, a function that given e (which can be anything)
; and l, a list, returns l if e is in l, otherwise it returns a list
; whose elements include e and all the elements of l. The order in
; which the elements appear does not matter.
(defunc add-no-dup (e l)
  :input-contract (listp l)
  :output-contract (listp (add-no-dup e l))
  (if (in e l) l (cons e l)))

(check= (isort (add-no-dup 'a '(c b))) '(a b c))
(check= (isort (add-no-dup 'a '(c a b))) '(a b c))

; Question 3e
;
; Define app-no-dup, a function that given x, a list and y, a
; list, adds each element in x to y using add-no-dup. It returns an
; list.  So, app-no-dup is similar to app, but uses add-no-dup
; instead of cons.
(defunc app-no-dup (x y)
  :input-contract (and (listp x) (listp y))
  :output-contract (listp (app-no-dup x y))
  (cond ((endp x) y)
        (t (add-no-dup (first x) (app-no-dup (rest x) y)))))

(check= (isort (app-no-dup '(a b c) '(d c b))) '(a b c d))
(check= (isort (app-no-dup '(b b c) '(d c c))) '(b c c d))

:program

; Question 3f
; 
; Below is the definition of mocus, a function that takes as input, f,
; a pform.  It returns a dnf, as per the detailed description
; above. To make it easy to check answers, it sort the result using
; isortll. Your job is to define the helper functions. In my solution,
; I used two helper functions. I defined a helper function, mocus-aux,
; that take as input, f, a lo-lo-pform and acc, a dnf. To deal with
; lists that contain a Boolean operator, I defined another helper
; function, mocus-l that takes as input l, a lo-pform which is not a
; lo-var and finds a formula in l that contains a Boolean operator,
; and returns a lo-lo-pform consisting of the new lists obtained by
; removing the operator, as per the description above. You don't have
; to follow this plan and I encourage you to experiment.
(defunc add-to-all (x l res)
  :input-contract (and (pformp x) (lo-lo-pformp l) (lo-lo-pformp res))
  :output-contract (lo-lo-pformp (add-to-all x l res))
  (cond ((endp l) res)
        (t (add-to-all x (rest l) (cons (add-no-dup x (first l)) res)))))


(defunc mocus-l (l)
  :input-contract (lo-pformp l)
  :output-contract (lo-lo-pformp (mocus-l l))
  (cond ((endp l) (list nil))
        (t (let ((c (first l)))
             (cond ((varp c) (add-to-all c (mocus-l (rest l)) nil))
                   ((equal '! (first (rest c))) 
                    (list (add-no-dup (first c) (rest l))
                          (add-no-dup (first (rest (rest c))) (rest l))))
                   ((equal '& (first (rest c))) 
                    (list (add-no-dup (first c) (add-no-dup (first (rest (rest c))) 
                                                            (rest l))))))))))

(defunc mocus-aux (f acc)
  :input-contract (and (lo-lo-pformp f) (dnfp acc))
  :output-contract (dnfp (mocus-aux f acc))
  (cond ((endp f) acc)
        ((lo-varp (first f))
         (mocus-aux (rest f) (add-subsume (first f) acc)))
        (t (mocus-aux (app-no-dup (mocus-l (first f)) (rest f)) acc))))

(defunc mocus (f)
  :input-contract (pformp f)
  :output-contract (dnfp (mocus f))
  (isortll (mocus-aux (list (list f)) nil)))

(check=
 (mocus
  '(E1 ! (((E4 ! E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8)))))
 '((e1) (e3) (e6) (e8) (e4 e7) (e5 e7)))

(check=
 (mocus
  '((E1 ! (((E4 & E5) & (E6 ! E7)) ! (E3 ! (E6 ! E8)))) ! E2))
 '((e1) (e2) (e3) (e6) (e8) (e4 e5 e7)))

; Example1: landing gear deployment failure
(check=
 (mocus '((A ! (B ! C)) & ((C ! A) & (C ! B))))
 '((c) (a b)))

; Example2: no flow to pad delue nozzles
(check=
 (mocus '((A ! B) & ((A ! C) & ((D ! B) & (D ! C)))))
 '((a d) (b c)))

; Example3: pressure tank failure
(check=
 (mocus '(T1 ! ((S & (S1 ! (K1 ! R))) ! K2)))
 '((k2) (t1) (k1 s) (r s) (s s1)))
 
; Question 3g
;
; We can use the our algorithm to generate the minimal DNF for the 
; CNF formulas given in exercise 3.4 of the lecture notes.
;
; Fill in the ...'s below and add two more check= forms, where
; n (see the lecture notes) is 4 and 8. 
(check=
 (mocus
  '((x1 ! y1) & (x2 ! y2)))
 '((x1 x2) (x1 y2) (x2 y1) (y1 y2)))

(check=
 (mocus
  '(((x & y) ! z) & ((z ! x) & y)))
  '((x y) (y z)))

(check=
 (mocus
  '(((x1 & x2) & (y1 ! y2)) ! (y2 & x1)))
  '((x1 y2) (x1 x2 y1))) 

; For n>1, how many conjunctive clauses are there in the minimal DNF
; corresponding to the CNF formula from exercise 3.4 of the lecture
; notes?

"..."

; Question 3h
;
; Now we will test the fault tree from the US Nuclear Regulatory
; Commission's Fault Tree Handbook, as described above.

(check=
 (mocus
  '(P1 ! ((((P2 ! S2) !
            (((S4 ! (P4 ! E4)) !
              ((P5 ! (S6 ! (P6 ! E6))) ! S5)) &
              (S3 ! (P3 ! E3)))) !
              E1) ! S1)))
 '((E1)
   (P1)
   (P2)
   (S1)
   (S2)
   (E3 E4)
   (E3 E6)
   (E3 P4)
   (E3 P5)
   (E3 P6)
   (E3 S4)
   (E3 S5)
   (E3 S6)
   (E4 P3)
   (E4 S3)
   (E6 P3)
   (E6 S3)
   (P3 P4)
   (P3 P5)
   (P3 P6)
   (P3 S4)
   (P3 S5)
   (P3 S6)
   (P4 S3)
   (P5 S3)
   (P6 S3)
   (S3 S4)
   (S3 S5)
   (S3 S6)))



;Here are some more examples for you to consider, if you wish.

(mocus
  '((((((((D2 & D1) ! I3) !
        (((M2 & M1) ! I2) !
        (((R2 & R1) ! I1) !
           F1))) & 
        (((D2 & D1) ! I3) !
        (((M2 & M1) ! I2) !
        (((R2 & R1) ! I1) !
           F2)))) !
        I5) !
      S2) &
     ((((((D2 & D1) ! I3) !
        (((M2 & M1) ! I2) !
        (((R2 & R1) ! I1) !
           F1))) & 
        (((D2 & D1) ! I3) !
        (((M2 & M1) ! I2) !
        (((R2 & R1) ! I1) !
           F2)))) !
        I4) !
      S1)) ! P1))#|ACL2s-ToDo-Line|#


(mocus
'((G1 ! (R1 ! (((G2 ! ((((G3 ! R2) ! S1) ! S2) & (((G3 ! R2) ! S3) !
 S4))) ! S2) & ((((G4 ! ((((G3 ! R2) ! S1) ! S5) & (((G3 ! R2) ! S3) !
 S6))) ! S5) ! S2) & (((G2 ! ((((G3 ! R2) ! S1) ! S2) & (((G3 ! R2) !
 S3) ! S4))) ! S4) & (((G4 ! ((((G3 ! R2) ! S1) ! S5) & (((G3 ! R2) !
 S3) ! S6))) ! S6) ! S4)))))) ! ((G5 ! (R4 ! (((G4 ! ((((G3 ! R2) !
 S1) ! S5) & (((G3 ! R2) ! S3) ! S6))) ! S5) & ((((G2 ! ((((G3 ! R2) !
 S1) ! S2) & (((G3 ! R2) ! S3) ! S4))) ! S2) ! S5) & (((G4 ! ((((G3 !
 R2) ! S1) ! S5) & (((G3 ! R2) ! S3) ! S6))) ! S6) & (((G2 ! ((((G3 !
 R2) ! S1) ! S2) & (((G3 ! R2) ! S3) ! S4))) ! S4) ! S6)))))) ! ((G6 !
 (R1 ! (((G2 ! (((((G3 ! R2) ! S1) ! S2) & (((G3 ! R2) ! S3) ! S4)) !
 ((((G7 ! R1) ! S2) & ((G7 ! R1) ! S4)) ! (((G8 ! R1) ! S2) & ((G8 !
 R1) ! S4))))) ! S2) & ((((G4 ! (((((G3 ! R2) ! S1) ! S5) & (((G3 !
 R2) ! S3) ! S6)) ! (((((G7 ! R1) ! S2) ! S5) & (((G7 ! R1) ! S4) !
 S6)) ! ((((G8 ! R1) ! S2) ! S5) & (((G8 ! R1) ! S4) ! S6))))) ! S5) !
 S2) & (((G2 ! (((((G3 ! R2) ! S1) ! S2) & (((G3 ! R2) ! S3) ! S4)) !
 ((((G7 ! R1) ! S2) & ((G7 ! R1) ! S4)) ! (((G8 ! R1) ! S2) & ((G8 !
 R1) ! S4))))) ! S4) & (((G4 ! (((((G3 ! R2) ! S1) ! S5) & (((G3 ! R2)
 ! S3) ! S6)) ! (((((G7 ! R1) ! S2) ! S5) & (((G7 ! R1) ! S4) ! S6)) !
 ((((G8 ! R1) ! S2) ! S5) & (((G8 ! R1) ! S4) ! S6))))) ! S6) !
 S4)))))) ! (G9 ! (R4 ! (((G4 ! (((((G3 ! R2) ! S1) ! S5) & (((G3 !
 R2) ! S3) ! S6)) ! ((((G10 ! R4) ! S5) & ((G10 ! R4) ! S6)) ! (((G12
 ! R4) ! S5) & ((G12 ! R4) ! S6))))) ! S5) & ((((G2 ! (((((G3 ! R2) !
 S1) ! S2) & (((G3 ! R2) ! S3) ! S4)) ! (((((G10 ! R4) ! S5) ! S2) &
 (((G10 ! R4) ! S6) ! S4)) ! ((((G12 ! R4) ! S5) ! S2) & (((G12 ! R4)
 ! S6) ! S4))))) ! S2) ! S5) & (((G4 ! (((((G3 ! R2) ! S1) ! S5) &
 (((G3 ! R2) ! S3) ! S6)) ! ((((G10 ! R4) ! S5) & ((G10 ! R4) ! S6)) !
 (((G12 ! R4) ! S5) & ((G12 ! R4) ! S6))))) ! S6) & (((G2 ! (((((G3 !
 R2) ! S1) ! S2) & (((G3 ! R2) ! S3) ! S4)) ! (((((G10 ! R4) ! S5) !
 S2) & (((G10 ! R4) ! S6) ! S4)) ! ((((G11 ! R4) ! S5) ! S2) & (((G11
 ! R4) ! S6) ! S4))))) ! S4) ! S6))))))))))

