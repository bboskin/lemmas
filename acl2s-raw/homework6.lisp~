; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
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

|#


#|

In this homework we will prove a little compiler correct.  This will
require proofs by induction, but we will generate the proof
obligations the induction principle generates for you, so you will
only be responsible for the equational reasoning part.

The following theorems are only useful for ACL2s.  If you use ACL2s to
check your conjectures, they will help ACL2s do a better job of
reasoning. You will not need to use them in your equational proofs.

|#

(defthm rest-force-thm
  (implies (acl2::force (consp x))
           (equal (rest x)
                  (acl2::rest x))))

(defthm first-force-thm
  (implies (acl2::force (consp x))
           (equal (first x)
                  (acl2::first x))))

(defthm second-force-thm
  (implies (acl2::force (consp (acl2::cdr x)))
           (equal (second x)
                  (acl2::second x))))

(defthm third-force-thm
  (implies (acl2::force (consp (acl2::cddr x)))
           (equal (third x)
                  (acl2::third x))))

#|

We introduce nand, a "universal" gate. Recall the notion of a complete
Boolean base from the lecture notes.  Nand, a binary operator, by
itself forms a complete Boolean base.

|#

(defunc nand (a b)
  :input-contract (and (booleanp a) (booleanp b))
  :output-contract (booleanp (nand a b))
  (not (and a b)))

#|

To see that nand forms a complete Boolean base, notice that we can use
it to define not and and.

|#

(thm (implies (booleanp x)
              (equal (not x)
                     (nand x x))))

(thm (implies (and (booleanp x)
                   (booleanp y))
              (equal (and x y)
                     (nand (nand x y)
                           (nand x y)))))

; Q1. Show how nand can be used to define or by filling in the ...'s
; below so that ACL2s accepts the definition. The expression you
; replace the ...'s with should be as simple as possible.  Use ACL2s
; to check your conjecture.

(thm (implies (and (booleanp x)
                   (booleanp y))
              (equal (or x y)
                     (nand (nand x x) 
                           (nand y y)))))


#|

We'll define a boolean expression type that uses variables which
represent boolean values (t or nil) and the connectives NOT, AND, and
OR.

|#

; This data type includes "nice" symbols. All you need to know is that
; it is a subtype of symbols and disjoint with Booleans. Feel free to
; use any thm's below as theorems in your proofs.
(defdata var acl2s::var)

(thm (implies (varp x)
              (symbolp x)))

(thm (implies (varp x)
              (not (booleanp x))))

(thm (implies (booleanp x)
              (not (varp x))))

; Here is another way of expressing subtype relationships in ACL2s.
(defdata-subtype var symbol)

; Here is another way of expressing that types are disjoint in ACL2s.
(defdata-disjoint var boolean)

; As a consequence, a var is not a list.
(thm (implies (varp x)
              (not (listp x))))

; Now the definition of a boolean expression.
(defdata bex
  (oneof boolean
         var
         (list 'not bex)
         (list 'and bex bex)
         (list 'or  bex bex)))

; It is often convenient to define subtypes. In this case we are
; defining subtypes of bex corresponding to not, and, and or bex
; expressions.
(defdata bex-not (list 'not bex))
(defdata bex-and (list 'and bex bex))
(defdata bex-or (list 'or bex bex))

; Notice that bex-not is a bex
(thm (implies (bex-notp e)
              (bexp e)))

(defdata-subtype bex-not bex)

; Notice that bex-and is a bex
(thm (implies (bex-andp e)
              (bexp e)))

(defdata-subtype bex-and bex)

; Notice that bex-or is a bex
(thm (implies (bex-orp e)
              (bexp e)))

(defdata-subtype bex-or bex)

#|

Next, we define an evaluator for boolean expressions. It takes an
extra argument: a list containing variables to treat as true.
Variables not appearing in the list are treated as being false
(nil). You can think of los, the second argument to bex-evaluate, as
an assignment. Recall that the definition of "in" can be found in the
lecture notes.

|#

(defdata lovar (listof var))

; Notice how we used bex-notp and bex-andp to simplify the code below.
(defunc bex-evaluate (be los)
  :input-contract (and (bexp be) (lovarp los))
  :output-contract (booleanp (bex-evaluate be los))
  (cond ((booleanp be) be)
        ((varp be) (in be los))
        ((bex-notp be)
         (not (bex-evaluate (second be) los)))
        ((bex-andp be)
         (and (bex-evaluate (second be) los)
              (bex-evaluate (third be) los)))
        (t (or (bex-evaluate (second be) los)
               (bex-evaluate (third be) los)))))

#|
Question 2:

What's involved in proving the bex-evaluate function's contract? It's
an inductive argument. We have two recursively-defined types
(bex and lovar), but we're going to use induction on bex.  Remember,
since we're proving the contract itself, we *don't* get to assume the
contract holds for bex-evaluate. 

Formalize in ACL2s the following statements, perform contact checking
and completion and provide proofs.

Example.

Suppose    (booleanp be).
Prove that (booleanp (bex-evaluate be los)).

FORMALIZATION:

(implies (booleanp be)
         (booleanp (bex-evaluate be los)))

CONTRACT CHECKING AND COMPLETION:

(implies (and (booleanp be)
              (lovarp los))
         (booleanp (bex-evaluate be los)))

PROOF:

C1. (booleanp be)
C2. (lovarp los)

(booleanp (bex-evaluate be los)))
  = { Def bex-evaluate, C1 }
(booleanp be)
  = { C1 }
t

2a: Suppose (varp be).
Prove that (booleanp (bex-evaluate be los)).

FORMALIZATION:

(implies (varp be)
         (booleanp (bex-evaluate be los)))    

CONTRACT CHECKING AND COMPLETION
|#

(thm (implies (and (varp be)
                   (lovarp los))
              (booleanp (bex-evaluate be los))))
#|
PROOF:

C1. (varp be)
C2. (lovarp los)
----------------
C3. (not (booleanp be)) {Disjoint var/boolean thm}

(booleanp (bex-evaluate be los))
= {Def bex-evaluate, C1, C3}
(booleanp (in be los))
= {Contract in}
t


2b: Suppose (bex-notp be) and 
            (booleanp (bex-evaluate (second be) los)).
Prove that  (booleanp (bex-evaluate be los)).

FORMALIZATION:

(implies (and (bex-notp be) 
              (booleanp (bex-evaluate (second be) los)))
        (booleanp (bex-evaluate be los)))
        
CONTRACT CHECKING AND COMPLETION
|#
(thm (implies (and (bex-notp be)
                   (booleanp (bex-evaluate (second be) los))
                   (lovarp los))
              (booleanp (bex-evaluate be los))))
#|   
PROOF:

C1: (bex-notp be)
C2: (booleanp (bex-evaluate (second be) los))
C3: (lovarp los))
------------------
C4: (and (not (booleanp be)) (not (varp e))) {Disjoint atom/cons}
C5: (bexp (second be)) {Def bexp}

(booleanp (bex-evaluate be los))
= {Def bex-evaluate, C1}
(booleanp (not (bex-evaluate (second be) los))
= {Definition of not, C2}
(booleanp (if (bex-evaluate (second be) los) nil t))
= {Case (bex-evaluate (second be) los), C2}
(booleanp (if t nil t)) ^ (booleanp (if nil nil t))
= {if axioms}
(booleanp nil) ^ (booleanp t)
= {boolean axioms}
t



2c: Suppose (bex-andp be) and
            (booleanp (bex-evaluate (second be) los)) and
            (booleanp (bex-evaluate (third be) los)).
Prove that  (booleanp (bex-evaluate be los)).

FORMALIZATION:

(implies (and (bex-andp be)
              (booleanp (bex-evaluate (second be) los))
              (booleanp (bex-evaluate (third be) los)))
         (booleanp (bex-evaluate be los)))
         
CONTRACT CHECKING AND COMPLETION
|#
(thm (implies (and (lovarp los)
                   (bex-andp be)
                   (booleanp (bex-evaluate (second be) los))
                   (booleanp (bex-evaluate (third be) los)))
              (booleanp (bex-evaluate be los)))) 
#|
PROOF:

C1: (bex-andp be)
C2: (lovarp los)
C3: (booleanp (bex-evaluate (second be) los))
C4: (booleanp (bex-evaluate (third be) los)))
-------------
C5: (and (not (booleanp be)) (not (varp be)) {Disjoint atom/cons}
C6: (bexp (second be)) {Def bexp}
C7: (bexp (third be)) {Def bexp}


(booleanp (bex-evaluate be los))
= {Def bex-evaluate, C1, C5}
(booleanp (and (bex-evaluate (second be) los)
               (bex-evaluate (third be) los)))
= {Def and, C3, C4} 
(booleanp (if (bex-evaluate (second be) los)
              (bex-evaluate (third be) los)
              nil))
= {Case (bex-evaluate (second be) los), C3}
(booleanp (if t (bex-evaluate (third be) los) nil))
^
(booleanp (if nil (bex-evaluate (third be) los) nil))
= {if axioms}
(booleanp (bex-evaluate (third be) los)) ^ (booleanp nil)
= {C4, boolean axiom}
t         
         
2d: Suppose (bex-orp be) and
            (booleanp (bex-evaluate (second be) los)) and
            (booleanp (bex-evaluate (third be) los)).
Prove that  (booleanp (bex-evaluate be los)).

FORMALIZATION:

(implies (and (bex-orp be)
              (booleanp (bex-evaluate (second be) los))
              (booleanp (bex-evaluate (third be) los)))
         (booleanp (bex-evaluate be los)))
         
CONTRACT CHECKING AND COMPLETION
|#

(thm (implies (and (lovarp los)
                   (bex-orp be)
                   (booleanp (bex-evaluate (second be) los))
                   (booleanp (bex-evaluate (third be) los)))
              (booleanp (bex-evaluate be los)))) 
#|
PROOF:

C1: (bex-orp be)
C2: (lovarp los)
C3: (booleanp (bex-evaluate (second be) los))
C4: (booleanp (bex-evaluate (third be) los)))
-----------
C5: (and (not (booleanp be)) (not (varp be))) {Disjoint atom/cons}
C6: (bexp (second be)) {Def bexp}
C7: (bexp (third be)) {Def bexp}


(booleanp (bex-evaluate be los))
= {Def bex-evaluate, C1, C5}
(booleanp (or (bex-evaluate (second be) los)
              (bex-evaluate (third be) los)))
= {Def or, C3, C4} 
(booleanp (if (bex-evaluate (second be) los) 
              t 
              (bex-evaluate (third be) los)))
= {Case (bex-evaluate (second be) los), C3}
(booleanp (if t t (bex-evaluate (third be) los)))
^
(booleanp (if nil t (bex-evaluate (third be) los)))
= {if axioms}
(booleanp t) ^ (booleanp (bex-evaluate (third be) los))
= {boolean axiom, C4}
t   

|#

#|

This is a bit embarrassing, but we didn't notice until last week that
the microcontroller that's going to run our next satellite launch
vehicle doesn't have NOT, AND and OR instructions.  Those darn
accountants decided to get the cheapest microcontroller and it is too
late to do anything about it.  The microcontroller only has one
Boolean instruction: NAND.  All of the boolean logic code we have was
written with the expectation that the NOT, AND, and OR operators were
all available. There's not enough time to manually rewrite all that
code before the scheduled launch, but we're pretty sure a good
compiler could do that work for us.

A couple of our interns aced 2800 last year, and they pointed out that
NAND was a complete Boolean base.  They also wrote a little compiler
that will take all of the ANDs, NOTs and ORs out of the Boolean
expressions and replace them with NANDs.  

|#

; Here is a data definition for our target language, which only has
; NANDs.
(defdata cex
  (oneof boolean
         var
         (list 'nand cex cex)))

#|

We define an evaluator for cex. As was the case with bex-evaluate, it
takes an extra argument: a list containing variables to treat as true.
Variables not appearing in the list are treated as being false
(nil). You can think of los as an assignment. Recall that the
definition of "in" can be found in the lecture notes.

|#

(defunc cex-evaluate (ce los)
  :input-contract (and (cexp ce) (lovarp los))
  :output-contract (booleanp (cex-evaluate ce los))
  (cond ((booleanp ce) ce)
        ((varp ce) (in ce los))
        (t (nand (cex-evaluate (second ce) los)
                 (cex-evaluate (third ce) los)))))

#|
Question 3:

What's involved in proving the cex-evaluate function's contract? It's
an inductive argument. We have two recursively-defined types
(cex and lovar), but we're going to use induction on cex.  Remember,
since we're proving the contract itself, we *don't* get to assume the
contract holds for cex-evaluate. 

Formalize in ACL2s the following statements, perform contact checking
and completion and provide proofs.


3a: Suppose (booleanp ce).
Prove that  (booleanp (cex-evaluate ce los)).


FORMALIZE:

(implies (booleanp ce)
         (booleanp (cex-evaluate ce los)))
         
CONTRACT CHECKING AND COMPLETION
|#
(thm (implies (and (booleanp ce)
                   (lovarp los))
              (booleanp (cex-evaluate ce los))))
#|
PROOF:

C1: (booleanp ce)
C2: (lovarp los)

(booleanp (cex-evaluate ce los))
= {Def cex-evaluate, C1}
(booleanp ce)
= {C1}
t

3b: Suppose (varp ce).
Prove that  (booleanp (cex-evaluate ce los)).

FORMALIZATION:

(implies (varp ce)
         (booleanp (cex-evaluate ce los)))
         
CONTRACT CHECKING AND COMPLETION:
|#
(thm (implies (and (varp ce)
                   (lovarp los))
              (booleanp (cex-evaluate ce los))))
#|
PROOF:

C1: (varp ce)
C2: (lovarp los)
----------------
C3: (not (booleanp ce)) {Disjoint boolean/var}

(booleanp (cex-evaluate ce los))
= {Def cex-evaluate, C1, C3}
(booleanp (in ce los))
== {Contract in}
t



3c: Suppose (cexp ce) and
            (not (booleanp ce))
            (not (varp ce)) 
            (booleanp (cex-evaluate (second ce) los)) and
            (booleanp (cex-evaluate (third ce) los)).
Prove that  (booleanp (cex-evaluate ce los)).

FORMALIZATION:

(implies (and (cexp ce)
              (not (booleanp ce))
              (not (varp ce)) 
              (booleanp (cex-evaluate (second ce) los))
              (booleanp (cex-evaluate (third ce) los)))
         (booleanp (cex-evaluate ce los)))
         
CONTRACT CHECKING AND COMPLETION:
|#

(thm (implies (and (cexp ce)
                   (not (booleanp ce))
                   (not (varp ce)) 
                   (lovarp los)
                   (booleanp (cex-evaluate (second ce) los))
                   (booleanp (cex-evaluate (third ce) los)))
              (booleanp (cex-evaluate ce los))))
#|

PROOF:

C1: (cexp ce)
C2: (not (booleanp ce))
C3: (not (varp ce)) 
C4: (lovarp los)
C5: (booleanp (cex-evaluate (second ce) los))
C6: (booleanp (cex-evaluate (third ce) los)))
-------------
C7: (cexp (second ce))
C8: (cexp (third ce))
a useful one:
C9: (booleanp (and (booleanp (cex-evaluate (second ce) los))
                   (booleanp (cex-evaluate (third ce) los))))  {Contract and, C5, C6}
                    

(booleanp (cex-evaluate ce los))
= {Def cex-evaluate, C2, C3}
(booleanp (nand (cex-evaluate (second ce) los)
                (cex-evaluate (third ce) los)))
= {Def nand, C5, C6}
(booleanp (not (and (cex-evaluate (second ce) los)
                    (cex-evaluate (third ce) los))))
= {Def not, C9}
(booleanp (if (and (cex-evaluate (second ce) los)
                   (cex-evaluate (third ce) los))
              nil
              t))
= {Case (and (cex-evaluate (second ce) los)
             (cex-evaluate (third ce) los)), C9}
(booleanp (if t nil t)) ^ (booleanp (if nil nil t))
= {if axioms}
(booleanp nil) ^ (booleanp t)
= {boolean axioms}
t

|#





#|

Here is the compiler written by our ace interns.  Notice they used the
equalities above relating nand with not, and and or to define the
compiler.

|#

(defunc compile (be)
  :input-contract (bexp be)
  :output-contract (cexp (compile be))
  (cond ((booleanp be) be)
        ((varp be) be)
        ((bex-notp be)
         (list 'nand
               (compile (second be))
               (compile (second be))))
        ((bex-andp be)
         (list 'nand
               (list 'nand
                     (compile (second be))
                     (compile (third be)))
               (list 'nand
                     (compile (second be))
                     (compile (third be)))))
        (t (list 'nand
                 (list 'nand
                       (compile (second be))
                       (compile (second be)))
                 (list 'nand
                       (compile (third be))
                       (compile (third be)))))))

#|
Question 4: 

It would be really silly to have our compiler pass accidentally leave
some NOTs or some ANDs or some ORs in the code. See if you can prove
the contract for compile. As before, you don't get to assume the
contract holds for be, but the induction principle will let you assume
it holds for pieces of be.

Formalize in ACL2s the following statements, perform contact checking
and completion and provide proofs.

4a: Suppose  (booleanp be).
Prove that   (cexp (compile be)).

FORMALIZE:
(implies (booleanp be)
         (cexp (compile be)))

CONTRACT CHECKING AND COMPLETION:
|#
(thm (implies (booleanp be)
              (cexp (compile be))))
#|
PROOF:

C1: (booleanp be)
--------
C2: (cexp be)

(cexp (compile be))
= {Def compile, C1}
(cexp be)
= {C2}
t

4b: Suppose (varp be).
Prove that  (cexp (compile be)).

FORMALIZE:

(implies (varp be)
         (cexp (compile be)))

CONTRACT CHECKING AND COMPLETION:
|#


(thm (implies (varp be)
              (cexp (compile be))))
#|
PROOF:

C1: (varp be)
-------------
C2: (not (booleanp be)) {Disjoint var/boolean}
C3: (cexp be) {Def cex}

(cexp (compile be))
= {Def compile, C1, C2}
(cexp be)
= {C3}
t

4c: Suppose (bex-notp be) and
            (cexp (compile (second be))).
Prove that  (cexp (compile be)).

FORMALIZATION:

(implies (and (bex-notp be)
              (cexp (compile (second be))))
         (cexp (compile be)))
         
CONTRACT CHECKING AND COMPLETION:      
|#
(thm (implies (and (bex-notp be)
                   (cexp (compile (second be))))
              (cexp (compile be))))

#|       
PROOF:

C1: (bex-notp be)
C2: (cexp (compile (second be)))
-------------
C3: (bexp (second be)) {Def cex}
C4: (cexp (list 'nand
                (cexp (compile (second be)))
                (cexp (compile (second be))))) {Def cex, C2}
C5: (and (not (varp be)) (not (booleanp be))) {Disjoint atom/cons}


(cexp (compile be))
= {Def compile, C1, C5}
(cexp (list 'nand
            (compile (second be))
            (compile (second be))))
= {C4}
t


4d: Suppose (bex-andp be) and 
            (cexp (compile (second be)))
            (cexp (compile (third be))).
Prove that  (cexp (compile be)).

FORMALIZATION:

(implies (and (bex-andp be)
              (cexp (compile (second be)))
              (cexp (compile (third be))))
         (cexp (compile be)))

CONTRACT CHECKING AND COMPLETION:

|#
(thm (implies (and (bex-andp be)
                   (cexp (compile (second be)))
                   (cexp (compile (third be))))
              (cexp (compile be))))
#|
PROOF:

C1: (bex-andp be)
C2: (cexp (compile (second be)))
C3: (cexp (compile (third be)))
---------------
C4: (bexp (second be)) {Def cex}
C5: (bexp (third be))) {Def cex}
C6: (cexp (list 'nand
                (compile (second be))
                (compile (third be))))
C7: (cexp (list 'nand
                (list 'nand
                      (compile (second be))
                      (compile (third be)))
                (list 'nand
                      (compile (second be))
                      (compile (third be)))))
C8: (and (not (booleanp be)) (not (varp be))) {Disjoint atom/cons}

(cexp (compile be))
= {Def compile, C1, C8}
(cexp (list 'nand
            (list 'nand
                  (compile (second be))
                  (compile (third be)))
            (list 'nand
                  (compile (second be))
                  (compile (third be)))))
= {C7}
t
                  
                  
4e: Suppose (bex-orp be) and 
            (cexp (compile (second be)))
            (cexp (compile (third be))).
Prove that  (cexp (compile be)).

FORMALIZATION:

(implies (and (bex-orp be)
              (cexp (compile (second be)))
              (cexp (compile (third be))))
         (cexp (compile be)))

CONTRACT CHECKING AND COMPLETION:

|#
(thm (implies (and (bex-orp be)
                   (cexp (compile (second be)))
                   (cexp (compile (third be))))
              (cexp (compile be))))


#|
PROOF:

C1: (bex-orp be)
C2: (cexp (compile (second be)))
C3: (cexp (compile (third be)))
---------------
C4: (bexp (second be))
C5: (bexp (third be)))
C6: (cexp (list 'nand
                (compile (second be))
                (compile (second be))))
C7: (cexp (list 'nand
                (compile (third be))
                (compile (third be))))
C8: (cexp (list 'nand
                (list 'nand
                      (compile (second be))
                      (compile (second be)))
                (list 'nand
                      (compile (third be))
                      (compile (third be)))))
C9: (and (not (varp be)) (not (booleanp be))) {Disjoint atom/cons}
                
(cexp (compile be))
= {Def compile, C1, C9}
(cexp (list 'nand
            (list 'nand
                  (compile (second be))
                  (compile (second be)))
            (list 'nand
                  (compile (third be))
                  (compile (third be)))))
= {C8}
t

There, that covers one part of correctness: the transformed code we
get from our compiler pass doesn't use any NOTs, ORs or ANDs. But what
about when we *run* that resulting code? The compiler isn't so helpful
if it sometimes changes the meaning of programs it compiles!  

What does it mean for the compiler to be correct?

Our crafty interns had just enough time to formalize this conjecture
and to use property-based testing with test? to gain some confidence
that the compiler is correct.

|#

(test?
 (implies (and (bexp be)
               (lovarp los))
          (equal (bex-evaluate be los)
                 (cex-evaluate (compile be) los))))

#|
OK, we tried testing it, and it at least seems right. But are we
really sure? Just failing to find a counterexample doesn't mean there
isn't one.

Our customers are not willing to launch their satellites without a
proof of correctness.  For an extra consulting fee, your job is to
verify the compiler.

Question 5:

Prove the conjecture we just tested. Given that we know (bexp be) and
(lovarp los), you need to prove that (bex-evaluate be los)  and
(cex-evaluate (compile be) los) are equal.

Formalize in ACL2s the following statements, perform contact checking
and completion and provide proofs.

5a: Suppose (booleanp be).
Prove that
(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los)).

FORMALIZE:

(implies (booleanp be)
         (equal (bex-evaluate be los)
                (cex-evaluate (compile be) los)))

CONTRACT CHECKING AND COMPLETION:
|#
(thm (implies (and (booleanp be)
                   (lovarp los))
              (equal (bex-evaluate be los)
                     (cex-evaluate (compile be) los))))
     
#|
PROOF:        
          
C1: (booleanp be)
C2: (lovarp los)
----------------
C3: (equal (compile be) be) {Def compile, C1}
C4: (booleanp (compile be)) {C1, C3}


(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los))
= {Def bex-evaluate}
(equal be (cex-evaluate (compile be) los)
= {C3}
(equal be (cex-evaluate be los))
= {Def cex-evaluate, C4}
(equal be be)
= {equal axiom}
t
         


5b: Suppose (varp be).
Prove that
(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los)).

FORMALIZE:

(implies (varp be)
         (equal (bex-evaluate be los)
                (cex-evaluate (compile be) los)))
                
CONTRACT CHECKING AND COMPLETION:    
|#
(thm (implies (and (varp be)
                   (lovarp los))
              (equal (bex-evaluate be los)
                     (cex-evaluate (compile be) los))))
     
#|
PROOF:

C1: (varp be)
C2: (lovarp los)
----------------
C3: (equal (compile be) be) {Def compile, C1}
C5: (not (booleanp be)) {Disjoint var/boolean}

(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los))
= {Def bex-evaluate, C1, C3}
(equal (in be los) (cex-evaluate (compile be) los)
= {C3}
(equal (in be los) (cex-evaluate be los))
= {Def cex-evaluate, C1, C5}
(equal (in be los) (in be los))
= {equal axiom}
t



5c: Suppose (bex-notp be) and 
            (equal (bex-evaluate (second be) los)
                   (cex-evaluate (compile (second be)) los)).
Prove that
(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los)).

FORMALIZE:
(implies (and (bex-notp be)
              (equal (bex-evaluate (second be) los)
                     (cex-evaluate (compile (second be)) los)))
         (equal (bex-evaluate be los)
                (cex-evaluate (compile be) los)))

CONTRACT CHECKING AND COMPLETION:
|#
(thm (implies (and (bex-notp be)
                   (lovarp los)
                   (equal (bex-evaluate (second be) los)
                          (cex-evaluate (compile (second be)) los)))
              (equal (bex-evaluate be los)
                     (cex-evaluate (compile be) los))))
                
#|    
PROOF:

C1: (bex-notp be)
C2: (lovarp los)
C3: (equal (bex-evaluate (second be) los)
           (cex-evaluate (compile (second be)) los))
----------------------
C4: (and (not (varp be))
         (not (booleanp be))) {Disjoint atom/cons}
C5: (bexp (second be)) {Def bex}  
C6: (booleanp (bex-evaluate (second be) los)) {Contract bex-evaluate, C5, C2}        
         
(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los))
= {Def bex-evaluate, C1, C4}
(equal (not (bex-evaluate (second be) los))
       (cex-evaluate (compile be) los))
= {Def compile, C1, C4}
(equal (not (bex-evaluate (second be) los))
       (cex-evaluate (list 'nand
                           (compile (second be))
                           (compile (second be))) los))
= {Def cex-evaluate}
(equal (not (bex-evaluate (second be) los))
       (nand (cex-evaluate (compile (second be)) los)
             (cex-evaluate (compile (second be)) los)))
= {nand axiom, C6}
(equal (not (bex-evaluate (second be) los))
       (not (cex-evaluate (compile (second be)) los)))
= {C3}
t

       
       
5d: Suppose (bex-andp be) and 
            (equal (bex-evaluate (second be) los)
                   (cex-evaluate (compile (second be)) los))
        and (equal (bex-evaluate (third be) los)
                   (cex-evaluate (compile (third be)) los)).
Prove that
(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los)).

FORMALIZATION:
(implies (and (bex-andp be)
              (equal (bex-evaluate (second be) los)
                     (cex-evaluate (compile (second be)) los))
              (equal (bex-evaluate (third be) los)
                     (cex-evaluate (compile (third be)) los)))
         (equal (bex-evaluate be los)
                (cex-evaluate (compile be) los)))
                
CONTRACT CHECKING AND COMPLETION:
|#
(thm (implies (and (bex-andp be)
                   (lovarp los)
                   (equal (bex-evaluate (second be) los)
                          (cex-evaluate (compile (second be)) los))
                   (equal (bex-evaluate (third be) los)
                          (cex-evaluate (compile (third be)) los)))
              (equal (bex-evaluate be los)
                     (cex-evaluate (compile be) los))))
#|
PROOF:

C1: (bex-andp be)
C2: (lovarp los)
C3: (equal (bex-evaluate (second be) los)
           (cex-evaluate (compile (second be)) los))
C4: (equal (bex-evaluate (third be) los)
           (cex-evaluate (compile (third be)) los))
--------------------------
C5: (and (not (varp be))
         (not (booleanp be))
         (not (bex-notp be))) {Disjoint bex thm}
C6: (bexp (second be)) {Def bex, C1}
C7: (bexp (third be)) {Def bex, C1}
C8: (cexp (compile (second be))) {Contract compile, C6}
C9: (cexp (compile (third be))) {Contract compile, C7}
C10: (booleanp (cex-evaluate (compile (second be)) los)) {Contract cex-evaluate, C8, C2}
C11: (booleanp (cex-evaluate (compile (third be)) los)) {Contract cex-evaluate, C9, C2}


(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los))
= {Def bex-evaluate C1, C5}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (cex-evaluate (compile be) los))
= {Def compile, C1, C5}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (cex-evaluate (list 'nand
                           (list 'nand
                                 (compile (second be))
                                 (compile (third be)))
                           (list 'nand
                                 (compile (second be))
                                 (compile (third be))))
                      los))
= {Def cex-evaluate}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (nand (cex-evaluate (list 'nand
                                 (compile (second be))
                                 (compile (third be))) los)
             (cex-evaluate (list 'nand
                                 (compile (second be))
                                 (compile (third be))) los)))
= {nand axiom}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (not (cex-evaluate (list 'nand
                                (compile (second be))
                                (compile (third be))) los)))
= {Def cex-evaluate}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (not (nand (cex-evaluate (compile (second be)) los)
                  (cex-evaluate (compile (third be)) los))))
= {Def nand, C10, C11}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (not (not (and (cex-evaluate (compile (second be)) los)
                      (cex-evaluate (compile (third be)) los)))))
= {not axioms}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (and (cex-evaluate (compile (second be)) los)
            (cex-evaluate (compile (third be)) los)))
= {equal axioms, C3}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (and (bex-evaluate (second be) los)
            (cex-evaluate (compile (third be)) los)))
= {equal axioms, C4}
(equal (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))
       (and (bex-evaluate (second be) los)
            (bex-evaluate (third be) los))) 
= {equal axioms]
t


5e: Suppose (bex-orp be) and 
            (equal (bex-evaluate (second be) los)
                   (cex-evaluate (compile (second be)) los))
        and (equal (bex-evaluate (third be) los)
                   (cex-evaluate (compile (third be)) los)).
Prove that
(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los)).

FORMALIZE:
(implies (and (bex-orp be)
              (equal (bex-evaluate (second be) los)
                     (cex-evaluate (compile (second be)) los)))
         (equal (bex-evaluate (third be) los)
                (cex-evaluate (compile (third be)) los)))

CONTRACT CHECKING AND COMPLETION:
|#

(thm (implies (and (bex-orp be)
                   (lovarp los)
                   (equal (bex-evaluate (second be) los)
                          (cex-evaluate (compile (second be)) los))
                   (equal (bex-evaluate (third be) los)
                          (cex-evaluate (compile (third be)) los)))
              (equal (bex-evaluate be los)
                     (cex-evaluate (compile be) los))))
     
#|
PROOF:

C1: (bex-orp be)
C2: (lovarp los)
C3: (equal (bex-evaluate (second be) los)
           (cex-evaluate (compile (second be)) los))
C4: (equal (bex-evaluate (third be) los)
           (cex-evaluate (compile (third be)) los))
-------------------------------
C5: (bexp (second be)) {Def bex}
C6: (bexp (third be)) {Def bex}
C7: (cexp (compile (second be))) {Contract compile, C5}
C8: (cexp (compile (third be))) {Contract compile, C6}
C9: (cexp (list 'nand (compile (second be)) (compile (second be)))) {Def cex, C8}
C10: (cexp (list 'nand (compile (third be)) (compile (third be)))) {Def cex, C9}
C11: (cexp (list 'nand
                 (list 'nand (compile (second be)) (compile (second be)))
                 (list 'nand (compile (third be)) (compile (third be))))) {Def cex, C9 ,C10}
C12: (booleanp (cex-evaluate (list 'nand (compile (second be)) (compile (second be))) los)) {Contract cex-evaluate, C9, C2}
C13: (booleanp (cex-evaluate (list 'nand (compile (third be)) (compile (third be))) los)) {Contract cex-evaluate, C10, C2}
C14: (booleanp (cex-evaluate (compile (second be)) los)) {Contract cex-evaluate, C7, C2}    
C15: (booleanp (cex-evaluate (compile (third be)) los)) {Contract cex-evaluate, C8, C2}    

(equal (bex-evaluate be los)
       (cex-evaluate (compile be) los))
= {Def bex-evaluate, C1, C2}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (cex-evaluate (compile be) los))
= {Def compile, C1}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (cex-evaluate 
          (list 'nand
                (list 'nand (compile (second be)) (compile (second be)))
                (list 'nand (compile (third be)) (compile (third be))))
          los))
= {Def cex-evaluate C11, C2}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (nand (cex-evaluate (list 'nand (compile (second be)) (compile (second be))) los)
             (cex-evaluate (list 'nand (compile (third be)) (compile (third be))) los)))
= {Def nand, C12, C13}          
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (not (and (cex-evaluate (list 'nand (compile (second be)) (compile (second be))) los)
                 (cex-evaluate (list 'nand (compile (third be)) (compile (third be))) los))))         
= {Def cex-evaluate, C7, C2}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (not (and (nand (cex-evaluate (compile (second be)) los)
                       (cex-evaluate (compile (second be)) los))
                 (cex-evaluate (list 'nand (compile (third be)) (compile (third be))) los))))
= {Def cex-evaluate, C8, C2}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (not (and (nand (cex-evaluate (compile (second be)) los)
                       (cex-evaluate (compile (second be)) los))
                 (nand (cex-evaluate (compile (third be)) los)
                       (cex-evaluate (compile (third be)) los)))))
= {nand-axioms, C14, C15}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (not (and (not (cex-evaluate (compile (second be)) los))
                 (not (cex-evaluate (compile (third be)) los)))))
= {PL (deMorgan)}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (or (cex-evaluate (compile (second be)) los)
           (cex-evaluate (compile (third be)) los)))
= {equal axioms, C3, C4}
(equal (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los))
       (or (bex-evaluate (second be) los)
           (bex-evaluate (third be) los)))
= {equal axiom}
t

After doing all that work, you wondered, why didn't I just use the
theorem prover? Oh well, you still got paid. ACL2s can prove this as
well:

|#

(defthm compiler-correctness
  (implies (and (bexp be)
                (lovarp los))
           (equal (bex-evaluate be los)
                  (cex-evaluate (compile be) los))))#|ACL2s-ToDo-Line|#


