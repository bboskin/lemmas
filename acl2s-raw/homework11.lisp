#|
Technical instructions:
 
- Open this file in ACL2s as hwk11.lisp

- Make sure you are in ACL2s mode. This is essential! Note that you
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

- When done, save your file and submit it as hwk11.lisp

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

THE GOAL

The goal of this homework is to develop a compiler that takes
expressions like this:

(sq ((inc x) * ((sq 12) + (sq y))))

and generates an equivalent program for a stack machine, say

((LOAD X)
 (PUSH 1)
 (ADD)
 (PUSH 12)
 (DUP)
 (MUL)
 (LOAD Y)
 (DUP)
 (MUL)
 (ADD)
 (MUL)
 (DUP)
 (MUL))

What we want to prove is that no matter what input is given to the
compiler, as long as it is a well-formed expression, then the compiler
generates an equivalent well-formed program.

So, notice that we have to define well-formed expressions and
programs. This is the *syntax* of expressions and programs.

What does it mean that the expression and the program are equivalent?
This is harder to answer and it requires that we define the semantics
of expressions and programs. Here's how we do that. 

We mean that given any assignment, a mapping from variables to values,
evaluating the expression under that assignment gives us a number and
if we evaluate the compiler-generated program on the empty stack, we
get a stack with one element in it, the same number.

You will be asked to come up with the specification as part of this
homework.

We start by defining expressions. Notice how I do this. I use a
mutually recursive data definition because it makes function
definitions nicer later.

|#
(defttag t)
(include-book "top" :uncertified-okp t)


(defdata2 
  (expr (oneof integer 
               symbol 
               inc-expr
               sq-expr
               +-expr
               *-expr))
  (inc-expr (list 'inc expr))
  (sq-expr  (list 'sq expr))
  (+-expr   (list expr '+ expr))
  (*-expr   (list expr '* expr)))

(suggest-lemma (exprp e) :with exprp)
(suggest-lemma (inc-exprp e) :with inc-exprp)
(suggest-lemma (*-exprp e) :with *-exprp)

#|

Gain some familiarity with exprp. Try the following and your own
examples (you do not have to submit them as part of the homework).

(exprp 12)
(exprp 'a)
(exprp '(inc x))
(exprp '(sq (inc 12)))
(exprp '((inc 12) * (sq x)))

Here are some basic relationships between the data definitions.  These
require proof. The forms below state that various data definitions are
disjoint. You do not have to do anything here.

|#

(defdata-disjoint inc-expr sq-expr)
(defdata-disjoint inc-expr +-expr
  :hints (("goal" :expand (inc-exprp defdata::x))))
(defdata-disjoint inc-expr *-expr
  :hints (("goal" :expand (inc-exprp defdata::x))))
(defdata-disjoint sq-expr +-expr
  :hints (("goal" :expand (sq-exprp defdata::x))))
(defdata-disjoint sq-expr *-expr
  :hints (("goal" :expand (sq-exprp defdata::x))))
(defdata-disjoint +-expr *-expr
  :hints (("goal" :expand (*-exprp defdata::x))))


#|

Here's my plan. I want to turn off the definitions of the types, so I
want to collect together a number of rules that allow the theorem
prover to reason at a higher level, i.e., to not have to expand out
definitions to reason about the types I defined. This is part of my
theorem proving strategy.

How did I come up with the theorems?  I let ACL2s show me what it
needed, but I also thought about my rewrite strategy, e.g., I wrote
theorems that should apply before destructor elimination.  The details
are not relevant for this assignment. I include them here for those of
you that want to learn how to use the theorem prover.

|#

(defthm exprp-car
  (implies (and (exprp x)
                (not (equal (car x) 'inc))
                (not (equal (car x) 'sq)))
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm exprp-car-2
  (implies (and (exprp x)
                (consp (cddr x)))
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm consp-exprp
  (implies (and (exprp x)
                (not (atom x))
                (not (inc-exprp x))
                (not (sq-exprp x)))
           (consp (cddr x)))
  :rule-classes :type-prescription)
 
(defthm consp-*-exprp
  (implies (*-exprp x)
           (consp (cddr x)))
  :rule-classes :type-prescription)
 
(defthm consp-+-exprp
  (implies (+-exprp x)
           (consp (cddr x)))
  :rule-classes :type-prescription)
 
(defthm +-exprp-car
  (implies (+-exprp x)
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm +-exprp-caddr
  (implies (+-exprp x)
           (exprp (caddr x)))
  :rule-classes :type-prescription)
 
(defthm *-exprp-car
  (implies (*-exprp x)
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm *-exprp-caddr
  (implies (*-exprp x)
           (exprp (caddr x)))
  :rule-classes :type-prescription)
 
(defthm sq-exprp-cadr
  (implies (sq-exprp x)
           (exprp (cadr x)))
  :rule-classes :type-prescription)
 
(defthm inc-exprp-cadr
  (implies (inc-exprp x)
           (exprp (cadr x)))
  :rule-classes :type-prescription)
 
(defthm exprp-cases
  (implies (and (exprp x)
                (not (integerp x))
                (not (symbolp x))
                (not (inc-exprp x))
                (not (sq-exprp x))
                (not (*-exprp x)))
           (+-exprp x))
  :rule-classes :type-prescription)
 
(defthm exprp-expand
  (equal (exprp x)
         (or (integerp x)
             (symbolp x)
             (inc-exprp x)
             (sq-exprp x)
             (*-exprp x)
             (+-exprp x)))
  :rule-classes ((:compound-recognizer) (:rewrite)))

; I now disable the definitions
(in-theory (disable exprp inc-exprp sq-exprp *-exprp +-exprp))

#|

Next, we define an assignment, which is a mapping from
symbols (variables) to integers.

|#

(defdata2 assignment (alistof symbol integer))

; Notice that an alist is a list of cons pairs!

(check= (assignmentp '((x . 3) (y . 5) (z . 2))) t)
(check= (assignmentp '((x . 3) (y . 5) (2 . z))) nil)

#|
Q1.

Define the function lookup that given a symbol (a variable) and an
assignment, looks up the value of the variable in an assignment.  If
the variable is not in the assignment, return a default value of 0.

Note you can use any of the following if you think
you have a valid definition and ACL2s can't prove it.

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)
(program)

|#

(defunc2 lookupvar (x alist)
  :input-contract (and (symbolp x) (assignmentp alist))
  :output-contract (integerp (lookupvar x alist))
  (cond ((endp alist) 0)
        ((equal (car (car alist)) x) (cdr (car alist)))
        (t (lookupvar x (cdr alist)))))

(check= (lookupvar 'z '((x . 3) (y . 5) (z . 2))) 2)
(check= (lookupvar 'a '((x . 3) (y . 5) (z . 2))) 0)

#|
Q2.

Now define a function to evaluate an expression under an assignment.

Notice how we are doing this.  We use the data types defined above to
check what kind of expression we have.

|#

(defunc2 evaluate (x alist)
  :input-contract (and (exprp x) (assignmentp alist))
  :output-contract (integerp (evaluate x alist))
  (cond
   ((integerp x) x)
   ((symbolp x) (lookupvar x alist))
   ((inc-exprp x) (+ 1 (evaluate (car (cdr x)) alist)))
   ((sq-exprp x) (expt (evaluate (car (cdr x)) alist) 2))
   ((*-exprp x) (* (evaluate (car x) alist)
                   (evaluate (car (cdr (cdr x))) alist)))
   ;; Added a case for +
   ((+-exprp x) (+ (evaluate (car x) alist)
                   (evaluate (car (cdr (cdr x))) alist)))
   (t 0)))

(check= (evaluate 3 '((a . 2))) 3)
(check= (evaluate 'a '((a . 2))) 2)
(check= (evaluate '(sq a) '((a . 2))) 4)
(check= (evaluate '(inc a) '((a . 2))) 3)
(check= (evaluate '(4 + a) '((a . 2))) 6)
(check= (evaluate '(4 * a) '((a . 2))) 8)
(check= (evaluate '((3 * b) + a)   '((a . 7) (b . 4))) 19)


#|

We defined what an expression is and what it means.

Next, we define a stack-based machine.

|#

(defdata2 stack (listof integer))
(defdata2 non-empty-stack (cons integer stack))
(defdata2 empty-stack nil)


(check= (stackp '()) t)
(check= (empty-stackp '()) t)
(check= (non-empty-stackp '()) nil)

(check= (stackp '(1 2 -11 4)) t)
(check= (empty-stackp '(1 2 -11 4)) nil)
(check= (non-empty-stackp '(1 2 -11 4)) t)

(check= (stackp '(1 2/3 -11 4)) nil)
(check= (empty-stackp '(1 2/3 -11 4)) nil)
(check= (non-empty-stackp '(1 2/3 -11 4)) nil)

; property-based testing examples
(test? (implies (non-empty-stackp x)
                (stackp x)))

(test? (implies (empty-stackp x)
                (stackp x)))

; Here are some properties that are theorems
(defdata-subtype non-empty-stack stack)
(defdata-subtype empty-stack stack)
(defdata-disjoint empty-stack non-empty-stack)

; Notice that I will allow one to pop an empty stack.
; The cdr of nil is nil.
(defunc2 pop-stack (stk) 
  :input-contract (stackp stk)
  :output-contract (stackp (pop-stack stk))
  (cdr stk))

; Notice that the top of an empty stack is 0
(defunc2 top-stack (stk)
  :input-contract (stackp stk)
  :output-contract (integerp (top-stack stk))
  (if (consp stk) (car stk) 0))

; Notice the output contract
(defunc2 push-stack (val stk) 
  :input-contract (and (stackp stk) (integerp val))
  :output-contract (non-empty-stackp (push-stack val stk))
  (cons val stk))

#|

Next, we define what an instruction is.  Again, we use multiple
data definitions.

|#

(defdata2 load-instr (list 'load symbol))
(defdata2 push-instr (list 'push integer))
(defdata2 dup-instr '(dup))
(defdata2 add-instr '(add))
(defdata2 mul-instr '(mul))
(defdata2 instr (oneof load-instr push-instr dup-instr add-instr mul-instr))

(check= (instrp '(load x)) t)
(check= (instrp '(push x)) nil)
(check= (instrp '(push 10)) t)
(check= (instrp '(dup)) t)
(check= (instrp '(mul x y)) nil)

#|
Q3.

Define how to execute a single instruction, given a memory (an
assignment) and a stack. 

Again, note that we will use our data-definitions to make this easy
note the last case of the cond.

Only use the stack-modifying functions we defined above, e.g., instead
of cons, use push-stack. That gives us confidence that we are not
manipulating a stack in a way that violates the contracts of the
stack-modifying functions.

A load instruction pushes the value of the variable onto the stack.

A push instruction pushes the integer onto the stack.

A dup instruction duplicates the top of the stack.

An add instruction replaces the two top elements of the stack with
their sum.

A mul instruction replaces the two top elements of the stack with 
their product.
|#

(defunc2 execute (instr alist stk)
  :input-contract (and (instrp instr) (assignmentp alist) (stackp stk))
  :output-contract (stackp (execute instr alist stk))
  (cond
   ((load-instrp instr)
    (push-stack (lookupvar (car (cdr instr)) alist) stk))
   ((push-instrp instr)
    (push-stack (car (cdr instr)) stk))
   ((dup-instrp instr)
    (push-stack (top-stack stk) stk))
   ((add-instrp instr)
    (let ((n (top-stack stk))
          (s1 (pop-stack stk)))
      (let ((m (top-stack s1))
            (s2 (pop-stack s1)))
        (push-stack (+ m n) s2))))
   (t
    (let ((n (top-stack stk))
          (s1 (pop-stack stk)))
      (let ((m (top-stack s1))
            (s2 (pop-stack s1)))
        (push-stack (* m n) s2))))))

(check= (execute '(load a)  '((a . 7) (b . 4))   '(3 2 1))
	'(7 3 2 1))
(check= (execute '(push 5)  '((a . 7) (b . 4))   '(3 2 1))
        '(5 3 2 1))
(check= (execute '(dup)     '((a . 7) (b . 4))   '(3 2 1))        '(3 3 2 1))
(check= (execute '(add)     '((a . 7) (b . 4))   '(3 2 1))
        '(5 1))
(check= (execute '(mul)     '((a . 7) (b . 4))   '(3 2 1))
        '(6 1))

#|

Next, we define a function that runs a program, but first, we need to
define what a program is: it is a list of instructions.

|#

(defdata2 program (listof instr))

#|
Q4.

Define m, a function that runs a program.  Just execute all of the
instructions.

|#
(defunc2 m (program alist stk)
  :input-contract (and (programp program)
                       (assignmentp alist)
                       (stackp stk))
  :output-contract (stackp (m program alist stk))
  (cond ((endp program) stk)
        (t (m (cdr program) alist (execute (car program) alist stk)))))

(check=
 (m '((load a) (dup) (add)) '((a . 7) (b . 4))  '(1 2 3))
 '(14 1 2 3))

#|

Q5.

Now, define the  compiler.

|#

(defunc2 compile-expression (x)
  :input-contract (exprp x)
  :output-contract (programp (compile-expression x))
  (cond
   ((integerp x) (cons (cons 'push (cons x nil)) nil))
   ((symbolp x) (cons (cons 'load (cons x nil)) nil))
   ((inc-exprp x)
    (append (compile-expression (car (cdr x))) '((push 1) (add))))
   ((sq-exprp x)
    (append (compile-expression (car (cdr x))) '((dup) (mul))))
   ((+-exprp x)
    (append (compile-expression (car x)) 
            (compile-expression (car (cdr (cdr x))))
            '((add))))
   (t 
    (append (compile-expression (car x)) 
            (compile-expression (car (cdr (cdr x))))
            '((mul))))))

(check=
 (compile-expression '(sq (inc (a + (3 * b)))))
 '((load a)
   (push 3)
   (load b)
   (mul)
   (add)
   (push 1)
   (add)
   (dup)
   (mul)))

(defgroup compiler-fns
  m push-stack evaluate compile-expressions)


(suggest-lemma (m (append p1 p2) a s)
	       :required-expressions (m p1 a s)
	       :with compiler-fns)

(test? (IMPLIES (AND (TRUE-LISTP P1)
              (STACKP S)
              (PROGRAMP (BINARY-APPEND P1 P2))
              (ASSIGNMENTP A))
         (EQUAL (M (APPEND P1 P2) A S)
                (M P1 A S))))


(suggest-lemma (m (append p1 p2) a s)
	       :required-expressions p2 a (m p1 a s)
	       :with compiler-fns)

(test? (IMPLIES (AND (TRUE-LISTP P1)
              (STACKP S)
              (PROGRAMP (BINARY-APPEND P1 P2))
              (ASSIGNMENTP A))
         (EQUAL (M (APPEND P1 P2) A S)
                (M P2 A (M P1 A S)))))


(suggest-lemma (m (append p1 p2) a s)
	       :required-expressions p2 a (m p1 a s)
	       :with compiler-fns
	       :hyps (programp p1) (programp p2))

(defthm m-append-dist
  (IMPLIES (AND (TRUE-LISTP P1)
		(STACKP S)
		(PROGRAMP (BINARY-APPEND P1 P2))
		(ASSIGNMENTP A)
		(PROGRAMP P1)
		(PROGRAMP P2))
	   (EQUAL (M (APPEND P1 P2) A S)
		  (M P2 A (M P1 A S)))))

(defunc ind-cc (e a s)
  :input-contract (and (exprp e) (assignmentp a) (stackp s))
  :output-contract t
  (cond ((integerp e) t)
        ((symbolp e) t)
        ((inc-exprp e) (ind-cc (cadr e) a s))
        ((sq-exprp e) (ind-cc (cadr e) a s))
        ((+-exprp e)
         (cons (ind-cc (car e) a s)
               (ind-cc (caddr e) a 
                       (push-stack (evaluate (car e) a) s))))
        ((*-exprp e)
         (cons (ind-cc (car e) a s)
               (ind-cc (caddr e) a 
                       (push-stack (evaluate (car e) a) s))))
        (t (list e a s))))

(suggest-lemma (m (compile-expression e) a s)
	       :required-expressions (evaluate e a)
	       :with compiler-fns)

(defthm compiler-correct
  (IMPLIES (AND (EXPRP E)
              (STACKP S)
              (PROGRAMP (COMPILE-EXPRESSION E))
              (ASSIGNMENTP A))
         (EQUAL (M (COMPILE-EXPRESSION E) A S)
                (PUSH-STACK (EVALUATE E A) S)))
  :hints
  (("Goal"
    :induct (ind-cc-induction-scheme-from-definition e a s))))

(suggest-lemma (top-stack (m (compile-expression e) a nil))
	       :with compiler-fns)

(defthm compiler-correct-exact
  (IMPLIES (AND (EXPRP E)
              (ASSIGNMENTP A)
              (PROGRAMP (COMPILE-EXPRESSION E))
              (STACKP (M (COMPILE-EXPRESSION E) A 'NIL)))
         (EQUAL (TOP-STACK (M (COMPILE-EXPRESSION E) A NIL))
                (EVALUATE E A))))


(defgroup list-ops append cons car cdr len)


(suggest-lemma (insert x ls)
	       :required-expressions (less x ls) (notless x ls)
	       :with all-lines
	       :hyps (orderedp ls))
