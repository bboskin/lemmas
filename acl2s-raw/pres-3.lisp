(defttag t)
(include-book "lemma-synth" :uncertified-okp t)

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


#|A bunch of theorems about expr so that we can reason properly|#
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

(in-theory (disable exprp inc-exprp sq-exprp *-exprp +-exprp))

#| Next, we define an assignment, which is a mapping from
   symbols (variables) to integers.|#

(defdata2 assignment (alistof symbol integer))

(defunc2 lookupvar (x alist)
  :input-contract (and (symbolp x) (assignmentp alist))
  :output-contract (integerp (lookupvar x alist))
  (cond ((endp alist) 0)
	((equal (caar alist) x) (cdar alist))
	(t (lookupvar x (rest alist)))))

(defunc2 evaluate (x alist)
  :input-contract (and (exprp x) (assignmentp alist))
  :output-contract (integerp (evaluate x alist))
  (cond
   ((integerp x) x)
   ((symbolp x) (lookupvar x alist))
   ((inc-exprp x) (+ 1 (evaluate (second x) alist)))
   ((sq-exprp x) (expt (evaluate (second x) alist) 2))
   ((*-exprp x) (* (evaluate (first x) alist)
                   (evaluate (third x) alist)))
   ((+-exprp x) (+ (evaluate (first x) alist)
                   (evaluate (third x) alist)))
   (t 0)))


#|Next, we define a stack-based machine.|#

(defdata2 stack (listof integer))
(defdata2 non-empty-stack (cons integer stack))
(defdata2 empty-stack nil)

; Here are some properties that are theorems
(defdata-subtype non-empty-stack stack)
(defdata-subtype empty-stack stack)
(defdata-disjoint empty-stack non-empty-stack)

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

(defunc2 execute (instr alist stk)
  :input-contract (and (instrp instr) (assignmentp alist) (stackp stk))
  :output-contract (stackp (execute instr alist stk))
  (cond
   ((load-instrp instr)
    (push-stack (lookupvar (second instr) alist) stk))
   ((push-instrp instr)
    (push-stack (second instr) stk))
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

(defdata2 program (listof instr))

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

(defunc2 compile-expression (x)
  :input-contract (exprp x)
  :output-contract (programp (compile-expression x))
  (cond
   ((integerp x) (list (list 'push x)))
   ((symbolp x) (list (list 'load x)))
   ((inc-exprp x)
    (append (compile-expression (second x)) '((push 1) (add))))
   ((sq-exprp x)
    (append (compile-expression (second x)) '((dup) (mul))))
   ((+-exprp x)
    (append (compile-expression (first x)) 
            (compile-expression (third x))
            '((add))))
   (t 
    (append (compile-expression (first x)) 
            (compile-expression (third x))
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

#|Now, we have some theorems to prove|#

(defgroup compiler-fns m push-stack evaluate compile-expressions)

(suggest-lemma (m (append p1 p2) a s)
	       :required-expressions m (m p1 a s)
	       :complete-hyps nil
	       :with compiler-fns
	       :hyps (programp p1) (programp p2) (stackp s) (assignmentp a))

(defthm m-append-dist
  (IMPLIES (AND (PROGRAMP P1)
              (PROGRAMP P2)
              (STACKP S)
              (ASSIGNMENTP A))
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
