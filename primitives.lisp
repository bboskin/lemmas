#|Primitives used in the ACL2s->miniKanren compiler|#
(load "mk.lisp")
(load "numbers.lisp")

#|
There are three explicit types here, denoted within the interpreter with tags

Variables (non-boolean symbols) : `(INTERNAL-SYMBOL ,s)
Numbers (little-endian binary) : `(INTERNAL-NUMBER ,s)
Cons cells : `(INTERNAL-CONS ,a ,d)

booleans are just themselves (t and nil)
|#


#|
Because predicates are nicely thought of as goals with no output,
for functions that return booleans, there are typically 2 versions.
One, with the expected name, which does not generate output.
Two, a second version, name-fn, which has an extra argument to generate output.
This is the explicit or generalized boolean that would be expected
from the function.
|#

;; basic recognizers
(defrel booleanpo (e)
  (conde
   ((== e t))
   ((== e nil))))

(defrel booleanpo-fn (e o)
  (conde
   ((booleanpo e) (== o t))
   ((conspo e) (== o nil))
   ((numberpo e) (== o nil))
   ((varpo e) (== o nil))))

(defrel varpo (e) (fresh (v) (== e `(INTERNAL-SYMBOL ,v))))
(defrel varpo-fn (e o)
  (conde
   ((varpo e) (== o t))
   ((booleanpo e) (== o nil))
   ((conspo e) (== o nil))
   ((numberpo e) (== o nil))))

(defun build-sym (s)
  (if (symbolp s)
      `(INTERNAL-SYMBOL ,s)
    (error "Not a symbol: ~a" s)))


;; a useful relation
(defrel non-nilo (e)
  (conde
   ((== e t))
   ((varpo e))
   ((numberpo e))
   ((conspo e))))

;; List primitives: cons, car, cdr, endp, consp
(defrel conso (a d o) (== o `(INTERNAL-CONS ,a ,d)))
(defrel caro (pr a) (fresh (d) (conso a d pr)))
(defrel cdro (pr d) (fresh (a) (conso a d pr)))

(defrel endpo (e) (== e '()))
(defrel endpo-fn (e o)
  (conde
   ((== e nil) (== o t))
   ((non-nilo e) (== o nil))))

(defrel conspo (e) (fresh (a d) (== e `(INTERNAL-CONS ,a ,d))))
(defrel conspo-fn (e o)
  (conde
   ((conspo e) (== o t))
   ((numberpo e) (== o nil))
   ((varpo e) (== o nil))
   ((booleanpo e) (== o nil))))


;; Other built-in list functions: append, reverse
(defrel appendo (l1 l2 o)
  (conde
   ((== l1 '()) (== l2 o))
   ((fresh (a d res)
	   (conso a d l1)
	   (conso a res o)
	   (appendo d l2 res)))))

(defrel reverso (l o)
  (conde
   ((== l '()) (== o '()))
   ((fresh (a d a-l res)
	   (conso a d l)
	   (conso a nil a-l)
	   (reverso d res)
	   (appendo res a-l o)
	   ))))

;; boolean functions that return values
(defrel ando (e1 e2 o)
  (conde
   ((non-nilo e1) (non-nilo e2) (== o e2))
   ((== e1 nil) (== o nil))
   ((== e2 nil) (== o nil))))

(defrel oro (e1 e2 o)
  (conde
   ((non-nilo e1) (== o e1))
   ((== e1 nil) (non-nilo e2) (== o e2))
   ((== e1 nil) (== e2 nil) (== o nil))))

(defrel noto (e o)
  (conde
   ((non-nilo e) (== o nil))
   ((== e nil) (== o t))))

;; The arithmetic operations: zerop, numberp, +, -, *, /, ^
(defrel zeropo (n) (== n '(INTERNAL-NUMBER)))
(defrel zeropo-fn (n o)
  (conde
   ((zeropo n) (== o t))
   ((do-less-than-o '(INTERNAL-NUMBER) n) (== o nil))
   ((conspo n) (== o nil))
   ((varpo n) (== o nil))
   ((booleanpo n) (== o nil))))

(defrel numberpo (n)
  (fresh (e) (== n `(INTERNAL-NUMBER . ,e))))
(defrel numberpo-fn (n o)
  (conde
   ((numberpo n) (== o t))
   ((conspo n) (== o nil))
   ((varpo n) (== o nil))
   ((booleanpo n) (== o nil))))


(defrel do-pluso (n m o)
  (fresh (a b c)
	 (== n `(INTERNAL-NUMBER . ,a))
	 (== m `(INTERNAL-NUMBER . ,b))
	 (== o `(INTERNAL-NUMBER . ,c))
	 (pluso a b c)))

(defrel do-minuso (n m o)
  (fresh (a b c)
	 (== n `(INTERNAL-NUMBER . ,a))
	 (== m `(INTERNAL-NUMBER . ,b))
	 (== o `(INTERNAL-NUMBER . ,c))
	 (minuso a b c)))

(defrel do-timeso (n m o)
  (fresh (a b c)
	 (== n `(INTERNAL-NUMBER . ,a))
	 (== m `(INTERNAL-NUMBER . ,b))
	 (== o `(INTERNAL-NUMBER . ,c))
	 (*o a b c)))

(defrel do-expo (n m o)
  (fresh (a b c)
	 (== n `(INTERNAL-NUMBER . ,a))
	 (== m `(INTERNAL-NUMBER . ,b))
	 (== o `(INTERNAL-NUMBER . ,c))
	 (expo a b c)))

;;; less than and leq as pure goals
(defrel do-less-than-o (n m)
  (fresh (a b)
	 (== n `(INTERNAL-NUMBER . ,a))
	 (== m `(INTERNAL-NUMBER . ,b))
	 (<o a b)))

(defrel do-less-than-equal-o (n m)
  (fresh (a b)
	 (== n `(INTERNAL-NUMBER . ,a))
	 (== m `(INTERNAL-NUMBER . ,b))
	 (<=o a b)))

;; versions that return t and nil
(defrel do-less-than-o-fn (n m o)
  (conde
   ((do-less-than-o n m) (== o 't))
   ((do-less-than-equal-o m n) (== o 'nil))))

(defrel do-less-than-equal-o-fn (n m o)
  (conde
   ((do-less-than-equal-o n m) (== o 't))
   ((do-less-than-o m n) (== o 'nil))))
