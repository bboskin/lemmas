(in-package "ACL2S")

#|Primitives used in the ACL2s->miniKanren compiler|#
;(load "mk-raw.lsp")
;(load "numbers-raw.lsp")

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

(defrel listpo (e)
  (conde
   ((endpo e))
   ((conspo e))))

(defrel listpo-fn (e o)
  (conde
   ((== e nil) (== o t))
   ((conspo e) (== o t))
   ((== e t) (== o nil))
   ((numberpo e) (== o nil))
   ((varpo e) (== o nil))
   ((nonvarpo e) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel improper-conspo (e)
  (fresh (d)
    (cdro e d)
    (conde
     ((improper-conspo d))
     ((numberpo d))
     ((symbolpo d))
     ((charpo d))
     ((stringpo d)))))

(defrel true-listpo (e)
  (conde
   ((endpo e))
   ((conspo e)
    (fresh (d)
      (cdro e d)
      (true-listpo d)))))

(defrel true-listpo-fn (e o)
  (conde
   ((true-listpo e) (== o t))
   ((== e t) (== o nil))
   ((improper-conspo e) (== o nil))
   ((numberpo e) (== o nil))
   ((varpo e) (== o nil))
   ((nonvarpo e) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel booleanpo (e)
  (conde
   ((== e t))
   ((== e nil))))

(defrel booleanpo-fn (e o)
  (conde
   ((varpo e) (== o nil))
   ((nonvarpo e) (== o nil))
   ((booleanpo e) (== o t))
   ((conspo e) (== o nil))
   ((numberpo e) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel varpo (e)
  (fresh (v)
	 (== e `(INTERNAL-VARSYMBOL ,v))))

(defrel nonvarpo (e)
  (fresh (v)
     (== e `(INTERNAL-SYMBOL ,v))))

(defrel varpo-fn (e o)
  (conde
   ((varpo e) (== o t))
   ((nonvarpo e) (== o nil))
   ((booleanpo e) (== o nil))
   ((conspo e) (== o nil))
   ((numberpo e) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defun build-sym (sy)
  (if (symbolp sy)
      (if (acl2s::varp sy)
	  `(INTERNAL-VARSYMBOL ,sy)
	`(INTERNAL-SYMBOL ,sy))
    (error "Not a symbol: ~a" s)))

(defrel symbolpo (sy)
  (conde
   ((varpo sy))
   ((nonvarpo sy))
   ((booleanpo sy))))

(defrel symbolpo-fn (sy o)
  (conde
   ((symbolpo sy) (== o t))
   ((numberpo sy) (== o nil))
   ((conspo sy) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo sy) (== o nil))))

;; a useful relation
(defrel non-nilo (e)
  (conde
   ((== e t))
   ((varpo e))
   ((nonvarpo e))
   ((numberpo e))
   ((conspo e))
   ((stringpo e))
   ((charpo e))))

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
   ((symbolpo e) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo e) (== o nil))))


;; Other built-in list functions: append, reverse
(defrel appendo (l1 l2 o)
  (conde
   ((== l1 '()) (== l2 o))
   ((fresh (a d res)
	   (conso a d l1)
	   (conso a res o)
	   (appendo d l2 res)))))

(defrel ls-reverso (l o)
  (conde
   ((== l '()) (== o '()))
   ((fresh (a d a-l res)
	   (conso a d l)
	   (conso a nil a-l)
	   (ls-reverso d res)
	   (appendo res a-l o)))))

(defrel leno (l n)
  (conde
   ((== l nil) (== n '(INTERNAL-NUMBER (0))))
   ((fresh (a d r)
	   (conso a d l)
	   (leno d r)
	   (do-pluso '(INTERNAL-NUMBER (0) 1) r n)))))

(defrel membero (x ls)
  (fresh (a d)
    (conso a d ls)
    (conde
     ((== a x))
     ((membero x d)))))

(defrel membero-fn (x ls o)
  (conde
   ((== ls nil) (== o nil))
   ((fresh (a d)
      (conso a d ls)
      (conde
       ((== a x) (== o t))
       ((membero-fn x d o)))))))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NEW NUMBER STUFF


;; predicates for new number representations

(defrel zeropo (n)
  (== n '(INTERNAL-NUMBER (0))))

(defrel zeropo-fn (n o)
  (conde
   ((zeropo n) (== o t))
   ((pospo n) (== o nil))
   ((negpo n) (== o nil))
   ((rationalp-exclu n) (== o nil))
   ((conspo n) (== o nil))
   ((symbolpo n) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel natpo (n)
  (fresh (e)
    (== n `(INTERNAL-NUMBER (0) . ,e))))

(defrel natpo-fn (n o)
  (conde
   ((natpo n) (== o t))
   ((negpo n) (== o nil))
   ((rationalp-exclu n) (== o nil))
   ((conspo n) (== o nil))
   ((symbolpo n) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))


(defrel pospo (n)
  (fresh (e)
    (fresh (a d) (== e `(,a . ,d)))
    (== n `(INTERNAL-NUMBER (0) . ,e))))

(defrel pospo-fn (n o)
  (conde
   ((pospo n) (== o t))
   ((zeropo n) (== o nil))
   ((negpo n) (== o nil))
   ((rationalp-exclu n) (== o nil))
   ((conspo n) (== o nil))
   ((symbolpo n) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel negpo (n)
  (fresh (e)
    (fresh (a d) (== e `(,a . ,d)))
    (== n `(INTERNAL-NUMBER (1) . ,e))))

(defrel negpo-fn (n o)
  (conde
   ((natpo n) (== o nil))
   ((negpo n) (== o t))
   ((rationalp-exclu n) (== o nil))
   ((conspo n) (== o nil))
   ((symbolpo n) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel integerpo (n)
  (conde
   ((natpo n))
   ((negpo n))))

(defrel integerpo-fn (n o)
  (conde
   ((integerpo n) (== o t))
   ((rationalp-exclu n) (== o nil))
   ((conspo n) (== o nil))
   ((symbolpo n) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))

(defrel rationalp-exclu (n)
  (fresh (numer denom)
    (== n `(INTERNAL-NUMBER (RATIONAL) ,numer ,denom))
    (integerpo numer)
    (integerpo denom)))

(defrel rationalpo (n)
  (conde
   ((integerpo n))
   ((rationalp-exclu n))))

(defrel rationalpo-fn (n o)
  (conde
   ((rationalpo n) (== o t))
   ((conspo n) (== o nil))
   ((symbolpo n) (== o nil))
   ((stringpo e) (== o nil))
   ((charpo s) (== o nil))))


;; numbers are just rationals, here
(defrel numberpo (n) (rationalpo n))

(defrel numberpo-fn (n o) (rationalpo-fn n o))

;; simplifying rationals so that checking for zero, etc, doesn't get hard
(defrel new-sign (s1 s2 o)
  (conde
   ((== s1 s2) (== o 0))
   ((conde
     ((== s1 1) (== s2 0))
     ((== s1 0) (== s2 1)))
    (== o 1))))

(defrel find-min (n m o)
  (conde
   ((<o n m) (== o n))
   ((<=o m n) (== o m))))

(defrel sub1o (n o)
  (conde
   ((== n '(1)) (== o nil))
   ((fresh (b1 b)
	   (== n `(,b1 . ,b))
	   (conde
	    ((== b1 1) (poso b)
	     (== o `(0 . ,b)))
	    ((== b1 0)
	     (fresh (o^)
		    (sub1o b o^)
		    (== o `(1 . ,o^)))))))))

(defrel divides (a b n)
  (conde
   ((== a '()) (== n '()))
   ((fresh (b1 bs)
      (== a `(,b1 . ,bs))
      (fresh (a-b n-1)
	(pluso b a-b a)
	(divides a-b b n-1)
	(pluso '(1) n-1 n))))))

;; this causes us to lose run*
(defrel does-not-divide (sm a b)
  (conde
   ((<o sm b)
    (fresh (k l)
      (pluso sm a k)
      (*o l b k)))
   ((<o sm b)
    (fresh (sm+1)
      (pluso '(1) sm sm+1)
      (does-not-divide sm+1 a b)))))


(defrel do-simp (a b c new-a new-b)
  (conde
   ((== c '(1)) (== new-a a) (== new-b b))
   ((fresh (q-a q-b c-1)
      (fresh (b1 b2 bs) (== c `(,b1 ,b2 . ,bs)))
      (conde
       ((divides a c new-a) (divides b c new-b))
       ;; this line below is unguarded, but makes the algorithm
       ;; way faster, and still correct for a run 1
       ((sub1o c c-1) (do-simp a b c-1 new-a new-b)))))))

#|
(defrel gcf (a b c f new-a new-b)
  (conde
   ((== c '(1)) (== f '(1)) (== new-a a) (== new-b b))
   ((fresh (q-a r-a q-b r-b c-1)
      (fresh (b1 b2 bs) (== c `(,b1 ,b2 . ,bs)))
      (/o a c q-a r-a)
      (/o b c q-b r-b)
      (conde
       ((== r-a nil) (== r-b nil) (== f c) (== q-a new-a) (== q-b new-b))
       ((conde
	 ((fresh (bit bs) (== r-a `(,bit . ,bs))))
	 ((fresh (bit bs) (== r-b `(,bit . ,bs)))))
	(sub1o c c-1)
	(gcf a b c-1 f new-a new-b)))))))
|#




(defrel simplifyo (n o)
  (conde
   ((integerpo n) (== n o))
   ((fresh (sgn d)
	   (== n `(INTERNAL-NUMBER (RATIONAL)
				   (INTERNAL-NUMBER (,sgn))
				   ,d))
	   (== o '(INTERNAL-NUMBER (0)))))
   ((fresh (numer n-sgn denom d-sgn quot rem sgn)
	   (== n `(INTERNAL-NUMBER (RATIONAL)
				   (INTERNAL-NUMBER (,n-sgn) . ,numer)
				   (INTERNAL-NUMBER (,d-sgn) . ,denom)))
	   (new-sign n-sgn d-sgn sgn)
	   (fresh (bit bs min new-n new-m)
		  (== rem `(,bit . ,bs))
		  (find-min numer denom min)
		  (do-simp numer denom min new-n new-m)
		  (conde
		   ((== new-m '(1))
		    (== o `(INTERNAL-NUMBER (,sgn) . ,new-n)))
		   ((fresh (bit1 bit2 bs)
			   (== new-m `(,bit1 ,bit2 . ,bs)))
		    (== o `(INTERNAL-NUMBER (RATIONAL)
					    (INTERNAL-NUMBER (,sgn) . ,new-n)
					    (INTERNAL-NUMBER (0) . ,new-m))))))))))

(defmacro test-simp (n)
  `(read-back-num (car (run 1 q (simplifyo (build-num ,n) q)))))


;; helper functions for dealing with rationals
(defrel coerce-to-rational (n o)
  (conde
   ((rationalp-exclu n) (== n o))
   ((integerpo n) (== o `(INTERNAL-NUMBER (RATIONAL) ,n
				     (INTERNAL-NUMBER (0) 1))))))

(defrel negate (n n-)
  (fresh (sgn e)
    (== n `(INTERNAL-NUMBER (,sgn) . ,e))
    (conde
     ((== sgn 0) (== n- `(INTERNAL-NUMBER (1) . ,e)))
     ((== sgn 1) (== n- `(INTERNAL-NUMBER (0) . ,e)))
     ((== sgn 'RATIONAL)
      (fresh (num denom num-)
	     (== e `(,num ,denom))
	     (negate num num-)
	     (== n- `(INTERNAL-NUMBER (RATIONAL) ,num- ,denom)))))))

(defrel numeratoro (n o)
  (conde
   ((integerpo n) (== o n))
   ((fresh (denom)
	   (== n `(INTERNAL-NUMBER (RATIONAL) ,o ,denom))))))

(defrel denominatoro (n o)
  (conde
   ((integerpo n) (== o '(INTERNAL-NUMBER (0) 1)))
   ((fresh (numer) (== n `(INTERNAL-NUMBER (RATIONAL) ,numer ,o))))))

;; The arithmetic operations: zerop, numberp, +, -, *, /, sqr

(defrel do-pluso-with-rationals (n m o)
  (fresh (new-n new-m)
    (coerce-to-rational n new-n)
    (coerce-to-rational m new-m)
    (fresh (n-num n-denom m-num m-denom cast-n cast-m C NUM)
      (numeratoro new-n n-num) (denominatoro new-n n-denom)
      (numeratoro new-m m-num) (denominatoro new-m m-denom)
      (do-timeso n-denom m-denom C)
      (do-timeso n-denom m-num cast-m)
      (do-timeso m-denom n-num cast-n)
      (do-pluso cast-m cast-n NUM)
      (simplifyo `(INTERNAL-NUMBER (RATIONAL) ,NUM ,C) o))))

(defrel do-pluso (n m o)
  (fresh (a a-tag b b-tag c c-tag)
	 (== n `(INTERNAL-NUMBER (,a-tag) . ,a))
	 (== m `(INTERNAL-NUMBER (,b-tag) . ,b))
	 (== o `(INTERNAL-NUMBER (,c-tag) . ,c))
	 (conde
	  ((== a-tag 0) (== b-tag 0) (== c-tag 0) (pluso a b c))
	  ((== a-tag 1) (== b-tag 1) (== c-tag 1) (poso c) (pluso a b c))
	  ((== a-tag 1) (== b-tag 0) (== c-tag 1) (poso c) (minuso a b c))
	  ((== a-tag 0) (== b-tag 1) (== c-tag 0) (minuso a b c))
	  ((== a-tag 0) (== b-tag 1) (== c-tag 1) (poso c) (minuso b a c))
	  ((== a-tag 1) (== b-tag 0) (== c-tag 0) (minuso b a c))
	  ((== a-tag 'RATIONAL) (conde ((== b-tag 1)) ((== b-tag 0)))
	   (do-pluso-with-rationals n m o))
	  ((== b-tag 'RATIONAL) (conde ((== a-tag 1)) ((== a-tag 0)))
	   (do-pluso-with-rationals n m o))
	  ((== a-tag 'RATIONAL) (== b-tag 'RATIONAL)
	   (do-pluso-with-rationals n m o)))))

(defrel do-minuso (n m o)
  (fresh (m-) (negate m m-) (do-pluso n m- o)))

(defrel do-timeso-with-rationals (n m o)
  (fresh (new-n new-m)
    (coerce-to-rational n new-n)
    (coerce-to-rational m new-m)
    (fresh (n-num n-denom m-num m-denom NUM DENOM)
      (numeratoro new-n n-num) (denominatoro new-n n-denom)
      (numeratoro new-m m-num) (denominatoro new-m m-denom)
      (do-timeso n-num m-num NUM)
      (do-timeso n-denom m-denom DENOM)
      (simplifyo `(INTERNAL-NUMBER (RATIONAL) ,NUM ,DENOM) o))))

(defrel do-timeso (n m o)
  (fresh (a a-tag b b-tag c c-tag)
    (== n `(INTERNAL-NUMBER (,a-tag) . ,a))
    (== m `(INTERNAL-NUMBER (,b-tag) . ,b))
    (== o `(INTERNAL-NUMBER (,c-tag) . ,c))
    (conde
     ((== a-tag 0) (== b-tag 0) (== c-tag 0) (*o a b c))
     ((== a-tag 1) (== b-tag 1) (== c-tag 0) (*o a b c))
     ((== a-tag 0) (== b-tag 1) (*o a b c)
      (conde ((== c '()) (== c-tag 0))
	     ((poso c) (== c-tag 1))))
     ((== a-tag 1) (== b-tag 0) (*o a b c)
      (conde ((== c '()) (== c-tag 0))
	     ((poso c) (== c-tag 1))))
     ((== a-tag 'RATIONAL) (conde ((== b-tag 1)) ((== b-tag 0)))
      (do-timeso-with-rationals n m o))
     ((== b-tag 'RATIONAL) (conde ((== a-tag 1)) ((== a-tag 0)))
      (do-timeso-with-rationals n m o))
     ((== a-tag 'RATIONAL) (== b-tag 'RATIONAL)
      (do-timeso-with-rationals n m o)))))

(defrel do-sqro (n o) (do-timeso n n o))

(defrel do-expto (n pow o)
  (conde
   ((zeropo pow) (== o '(INTERNAL-NUMBER (0) 1)))
   ((pospo pow)
    (fresh (pow-1 r)
	   (do-pluso '(INTERNAl-NUMBER (0) 1) pow-1 pow)
	   (do-expto n pow-1 r)
	   (do-timeso n r o)))))


;;; less than and leq as pure goals
;;; they assume that the numbers provided are simplified 

(defrel do-less-than-o-with-rationals (n m)
  (fresh (new-n new-m n-num n-denom m-num m-denom cast-n cast-m)
    (coerce-to-rational n new-n)
    (coerce-to-rational m new-m)
    (numeratoro new-n n-num) (denominatoro new-n n-denom)
    (numeratoro new-m m-num) (denominatoro new-m m-denom)
    (do-timeso n-num m-denom cast-n)
    (do-timeso m-num n-denom cast-m)
    (do-less-than-o cast-n cast-m)))

(defrel do-less-than-o (n m)
  (fresh (n-sgn n- m-sgn m-)
    (== n `(INTERNAL-NUMBER (,n-sgn) . ,n-))
    (== m `(INTERNAL-NUMBER (,m-sgn) . ,m-))
    (conde
     ((== n-sgn 1) (== m-sgn 0))
     ((== n-sgn 0) (== m-sgn 0) (<o n- m-))
     ((== n-sgn 1) (== m-sgn 1) (<o m- n-))
     ((== n-sgn 'RATIONAL)
      (conde ((== m-sgn 0)) ((== m-sgn 1)))
      (do-less-than-o-with-rationals n m))
     ((== m-sgn 'RATIONAL)
      (conde ((== n-sgn 0)) ((== n-sgn 1)))
      (do-less-than-o-with-rationals n m))
     ((== n-sgn 'RATIONAL) (== m-sgn 'RATIONAL)
      (do-less-than-o-with-rationals n m)))))

(defrel do-less-than-equal-o (n m)
  (conde ((== n m))
	 ((do-less-than-o n m))))

(defrel do-greater-than-o (n m)
  (do-less-than-o m n))

(defrel do-greater-than-equal-o (n m)
  (do-less-than-equal-o m n))

;; versions that return t and nil
(defrel do-less-than-o-fn (n m o)
  (conde
   ((do-less-than-o n m) (== o 't))
   ((do-less-than-equal-o m n) (== o 'nil))))

(defrel do-less-than-equal-o-fn (n m o)
  (conde
   ((do-less-than-equal-o n m) (== o 't))
   ((do-less-than-o m n) (== o 'nil))))

(defrel do-greater-than-o-fn (n m o)
  (conde
   ((do-less-than-o m n) (== o 't))
   ((do-less-than-equal-o n m) (== o 'nil))))

(defrel do-greater-than-equal-o-fn (n m o)
  (conde
   ((do-less-than-equal-o m n) (== o 't))
   ((do-less-than-o n m) (== o 'nil))))


;;;;;;;;;;;;;;;;;;
;; String library (and characters)

(defun build-string-inner (str)
  (cond
   ((equal str "") '())
   (t (cons (char str 0)
	    (build-string-inner (subseq str 1))))))

(defun build-string (str)
  `(INTERNAL-STRING . ,(build-string-inner str)))

(defun read-back-string (str)
  (cond
   ((equal str '()) "")
   (t (concatenate 'string
		   (make-string 1 :initial-element (car str))
		   (read-back-string (cdr str))))))


(defun build-char (c)
  `(INTERNAL-CHAR ,c))

;; relations
(defrel stringpo (str)
  (fresh (s^)
	 (== str `(INTERNAL-STRING . ,s^))))

(defrel stringpo-fn (str o)
  (conde
   ((stringpo str) (== o t))
   ((charpo str) (== o nil))
   ((numberpo str) (== o nil))
   ((symbolpo str) (== o nil))
   ((booleanpo str) (== o nil))
   ((conspo str) (== o nil))))

(defrel charpo (c)
  (fresh (c^)
	 (== c `(INTERNAL-CHAR ,c^))))

(defrel charpo-fn (c o)
  (conde
   ((stringpo c) (== o nil))
   ((charpo c) (== o t))
   ((numberpo c) (== o nil))
   ((symbolpo c) (== o nil))
   ((booleanpo c) (== o nil))
   ((conspo c) (== o nil))))

;; concatenate
(defrel concato (s1 s2 o)
  (fresh (a b c)
    (== s1 `(INTERNAL-STRING . ,a))
    (== s2 `(INTERNAL-STRING . ,b))
    (== o `(INTERNAL-STRING . ,c))
    (concato-inner a b c)))

(defrel concato-inner (s1 s2 o)
  (conde
   ((== s1 '()) (== s2 o))
   ((fresh (c1 d r)
      (== s1 `(,c1 . ,d))
      (== o `(,c1 . ,r))
      (concato-inner d s2 r)))))

;; length
(defrel str-leno (st n)
  (fresh (str num)
    (== st `(INTERNAL-STRING . ,str))
    (== n `(INTERNAL-NUMBER (0)  . ,num))
    (str-leno-inner str num)))

(defrel str-leno-inner (str num)
  (conde
   ((== str '()) (== num '()))
   ((fresh (c1 d r)
      (== str `(,c1 . ,d))
      (str-leno-inner d r)
      (pluso '(1) r num)))))

;; reverse

(defrel str-revo (st r)
  (fresh (str rev)
    (== st `(INTERNAL-STRING . ,str))
    (== r `(INTERNAL-STRING . ,rev))
    (str-revo-inner str '()  rev)))

(defrel str-revo-inner (st a r)
  (conde
   ((== st '()) (== a r))
   ((fresh (c d)
	   (== st `(,c . ,d))
	   (str-revo-inner d `(,c . ,a) r)))))

;; subseq

(defrel subseqo (str start end o)
  (fresh (a n m r)
    (== str `(INTERNAL-STRING . ,a))
    (== start `(INTERNAL-NUMBER (0) . ,n))
    (== end `(INTERNAL-NUMBER (0) . ,m))
    (== o `(INTERNAL-STRING . ,r))
    (<o n m)
    (subseqo-inner a n m '() r)))

;; variant with 1 argument
(defrel subseqo1 (str start o)
  (fresh (n)
    (str-leno str n)
    (subseqo str start n o)))

(defrel subseqo-inner (str start end i o)
  (conde
   ((== str '()) (== o '()))
   ((fresh (a d i+1)
      (== str `(,a . ,d))
      (pluso '(1) i i+1)
      (conde
       ((== end i) (== o '()))
       ((<o i end)
	(conde
	 ((<o i start) (subseqo-inner d start end i+1 o))
	 ((<=o start i)
	  (fresh (r)
	    (== o `(,a . ,r))
	    (subseqo-inner d start end i+1 r))))))))))





