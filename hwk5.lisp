#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 5.
 Due: 3/12 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 5".

 The group members are:

 ... (put the names of the group members here)
 
 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. acl2s-compute is the form you use
 when you are using ACL2s to compute something, e.g., running a
 function on some input. acl2s-query is the form you use when you are
 querying ACL2s, e.g., a property without a name. If the property has
 a name, then that is not a query, but an event and you have to use
 acl2s-event.

 (acl2s-compute '(+ 1 2))
 (acl2s-query '(property (p q :all)
                 (iff (=> p q)
                      (v (! p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)

(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))

(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))

#|
 
 Here is the definition of a propositional formula. 
 
|#

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|
 
 Notice that in addition to propositional variables, we allow atoms
 such as (foo x). 

 Here are some assertions (see the common lisp manual).
 
|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#

(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))

#|

 Here are some examples you can try.

(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(xor p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name f) "ACL2S"))
      ((cons x xs)
       (if (in x '(iff xor))
           (nary-to-2ary x xs)
         (mapcar #'to-acl2s f)))
      (_ f))))

(to-acl2s '(and a b c d))
(to-acl2s '(iff a b c d))
(to-acl2s '(xor a b c d))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))
(pvars '(if p q (or r (foo t s) (and (not q)))))

(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))

(boolean-hyps '(p q r))

(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
	 (pvars (pvars siff))
	 (aiff (to-acl2s siff))
         (af (second aiff))
         (ag (third aiff))
         (bhyps (boolean-hyps pvars)))
    (acl2s-query
     `(acl2s::property ,bhyps (acl2s::iff ,af ,ag)))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (== (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)

#|

; This will lead to an error. Try it.
; In sbcl :top gets you out of the debugger.
(assert-acl2s-equal 'p 'q)

|#

; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|
 
 Question 1. (25 pts)

 Define function, p-simplify that given a propositional formula
 returns an equivalent propositional formula with the following
 properties. 

 A. The skeleton of the returned formula is either a constant or does
 not include any constants. For example:

 (and p t (foo t nil) q) should be simplified to (and p (foo t nil) q)
 (and p t (foo t b) nil) should be simplified to nil

 B. Flatten expressions, e.g.:

 (and p q (and r s) (or u v)) is not flat, but this is
 (and p q r s (or u v))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t. 

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain
 
 (not (not f))
 (not (iff ...))
 (not (xor ...))

 E. Apply Shannon expansions in 61-67.

 For example

 (and (or p q) (or r q p) p) should be simplified to

 p because (and (or t q) (or r q t) p) is (and t t p) is p

 F. Simplify formulas so that no subexpressions of the form

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or x y (foo a b) z (not (foo a b)) w) should be simplified to 

 t 

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. Such considerations are important
 when you use Tseitin, because experience has shown that even
 transformations such as NNF are usually a bad idea when generating
 CNF, as they tend to result in CNF formulas that take modern solvers
 longer to analyze.

 Test your definition with assert-acl2s-equal using at least 10
 propositional formulas that include non-variable atoms, all of the
 operators, deeply nested formulas, etc.

 
|#

; SIMPLIFICATIONS AND FLATTENING AND SINK -----------------------

; helpers

(defun flatten-args (op args)
  (when (or (== op 'and) (== op 'or) (== op 'iff) (== op 'xor))
    (reduce #'append
            (mapcar #'(lambda (a)
			(if (and (consp a) (== (car a) op))
                            (flatten-args op (cdr a))
                            (list a)))
                    args))))

(defun count-nots (f num)
  (if (and (consp f) (== (car f) 'not))
      (count-nots (cadr f) (+ 1 num))
      (list f (oddp num))))

(defun odd-num-nil (f arg num)
  (if (endp f)
      (oddp num)
      (if (== (car f) arg)
	  (odd-num-nil (cdr f) arg (+ 1 num))
	  (odd-num-nil (cdr f) arg num))))

(defun negate-non-const (args)
  (if (endp args)
      nil
      (let ((a (car args)))
	(if (booleanp a)
            (cons a (negate-non-const (cdr args)))
            (cons `(not ,a) (cdr args))))))

(defun negate (f)
  (cond ((== f t) nil)
        ((== f nil) t)
        (t `(not ,f))))

(defun complement-lit (x)
  (if (and (consp x) (== (car x) 'not) (== (len x) 2))
      (cadr x)
      `(not ,x)))

(defun any-complement-p (lst)
  (some #'(lambda (x) (in (complement-lit x) lst)) lst))

(defun remove-complements (lst)
  (let ((result nil)
        (count 0))
    (dolist (x lst)
      (let ((comp (complement-lit x)))
        (if (member comp result :test #'equal)
            (progn
              (setf result (remove comp result :test #'equal :count 1))
              (incf count))
            (push x result))))
    (cons (reverse result) count)))

(defun remove-dup-pairs (lst)
  (let ((result nil))
    (dolist (x lst)
      (if (member x result :test #'equal)
          (setf result (remove x result :test #'equal :count 1))
          (push x result)))
    (reverse result)))

; simplify functions

(defun simplify-and (f)
  (when (and (consp f) (== (car f) 'and))
    (cond ((endp (cdr f)) t)
          ((== (len (cdr f)) 1) (cadr f))
          (t (let* ((flat-f (flatten-args 'and (cdr f)))
                    (clean (remove-dups (remove t flat-f))))
               (cond ((in nil flat-f) nil)
                     ((any-complement-p clean) nil)
                     ((endp clean) t)
                     ((== (len clean) 1) (car clean))
                     (t (cons 'and clean))))))))
		     
(defun simplify-or (f)
  (when (and (consp f) (== (car f) 'or))
    (cond ((endp (cdr f)) nil)
          ((== (len (cdr f)) 1) (cadr f))
          (t (let* ((flat-f (flatten-args 'or (cdr f)))
                    (clean (remove-dups (remove nil flat-f))))
               (cond ((in t flat-f) t)
                     ((any-complement-p clean) t)
                     ((endp clean) nil)
                     ((== (len clean) 1) (car clean))
                     (t (cons 'or clean))))))))

(defun simplify-not (f)
  (when (and (consp f) (== (car f) 'not))
    (let* ((result (count-nots f 0))
           (inner (car result))
           (oddp-num (cadr result)))
      (cond ((== inner t)   (if oddp-num nil t))
            ((== inner nil) (if oddp-num t nil))
            ((and oddp-num (consp inner) (== (car inner) 'iff))
             (cons 'iff (negate-non-const (cdr inner))))
            ((and oddp-num (consp inner) (== (car inner) 'xor))
             (cons 'xor (negate-non-const (cdr inner))))
            (oddp-num `(not ,inner))
            (t inner)))))

(defun simplify-implies (f)
  (when (and (consp f) (== (car f) 'implies))
    (let ((first (cadr f))
          (second (caddr f)))
      (cond ((== first t) second)
            ((== first nil) t)
            ((== second t) t)
            ((== second nil) `(not ,first))
            ((equal second (complement-lit first)) second)
            (t f)))))

(defun simplify-iff (f)
  (when (and (consp f) (== (car f) 'iff))
    (cond ((endp (cdr f)) t)
          ((== (len (cdr f)) 1) (cadr f))
          (t (let* ((flat-f (flatten-args 'iff (cdr f)))
                    (deduped (remove-dup-pairs flat-f))
                    (comp-result (remove-complements deduped))
                    (comp-args (car comp-result))
                    (comp-count (cdr comp-result))
                    (with-nils (if (> comp-count 0)
                                   (append (make-list comp-count :initial-element nil)
                                           comp-args)
                                   comp-args))
                    (simp-f (remove t with-nils))
                    (simp-f-nil (remove nil simp-f))
                    (result (if (odd-num-nil simp-f nil 0)
                                (negate-non-const simp-f-nil)
				simp-f-nil)))
               (cond ((endp result) t)
                     ((== (len result) 1) (car result))
                     (t (cons 'iff result))))))))

(defun simplify-xor (f)
  (when (and (consp f) (== (car f) 'xor))
    (cond ((endp (cdr f)) nil)
          ((== (len (cdr f)) 1) (cadr f))
          (t (let* ((flat-f (flatten-args 'xor (cdr f)))
                    (deduped (remove-dup-pairs flat-f))
                    (comp-result (remove-complements deduped))
                    (comp-args (car comp-result))
                    (comp-count (cdr comp-result))
                    (with-ts (if (> comp-count 0)
                                 (append (make-list comp-count :initial-element t)
                                         comp-args)
                                 comp-args))
                    (simp-f (remove nil with-ts))
                    (simp-f-t (remove t simp-f))
                    (result (cond ((endp simp-f-t) nil)
                                  ((== (len simp-f-t) 1) (car simp-f-t))
                                  (t (cons 'xor simp-f-t)))))
               (if (odd-num-nil simp-f t 0)
                   (negate result)
                   result))))))

	       
(defun simplify-if (f)
  (when (and (consp f) (== (car f) 'if))
    (cond ((== (cadr f) t) (caddr f))
          ((== (cadr f) nil) (cadddr f))
          (t f))))

(defun simplify (f)
  (match f
      ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
     (if (p-funp op)
	 (cond ((== op 'and) (simplify-and f))
	       ((== op 'or) (simplify-or f))
	       ((== op 'not) (simplify-not f))
	       ((== op 'implies) (simplify-implies f))
	       ((== op 'iff) (simplify-iff f))
	       ((== op 'xor) (simplify-xor f))
	       ((== op 'if) (simplify-if f))
	       (t nil))
	 nil))
    (_ f)))

; SHANNON ----------------------------------------------------

(defun literalp (x)
  (or (and (symbolp x) (not (booleanp x)))
      (and (consp x)
           (== (car x) 'not)
           (== (len x) 2)
           (symbolp (cadr x))
           (not (booleanp (cadr x))))))

(defun get-literals (f)
  (match f
      ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (if (p-funp op)
         (remove-dups (remove-if-not #'literalp args))
	 nil))
    (_ nil)))

(defun literal-var (lit)
  (if (symbolp lit) lit (cadr lit)))

(defun p-subst (f var val)
  (match f
      ((type boolean) f)
    ((type symbol) (if (== f var) val f))
    ((list* op args)
     (if (p-funp op)
	 (cons op (mapcar #'(lambda (a) (p-subst a var val)) args))
	 f))
    (_ f)))

(defun shannon-subst-val (op lit)
  (let ((pos (symbolp lit)))
    (cond
      ((== op 'and) (if pos t nil))        
      ((== op 'or)  (if pos nil t))        
      (t nil))))

(defun shannon-reduce-args (op remaining seen)
  (if (endp remaining)
      (reverse seen)
    (let ((a (car remaining))
          (rest (cdr remaining)))
      (if (literalp a)
          (let* ((var (literal-var a))
                 (val (shannon-subst-val op a))
                 (new-seen (mapcar #'(lambda (s) (p-subst s var val)) seen))
                 (new-rest (mapcar #'(lambda (r) (p-subst r var val)) rest)))
            (shannon-reduce-args op new-rest (cons a new-seen)))
        (shannon-reduce-args op rest (cons a seen))))))

(defun literal-val (lit)
  (if (symbolp lit) t nil))

(defun subst-literals-true (f lits)
  (reduce #'(lambda (acc lit)
              (p-subst acc (literal-var lit) (literal-val lit)))
          lits :initial-value f))

(defun subst-literals-false (f lits)
  (reduce #'(lambda (acc lit)
              (p-subst acc (literal-var lit) (if (symbolp lit) nil t)))
          lits :initial-value f))

(defun shannon-reduce-implies (f)
  (let ((ante (cadr f))
        (conseq (caddr f)))
    (let* ((ante-lits (cond ((literalp ante) (list ante))
                            ((and (consp ante) (== (car ante) 'and))
                             (remove-if-not #'literalp (cdr ante)))
                            (t nil)))
           (new-conseq (subst-literals-true conseq ante-lits))
           (conseq-lits (if (literalp new-conseq) (list new-conseq) nil))
           (new-ante (subst-literals-false ante conseq-lits)))
      `(implies ,new-ante ,new-conseq))))

; rules 61-67
(defun shannon-reduce (f)
  (match f
    ((list* op args)
     (cond ((in op '(and or))
            (cons op (shannon-reduce-args op args nil)))
           ((== op 'implies)
            (shannon-reduce-implies f))
           (t f)))
    (_ f)))

(defparameter *no-simplification* (gensym "NO-SIMP"))

(defun try-simplify (op f)
  (let ((result (cond ((== op 'and)     (simplify-and f))
                      ((== op 'or)      (simplify-or f))
                      ((== op 'not)     (simplify-not f))
                      ((== op 'implies) (simplify-implies f))
                      ((== op 'iff)     (simplify-iff f))
                      ((== op 'xor)     (simplify-xor f))
                      ((== op 'if)      (simplify-if f))
                      (t *no-simplification*))))
    (if (== result nil)
	(if (and (consp f) (== (car f) op)) nil *no-simplification*)
	(if result result *no-simplification*))))

(defun simplify-step (f)
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
     (if (p-funp op)
         (let ((result (try-simplify op f)))
           (if (== result *no-simplification*) f result))
       f))
    (_ f)))

(defun p-simplify-args (args)
  (mapcar #'p-simplify args))

(defun p-simplify (f)
  (match f
      ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
     (if (p-funp op)
         (let* ((simplified-args (p-simplify-args args))
                (rebuilt (cons op simplified-args))
                (after-shannon (shannon-reduce rebuilt))
                (after-shannon-simp
                 (match after-shannon
                     ((list* sop sargs)
                      (if (p-funp sop)
                          (cons sop (p-simplify-args sargs))
			  after-shannon))
                   (_ after-shannon)))
                (result (simplify-step after-shannon-simp)))
           (if (equal result rebuilt)
               result
               (p-simplify result)))
	 f))
    (_ f)))

(assert-acl2s-equal (p-simplify '(and p (and q t) nil)) nil)
(assert-acl2s-equal (p-simplify '(not (not (and p t)))) 'p)
(assert-acl2s-equal (p-simplify '(and (or p q) (or r q p) p)) 'p)
(assert-acl2s-equal (p-simplify '(not (iff p q r))) '(iff (not p) q r))
(assert-acl2s-equal (p-simplify '(not (not (not (xor a b))))) '(xor (not a) b))
(assert-acl2s-equal (p-simplify '(xor a (xor a b))) 'b)
(assert-acl2s-equal (p-simplify '(or x (foo a b) (not x) y)) t)
(assert-acl2s-equal (p-simplify '(and (not (not p)) (or q nil) (and r (and s t)))) '(and p q r s))
(assert-acl2s-equal (p-simplify '(implies p (and p q))) '(implies p q))
(assert-acl2s-equal (p-simplify '(implies (and p q) (or (not p) r))) '(implies (and p q) r))
(assert-acl2s-equal (p-simplify '(implies (or a b) a)) '(implies b a))
(assert-acl2s-equal (p-simplify '(iff (iff a b) (iff b c))) '(iff a c))
(assert-acl2s-equal (p-simplify '(xor p (not p))) t)
(assert-acl2s-equal (p-simplify '(or (and p q) (or (not p) r) (not p))) '(or q r (not p)))
(assert-acl2s-equal (p-simplify '(and (not (not x)) (and t y) (or x (foo a b)) x)) '(and x y))

#|

 Question 2. (20 pts)

 Define tseitin, a function that given a propositional formula,
 something that satisfies p-formulap, applies the tseitin
 transformation to generate a CNF formula that is equi-satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 You should simplify the formula first, using p-simplify, but do not
 perform any other simplifications. Any simpification you want to
 perform must be done in p-simplify.

 Test tseitin using with assert-acl2s-equal using at least 10
 propositional formulas.

|#

; collect all symbols deeply from a formula
(defun collect-all-symbols (f)
  (cond
    ((null f) nil)
    ((symbolp f)
     (if (member f '(and or not implies iff xor if true false))
         nil
	 (list f)))
    ((consp f)
     (remove-dups
      (reduce #'append
              (mapcar #'collect-all-symbols f)
              :initial-value nil)))
    (t nil)))

(defun get-next-avail-const-name-help (used n)
  (let ((candidate (intern (format nil "C~A" n))))
    (if (member candidate used)
        (get-next-avail-const-name-help used (1+ n))
      (values candidate (1+ n)))))

; generate CNF clauses for: tv <=> (op args...)
(defun gen-clauses (tv op args used n)
  (cond
    ((== op 'not)
     (let ((a (car args)))
       (values (list `(or ,(negate tv) ,(negate a))
                     `(or ,tv ,a))
               used n)))
    ((== op 'and)
     (values
      (append
       (mapcar #'(lambda (a) `(or ,(negate tv) ,a)) args)
       (list (cons 'or (cons tv (mapcar #'negate args)))))
      used n))
    ((== op 'or)
     (values
      (append
       (mapcar #'(lambda (a) `(or ,tv ,(negate a))) args)
       (list (cons 'or (cons (negate tv) args))))
      used n))
    ((== op 'implies)
     (let ((a (first args)) (b (second args)))
       (values (list `(or ,(negate tv) ,(negate a) ,b)
                     `(or ,tv ,a)
                     `(or ,tv ,(negate b)))
               used n)))
    ((== op 'iff)
     (if (<= (len args) 2)
         (let ((a (first args)) (b (second args)))
           (values (list `(or ,(negate tv) ,(negate a) ,b)
                         `(or ,(negate tv) ,a ,(negate b))
                         `(or ,tv ,(negate a) ,(negate b))
                         `(or ,tv ,a ,b))
                   used n))
	 (gen-nary-chain tv 'iff args used n)))
    ((== op 'xor)
     (if (<= (len args) 2)
         (let ((a (first args)) (b (second args)))
           (values (list `(or ,(negate tv) ,a ,b)
                         `(or ,(negate tv) ,(negate a) ,(negate b))
                         `(or ,tv ,(negate a) ,b)
                         `(or ,tv ,a ,(negate b)))
                   used n))
	 (gen-nary-chain tv 'xor args used n)))
    ((== op 'if)
     (let ((a (first args)) (b (second args)) (c (third args)))
       (values (list `(or ,(negate a) ,(negate tv) ,b)
                     `(or ,(negate a) ,tv ,(negate b))
                     `(or ,a ,(negate tv) ,c)
                     `(or ,a ,tv ,(negate c)))
               used n)))
    (t (error "Unknown operator in gen-clauses: ~a" op))))

; handle n-ary iff/xor by chaining into binary with intermediate vars
(defun gen-nary-chain (tv op args used n)
  (if (<= (len args) 2)
      (gen-clauses tv op args used n)
    (multiple-value-bind (intermediate new-n)
        (get-next-avail-const-name-help used n)
      (let ((new-used (cons intermediate used)))
        (multiple-value-bind (first-clauses used2 n2)
            (gen-clauses intermediate op
                        (list (first args) (second args))
                        new-used new-n)
          (multiple-value-bind (rest-clauses used3 n3)
              (gen-nary-chain tv op (cons intermediate (cddr args)) used2 n2)
            (values (append first-clauses rest-clauses) used3 n3)))))))

; walk formula tree bottom-up, assigning tseitin variables
(defun tseitin-walk-args (args clauses amap used n acc)
  (if (endp args)
      (values (reverse acc) clauses amap used n)
    (multiple-value-bind (var new-clauses new-amap new-used new-n)
        (tseitin-walk (car args) clauses amap used n)
      (tseitin-walk-args (cdr args) new-clauses new-amap new-used new-n
                         (cons var acc)))))

(defun tseitin-walk (f clauses amap used n)
  (cond
    ((booleanp f) (values f clauses amap used n))
    ((symbolp f) (values f clauses amap used n))
    ((and (consp f) (p-funp (car f)))
     (let ((op (car f))
           (args (cdr f)))
       (multiple-value-bind (child-vars new-clauses new-amap new-used new-n)
           (tseitin-walk-args args clauses amap used n nil)
         (multiple-value-bind (tv next-n)
             (get-next-avail-const-name-help new-used new-n)
           (let ((updated-used (cons tv new-used)))
             (multiple-value-bind (op-clauses final-used final-n)
                 (gen-clauses tv op child-vars updated-used next-n)
               (values tv
                       (append new-clauses op-clauses)
                       new-amap
                       final-used
                       final-n)))))))
    ((consp f)
     (let ((existing (key-alist->val f amap)))
       (if existing
           (values existing clauses amap used n)
           (multiple-value-bind (pv next-n)
               (get-next-avail-const-name-help used n)
             (values pv clauses (acons f pv amap)
                     (cons pv used) next-n)))))
    (t (error "Unexpected formula in tseitin-walk: ~a" f))))

(defun tseitin (f)
  (let ((simp (p-simplify f)))
    (if (booleanp simp)
        simp
      (let ((all-syms (remove-dups (collect-all-symbols simp))))
        (multiple-value-bind (top-var clauses)
            (tseitin-walk simp nil nil all-syms 0)
          (cons 'and (cons `(or ,top-var) clauses)))))))


(assert-acl2s-equal
  (tseitin '(and (foo (if a b)) (not (foo (if a b)))))
  '(and (or C2)
        (or (not C1) (not C0)) (or C1 C0)
        (or (not C2) C0) (or (not C2) C1) (or C2 (not C0) (not C1))))
(assert-acl2s-equal
  (tseitin '(and C0 C1 (or C2 C3)))
  '(and (or C5)
        (or C4 (not C2)) (or C4 (not C3)) (or (not C4) C2 C3)
        (or (not C5) C0) (or (not C5) C1) (or (not C5) C4)
        (or C5 (not C0) (not C1) (not C4))))
(assert-acl2s-equal (tseitin '(or a t)) t)
(assert-acl2s-equal (tseitin '(and a nil)) nil)
(assert-acl2s-equal
  (tseitin '(not (not (not (not a)))))
  '(and (or a)))
(assert-acl2s-equal
  (tseitin '(or (bar x y) (not (bar x y)))) t)
(assert-acl2s-equal
  (tseitin '(and (or (implies a b) (iff c d))
                 (xor (not e) (if f g h))))
  '(and (or C6)
        (or (not C0) (not a) b) (or C0 a) (or C0 (not b))
        (or (not C1) (not c) d) (or (not C1) c (not d))
        (or C1 (not c) (not d)) (or C1 c d)
        (or C2 (not C0)) (or C2 (not C1)) (or (not C2) C0 C1)
        (or (not C3) (not e)) (or C3 e)
        (or (not f) (not C4) g) (or (not f) C4 (not g))
        (or f (not C4) h) (or f C4 (not h))
        (or (not C5) C3 C4) (or (not C5) (not C3) (not C4))
        (or C5 (not C3) C4) (or C5 C3 (not C4))
        (or (not C6) C2) (or (not C6) C5)
        (or C6 (not C2) (not C5))))
(assert-acl2s-equal
  (tseitin '(xor a b c d e))
  '(and (or C0)
        (or (not C1) a b) (or (not C1) (not a) (not b))
        (or C1 (not a) b) (or C1 a (not b))
        (or (not C2) C1 c) (or (not C2) (not C1) (not c))
        (or C2 (not C1) c) (or C2 C1 (not c))
        (or (not C3) C2 d) (or (not C3) (not C2) (not d))
        (or C3 (not C2) d) (or C3 C2 (not d))
        (or (not C0) C3 e) (or (not C0) (not C3) (not e))
        (or C0 (not C3) e) (or C0 C3 (not e))))
(assert-acl2s-equal
  (tseitin '(implies (baz (and x y)) (quux (not z))))
  '(and (or C2)
        (or (not C2) (not C0) C1)
        (or C2 C0)
        (or C2 (not C1))))
(assert-acl2s-equal
  (tseitin '(iff a b c d))
  '(and (or C0)
        (or (not C1) (not a) b) (or (not C1) a (not b))
        (or C1 (not a) (not b)) (or C1 a b)
        (or (not C2) (not C1) c) (or (not C2) C1 (not c))
        (or C2 (not C1) (not c)) (or C2 C1 c)
        (or (not C0) (not C2) d) (or (not C0) C2 (not d))
        (or C0 (not C2) (not d)) (or C0 C2 d)))
(assert-acl2s-equal
  (tseitin '(and (or a nil) (implies t b)))
  '(and (or C0)
        (or (not C0) a) (or (not C0) b)
        (or C0 (not a) (not b))))

#|

 Question 3. (30 pts)

 Define DP, a function that given a propositional formula in CNF,
 applies the Davis-Putnam algorithm to determine if the formula is
 satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DP returns 'sat and a satisfying assignment: an
 alist mapping each atom in the formula to t/nil. Use values to return
 multiple values.

 If it is usat, return 'unsat.

 Do some profiling

 Test DP using with assert-acl2s-equal using at least 10
 propositional formulas. 

 It is easy to extend dp to support arbitrary formulas by using
 tseitin to generate CNF.

|#

; convert input CNF to list of clauses so just can play with the variables within 
(defun cnf-to-clauses (f)
  "Convert CNF formula to list-of-lists representation."
  (cond
    ((eq f t) nil)              
    ((eq f nil) (list nil))     
    ((and (consp f) (eq (car f) 'and))
     (mapcan #'(lambda (c)
                 (cond
                   ((eq c t) nil)           
                   ((eq c nil) (list nil))  
                   ((and (consp c) (eq (car c) 'or))
                    (list (cdr c)))
                   (t (list (list c)))))   
             (cdr f)))
    ((and (consp f) (eq (car f) 'or))
     (list (cdr f)))            
    (t (list (list f)))))      

(defun all-literals (clauses)
  (remove-duplicates (reduce #'append clauses :initial-value nil)
                     :test #'equal))

(defun all-vars (clauses)
  (remove-duplicates (mapcar #'lit-var (all-literals clauses))
                     :test #'equal))

(defun has-empty-clause-p (clauses)
  (member nil clauses :test #'equal))

; extract variable from literal 
(defun lit-var (lit)
  (if (and (consp lit) (eq (car lit) 'not) (= (length lit) 2))
      (cadr lit)
    lit))

; is literal positive?
(defun lit-positive-p (lit)
  (not (and (consp lit) (eq (car lit) 'not) (= (length lit) 2))))

; return complement of literal
(defun lit-negate (lit)
  (if (and (consp lit) (eq (car lit) 'not) (= (length lit) 2))
      (cadr lit)
    `(not ,lit)))

; sees if clause contain both ℓ and ¬ℓ for some ℓ
(defun tautological-p (clause)
  (some #'(lambda (lit)
            (member (lit-negate lit) clause :test #'equal))
        clause))


;;;;;; Pure Literal Rule ;;;;;;

; find literal whose complement doesnt appear
(defun find-pure-literal (clauses)
  (let ((lits (all-literals clauses)))
    (dolist (lit lits nil)
      (unless (member (lit-negate lit) lits :test #'equal)
	(return lit)))))

; repeatedly apply pure literal rule until no pure literals remain
(defun apply-pure-literal-rule (clauses assignment)
  (let ((pure (find-pure-literal clauses)))
    (if pure
        (let ((var (lit-var pure))
              (val (lit-positive-p pure)))
          (apply-pure-literal-rule
           (remove-if #'(lambda (c) (member pure c :test #'equal))
                      clauses)
           (acons var val assignment)))
	(values clauses assignment))))


;;;;;; BCP ;;;;;;

; return literal from unit clause, or nil
(defun find-unit-clause (clauses)
  (dolist (c clauses nil)
    (when (= (length c) 1)
      (return (car c)))))

; subsumption + unit resolution for literal lit
(defun propagate-literal (lit clauses)
  (let ((neg (lit-negate lit)))
    (mapcar #'(lambda (c) (remove neg c :test #'equal))
            (remove-if #'(lambda (c) (member lit c :test #'equal))
                       clauses))))

; repeatedly apply BCP
(defun bcp (clauses assignment)
  (let ((unit (find-unit-clause clauses)))
    (if unit
        (let ((var (lit-var unit))
              (val (lit-positive-p unit)))
          (bcp (propagate-literal unit clauses)
               (acons var val assignment)))
      (values clauses assignment))))


;;;;;; Resolution ;;;;;;

; splits clauses into P (positive), N (negative), E (rest). Clauses containing both var and (not var) are discarded
(defun partition-clauses (var clauses)
  (let ((pos var)
        (neg `(not ,var))
        (p nil) (n nil) (e nil))
    (dolist (c clauses)
      (let ((has-pos (member pos c :test #'equal))
            (has-neg (member neg c :test #'equal)))
        (cond
          ((and has-pos has-neg) nil)   ; discard
          (has-pos (push c p))
          (has-neg (push c n))
          (t       (push c e)))))
    (values p n e)))

(defun generate-resolvents (var p-clauses n-clauses)
  (let ((pos var)
        (neg `(not ,var))
        (resolvents nil))
    (dolist (pc p-clauses)
      (dolist (nc n-clauses)
        (let ((resolvent
               (remove-duplicates
                (append (remove pos pc :test #'equal)
                        (remove neg nc :test #'equal))
                :test #'equal)))
          (unless (tautological-p resolvent)
            (push resolvent resolvents)))))
    resolvents))

; picks a variable to resolve on, uses first variable in first clause
(defun choose-resolution-var (clauses)
  (lit-var (caar clauses)))


;;;;;; Reconstruct Solution ;;;;;;

; ensures clause satisfied by (partial) assignment
(defun clause-satisfied-p (clause assignment)
  (some #'(lambda (lit)
            (let* ((var (lit-var lit))
                   (pos (lit-positive-p lit))
                   (entry (assoc var assignment :test #'equal)))
              (and entry (eq (cdr entry) pos))))
        clause))

; extend assignment to assign resolved and remaining variables values
(defun reconstruct-assignment (assignment res-history original-vars)
  (dolist (step res-history)
    (let* ((var       (first step))
           (p-clauses (second step))
           (ci (mapcar #'(lambda (c) (remove var c :test #'equal))
                       p-clauses)))
      (if (every #'(lambda (c) (clause-satisfied-p c assignment)) ci)
          (push (cons var nil) assignment)    ; p = false suffices
          (push (cons var t) assignment))))     ; p = true needed
  (dolist (v original-vars)
    (unless (assoc v assignment :test #'equal)
      (push (cons v t) assignment)))
  assignment)


;;;;;; DP ;;;;;;

; apply bcp and pure literal rule until reach fixpoint
(defun bcp-and-pure-fixpoint (clauses assignment)
  (multiple-value-bind (cl1 asgn1) (bcp clauses assignment)
    (when (or (has-empty-clause-p cl1) (null cl1))
      (return-from bcp-and-pure-fixpoint (values cl1 asgn1)))
    (multiple-value-bind (cl2 asgn2) (apply-pure-literal-rule cl1 asgn1)
      (if (equal cl2 cl1)
          (values cl2 asgn2)          ; fixpoint reached
          (bcp-and-pure-fixpoint cl2 asgn2)))))

(defun dp-solve (clauses assignment res-history original-vars)
  ;  base case 1: empty clause derived = UNSAT
  (when (has-empty-clause-p clauses)
    (return-from dp-solve (values 'unsat nil)))
  ; base case 2: no clauses remain = SAT
  (when (null clauses)
    (return-from dp-solve
      (values 'sat (reconstruct-assignment assignment res-history
                                           original-vars))))
  ; BCP + Pure Literal to fixpoint
  (multiple-value-bind (fp-cl fp-asgn)
      (bcp-and-pure-fixpoint clauses assignment)
    (when (has-empty-clause-p fp-cl)
      (return-from dp-solve (values 'unsat nil)))
    (when (null fp-cl)
      (return-from dp-solve
        (values 'sat (reconstruct-assignment fp-asgn res-history
                                             original-vars))))
    ; Resolution
    (let ((var (choose-resolution-var fp-cl)))
      (multiple-value-bind (p n e)
          (partition-clauses var fp-cl)
        (let ((resolvents (generate-resolvents var p n)))
          (dp-solve (append e resolvents)
                    fp-asgn
                    (cons (list var p n) res-history)
                    original-vars))))))

(defun dp (f)
  (cond
    ((eq f t) (values 'sat nil))
    ((eq f nil) (values 'unsat nil))
    (t (let* ((clauses (cnf-to-clauses f))
              (vars (all-vars clauses)))
         (dp-solve clauses nil nil vars)))))

(assert
 (equal
  (multiple-value-list
   (dp '(and
         x1
         (or (not x1) x2)
         (or (not x2) x3)
         (or (not x3) x4)
         (or (not x4) x5)
         (or (not x5) x6)
         (or (not x6) x7)
         (or (not x7) x8))))
  '(sat ((x8 . t) (x7 . t) (x6 . t) (x5 . t)
         (x4 . t) (x3 . t) (x2 . t) (x1 . t)))))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         x1
         (or (not x1) x2)
         (or (not x2) x3)
         (or (not x3) x4)
         (or (not x4) x5)
         (or (not x5) x6)
         (or (not x6) x7)
         (or (not x7) x8)
         (not x8))))
  '(unsat nil)))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         (or a1 b1)
         (or a2 b2)
         (or a3 b3)
         (or a4 b4)
         (or a5 b5)
         (not b1)
         (not b2)
         (not b3)
         (not b4)
         (not b5))))
  '(sat ((a5 . t) (b5 . nil) (a4 . t) (b4 . nil) (a3 . t) (b3 . nil) (a2 . t) (b2 . nil) (a1 . t) (b1 . nil)))))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         (or c1 c2 c3 c4 c5)
         (or (not c1) (not c2))
         (or (not c1) (not c3))
         (or (not c1) (not c4))
         (or (not c1) (not c5))
         (or (not c2) (not c3))
         (or (not c2) (not c4))
         (or (not c2) (not c5))
         (or (not c3) (not c4))
         (or (not c3) (not c5))
         (or (not c4) (not c5))
         (not c1)
         (not c2)
         (not c3)
         (not c4)
         (not c5))))
  '(unsat nil)))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         (or v1r v1g v1b)
         (or v2r v2g v2b)
         (or v3r v3g v3b)
         (or v4r v4g v4b)

         (or (not v1r) (not v1g))
         (or (not v1r) (not v1b))
         (or (not v1g) (not v1b))
         (or (not v2r) (not v2g))
         (or (not v2r) (not v2b))
         (or (not v2g) (not v2b))
         (or (not v3r) (not v3g))
         (or (not v3r) (not v3b))
         (or (not v3g) (not v3b))
         (or (not v4r) (not v4g))
         (or (not v4r) (not v4b))
         (or (not v4g) (not v4b))

         (or (not v1r) (not v2r))
         (or (not v1g) (not v2g))
         (or (not v1b) (not v2b))
         (or (not v2r) (not v3r))
         (or (not v2g) (not v3g))
         (or (not v2b) (not v3b))
         (or (not v3r) (not v4r))
         (or (not v3g) (not v4g))
         (or (not v3b) (not v4b))

         v1r
         (not v2r)
         (not v2b)
         (not v3r)
         (not v3g)
         (not v4r)
         (not v4b))))
  '(sat ((v4g . t) (v4r) (v4b) (v3b . t) (v3r) (v3g) (v2g . t) (v2b) (v2r) (v1b) (v1g) (v1r . t)))))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         (or k1r k1g k1b)
         (or k2r k2g k2b)
         (or k3r k3g k3b)
         (or k4r k4g k4b)

         (or (not k1r) (not k1g))
         (or (not k1r) (not k1b))
         (or (not k1g) (not k1b))
         (or (not k2r) (not k2g))
         (or (not k2r) (not k2b))
         (or (not k2g) (not k2b))
         (or (not k3r) (not k3g))
         (or (not k3r) (not k3b))
         (or (not k3g) (not k3b))
         (or (not k4r) (not k4g))
         (or (not k4r) (not k4b))
         (or (not k4g) (not k4b))

         (or (not k1r) (not k2r))
         (or (not k1g) (not k2g))
         (or (not k1b) (not k2b))
         (or (not k1r) (not k3r))
         (or (not k1g) (not k3g))
         (or (not k1b) (not k3b))
         (or (not k1r) (not k4r))
         (or (not k1g) (not k4g))
         (or (not k1b) (not k4b))
         (or (not k2r) (not k3r))
         (or (not k2g) (not k3g))
         (or (not k2b) (not k3b))
         (or (not k2r) (not k4r))
         (or (not k2g) (not k4g))
         (or (not k2b) (not k4b))
         (or (not k3r) (not k4r))
         (or (not k3g) (not k4g))
         (or (not k3b) (not k4b)))))
  '(unsat nil)))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         a1
         b1
         (or (not a1) a2)
         (or (not a2) a3)
         (or (not a3) a4)
         (or (not b1) b2)
         (or (not b2) b3)
         (or (not b3) b4)
         (or (not a4) c1)
         (or (not b4) c2)
         (or (not c1) d)
         (or (not c2) d))))
  '(sat ((d . t) (c2 . t) (c1 . t) (b4 . t) (b3 . t) (b2 . t) (a4 . t) (a3 . t)
 (a2 . t) (b1 . t) (a1 . t)))))
(assert
 (equal
  (multiple-value-list
   (dp '(and
         a1
         b1
         (or (not a1) a2)
         (or (not a2) a3)
         (or (not a3) a4)
         (or (not b1) b2)
         (or (not b2) b3)
         (or (not b3) b4)
         (or (not a4) c)
         (or (not b4) c)
         (not c))))
  '(unsat nil)))
(assert
 (equal
  (multiple-value-list
   (dp '(and (or j1s1 j1s2 j1s3 j1s4) (or j2s1 j2s2 j2s3 j2s4) (or j3s1 j3s2 j3s3 j3s4) (or j4s1 j4s2 j4s3 j4s4)
         (or (not j1s1) (not j1s2)) (or (not j1s1) (not j1s3)) (or (not j1s1) (not j1s4)) (or (not j1s2) (not j1s3)) (or (not j1s2) (not j1s4)) (or (not j1s3) (not j1s4))
         (or (not j2s1) (not j2s2)) (or (not j2s1) (not j2s3)) (or (not j2s1) (not j2s4)) (or (not j2s2) (not j2s3)) (or (not j2s2) (not j2s4)) (or (not j2s3) (not j2s4))
         (or (not j3s1) (not j3s2)) (or (not j3s1) (not j3s3)) (or (not j3s1) (not j3s4)) (or (not j3s2) (not j3s3)) (or (not j3s2) (not j3s4)) (or (not j3s3) (not j3s4))
         (or (not j4s1) (not j4s2)) (or (not j4s1) (not j4s3)) (or (not j4s1) (not j4s4)) (or (not j4s2) (not j4s3)) (or (not j4s2) (not j4s4)) (or (not j4s3) (not j4s4))
         (or (not j1s1) (not j2s1)) (or (not j1s1) (not j3s1)) (or (not j1s1) (not j4s1)) (or (not j2s1) (not j3s1)) (or (not j2s1) (not j4s1)) (or (not j3s1) (not j4s1))
         (or (not j1s2) (not j2s2)) (or (not j1s2) (not j3s2)) (or (not j1s2) (not j4s2)) (or (not j2s2) (not j3s2)) (or (not j2s2) (not j4s2)) (or (not j3s2) (not j4s2))
         (or (not j1s3) (not j2s3)) (or (not j1s3) (not j3s3)) (or (not j1s3) (not j4s3)) (or (not j2s3) (not j3s3)) (or (not j2s3) (not j4s3)) (or (not j3s3) (not j4s3))
         (or (not j1s4) (not j2s4)) (or (not j1s4) (not j3s4)) (or (not j1s4) (not j4s4)) (or (not j2s4) (not j3s4)) (or (not j2s4) (not j4s4)) (or (not j3s4) (not j4s4))
         j1s1 j2s2 j3s3 j4s4)))
  '(sat ((j4s4 . t) (j4s3) (j3s4) (j3s3 . t) (j4s2) (j3s2) (j2s4) (j2s3) (j2s2 . t)
	 (j4s1) (j3s1) (j2s1) (j1s4) (j1s3) (j1s2) (j1s1 . t)))))

(assert
 (equal
  (multiple-value-list
   (dp '(and (or p1s1 p1s2 p1s3 p1s4) (or p2s1 p2s2 p2s3 p2s4) (or p3s1 p3s2 p3s3 p3s4) (or p4s1 p4s2 p4s3 p4s4) (or p5s1 p5s2 p5s3 p5s4)
         (or (not p1s1) (not p1s2)) (or (not p1s1) (not p1s3)) (or (not p1s1) (not p1s4)) (or (not p1s2) (not p1s3)) (or (not p1s2) (not p1s4)) (or (not p1s3) (not p1s4))
         (or (not p2s1) (not p2s2)) (or (not p2s1) (not p2s3)) (or (not p2s1) (not p2s4)) (or (not p2s2) (not p2s3)) (or (not p2s2) (not p2s4)) (or (not p2s3) (not p2s4))
         (or (not p3s1) (not p3s2)) (or (not p3s1) (not p3s3)) (or (not p3s1) (not p3s4)) (or (not p3s2) (not p3s3)) (or (not p3s2) (not p3s4)) (or (not p3s3) (not p3s4))
         (or (not p4s1) (not p4s2)) (or (not p4s1) (not p4s3)) (or (not p4s1) (not p4s4)) (or (not p4s2) (not p4s3)) (or (not p4s2) (not p4s4)) (or (not p4s3) (not p4s4))
         (or (not p5s1) (not p5s2)) (or (not p5s1) (not p5s3)) (or (not p5s1) (not p5s4)) (or (not p5s2) (not p5s3)) (or (not p5s2) (not p5s4)) (or (not p5s3) (not p5s4))
         (or (not p1s1) (not p2s1)) (or (not p1s1) (not p3s1)) (or (not p1s1) (not p4s1)) (or (not p1s1) (not p5s1)) (or (not p2s1) (not p3s1)) (or (not p2s1) (not p4s1)) (or (not p2s1) (not p5s1)) (or (not p3s1) (not p4s1)) (or (not p3s1) (not p5s1)) (or (not p4s1) (not p5s1))
         (or (not p1s2) (not p2s2)) (or (not p1s2) (not p3s2)) (or (not p1s2) (not p4s2)) (or (not p1s2) (not p5s2)) (or (not p2s2) (not p3s2)) (or (not p2s2) (not p4s2)) (or (not p2s2) (not p5s2)) (or (not p3s2) (not p4s2)) (or (not p3s2) (not p5s2)) (or (not p4s2) (not p5s2))
         (or (not p1s3) (not p2s3)) (or (not p1s3) (not p3s3)) (or (not p1s3) (not p4s3)) (or (not p1s3) (not p5s3)) (or (not p2s3) (not p3s3)) (or (not p2s3) (not p4s3)) (or (not p2s3) (not p5s3)) (or (not p3s3) (not p4s3)) (or (not p3s3) (not p5s3)) (or (not p4s3) (not p5s3))
         (or (not p1s4) (not p2s4)) (or (not p1s4) (not p3s4)) (or (not p1s4) (not p4s4)) (or (not p1s4) (not p5s4)) (or (not p2s4) (not p3s4)) (or (not p2s4) (not p4s4)) (or (not p2s4) (not p5s4)) (or (not p3s4) (not p4s4)) (or (not p3s4) (not p5s4)) (or (not p4s4) (not p5s4)))))
  '(unsat nil)))




#|

 Question 4.

 Part1: (25pts) Profile DP and make it as efficient as possible. If it
 meets the efficiency criteria of the evaluator, you get credit. The
 fastest submission will get 20 extra points, no matter how slow. To
 generate interesting problems, see your book.

 Part 2: (30pts) Define DPLL, a function that given a propositional
 formula in CNF, applies the DPLL algorithm to determine if the
 formula is satisfiable. You have to implement the iterative with
 backjumping version of DPLL from the book.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DPLL returns 'sat and a satisfying assignment:
 an alist mapping each atom in the formula to t/nil. Use values to
 return multiple values.

 If it is usat, return 'unsat.

 Test DPLL using with assert-acl2s-equal using at least 10
 propositional formulas.

 The fastest submission will get 20 extra points, no matter how
 slow. To generate interesting problems, see your book.

|#

; picks the variable that appears in the shortest clause
(defun choose-dpll-var (clauses)
  (let ((best nil) (best-len most-positive-fixnum))
    (dolist (c clauses)
      (when (and c (< (length c) best-len))
        (setf best c best-len (length c))))
    (when best (lit-var (car best)))))

; recursive DPLL w/ backjumping
(defun dpll-solve (clauses assignment all-vars)
  (multiple-value-bind (cl asgn)
      (bcp-and-pure-fixpoint clauses assignment)
    (cond
      ((has-empty-clause-p cl)
       (values 'unsat (mapcar #'car asgn)))
      ((null cl)
       (let ((full asgn))
         (dolist (v all-vars)
           (unless (assoc v full :test #'equal)
             (push (cons v t) full)))
         (values 'sat full)))
      (t
       (let ((var (choose-dpll-var cl)))
         (multiple-value-bind (r1 a1)
             (dpll-solve (propagate-literal var cl)
                         (acons var t asgn)
                         all-vars)
           (if (eq r1 'sat)
               (values 'sat a1)
               (if (not (member var a1 :test #'equal))
                   (values 'unsat a1)
		   (multiple-value-bind (r2 a2)
                       (dpll-solve (propagate-literal (lit-negate var) cl)
				   (acons var nil asgn)
				   all-vars)
                     (if (eq r2 'sat)
			 (values 'sat a2)
			 (values 'unsat
				 (remove var
					 (union a1 a2 :test #'equal)
					 :test #'equal))))))))))))

(defun dpll (f)
  (cond
    ((eq f t)   (values 'sat nil))
    ((eq f nil) (values 'unsat nil))
    (t (let* ((clauses (cnf-to-clauses f))
              (vars    (all-vars clauses)))
         (dpll-solve clauses nil vars)))))



(assert (equal (multiple-value-list
                (dpll t))
               '(sat nil)))
(assert (equal (multiple-value-list
                (dpll nil))
               '(unsat nil)))
(assert (equal (multiple-value-list
                (dpll 'a))
               '(sat ((a . t)))))
(assert (equal (multiple-value-list
                (dpll '(not a)))
               '(sat ((a . nil)))))
(assert (equal (multiple-value-list
                (dpll '(and a (not a))))
               '(unsat (a))))
(assert (equal (multiple-value-list
                (dpll '(and a
                        (or (not a) b)
                        (or (not b) c))))
               '(sat ((c . t) (b . t) (a . t)))))
(assert (equal (multiple-value-list
                (dpll '(and a
                        (or (not a) b)
                        (not b))))
               '(unsat (b a))))
(assert (equal (multiple-value-list
                (dpll '(and a
                        b
                        (or (not a) (not b)))))
               '(unsat (b a))))
(assert (equal (multiple-value-list
                (dpll '(and a
                        (or (not a) b)
                        (or (not b) c)
                        (or (not c) d)
                        (not d))))
               '(unsat (d c b a))))
(assert (equal (multiple-value-list
                (dpll '(and (not x1)
                        (not x2)
                        (not x3)
                        (not x4))))
               '(sat ((x4 . nil) (x3 . nil) (x2 . nil) (x1 . nil)))))
(assert (equal (multiple-value-list
                (dpll '(and
                        (or x1 x2 x3 x4)
                        (or (not x1) (not x2))
                        (or (not x1) (not x3))
                        (or (not x1) (not x4))
                        (or (not x2) (not x3))
                        (or (not x2) (not x4))
                        (or (not x3) (not x4))
                        (or (not x1))
                        (or (not x2))
                        (or (not x3))
                        (or (not x4)))))
               '(unsat (X4 X3 X2 X1))))
(assert (equal (multiple-value-list
                (dpll '(and
                        x1
                        x2
                        x3
                        (or (not x1) (not x2))
                        (or (not x1) (not x3))
                        (or (not x2) (not x3)))))
               '(unsat (x3 x2 x1))))
