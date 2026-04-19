#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Spring 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

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

 Here are some examples you can try. 

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input. 

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

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

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


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
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

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

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.
 
|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and 
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s::acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.
 
|#


#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

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
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t 
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because 
 
 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

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
 increase the size of a formula. 

|#

; Collect all variables appearing in a FO term
(defun fo-term-vars (term)
  (cond
    ((variable-symbolp term) (list term))
    ((constant-symbolp term) nil)
    ((quotep term) nil)
    ((constant-objectp term) nil)
    ((and (consp term) (function-symbolp (car term)))
     (remove-dups
      (reduce #'append (mapcar #'fo-term-vars (cdr term))
              :initial-value nil)))
    (t nil)))

; Collect all free variables in a FO formula
(defun fo-free-vars (f)
  (cond
    ((booleanp f) nil)
    ((variable-symbolp f) (list f))
    ((constant-symbolp f) nil)
    ((quotep f) nil)
    ((constant-objectp f) nil)
    ((consp f)
     (let ((pop (car f))
           (args (cdr f)))
       (cond
         ;; quantifier: bound vars are not free
         ((in pop *fo-quantifiers*)
          (let* ((vars (cadr f))
                 (body (caddr f))
                 (var-list (if (variable-symbolp vars) (list vars) vars))
                 (body-fvs (fo-free-vars body)))
            (remove-if #'(lambda (v) (in v var-list)) body-fvs)))
         ;; propositional connective: union of free vars in args
         ((p-funp pop)
          (remove-dups
           (reduce #'append (mapcar #'fo-free-vars args)
                   :initial-value nil)))
         ;; equality
         ((== pop '=)
          (remove-dups (append (fo-term-vars (cadr f))
                               (fo-term-vars (caddr f)))))
         ;; atomic relation: free vars are the term vars
         (t
          (remove-dups
           (reduce #'append (mapcar #'fo-term-vars args)
                   :initial-value nil))))))
    (t nil)))

; Check if all arguments are constant-objects or quoted objects
(defun ground-argsp (args)
  (every #'(lambda (a) (or (constant-objectp a) (quotep a))) args))

; Recursively simplify a FO term. Evaluates ground ACL2s function applications via acl2s-compute.
(defun fo-simplify-term (term)
  (cond
    ((variable-symbolp term) term)
    ((constant-symbolp term) term)
    ((quotep term) term)
    ((constant-objectp term) term)
    ((and (consp term) (function-symbolp (car term)))
     (let* ((f (car term))
            (args (cdr term))
            (sargs (mapcar #'fo-simplify-term args))
            (rebuilt (cons f sargs)))
       (if (ground-argsp sargs)
           ;; try to evaluate via ACL2s
           (let ((result (acl2s-compute (to-acl2s rebuilt))))
             (if (car result)
                 ;; error (e.g. contract violation) — keep as-is
                 rebuilt
                 ;; success — use the computed value
                 (let ((val (cadr result)))
                   (if (constant-objectp val)
                       val
                       ;; wrap non-atomic results in a quote
                       `(quote ,val)))))
           rebuilt)))
    (t term)))

; Simplify an atomic FO formula by simplifying its terms
(defun fo-simplify-atomic (f)
  (cond
    ((and (consp f) (== (car f) '=) (== (len f) 3))
     `(= ,(fo-simplify-term (cadr f)) ,(fo-simplify-term (caddr f))))
    ((consp f)
     (cons (car f) (mapcar #'fo-simplify-term (cdr f))))
    (t f)))


; PROPOSITIONAL SIMPLIFICATION HELPERS


; Flatten nested applications of an associative operator
(defun flatten-args (op args)
  (reduce #'append
          (mapcar #'(lambda (a)
                      (if (and (consp a) (== (car a) op))
                          (flatten-args op (cdr a))
                          (list a)))
                  args)))

; Return the complement of a literal/formula
(defun complement-lit (x)
  (if (and (consp x) (== (car x) 'not) (== (len x) 2))
      (cadr x)
      `(not ,x)))

; Check if any element's complement also appears in lst
(defun any-complement-p (lst)
  (some #'(lambda (x) (in (complement-lit x) lst)) lst))

; Collapse nested nots: returns (inner-form is-odd-p)
(defun count-nots (f num)
  (if (and (consp f) (== (car f) 'not) (== (len f) 2))
      (count-nots (cadr f) (+ 1 num))
      (list f (oddp num))))

; Remove elements appearing in pairs (for iff: p iff p = t)
(defun remove-dup-pairs (lst)
  (let ((result nil))
    (dolist (x lst)
      (if (member x result :test #'equal)
          (setf result (remove x result :test #'equal :count 1))
          (push x result)))
    (reverse result)))

; Remove complement pairs from lst. Returns (remaining . count)
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

; Check if arg appears an odd number of times in list f
(defun odd-num-nil (f arg num)
  (if (endp f)
      (oddp num)
      (if (equal (car f) arg)
          (odd-num-nil (cdr f) arg (+ 1 num))
          (odd-num-nil (cdr f) arg num))))

; Negate the first non-boolean argument in args
(defun negate-non-const (args)
  (if (endp args)
      nil
      (let ((a (car args)))
        (if (booleanp a)
            (cons a (negate-non-const (cdr args)))
            (cons `(not ,a) (cdr args))))))


; INDIVIDUAL OPERATOR SIMPLIFIERS


; Simplify (not ...). args is a singleton list
(defun simplify-fo-not (args)
  (let* ((inner (car args))
         (full `(not ,inner))
         (result (count-nots full 0))
         (core (car result))
         (oddp-num (cadr result)))
    (cond ((== core t)   (if oddp-num nil t))
          ((== core nil) (if oddp-num t nil))
          (oddp-num `(not ,core))
          (t core))))

; Simplify (and args...). Handles identity=t, sink=nil, flatten, dedup, complement elimination
(defun simplify-fo-and (args)
  (cond
    ((endp args) t)
    ((== (len args) 1) (car args))
    (t (let* ((flat (flatten-args 'and args))
              (clean (remove-dups (remove t flat))))
         (cond ((in nil flat) nil)
               ((any-complement-p clean) nil)
               ((endp clean) t)
               ((== (len clean) 1) (car clean))
               (t (cons 'and clean)))))))

; Simplify (or args...). Handles identity=nil, sink=t, flatten, dedup, complement elimination
(defun simplify-fo-or (args)
  (cond
    ((endp args) nil)
    ((== (len args) 1) (car args))
    (t (let* ((flat (flatten-args 'or args))
              (clean (remove-dups (remove nil flat))))
         (cond ((in t flat) t)
               ((any-complement-p clean) t)
               ((endp clean) nil)
               ((== (len clean) 1) (car clean))
               (t (cons 'or clean)))))))

; Simplify (implies ante conseq)
(defun simplify-fo-implies (args)
  (let ((ante (car args))
        (conseq (cadr args)))
    (cond ((== ante t) conseq)
          ((== ante nil) t)
          ((== conseq t) t)
          ((== conseq nil) `(not ,ante))
          ((equal ante conseq) t)
          ((equal conseq (complement-lit ante)) conseq)
          (t `(implies ,ante ,conseq)))))

; Simplify (iff args...). Handles identity=t, flatten, dup-pair cancellation, complement-pair handling
(defun simplify-fo-iff (args)
  (cond
    ((endp args) t)
    ((== (len args) 1) (car args))
    (t (let* ((flat (flatten-args 'iff args))
              (deduped (remove-dup-pairs flat))
              (comp-result (remove-complements deduped))
              (comp-args (car comp-result))
              (comp-count (cdr comp-result))
              ;; each complement pair contributes a nil
              (with-nils (if (> comp-count 0)
                             (append (make-list comp-count
                                                :initial-element nil)
                                     comp-args)
                             comp-args))
              (simp-f (remove t with-nils))
              (simp-f-nil (remove nil simp-f))
              (negate-p (odd-num-nil simp-f nil 0))
              (result (if negate-p
                          (negate-non-const simp-f-nil)
                          simp-f-nil)))
         (cond ((endp result) (if negate-p nil t))
               ((== (len result) 1) (car result))
               (t (cons 'iff result)))))))

; Simplify (if test then else)
(defun simplify-fo-if (args)
  (let ((test (car args))
        (then-br (cadr args))
        (else-br (caddr args)))
    (cond ((== test t) then-br)
          ((== test nil) else-br)
          (t `(if ,test ,then-br ,else-br)))))


; QUANTIFIER SIMPLIFICATION (requirement F)


; Remove vacuous quantified variables. If all are vacuous, drop the quantifier entirely
(defun simplify-quantifier (q vars body)
  (let* ((var-list (if (variable-symbolp vars) (list vars) vars))
         (fvs (fo-free-vars body))
         (live (remove-if-not #'(lambda (v) (in v fvs)) var-list)))
    (cond ((endp live) body)
          ((== (len live) 1) `(,q ,(car live) ,body))
          (t `(,q ,live ,body)))))


; MAIN SIMPLIFIER 

; Apply one round of operator-specific simplification. Returns the simplified formula
(defun fo-simplify-step (pop sargs)
  (cond ((== pop 'not)     (simplify-fo-not sargs))
        ((== pop 'and)     (simplify-fo-and sargs))
        ((== pop 'or)      (simplify-fo-or sargs))
        ((== pop 'implies) (simplify-fo-implies sargs))
        ((== pop 'iff)     (simplify-fo-iff sargs))
        ((== pop 'if)      (simplify-fo-if sargs))
        (t (cons pop sargs))))

; Simplify a first-order formula. Bottom-up: simplify subformulas
; first, then apply simplification rules at the top level.
; Re-simplifies if anything changed (fixed-point).
(defun fo-simplify (f)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((quotep f) f)
    ((constant-objectp f) f)
    ((consp f)
     (let ((pop (car f))
           (args (cdr f)))
       (cond
         ;; --- Quantifier ---
         ((in pop *fo-quantifiers*)
          (let* ((vars (cadr f))
                 (body (caddr f))
                 (sbody (fo-simplify body)))
            (simplify-quantifier pop vars sbody)))
 
         ;; --- Propositional connective ---
         ((p-funp pop)
          (let* ((sargs (mapcar #'fo-simplify args))
                 (result (fo-simplify-step pop sargs))
                 (rebuilt (cons pop sargs)))
            ;; if simplification changed something, re-simplify
            (if (equal result rebuilt)
                result
                (fo-simplify result))))
 
         ;; --- Atomic formula (relation or equality) ---
         (t (fo-simplify-atomic f)))))
    (t f)))


;; TESTS

(assert (equal (fo-simplify '(and (p x) t (q t y) (and r s) (and p s)))
               '(and (p x) (q t y) r p s)))
(assert (equal (fo-simplify '(or (not x) (forall (x w) (P y z))))
	       '(or (not x) (P y z))))
(assert (equal (fo-simplify '(if (not t) x (forall (x w) (P x y z))))
	       '(forall x (P x y z))))
(assert (equal (fo-simplify '(implies t (not (not (not x)))))
	       '(not x)))
(assert (equal (fo-simplify '(P (binary-+ 4 2) 3))
	       '(P 6 3)))
(assert (equal (fo-simplify '(and p x t nil))
	       nil))
(assert (equal (fo-simplify '(or (f) (f1) (p a b) (not (p a b)) (= w z)))
	       t))
(assert (equal (fo-simplify '(iff x y x (iff a b)))
	       '(iff y a b)))
(assert (equal (fo-simplify '(iff x (not x)))
	       nil))
(assert (equal (fo-simplify '(or x y nil))
	       '(or x y)))

#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

; Eliminate implies, iff, and if from a FO formula.
; Keeps quantifiers and other connectives, just recursively rewrites
; the forbidden propositional operators away.

(defun expand-iff (args)
  (cond
    ((endp args) t)
    ((endp (cdr args)) (car args))
    ((endp (cddr args))
     (let ((a (car args))
           (b (cadr args)))
       `(and (or ,a (not ,b))
             (or (not ,a) ,b))))
    (t
     (cons 'and
           (mapcar #'(lambda (pair)
                       (expand-iff pair))
                   (mapcar #'list
                           args
                           (cdr args)))))))

(defun nnf-list (fs)
  (mapcar #'nnf fs))

(defun nnf (f)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((quotep f) f)
    ((constant-objectp f) f)
    ((and (consp f) (in (car f) *fo-quantifiers*))
     (let ((q (car f))
           (vars (cadr f))
           (body (caddr f)))
       `(,q ,vars ,(nnf body))))
    ((and (consp f) (== (car f) 'not) (== (len f) 2))
     `(not ,(nnf (cadr f))))
    ((and (consp f) (== (car f) 'and))
     (cons 'and (nnf-list (cdr f))))
    ((and (consp f) (== (car f) 'or))
     (cons 'or (nnf-list (cdr f))))
    ((and (consp f) (== (car f) 'implies) (== (len f) 3))
     (nnf `(or (not ,(cadr f)) ,(caddr f))))
    ((and (consp f) (== (car f) 'iff))
     (nnf (expand-iff (cdr f))))
    ((and (consp f) (== (car f) 'if) (== (len f) 4))
     (nnf `(or (and ,(cadr f) ,(caddr f))
               (and (not ,(cadr f)) ,(cadddr f)))))
    (t f)))

(assert (equal (nnf '(if x y z))
	       '(or (and x y) (and (not x) z))))
(assert (equal (nnf '(implies x y))
	       '(or (not x) y)))
(assert (equal (nnf '(iff x y z p))
	       '(and (and (or x (not y)) (or (not x) y)) (and (or y (not z)) (or (not y) z))
		    (and (or z (not p)) (or (not z) p)))))
(assert (equal (nnf '(and x y (implies x y)))
	       '(and x y (or (not x) y))))
(assert (equal (nnf '(and (implies (p x) (q x))
                          (if (r x) (s x) (t x))))
               '(and (or (not (p x)) (q x))
                     (or (and (r x) (s x))
                         (and (not (r x)) (t x))))))

(assert (equal (nnf '(iff (p x) (q x)))
               '(and (or (p x) (not (q x)))
                     (or (not (p x)) (q x)))))

(assert (equal (nnf '(not (iff (p x) (q x))))
               '(not (and (or (p x) (not (q x)))
                          (or (not (p x)) (q x))))))

(assert (equal (nnf '(iff x y z p))
               '(and (and (or x (not y))
                          (or (not x) y))
                     (and (or y (not z))
                          (or (not y) z))
                     (and (or z (not p))
                          (or (not z) p)))))

(assert (equal (nnf '(forall (x y)
                        (if (implies (p x) (q y))
                            (iff (r x) (s y))
                            (t y))))
               '(forall (x y)
                  (or (and (or (not (p x)) (q y))
                           (and (or (r x) (not (s y)))
                                (or (not (r x)) (s y))))
                      (and (not (or (not (p x)) (q y)))
                       (t y))))))
(assert (equal (nnf '(not (implies (p x) (q x))))
               '(not (or (not (p x)) (q x)))))

#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas. 
 
|#

;;;;;;;;;;;;;;;;;;
;; True NNF     ;;
;;;;;;;;;;;;;;;;;; 

(defun push-neg (f)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((quotep f) f)
    ((constant-objectp f) f)

    ((and (consp f) (== (car f) 'not) (== (len f) 2))
     (push-neg-not (cadr f)))

    ((and (consp f) (in (car f) *fo-quantifiers*))
     `(,(car f) ,(cadr f) ,(push-neg (caddr f))))

    ((and (consp f) (in (car f) '(and or)))
     (cons (car f) (mapcar #'push-neg (cdr f))))

    (t f)))

(defun push-neg-not (f)
  (cond
    ((== f t) nil)
    ((== f nil) t)

    ((and (consp f) (== (car f) 'not) (== (len f) 2))
     (push-neg (cadr f)))

    ((and (consp f) (== (car f) 'and))
     (cons 'or (mapcar #'push-neg-not (cdr f))))

    ((and (consp f) (== (car f) 'or))
     (cons 'and (mapcar #'push-neg-not (cdr f))))

    ((and (consp f) (== (car f) 'forall))
     `(exists ,(cadr f) ,(push-neg-not (caddr f))))

    ((and (consp f) (== (car f) 'exists))
     `(forall ,(cadr f) ,(push-neg-not (caddr f))))

    (t `(not ,(push-neg f)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Free-variable utilities    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun union-eq (xs ys)
  (cond
    ((endp xs) ys)
    ((in (car xs) ys) (union-eq (cdr xs) ys))
    (t (cons (car xs) (union-eq (cdr xs) ys)))))

(defun remove-all (xs ys)
  (cond
    ((endp ys) nil)
    ((in (car ys) xs) (remove-all xs (cdr ys)))
    (t (cons (car ys) (remove-all xs (cdr ys))))))

(defun free-vars (f)
  (cond
    ((booleanp f) nil)
    ((variable-symbolp f) (list f))
    ((constant-symbolp f) nil)
    ((quotep f) nil)
    ((constant-objectp f) nil)

    ((and (consp f) (== (car f) 'not))
     (free-vars (cadr f)))

    ((and (consp f) (in (car f) '(and or)))
     (free-vars-list (cdr f)))

    ((and (consp f) (in (car f) *fo-quantifiers*))
     (let* ((vars (cadr f))
            (var-list (if (variable-symbolp vars) (list vars) vars)))
       (remove-all var-list (free-vars (caddr f)))))

    ((consp f)
     ;; relation/function/equality application
     (free-vars-list (cdr f)))

    (t nil)))

(defun free-vars-list (xs)
  (cond
    ((endp xs) nil)
    (t (union-eq (free-vars (car xs))
                 (free-vars-list (cdr xs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simultaneous substitution    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun subst-all (pairs f)
  (cond
    ((booleanp f) f)

    ((variable-symbolp f)
     (let ((pair (assoc f pairs :test #'equal)))
       (if pair (cdr pair) f)))

    ((constant-symbolp f) f)
    ((quotep f) f)
    ((constant-objectp f) f)

    ;; quantifier: do not substitute bound vars in the body
    ((and (consp f) (in (car f) *fo-quantifiers*))
     (let* ((q (car f))
            (vars (cadr f))
            (var-list (if (variable-symbolp vars) (list vars) vars))
            (filtered (remove-if #'(lambda (p) (in (car p) var-list)) pairs)))
       `(,q ,vars ,(subst-all filtered (caddr f)))))

    ((consp f)
     (cons (car f)
           (mapcar #'(lambda (a) (subst-all pairs a)) (cdr f))))

    (t f)))

;;;;;;;;;;;;;;;;;;;;;;;
;; Skolemization     ;;
;;;;;;;;;;;;;;;;;;;;;;;

(defun make-skolem-term (univ-vars)
  (if (endp univ-vars)
      (gentemp "C")
      (cons (gentemp "SK") univ-vars)))

(defun skolemize (f univ-vars)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((quotep f) f)
    ((constant-objectp f) f)

    ;; forall: keep it, extend universal scope
    ((and (consp f) (== (car f) 'forall))
     (let* ((vars (cadr f))
            (var-list (if (variable-symbolp vars) (list vars) vars))
            (new-scope (append univ-vars var-list))
            (new-body (skolemize (caddr f) new-scope)))
       `(forall ,vars ,new-body)))

    ;; exists: replace vars by Skolem constants/functions, then drop exists
    ((and (consp f) (== (car f) 'exists))
     (let* ((vars (cadr f))
            (var-list (if (variable-symbolp vars) (list vars) vars))
            (pairs (mapcar #'(lambda (v)
                               (cons v (make-skolem-term univ-vars)))
                           var-list))
            (new-body (subst-all pairs (caddr f))))
       (skolemize new-body univ-vars)))

    ((consp f)
     (cons (car f)
           (mapcar #'(lambda (a) (skolemize a univ-vars)) (cdr f))))

    (t f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Prenex Normal Form   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pnf (f)
  ;; returns (vars . matrix), where vars are leading universal vars
  (cond
    ((and (consp f) (== (car f) 'forall))
     (let* ((vars (cadr f))
            (var-list (if (variable-symbolp vars) (list vars) vars))
            (inner (pnf (caddr f))))
       (cons (append var-list (car inner))
             (cdr inner))))

    ((and (consp f) (== (car f) 'and))
     (pnf-and (cdr f)))

    ((and (consp f) (== (car f) 'or))
     (pnf-or (cdr f)))

    ((and (consp f) (== (car f) 'not))
     (cons nil f))

    (t (cons nil f))))

(defun pnf-and (args)
  ;; Merge universal prefixes position-by-position:
  ;; (forall x φ) ∧ (forall y ψ)  ≡  forall z (φ[z/x] ∧ ψ[z/y])
  ;; Then we later remove vacuous quantified vars.
  (let* ((results (mapcar #'pnf args))
         (max-vars (if (endp results)
                       0
                       (apply #'max
                              (mapcar #'(lambda (r) (length (car r))) results))))
         (matrices (mapcar #'cdr results))
         (merged-vars nil))
    (dotimes (i max-vars)
      (let ((fresh (gentemp "X")))
        (push fresh merged-vars)
        (setf matrices
              (loop for matrix in matrices
                    for result in results
                    collect
                    (let ((rvars (car result)))
                      (if (< i (length rvars))
                          (subst-all (list (cons (nth i rvars) fresh)) matrix)
                          matrix))))))
    (cons (reverse merged-vars)
          (if (== (len matrices) 1)
              (car matrices)
              (cons 'and matrices)))))

(defun pnf-or (args)
  ;; Under disjunction, pull universal quantifiers outward.
  ;; Rename to avoid capture/clashes.
  (let ((all-vars nil)
        (new-args nil))
    (dolist (a args)
      (let* ((result (pnf a))
             (rvars (car result))
             (rmatrix (cdr result))
             (pairs nil)
             (new-rvars nil))
        (dolist (v rvars)
          (let ((nv (if (in v all-vars) (gentemp "X") v)))
            (push (cons v nv) pairs)
            (push nv new-rvars)
            (push nv all-vars)))
        (setf new-rvars (reverse new-rvars))
        (push (subst-all pairs rmatrix) new-args)))
    (cons (reverse all-vars)
          (if (== (len new-args) 1)
              (car (reverse new-args))
              (cons 'or (reverse new-args))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remove vacuous universal quantifiers   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun keep-used-vars (vars matrix)
  (cond
    ((endp vars) nil)
    ((in (car vars) (free-vars matrix))
     (cons (car vars) (keep-used-vars (cdr vars) matrix)))
    (t (keep-used-vars (cdr vars) matrix))))

(defun rebuild-foralls (vars matrix)
  (if (endp vars)
      matrix
      (if (== (len vars) 1)
          `(forall ,(car vars) ,matrix)
          `(forall ,vars ,matrix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CNF conversion on quantifier-free matrix   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun merge-or-clauses (a b)
  (let ((a-lits (if (and (consp a) (== (car a) 'or)) (cdr a) (list a)))
        (b-lits (if (and (consp b) (== (car b) 'or)) (cdr b) (list b))))
    (let ((all (append a-lits b-lits)))
      (if (== (len all) 1)
          (car all)
          (cons 'or all)))))

(defun dist-or-two (a b)
  (let ((a-conjs (if (and (consp a) (== (car a) 'and)) (cdr a) (list a)))
        (b-conjs (if (and (consp b) (== (car b) 'and)) (cdr b) (list b))))
    (let ((clauses nil))
      (dolist (ac a-conjs)
        (dolist (bc b-conjs)
          (push (merge-or-clauses ac bc) clauses)))
      (if (== (len clauses) 1)
          (car clauses)
          (cons 'and (reverse clauses))))))

(defun to-cnf (f)
  (cond
    ((and (consp f) (== (car f) 'and))
     (let* ((cnf-args (mapcar #'to-cnf (cdr f)))
            (flat nil))
       (dolist (a cnf-args)
         (if (and (consp a) (== (car a) 'and))
             (dolist (c (cdr a)) (push c flat))
             (push a flat)))
       (let ((r (reverse flat)))
         (if (== (len r) 1)
             (car r)
             (cons 'and r)))))

    ((and (consp f) (== (car f) 'or))
     (let ((cnf-args (mapcar #'to-cnf (cdr f))))
       (reduce #'dist-or-two cnf-args)))

    (t f)))

;;;;;;;;;;;;;;;;;;

(defun simp-skolem-pnf-cnf (f)
  (let* ((simplified (fo-simplify f))
         ;; eliminate implies/iff/if using  existing nnf pass
         (nnf-form (nnf simplified))
         ;; true NNF: push negation through quantifiers/connectives
         (true-nnf (push-neg nnf-form))
         ;; Skolemize inside-out
         (skolemized (skolemize true-nnf nil))
         ;; Pull universal quantifiers left
         (pnf-result (pnf skolemized))
         (vars0 (car pnf-result))
         (matrix0 (cdr pnf-result))
         ;; Remove vacuous universals
         (vars (keep-used-vars vars0 matrix0))
         ;; CNF the matrix
         (cnf-matrix (to-cnf matrix0)))
    (rebuild-foralls vars cnf-matrix)))


;; (exists x (P x))  ⟹  (P c)
(simp-skolem-pnf-cnf '(exists x (P x)))

;; ∀x ∃y R(x,y)  ⟹  ∀x R(x, sk(x))
(simp-skolem-pnf-cnf '(forall x (exists y (R x y))))

;; ∀x (P(x) → Q(x))  ⟹  ∀x (or (not (P x)) (Q x))
(simp-skolem-pnf-cnf '(forall x (implies (P x) (Q x))))

;; ∃x ¬¬P(x)  ⟹  (P c)
(simp-skolem-pnf-cnf '(exists x (not (not (P x)))))

;; ¬∀x P(x)  ⟹  (not (P c))   [becomes ∃x ¬P(x), then skolemized]
(simp-skolem-pnf-cnf '(not (forall x (P x))))

;; ∀x ∃y ∀z ∃w R(x,y,z,w)
;;   ⟹  ∀x ∀z R(x, sk1(x), z, sk2(x,z))
(simp-skolem-pnf-cnf '(forall x (exists y (forall z (exists w (R x y z w))))))

;; (∀x P(x)) ∧ (∀y Q(y))  ⟹  ∀z (and (P z) (Q z))
(simp-skolem-pnf-cnf '(and (forall x (P x)) (forall y (Q y))))

;; (∀x P(x)) ∨ (∀y Q(y))  ⟹  ∀x ∀y (or (P x) (Q y))
(simp-skolem-pnf-cnf '(or (forall x (P x)) (forall y (Q y))))

;; ∃x (iff (P x) (Q x))
;;   ⟹  (and (or (not (P c)) (Q c)) (or (not (Q c)) (P c)))
(simp-skolem-pnf-cnf '(exists x (iff (P x) (Q x))))

;;   ⟹  ∀x (and (or (P x) (R x)) (or (Q x) (R x)))
(simp-skolem-pnf-cnf '(forall x (or (and (P x) (Q x)) (R x))))

(simp-skolem-pnf-cnf '(forall x (forall y (P x))))

;; ∀x (implies (exists y (R x y)) (and (P x) (Q x)))
;;   NNF: ∀x (or (forall y (not (R x y))) (and (P x) (Q x)))
;;   Skolem: ∀x (or (not (R x y)) ...) — but the inner forall under or needs PNF
(simp-skolem-pnf-cnf
 '(forall x (implies (exists y (R x y))
                     (and (P x) (Q x)))))

#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#
 
(defun subst-term (term sub)
  (cond
    ((variable-symbolp term)
     (let ((hit (assoc term sub :test #'equal)))
       (if hit
           (subst-term (cdr hit) sub)   ; chase substitution fully
           term)))
    ((or (booleanp term)
         (constant-symbolp term)
         (quotep term)
         (constant-objectp term))
     term)
    ((consp term)
     (cons (car term)
           (mapcar (lambda (a) (subst-term a sub))
                   (cdr term))))
    (t term)))

(defun pair-list (xs ys)
  (cond
    ((and (endp xs) (endp ys)) nil)
    ((or (endp xs) (endp ys)) 'fail)
    (t
     (cons (cons (car xs) (car ys))
           (pair-list (cdr xs) (cdr ys))))))

(defun apply-sub-to-equations (sub eqs)
  (mapcar (lambda (eq)
            (cons (subst-term (car eq) sub)
                  (subst-term (cdr eq) sub)))
          eqs))

(defun compose-subst (new old)
  ;; Compose NEW after OLD:
  ;; apply NEW to RHSs of OLD, then add NEW, removing overwritten vars.
  (append new
          (remove-if
           (lambda (binding)
             (assoc (car binding) new :test #'equal))
           (mapcar (lambda (b)
                     (cons (car b)
                           (subst-term (cdr b) new)))
                   old))))

(defun unify-var (v term rest sub)
  (cond
    ((equal v term)
     (unify-aux rest sub))
    ((member v (fo-term-vars term) :test #'equal) ; occurs check
     'fail)
    (t
     (let* ((theta (list (cons v term)))
            (new-rest (apply-sub-to-equations theta rest))
            (new-sub (compose-subst theta sub)))
       (unify-aux new-rest new-sub)))))

(defun unify-aux (eqs sub)
  (if (endp eqs)
      sub
      (let* ((eq (car eqs))
             (s (subst-term (car eq) sub))
             (term (subst-term (cdr eq) sub))
             (rest (cdr eqs)))
        (cond
          ;; delete
          ((equal s term)
           (unify-aux rest sub))

          ;; eliminate / orient
          ((variable-symbolp s)
           (unify-var s term rest sub))

          ((variable-symbolp term)
           (unify-var term s rest sub))

          ;; decompose
          ((and (consp s) (consp term)
                (equal (car s) (car term))
                (= (length (cdr s)) (length (cdr term))))
           (let ((pairs (pair-list (cdr s) (cdr term))))
             (if (eq pairs 'fail)
                 'fail
                 (unify-aux (append pairs rest) sub))))

          ;; clash
          (t 'fail)))))

(defun unify (l)
  (if (endp l)
      'fail
      (unify-aux l nil)))

(defun binding< (a b)
  (string< (symbol-name (car a))
           (symbol-name (car b))))

(defun normalize-subst (x)
  (if (eq x 'fail)
      'fail
      (sort (copy-list x) #'binding<)))

(assert (equal (normalize-subst (unify (list (cons 'x 'a))))
               '((x . a))))

(assert (equal (normalize-subst (unify (list (cons 'x 'y))))
               '((x . y))))

(assert (equal (normalize-subst (unify (list (cons '(f x) '(f a)))))
               '((x . a))))

(assert (equal (normalize-subst (unify (list (cons '(f x y) '(f a b)))))
               '((x . a) (y . b))))

(assert (equal (normalize-subst (unify (list (cons '(f x x) '(f a a)))))
               '((x . a))))

(assert (equal (normalize-subst (unify (list (cons '(f x b) '(f a y)))))
               '((x . a) (y . b))))

(assert (equal (normalize-subst (unify (list (cons '(g x (f y)) '(g a (f b))))))
               '((x . a) (y . b))))

(assert (equal (unify (list (cons '(f x x) '(f a b))))
               'fail))

(assert (equal (unify (list (cons 'x '(f x))))
               'fail))

(assert (equal (normalize-subst
                (unify (list (cons '(f x (g y)) '(f (g z) (g a))))))
               '((x . (g z)) (y . a))))

#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).


|#

(defparameter *fo5-skolem-counter* 0)
(defparameter *fo5-var-counter* 0)

(defun fo5-reset-state ()
  (setf *fo5-skolem-counter* 0
        *fo5-var-counter* 0))

(defun fo5-mk-skolem-symbol ()
  (incf *fo5-skolem-counter*)
  (intern (format nil "SK~A" *fo5-skolem-counter*)))

(defun fo5-mk-var-symbol (base)
  (incf *fo5-var-counter*)
  (intern (format nil "?~A~A" (string-upcase base) *fo5-var-counter*)))

(defun fo5-symbol-prefix-p (prefix sym)
  (and (symbolp sym)
       (let ((s (symbol-name sym)))
         (and (<= (length prefix) (length s))
              (string= prefix s :end2 (length prefix))))))

(defun fo5-variable-p (x)
  (and (symbolp x) (fo5-symbol-prefix-p "?" x)))

(defun fo5-connective-p (x)
  (member x '(not and or implies iff forall exists) :test #'eq))

(defun fo5-atom-p (x)
  (and (consp x)
       (symbolp (car x))
       (not (fo5-connective-p (car x)))))

(defun fo5-copy-tree (x)
  (if (consp x)
      (cons (fo5-copy-tree (car x)) (fo5-copy-tree (cdr x)))
      x))

(defun fo5-flatten-op (op args)
  (loop for a in args append
        (if (and (consp a) (eq (car a) op))
            (cdr a)
            (list a))))

(defun fo5-make-and (&rest args)
  (let ((xs (remove-if (lambda (x) (eq x t)) (fo5-flatten-op 'and args))))
    (cond ((null xs) t)
          ((null (cdr xs)) (car xs))
          (t (cons 'and xs)))))

(defun fo5-make-or (&rest args)
  (let ((xs (remove-if (lambda (x) (eq x nil)) (fo5-flatten-op 'or args))))
    (cond ((null xs) nil)
          ((null (cdr xs)) (car xs))
          (t (cons 'or xs)))))

(defun fo5-formula->string (x)
  (with-output-to-string (s) (prin1 x s)))

(defun fo5-canonical-sort (xs)
  (sort (copy-list xs) #'string< :key #'fo5-formula->string))

(defun fo5-remove-duplicates-by-string (xs)
  (remove-duplicates xs :test #'equal))

(defun fo5-subst-term (term sigma)
  (cond ((fo5-variable-p term)
         (let ((p (assoc term sigma :test #'eq)))
           (if p
               (fo5-subst-term (cdr p) sigma)
               term)))
        ((consp term)
         (mapcar (lambda (x) (fo5-subst-term x sigma)) term))
        (t term)))

(defun fo5-subst-formula (f sigma)
  (cond ((fo5-atom-p f) (mapcar (lambda (x) (fo5-subst-term x sigma)) f))
        ((atom f) f)
        ((eq (car f) 'not) (list 'not (fo5-subst-formula (cadr f) sigma)))
        ((member (car f) '(and or implies iff) :test #'eq)
         (cons (car f)
               (mapcar (lambda (x) (fo5-subst-formula x sigma)) (cdr f))))
        ((member (car f) '(forall exists) :test #'eq)
         (destructuring-bind (q vars body) f
           (let ((sigma2 (remove-if (lambda (p) (member (car p) vars :test #'eq))
                                    sigma)))
             (list q vars (fo5-subst-formula body sigma2)))))
        (t f)))

(defun fo5-occurs-in-term-p (v term sigma)
  (let ((t1 (fo5-subst-term term sigma)))
    (cond ((eq v t1) t)
          ((consp t1) (some (lambda (x) (fo5-occurs-in-term-p v x sigma)) t1))
          (t nil))))

(defun fo5-extend-unifier (v term sigma)
  (let ((term1 (fo5-subst-term term sigma)))
    (cond ((eq v term1) sigma)
          ((fo5-occurs-in-term-p v term1 sigma) :fail)
          (t
           (let ((sigma2
                   (mapcar (lambda (p)
                             (cons (car p)
                                   (fo5-subst-term (cdr p)
                                                   (list (cons v term1)))))
                           sigma)))
             (acons v term1 sigma2))))))

(defun fo5-unify-term-list (xs ys sigma)
  (if (eq sigma :fail)
      :fail
      (if (null xs)
          sigma
          (fo5-unify-term-list (cdr xs) (cdr ys)
                               (fo5-unify-term (car xs) (car ys) sigma)))))

(defun fo5-unify-term (s1 t1 sigma)
  (let ((s (fo5-subst-term s1 sigma))
        (tt (fo5-subst-term t1 sigma)))
    (cond ((equal s tt) sigma)
          ((fo5-variable-p s) (fo5-extend-unifier s tt sigma))
          ((fo5-variable-p tt) (fo5-extend-unifier tt s sigma))
          ((and (consp s) (consp tt)
                (= (length s) (length tt))
                (equal (car s) (car tt)))
           (fo5-unify-term-list (cdr s) (cdr tt) sigma))
          (t :fail))))

(defun fo5-unify-atoms (a b &optional (sigma nil))
  (if (and (consp a) (consp b)
           (eq (car a) (car b))
           (= (length a) (length b)))
      (fo5-unify-term-list (cdr a) (cdr b) sigma)
      :fail))

(defun fo5-match-term (pat obj env)
  (cond ((eq env :fail) :fail)
        ((fo5-variable-p pat)
         (let ((p (assoc pat env :test #'eq)))
           (if p
               (if (equal (cdr p) obj) env :fail)
               (acons pat obj env))))
        ((atom pat)
         (if (equal pat obj) env :fail))
        ((and (consp pat) (consp obj)
              (eq (car pat) (car obj))
              (= (length pat) (length obj)))
         (fo5-match-term-list (cdr pat) (cdr obj) env))
        (t :fail)))

(defun fo5-match-term-list (ps os env)
  (if (null ps)
      env
      (fo5-match-term-list (cdr ps) (cdr os)
                           (fo5-match-term (car ps) (car os) env))))

(defun fo5-match-atom (a b &optional (env nil))
  (if (and (eq (car a) (car b)) (= (length a) (length b)))
      (fo5-match-term-list (cdr a) (cdr b) env)
      :fail))

(defun fo5-elim-iff-implies (f)
  (cond ((fo5-atom-p f) f)
        ((atom f) f)
        ((eq (car f) 'not)
         (list 'not (fo5-elim-iff-implies (cadr f))))
        ((eq (car f) 'implies)
         (fo5-make-or (list 'not (fo5-elim-iff-implies (cadr f)))
                      (fo5-elim-iff-implies (caddr f))))
        ((eq (car f) 'iff)
         (let ((a (fo5-elim-iff-implies (cadr f)))
               (b (fo5-elim-iff-implies (caddr f))))
           (fo5-make-and (fo5-make-or (list 'not a) b)
                         (fo5-make-or (list 'not b) a))))
        ((member (car f) '(and or) :test #'eq)
         (cons (car f) (mapcar #'fo5-elim-iff-implies (cdr f))))
        ((member (car f) '(forall exists) :test #'eq)
         (list (car f) (cadr f) (fo5-elim-iff-implies (caddr f))))
        (t f)))

(defun fo5-nnf (f)
  (cond
    ((fo5-atom-p f) f)
    ((atom f) f)
    ((eq (car f) 'not)
     (let ((g (cadr f)))
       (cond
         ((fo5-atom-p g) f)
         ((atom g) f)
         ((eq (car g) 'not) (fo5-nnf (cadr g)))
         ((eq (car g) 'and)
          (apply #'fo5-make-or
                 (mapcar (lambda (x) (fo5-nnf (list 'not x))) (cdr g))))
         ((eq (car g) 'or)
          (apply #'fo5-make-and
                 (mapcar (lambda (x) (fo5-nnf (list 'not x))) (cdr g))))
         ((eq (car g) 'forall)
          (list 'exists (cadr g) (fo5-nnf (list 'not (caddr g)))))
         ((eq (car g) 'exists)
          (list 'forall (cadr g) (fo5-nnf (list 'not (caddr g)))))
         (t (list 'not (fo5-nnf g))))))
    ((eq (car f) 'and)
     (cons 'and (mapcar #'fo5-nnf (cdr f))))
    ((eq (car f) 'or)
     (cons 'or (mapcar #'fo5-nnf (cdr f))))
    ((member (car f) '(forall exists) :test #'eq)
     (list (car f) (cadr f) (fo5-nnf (caddr f))))
    (t f)))

(defun fo5-standardize-apart (f &optional (env nil))
  (cond
    ((fo5-atom-p f)
     (mapcar (lambda (x) (fo5-standardize-apart-term x env)) f))
    ((atom f) f)
    ((eq (car f) 'not)
     (list 'not (fo5-standardize-apart (cadr f) env)))
    ((member (car f) '(and or) :test #'eq)
     (cons (car f) (mapcar (lambda (x) (fo5-standardize-apart x env)) (cdr f))))
    ((member (car f) '(forall exists) :test #'eq)
     (destructuring-bind (q vars body) f
       (let* ((new-vars (mapcar #'fo5-mk-var-symbol vars))
              (pairs (mapcar #'cons vars new-vars))
              (env2 (append pairs env)))
         (list q new-vars (fo5-standardize-apart body env2)))))
    (t f)))

(defun fo5-standardize-apart-term (term env)
  (cond ((symbolp term)
         (let ((p (assoc term env :test #'eq)))
           (if p (cdr p) term)))
        ((consp term)
         (mapcar (lambda (x) (fo5-standardize-apart-term x env)) term))
        (t term)))

(defun fo5-skolemize (f &optional (uvars nil))
  (cond
    ((fo5-atom-p f) f)
    ((atom f) f)
    ((eq (car f) 'not) (list 'not (fo5-skolemize (cadr f) uvars)))
    ((member (car f) '(and or) :test #'eq)
     (cons (car f) (mapcar (lambda (x) (fo5-skolemize x uvars)) (cdr f))))
    ((eq (car f) 'forall)
     (destructuring-bind (_q vars body) f
       (declare (ignore _q))
       (fo5-skolemize body (append uvars vars))))
    ((eq (car f) 'exists)
     (destructuring-bind (_q vars body) f
       (declare (ignore _q))
       (let ((body1 body))
         (dolist (v vars)
           (let* ((sk (fo5-mk-skolem-symbol))
                  (term (if uvars (cons sk uvars) sk)))
             (setf body1 (fo5-subst-formula body1 (list (cons v term))))))
         (fo5-skolemize body1 uvars))))
    (t f)))

(defun fo5-drop-universals (f)
  (cond
    ((fo5-atom-p f) f)
    ((atom f) f)
    ((eq (car f) 'not) (list 'not (fo5-drop-universals (cadr f))))
    ((member (car f) '(and or) :test #'eq)
     (cons (car f) (mapcar #'fo5-drop-universals (cdr f))))
    ((eq (car f) 'forall)
     (fo5-drop-universals (caddr f)))
    (t f)))

(defun fo5-distribute-or-over-and (a b)
  (cond ((and (consp a) (eq (car a) 'and))
         (apply #'fo5-make-and
                (mapcar (lambda (x) (fo5-distribute-or-over-and x b)) (cdr a))))
        ((and (consp b) (eq (car b) 'and))
         (apply #'fo5-make-and
                (mapcar (lambda (x) (fo5-distribute-or-over-and a x)) (cdr b))))
        (t (fo5-make-or a b))))

(defun fo5-cnf-form (f)
  (cond
    ((fo5-atom-p f) f)
    ((and (consp f) (eq (car f) 'not)) f)
    ((and (consp f) (eq (car f) 'and))
     (apply #'fo5-make-and (mapcar #'fo5-cnf-form (cdr f))))
    ((and (consp f) (eq (car f) 'or))
     (reduce #'fo5-distribute-or-over-and
             (mapcar #'fo5-cnf-form (cdr f))))
    (t f)))

(defun fo5-literal-sign (lit) (car lit))
(defun fo5-literal-atom (lit) (cadr lit))
(defun fo5-pos-lit (a) (list :pos a))
(defun fo5-neg-lit (a) (list :neg a))

(defun fo5-canonical-clause (cl)
  (fo5-canonical-sort (remove-duplicates cl :test #'equal)))

(defun fo5-canonical-clauseset (cls)
  (remove-duplicates
   (mapcar #'fo5-canonical-clause cls)
   :test #'equal))

(defun fo5-opposite-sign-p (l1 l2)
  (not (eq (fo5-literal-sign l1) (fo5-literal-sign l2))))

(defun fo5-literal-subst (lit sigma)
  (list (fo5-literal-sign lit) (fo5-subst-term (fo5-literal-atom lit) sigma)))

(defun fo5-clause-subst (cl sigma)
  (fo5-canonical-clause
   (mapcar (lambda (lit) (fo5-literal-subst lit sigma)) cl)))

(defun fo5-conjunction->clauses (f)
  (cond
    ((eq f t) nil)
    ((and (consp f) (eq (car f) 'and))
     (mapcan #'fo5-conjunction->clauses (cdr f)))
    (t (list (fo5-disjunction->clause f)))))

(defun fo5-disjunction->clause (f)
  (fo5-canonical-clause
   (cond
     ((and (consp f) (eq (car f) 'or))
      (mapcan #'fo5-disjunction->clause (cdr f)))
     ((and (consp f) (eq (car f) 'not))
      (list (fo5-neg-lit (cadr f))))
     (t
      (list (fo5-pos-lit f))))))

(defun fo5-formula->clauses (f)
  (fo5-conjunction->clauses f))

(defun fo5-positive-clause-p (cl)
  (every (lambda (lit) (eq (fo5-literal-sign lit) :pos)) cl))

(defun fo5-negative-lits (cl)
  (remove-if-not (lambda (lit) (eq (fo5-literal-sign lit) :neg)) cl))

(defun fo5-positive-lits (cl)
  (remove-if-not (lambda (lit) (eq (fo5-literal-sign lit) :pos)) cl))

(defun fo5-remove-lits (cl lits)
  (let ((ans (copy-list cl)))
    (dolist (lit lits)
      (setf ans (remove lit ans :test #'equal :count 1)))
    ans))

(defun fo5-clause-empty-p (cl) (null cl))

(defun fo5-clause-tautology-p (cl)
  (some (lambda (l1)
          (some (lambda (l2)
                  (and (fo5-opposite-sign-p l1 l2)
                       (not (eq (fo5-unify-atoms (fo5-literal-atom l1)
                                                 (fo5-literal-atom l2))
                                :fail))))
                cl))
        cl))

(defun fo5-clause-subsumes-p (c d)
  (labels ((try-match (pending env)
             (cond
               ((eq env :fail) nil)
               ((null pending) t)
               (t
                (let ((lit (car pending)))
                  (some (lambda (d-lit)
                          (when (eq (fo5-literal-sign lit) (fo5-literal-sign d-lit))
                            (let ((env2 (fo5-match-atom (fo5-literal-atom lit)
                                                        (fo5-literal-atom d-lit)
                                                        env)))
                              (try-match (cdr pending) env2))))
                        d))))))
    (try-match c nil)))

(defun fo5-forward-subsumed-p (new-clause clauses)
  (some (lambda (old) (fo5-clause-subsumes-p old new-clause)) clauses))

(defun fo5-backward-replace (new-clause clauses)
  (remove-if (lambda (old) (fo5-clause-subsumes-p new-clause old)) clauses))

(defun fo5-vars-in-term (tm)
  (cond ((fo5-variable-p tm) (list tm))
        ((consp tm) (fo5-remove-duplicates-by-string
                     (mapcan #'fo5-vars-in-term tm)))
        (t nil)))

(defun fo5-vars-in-atom (a)
  (mapcan #'fo5-vars-in-term (cdr a)))

(defun fo5-vars-in-clause (cl)
  (fo5-remove-duplicates-by-string
   (mapcan (lambda (lit) (fo5-vars-in-atom (fo5-literal-atom lit))) cl)))

(defun fo5-rename-clause-apart (cl)
  (let* ((vars (fo5-vars-in-clause cl))
         (sigma (mapcar (lambda (v) (cons v (fo5-mk-var-symbol "V"))) vars)))
    (fo5-clause-subst cl sigma)))

(defun fo5-non-empty-subsets (xs)
  (labels ((rec (ys)
             (if (null ys)
                 (list nil)
                 (let ((rest (rec (cdr ys))))
                   (append rest
                           (mapcar (lambda (r) (cons (car ys) r)) rest))))))
    (remove nil (rec xs))))

(defun fo5-unify-atom-list (atoms)
  (cond ((null atoms) nil)
        ((null (cdr atoms)) nil)
        (t
         (let ((sigma nil)
               (pivot (car atoms)))
           (dolist (a (cdr atoms) sigma)
             (setf sigma (fo5-unify-atoms (fo5-subst-term pivot sigma)
                                          (fo5-subst-term a sigma)
                                          sigma))
             (when (eq sigma :fail)
               (return :fail)))))))

(defun fo5-u-resolvents-one-way (pos-cl other-cl)
  (let* ((c (fo5-rename-clause-apart pos-cl))
         (d (fo5-rename-clause-apart other-cl))
         (csubs (fo5-non-empty-subsets (fo5-positive-lits c)))
         (dsubs (fo5-non-empty-subsets (fo5-negative-lits d)))
         (out nil))
    (dolist (cs csubs)
      (dolist (ds dsubs)
        (let* ((atoms (append (mapcar #'fo5-literal-atom cs)
                              (mapcar #'fo5-literal-atom ds)))
               (sigma (fo5-unify-atom-list atoms)))
          (unless (eq sigma :fail)
            (let* ((rest (append (fo5-remove-lits c cs)
                                 (fo5-remove-lits d ds)))
                   (res (fo5-clause-subst rest sigma)))
              (unless (or (fo5-clause-tautology-p res)
                          (member res out :test #'equal))
                (push res out)))))))
    out))

(defun fo5-positive-u-resolvents (c d)
  (append
   (if (fo5-positive-clause-p c) (fo5-u-resolvents-one-way c d) nil)
   (if (fo5-positive-clause-p d) (fo5-u-resolvents-one-way d c) nil)))

(defun fo5-add-clause-with-subsumption (clause processed worklist)
  (let ((cl (fo5-canonical-clause clause)))
    (cond
      ((fo5-clause-tautology-p cl)
       (values processed worklist nil))
      ((or (fo5-forward-subsumed-p cl processed)
           (fo5-forward-subsumed-p cl worklist))
       (values processed worklist nil))
      (t
       (let ((new-proc (fo5-backward-replace cl processed))
             (new-work (fo5-backward-replace cl worklist)))
         (values new-proc (cons cl new-work) t))))))

(defun fo5-pick-shortest (worklist)
  (let ((best (car worklist)))
    (dolist (c (cdr worklist))
      (when (< (length c) (length best))
        (setf best c)))
    best))

(defun fo5-saturate-positive-uresolution (clauses &key (max-iterations 5000))
  (let ((processed nil)
        (worklist (fo5-canonical-clauseset
                   (remove-if #'fo5-clause-tautology-p clauses)))
        (iters 0))
    (when (some #'fo5-clause-empty-p worklist)
      (return-from fo5-saturate-positive-uresolution 'valid))
    (loop while (and worklist (< iters max-iterations)) do
      (incf iters)
      (let ((given (fo5-pick-shortest worklist)))
        (setf worklist (remove given worklist :test #'equal :count 1))
        (dolist (old processed)
          (dolist (r (fo5-positive-u-resolvents given old))
            (when (fo5-clause-empty-p r)
              (return-from fo5-saturate-positive-uresolution 'valid))
            (multiple-value-bind (p w addedp)
                (fo5-add-clause-with-subsumption r processed worklist)
              (declare (ignore addedp))
              (setf processed p
                    worklist w))))
        (dolist (r (fo5-positive-u-resolvents given given))
          (when (fo5-clause-empty-p r)
            (return-from fo5-saturate-positive-uresolution 'valid))
          (multiple-value-bind (p w addedp)
              (fo5-add-clause-with-subsumption r processed worklist)
            (declare (ignore addedp))
            (setf processed p
                  worklist w)))
        (push given processed)))
    'unknown))

(defun fo5-negate-formula (f)
  (list 'not f))

(defun fo5-clausify-negation (f)
  (fo5-reset-state)
  (let* ((g1 (fo5-negate-formula f))
         (g2 (fo5-elim-iff-implies g1))
         (g3 (fo5-nnf g2))
         (g4 (fo5-standardize-apart g3))
         (g5 (fo5-skolemize g4))
         (g6 (fo5-drop-universals g5))
         (g7 (fo5-cnf-form g6))
         (cls (fo5-formula->clauses g7)))
    cls))

(defun fo-no=-val (f &key (max-iterations 5000))
  (let ((clauses (fo5-clausify-negation f)))
    (fo5-saturate-positive-uresolution clauses
                                       :max-iterations max-iterations)))


(assert (equal (fo-no=-val '(or (P a) (not (P a))))
               'valid))

(assert (equal (fo-no=-val '(implies (forall (x) (P x))
                                     (exists (y) (P y))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (and (forall (x) (implies (P x) (Q x)))
                                  (forall (x) (P x)))
                             (forall (x) (Q x))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (forall (x) (implies (P x) (Q x)))
                             (implies (exists (x) (P x))
                                      (exists (x) (Q x)))))
               'valid))

(assert (equal (fo-no=-val '(implies (exists (x) (not (P x)))
                                     (not (forall (x) (P x)))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (and (forall (x) (implies (G x) (M x)))
                                  (forall (x) (implies (M x) (H x))))
                             (forall (x) (implies (G x) (H x)))))
               'valid))

(assert (equal (fo-no=-val '(not
                             (and (forall (x y) (or (R x y) (Q x)))
                                  (forall (x) (not (R x (g x))))
                                  (forall (y) (not (Q y))))))
               'valid))

(assert (equal (fo-no=-val '(not
                             (exists (b)
                               (forall (x)
                                 (iff (S b x)
                                      (not (S x x)))))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (forall (x) (and (P x) (Q x)))
                             (and (forall (x) (P x))
                                  (forall (x) (Q x)))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (and (forall (x) (or (A x) (B x)))
                                  (forall (x) (not (A x))))
                             (forall (x) (B x))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (forall (x) (implies (Human x) (Mortal x)))
                             (implies (Human socrates)
                                      (exists (y) (Mortal y)))))
               'valid))

(assert (equal (fo-no=-val '(implies
                             (and (exists (x) (not (P x)))
                                  (forall (x) (implies (Q x) (P x))))
                             (exists (x) (not (Q x)))))
               'valid))

(assert (equal (fo-no=-val '(exists (y) (implies (P y) (forall (x) (P x)))))
               'valid))
