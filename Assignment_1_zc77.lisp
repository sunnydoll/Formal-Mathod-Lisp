; *************** BEGIN INITIALIZATION FOR PROGRAMMING MODE *************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the TRACE* book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the EVALABLE-LD-PRINTING book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "evalable-ld-printing" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil);v4.0 change

;; #+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading DataDef+RandomTesting book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
;; (include-book "countereg-gen/top" :uncertified-okp nil :dir :system :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading programming mode.") (value :invisible))


(er-progn 
  (program)
  (defun book-beginning () ()) ; to prevent book development
  (set-irrelevant-formals-ok :warn)
  (set-bogus-mutual-recursion-ok :warn)
  (set-ignore-ok :warn)
  (set-verify-guards-eagerness 0)
  (set-default-hints '(("Goal" :error "This depends on a proof, and proofs are disabled in Programming mode.  The session mode can be changed under the \"ACL2s\" menu.")))
  (reset-prehistory t)
  (set-guard-checking :none)
  (assign evalable-ld-printingp t)
  (assign evalable-printing-abstractions '(list cons))
  (assign triple-print-prefix "; "))
  

(cw "~@0Programming mode loaded.~%~@1"
      #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
      #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")

; **************** END INITIALIZATION FOR PROGRAMMING MODE **************** ;
;$ACL2s-SMode$;Programming
#|
Course: CS680 - Formal Methods
Professor: Jeremy Johnson
Student: Zhichao Cao
Email: zc77@drexel.edu
|#

(defun lookup (target enviroment)
  (if 
    (null enviroment) 
    (er hard 'lookup "Variable Name Not Found")
    (if
      (equal (first (first enviroment)) target)
      (first (rest (first enviroment)))
      (lookup target (rest enviroment))
     )
    )
  )


(defun is-reserved-word (word)
  (cond
   ( (equal word 't) t)
   ( (equal word 'nil) t)
   ( (equal word 'or) t)
   ( (equal word 'and) t)
   ( (equal word 'not) t)
   ( (equal word 'implies) t)
  ( (equal word 'iff) t)
   ;Otherwise
   ( t nil)
  )
 )

(defun is-constant (expression)
  ;This is true when the expression is t or nil
  ;It is false otherwise
  (or (equal expression t) (equal expression nil))
 )

(defun is-variable (expression)
  (and
   (symbolp expression)
   (not (is-reserved-word expression))
  )
)

(defun is-not (expression)
  (equal (first expression) 'not)
)

(defun is-or (expression)
  (equal (first expression) 'or)
)

(defun is-and (expression)
  (equal (first expression) 'and)
)

(defun is-implies (expression)
  (equal (first expression) 'implies)
)

(defun is-iff (expression)
  (equal (first expression) 'iff)
)
(defun op1 (expr)
  (second expr))

(defun op2 (expr)
  (third expr))

(defun bool-eval (expr env)
  (cond
    ( (is-constant expr) expr )
    ( (is-variable expr) (lookup expr env) )
    ( (is-not expr) (not (bool-eval (op1 expr) env)) )
    ( (is-or expr) (or (bool-eval (op1 expr) env) (bool-eval (op2 expr) env)) )
    ( (is-and expr) (and (bool-eval (op1 expr) env) (bool-eval (op2 expr) env)) )
    ( (is-implies expr) (implies (bool-eval (op1 expr) env) (bool-eval (op2 expr) env)) )
    ( (is-iff expr) (iff (bool-eval (op1 expr) env) (bool-eval (op2 expr) env)) )
  )
)

(defun get-variables (expr)
  (cond
    ( (is-constant expr) '() )
    ( (is-variable expr) (list expr) )
    ( (is-not expr) (get-variables (op1 expr)) )
    ( (or (is-or expr) (is-and expr) (is-implies expr) (is-iff expr))
      (remove-duplicates (append (get-variables (op1 expr))
                                 (get-variables (op2 expr)))) )
  )
)

(check= (get-variables '(and p (or p q))) '(p q))

(defun insert-binding (b envs)
  (if (equal envs nil)
    nil
    (cons (cons b (first envs)) (insert-binding b (rest envs))))
)

(check= (insert-binding '(a nil) '( ((b nil)) )) '( ((a nil) (b nil)) ))
(check= (insert-binding '(a nil) '( ((b nil)) ((b t)) ))
        '( ((a nil) (b nil)) ((a nil) (b t)) ))

(defun make-truth-table (vars)
  (if (equal vars nil)
    '( () )
    (let ( (tt (make-truth-table (rest vars))) )
      (append (insert-binding (list (first vars) nil) tt)
              (insert-binding (list (first vars) t) tt)))))

(check= (make-truth-table '(a)) '( ((a nil)) ((a t)) ))
(check= (make-truth-table '(a b)) '( ((a nil) (b nil))
                                     ((a nil) (b t))
                                     ((a t) (b nil))
                                     ((a t) (b t)) ))

(defun eval-truth-table (expr envs)
  (if (equal envs nil)
    nil
    (cons (bool-eval expr (first envs)) (eval-truth-table expr (rest envs)))
  )
)

(check= (eval-truth-table '(or a b) '( ((a nil) (b nil))
                                     ((a nil) (b t))
                                     ((a t) (b nil))
                                     ((a t) (b t)) ))
        '(nil t t t))

(check= (eval-truth-table '(iff (implies a b) (or (not a) b)) 
                                    '( ((a nil) (b nil))
                                     ((a nil) (b t))
                                     ((a t) (b nil))
                                     ((a t) (b t)) ))
        '(t t t t))

(defun all-true (blist)
  (if (equal blist nil)
    t
    (and (first blist) (all-true (rest blist)))))

(check= (all-true (eval-truth-table '(iff (implies a b) (or (not a) b)) 
                                    '( ((a nil) (b nil))
                                     ((a nil) (b t))
                                     ((a t) (b nil))
                                     ((a t) (b t)) ))) t)

(defun valid (expr)
  (all-true (eval-truth-table expr (make-truth-table (get-variables expr))))
)

(check= (valid '(iff (implies a b) (or (not a) b))) t)
(check= (valid '(iff (or a b) (or b a))) t)
(check= (valid '(iff (iff a b) (iff b a))) t)
(check= (valid '(iff (implies a b) (implies b a))) nil)

;; Functions defined below are defined for Assignment 1
(defun has-true (blist)
  ;; Function checks whether there is a true value in the result list of eval-truth-table function
  (if (equal blist nil)
    nil
    (or (first blist) (has-true (rest blist))))
    ;(if (equal (first blist) t) t (has-true (rest blist))))
)

(check= (has-true (eval-truth-table '(or a b) '( ((a nil) (b nil))
                                     ((a nil) (b t))
                                     ((a t) (b nil))
                                     ((a t) (b t)) ))) t)

(check= (has-true (eval-truth-table '(iff (implies a b) (implies b a)) 
                                    '( ((a nil) (b nil))
                                     ((a nil) (b t))
                                     ((a t) (b nil))
                                     ((a t) (b t)) ))) t)

(defun satisfy (expr)
  ;; Function uses a truth table to check whether a boolean formula can be satisfied
  (has-true (eval-truth-table expr (make-truth-table (get-variables expr))))
)

(check= (satisfy '(iff (implies a b) (or (not a) b))) t)
(check= (satisfy '(iff (or a b) (or b a))) t)
(check= (satisfy '(iff (iff a b) (iff b a))) t)
(check= (satisfy '(and a (not a))) nil)
(check= (satisfy '(or a (not a))) t)
(check= (satisfy '(iff (implies a b) (implies b a))) t)
(check= (satisfy '(not (iff (implies a b) (implies b a)))) t)

(defun alter-valid (expr)
  (if (equal (satisfy (list 'not expr)) t) nil t)
 )

(check= (alter-valid '(iff (implies a b) (or (not a) b))) t)
(check= (alter-valid '(iff (or a b) (or b a))) t)
(check= (alter-valid '(iff (iff a b) (iff b a))) t)
(check= (alter-valid '(iff (implies a b) (implies b a))) nil)
