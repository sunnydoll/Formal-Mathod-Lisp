;$ACL2s-SMode$;Programming
#|

This file contains an implementation of a tautology checker for boolean
expressions.  

(valid expr) = t when expr is valid.  I.E. expr is true for all possible models
(truth assignments) of the variables occurring in expr.  Otherwise (valid expr) = nil.

The function valid is implemented by constructing a truth table for the variables
occuring in the expression and then evaluating the expression for each entry in the
truth table.

The function (bool-eval expr env) takes a boolean expression and an environment and
returns t or nil depending on whether expr is true or false for the assignment of the
variables in the environment.  It is assumed that all variables in expr have an
assignment in env.

An environment is a list of bindings where a binding is a pair containing a
variable and its associated value
env = ((var1 val1) ... (varn valn))
lookup returns the value associated with a given variable provided a corresponding
binding exists.  If not such binding exists an error is thrown.

A variable is a symbol that is not a reserved word.

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

