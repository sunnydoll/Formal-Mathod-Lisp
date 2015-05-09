;$ACL2s-SMode$;Programming
(defun lookup (target enviroment)
  (if 
    (null enviroment) 
    (er hard 'lookup "Variable Name Not Found")
    (if
      (equal (car (car enviroment)) target)
      (car (cdr (car enviroment)))
      (lookup target (cdr enviroment))
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

(defun is-ite (expression)
  (equal (first expression) 'ite)
)

(defun op1 (expr)
  (second expr))

(defun op2 (expr)
  (third expr))

(defun op3 (expr)
  (fourth expr))


(defun bool-eval (expr env)
  (cond
    ( (is-constant expr) expr )
    ( (is-variable expr) (lookup expr env) )
    ( (is-not expr) (not (bool-eval (op1 expr) env)) )
    ( (is-or expr) (or (bool-eval (op1 expr) env) (bool-eval (op2 expr) env)) )
    ( (is-and expr) (and (bool-eval (op1 expr) env) (bool-eval (op2 expr) env)) )
  )
)

(mutual-recursion
(defun nnf-not (expr)
  (cond
   ( (is-constant (op1 expr)) expr )
   ( (is-variable (op1 expr)) expr )
   ( (is-not (op1 expr)) (nnf (op1 (op1 expr))) )
   ( (is-or (op1 expr)) (list 'and (nnf (list 'not (op1 (op1 expr))))
                                   (nnf (list 'not (op2 (op1 expr))))) ) 
   ( (is-and (op1 expr)) (list 'or (nnf (list 'not (op1 (op1 expr))))
                                   (nnf (list 'not (op2 (op1 expr))))) )
  )
)

(defun nnf (expr)
  (cond
   ( (is-constant expr) expr )
   ( (is-variable expr) expr )
   ( (is-not expr) (nnf-not expr) )
   ( (is-or expr) (list 'or (nnf (op1 expr)) (nnf (op2 expr))) )
   ( (is-and expr) (list 'and (nnf (op1 expr)) (nnf (op2 expr))) )
  ) 
)
)

(defun is-nnf (expr)
  (cond
   ( (is-constant expr) t)
   ( (is-variable expr) t )
   ( (is-not expr) (is-variable (op1 expr)) )
   ( (is-or expr) (and (is-nnf (op1 expr)) (is-nnf (op2 expr))) )
   ( (is-and expr) (and (is-nnf (op1 expr)) (is-nnf (op2 expr))) )
  ) 
)

(defun no-or (expr)
  (cond
   ( (is-constant expr) t)
   ( (is-variable expr) t )
   ( (is-not expr) (no-or (op1 expr)) )
   ( (is-or expr) nil )
   ( (is-and expr) (and (no-or (op1 expr)) (no-or (op2 expr))) )
  ) 
)

(defun no-andor (expr)
  (cond
   ( (is-constant expr) t )
   ( (is-variable expr) t )
   ( (is-not expr) (no-andor (op1 expr)) )
   ( (is-or expr) (and (no-andor (op1 expr)) (no-andor (op2 expr))) )
   ( (is-and expr) (and (no-or (op1 expr)) (no-or (op2 expr))) )
  )
)
                      
(defun is-dnf (expr)
  (and (is-nnf expr) (no-andor expr))
)

; assume (and (is-dnf expr1) (is-dnf expr2))
; distribute and over or in (and expr1 expr2)
(defun distrib-andor (expr1 expr2)
  (cond
   ( (and (not (is-or expr1)) (not (is-or expr2))) (list 'and expr1 expr2) )
   ( (and (not (is-or expr1)) (is-or expr2))
      (list 'or (distrib-andor expr1 (op1 expr2)) 
                (distrib-andor expr1 (op2 expr2))) )
   ( (and (is-or expr1) (not (is-or expr2)))
      (list 'or (distrib-andor (op1 expr1) expr2) 
                (distrib-andor (op2 expr1) expr2)) )
   ( (and (is-or expr1) (is-or expr2))
      (list 'or (distrib-andor (op1 expr1) (op1 expr2))
                (list 'or (distrib-andor (op1 expr1) (op2 expr2))
                      (list 'or (distrib-andor (op2 expr1) (op1 expr2))
                            (distrib-andor (op2 expr1) (op2 expr2))))) )
  )
)
   
; assume (is-nnf expr)
(defun dnf (expr)
  (cond
   ( (is-constant expr) expr )
   ( (is-variable expr) expr )
   ( (is-not expr) expr )
   ( (is-or expr) (list 'or (dnf (op1 expr)) (dnf (op2 expr))) )
   ( (is-and expr) (distrib-andor (dnf (op1 expr)) (dnf (op2 expr))) )
  )
)