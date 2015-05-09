;$ACL2s-SMode$;Bare Bones
(defunc booleanp (x)
   :input-contract t
   :output-contract (booleanp (booleanp x))
(if (equal x t)
     t
    (equal x nil)))

(defunc and (a b)
   :input-contract (if (booleanp a) (booleanp b) nil)
   :output-contract (booleanp (and a b))
(if a b nil))

(check= (and nil nil) nil)
(check= (and nil t) nil)
(check= (and t nil) nil)
(check= (and t t) t)

(defunc or (a b)
   :input-contract (and (booleanp a) (booleanp b))
   :output-contract (booleanp (or a b))
(if a t b))


(check= (or nil nil) nil)
(check= (or nil t) t)
(check= (or t nil) t)
(check= (or t t) t)#|ACL2s-ToDo-Line|#




