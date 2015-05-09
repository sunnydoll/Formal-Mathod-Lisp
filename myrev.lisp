(defunc app (a b)
  :input-contract (and (true-listp a) (true-listp b))
  :output-contract (true-listp (app a b))
 (if (endp a)
     b
     (cons (first a) (app (rest a) b))))

(thm (implies (true-listp x)
     (equal (app x nil) x)))

(thm (implies (and (true-listp x) (true-listp y))
              (equal (len (app x y)) (+ (len x) (len y)))))
     
(thm (implies (and (true-listp x) (true-listp y) (true-listp z))
              (equal (app (app x y) z) (app x (app y z)))))


(defunc myrev (a)
:input-contract (true-listp a)
:output-contract (true-listp (myrev a))
  (if (endp a)
    nil
    (app (myrev (rest a)) (cons (first a) nil))))
