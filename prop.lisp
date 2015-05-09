;$ACL2s-SMode$;ACL2s
(thm (implies (and (booleanp p) (booleanp q))
(iff (implies p q) (or (not p) q))))

(thm (implies (and (booleanp p) (booleanp q))
              (iff (and p q) (if p q nil))))

(thm (implies (and (booleanp p) (booleanp q))
              (iff (or p q) (if p t q))))

(thm (implies (booleanp p)
              (iff (not p) (if p nil t))))#|ACL2s-ToDo-Line|#


     
(thm (implies (and (booleanp p) (booleanp q) (booleanp r))
              (implies (and (iff p q) r) (not p))))

(thm (implies (and (booleanp p) (booleanp q))
(iff (xor p q) (or p q))))