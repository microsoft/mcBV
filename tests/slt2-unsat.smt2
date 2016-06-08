(set-logic QF_BV)

(set-info :status unsat)

(declare-const X (_ BitVec 4))

(assert (and
			(not (bvslt X #x0))
			(bvslt X #xF)))
			
(check-sat)
