(set-logic QF_BV)

(set-info :status unsat)

(declare-const X (_ BitVec 4))

(assert (and
			(= X #x1)
			(bvslt X #xF)))

(check-sat)
