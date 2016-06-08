(set-logic QF_BV)
(set-info :status sat)

(declare-fun v1 () (_ BitVec 8))
(declare-fun v3 () (_ BitVec 8))
(declare-fun v4 () (_ BitVec 8))
(declare-fun v5 () (_ BitVec 1))

(assert 
	(not (= (ite 
				true
				(bvudiv v1 v3)
				v4) 
			 v1))
	)

(check-sat)

