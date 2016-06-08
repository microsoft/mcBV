(set-logic QF_BV)
(set-info :status sat)

(declare-fun v1 () (_ BitVec 32))
(declare-fun v3 () (_ BitVec 32))
(declare-fun v4 () (_ BitVec 32))
(declare-fun v5 () (_ BitVec 1))

(assert 
	(= (ite 
		   (= (_ bv1 1) v5)
		   (bvudiv v1 v3)
		   v4) 
		v1)
	)

(check-sat)

