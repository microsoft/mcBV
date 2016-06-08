(set-logic QF_BV)

(set-info :status sat)

(declare-fun X () (_ BitVec 8))
(declare-fun Y () (_ BitVec 32))

(assert (and 
			(not (= (bvand (bvshl (bvand ((_ zero_extend 24) X) (_ bv255 32)) ((_ zero_extend 24) (_ bv2 8))) (_ bv15 32)) (_ bv0 32))) 
			(= Y (bvand (bvshl (bvand ((_ zero_extend 24) X) (_ bv255 32)) ((_ zero_extend 24) (_ bv2 8))) (_ bv15 32)))
			(not (= (bvsub Y (_ bv3 32)) (_ bv0 32))) 
			(bvslt (_ bv0 32) (bvadd Y (_ bv115 32))) 
			(not (= Y (_ bv4294967295 32)))
			))

(check-sat)
; (get-model)
