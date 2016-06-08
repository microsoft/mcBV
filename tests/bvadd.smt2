(set-logic QF_BV)
(set-info :source |
	Constructed by Aleksandar Zeljic to test bvAdd
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))


(assert (bvule b #b0101))
(assert (bvule a #b0011))
(assert (bvuge c #b1000))
(assert (= c (bvadd a b)))
(check-sat)
(exit)
