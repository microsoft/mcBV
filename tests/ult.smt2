(set-logic QF_BV)

(set-info :status sat)

(declare-fun X () (_ BitVec 8))
(declare-fun mcbv!0 () (_ BitVec 8))


(assert (bvugt #x01 X))

;; The above gets rewritten to:

;; (assert (bvule #x01 mcbv!0))
;; (assert (not (= X #x00)))
;; (assert (= mcbv!0 (bvadd #xff X)))

;; 1:bv := Z3's mcbv!0 
;; [2]  := Z3's (bvule #x01 mcbv!0) 
;; 3:bv := Z3's X 
;; [4]  := Z3's (= X #x00) 
;; [5]  := Z3's (= mcbv!0 (bvadd #xff X)) 

;; Boolean watches: 
;;  | ==> 2
;;  | ==> -4
;;  | ==> 5


(check-sat) 
; (get-model)

