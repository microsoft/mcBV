(set-logic QF_BV)

(set-info :status sat)

(declare-fun X () (_ BitVec 8))
(declare-fun Y () (_ BitVec 32))

(declare-fun k!0 () (_ BitVec 2))     
(declare-fun mcbv!1 () (_ BitVec 32))
(declare-fun mcbv!2 () (_ BitVec 32)) 
(declare-fun mcbv!3 () (_ BitVec 30))
(declare-fun mcbv!4 () (_ BitVec 32))

(assert (and
	(not (= k!0 #b00)) 
	(= Y mcbv!1)
	(not (= Y #x00000003))
	(bvule #x80000000 mcbv!2)
	(not (= Y #x7fffff8d))
	(not (= Y #xffffffff))
	(= mcbv!1 mcbv!4)
	(= mcbv!2 (bvadd #x80000072 Y))
	(= mcbv!3 (concat #x0000000 k!0))
	(= mcbv!4 (concat mcbv!3 #b00))
))

;; Z3 says SAT w/ the following model:
;; 
;; (model 
;;   (define-fun k!0 () (_ BitVec 2)
;;     #b01)
;;   (define-fun Y () (_ BitVec 32)
;;     #x00000004)
;;   (define-fun mcbv!3 () (_ BitVec 30)
;;     #b000000000000000000000000000001)
;;   (define-fun mcbv!2 () (_ BitVec 32)
;;     #x80000076)
;;   (define-fun mcbv!4 () (_ BitVec 32)
;;     #x00000004)
;;   (define-fun mcbv!1 () (_ BitVec 32)
;;     #x00000004)
;; )


(check-sat)
; (get-model)
