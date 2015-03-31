#lang racket

;; basic Fourier-Motzkin elimination functions
;; and some other basic math reasoning for inequalities
;; & linear expressions


(require redex "dtr-lang.rkt" "fme-bridge.rkt")
(provide (all-defined-out))

(define-judgment-form λDTR
  #:mode (fme-imp I I)
  #:contract (fme-imp Φ Φ)
  [(where #t ,(redex-fme-imp? (term Φ_1) (term Φ_2)))
   ----------- "FME-Imp"
   (fme-imp Φ_1 Φ_2)])

(define-judgment-form λDTR
  #:mode (fme-sat I)
  #:contract (fme-sat Φ)
  [(where #t ,(redex-fme-sat? (term Φ)))
   ----------- "FME-Sat"
   (fme-sat Φ)])

(define-metafunction λDTR
  fme-elim : Φ x -> Φ
  [(fme-elim Φ x) ,(sli->redex (fme-elim-var (redex->fme (term Φ)) (term x)))])

(define-judgment-form λDTR
  #:mode (lexp-equal I I)
  #:contract (lexp-equal o o)
  [----------- "LExp-Equal-Refl"
   (lexp-equal o o)]
  [(where #t (redex-sli-equal? o_1 o_2))
   ----------- "LExp-Equal"
   (lexp-equal o_1 o_2)])
