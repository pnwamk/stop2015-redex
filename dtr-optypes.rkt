#lang racket

;; definitions herein are similar to Tobin-Hochstadt & Felleisen's
;; ICFP 2010 "Logical Types for Untyped Languages", but with added
;; details for refinements and linear inequalities

(require redex "dtr-lang.rkt")
(provide (all-defined-out))

(define-metafunction λDTR
  op-τ : op -> τ
  [(op-τ add1) (x : Int → (Int= (+ 1 (id x))) 
                  (TT FF (+ 1 (id x))))]
  [(op-τ +) (x : Int → 
               (y : Int → (Int= (+ (id x) (id y)))
                  (TT FF (+ (id x) (id y))))
               (TT FF Ø))]
  [(op-τ (* i)) (x : Int → (Int= (* i (id x)))
                   (TT FF (* i (id x))))]
  [(op-τ zero?) (x : Int → 
                   (U #t #f)
                   ((is x (Int= 0))
                    (Or: (is x (Int> 0))
                         (is x (Int< 0)))
                    Ø))]
  [(op-τ <=) (x : Int → 
                (y : Int → (U #t #f)
                   ((And: (is x (Int<= (id y)))
                          (is y (Int>= (id x))))
                    (And: (is x (Int> (id y)))
                          (is y (Int< (id x))))
                    Ø))
                (TT FF Ø))]
  [(op-τ int?) (x : Top → 
                  (U #t #f)
                  ((is x Int) (! x Int) Ø))]
  [(op-τ str?) (x : Top → 
                  (U #t #f)
                  ((is x Str) (! x Str) Ø))]
  [(op-τ str-len) (x : Str → 
                     Int 
                     (TT FF Ø))]
  [(op-τ vec-len) (x : (♯ Top) → (Int= (o-len (id x)))
                     (TT FF ((LEN) @ x)))]
  [(op-τ error) (x : Str → (U) 
                  (FF FF Ø))]
  [(op-τ bool?) (x : Top → 
                   (U #t #f)
                   ((is x (U #t #f)) (! x (U #t #f)) Ø))]
  [(op-τ proc?) (x : Top → 
                   (U #t #f)
                   ((is x (y : (U) → Top (TT TT Ø)))
                    (! x (y : (U) → Top (TT TT Ø)))
                    Ø))]
  [(op-τ cons?) (x : Top → 
                   (U #t #f)
                   ((is x (Top × Top))
                    (! x (Top × Top))
                    Ø))]
  [(op-τ vec?) (x : Top → 
                   (U #t #f)
                   ((is x (♯ Top))
                    (! x (♯ Top))
                    Ø))]
  [(op-τ neg) (x : (U Int #t #f) → 
                   (y : (U Int #t #f) where (Or: (And: (is x Int) (is y Int))
                                                 (And: (is x (U #t #f)) (is y (U #t #f)))))
                   (TT TT Ø))])
