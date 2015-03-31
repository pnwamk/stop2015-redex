#lang racket

;; TypeOf judgement, similar to "Logical Types for Untyped Languages"
;; but entirely algorithmic

(require redex "dtr-lang.rkt" "dtr-logic.rkt" "dtr-optypes.rkt")
(provide (all-defined-out))

;                                             ;;;; 
;                                            ;     
;  ;;;;;;;                           ;;;     ;     
;     ;    ;      ; ; ;;;     ;;;   ;   ;  ;;;;;;; 
;     ;     ;    ;  ;;   ;   ;   ; ;     ;   ;     
;     ;     ;    ;  ;    ;  ;    ; ;     ;   ;     
;     ;      ;  ;   ;    ;  ;;;;;; ;     ;   ;     
;     ;      ;  ;   ;    ;  ;      ;     ;   ;     
;     ;       ;;    ;;   ;  ;       ;   ;    ;     
;     ;       ;;    ; ;;;    ;;;;;   ;;;     ;     
;             ;     ;                              
;            ;      ;                              
;          ;;;      ;                              


(define-judgment-form λDTR
  #:mode (typeof I I O O)
  #:contract (typeof Γ e τ (ψ ψ oo))
  
  [-------------- "T-Int"
   (typeof Γ i (Int= i) (TT FF i))]
  
  [-------------- "T-Str"
   (typeof Γ string Str (TT FF Ø))]
  
  [-------------- "T-Const"
   (typeof Γ op (op-τ op) (TT FF Ø))]
  
  [-------------- "T-True"
   (typeof Γ #t #t (TT FF Ø))]
  
  [-------------- "T-False"
   (typeof Γ #f #f (FF TT Ø))]
  
  [(proves Γ (is x τ))
   -------------- "T-AnnVar"
   (typeof Γ (ann x τ) τ ((And: (! x #f) (is x τ)) 
                          (And: (is x #f) (is x τ)) 
                          (id x)))]
  
  [(typeof (env/implied-by-ψ* Γ (is x σ)) e τ (ψ_+ ψ_- oo))
   -------------- "T-Abs"
   (typeof Γ
           (λ (x : σ) e)
           (x : σ → τ (ψ_+ ψ_- oo))
           (TT FF Ø))]
  
  [(where/hidden #f ,(member (term e_1) '(car cdr vec)))
   (where/hidden ν (fresh-var Γ (e_1 e_2)))
   (typeof Γ e_1 σ_λ (ψ_1+ ψ_1- oo_1))
   (where (x : σ_f → τ_f (ψ_f+ ψ_f- oo_f)) (exists/fun-τ σ_λ))
   (typeof Γ e_2 σ_2 (ψ_2+ ψ_2- oo_2))
   (subtype Γ (id ν) σ_2 σ_f)
   (where τ_f* (update-τ Γ τ_f (is x σ_2)))
   -------------- "T-App"
   (typeof Γ
           (e_1 e_2)
           (subst τ_f* oo_2 x)
           ((And: (subst ψ_f+ oo_2 x) (true-ψ τ_f*))
            (And: (subst ψ_f- oo_2 x) (false-ψ τ_f*))
            (subst oo_f oo_2 x)))]
  
  [(typeof Γ e_1 τ_1 (ψ_1+ ψ_1- oo_1))
   (typeof (env/implied-by-ψ* Γ ψ_1+) e_2 τ_2 (ψ_2+ ψ_2- oo_2))
   (typeof (env/implied-by-ψ* Γ ψ_1-) e_3 τ_3 (ψ_3+ ψ_3- oo_3))
   ------------------------------ "T-If"
   (typeof Γ
           (if e_1 e_2 e_3)
           (τ-join τ_2 τ_3)
           ((Or: (And: ψ_1+ ψ_2+) 
                 (And: ψ_1- ψ_3+))
            (Or: (And: ψ_1+ ψ_2-) 
                 (And: ψ_1- ψ_3-))
            (oo-join oo_2 oo_3)))]
  
  [(typeof Γ e_x τ (ψ_x+ ψ_x- oo_x))
   (where ψ (And: (is x τ)
                  (Or: (And: (! x #f)  ψ_x+) 
                       (And: (is x #f) ψ_x-))))
   (typeof (env/implied-by-ψ* Γ ψ) e σ (ψ_+ ψ_- oo))
   -------------------------- "T-Let"
   (typeof Γ
           (let (x e_x) e)
           (subst σ oo_x x)
           ((subst (And: ψ_+ ψ) oo_x x)
            (subst (And: ψ_- ψ) oo_x x)
            (subst oo oo_x x)))]
  
  [(typeof Γ e_1 τ (ψ_1+ ψ_1- oo_1))
   (typeof Γ e_2 σ (ψ_2+ ψ_2- oo_2))
   ------------------------- "T-Cons"
   (typeof Γ (cons e_1 e_2) (τ × σ) (TT FF Ø))]

  [(typeof Γ e σ_c (ψ_+ ψ_- oo))
   (where (τ × σ) (exists/pair-τ σ_c))
   (where/hidden ν (fresh-var Γ (car e)))
   ------------------------- "T-Car"
   (typeof Γ
           (car e) 
           τ
           ((subst (And: (((CAR) @ ν) -! #f)
                         (And: (((CAR) @ ν) -: τ)
                               (true-ψ τ))) 
                   oo ν)
            (subst (And: (((CAR) @ ν) -: #f)
                         (And: (((CAR) @ ν) -: τ)
                               (false-ψ τ)))
                   oo ν)
            (subst ((CAR) @ ν) oo ν)))]
  
  [(typeof Γ e σ_c (ψ_+ ψ_- oo))
   (where (τ × σ) (exists/pair-τ σ_c))
   (where/hidden ν (fresh-var Γ (cdr e)))
   ------------------------- "T-Cdr"
   (typeof Γ
           (cdr e) 
           σ
           ((subst (And: (((CDR) @ ν) -! #f)
                         (And: (((CDR) @ ν) -: σ)
                               (true-ψ σ))) 
                   oo ν)
            (subst (And: (((CDR) @ ν) -: #f)
                         (And: (((CDR) @ ν) -: σ)
                               (false-ψ σ)))
                   oo ν)
            (subst ((CDR) @ ν) oo ν)))]
  
  [(typeof Γ e_0 τ_0 (ψ_0+ ψ_0- oo_0)) ...
   (where τ (τ-join τ_0 ...))
   (where i (len (e_0 ...)))
   (where/hidden ν (fresh-var Γ (vec e_0 ...)))
   ------------------------- "T-Vec"
   (typeof Γ (vec e_0 ...) (ν : (♯ τ) where (Φ= i (o-len (id ν))))
           (TT FF Ø))]
  
  [(typeof Γ e_1 σ_v (ψ_1+ ψ_1- oo_1))
   (typeof Γ e_2 σ_i (ψ_2+ ψ_2- oo_2))
   (where (♯ τ) (exists/vec-τ σ_v))
   (where o_1 (fresh-if-needed oo_1 Γ e_1 e_2))
   (where o_2 (fresh-if-needed oo_2 o_1 Γ e_1 e_2))
   (subtype (env/implied-by-ψ* Γ (o_1 -: σ_v)) o_2 σ_i (IntRange 0 (+ -1 (o-len o_1))))
   ------------------------- "T-VecRef"
   (typeof Γ (vec-ref e_1 e_2) τ 
           ((true-ψ τ) (false-ψ τ) Ø))])


