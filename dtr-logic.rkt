#lang racket

;; definitions herein are similar to Tobin-Hochstadt & Felleisen's
;; ICFP 2010 "Logical Types for Untyped Languages", but with added
;; details for refinements and linear inequalities


(require redex "dtr-lang.rkt" "dtr-fme.rkt")
(provide (all-defined-out))

(define-judgment-form λDTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj o o)]
  
  [(lexp-equal o_1 o_2)
   ------------------- "SO-Equal"
   (subobj o_1 o_2)]
  
  [------------------- "SO-Top"
   (subobj oo Ø)])

;; subtyping where the context and object are unspecified/arbitrary
(define-judgment-form λDTR
  #:mode (simple-subtype I I)
  #:contract (simple-subtype τ τ)
  [(where/hidden ν (fresh-var σ τ))
   (subtype (empty-env) (id ν) σ τ)
   --------------------------- "S-EmptyCtx"
   (simple-subtype σ τ)])

;; Φ : what linear inequalities currently hold
;; o : who are we talking about
;; τ : subtype
;; σ : supertype
(define-judgment-form λDTR
  #:mode (subtype I I I I)
  #:contract (subtype Γ o τ σ)
  [--------------- "S-Refl"
   (subtype Γ o τ τ)]
  
  [--------------- "S-Top"
   (subtype Γ o τ Top)]
  
  [(subtype Γ o σ τ)
   --------------- "S-UnionSuper"
   (subtype Γ o σ (U τ_1 ... τ τ_2 ...))]
  
  [(subtype Γ o τ σ) ...
   --------------- "S-UnionSub"
   (subtype Γ o (U τ ...) σ)]
  
  [(subtype Γ (o-car o) τ_1 τ_2)
   (subtype Γ (o-cdr o) σ_1 σ_2)
   ----------------- "S-Pair"
   (subtype Γ o (τ_1 × σ_1) (τ_2 × σ_2))]
  
  [(where/hidden ν (fresh-var Γ o τ σ))
   (subtype Γ (id ν) τ σ)
   ----------------- "S-Vec"
   (subtype Γ o (♯ τ) (♯ σ))]
  
  [(where/hidden ν (fresh-var Γ o
                              (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1))
                              (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2))))
   (where/hidden ν_x (fresh-var ν Γ o
                              (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1))
                              (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2))))
   (subtype Γ (id ν_x) σ_2 σ_1)
   (proves (env/implied-by-ψ* Γ 
                              ((id ν_x) -: σ_2)
                              ((id ν) -: (subst τ_1 (id ν_x) x)))
           ((id ν) -: (subst τ_2 (id ν_x) x)))
   (proves (env/implied-by-ψ* Γ 
                              ((id ν_x) -: σ_2)
                              (subst ψ_1+ (id ν_x) x)) 
           (subst ψ_2+ (id ν_x) y))
   (proves (env/implied-by-ψ* Γ
                              ((id ν_x) -: σ_2)
                              (subst ψ_1- (id ν_x) x))
           (subst ψ_2- (id ν_x) y))
   (subobj (subst oo_1 (id y) x) oo_2)
   ------------------------------------------ "S-Abs"
   (subtype Γ o
            (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1))
            (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2)))]
  
  [(proves (env/implied-by-ψ* Γ (o -: (subst τ_x o x)) (subst ψ_x o x))
           (o -: τ))
   ------------------- "S-Refine-Sub"
   (subtype Γ o (x : τ_x where ψ_x) τ)]
  
  [(proves (env/implied-by-ψ* Γ (o -: τ))
           (And: (o -: (subst τ_y o y)) 
                 (subst ψ_y o y)))
   ------------------- "S-Refine-Super"
   (subtype Γ o τ (y : τ_y where ψ_y))])


;                                                  
;                                                  
;                                                  
;   ;;;;;;                                         
;   ;    ;;                                        
;   ;     ;  ;;;;    ;;;;   ;    ;   ;;;;    ;;;;  
;   ;     ;  ;;  ;  ;;  ;;  ;;  ;;  ;    ;  ;    ; 
;   ;    ;;  ;      ;    ;   ;  ;   ;;;;;;  ;      
;   ;;;;;;   ;      ;    ;   ;  ;   ;        ;;;;  
;   ;        ;      ;    ;   ;;;;   ;            ; 
;   ;        ;      ;;  ;;    ;;    ;;   ;  ;    ; 
;   ;        ;       ;;;;     ;;     ;;;;;   ;;;;  
;                                                  
;                                                  
;                                                  
;                                                  


(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  
  [(subtype (env Φ (δ_1 ... δ_2 ...) ()) o_1 τ σ)
   (lexp-equal o_1 o_2)
   ---------------- "L-Sub"
   (proves (env Φ (δ_1 ... (o_1 -: τ) δ_2 ...) ()) 
           (o_2 -: σ))]
  
  [(subtype (env Φ [δ_1 ... δ_2 ...] ()) o_1 σ τ)
   (lexp-equal o_1 o_2)
   ---------------- "L-SubNot"
   (proves (env Φ (δ_1 ... (o_1 -! τ) δ_2 ...) ()) 
           (o_2 -! σ))]
  
  [(type-conflict (env Φ () ()) τ σ)
   (lexp-equal o_1 o_2)
   ---------------- "L-Conflict"
   (proves (env Φ (δ_1 ... (o_1 -: τ) δ_2 ...) ()) 
           (o_2 -! σ))]
  
  [(fme-imp Φ Φ_1)
   ---------------- "L-FME"
   (proves (env Φ δ* ()) 
           Φ_1)]
  
  [(where #f (fme-sat Φ))
   ---------------- "L-FME-Unsat"
   (proves (env Φ δ* ()) 
           ψ)]
  
  [---------------------- "L-Bot"
   (proves (env Φ (δ_1 ... (o -: (U)) δ_2 ...) ()) 
           ψ)]
  
  [---------------------- "L-True"
   (proves Γ TT)]
  
  [(proves (env Φ δ* (ψ_1 ...)) 
           ψ)
   ---------------------- "L-Weaken"
   (proves (env Φ δ* (TT ψ_1 ...)) 
           ψ)]
  
  [---------------------- "L-ExFalso"
   (proves (env Φ δ* (FF ψ_1 ...)) 
           ψ)]
  
  [(proves (env Φ δ* [ψ_1 ψ_2 ψ_3 ...]) 
           ψ)
   ---------------------- "L-Simp"
   (proves (env Φ δ* ((ψ_1 ∧ ψ_2) ψ_3 ...)) 
           ψ)]
  
  [(proves (env Φ δ* ()) ψ_1)
   (proves (env Φ δ* ()) ψ_2)
   ---------------------- "L-Conj"
   (proves (env Φ δ* ()) 
           (ψ_1 ∧ ψ_2))]
  
  [(proves (env Φ δ* (ψ_1 ψ_3 ...)) 
           ψ)
   (proves (env Φ δ* (ψ_2 ψ_3 ...)) 
           ψ)
   ---------------------- "L-DisjElim"
   (proves (env Φ δ* ((ψ_1 ∨ ψ_2) ψ_3 ...)) 
           ψ)]
  
  [(proves (env Φ δ* ()) ψ_1)
   ---------------------- "L-Add-L"
   (proves (env Φ δ* ()) 
           (ψ_1 ∨ ψ_2))]
  
  [(proves (env Φ δ* ()) 
           ψ_2)
   ---------------------- "L-Add-R"
   (proves (env Φ δ* ()) 
           (ψ_1 ∨ ψ_2))]
  
  [(proves (env (app Φ Φ_1) δ* (ψ_2 ψ_3 ...)) 
           ψ)
   ---------------------- "L-SLI"
   (proves (env Φ δ* (Φ_1 ψ_2 ψ_3 ...)) 
           ψ)]
  
  [(where Φ_2 (app Φ Φ_1))
   (proves (env Φ_2 (Φ-update-δ* δ* Φ_2) ()) 
           ψ)
   ---------------------- "L-SLI/Φ"
   (proves (env Φ δ* (Φ_1)) 
           ψ)]
  
  [(contains-non-δ (ψ_2 ...))
   (proves (env Φ δ* (ψ_2 ... δ_1)) 
           ψ)
   ---------------------- "L-Delay-δ"
   (proves (env Φ δ* (δ_1 ψ_2 ...)) 
           ψ)]
  
  [(proves (env Φ
                (ext (update-ψ* (Φ-env: Φ) δ* δ_1) δ_1)
                (update-ψ* (Φ-env: Φ) (δ_2 δ_3 ...) δ_1))
           ψ)
   ---------------------- "L-Update"
   (proves (env Φ δ* (δ_1 δ_2 δ_3 ...)) 
           ψ)]
  
  [(proves (env Φ
                (Φ-update-δ* (ext (update-ψ* (Φ-env: Φ) δ* δ) δ) Φ)
                ())
           ψ)
   ---------------------- "L-Update/Φ"
   (proves (env Φ δ* (δ)) 
           ψ)])



;                        ;                                 
;                        ;                                 
;   ;    ;               ;           ;                     
;   ;    ;  ; ;;;    ;;; ;   ;;;   ;;;;;;     ;;;    ;;;;  
;   ;    ;  ;;   ;  ;   ;;      ;    ;       ;   ;  ;      
;   ;    ;  ;    ;  ;    ;      ;    ;      ;    ;  ;;     
;   ;    ;  ;    ;  ;    ;   ;;;;    ;      ;;;;;;    ;;   
;   ;    ;  ;    ;  ;    ;  ;   ;    ;      ;           ;  
;   ;    ;  ;;   ;  ;   ;;  ;   ;    ;      ;           ;  
;    ;;;;   ; ;;;    ;;; ;   ;;;;;    ;;;    ;;;;;  ;;;;   
;           ;                                              
;           ;                                              
;           ;                                              


(define-metafunction λDTR
  update-π : Γ -? τ -? σ π -> τ
  ;; updates CAR/CDR
  [(update-π Γ -?_τ τ -?_σ σ [pe ... CAR])
   (update-π Γ -?_τ τ -?_σ (σ × Top) [pe ... ])]
  
  [(update-π Γ -?_τ τ -?_σ σ [pe ... CDR])
   (update-π Γ -?_τ τ -?_σ (Top × σ) [pe ... ])]
  
  ;; updates LEN
  [(update-π Γ -?_τ τ -?_σ σ [pe ... LEN])
   (update-π Γ -?_τ τ -?_σ (♯ Top) [pe ... ])]
  
  ;; restrict
  [(update-π Γ -: τ -: σ ()) (restrict Γ τ σ)]
  
  ;; remove
  [(update-π Γ -: τ -! σ ()) (remove Γ τ σ)]
  [(update-π Γ -! τ -: σ ()) τ] ; can't flip them and remove, since τ's 
                                ; boolean is fixed by caller already
  ; negation union
  [(update-π Γ -! τ -! σ ()) σ
   (where/hidden ν (fresh-var Γ τ σ))
   (judgment-holds (subtype Γ (id ν) τ σ))]
  [(update-π Γ -! τ -! σ ()) τ
   (where/hidden ν (fresh-var Γ τ σ))
   (where/hidden #f (subtype Γ (id ν) τ σ))
   (judgment-holds (subtype Γ (id ν) σ τ))]
  [(update-π Γ -! τ -! σ ()) (U: τ σ)
   (where/hidden ν (fresh-var Γ τ σ))
   (where/hidden #f (subtype Γ (id ν) τ σ))
   (where/hidden #f (subtype Γ (id ν) σ τ))])


(define-metafunction λDTR
  restrict : Γ τ σ -> τ
  ;; No common value
  [(restrict Γ τ σ) (U)
   (judgment-holds (type-conflict Γ τ σ))]
  
  ;; Refinements
  ;; dnf on the conjuction should simplify obvious contradictions
  [(restrict Γ (x : τ_x where ψ_x) (y : τ_y where ψ_y))
   (x : (restrict Γ τ_x τ_y) where (dnf (And: ψ_x (subst ψ_y (id x) y))))
   (where/hidden #f (type-conflict Γ (x : τ_x where ψ_x) (y : τ_y where ψ_y)))]
  [(restrict Γ (x : τ_x where ψ_x) τ)
   (x : (restrict Γ τ_x τ) where ψ_x)
   (where/hidden #f (is-Refine τ))
   (where/hidden #f (type-conflict Γ (x : τ_x where ψ_x) τ))]
  [(restrict Γ τ (y : τ_y where ψ_y)) (y : (restrict Γ τ τ_y) where ψ_y)
   (where/hidden #f (is-Refine τ))
   (where/hidden #f (type-conflict Γ τ (y : τ_y where ψ_y)))]
  
  ;; Unions
  [(restrict Γ (U τ ...) σ) (U: ,@(map (λ (t) (term (restrict Γ ,t σ))) (term (τ ...))))
   (where/hidden #f (type-conflict Γ (U τ ...) σ))]
  
  [(restrict Γ τ (U σ ...)) (U: ,@(map (λ (t) (term (restrict Γ τ ,t))) (term (σ ...))))
   (where/hidden #f (is-U τ))
   (where/hidden #f (type-conflict Γ τ (U σ ...)))]
  
  ;; Pairs
  [(restrict Γ (τ_0 × σ_0) (τ_1 × σ_1)) (Pair: (restrict Γ τ_0 τ_1) (restrict Γ σ_0 σ_1))
   (where/hidden ν (fresh-var Γ τ_0 σ_0 τ_1 σ_1))
   (where/hidden #f (subtype Γ (id ν) (τ_0 × σ_0) (τ_1 × σ_1)))]
  
  ;; Vecs
  [(restrict Γ (♯ τ) (♯ σ)) (Vec: (restrict Γ τ σ))
   (where/hidden ν (fresh-var Γ τ σ))
   (where/hidden #f (subtype Γ (id ν) (♯ τ) (♯ σ)))]
  
  ;; else if τ <: σ
  [(restrict Γ τ σ) τ
   (where/hidden ν (fresh-var Γ τ σ))
   (judgment-holds (subtype Γ (id ν) τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))]
  
  ;; else
  [(restrict Γ τ σ) σ
   (where/hidden ν (fresh-var Γ τ σ))
   (where #f (subtype Γ (id ν) τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))])

;; remove
(define-metafunction λDTR
  remove : Γ τ σ -> τ
  ;; τ_1 <: τ_2
  [(remove Γ τ σ) (U)
   (where/hidden ν (fresh-var Γ τ σ))
   (judgment-holds (subtype Γ (id ν) τ σ))]
  
  ;; Union
  [(remove Γ (U τ ...) σ) (U: ,@(map (λ (t) (term (remove Γ ,t σ))) (term (τ ...))))
   (where/hidden ν (fresh-var Γ (U τ ...) σ))
   (where/hidden #f (subtype Γ (id ν) (U τ ...) σ))]
  
  ;; Refinement
  [(remove Γ (x : τ where ψ_x) σ) (x : (remove Γ τ σ) where ψ_x)
   (where/hidden ν (fresh-var Γ (x : τ where ψ_x) σ))
   (where/hidden #f (subtype Γ (id ν) (x : τ where ψ_x) σ))
   (where/hidden #f (is-Refine σ))]
  
  ;; Pairs
  [(remove Γ (τ_0 × σ_0) (τ_1 × σ_1)) (Pair: (remove Γ τ_0 τ_1) 
                                             (remove Γ σ_0 σ_1))
   (where/hidden ν (fresh-var Γ (τ_0 × σ_0) (τ_1 × σ_1)))
   (where/hidden #f (subtype Γ (id ν) (τ_0 × σ_0) (τ_1 × σ_1)))]
  
  ;; Vecs
  [(remove Γ (♯ τ) (♯ σ)) (Vec: (remove Γ τ σ))
   (where/hidden ν (fresh-var Γ (♯ τ) (♯ σ)))
   (where/hidden #f (subtype Γ (id ν) (♯ τ) (♯ σ)))]
  
  ;; non-special-case
  [(remove Γ τ σ) τ
   (where/hidden ν (fresh-var Γ τ σ))
   (where/hidden #f (subtype Γ (id ν) τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-Refine τ))
   (where/hidden #f ,(and (term (is-Pair τ)) (term (is-Pair σ))))
   (where/hidden #f ,(and (term (is-Vec τ)) (term (is-Vec σ))))])

(define-metafunction λDTR
  update-τ : Γ τ δ -> τ
  [(update-τ Γ Top δ) Top]
  [(update-τ Γ Int δ) Int]
  [(update-τ Γ Str δ) Str]
  [(update-τ Γ #t δ) #t]
  [(update-τ Γ #f δ) #f]
  [(update-τ Γ (U τ ...) δ) (U: (update-τ Γ τ δ) ...)]
  [(update-τ Γ (τ × σ) δ)
   (Pair: (update-τ Γ τ δ) (update-τ Γ σ δ))]
  [(update-τ Γ (♯ τ) δ)
   (Vec: (update-τ Γ τ δ))]
  [(update-τ Γ (x : σ → τ (ψ_+ ψ_- oo_f)) (o -? σ_new))
   (x : (update-τ Γ σ (o -? σ_new)) → τ (ψ_+ ψ_- oo_f))
   (where #t (var-in-o x o))]
  [(update-τ Γ (y : σ → τ (ψ_+ ψ_- oo_f)) (o -? σ_new))
   (ν : (update-τ Γ (subst-τ σ (id ν) y) (o -? σ_new))
      →
      (update-τ Γ (subst-τ τ (id ν) y) (o -? σ_new))
      ((update-ψ Γ (subst ψ_+ (id ν) y) (o -? σ_new))
       (update-ψ Γ (subst ψ_- (id ν) y) (o -? σ_new))
       (subst-oo oo_f (id ν) y)))
   (where #f (var-in-o y o))
   (where/hidden ν (fresh-var Γ (y : σ → τ (ψ_+ ψ_- oo_f)) (o -? σ_new)))]
  [(update-τ Γ (x : τ where ψ) (o -? σ)) (x : τ where ψ)
                                        (where #t (var-in-o x o))]
  [(update-τ Γ (y : τ where ψ) (o -? σ))
   (ν : (update-τ Γ (subst-τ τ (id ν) y) (o -? σ))
      where (update-ψ Γ (subst ψ (id ν) y) (o -? σ)))
   (where #f (var-in-o y o))
   (where/hidden ν (fresh-var Γ (y : τ where ψ) (o -? σ)))])



;; update type info in lhs w/ rhs if applicable
(define-metafunction λDTR
  update-δ : Γ δ δ -> δ
  ;; overlapping paths
  [(update-δ Γ 
             (((pe_τ ...) @ x) -?_τ τ) 
             (((pe_σ ... pe_τ ...) @ x) -?_σ σ))
   (((pe_τ ...) @ x) -?_τ (update-π Γ -?_τ τ -?_σ σ (pe_σ ...)))]
  
  ;; equal linear expressions, update types w/ empty path
  [(update-δ Γ (o_τ -?_τ τ) (o_σ -?_σ σ))
   (o_τ -?_τ (update-π Γ -?_τ τ -?_σ σ ()))
   (judgment-holds (lexp-equal o_τ o_σ))]
  
  ;; incompatible objects, no-op
  [(update-δ Γ (o_τ -?_τ τ) (o_σ -?_σ σ)) (o_τ -?_τ τ)
   (where #f (path-postfix o_τ o_σ))
   (where #f (lexp-equal o_τ o_σ))])

(define-metafunction λDTR
  update-ψ : Γ ψ δ -> ψ
  [(update-ψ Γ TT δ) TT]
  [(update-ψ Γ FF δ) FF]
  [(update-ψ Γ (o -: τ) δ) (update-δ Γ (o -: τ_*) δ)
   (where τ_* (update-τ Γ τ δ))]
  [(update-ψ Γ (o -! τ) δ) (update-δ Γ (o -! τ) δ)]
  [(update-ψ Γ (ψ_1 ∧ ψ_2) δ) (And: (update-ψ Γ ψ_1 δ) 
                                        (update-ψ Γ ψ_2 δ))]
  [(update-ψ Γ (ψ_1 ∨ ψ_2) δ) (Or:  (update-ψ Γ ψ_1 δ) 
                                        (update-ψ Γ ψ_2 δ))]
  [(update-ψ Γ Φ δ) Φ])

(define-metafunction λDTR
  update-ψ* : Γ ψ* δ -> ψ*
  [(update-ψ* Γ (ψ ...) δ) ((update-ψ Γ ψ δ) ...)])



(define-judgment-form λDTR
  #:mode (common-val I I I)
  #:contract (common-val Γ τ τ)
  [------------------ "CV-Eq"
   (common-val Γ τ τ)]
  
  [------------------ "CV-Top-lhs"
   (common-val Γ Top τ)]
  
  [------------------ "CV-Top-rhs"
   (common-val Γ τ Top)]
  
  [(common-val Γ τ σ)
   ------------------ "CV-Union-lhs"
   (common-val Γ (U τ_1 ... τ τ_2 ...) σ)]
  
  [(common-val Γ τ σ)
   (where/hidden #f (is-U τ))
   ------------------ "CV-Union-rhs"
   (common-val Γ τ (U σ_1 ... σ σ_2 ...))]
  
  [(common-val Γ τ_1 τ_2)
   (common-val Γ σ_1 σ_2)
   -------------------- "CV-Pair"
   (common-val Γ (τ_1 × σ_1) (τ_2 × σ_2))]
  
  [(common-val Γ τ σ)
   -------------------- "CV-Vec"
   (common-val Γ (♯ τ) (♯ σ))]
  
  [------------------ "CV-Abs"
   (common-val Γ (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1)) 
                 (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2)))]
  
  ;; We only carry the Φ with us because other contradictions
  ;; can be had by updating recursively into types with δs,
  ;; Φ is the only case where the indirect relationships
  ;; bewteen values can help prove a contradiction that
  ;; otherwise wouldn't be apparent
  [(implied-by-ψ ψ_x ψ_x*)
   (where #f (proves (env Φ () (ψ_x*)) FF))
   (common-val (env Φ δ* ψ*) τ σ)
   (not-Refine σ)
   ----------------- "CV-Refine-L"
   (common-val (env Φ δ* ψ*) (x : τ where ψ_x) σ)]
  
  [(implied-by-ψ ψ_y ψ_y*)
   (where #f (proves (env Φ () (ψ_y*)) FF))
   (common-val (env Φ δ* ψ*) τ σ)
   (not-Refine τ)
   ----------------- "CV-Refine-R"
   (common-val (env Φ δ* ψ*) τ (y : σ where ψ_y))]
  
  [(where/hidden o_ν (id (fresh-var (env Φ δ* ψ*)
                                    (x : τ where ψ_x) 
                                    (y : σ where ψ_y))))
   (implied-by-ψs ((subst ψ_x o_ν x) 
                   (subst ψ_y o_ν y))
                  ψ*_1)
   (where #f (proves (env Φ () ψ*_1)
                     FF))
   (common-val (env Φ δ* ψ*) τ σ)
   ----------------- "CV-Refine"
   (common-val (env Φ δ* ψ*) 
               (x : τ where ψ_x) 
               (y : σ where ψ_y))])

(define-judgment-form λDTR
  #:mode (type-conflict I I I)
  #:contract (type-conflict Γ τ τ)
  [(where #f (common-val Γ τ σ))
   --------------- "TC-Conflict"
   (type-conflict Γ τ σ)])


(define-judgment-form λDTR
  #:mode (contains-non-δ I)
  #:contract (contains-non-δ ψ*)
  [(where #f (is-δ ψ_2))
   ------------ "Contains-Non-δ"
   (contains-non-δ (ψ_1 ... ψ_2 ψ_3 ...))])

(define-judgment-form λDTR
  #:mode (path-postfix I I)
  #:contract (path-postfix o o)
  ;; lhs is a postfix of the rhs object 
  ;; (i.e. rhs can update lhs)
  [------------------ "Path-Postfix"
   (path-postfix ((pe_2 ...) @ x) 
                 ((pe_1 ... pe_2 ...) @ x))])


(define-metafunction λDTR
  Type: : o -? τ -> ψ
  [(Type: o -: τ) FF
   (judgment-holds (simple-subtype τ (U)))]
  [(Type: o -: τ) (o -: τ)
   (where #f (simple-subtype τ (U)))]
  [(Type: o -! τ) (o -! τ)])



(define-metafunction λDTR
  oo-join : oo oo -> oo
  [(oo-join oo Ø) Ø]
  [(oo-join Ø oo) Ø]
  [(oo-join o_1 o_2) Ø
   (where #f (lexp-equal o_1 o_2))]
  [(oo-join o_1 o_2) o_1
   (judgment-holds (lexp-equal o_1 o_2))])

(define-metafunction λDTR
  τ-join : τ ... -> τ
  [(τ-join) Top]
  [(τ-join τ) τ]
  [(τ-join τ σ) σ
   (judgment-holds (simple-subtype τ σ))]
  [(τ-join τ σ) τ
   (judgment-holds (simple-subtype σ τ))]
  [(τ-join τ σ) (U: τ σ)
   (where #f (simple-subtype τ σ))
   (where #f (simple-subtype σ τ))]
  [(τ-join τ σ_0 σ_1 σ_2)
   (τ-join (τ-join τ σ_0) σ_2)]
  [(τ-join τ σ_0 σ_1 σ_2 σ_3 ...)
   (τ-join (τ-join τ σ_0) σ_2 σ_3 ...)])






(define-metafunction λDTR
  Pair: : τ τ -> τ
  [(Pair: τ σ) (U)
   (judgment-holds (simple-subtype τ (U)))]
  [(Pair: τ σ) (U)
   (judgment-holds (simple-subtype σ (U)))
   (where/hidden #f (simple-subtype τ (U)))]
  [(Pair: τ σ) (τ × σ)
   (where #f (simple-subtype τ (U)))
   (where #f (simple-subtype σ (U)))])

(define-metafunction λDTR
  Vec: : τ -> τ
  [(Vec: τ) (U)
   (judgment-holds (simple-subtype τ (U)))]
  [(Vec: τ) (♯ τ)
   (where #f (simple-subtype τ (U)))])





(define-metafunction λDTR
  dnf : ψ -> ψ
  [(dnf ψ) ,(let* ([unfolded-ψ (term (dnf* (([] [])) ψ_2 []))]
                   [disjuncts (map (λ (univ)
                                     (match univ
                                       [(list) (term TT)]
                                       [(list '() fs)
                                        (term ,(foldl (λ (cur acc)
                                                        (match cur
                                                          [(list o b t) 
                                                           (term (And: ,acc (Type: ,o ,b ,t)))]))
                                                      (term TT)
                                                      fs))]
                                       [(list sli fs) 
                                        (term (And: ,sli ,(foldl (λ (cur acc) 
                                                                   (term (And: ,acc ,cur)))
                                                                 (term TT)
                                                                 fs)))]))
                                   unfolded-ψ)])
              (foldl 
               (λ (disj dnf) (term (Or: ,disj ,dnf)))
               (term FF) 
               disjuncts))
           (judgment-holds (implied-by-ψ ψ ψ_2))])

(define-metafunction λDTR
  ;; ((Φ (δ ...)) ...) disjuncts so far
  ;; ψ current prop
  ;; Γ prop stack (i.e. TO DO))
  dnf* : ((Φ (δ ...)) ...) ψ ψ* -> ((Φ (δ ...)) ...)
  ;; TT
  [(dnf* ((Φ (δ ...)) ...) TT ()) 
   ((Φ (δ ...)) ...)]
  [(dnf* ((Φ (δ ...)) ...) TT (ψ ψ_1 ...)) 
   (dnf* ((Φ (δ ...)) ...) ψ (ψ_1 ...))]
  ;; FF
  [(dnf* ((Φ (δ ...)) ...) FF (ψ ...))
   ()]
  ;; And
  [(dnf* ((Φ (δ ...)) ...) (ψ_1 ∧ ψ_2) (ψ ...))
   (dnf* ((Φ (δ ...)) ...) ψ_1 (ψ_2 ψ ...))]
  ;; Or
  [(dnf* ((Φ (δ ...)) ...) (ψ_1 ∨ ψ_2) (ψ ...))
   (app (dnf* ((Φ (δ ...)) ...) ψ_1 (ψ ...))
        (dnf* ((Φ (δ ...)) ...) ψ_2 (ψ ...)))]
  ;; Φ
  [(dnf* ((Φ (δ ...)) ...) Φ_1 ())
   (((app Φ Φ_1) (δ ...)) ...)]
  [(dnf* ((Φ (δ ...)) ...) Φ_1 (ψ ψ_1 ...))
   (dnf* (((app Φ Φ_1) (δ ...)) ...) ψ (ψ_1 ...))]
  
  ;; δ
  [(dnf* ((Φ (δ ...)) ...) (o -? τ) ())
   ((Φ (update-ψ* (empty-env) (ext (δ ...) (o -? τ)) (o -? τ))) ...)]
  [(dnf* ((Φ (δ ...)) ...) (o -? τ) (ψ ψ_1 ...))
   (dnf* ((Φ (update-ψ* (empty-env) (ext (δ ...) (o -? τ)) (o -? τ))) ...) 
         (update-ψ (empty-env) ψ (o -? τ))
         (update-ψ* (empty-env) (ψ_1 ...) (o -? τ)))])


(define-judgment-form λDTR
  #:mode (atomic-type I)
  #:contract (atomic-type τ)
  [(where #t ,(not (not (member (term τ) (term (Top #t #f Int Str))))))
   ------------------------------- "Atomic Type"
   (atomic-type τ)])

(define-judgment-form λDTR
  #:mode (implied-by-δ I O)
  #:contract (implied-by-δ δ ψ)
  [-------------------------- "Implied-Not"
   (implied-by-δ (o -! τ) (o -! τ))]
  [(atomic-type τ)
   -------------------------- "Implied-Is-Atomic"
   (implied-by-δ (o -: τ) (o -: τ))]
  [-------------------------- "Implied-Is-Union"
   (implied-by-δ (o -: (U τ ...)) (o -: (U τ ...)))]
  [-------------------------- "Implied-Is-Abs"
   (implied-by-δ (o -: (x : σ → τ (ψ_+ ψ_- oo))) (o -: (x : σ → τ (ψ_+ ψ_- oo))))]
  [(implied-by-δ ((o-car o) -: τ) ψ_τ)
   (implied-by-δ ((o-car o) -: σ) ψ_σ)
   ---------------------------- "Implied-Is-Pair"
   (implied-by-δ (o -: (τ × σ)) (And: (o -: (τ × σ))
                                     (And: ψ_τ ψ_σ)))]
  [(where/hidden ν (fresh-var (o -: (♯ τ))))
   (implied-by-δ ((id ν) -: τ) ψ_τ)
   --------------------------- "Implied-Is-Vec"
   (implied-by-δ (o -: (♯ τ)) (And: (o -: (♯ τ))
                                   (subst ψ_τ Ø ν)))]
  [(implied-by-ψ (subst ψ o x) ψ_R)
   (implied-by-δ (o -: (subst τ o x)) ψ_τ)
   -------------------------- "Implied-Is-Ref"
   (implied-by-δ (o -: (x : τ where ψ)) (And: ψ_τ ψ_R))])

(define-judgment-form λDTR
  #:mode (implied-by-ψ I O)
  #:contract (implied-by-ψ ψ ψ)
  [------------------- "Implied-True"
   (implied-by-ψ TT TT)]
  [------------------- "Implied-False"
   (implied-by-ψ FF FF)]
  [(implied-by-δ δ ψ)
   ------------------ "Implied-Atom"
   (implied-by-ψ δ ψ)]
  ;; And/Or
  [(implied-by-ψ ψ_1 ψ_1*)
   (implied-by-ψ ψ_2 ψ_2*)
   ----------------- "Implied-And"
   (implied-by-ψ (ψ_1 ∧ ψ_2) (And: ψ_1* ψ_2*))]
  [(implied-by-ψ ψ_1 ψ_1*)
   (implied-by-ψ ψ_2 ψ_2*)
   ----------------- "Implied-Or"
   (implied-by-ψ (ψ_1 ∨ ψ_2) (Or: ψ_1* ψ_2*))]
  ;; Φ
  [---------------------- "Implied SLI"
   (implied-by-ψ Φ Φ)])


(define-judgment-form λDTR
  #:mode (implied-by-ψs I O)
  #:contract (implied-by-ψs ψ* ψ*)
  [(implied-by-ψ ψ ψ_*) ...
   ----------------------- "Implied-by-ψs"
   (implied-by-ψs (ψ ...) (ψ_* ...))])

(define-metafunction λDTR
  Φ-update-δ* : δ* Φ -> δ*
  [(Φ-update-δ* ((o -? τ) ...) Φ) ((o -? (Φ-update-τ o -? τ Φ)) ...)]) ;; TODO

(define-metafunction λDTR
  Φ-update-ψ : ψ Φ -> ψ
  ;; TT/FF
  [(Φ-update-ψ TT Φ) TT]
  [(Φ-update-ψ FF Φ) FF]
  ;; fact
  [(Φ-update-ψ (o -? τ) Φ) (Φ-update-τ o -? τ Φ)]
  ;; And/Or
  [(Φ-update-ψ (ψ_1 ∧ ψ_2) Φ) (And: (Φ-update-ψ ψ_1)
                                    (Φ-update-ψ ψ_2))]
  [(Φ-update-ψ (ψ_1 ∨ ψ_2) Φ) (Or: (Φ-update-ψ ψ_1)
                                   (Φ-update-ψ ψ_2))]
  ;; Φ
  [(Φ-update-ψ Φ Φ_new) 
   Φ
   (judgment-holds (fme-sat (app Φ Φ_new)))]
  [(Φ-update-ψ Φ Φ_new) 
   FF
   (where #f (fme-sat (app Φ Φ_new)))])

(define-metafunction λDTR
  Φ-update-τ : o -? τ Φ -> τ
  [(Φ-update-τ o -! τ Φ) τ]
  [(Φ-update-τ o -: Top Φ) Top]
  [(Φ-update-τ o -: #t Φ) #t]
  [(Φ-update-τ o -: #f Φ) #f]
  [(Φ-update-τ o -: Int Φ) Int]
  [(Φ-update-τ o -: Str Φ) Str]
  [(Φ-update-τ o -: (U τ ...) Φ) (U  (Φ-update-τ o -: τ Φ) ...)]
  [(Φ-update-τ o -: (x : σ → τ (ψ_+ ψ_- oo)) Φ) (x : σ → τ (ψ_+ ψ_- oo))]
  [(Φ-update-τ o -: (τ × σ) Φ) ((Φ-update-τ (o-car o) -: τ Φ) × (Φ-update-τ (o-cdr o) -: σ Φ))]
  [(Φ-update-τ o -: (♯ τ) Φ) (♯ (Φ-update-τ (id ν) -: τ Φ))
                            (where/hidden ν (fresh-var o τ Φ))]
  [(Φ-update-τ o -: (x : τ where ψ_x) Φ) (ν : (Φ-update-τ o -: (subst τ (id ν) x) Φ)
                                            where ψ_new)
   (where ψ_new (dnf (Φ-update-ψ (subst ψ_x (id ν) x) Φ)))
   (judgment-holds (<> ψ_new FF))
   (where/hidden ν (fresh-var o x τ Φ_x Φ))]
  [(Φ-update-τ o -: (x : τ where ψ_x) Φ) (U)
   (where FF (dnf (Φ-update-ψ (subst ψ_x (id ν) x) Φ)))
   (where/hidden ν (fresh-var o x τ Φ_x Φ))])



(define-metafunction λDTR
  true-ψ : τ -> ψ
  [(true-ψ τ) TT
   (where #f (simple-subtype #f τ))]
  [(true-ψ τ) FF
   (judgment-holds (simple-subtype #f τ))])

(define-metafunction λDTR
  false-ψ : τ -> ψ
  [(false-ψ τ) FF
   (where #f (simple-subtype #f τ))]
  [(false-ψ τ) TT
   (judgment-holds (simple-subtype #f τ))])


;; substitute oo_new for x in the first argument
;; USE THIS ONE! this will do dnf simplification
;; when nullifying in props, which is a *must*
(define-metafunction λDTR
  subst : any oo x -> any
  [(subst (ψ_+ ψ_- oo) oo_new x) ((subst ψ_+ oo_new x) 
                                  (subst ψ_- oo_new x) 
                                  (subst oo oo_new x))]
  [(subst oo oo_new x) (subst-oo oo       oo_new x)]
  [(subst ψ  Ø  x)     (subst-ψ  (dnf ψ)  Ø x)]
  [(subst ψ  o_new  x) (subst-ψ  ψ        o_new x)]
  [(subst τ  oo_new x) (subst-τ  τ        oo_new x)])


;; substitution in oo
;; will null out completely invalid combinations 
;; (e.g. creating a linear expression w/ a non-empty path)
(define-metafunction λDTR
  subst-oo : oo oo x -> oo
  ;; null -> null
  [(subst-oo Ø oo_new x) Ø]
  ;; matched obj w/ empty path
  [(subst-oo (() @ x) oo_new x) oo_new]
  ;; null into obj
  [(subst-oo (π @ x) Ø x) Ø]
  [(subst-oo (π @ x) oo y) (π @ x)
   (judgment-holds (<> x y))]
  ;; obj into obj, path join
  [(subst-oo ([pe_0 pe_1 ...] @ x) (π_y @ y) x) ((app [pe_0 pe_1 ...] π_y) @ y)]
  ;; invalid obj/linear combinations, resulting in Ø
  [(subst-oo ([pe_0 pe_1 ...] @ x) i x) Ø]
  [(subst-oo ([pe_0 pe_1 ...] @ x) (* i o) x) Ø]
  [(subst-oo ((pe_0 pe_1 ...) @ x) (+ o_l o_r) x) Ø]
  ;; possibly valid linear combinations
  [(subst-oo i oo x) i]
  [(subst-oo (+ o_l o_r) oo x) (+: (subst-oo o_l oo x)
                                   (subst-oo o_r oo x))]
  [(subst-oo (* i o) oo x) (*: i
                               (subst-oo o oo x))])

(define-metafunction λDTR
  subst-ψ : ψ oo x -> ψ
  ;; TT/FF
  [(subst-ψ TT oo x) TT]
  [(subst-ψ FF oo x) FF]
  ;; fact
  [(subst-ψ (o -? τ) oo x) TT
   (where Ø (subst-oo o oo x))]
  [(subst-ψ (o_1 -? τ) oo x) (o_2 -? (subst-τ τ oo x))
   (where o_2 (subst-oo o_1 oo x))]
  ;; And/Or
  [(subst-ψ (ψ_1 ∧ ψ_2) oo x) (And: (subst-ψ ψ_1 oo x)
                                    (subst-ψ ψ_2 oo x))]
  [(subst-ψ (ψ_1 ∨ ψ_2) oo x) (Or: (subst-ψ ψ_1 oo x)
                                   (subst-ψ ψ_2 oo x))]
  
  ;; Φ
  [(subst-ψ Φ Ø x) (fme-elim Φ x)]
  [(subst-ψ Φ o x) (subst-Φ Φ o x)])

(define-metafunction λDTR
  subst-Φ : Φ o x -> ψ
  [(subst-Φ [] o x) []]
  [(subst-Φ [(≤ o_1l o_1r) (≤ o_2l o_2r) ...] o x) FF
   (where FF (subst-Φ [(≤ o_2l o_2r) ...] o x))]
  [(subst-Φ [(≤ o_1l o_1r) (≤ o_2l o_2r) ...] o x) FF
    (where [] (≤: (subst-oo o_1l o x)
                  (subst-oo o_1r o x)))]
  [(subst-Φ [(≤ o_1l o_1r) (≤ o_2l o_2r) ...] o x) (app [(≤ o_l o_r)] Φ_rest)
   (where Φ_rest (subst-Φ [(≤ o_2l o_2r) ...] o x))
   (where [(≤ o_l o_r)] (≤: (subst-oo o_1l o x)
                            (subst-oo o_1r o x)))])

;; standard captura avoiding substitution
;; with smart constructors
(define-metafunction λDTR
  subst-τ : τ oo x -> τ
  [(subst-τ Top oo x) Top]
  [(subst-τ Int oo x) Int]
  [(subst-τ Str oo x) Str]
  [(subst-τ #t oo x) #t]
  [(subst-τ #f oo x) #f]
  [(subst-τ (U τ ...) oo x) (U: (subst-τ τ oo x) ...)]
  [(subst-τ (τ × σ) oo x)
   (Pair: (subst-τ τ oo x) (subst-τ σ oo x))]
  [(subst-τ (♯ τ) oo x)
   (Vec: (subst-τ τ oo x))]
  [(subst-τ (x : σ → τ (ψ_+ ψ_- oo_f)) oo x) 
   (x : (subst-τ σ oo x) → τ (ψ_+ ψ_- oo_f))]
  [(subst-τ (y : σ → τ (ψ_+ ψ_- oo_f)) oo x)
   (ν : (subst-τ (subst-τ σ (id ν) y) oo x)
      →
      (subst (subst-τ τ (id ν) y) oo x)
      ((subst (subst-ψ ψ_+ (id ν) y) oo x)
       (subst (subst-ψ ψ_- (id ν) y) oo x)
       (subst-oo (subst-oo oo_f (id ν) y) oo x)))
   (judgment-holds (<> x y))
   (where/hidden ν (fresh-var (y : σ → τ (ψ_+ ψ_- oo_f)) oo x))]
  [(subst-τ (x : τ where ψ) oo x) (x : τ where ψ)]
  [(subst-τ (y : τ where ψ) oo x)
   (ν : (subst-τ (subst-τ τ (id ν) y) oo x) 
      where (subst (subst ψ (id ν) y) oo x))
   (judgment-holds (<> x y))
   (where/hidden ν (fresh-var (y : τ where ψ) oo x))])


(define-metafunction λDTR
  env/implied-by-ψ* : Γ ψ ... -> Γ
  [(env/implied-by-ψ* (env Φ δ* ψ*) ψ ...) (env Φ δ* (app ψ* ψ*_2))
                                           (judgment-holds (implied-by-ψs (ψ ...) ψ*_2))])

(define-metafunction λDTR
  env: : ψ ... -> Γ
  [(env: ψ ...) (env () () ψ*_2)
                (judgment-holds (implied-by-ψs (ψ ...) ψ*_2))])
