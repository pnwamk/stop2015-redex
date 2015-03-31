#lang racket

(require redex "dtr-lang.rkt" "dtr-logic.rkt" "dtr-fme.rkt" rackunit)

;; oo substs tests
(check-equal? (term (subst (id x) Ø x)) (term Ø))
(check-equal? (term (subst (id y) Ø x)) (term (id y)))
(check-equal? (term (subst Ø (id y) x)) (term Ø))
(check-equal? (term (subst ((CAR) @ y) (id z) y)) (term ((CAR) @ z)))
(check-equal? (term (subst ((CDR) @ y) (id z) y)) (term ((CDR) @ z)))
(check-equal? (term (subst ((LEN) @ y) (id z) y)) (term ((LEN) @ z)))
(check-equal? (term (subst ((CAR) @ y) ((CDR) @ z) y)) (term ((CAR CDR) @ z)))
(check-equal? (term (subst ((CDR) @ y) ((CAR) @ z) y)) (term ((CDR CAR) @ z)))
(check-equal? (term (subst ((LEN) @ y) ((CAR) @ z) y)) (term ((LEN CAR) @ z)))

;; type subst tests
(check-equal? (term (subst Top (id z) x)) (term Top))
(check-equal? (term (subst Top Ø x)) (term Top))
(check-equal? (term (subst Int (id z) x)) (term Int))
(check-equal? (term (subst Str (id z) x)) (term Str))
(check-equal? (term (subst #t (id z) x)) #t)
(check-equal? (term (subst #f (id z) x)) #f)
(check-equal? (term (subst (U Int Str) (id z) x)) (term (U Int Str)))
(check-equal? (term (subst (x : Top → (U #t #f) (((id x) -: Int) ((id x) -! Int) Ø)) 
                           (id z) 
                           x)) 
              (term (x : Top → (U #t #f) (((id x) -: Int) ((id x) -! Int) Ø))))
(check-true (match (term (subst (y : Top → (U #t #f) (((id x) -: Int) ((id x) -! Int) Ø)) 
                                (id z) 
                                x))
              [`(,y : Top → (U #t #f) (((() @ z) -: Int) ((() @ z) -! Int) Ø)) #t]
              [_ #f]))
(check-true (match (term (subst (y : Int → Int (TT FF (id x)))
                                (id z) 
                                x))
              [`(,y : Int → Int (TT FF (() @ z))) #t]
              [_ #f]))
(check-equal? (term (subst ((U Int Str) × (U Int Str)) (id z) x)) 
              (term ((U Int Str) × (U Int Str))))
(check-equal? (term (subst (♯ (U Int Str)) (id z) x)) 
              (term (♯ (U Int Str))))


(check-equal? (term (subst ((id x) -: Int) (id x) x)) 
              (term ((id x) -: Int)))
(check-equal? (term (subst ((id x) -: Int) (id y) x)) 
              (term ((id y) -: Int)))
(check-equal? (term (subst ((id x) -: Int) Ø y)) 
              (term ((id x) -: Int)))
(check-equal? (term (subst ((id x) -: Int) Ø x)) 
              (term TT))
(check-equal? (term (subst ((+ 42 (* 13 (id x))) -: Int) Ø x)) 
              (term TT))
(check-equal? (term (subst (((+ 42 (* 13 (id x))) -: Int) ∧ ((+ 42 (* 13 (id x))) -: Int)) Ø x)) 
              (term TT))
(check-equal? (term (subst ((+ 42 (* 13 (id x))) -: Int) (+ (id z) (id q)) x))
              (term ((+ 42 (* 13 (+ (id z) (id q)))) -: Int)))
(check-equal? (term (subst (((+ 42 (* 13 (id x))) -: Int) ∨ ((+ 42 (* 13 (id x))) -: Int)) 
                           (+ (id z) (id q)) x))
              (term (((+ 42 (* 13 (+ (id z) (id q)))) -: Int) 
                     ∨ ((+ 42 (* 13 (+ (id z) (id q)))) -: Int))))

;; fme tests
(check-true (judgment-holds (fme-sat [])))
(check-true (judgment-holds (fme-sat [(≤ (id x) (id y))])))
(check-true (judgment-holds (fme-sat [(≤ (id x) (id y))
                                      (≤ (+ 1 (id y)) (id z))])))
(check-false (judgment-holds (fme-sat [(≤ (id x) (id y))
                                       (≤ (+ 1 (id y)) (id z))
                                       (≤ (id z) (id x))])))
(check-true (judgment-holds (fme-imp ((≤ (id x) 3)) 
                                     ((≤ (id x) 5)))))
(check-equal? (term (subst ((≤ (id x) (id z))
                            (≤ (id z) (o-car (id z)))
                            (≤ (o-car (id z)) (id y)))
                           Ø
                           z))
              (term ((≤ (* 1 (() @ x)) 
                        (* 1 (() @ y))))))


;; simple-subtype tests
(check-true (judgment-holds (simple-subtype Int Int)))
(check-true (judgment-holds (simple-subtype Int Top)))
(check-true (judgment-holds (simple-subtype (U) Int)))
(check-true (judgment-holds (simple-subtype Int (U Int #f))))
(check-true (judgment-holds (simple-subtype (U #t #f) (U Int #t #f))))
(check-true (judgment-holds (simple-subtype Int Int)))
(check-false (judgment-holds (simple-subtype (U Int #t) Int)))
(check-true (judgment-holds (simple-subtype (U Int Int) Int)))
(check-true (judgment-holds (simple-subtype (U Int Int) (U Int #t))))
(check-true (judgment-holds 
             (simple-subtype (x : Top → (U #t #f) (((id x) -: Int) ((id x) -! Int) Ø)) 
                      (x : Top → (U #t #f) (((id x) -: Int) ((id x) -! Int) Ø)))))
(check-true (judgment-holds 
             (simple-subtype (x : Top → (U #t #f) (((id x) -: Int) ((id x) -! Int) Ø)) 
                      (y : Top → (U #t #f) (((id y) -: Int) ((id y) -! Int) Ø)))))
(check-true (judgment-holds 
             (simple-subtype (x : Top → Int (TT TT Ø))
                      (y : Int → (U Int #t #f) (TT TT Ø)))))

;; subtype tests w/ refinements
(check-true (judgment-holds (simple-subtype (x : Int where [(≤ (id x) 5)]) Int)))
(check-true (judgment-holds (simple-subtype (y : Int where [(≤ (id y) 3)]) 
                                     (x : Int where [(≤ (id x) 5)]))))
(check-false (judgment-holds (simple-subtype (y : Int where [(≤ (id y) 13)]) 
                                      (x : Int where [(≤ (id x) 5)]))))
(check-true (judgment-holds (simple-subtype (x : (U Int Str) 
                                               → (y : Top where (Or: (And: ((id x) -: Int) ((id y) -: Int))
                                                                     (And: ((id x) -: Str) ((id y) -: Str))))
                                                 (TT FF Ø))
                                            (x : Int → Int (TT FF Ø)))))



;; update* fact tests
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: Int)]
                             ((id x) -: Str))) 
              (term (((id x) -: (U)))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: Str)]
                             ((id x) -! Str)))
              (term (((id x) -: (U)))))
(check-equal? (term (update-ψ* (empty-env) 
                             [((id x) -: (U Int Str))]
                             ((id x) -! Str))) 
              (term (((id x) -: Int))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (U Int Str))]
                             ((id x) -: (U #t Str)))) 
              (term (((id x) -: Str))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (Top × Top))]
                             (((CAR) @ x) -: Int))) 
              (term (((id x) -: (Int × Top)))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (Top × Top))]
                             (((CDR) @ x) -: Int))) 
              (term (((id x) -: (Top × Int)))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (Int × Top))]
                             (((CAR) @ x) -: Str))) 
              (term (((id x) -: (U)))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: Int)]
                             (((CAR) @ x) -: Str))) 
              (term (((id x) -: (U)))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (♯ (U Int Str)))]
                             ((id x) -: (♯ Str))))
              (term (((id x) -: (♯ Str)))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (♯ (U Int Str)))]
                             ((id x) -! (♯ Str))))
              (term (((id x) -: (♯ Int)))))
(check-not-false 
 (redex-match λDTR
              (((() @ x) -: (y : Int where ((≤ (() @ y) (() @ y))))))
              (term (update-ψ* (empty-env) 
                             [((id x) -: (z : (U Int Str) where [(≤ (id z) (id z))]))]
                             ((id x) -: Int)))))
(check-not-false 
 (redex-match λDTR
              (((() @ x) -: (z : Int where ((≤ (() @ z) (() @ z))))))
              (term (update-ψ* (empty-env)
                             [((id x) -: (z : (U Int Str) where [(≤ (id z) (id z))]))]
                             ((id x) -! Str)))))
(check-not-false (term (redex-match λDTR 
                                    (((id x) -: (z : Int where [(≤ (id z) (id z))
                                                                (≤ (id z) (+ 1 (id z)))])))
                                    (term (update-ψ* (empty-env) [((id x) -: (z : (U Int Str) where [(≤ (id z) (id z))]))]
                                                   ((id x) -: (q : Int where [(≤ (id q) (+ 1 (id q)))])))))))
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: (z : (U Int Str) where (Φ< (id z) (id x))))]
                             ((id x) -: (q : Int where (Φ< (id x) (id q))))))
              (term (((id x) -: (U)))))

;; update* (empty-env) other tests
(check-equal? (term (update-ψ* (empty-env)
                             [((id x) -: Int)
                              ((id x) -: Int)]
                             ((id x) -: Str))) 
              (term (((id x) -: (U)) 
                     ((id x) -: (U)))))
(check-equal? (term (update-ψ* (empty-env)
                             [(TT ∧ ((id x) -: Int))]
                             ((id x) -: Str))) 
              (term (((id x) -: (U)))))
(check-equal? (term (update-ψ* (empty-env) 
                             [(((id x) -: Int) ∨ FF)]
                             ((id x) -: Str)))
              (term (((id x) -: (U)))))

;;logic tests
(check-false (judgment-holds (proves (empty-env) FF)))
(check-true (judgment-holds (proves (env: ((id x) -: Int))
                                    ((id x) -: Int))))
(check-true (judgment-holds (proves (env: ((id x) -: Int))
                                    ((id x) -! Str))))
(check-true (judgment-holds (proves (env: (((id x) -: Int) 
                                           ∧ ((id y) -: #f))) 
                                    (((id y) -: #f) 
                                     ∧ ((id x) -: Int)))))
(check-true (judgment-holds (proves (env: ((id x) -: Int)) 
                                    (((id x) -: Int) 
                                     ∨ ((id x) -: (U #t #f))))))
(check-true (judgment-holds (proves (env: ((id x) -: Int)
                                          ((id x) -! Int)) 
                                    FF)))
(check-true (judgment-holds (proves (env: ((id x) -: Int) 
                                          ((id x) -: Str)) 
                                    FF)))
(check-true (judgment-holds (proves (env: ((id x) -: (U #t #f Int)) 
                                          (((id x) -! #t) 
                                           ∧ ((id x) -: (U #t Int))))
                                    ((id x) -: Int))))
(check-true (judgment-holds (proves (env: ((((id z) -: (U)) ∨ FF)
                                           ∨ ((id x) -: Int))
                                          (((id x) -! Int) 
                                           ∨ ((id y) -: (U #t #f)))
                                          (((id y) -: Int) 
                                           ∨ ((id z) -: (U #t #f)))) 
                                    ((id z) -: (U #t #f)))))

(check-true (judgment-holds (proves (env: [(≤ (id x) 3)]) [(≤ (id x) 5)])))

(check-true (judgment-holds (subtype (empty-env) 
                                         (id ,(gensym))
                                         (U (x : Int where ((≤ (() @ x) (+ 1 (() @ x))) (≤ (+ 1 (() @ x)) (() @ x))))
                                            (y : Int where ((≤ (() @ y) 0) (≤ 0 (() @ y)))))
                                         Int)))

(check-true (judgment-holds (subtype (empty-env) 
                                         (id ,(gensym))
                                         (U (x : (z : Int where ((≤ (() @ x) (+ 1 (() @ z))))) 
                                               where ((≤ (+ 1 (() @ x)) (() @ x))))
                                            (y : Int where ((≤ (() @ y) 0) (≤ 0 (() @ y)))))
                                         Int)))

(check-true (judgment-holds (subtype (empty-env) 
                                         (id ,(gensym))
                                         (U (x : Int where ((≤ (() @ x) (+ 1 (() @ x))) (≤ (+ 1 (() @ x)) (() @ x))))
                                            (y : (z : Int where ((≤ (() @ z) 0))) 
                                               where ((≤ 0 (() @ y)))))
                                         Int)))

;; arbitrary refinement subtyping =O
(check-true (judgment-holds (subtype (env: (is y Top)) 
                                         (id x)
                                         (z : (U Int Str) where (Or: (And: (is x Int) (is y Int))
                                                                     (And: (is x Str) (is y Str))))
                                         (U Int Str))))

(check-true (judgment-holds (subtype (env: (is y Int)) 
                                         (id x)
                                         (z : (U Int Str) where (Or: (And: (is x Int) (is y Int))
                                                                     (And: (is x Str) (is y Str))))
                                         Int)))

(check-true (judgment-holds (simple-subtype (fresh142766
                                      :
                                      (U Int #t #f)
                                      where
                                      (((41 -: (fresh142768 : Int where ((≤ (() @ fresh142768) 41) (≤ 41 (() @ fresh142768))))) ∧ ((() @ fresh142766) -: Int))
                                       ∨
                                       ((41 -: (U)) ∧ ((() @ fresh142766) -: (U #t #f)))))
                                     Int)))
