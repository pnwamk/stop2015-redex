#lang racket

(require redex "dtr-lang.rkt" "dtr-logic.rkt" "dtr-tc.rkt" rackunit)

(define-judgment-form λDTR
  #:mode (typeof* I I I I)
  #:contract (typeof* Γ e τ (ψ ψ oo))
  [(where o (id ,(gensym)))
   (typeof Γ e_1 τ_2 (ψ_2+ ψ_2- oo_2))
   (subtype Γ o τ_2 τ_1)
   (proves (env/implied-by-ψ* Γ ψ_2+) ψ_1+)
   (proves (env/implied-by-ψ* Γ ψ_2-) ψ_1-)
   (subobj oo_2 oo_1)
   -------------- "T-Subsume"
   (typeof* Γ e_1 τ_1 (ψ_1+ ψ_1- oo_1))])

(define-metafunction λDTR
  and : e e -> e
  [(and e_1 e_2) (if e_1 e_2 #f)])

(define-metafunction λDTR
  or : e e -> e
  [(or e_1 e_2) (let (tmp e_1) 
                  (if (ann tmp (U #t #f))
                      (ann tmp (U #t #f))
                      e_2))])

(define-metafunction λDTR
  Option : τ -> τ
  [(Option τ) (U τ #f)])

;; T-Int
(check-true 
 (judgment-holds 
  (typeof* (empty-env) 
           42 
           Int 
           (TT FF Ø))))

;; T-Str
(check-true 
 (judgment-holds 
  (typeof* (empty-env) 
           "Hello World"
           Str 
           (TT FF Ø))))

;; T-True
(check-true 
 (judgment-holds 
  (typeof* (empty-env) 
           #t
           #t 
           (TT FF Ø))))

;; T-False
(check-true 
 (judgment-holds 
  (typeof* (empty-env) 
           #f
           #f
           (FF TT Ø))))

;; T-Var
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Int))
           (ann x Int)
           Int
           (TT FF Ø))))


;; T-Abs
(check-true 
 (judgment-holds 
  (typeof* (empty-env)
           (λ (x : Int) (ann x Int))
           (x : Int → Int (TT FF (id x)))
           (TT FF Ø))))

;; T-App
(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (add1 41)
           Int
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (add1 41)
           (Int= 42)
           (TT FF 42))))

;; T-App w/ τ-update
(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (neg 41)
           Int
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (env: (is x Int))
           (neg (ann x Int))
           Int
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (env: (is x Int))
           (neg (zero? (ann x Int)))
           (U #t #f)
           (TT FF Ø))))

;; T-If
(check-true
 (judgment-holds 
  (typeof* (env: (is x (U #t #f)))
           (if (ann x (U #t #f))
               (add1 41)
               42)
           (Int= 42)
           (TT TT 42))))

(check-true
 (judgment-holds 
  (typeof* (env: (is x (U #t #f)))
           (if (ann x (U #t #f))
               42
               "Hello World")
           (U Int Str)
           (TT FF Ø))))

;; T-Let
(check-true
 (judgment-holds 
  (typeof* (env: (is x (U #t #f)))
           (let (y (ann x (U #t #f)))
            (if (ann y (U #t #f))
               42
               "Hello World"))
           (U Int Str)
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (env: (is x Top))
           (let (y (ann x Top))
             (ann y Top))
           Top
           ((! x #f) (is x #f) (id x)))))

(check-true
 (judgment-holds 
  (typeof* (env: (is x Top))
           (let (y (int? (ann x Top)))
             (ann y (U #t #f)))
           (U #t #f)
           ((is x Int) (! x Int) Ø))))

;; T-Cons
(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (cons 42 "Hello World")
           (Int × Str)
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (cons (cons 40 2) (cons "Hello" "World"))
           ((Int × Int) × (Str × Str))
           (TT FF Ø))))

;; T-Car
(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (car (cons 42 "Hello World"))
           Int
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (env: (is p (Int × Str)))
           (car (ann p (Int × Str)))
           Int
           (TT FF ((CAR) @ p)))))

;; T-Cdr
(check-true
 (judgment-holds 
  (typeof* (empty-env)
           (cdr (cons 42 "Hello World"))
           Str
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* (env: (is p (Int × Str)))
           (cdr (ann p (Int × Str)))
           Str
           (TT FF ((CDR) @ p)))))

;; T-Vec
(check-true
 (judgment-holds
  (typeof* (empty-env)
           (vec 42)
           (♯ Int)
           (TT FF Ø))))

(check-true
 (judgment-holds
  (typeof* (empty-env)
           (vec 42 "Hello World")
           (♯ (U Int Str))
           (TT FF Ø))))

(check-true
 (judgment-holds
  (typeof* (empty-env)
           (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!")
           (♯ (U Int Str))
           (TT FF Ø))))

;; T-VecRef
;; i.e. tests that require reasoning about linear combinations
;; *and* vector bounds
(check-true
 (judgment-holds
  (typeof* (empty-env)
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") 0)
           (U Int Str)
           (TT TT Ø))))

(check-true
 (judgment-holds
  (typeof* (empty-env)
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") ((* 2) 2))
           (U Int Str)
           (TT TT Ø))))

(check-false
 (judgment-holds
  (typeof* (empty-env)
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") ((+ 0) -1))
           (U Int Str)
           (TT TT Ø))))

(check-true
 (judgment-holds
  (typeof* (empty-env)
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") 7)
           (U Int Str)
           (TT TT Ø))))

(check-false
 (judgment-holds
  (typeof* (empty-env)
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") ((* 2) 4))
           (U Int Str)
           (TT TT Ø))))


(check-true 
 (judgment-holds 
  (typeof* (env: (is x Int) (is v (♯ Str)))
           (if (and ((<= 0) (ann x Int))
                    ((<= (ann x Int)) ((+ -1) (vec-len (ann v (♯ Str))))))
               (vec-ref (ann v (♯ Str)) (ann x (IntRange 0 (+ -1 (o-len (id v))))))
               (error "bad index!"))
           Str
           (TT FF Ø))))

;;; Original tests+

;;; Example 1
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (if (int? (ann x Top))
               (add1 (ann x Int))
               0) 
           Int 
           (TT FF Ø))))

(check-true 
 (judgment-holds 
  (typeof* (empty-env)
           (λ (x : Int)
             (add1 (ann x Int)))
           (x : Int → Int (TT FF Ø))
           (TT FF Ø))))

(check-true 
 (judgment-holds 
  (typeof* (env: (is x (U Str Int)))
           (if (int? (ann x Top))
               (add1 (ann x Int))
               (str-len (ann x Str)))
           Int
           (TT FF Ø))))

(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (int? (ann x Top))
           (U #t #f)
           ((is x Int) (! x Int) Ø))))

(check-true 
 (judgment-holds 
  (typeof* (empty-env)
           (λ (x : Top)
             (int? (ann x Top)))
           (x : Top → (U #t #f) ((is x Int) (! x Int) Ø))
           (TT FF Ø))))


;;; Example 2
(check-true 
 (judgment-holds 
  (typeof* (empty-env)
           (λ (x : (U Str Int))
             (if (int? (ann x Top))
                 (add1 (ann x Int))
                 (str-len (ann x Str))))
           (x : (U Str Int) → Int (TT FF Ø))
           (TT FF Ø))))

(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (if (int? (ann x Top))
               #t
               (str? (ann x Top)))
           (U #t #f)
           ((is x (U Int Str)) (! x (U Int Str)) Ø))))

;;; Example 3
(check-true 
 (judgment-holds 
  (typeof* (env: (is x (Option Str)))
           (if (ann x Top)
               (str-len (ann x Str))
               (error "string not found!"))
           Int
           (TT FF Ø))))


(check-true
 (judgment-holds 
  (typeof* (env: (is x Top))
           (let (tmp (int? (ann x Top))) 
             (ann tmp (U #t #f)))
           (U #t #f)
           ((is x Int) (! x Int) Ø))))

(check-true
 (judgment-holds 
  (typeof* (env: (is x Top))
           (let (tmp (int? (ann x Top))) 
             (if (ann tmp (U #t #f))
                 (ann tmp (U #t #f))
                 (str? (ann x Top))))
           (U #t #f)
           ((is x (U Int Str)) (! x (U Int Str)) Ø))))

(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (or (int? (ann x Top))
               (str? (ann x Top)))
           (U #t #f)
           ((is x (U Int Str)) (! x (U Int Str)) Ø))))

;;; Example 4
(check-true (judgment-holds 
             (typeof* (env: (is f (x : (U Int Str) → Int (TT FF Ø)))
                            (is x Top))
                      (if (or (int? (ann x Top))
                              (str? (ann x Top)))
                          ((ann f (x : (U Int Str) → Int (TT FF Ø)))
                           (ann x (U Int Str)))
                          0)
                      Int
                      (TT FF Ø))))


;;; Example 5
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top) (is y Top))
           (if (and (int? (ann x Top)) (str? (ann y Top)))
               ((+ (ann x Int)) (str-len (ann y Str)))
               0)
           Int
           (TT FF Ø))))

;;; Example 6
(check-false 
 (judgment-holds 
  (typeof* (env: (is x Top) (is y Top))
           (if (and (int? (ann x Top)) (str? (ann y Top)))
               ((+ (ann x Int)) (str-len (ann y Str)))
               (str-len (ann y Str)))
           Int
           (TT FF Ø))))

;;; Example 7
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top) (is y Top))
           (if (if (int? (ann x Top)) (str? (ann y Top)) #f)
               ((+ (ann x Int)) (str-len (ann y Str)))
               0)
           Int
           (TT FF Ø))))

;;; Example 8
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (let (tmp (str? (ann x Top)))
             (if (ann tmp Top)
                 (ann tmp Top)
                 (int? (ann x Top))))
           Top
           ((is x (U Str Int)) (! x (U Str Int)) Ø))))

;;; Example 9
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (if (let (tmp (int? (ann x Top)))
                 (if (ann tmp Top)
                     (ann tmp Top)
                     (str? (ann x Top))))
               ((λ (x : (U Str Int))
                  (if (int? (ann x Top))
                      (add1 (ann x Int))
                      (str-len (ann x Str))))
                (ann x (U Int Str)))
               0)
           Int
           (TT FF Ø))))


;;; Example 10
(check-true 
 (judgment-holds 
  (typeof* (env: (is p (Top × Top)))
           (if (int? (car (ann p (Top × Top))))
               (add1 (car (ann p (Int × Top))))
               7)
           Int
           (TT FF Ø))))

;;; Example 11
(check-true 
 (judgment-holds 
  (typeof* (env: (is p (Top × Top))
                 (is g (x : (Int × Int) → Int (TT FF Ø))))
           (if (and (int? (car (ann p (Top × Top))))
                    (int? (cdr (ann p (Top × Top)))))
               ((ann g (x : (Int × Int) → Int (TT FF Ø)))
                (ann p (Int × Int)))
               42)
           Int
           (TT FF Ø))))

;;; Example 12
(check-true 
 (judgment-holds 
  (typeof* (empty-env)
           (λ (p : (Top × Top))
             (int? (car (ann p (Top × Top)))))
           (x : (Top × Top) →
             (U #t #f)
             ((((CAR) @ x) -: Int)
              (((CAR) @ x) -! Int)
              Ø))
           (TT FF Ø))))

(check-true 
 (judgment-holds 
  (typeof* (empty-env)
           (λ (p : (Top × Top))
             (int? (cdr (ann p (Top × Top)))))
           (x : (Top × Top) →
             (U #t #f)
             ((((CDR) @ x) -: Int)
              (((CDR) @ x) -! Int)
              Ø))
           (TT FF Ø))))

;;; Example 13
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top) (is y (U Int Str)))
           (if (and (int? (ann x Top)) (str? (ann y Top)))
               ((+ (ann x Int)) (str-len (ann y Str)))
               (if (int? (ann x Top))
                   ((+ (ann x Int)) (ann y Int))
                   0))
           Int
           (TT FF Ø))))

;;; Example 14
(check-true 
 (judgment-holds 
  (typeof* (env: (is x Top))
           (λ (y : (U Int Str))
             (if (and (int? (ann x Top)) (str? (ann y Top)))
                 ((+ (ann x Int)) (str-len (ann y Str)))
                 (if (int? (ann x Top))
                     ((+ (ann x Int)) (ann y Int))
                     0)))
           (x : (U Str Int) → Int (TT FF Ø))
           (TT FF Ø))))

