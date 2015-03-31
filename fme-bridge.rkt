#lang racket

;; functions responsible for converting redex model representations
;; into data the 'fme' library can parse, and for taking 'fme' library
;; output and converting it back into redex model representations


(require fme racket/contract racket/set)
(provide (all-defined-out))

(define int? exact-integer?)

(define (fme-elim-var Φ x)
  (fme-elim* Φ (λ (var)
                 (match var
                   [(list π '@ (? (curry equal? x))) #t]
                   [_ #f]))))

(define (redex-fme-sat? e)
  (fme-sat? (redex->fme e)))

(define (redex-sli-equal? sli1 sli2)
  (equal? (redex->fme sli1) (redex->fme sli2)))

(define (redex-fme-imp? e1 e2)
  (fme-imp? (redex->fme e1)
            (redex->fme e2)))

(define/contract (redex->fme e)
  (-> any/c (set/c leq?))
  (let parse ([e e])
    (match e
      [(list) (set)]
      [(cons (list '≤ lhs rhs) rest) 
       (set-add (parse rest) (leq (parse lhs)
                                  (parse rhs)))]
      [(? int? i) (lexp i)]
      [(list π '@ x) (lexp `(1 (,π @ ,x)))]
      [(list '* (? int? i) o) (lexp-scale (parse o) i)]
      [(list '+ o1 o2) (lexp-plus (parse o1) (parse o2))]
      [else (error 'redex->fme-lexp "bad fme-exp!!! ~a" e)])))

(define/contract (lexp->redex l)
  (-> lexp? (or/c list? int?))
  (define vars-exp (match (lexp-vars l)
                     ['() #f]
                     [(cons x xs) 
                      (for/fold ([rexp `(* ,(lexp-coeff l x) ,x)])
                                ([x* xs])
                        `(+ (* ,(lexp-coeff l x*) ,x*)
                            ,rexp))]))
  (define c (lexp-const l))
  (cond
    [(not vars-exp) c]
    [(zero? c) vars-exp]
    [else `(+ ,c ,vars-exp)]))

(define/contract (leq->redex e)
  (-> leq? list?)
  (define-values (l r) (leq-lexps e))
  `(≤ ,(lexp->redex l) ,(lexp->redex r)))

(define/contract (sli->redex sli)
  (-> sli? list?)
  (for/list ([ineq (in-set sli)])
      (leq->redex ineq)))


