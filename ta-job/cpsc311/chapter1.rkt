#lang plait

(define-type Value
  [numV (n : Number)]
  [boolV (b : Boolean)]
    )

(define-type Exp
  [litE (l : Value)]
  [plusE (left : Exp) (right : Exp)]
  [condE (c : Exp) (t : Exp) (f : Exp)]
    )

(val->num : (Value -> Number))
(define (val->num v)
  (type-case Value v
    [(numV n) n]
    [else (error 'add "expected a num")]
    ))

(val->bool : (Value -> Boolean))
(define (val->bool v)
  (type-case Value v
    [(boolV n) n]
    [else (error 'add "expected a bool")]
    ))

(add : (Value Value -> Value))
(define (add l r)
  (numV (+ (val->num l) (val->num r))))

(eval : (Exp -> Value))
(define (eval e)
  (type-case Exp e
    [(litE n) n]
    [(plusE l r) (add (eval l) (eval r))]
    [(condE c t f) (if (val->bool (eval c)) (eval t) (eval f))]
    ))

(parse : (S-Exp -> Exp))
(define (parse s)
  (cond
    [(s-exp-number?  s) (litE (numV  (s-exp->number  s)))]
    [(s-exp-boolean? s) (litE (boolV (s-exp->boolean s)))]
    [(s-exp-list? s)
      (let
        ([l (s-exp->list s)])
        (case (s-exp->symbol (first l))
          ['+  (plusE (parse (second l)) (parse (third l)))]
          ['if (condE (parse (second l)) (parse (third l)) (parse (fourth l)))]
          [else (error 'parse "not an addition")]
          )
      )]
    ))

(parse `{if #t 5 6})

