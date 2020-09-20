#lang plai

;; ==============DEFINE-TYPE================
;; BFAE
;; variants: num, add, sub, id, fun, app
;;           newbox, setbox, openbox, seqn
;;           rec, getrec, setrec
(define-type BFAE
  [num     (n number?)]
  [add     (lhs BFAE?) (rhs BFAE?)]
  [sub     (lhs BFAE?) (rhs BFAE?)]
  [id      (name symbol?)]
  [fun     (param symbol?) (body BFAE?)]
  [app     (ftn BFAE?) (arg BFAE?)]
  [newbox  (val BFAE?)]
  [setbox  (box BFAE?) (val BFAE?)]
  [openbox (box BFAE?)]
  [seqn    (seq1 BFAE?) (seqs (listof BFAE?))]
  [rec     (fields (listof unit?))]
  [getrec  (fields BFAE?) (selected symbol?)]
  [setrec  (fields BFAE?) (changed symbol?) (newval BFAE?)])

;; BFAE-Value
;; variants: numV, closureV, boxV, recordV
(define-type BFAE-Value
  [numV     (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds DefrdSub?)]
  [boxV     (address integer?)]
  [recordV  (fields (listof rec-unit?))])

;; DefrdSub: mtSub or aSub
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (ds DefrdSub?)])

;; Store: mtSto or aSto
(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)])

;; Value*Store: a pair of BFAE-Value and Store
(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])
;; ============END OF DEFINE-TYPE===============

; unit?: pair -> bool
; To determine whether the pair consists of one symbol and one BFAE
(define (unit? pair)
  (and (symbol? (first pair)) (BFAE? (second pair))))
;(test (unit? (list 'x (num 3))) #t)
;(test (unit? (list (id 'x) (num 3))) #f)

; rec-unit?: list -> bool
; To determine whether the list consists of one symbol and one number
(define (rec-unit? pair)
  (and (symbol? (first pair)) (number? (second pair))))
;(test (rec-unit? (list 'x 3)) #t)
;(test (rec-unit? (list (id 'x) (num 3))) #f)

; parse : sexpr -> BFAE
;; to convert s-expressions into BFAEs
(define (parse sexp)
  (match sexp
    [(? number?)               (num sexp)]
    [(list '+ l r)             (add (parse l) (parse r))]
    [(list '- l r)             (sub (parse l) (parse r))]
    [(? symbol?)               (id sexp)]
    [(list 'fun p b)           (fun (first p) (parse b))]
    [(list 'newbox v)          (newbox (parse v))]
    [(list 'setbox b v)        (setbox (parse b) (parse v))]
    [(list 'openbox b)         (openbox (parse b))]
    [(list 'seqn s1 ss ...)    (seqn (parse s1) (map parse ss))]
    [(list 'rec u ...)         (rec (map (lambda (x) (list (first x) (parse (second x)))) u))]
    [(list 'get f s)           (getrec (parse f) s)]
    [(list 'set f c nv)        (setrec (parse f) c (parse nv))]
    [(list f a)                (app (parse f) (parse a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))
;(test (parse 3) (num 3))
;(test (parse '(+ 3 4)) (add (num 3) (num 4)))
;(test (parse 'x) (id 'x))
;(test (parse '(fun (x) (+ x 3))) (fun 'x (add (id 'x) (num 3))))
;(test (parse '(newbox b)) (newbox (id 'b)))
;(test (parse '(setbox (newbox b) 3)) (setbox (newbox (id 'b)) (num 3)))
;(test (parse '(openbox (newbox b))) (openbox (newbox (id 'b))))
;(test (parse '(seqn (newbox b) (setbox b 3) (openbox b))) (seqn (newbox (id 'b)) (list (setbox (id 'b) (num 3)) (openbox (id 'b)))))
;(test (parse '(rec (x 3) (y 2) (z 5))) (rec (list (list 'x (num 3)) (list 'y (num 2)) (list 'z (num 5)))))
;(test (parse '(get (rec (x 3) (y 4)) x)) (getrec (rec (list (list 'x (num 3)) (list 'y (num 4)))) 'x))
;(test (parse '(set (rec (x 3) (y 4)) x 2)) (setrec (rec (list (list 'x (num 3)) (list 'y (num 4)))) 'x (num 2)))
;(test (parse '((fun (x) (+ x 1)) 10)) (app (fun 'x (add (id 'x) (num 1))) (num 10)))
(test/exn (parse '('x 'y 'z)) "parse: bad syntax: ((quote x) (quote y) (quote z))")

; lookup-ds: symbol DefrdSub -> BFAE-Value
; To find BFAE-Value of symbol in DefrdSub
(define (lookup-ds name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup-ds "free identifier")]
    [aSub  (x val rest)
           (if (symbol=? x name)
               val
               (lookup-ds name rest))]))
;(test/exn (lookup-ds 'x (mtSub)) "free identifier")
;(test (lookup-ds 'x (aSub 'x (numV 3) (mtSub))) (numV 3))
;(test/exn (lookup-ds 'x (aSub 'y (numV 3) (mtSub))) "free identifier")

; lookup-st: integer Store -> BFAE-Value
; To find BFAE-Value of integer in Store
(define (lookup-st addr st)
  (type-case Store st
    [mtSto () (error 'lookup-st "unallocated")]
    [aSto  (i val rest)
           (if (= i addr)
               val
               (lookup-st addr rest))]))
;(test/exn (lookup-st 1 (mtSto)) "unallocated")
;(test (lookup-st 1 (aSto 1 (numV 3) (mtSto))) (numV 3))
;(test/exn (lookup-st 2 (aSto 1 (numV 3) (mtSto))) "unallocated")

; lookup-recV: symbol recordV -> integer
; To find address of symbol in recordV
(define (lookup-recV name recV)
  (cond
    [(empty? (recordV-fields recV)) (error 'lookup-recV "no such field")]
    [else (if (symbol=? name (first (first (recordV-fields recV))))
              (second (first (recordV-fields recV)))
              (lookup-recV name (recordV (rest (recordV-fields recV)))))]))
;(test/exn (lookup-recV 'x (recordV (list ))) "no such field")
;(test (lookup-recV 'x (recordV (list (list 'x 1)))) 1)
;(test/exn (lookup-recV 'y (recordV (list (list 'x 1)))) "no such field")

; replace-st: integer BFAE-Value Store -> Store
; To replace the value at addr in Store
(define (replace-st addr to st)
  (type-case Store st
    [mtSto ()  st]
    [aSto  (i from rest)
           (if (= addr i)
               (aSto i to   (replace-st addr to rest))
               (aSto i from (replace-st addr to rest)))]))
;(test (replace-st 1 (numV 3) (mtSto)) (mtSto))
;(test (replace-st 1 (numV 3) (aSto 1 (numV 5) (mtSto))) (aSto 1 (numV 3) (mtSto)))
;(test (replace-st 2 (numV 3) (aSto 1 (numV 5) (aSto 2 (numV 2)(mtSto)))) (aSto 1 (numV 5) (aSto 2 (numV 3)(mtSto))))

;; ============ functions from lecture note =============
; numV-op: (numV numV -> numV) -> (BFAE-Value BFAE-Value -> BFAE-Value)
; Anonymous func for making numV+, numV-
(define (numV-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
; numV+, numV-: numV numV -> numV
; Helper funcs to interpret add and sub of BFAE
(define numV+ (numV-op +))
(define numV- (numV-op -))

; max-address: Store -> integer
; To find max-address in Store
(define (max-address st)
  (type-case Store st
   [mtSto () 0]
   [aSto (n v st)
         (max n (max-address st))]))

; malloc: Store -> integer
; To find int one more bigger than max-address of Store
(define (malloc st)
  (+ 1 (max-address st)))

; interp-two: BFAE BFAE DefrdSub Store (Value Value Store -> Value*Store) -> Value*Store
; To interp two BFAEs under DefredSub and Store, and then run lambda function
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         [type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)]]]))
;; ======================================================

; interp-ss: list-of-BFAE DefrdSub Store -> Value*Store
; To interp list of BFAEs so that the value of whole is the value of last expr
(define (interp-ss ss ds st)
  (type-case Value*Store (interp (first ss) ds st)
    [v*s (val1 st1) (if (empty? (rest ss))
                        (v*s val1 st1)
                        (interp-ss (rest ss) ds st1))]))

; interp-rec: list-of-unit DefrdSub Store recordV -> Value*Store
; To interp the second one of each (symbol, BFAE) so that make a pair of recordV and Store
(define (interp-rec fields ds st recV)
  (if (empty? fields)
      (v*s recV st)
      (type-case Value*Store (interp (second (first fields)) ds st)
        [v*s (v1 st1)
             (local [(define a (malloc st1))]
               (interp-rec (rest fields) ds (aSto a v1 st1) (recordV (append (recordV-fields recV) (list (list (first (first fields)) a))))))])
  ))

; interp: BFAE DefrdSub Store -> Value*Store
;; to interpret BFAE to BFAE-Value
(define (interp expr ds st)
  (type-case BFAE expr
    [num (n)      (v*s (numV n) st)]
    [add (l r)    (interp-two l r ds st
                              (lambda (v1 v2 st1) (v*s (numV+ v1 v2) st1)))]
    [sub (l r)    (interp-two l r ds st
                              (lambda (v1 v2 st1) (v*s (numV- v1 v2) st1)))]
    [id (s)       (v*s (lookup-ds s ds) st)]
    [fun (x b)    (v*s (closureV x b ds) st)]
    [app (f a)    (interp-two f a ds st
                              (lambda (f-val a-val st1)
                                (interp (closureV-body f-val) (aSub (closureV-param f-val) a-val (closureV-ds f-val)) st1)))]
    
    [newbox (val) (type-case Value*Store (interp val ds st)
                    [v*s (v1 st1)
                         (local [(define a (malloc st1))]
                           (v*s (boxV a)
                                (aSto a v1 st1)))])]
    
    [setbox (bx-expr val-expr) (interp-two bx-expr val-expr ds st
                                           (lambda (bx-val val st1)
                                             (v*s val
                                                  (replace-st (boxV-address bx-val) val st1))))]
    
    [openbox (bx-expr) (type-case Value*Store (interp bx-expr ds st)
                          [v*s (bx-val st1)
                               (v*s (lookup-st (boxV-address bx-val) st1) st1)])]
    
    [seqn (s1 ss) (type-case Value*Store (interp s1 ds st)
                    [v*s (v1 st1) (if (empty? ss)
                                      (v*s v1 st1)
                                      (interp-ss ss ds st1))])]

    [rec (f)     (type-case Value*Store (interp-rec f ds st (recordV (list )))
                      [v*s (v1 st1) (v*s v1 st1)])]
    
    [getrec (f s)    (type-case Value*Store (interp f ds st)
                       [v*s (rec-val st1)
                            (v*s (lookup-st (lookup-recV s rec-val) st1) st1)])]
    
    [setrec (f c nv) (interp-two f nv ds st
                                 (lambda (rec-val new-val st1)
                                   (v*s new-val
                                        (replace-st (lookup-recV c rec-val) new-val st1))))]
    ))


; interp-expr: BFAE -> number or symbol
(define (interp-expr bfae)
  (define value (v*s-value (interp bfae (mtSub) (mtSto))))
    (type-case BFAE-Value value
      [numV     (n)          n]
      [closureV (p b ds)    'func]
      [boxV     (a)         'box]
      [recordV  (f)         'record]))
;(test (interp-expr (num 3)) 3)
;(test (interp-expr (fun 'x (add (id 'x) (num 3)))) 'func)
;(test (interp-expr (newbox (num 0))) 'box)
;(test (interp-expr (rec (list (list 'x (num 3)) (list 'y (num 2)) (list 'z (num 5))))) 'record)
;(test (interp-expr (app (fun 'x (getrec (id 'x) 'x)) (rec (list (list 'x (num 3)) (list 'y (num 2)))))) 3)


#|(test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))
(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "unallocated")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record) |#
