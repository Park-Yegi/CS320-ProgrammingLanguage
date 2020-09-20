#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

; string->sexpr: string -> sexpr
; to change string to sexpr
(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))
;(test/exn (string->sexpr 1) "expects argument of type <string>")
;(test/exn (string->sexpr ".") "syntax error (bad contents)")
;(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")


;; -------DEFINE-TYPE----------
;; FWAE abstract syntax trees
;; type of variant: num, add, sub, with, id, fun, app
(define-type FWAE
  [num  (n number?)]
  [add  (lhs FWAE?) (rhs FWAE?)] 
  [sub  (lhs FWAE?) (rhs FWAE?)]
  [with (name symbol?) (named-expr FWAE?) (body FWAE?)]
  [id   (name symbol?)]
  [fun  (params (listof symbol?)) (body FWAE?)]
  [app  (ftn FWAE?) (arg (listof FWAE?))]
  [rcd  (fields (listof unit?))]
  [acc  (fields FWAE?) (select symbol?)])

;; FWAE-Value abstract syntax trees
(define-type FWAE-Value
  [numV     (n number?)]
  [closureV (params (listof symbol?)) (body FWAE?) (ds DefrdSub?)]
  [recordV  (r rcd?)])

;; Deferred Substitution
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FWAE-Value?) (ds DefrdSub?)])
;; ------END OF DEFINE-TYPE--------


; unit?: pair -> bool
; To determine whether the pair consists of one symbol and one FWAE
(define (unit? pair)
  (and (symbol? (first pair)) (FWAE? (second pair))))
;(test (unit? (list 'x (num 3))) #t)
;(test (unit? (list (id 'x) (num 3))) #f)

; same?: list-of-sym -> bool
; To find out whether there are two same parameters or not
(define (same? params)
  (if (= (length params) (length (remove-duplicates params))) #f #t))
;(test (same? '(a a b c a)) #t)
;(test (same? '(a b c d)) #f)


; dup?: list-of-pair(key, value) -> bool
; To find out whether there are two same keys or not
(define (dup? pairs)
  (define keys (map first pairs))
  (same? keys))
;(test (dup? '(('a 3) ('b 2) ('a 1))) #t)
;(test (dup? '(('a 1) ('b 2) ('c 3))) #f)


; parse-sexpr : sexpr -> FWAE
;; to convert s-expressions into FWAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?)               (num sexp)]
    [(list '+ l r)             (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r)             (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?)               (id sexp)]
    [(list 'fun p b)           (if (same? p)
                                   (error 'parse "bad syntax")
                                   (fun p (parse-sexpr b)))]
    [(list 'record p ...)      (if (dup? p)
                                   (error 'parse "duplicate fields")
                                   (rcd (map (lambda (x) (list (first x) (parse-sexpr (second x)))) p)))]
    [(list 'access f s)        (acc (parse-sexpr f) s)]
    [(list f a ...)            (app (parse-sexpr f) (map parse-sexpr a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))
;(test (parse-sexpr (string->sexpr "3")) (num 3))
;(test (parse-sexpr '(+ 2 5)) (add (num 2) (num 5)))
;(test (parse-sexpr '(- x 3)) (sub (id 'x) (num 3)))
;(test (parse-sexpr '(with (x 3) (+ x x))) (with 'x (num 3) (add (id 'x) (id 'x))))
;(test (parse-sexpr 'x) (id 'x))
;(test/exn (parse-sexpr '(fun (x x) (+ x 1))) "parse: bad syntax")
;(test (parse-sexpr '(fun (x y) (+ x 1))) (fun '(x y) (add (id 'x) (num 1))))
;(test (parse-sexpr '((fun (x y) (+ x y)) 10 2))  (app (fun '(x y) (add (id 'x) (id 'y))) (list (num 10) (num 2))))
;(test (parse-sexpr '(record (x 3))) (rcd (list (list 'x (num 3)))))
;(test (parse-sexpr '(record (x 3) (y 2))) (rcd (list (list 'x (num 3)) (list 'y (num 2)))))
;(test/exn (parse-sexpr '(record (x 2) (x 3))) "parse: duplicate fields")
;(test (parse-sexpr '(access (record (x 3) (y 2)) x)) (acc (rcd (list (list 'x (num 3)) (list 'y (num 2)))) 'x))


; parse: string -> FWAE
;; to parse a string containing a FWAE expression to a FWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

; lookup: symbol DefrdSub -> FWAE-Value
; To find FWAE-Value of symbol in DefrdSub
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub  (x val rest)
           (if (symbol=? x name)
               val
               (lookup name rest))]))

; lookup-record: list-of-pair symbol -> FWAE
; To return second of pair if the first of pair is same as symbol
(define (lookup-record pairs id)
  (cond
    [(empty? pairs) (error 'lookup-record "no such field")]
    [else           (if (symbol=? id (first (first pairs)))
                        (second (first pairs))
                        (lookup-record (rest pairs) id))]))
;(test/exn (lookup-record (list (list 'x (num 3)) (list 'y (num 2)) (list 'z (num 1))) 'a) "lookup-record: no such field")
;(test (lookup-record (list (list 'x (num 3)) (list 'y (num 2)) (list 'z (num 1))) 'x) (num 3))

; num-op: (number number -> number) -> (FWAE-Value FWAE-Value -> FWAE-Value)
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


; interp_argu: list-of-FWAE DefrdSub -> list-of-FWAE-Value
; To get the list-of-value of parameters from list-of-arguments
(define (interp_argu a ds)
  (cond
    [(empty? a) empty]
    [else (append (list (interp (first a) ds)) (interp_argu (rest a) ds))]))



;; extend_ds: list-of-sym list-of-FWAE-Value DefrdSub -> DefrdSub
; To add (symbol, value) sets to DefrdSub
(define (extend_ds syms vals ds)
  (cond
    [(empty? syms) ds]
    [else (extend_ds (rest syms) (rest vals) (aSub (first syms) (first vals) ds))]))
;(test (extend_ds '() '() (mtSub)) (mtSub))
;(test (extend_ds '(x) (list (numV 3)) (mtSub)) (aSub 'x (numV 3) (mtSub)))
;(test (extend_ds '(x y) (list (numV 3) (numV 5)) (mtSub)) (aSub 'y (numV 5) (aSub 'x (numV 3) (mtSub))))


; interp: FWAE DefrdSub-> FWAE-Value
;; to interpret FWAE to FWAE-Value
(define (interp fwae ds)
  (type-case FWAE fwae
    [num (n)      (numV n)]
    [add (l r)    (num+ (interp l ds) (interp r ds))]
    [sub (l r)    (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub x (interp i ds) ds))]
    [id (s)       (lookup s ds)]
    [fun (x b)    (closureV x b ds)]
    [app (f a)    (local [(define f-val (interp f ds))
                          (define a-val (interp_argu a ds))]
                     (if (= (length a-val) (length (closureV-params f-val)))
                        (interp (closureV-body f-val)
                            (extend_ds (closureV-params f-val) a-val (closureV-ds f-val)))
                        (error 'interp "wrong arity")))]
    [rcd (f)      (recordV (rcd (map (lambda (x)
                                       (define f-val (interp (second x) ds))
                                       (list (first x)
                                             (type-case FWAE-Value f-val
                                               [numV (n)          (num (numV-n f-val))]
                                               [closureV (p b ds) (fun (closureV-params f-val) (closureV-body f-val) ds)]
                                               [recordV (r)       (rcd (rcd-fields (recordV-r f-val)))]))
                                       ) f)))]
    [acc (f s)    (interp (lookup-record (rcd-fields (recordV-r (interp f ds))) s) ds)]))

;; test case of interp_argu
;(test (interp_argu '() (mtSub)) '())
;(test (interp_argu (list (num 3)) (mtSub)) (list (numV 3)))
;(test (interp_argu (list (num 3) (num 5) (num 7)) (mtSub)) (list (numV 3) (numV 5) (numV 7)))
;(test (interp_argu (list (id 'x) (num 5) (num 7)) (aSub 'x (numV 3) (mtSub))) (list (numV 3) (numV 5) (numV 7)))
;(test (interp_argu (list (fun '(x y) (add (id 'x) (id 'y)))) (mtSub)) (list (closureV '(x y) (add (id 'x) (id 'y)) (mtSub))))

;; test case of interp
;(test (interp (num 3) (mtSub)) (numV 3))
;(test (interp (add (num 3) (num 5)) (mtSub)) (numV 8))
;(test (interp (sub (num 5) (id 'x)) (aSub 'x (numV 2) (mtSub))) (numV 3))
;(test (interp (with 'x (num 3) (add (id 'x) (num 3))) (mtSub)) (numV 6))
;(test/exn (interp (id 'x) (mtSub)) "lookup: free identifier")
;(test (interp (id 'x) (aSub 'x (numV 3) (mtSub))) (numV 3))
;(test (interp (fun '(x y) (add (id 'x) (id 'y))) (mtSub)) (closureV '(x y) (add (id 'x) (id 'y)) (mtSub)))
;(test (interp (app (fun '(x y) (add (id 'x) (id 'y))) (list (num 3) (num 5))) (mtSub)) (numV 8))
;(test/exn (interp (app (fun '(x y) (add (id 'x) (id 'y))) (list (num 5))) (mtSub)) "interp: wrong arity")
;(test (interp (rcd (list (list 'x (num 2)))) (mtSub)) (recordV (rcd (list (list 'x (num 2))))))
;(test (interp (rcd (list (list 'x (num 2)) (list 'y (num 3)))) (mtSub)) (recordV (rcd (list (list 'x (num 2)) (list 'y (num 3))))))
;(test (interp (acc (rcd (list (list 'x (num 2)) (list 'y (num 3)))) 'x) (mtSub)) (numV 2)) 


; run : string -> number or string
;; to evaluate a FWAE program contained in a string
(define (run str)
  (define value (interp (parse str) (mtSub)))
  (type-case FWAE-Value value
    [numV (n)          n]
    [closureV (p b ds) 'function]
    [recordV (r)       'record]))
;(test (run "3") 3)
;(test (run "{+ 3 5}") 8)
;(test (run "{with {x 3} {+ x 3}}") 6)
;(test/exn (run "x") "lookup: free identifier")
;(test (run "{fun {x y} {+ x y}}") 'function)
;(test (run "{{fun {x y} {+ x y}} 3 5}") 8)

#|
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test/exn (run "{access {record {b 10} {b {+ 1 2}}} b}") "duplicate fields")
(test/exn (run "{access {record {a 10}} b}") "no such field")
(test (run "{with {g {fun {r} {access r c}}} {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test/exn (run "{record {z {access {record {z 0}} y}}}") "no such field")
(test (run "{with {f {fun {a b} {+ a b}}} {with {g {fun {x} {- x 5}}} {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}} {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}} {h 1 4 5 6}}") 7)
(test (run "{with {f {fun {} 4}} {with {g {fun {x} {+ x x}}} {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {access {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {access a a} b}}} {with {g {fun {x} {+ 5 x}}} {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}} {access {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}} {access {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}} {access {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}} {access {f 1 2 3} d}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}} {f {access {access {record {a {record {a 10} {b {- 5 2}}}} {b {access {record {x 50}} x}}} a} b}}}") 8)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{record {a 10}}") `record)
(test (run "{access {record {a 10}} a}") 10)
(test (run "{access {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{access {record {a {record {b 10}}}} a}") `record)
(test (run "{access {access {record {a {record {a 10}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{+ {access {record {a 10}} a} {access {record {a 20}} a}}") 30)
(test (run "{+ {access {record {a 10}} a} {access {record {a 20}} a}}") 30)
(test (run "{record {a 10}}") `record)
(test (run "{record {a {- 2 1}}}") `record)
(test (run "{access {record {a 10}} a}") 10)
(test (run "{access {record {a {- 2 1}}} a}") 1)
(test (run "{access {record {a {record {b 10}}}} a}") `record)
(test (run "{access {access {record {a {record {a 10}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {access y y}}") 2)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {access y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {access r c}}} {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
|#

(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {access r c}}} {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {f {fun {a b} {+ a b}}} {with {g {fun {x} {- x 5}}} {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}} {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}} {h 1 4 5 6}}") 7) 
(test (run "{with {f {fun {} 4}} {with {g {fun {x} {+ x x}}} {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {access {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {access a a} b}}} {with {g {fun {x} {+ 5 x}}} {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}} {access {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}} {access {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}} {f {access {access {record {a {record {a 10} {b {- 5 2}}}} {b {access {record {x 50}} x}}} a} b}}}") 8)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{access {record {a 10}} a}") 10)
(test (run "{access {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{access {record {a {record {b 10}}}} a}") 'record)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{+ {access {record {a 10}} a} {access {record {a 20}} a}}") 30)
(test (run "{access {record {a {record {b 10}}}} a}") 'record)
(test (run "{access {access {record {a {record {a 10}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {access y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {access r c}}} {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test/exn (run "{access {record {b 10} {b {+ 1 2}}} b}") "duplicate fields")
(test/exn (run "{access {record {a 10}} b}") "no such field")
(test/exn (run "{record {z {access {record {z 0}} y}}}") "no such field")
(test (run "{with {f {fun {} {fun {f} {fun {} 5}}}} {+ {{{f} 1}} {{{f} 2}}}}") 10)
(test (run "{with {d {record {a 0} {c 1} {b 0} {e 1}}} {{fun {c} {access c e}} d}}") 1)
(test (run "{with {g {fun {r} {access {r} c}}} {g {fun {} {record {a 0} {c 12} {b 7}}}}}") 12)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}} {access {f 1 {fun {y} y} 3} y}}") 'function)
(test (run "{with {f {fun {a b c d e} {fun {x y z} {+ x {+ y {+ z {access {record {a a} {b b} {c c} {d d} {e e}} a}}}}}}} {{f 1 2 3 4 5} {+ 1 2} 3 3}}") 10)
(test/exn (run "{access {record {b 10} {a {+ {record {a 0} {c 1} {b 0} {b 1}} 2}}} b}") "duplicate fields")
(test/exn (run "{access {with {d {record {a 0} {c 1} {b 0} {e 1}}} {access d d}} b}") "no such field")
(test/exn (run "{with {d {record {a 0} {c 1} {b 0} {e 1}}} {{fun {c} {access c d}} d}}") "no such field")
(test/exn (run "{with {g {fun {r} {access r c}}} {g {record {a 0} {b 7}}}}") "no such field")
(test/exn (run "{with {f {fun {a b c d e} {fun {x y z a} {+ x {+ y {+ z {access {record {a a} {b b} {c c} {d d} {e e}} a}}}}}}} {{f 1 2 3 4 5} {+ 1 2} 3 3}}") "wrong arity")

