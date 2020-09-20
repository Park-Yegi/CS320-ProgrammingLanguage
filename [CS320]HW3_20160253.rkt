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

;; MUWAE abstract syntax trees
(define-type MUWAE
  [num       (items (listof number?))]
  [add       (left MUWAE?) (right MUWAE?)]
  [sub       (left MUWAE?) (right MUWAE?)]
  [with      (name symbol?) (init MUWAE?) (body MUWAE?)]
  [id        (name symbol?)]
  [muwae-min (left MUWAE?) (middle MUWAE?) (right MUWAE?)]
  [muwae-max (left MUWAE?) (middle MUWAE?) (right MUWAE?)])

; bin-op : (number number -> number) (listof number) (listof number) -> (listof number)
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists, and return the list of all of the results
;; Assumption: if either ls or rs is null, the output is also null
(define (bin-op op ls rs)
  ; helper: number list-of-number -> list-of-number
  ;; to op all elements of rs with l
  (define (helper l rs)
    ; f : number -> number
    ;; to op l and r
    (define (f r)
      (op l r))
    (if (null? rs)
        null
        (map f rs)))
  (if (null? ls)
    null
    (append (helper (first ls) rs) (bin-op op (rest ls) rs))))

;(test (bin-op + '() '()) '())
;(test (bin-op + '() '(1)) '())
;(test (bin-op - '(1) '()) '())
;(test (bin-op - '(3) '(1)) '(2))
;(test (bin-op + '(1 2) '(3 4)) '(4 5 5 6))

; parse-sexpr : sexpr -> MUWAE
;; to convert s-expressions into MUWAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num (list sexp))]
    [(? (listof number?)) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(list 'muwae-min l m r) (muwae-min (parse-sexpr l) (parse-sexpr m) (parse-sexpr r))]
    [(list 'muwae-max l m r) (muwae-max (parse-sexpr l) (parse-sexpr m) (parse-sexpr r))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

(test (parse-sexpr '3) (num '(3)))
(test (parse-sexpr '(1 2 3)) (num '(1 2 3)))
(test (parse-sexpr '(+ 2 5)) (add (num '(2)) (num '(5))))
(test (parse-sexpr '(- x 3)) (sub (id 'x) (num '(3))))
(test (parse-sexpr '(with (x 3) (+ x x))) (with 'x (num '(3)) (add (id 'x) (id 'x))))
(test (parse-sexpr 'x) (id 'x))
(test (parse-sexpr '(muwae-min 1 2 3)) (muwae-min (num '(1)) (num '(2)) (num '(3))))
(test (parse-sexpr '(muwae-max x y z)) (muwae-max (id 'x) (id 'y) (id 'z)))
(test/exn (parse-sexpr '(error test)) "parse: bad syntax: (error test)")


; parse: string -> MUWAE
;; to parse a string containing a MUWAE expression to a MUWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))


; subst: MUWAE symbol list-of-number -> MUWAE
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (type-case MUWAE expr
    [num (n)   expr]
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (num to) expr)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]
    [muwae-min (l m r) (muwae-min (subst l from to) (subst m from to) (subst r from to))]
    [muwae-max (l m r) (muwae-max (subst l from to) (subst m from to) (subst r from to))]
    ))

;(test (subst (muwae-max (num '(1)) (num '(2)) (num '(3))) 'x '(4)) (muwae-max (num '(1)) (num '(2)) (num '(3))))
;(test (subst (muwae-min (id 'x) (num '(1)) (num '(2))) 'x '(2)) (muwae-min (num '(2)) (num '(1)) (num '(2))))


;; eval: MUWAE -> list-of-number
;; to evaluate MUWAE expressions by reducing them to list-of-number
;; Assumption: l, m, r of muwae-min&muwae-max is a list-of-number in which there is only one element.
(define (eval expr)
  (type-case MUWAE expr
    [num (i) i]
    [add (l r) (bin-op + (eval l) (eval r))]
    [sub (l r) (bin-op - (eval l) (eval r))]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name) (error 'eval "free identifier: ~s" name)]
    [muwae-min (l m r)
               (define left   (first (eval l)))
               (define middle (first (eval m)))
               (define right  (first (eval r)))
               (cond
                 [(< left middle) (if (< left right) (eval l) (eval r))]
                 [(> left middle) (if (< middle right) (eval m) (eval r))]
                 [else            (if (< left right) (eval l) (eval r))])]
    [muwae-max (l m r)
               (define left   (first (eval l)))
               (define middle (first (eval m)))
               (define right  (first (eval r)))
               (cond
                 [(< left middle) (if (< middle right) (eval r) (eval m))]
                 [(> left middle) (if (< left right) (eval r) (eval l))]
                 [else            (if (< left right) (eval r) (eval l))])]))

;(test (eval (num '(1 2))) '(1 2))
;(test (eval (add (num '(1)) (num '(2)))) '(3))
;(test (eval (sub (num '(5 7)) (num '(1 2)))) '(4 3 6 5))
;(test (eval (with 'x (num '(2 3)) (add (id 'x) (id 'x)))) '(4 5 5 6))
;(test/exn (eval (id 'x)) "eval: free identifier: x")
;(test (eval (muwae-min (num '(1)) (num '(-1)) (num '(0)))) '(-1))
;(test (eval (muwae-max (num '(0)) (num '(0)) (num '(0)))) '(0))
;(test (eval (muwae-max (with 'x (num '(3)) (add (num '(3)) (id 'x))) (num '(1)) (num '(2)))) '(6))


; run : string -> listof number
;; to evaluate a MUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;(test (run "{+ 1 3}") '(4))
;(test (run "{+ {1} {3 4}}") '(4 5))
;(test (run "{with {x 2} {muwae-min 7 4 x}}") '(2))
;(test (run "{+ {muwae-min 10 9 8} {muwae-max 1 2 3}}") '(11))
;(test (run "{with {x {muwae-min 1 2 3}} {+ x x}}") '(2))

;(test (run "{+ 3 7}") '(10))
;(test (run "{- 10 {3 5}}") '(7 5))
;(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))

;(test (run "{+ {1 2} {3 4}}") '(4 5 5 6))
;(test (run "{- {+ {1 2} {3 4}} {1 2}}") '(3 2 4 3 4 3 5 4))
;(test (run "{- {10 2 1} {3 2}}") '(7 8 -1 0 -2 -1))
;(test (run "{with {x {1 2}} {+ x {4 3}}}") '(5 4 6 5))
;(test (run "{with {x 9} {+ x {with {x 3} x}}}") '(12))
;(test (run "{with {x 100} {+ x {with {y 3} x}}}") '(200))
;(test (run "{with {x 5} {+ x {with {x 3} 10}}}") '(15))
;(test (run "{with {x {7 5}} {+ x x}}") '(14 12 12 10))
;(test (run "{with {x {1 2}} {+ x {4 3}}}") '(5 4 6 5))
;(test (run "{with {x 2} {- {+ x x} x}}") '(2))
;(test (run "{+ {muwae-min 3 5 7} {muwae-min 10 100 1000}}") '(13))
;(test (run "{+ {muwae-min 9 3 7} {muwae-max 6 2 20}}") '(23))
;(test (run "{with {x 10} {muwae-max x 2 3}}") '(10))
;(test (run "{with {x 20} {with {y 5} {with {z {10 20}} {+ z {muwae-max {+ x y} 0 12}}}}}") '(35 45))
;(test (run "{with {x 20} {with {y 5} {with {z {10 20}} {+ z {muwae-min {+ x y} 0 12}}}}}") '(10 20))
;(test (run "{with {x {muwae-min 3 9 5}} {with {y {- x 3}} y}}") '(0))
;(test (run "{with {x {muwae-max 2 3 5}} {muwae-min x 7 6}}") '(5))
;(test (run "{with {x {muwae-max 9 7 10}} {muwae-max 8 x {+ 1 x}}}") '(11))
;(test (run "{- {muwae-min 6 4 5} {muwae-max 2 3 4}}") '(0))
;(test (run "{with {x {+ 7 2}} {muwae-min x 7 0}}") '(0))
;(test (run "{+ {muwae-min 9 3 7} {muwae-max 6 2 20}}") '(23))
;(test (run "{with {x {13}} {muwae-min x 1 12}}") '(1))
;(test (run "{with {x {muwae-min 2 1 3}} {+ x x}}") '(2))
;(test (run "{with {a 10} {with {b 19} {with {c 2} {muwae-min a b c}}}}") '(2))
;(test (run "{with {x 3} {muwae-max 3 4 {+ x x}}}") '(6))
;(test (run "{with {a 10} {with {b 19} {with {c 2} {muwae-max a b c}}}}") '(19))
;(test (run "{with {x {muwae-min 2 5 4}} {+ x x}}") '(4))
;(test (run "{with {x {muwae-max 2 5 4}} {+ x x}}") '(10))
;(test (run "{with {x {- 11 3}} {muwae-max x {+ x x} {- x x}}}") '(16))
;(test (run "{with {x {- 11 3}} {muwae-min x {+ x x} {- x x}}}") '(0))
;(test (run "{muwae-min {+ 4 4} {with {x 5} {+ x {with {x 3} 10}}} 3}") '(3))
;(test (run "{muwae-max {+ 4 4} {with {x 5} {+ x {with {x 3} 10}}} 3}") '(15))
;(test (run "{with {x {13}} {muwae-min x 1 12}}") '(1))
;(test (run "{with {x {10} } {muwae-max x 2 3}}") '(10))
;(test (run "{with {x {muwae-min 2 1 3}} {+ x x}}") '(2))
;(test (run "{with {x {muwae-max 2 1 3}} {+ x x}}") '(6))
;(test (run "{with {x 2} {muwae-min x 3 10}}") '(2))
;(test (run "{with {x 2} {muwae-max x 3 10}}") '(10))
;(test (run "{muwae-min {+ 4 4} 2 3} ") '(2))
;(test (run "{muwae-max {+ 4 4} 2 3} ") '(8))
;(test (run "{with {x 10} {muwae-min x 2 3}}") '(2))
;(test (run "{with {x 10} {muwae-max x 2 3}}") '(10))
;(test (run "{with {x {10}} {muwae-max x 2 3}}") '(10))
;(test (run "{muwae-min {+ 3 4} 5 6}") '(5))
;(test (run "{muwae-max {+ 3 4} 5 6}") '(7))
;(test (run "{with {x {10}} {muwae-min x {3} {5}}}") '(3))
;(test (run "{with {x {10}} {muwae-max x {3} {5}}}") '(10))
;(test (run "{muwae-min {3} 4 5}") '(3))
;(test (run "{muwae-max {3} 4 {5}}") '(5))
;(test (run "{+ {10 100 1000 10000} {muwae-min {- 3 4} 5 6}}") '(9 99 999 9999))
