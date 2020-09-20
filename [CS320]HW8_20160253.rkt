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

;; ===========DEFINE-TYPE================
(define-type KCFAE
  [num       (n number?)]
  [add       (lhs KCFAE?)
             (rhs KCFAE?)]
  [sub       (lhs KCFAE?)
             (rhs KCFAE?)]
  [id        (name symbol?)]
  [fun       (param (listof symbol?))
             (body KCFAE?)]
  [app       (fun-expr KCFAE?)
             (arg-expr (listof KCFAE?))]
  [if0       (test KCFAE?)
             (then KCFAE?)
             (else KCFAE?)]
  [withcc    (name symbol?)
             (body KCFAE?)]
  [try-catch (try KCFAE?)
             (catch KCFAE?)]
  [throw])

(define-type KCFAE-Value
  [numV     (n number?)]
  [closureV (param (listof symbol?))
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV    (proc procedure?)]
  [throwV])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; =====================================

;; parse : S-expr -> KCFAE
;; to convert s-expressions into KCFAEs
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(fun) (fun (second sexp) (parse (third sexp)))]
       [(if0) (if0 (parse (second sexp))
                   (parse (third sexp))
                   (parse (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse (third sexp)))]
       [(try) (try-catch (parse (second sexp)) (parse (fourth sexp)))]
       [(throw) (throw)]
       [else (app (parse (first sexp)) (map parse (rest sexp)))])]))

;(test (parse 3) (num 3))
;(test (parse 'x) (id 'x))
;(test (parse '{+ 1 2}) (add (num 1) (num 2)))
;(test (parse '{- 1 2}) (sub (num 1) (num 2)))
;(test (parse '{fun {} x}) (fun '() (id 'x)))
;(test (parse '{fun {x} x}) (fun '(x) (id 'x)))
;(test (parse '{fun {x y} x}) (fun '(x y) (id 'x)))
;(test (parse '{1}) (app (num 1) '()))
;(test (parse '{1 2}) (app (num 1) (list (num 2))))
;(test (parse '{1 2 3}) (app (num 1) (list (num 2) (num 3))))
;(test (parse '{if0 0 1 2}) (if0 (num 0) (num 1) (num 2)))
;(test (parse '{withcc x 2}) (withcc 'x (num 2)))
;(test (parse '{try {+ 1 2} catch 0}) (try-catch (add (num 1) (num 2)) (num 0)))
;(test (parse '{throw}) (throw))

;; ----------------------------------------

; interp_argu: list-of-KCFAE DefrdSub (KCFAE->Value -> alpha) -> list-of-KCFAE-Value
; To get the list-of-value of parameters from list-of-arguments
(define (interp_argu a ds k)
  (cond
    [(empty? a) (k empty)]
    [else (interp (first a) ds (lambda (arg-val)
                                 (if (throwV? arg-val)
                                     (k (list arg-val))
                                     (local [(define mid (interp_argu (rest a) ds (lambda (x) x)))]
                                      (if (list? mid)
                                          (k (append (list arg-val) mid))
                                          mid)))))]))


;; extend_ds: list-of-sym list-of-KCFAE-Value DefrdSub -> DefrdSub
; To add (symbol, value) sets to DefrdSub
(define (extend_ds syms vals ds)
  (cond
    [(empty? syms) ds]
    [else (extend_ds (rest syms) (rest vals) (aSub (first syms) (first vals) ds))]))
;(test (extend_ds '() '() (mtSub)) (mtSub))
;(test (extend_ds '(x) (list (numV 3)) (mtSub)) (aSub 'x (numV 3) (mtSub)))
;(test (extend_ds '(x y) (list (numV 3) (numV 5)) (mtSub)) (aSub 'y (numV 5) (aSub 'x (numV 3) (mtSub))))


;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
;; To interpret KCFAE to KCFAE-Value
(define (interp a-fae ds k)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (if (throwV? v1)
                             (k (throwV))
                             (interp r ds
                                     (lambda (v2)
                                       (if (throwV? v2)
                                           (k (throwV))
                                           (k (num+ v1 v2))))))))]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (if (throwV? v1)
                             (k (throwV))
                             (interp r ds
                                     (lambda (v2)
                                       (if (throwV? v2)
                                           (k (throwV))
                                           (k (num- v1 v2))))))))]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (if (throwV? fun-val)
                       (k (throwV))
                       (interp_argu arg-expr ds
                           (lambda (arg-vals)
                             (if (empty? (filter throwV? arg-vals))
                                 (type-case KCFAE-Value fun-val
                                   [closureV (param body ds)
                                             (if (= (length arg-vals) (length param))
                                                 (interp body
                                                         (extend_ds param arg-vals ds)
                                                         k)
                                                 (error 'interp "wrong arity"))]
                                   [contV (k)
                                          (k (first arg-vals))]
                                   [else (error 'interp "not a function")])
                                 (k (throwV))))))))]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (throwV? v)
                       (k (throwV))
                       (if (numzero? v)
                           (interp then-expr ds k)
                           (interp else-expr ds k)))))]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k)]
    [try-catch (try catch)
               (interp try ds
                       (lambda (try-val)
                         (if (throwV? try-val)
                             (interp catch ds k)
                             (k try-val))))]
    [throw ()  (k (throwV))]))
;(test (interp (num 3) (mtSub) (lambda (x) x)) (numV 3))
;(test (interp (add (num 3) (num 2)) (mtSub) (lambda (x) x)) (numV 5))
;(test (interp (sub (num 3) (num 2)) (mtSub) (lambda (x) x)) (numV 1))
;(test/exn (interp (id 'x) (mtSub) (lambda (x) x)) "lookup: free variable")
;(test (interp (id 'x) (aSub 'x (numV 3) (mtSub)) (lambda (x) x)) (numV 3))
;(test (interp (fun '(x y) (add (id 'x) (id 'y))) (mtSub) (lambda (x) x)) (closureV '(x y) (add (id 'x) (id 'y)) (mtSub)))


;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
; Anonymous func for making num+, num-
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
; num+, num-: numV numV -> numV
; Helper funcs to interpret add and sub of KCFAE
(define num+ (num-op + '+))
(define num- (num-op - '-))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

; lookup: symbol DefrdSub -> KCFAE-Value
; To find KCFAE-Value which is matched with symbol in DefrdSub
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))
;(test/exn (lookup 'x (mtSub)) "free variable")
;(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
;(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> KCFAE-Value
;; To call 'interp' with empty environment and identity func
(define (interp-expr a-fae)
  (type-case KCFAE-Value (interp a-fae (mtSub) (lambda (x) x))
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]
    [throwV () 'throw]))
;(test (interp-expr (num 3)) (numV 3))
;(test (interp-expr (add (num 3) (num 2))) (numV 5))
;(test (interp-expr (sub (num 3) (num 2))) (numV 1))
;(test/exn (interp-expr (id 'x)) "lookup: free variable")
;(test (interp-expr (fun '(x y) (add (id 'x) (id 'y)))) (closureV '(x y) (add (id 'x) (id 'y)) (mtSub)))

; run : string -> number or 'function
;; to evaluate a KCFAE program contained in a string
(define (run str)
  (interp-expr (parse (string->sexpr str))))

;(test (run "{{fun {} 1}}") 1)
;(test (run "{{fun {x y} {+ x y}} 1 2}") 3)
;(test (run "{fun {} 1}") 'function)
;(test (run "{fun {x y z w} 1}") 'function)
;(test (run "{withcc x {try {throw} catch 1}}") 1)
;(test (run "{withcc x {+ 1 {x 2}}}") 2)
;(test (run "{try {+ {throw} 1} catch {fun {x} x}}") 'function)
;(test (run "{withcc x {try {+ {throw} 1} catch x}}") 'function)
;(test (run "{try {if0 0 {throw} 1} catch 0}") 0)


#|(test (run "{try 7 catch 8}")
        7)
  (test (run "{try {throw} catch 8}")
        8)
  (test (run "{try {+ 1 {throw}} catch 8}")
        8)
  (test (run "{{fun {f} {try {f 3} catch 8}}
               {fun {x} {throw}}}")
        8)
  (test (run "{try {try {throw} catch 8} catch 9}")
        8)
  (test (run "{try {try {throw} catch {throw}} catch 9}")
        9)
  (test (run "{try {try 7 catch {throw}} catch 9}")
        7)
  (test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}")
	8)

; multiple arguments (5)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)

; exceptions (35)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) ; exit from recursive function using continuation
(test (run "{withcc k {- 0 {k 100}}}" ) 100)
(test (run "{withcc k {k {- 0 100}}}" ) -100)
(test (run "{withcc k {k {+ 100 11}}}" ) 111)
(test (run "{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}" ) 0)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}") 20)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}") 110) ; exit from recursive function using try-catch
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}") 54) ; equal? for multiple recursive try-catch
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}") 2)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}") 20110464) ; recursive try-catch throwing (1)
(test (run "{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}") 0)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}") 89)
(test (run "{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}") 11)
(test (run "{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}") 5)
(test (run "{+ {try {- 10 {throw}} catch 3} 10}") 13)
(test (run "{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}") 54)
(test (run "{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}") 10)
(test (run "{try {- 0 {throw}} catch 5}") 5)
(test (run "{try {if0 {throw} 3 4} catch 5}") 5)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)

; multiple arguments (6)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x done}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 1099)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 11053)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {+ y {g g {- y 1} z}}}} 10}}}") 0)
(test (run "{withcc done {{fun {f x} {f f x {fun {x} {if0 x {fun {y} {fun {x} {+ x y}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}}") 64)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}} 5}") 'function)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}}") 42)

; exceptions (4)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}} catch 4242}") 4242)
(test (run "{withcc esc {{try {withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} catch esc} 33}}") 33)
(test (run "{try {try {throw} catch {try {throw} catch {try {throw} catch {+ {withcc k {try {throw} catch {k 0}}} {throw}}}}} catch 0}") 0)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {throw}}}}} catch 4242}") 4242) |#