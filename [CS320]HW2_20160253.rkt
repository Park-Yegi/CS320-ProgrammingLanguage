#lang plai

; type WAE: an variant is num or add or sub or with or id
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

; free-ids: WAE -> list-of-symbol
; to find out the list of free identifiers
(define (free-ids w)
  (type-case WAE w
    [num (n)      '()]
    [add (l r)    (remove-duplicates (sort (append (free-ids l) (free-ids r)) symbol<?))]
    [sub (l r)    (remove-duplicates (sort (append (free-ids l) (free-ids r)) symbol<?))]
    [with (n e b) (remove-duplicates (sort (append (free-ids e) (remove n (free-ids b))) symbol<?))]
    [id (n)       (cons n empty)]))

(test (free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '())
(test (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
(test (free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b y))
(test (free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b t y))
(test (free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a b c y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))


; binding-ids: WAE -> list-of-symbol
; to find out the list of identifiers which are binding occurences
(define (binding-ids w)
  (type-case WAE w
    [num  (n)     '()]
    [add  (l r)   '()]
    [sub  (l r)   '()]
    [with (n e b) (remove-duplicates (sort (cons (with-name w) (append (binding-ids (with-body w)) (binding-ids (with-named-expr w)))) symbol<?))]
    [id   (n)     '()]))

(test (binding-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
(test (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x y))
(test (binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
(test (binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
(test (binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w z))


; check-bound: symbol WAE -> boolean
; to determine the symbol is used in WAE
(define (check-bound s w)
  (type-case WAE w
    [num (n)      #f]
    [add (l r)    (or (check-bound s l) (check-bound s r))]
    [sub (l r)    (or (check-bound s l) (check-bound s r))]
    [with (n e b) (or (check-bound s e) (check-bound s b))]
    [id (n)       (if (eq? n s) #t #f)]
  ))

(test (check-bound 'x (num 3)) #f)
(test (check-bound 'x (id 'x)) #t)
(test (check-bound 'x (id 'y)) #f)
(test (check-bound 'x (add (id 'x) (num 3))) #t)
(test (check-bound 'x (add (id 'y) (num 3))) #f)
(test (check-bound 'x (with 'y (num 3) (add (id 'x) (id 'y)))) #t)


; bound-ids: WAE -> list-of-sym
; to find out the list of identifiers which are bound occurences
(define (bound-ids w)
  (type-case WAE w
    [num (n)      '()]
    [add (l r)    (remove-duplicates (sort (append (bound-ids l) (bound-ids r)) symbol<?))]
    [sub (l r)    (remove-duplicates (sort (append (bound-ids l) (bound-ids r)) symbol<?))]
    [with (n e b) (if (check-bound n b) (remove-duplicates (sort (cons n (append (bound-ids e) (bound-ids b))) symbol<?)) (remove-duplicates (sort (append (bound-ids e) (bound-ids b)) symbol<?)))]
    [id (n)       '()]))

(test (bound-ids (with 'x (num 3) (add (id 'y) (num 3)))) '())
(test (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
(test (bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
(test (bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
(test (bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x))
(test (bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x z))
(test (bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
(test (bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))
