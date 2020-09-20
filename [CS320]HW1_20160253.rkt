#lang plai

; Homework#1-1
; dollar->won: number -> number
; to compute the amount of won which is equivalent to the amount of dollar

(define (dollar->won dollar)
  (* 1100 dollar))

(test (dollar->won 5) 5500)
(test (dollar->won 3.14) 3454)
(test (dollar->won 10000) 11000000)


; Homework#1-2
; volume-cuboid: number number number -> number
; to calculate the volume of cuboid with the lengths of three sides
; Assume that all inputs are integer

(define (volume-cuboid width length height)
  (* width length height))

(test (volume-cuboid 3 4 5) 60)
(test (volume-cuboid 1 1 1) 1)
(test (volume-cuboid 7 11 3) 231)


; Homework#1-3
; is-even?: number -> boolean
; to determine the number is even or not
; Assume that the input is integer

(define (is-even? num)
  (= (modulo num 2) 0))

(test (is-even? 3) #f)
(test (is-even? 2) #t)
(test (is-even? 0) #t)
(test (is-even? -2) #t)
(test (is-even? -5) #f)


; Homework#1-4
; gcd: number number -> number
; to compute gcd of two numbers

; -----Assumption-------
; Assume that all inputs are integer
; if (input < 0) -> replace with absolute value
; if (input = 0) -> gcd(0,a)=a

(define (gcd n1 n2)
  (define num1 (abs n1))
  (define num2 (abs n2))
  (cond
    [(and (= num1 0) (= num2 0)) 0]
    [(= num1 0) num2]
    [(= num2 0) num1]
    [else (cond
      [(< num1 num2) (gcd num2 num1)]
      [(= (modulo num1 num2) 0) num2]
      [else (gcd num2 (modulo num1 num2))])]))

(test (gcd 0 0) 0)
(test (gcd 0 5) 5)
(test (gcd 9 24) 3)
(test (gcd 12 -18) 6)
(test (gcd -30 45) 15)
(test (gcd -30 -45) 15)


; Homework#1-5
; lcm: number number -> number
; to compute lcm of two numbers

; ------Assumptions----------
; Same assumption with Homework#1-4(gcd)
; if (gcd(a,b) = 0) -> lcm(a,b) = 0 

(define (lcm num1 num2)
  (cond
    [(= (gcd num1 num2) 0) 0]
    [else (abs (/ (* num1 num2) (gcd num1 num2)))]))

(test (lcm 0 0) 0)
(test (lcm 0 5) 0)
(test (lcm 2 3) 6)
(test (lcm -18 15) 90)
(test (lcm 49 -21) 147)
(test (lcm -1 -3) 3)


; Homework#1-6
; type COURSE: variant is CS320 or CS311 or CS330
(define-type COURSE
  [CS320 (quiz number?)
         (homework number?)]
  [CS311 (homework number?)]
  [CS330 (projects number?)
         (homework number?)])

; making four COURSEs
(define cs1 (CS320 4 10))
(define cs2 (CS311 6))
(define cs3 (CS330 4 8))
(define cs4 (CS330 1 5))

; Homework#1-7
; have-homework: COURSE -> number
; to find out how many homework in COURSE
(define (have-homework c)
  (type-case COURSE c
    [CS320 (q h)  h]
    [CS311 (h)    h]
    [CS330 (p h)  h]))

(test (have-homework cs1) 10)
(test (have-homework cs2) 6)
(test (have-homework cs3) 8)
(test (have-homework cs4) 5)


; Homework#1-8
; have-projects: COURSE -> boolean
; to find out whether the COURSE has more than or equal to two projects or not
(define (have-projects c)
  (type-case COURSE c
    [CS320 (q h)  #f]
    [CS311 (h)    #f]
    [CS330 (p h)  (>= p 2)]))

(test (have-projects cs1) #f)
(test (have-projects cs2) #f)
(test (have-projects cs3) #t)
(test (have-projects cs4) #f)


; Homework#1-9
; change-to-name: symbol -> symbol
; to change one symbol to one symbol
; dog -> happy, cat -> smart, pig -> pinky, else -> not change
(define (change-to-name pet)
  (cond
    [(eq? pet 'dog) 'happy]
    [(eq? pet 'cat) 'smart]
    [(eq? pet 'pig) 'pinky]
    [else pet]))

(test (change-to-name 'dog) 'happy)
(test (change-to-name 'cat) 'smart)
(test (change-to-name 'pig) 'pinky)
(test (change-to-name 'fish) 'fish)


; name-pets: list-of-symbols -> list-of-symbols
; to replace 'dog to 'happy, 'cat to 'smart, and 'pig to 'pinky in list pets
(define (name-pets pets)
  (map change-to-name pets))

(test (name-pets '()) '())
(test (name-pets '(pig)) '(pinky))
(test (name-pets '(fish)) '(fish))
(test (name-pets '(dog cat cat cat)) '(happy smart smart smart))
(test (name-pets '(bird pig cat pig)) '(bird pinky smart pinky))
(test (name-pets '(dog cat pig)) '(happy smart pinky))


; Homework#1-10
; give-name: symbol symbol list-of-symbols -> list-of-symbols
; to replace old to new in list pets
(define (give-name old new pets)
  (map (lambda (pet)
         (cond
           [(eq? pet old) new]
           [else pet]))
       pets))

(test (give-name 'bear 'pooh (cons 'pig (cons 'cat (cons 'bear empty)))) '(pig cat pooh))
(test (give-name 'duck 'donald '()) '())
(test (give-name 'duck 'donald '(duck dog cat)) '(donald dog cat))
(test (give-name 'duck 'donald '(dog cat)) '(dog cat))
(test (give-name 'rabbit 'judy '(rabbit duck dog rabbit rabbit)) '(judy duck dog judy judy))
