#lang plai-typed

;;============DEFINE-TYPE==================
;;EXPR
(define-type EXPR
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR) (rhs : EXPR)]
  [sub (lhs : EXPR) (rhs : EXPR)]
  [equ (lhs : EXPR) (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : EXPR)]
  [app (fun-expr : EXPR) (arg-expr : EXPR)]
  [ifthenelse (test-expr : EXPR) (then-expr : EXPR) (else-expr : EXPR)]
  [rec (name : symbol) (ty : TE) (named-expr : EXPR) (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)]
  [tfun (name : symbol) (expr : EXPR)]
  [tapp (body : EXPR) (type : TE)])

;;TE
(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [idTE (name : symbol)]
  [tvTE (name : symbol)])

;;Type
(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)]
  [idT (name : symbol)]
  [tvT (name : symbol)])

;; EXPR-Value
(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : EXPR) (ds : DefrdSub)]
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])

;;DefrdSub
(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : EXPR-Value) (ds : DefrdSub)]
  [aRecSub (name : symbol) (value-box : (boxof EXPR-Value)) (ds : DefrdSub)])

;;TypeEnv
(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol) (type : Type) (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)]
  [pBind (name : Type) (rest : TypeEnv)])
;;==================END OF DEFINE-TYPE===========================

;;==================HELPER FUNCTIONS============================= 
;; num-op : (number number -> number) -> (EXPR-Value EXPR-Value -> EXPR-Value)
; Anonymous func for making num+, num-
(define num-op : ((number number -> number) '_a -> (EXPR-Value EXPR-Value -> EXPR-Value))
  (lambda (op op-name)
    (lambda (x y)
      (numV (op (numV-n x) (numV-n y))))))
;; numV+, numV- : numV numV -> numV
;; Helper funcs to interpret add, sub of EXPR
(define numV+ : (EXPR-Value EXPR-Value -> EXPR-Value)
  (num-op + '+))
(define numV- : (EXPR-Value EXPR-Value -> EXPR-Value)
  (num-op - '-))
;; numV= : numV numV -> boolV
;; Helper func to interpret equ of EXPR
(define numV= : (EXPR-Value EXPR-Value -> EXPR-Value)
  (lambda (x y)
    (boolV (= (numV-n x) (numV-n y)))
))
;(test (numV+ (numV 3) (numV 2)) (numV 5))
;(test (numV- (numV 3) (numV 2)) (numV 1))
;(test (numV= (numV 1) (numV 2)) (boolV #f))
;(test (numV= (numV 1) (numV 1)) (boolV #t))


;; lookup: symbol DefrdSub -> EXPR-Value
;; To find out the value of symbol in DefrdSub
(define lookup : (symbol DefrdSub -> EXPR-Value)
  (lambda (name ds)
    (type-case DefrdSub ds
      [mtSub () (error 'lookup "free variable")]
      [aSub  (sub-name val rest-ds)
             (if (symbol=? sub-name name)
                 val
                 (lookup name rest-ds))]
      [aRecSub (sub-name val-box rest-ds)
               (if (symbol=? sub-name name)
                   (unbox val-box)
                   (lookup name rest-ds))])))
;(test/exn (lookup 'x (aSub 'y (numV 3) (mtSub))) "free variable")
;(test (lookup 'x (aSub 'x (numV 3) (mtSub))) (numV 3))


;; get-type: symbol TypeEnv -> Type
;; To find out the type of symbol in TypeEnv
(define get-type : (symbol TypeEnv -> Type)
  (lambda (name-to-find env)
    (type-case TypeEnv env
      [mtEnv () (error 'get-type "free variable, so no type")]
      [aBind (name ty rest)
             (if (symbol=? name-to-find name)
                 ty
                 (get-type name-to-find rest))]
      [tBind (name var1-name var1-ty var2-name var2-ty rest)
             (get-type name-to-find rest)]
      [pBind (name rest)
             (get-type name-to-find rest)])))
;(test/exn (get-type 'x (mtEnv)) "free variable, so no type")
;(test (get-type 'x (aBind 'x (numT) (mtEnv))) (numT))
;(test (get-type 'x (tBind 'fruit 'apple (numT) 'banana (numT) (aBind 'x (numT) (mtEnv)))) (numT))


;; find-type-id: symbol TypeEnv -> TypeEnv
;; To find a type environment that the first element is type id or 'alpha
(define find-type-id : (symbol TypeEnv -> TypeEnv)
  (lambda (name-to-find env)
    (type-case TypeEnv env
      [mtEnv () (error 'find-type-id "free type name, so no type")]
      [aBind (name ty rest)
             (if (symbol=? name-to-find name)
                 env
                 (find-type-id name-to-find rest))]
      [tBind (name var1-name var1-ty var2-name var2-ty rest)
             (if (symbol=? name-to-find name)
                 env
                 (find-type-id name-to-find rest))]
      [pBind (name rest)
             (if (symbol=? name-to-find (tvT-name name))
                 env
                 (find-type-id name-to-find rest))])))

;(test/exn (find-type-id 'x (mtEnv)) "free type name, so no type")
;(test (find-type-id 'fruit (aBind 'x (numT) (tBind 'fruit 'apple (numT) 'banana (numT) (mtEnv)))) (tBind 'fruit 'apple (numT) 'banana (numT) (mtEnv)))
;(test (find-type-id 'fruit (tBind 'fruit 'apple (numT) 'banana (numT) (aBind 'x (numT) (mtEnv)))) (tBind 'fruit 'apple (numT) 'banana (numT) (aBind 'x (numT) (mtEnv))))


;; parse-type: TE -> Type
;; To convert TE to Type
(define parse-type : (TE -> Type)
  (lambda (te)
    (type-case TE te
      [numTE () (numT)]
      [boolTE () (boolT)]
      [arrowTE (param result)
               (arrowT (parse-type param) (parse-type result))]
      [polyTE (forall body)
              (polyT forall (parse-type body))]
      [idTE (id) (idT id)]
      [tvTE (tv) (tvT tv)])))
;(test (parse-type (numTE)) (numT))
;(test (parse-type (boolTE)) (boolT))
;(test (parse-type (arrowTE (numTE) (boolTE))) (arrowT (numT) (boolT)))
;(test (parse-type (polyTE 'x (numTE))) (polyT 'x (numT)))
;(test (parse-type (idTE 'x)) (idT 'x))
;(test (parse-type (tvTE 'x)) (tvT 'x))


;; validpolyT: (listof symbol) Type -> boolean
;; To check whether the polyT satisfy well-formedness or not
(define validpolyT : ((listof symbol) Type -> boolean)
  (lambda (syms body)
    (type-case Type body
      [numT () #t]
      [boolT () #t]
      [arrowT (param result) (and (validpolyT syms param)
                                  (validpolyT syms result))]
      [polyT (forall1 body1) (validpolyT (append syms (list forall1)) body1)]
      [idT (id) (member id syms)]
      [tvT (tv) (member tv syms)])))


;; validtype: Type TypeEnv -> TypeEnv
;; To check the Well-Formedness of type
(define validtype : (Type TypeEnv -> TypeEnv)
  (lambda (ty env)
    (type-case Type ty
      [numT () (mtEnv)]
      [boolT () (mtEnv)]
      [arrowT (param result) (begin (validtype param env)
                                    (validtype result env))]
      [polyT (forall body) (if (validpolyT (list forall) body)
                               env
                               (error 'validtype "free"))]
      [idT (id) (find-type-id id env)]
      [tvT (tv) (find-type-id tv env)])))

;; replace-alpha: symbol Type Type -> Type
;; To replace symbol of tfunction body with fixed type
(define replace-alpha : (symbol Type Type -> Type)
  (lambda (name body tau)
    (type-case Type body
      [numT () (numT)]
      [boolT () (boolT)]
      [arrowT (param result) (arrowT (replace-alpha name param tau) (replace-alpha name result tau))]
      [polyT (forall body) (polyT forall body)]
      [idT (id) body]
      [tvT (tv) (if (symbol=? tv name)
                    tau
                    body)])))


;; index-of: (listof symbol) symbol number -> number
;; To compute the index of symbol in list
(define index-of : ((listof symbol) symbol number -> number)
  (lambda (syms name numth)
     (cond
       [(empty? syms) -1]
       [else (if (symbol=? (first syms) name)
                 numth
                 (index-of (rest syms) name (+ 1 numth)))])))
;(test (index-of (list 'a 'b 'c) 'a 0) 0)
;(test (index-of (list 'a 'b 'c) 'c 0) 2)
;(test (index-of (list 'a 'b 'c) 'd 0) -1)

;; equal-type?: Type Type (listof symbol) (listof symbole) -> boolean
;; To check the two type is same or not, in this case alpha==beta if they are in the same location
(define equal-type? : (Type Type (listof symbol) (listof symbol) -> boolean)
  (lambda (ty1 ty2 syms1 syms2)
    (type-case Type ty1
      [numT () (type-case Type ty2
                 [numT () #t]
                 [else #f])]
      [boolT () (type-case Type ty2
                  [boolT () #t]
                  [else #f])]
      [arrowT (pa1 re1)
              (type-case Type ty2
                [arrowT (pa2 re2)
                        (and (equal-type? pa1 pa2 syms1 syms2)
                             (equal-type? re1 re2 syms1 syms2))]
                [else #f])]
      [polyT (all1 body1)
             (type-case Type ty2
               [polyT (all2 body2)
                      (equal-type? body1 body2 (cons all1 syms1) (cons all2 syms2))]
               [else #f])]
      [idT (id1) (type-case Type ty2
                   [idT (id2) (symbol=? id1 id2)]
                   [else #f])]
      [tvT (tv1) (type-case Type ty2
                   [tvT (tv2) (= (index-of syms1 tv1 0) (index-of syms2 tv2 0))]
                   [else #f])])))


;;=================END OF HELPER FUNCTIONS===================
;; interp: EXPR DefrdSub -> EXPR-Value
;; To interpret EXPR to EXPR-Value under DefrdSub
(define interp : (EXPR DefrdSub -> EXPR-Value)
  (lambda (expr ds)
    (type-case EXPR expr
      [num (n) (numV n)]
      [bool (b) (boolV b)]
      [add (l r) (numV+ (interp l ds) (interp r ds))]
      [sub (l r) (numV- (interp l ds) (interp r ds))]
      [equ (l r) (numV= (interp l ds) (interp r ds))]
      [id (s) (lookup s ds)]
      [fun (x ty b) (closureV x b ds)]
      [app (f a) (local [(define f-val (interp f ds))
                         (define a-val (interp a ds))]
                   (type-case EXPR-Value f-val
                     [closureV (param body rest)
                               (interp body (aSub param a-val rest))]
                     [constructorV (right?)
                                   (variantV right? a-val)]
                     [else (error 'interp "not applicable")]))]
      [ifthenelse (test-expr then-expr else-expr)
                  (if (boolV-b (interp test-expr ds))
                      (interp then-expr ds)
                      (interp else-expr ds))]
      [rec (bound-id ty named-expr body-expr)
             (local [(define value-holder (box (numV 42)))
                     (define new-ds
                             (aRecSub bound-id value-holder ds))]
               (begin
                 (set-box! value-holder (interp named-expr new-ds))
                 (interp body-expr new-ds)))]
      [with-type (type-name var1-name var1-te
                            var2-name var2-te
                            body-expr)
                 (interp body-expr
                         (aSub var1-name (constructorV false)
                               (aSub var2-name (constructorV true) ds)))]
      [cases (ty dispatch-expr
                 var1-name var1-id var1-rhs
                 var2-name var2-id var2-rhs)
             (type-case EXPR-Value (interp dispatch-expr ds)
               [variantV (right? val)
                         (if (not right?)
                             (interp var1-rhs (aSub var1-id val ds))
                             (interp var2-rhs (aSub var2-id val ds)))]
               [else (error 'interp "not a variant result")])]
      [tfun (tname texpr)
            (interp texpr ds)]
      [tapp (texpr ttype)
            (interp texpr ds)])
  )
)
;(test (interp (num 3) (mtSub)) (numV 3))
;(test (interp (bool #f) (mtSub)) (boolV #f))
;(test (interp (add (num 3) (num 2)) (mtSub)) (numV 5))
;(test (interp (sub (num 3) (num 2)) (mtSub)) (numV 1))
;(test (interp (equ (num 2) (num 2)) (mtSub)) (boolV #t))
;(test (interp (id 'x) (aSub 'x (numV 3) (mtSub))) (numV 3))
;(test (interp (fun 'x (numTE) (id 'x)) (mtSub)) (closureV 'x (id 'x) (mtSub))) 



;; typecheck: EXPR TypeEnv -> Type
;; To check the type is valid or not
(define typecheck : (EXPR TypeEnv -> Type)
  (lambda (expr env)
    (type-case EXPR expr
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (error 'typecheck "Addition with non-number")])]
             [else (error 'typecheck "Addition with non-number")])]
      [sub (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (error 'typecheck "Substraction with non-number")])]
             [else (error 'typecheck "Substraction with non-number")])]
      [equ (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (boolT)]
                     [else (error 'typecheck "Equality with non-number")])]
             [else (error 'typecheck "Equality with non-number")])]
      [id (name) (get-type name env)]
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (begin
               (validtype param-type env)
               (arrowT param-type
                       (typecheck body (aBind name param-type env)))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                     (type-case Type param-type
                       [tvT (tv) (typecheck arg env)]
                       [else (if (equal-type? param-type
                                             (typecheck arg env) empty empty)
                                 result-type   
                                 (error 'typecheck "Type of parameter and argument are different"))])]
             [else (error 'typecheck "fn in function application is not a function")])]
      [ifthenelse (test-expr then-expr else-expr)
                  (type-case Type (typecheck test-expr env)
                    [boolT () (local [(define test-ty (typecheck then-expr env))]
                                (if (equal-type? test-ty (typecheck else-expr env) empty empty)
                                    test-ty
                                    (error 'typecheck "Two branches have different type")))]
                    [else (error 'typecheck "Test expression of ifthenelse is not a boolean")])]
      [rec (name ty rhs-expr body-expr)
           (local [(define rhs-ty (parse-type ty))
                   (define new-env (aBind name rhs-ty env))]
             (if (equal? rhs-ty (typecheck rhs-expr new-env))
                 (typecheck body-expr new-env)
                 (error 'typecheck "Programmer wrote wrong type")))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
                (local [(define var1-ty (parse-type var1-te))
                        (define var2-ty (parse-type var2-te))
                        (define new-env (tBind type-name
                                               var1-name var1-ty
                                               var2-name var2-ty env))]
                  (begin
                    (validtype var1-ty new-env)
                    (validtype var2-ty new-env)
                    (typecheck body-expr
                               (aBind var1-name
                                      (arrowT var1-ty
                                              (idT type-name))
                                      (aBind var2-name
                                             (arrowT var2-ty
                                                     (idT type-name))
                                             new-env)))))]
      [cases (type-name dispatch-expr var1-name var1-id var1-rhs
                                      var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck dispatch-expr env)
                [idT (name)
                     (if (equal? name type-name)
                         (local [(define rhs1-ty
                                   (typecheck var1-rhs
                                              (aBind var1-id (tBind-var1-type bind) env)))
                                 (define rhs2-ty
                                   (typecheck var2-rhs
                                              (aBind var2-id (tBind-var2-type bind) env)))]
                           (if (equal? rhs1-ty rhs2-ty)
                               rhs1-ty
                               (error 'typecheck "Two branches have different types")))
                         (error 'typecheck "The type of idT and type-name don't match"))]
                [else (error 'typecheck "In cases there is no idT in dipatch-expr")])
              (error 'typecheck "matching variant names")))]
      [tfun (tname texpr)
            (polyT tname
                   (typecheck texpr (pBind (tvT tname) env)))]
      [tapp (texpr ttype)
            (local [(define param-ttype (parse-type ttype))]
              (begin (validtype param-ttype env)
                     (type-case Type (typecheck texpr env)
                       [polyT (tfun-name tfun-body)
                              (replace-alpha tfun-name tfun-body param-ttype)]
                       [else (error 'typecheck "The function in tapp is not tfun")])))])
                                      
   )
)
;(test (typecheck (num 3) (mtEnv)) (numT))
;(test (typecheck (bool true) (mtEnv)) (boolT))
;(test (typecheck (add (num 3) (num 2)) (mtEnv)) (numT))
;(test/exn (typecheck (add (num 3) (bool true)) (mtEnv)) "Addition with non-number")
;(test (typecheck (sub (num 3) (num 2)) (mtEnv)) (numT))
;(test/exn (typecheck (sub (num 3) (bool true)) (mtEnv)) "Substraction with non-number")
;(test (typecheck (equ (num 3) (num 2)) (mtEnv)) (boolT))
;(test/exn (typecheck (equ (num 3) (bool true)) (mtEnv)) "Equality with non-number")
;(test (typecheck (id 'x) (aBind 'x (numT) (mtEnv))) (numT))
;(test/exn (typecheck (id 'x) (mtEnv)) "free variable")



;;;;;; test cases in hompage
#|(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'alpha (tvT 'alpha))) (mtEnv)))
      (polyT 'alpha (tvT 'alpha)))
      
(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (numTE))
              (mtSub))
      (closureV 'x (id 'x) (mtSub)))
      
(test (typecheck
       (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
             (polyTE 'beta (arrowTE (tvTE 'beta) (tvTE 'beta))))
       (mtEnv))
      (arrowT (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))
              (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))))
              
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (interp (tfun 'alpha (tfun 'beta (num 3))) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
      
(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (interp (app
               (tapp (ifthenelse (bool true)
                                 (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                                 (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))))
                     (numTE)) (num 30)) (mtSub))
      (numV 30))
      
(test (interp
       (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                 (app (tapp (id 'x) (numTE)) (num 10)))
        (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))) (mtSub)) (numV 10))
        
(test (typecheck
       (tfun 'alpha
             (fun 'alpha (arrowTE (numTE) (numTE))
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (polyT 'alpha (arrowT (arrowT (numT) (numT)) (arrowT (tvT 'alpha) (tvT 'alpha)))))
      
(test (typecheck
       (fun 'alpha (arrowTE (numTE) (numTE))
            (tfun 'alpha
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (arrowT (arrowT (numT) (numT)) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))

(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (typecheck (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtEnv)) (arrowT (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtEnv)) (arrowT (numT) (numT)))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'beta)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))
(test (typecheck (ifthenelse (equ (num 8) (num 10))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (fun 'y (tvTE 'beta) (id 'y)))))
                             (tfun 'beta (tfun 'alpha (fun 'x (tvTE 'beta) (fun 'y (tvTE 'alpha) (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (arrowT (tvT 'beta) (tvT 'beta))))))

(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (arrowTE (numTE) (numTE)))
          (mtEnv)) (arrowT (arrowT (numT) (numT)) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'alpha
                                                                                        (fun 'alpha (tvTE 'alpha)
                                                                                             (id 'alpha)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))


(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (num 42)) (id 'f)) (aBind 'f (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))) (mtEnv))) (numT))

;;; tests on noah 234th article
(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv))
      (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

;;; tests on noah 236th article
(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv))
      (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtEnv)) (numT))
(test (interp (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtSub)) (numV 10)) |#
