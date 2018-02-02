#lang curly-fn hackett/private/kernel

(require hackett/private/util/require
         (only-in racket/base begin begin-for-syntax for-syntax)
         (postfix-in - (combine-in racket/base racket/splicing))

         (for-syntax racket/base
                     racket/match
                     racket/pretty
                     racket/syntax
                     hackett/private/typecheck
                     hackett/private/util/stx)
         syntax/parse/define

         (only-in hackett/private/adt type-constructor-val data-constructor-val)
         (only-in hackett/private/base ~type)
         (only-in hackett/private/class instance)
         hackett/private/prim
         hackett/private/provide)

(begin-for-syntax
  ; τ? -> (listof identifier?) τ?
  (define (unquantify ty)
    (match ty
      [(τ:∀ x t)
       (let-values ([(xs t*) (unquantify t)])
         (values (cons x xs) t*))]
      [t
       (values '() t)]))

  ; (listof τ?) τ? -> (listof τ?)
  (define (data-con-field-types inst-vars con-ty)
    (define-values [xs fn-ty] (unquantify con-ty))
    (unless (equal? (length xs) (length inst-vars))
      (error 'data-con-field-types "unexpected number of quantified variables in constructor"))
    (match-define (τ:->** arg-tys ... (τ:app* (τ:con _) (τ:var con-vars) ...)) fn-ty)
    (unless (equal? (length con-vars) (length inst-vars))
      (raise-arguments-error 'data-con-field-types
                             "inconsistent number of variables given for instantiation"
                             "expected" (length con-vars)
                             "given" (length inst-vars)))
    (define var-subst (map cons con-vars inst-vars))
    (map #{insts % var-subst} arg-tys)))

(define-syntax-parser derive-instance/Show
  [(_ {~type ty-con:type-constructor-val})
   #:with [data-con:data-constructor-val ...] (attribute ty-con.data-constructors)
   #:with [ty-con-var-id ...] (build-list (attribute ty-con.arity) generate-temporary)
   #:do [(define ty-con-vars (map τ:var (attribute ty-con-var-id)))
         (define data-con-tys
           (map #{data-con-field-types ty-con-vars %}
                (attribute data-con.type)))
         (pretty-print (attribute ty-con.local-value))
         (pretty-print (attribute data-con.type))
         (pretty-print data-con-tys)]
   #:with [[data-con-ty-expr-binding ...] ...] (map generate-temporaries data-con-tys)
   #:with [[data-con-ty-expr ...] ...] (map #{map preservable-property->expression %} data-con-tys)
   (print
    #'(splicing-let-syntax- ([data-con-ty-expr-binding data-con-ty-expr] ... ...)
        (instance (forall [ty-con-var-id ...] (Show data-con-ty-expr-binding) ... ...
                          => (Show (ty-con ty-con-var-id ...)))
          [show undefined!])))
   (syntax-property
    #'(splicing-let-syntax- ([data-con-ty-expr-binding
                              (make-type-variable-transformer data-con-ty-expr)]
                             ... ...)
        (instance (forall [ty-con-var-id ...] (Show data-con-ty-expr-binding) ... ...
                          => (Show (ty-con ty-con-var-id ...)))
          [show (λ (x) "")]))
    'disappeared-use
    (syntax-local-introduce #'ty-con))])

(data (Foo a) (Bar a) (Baz Integer))
(derive-instance/Show Foo)

(main (print (show (Bar 42))))
