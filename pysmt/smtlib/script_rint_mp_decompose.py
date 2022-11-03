
rint_prologue = '''
(define-fun ri.r_dn ((p Int) (v Real)) Real
  (let ((w (- v (/ (abs v) (ri.err_denom p)) (ri.err_min p))))
    (ite (>= w (- (ri.max_value p))) w
      (- ri.large_value) ))
)

(define-fun ri.r_up ((p Int) (v Real)) Real
  (let ((w (+ v (/ (abs v) (ri.err_denom p)) (ri.err_min p))))
    (ite (<= w (ri.max_value p)) w
      ri.large_value ))
)

(define-fun is_ninf ( (p Int) (l Real) ) Bool (< l (- (ri.max_value p))))
(define-fun is_pinf ( (p Int) (u Real) ) Bool (> u (ri.max_value p)))
(define-fun p_nan ( (p_nan Bool) ) Bool p_nan)

(define-const ri.zero Real 0.0)
(define-const ri.zero.l Real 0.0)
(define-const ri.zero.u Real 0.0)
(define-const ri.zero.p_nan Bool false)

(define-const ri.zero_nan Real 0.0)
(define-const ri.zero_nan.l Real 0.0)
(define-const ri.zero_nan.u Real 0.0)
(define-const ri.zero_nan.p_nan Bool true)

(define-fun ri.pinf.l ((p Int)) Real ri.large_value)
(define-fun ri.pinf.u ((p Int)) Real ri.large_value)
(define-fun ri.pinf.p_nan ((p Int)) Bool false)

(define-fun ri.ninf.l ((p Int)) Real (- ri.large_value))
(define-fun ri.ninf.u ((p Int)) Real (- ri.large_value))
(define-fun ri.ninf.p_nan ((p Int)) Bool false)

(define-const ri.ninf_nan Real (- ri.large_value))
(define-const ri.ninf_nan.l Real (- ri.large_value))
(define-const ri.ninf_nan.u Real (- ri.large_value))
(define-const ri.ninf_nan.p_nan Bool true)

(define-fun ri.entire.l ((p Int)) Real (- ri.large_value))
(define-fun ri.entire.u ((p Int)) Real ri.large_value)
(define-fun ri.entire.p_nan ((p Int)) Bool true)

(define-fun ri_to_ri.l ((p Int) (l Real)) Real (ri.r_dn p l))
(define-fun ri_to_ri.u ((p Int) (u Real)) Real (ri.r_up p u))
(define-fun ri_to_ri.p_nan ((p_nan Bool)) Bool p_nan)

(define-fun real_to_ri.l ((p Int) (v Real)) Real (ri.r_dn p v))
(define-fun real_to_ri.u ((p Int) (v Real)) Real (ri.r_up p v))
(define-fun real_to_ri.p_nan ((v Real)) Bool false)

(define-fun ri.exact.l ((v Real)) Real v)
(define-fun ri.exact.u ((v Real)) Real v)
(define-fun ri.exact.p_nan ((v Real)) Bool false)

;; abs

(define-fun ri.abs.l ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (ite (>= x.l 0.0) x.l (ite (>= x.u 0.0) 0.0 (- x.u))) )

(define-fun ri.abs.u ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (ite (>= x.u (- x.l)) x.u (- x.l)) )

(define-fun ri.abs.p_nan ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  x.p_nan )

;; neg

(define-fun ri.neg.l ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (- x.u) )

(define-fun ri.neg.u ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (- x.l) )

(define-fun ri.neg.p_nan ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  x.p_nan )

;; add

(define-fun ri.add.l ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_dn p (+ x.l y.l)) )

(define-fun ri.add.u ( (p Int)
                       (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_up p (+ x.u y.u)) )

(define-fun ri.add.p_nan ( (p Int) 
                            (x.l Real) (x.u Real) (x.p_nan Bool) 
                            (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or x.p_nan y.p_nan
      (and (is_ninf p x.l) (is_pinf p y.u)) 
      (and (is_pinf p x.u) (is_ninf p y.l)) ) )

;; sub

(define-fun ri.sub.l ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_dn p (- x.l y.u)) ) 

(define-fun ri.sub.u ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_up p (- x.u y.l)) )

(define-fun ri.sub.p_nan ( (p Int) 
                            (x.l Real) (x.u Real) (x.p_nan Bool) 
                            (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or x.p_nan y.p_nan 
      (and (is_ninf p x.l) (is_ninf p y.u))
      (and (is_pinf p x.u) (is_pinf p y.l)) ) ) 

;; sub_exact

(define-fun ri.sub_exact.l ( (p Int) 
                             (x.l Real) (x.u Real) (x.p_nan Bool)
                             (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (- x.l y.u) ) 

(define-fun ri.sub_exact.u ( (p Int) 
                             (x.l Real) (x.u Real) (x.p_nan Bool) 
                             (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (- x.u y.l) ) 

(define-fun ri.sub_exact.p_nan ( (p Int) 
                                  (x.l Real) (x.u Real) (x.p_nan Bool)
                                  (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or x.p_nan y.p_nan
      (and (is_ninf p x.l) (is_ninf p y.u))
      (and (is_pinf p x.u) (is_pinf p y.l)) ) ) 

;; mul

(define-fun ri.mul.l ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (>= x.l 0.0)
    (ite (= x.u 0.0)
      ;(ite (and (not (is_ninf p y.l)) (not (is_pinf p y.u)) (not x.p_nan) (not y.p_nan))
      ;  ;; [x] = [0.0]
      ;  ri.zero.l

      ;  ;; [x] = [0.0] and (-inf = [y] or [y] = +inf)
      ;  ri.nai.l )
      ri.zero.l

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_pinf p x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; 0.0 <= [x] and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( (l (ri.r_dn p (* x.l y.l)))
                 ;(u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                 ;        (ri.r_up p (* x.u y.u)) ))
                 )
            l
            ) )

        (ite (<= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( (l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
                         (ri.r_dn p (* x.u y.l)) ))
                 ;(u (ri.r_up p (* x.l y.u)))
                 )
            l
            ) 

          ;;  0.0 <= [x] and [x] != [0.0] and [y] strictly contains 0.0
          (let ( (l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value) 
                         (ri.r_dn p (* x.u y.l)) ))
                 ;(u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                 ;        (ri.r_up p (* x.u y.u)) ))
                 )
            l
            ) ) ) )

    (ite (<= x.u 0.0)
      (ite (>= y.l 0.0)
        (ite (and (not (is_pinf p y.u)) (= y.u 0.0))
          ;; [x] <= 0.0 and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_ninf p x.l)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] <= 0.0 and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( (l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                         (ri.r_dn p (* x.l y.u)) ))
                 ;(u (ri.r_up p (* x.u y.l))) 
                 )
            l
            ))

        (ite (<= y.u 0.0)
          ;; [x] <= 0.0 and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( (l (ri.r_dn p (* x.u y.u)))
                 ;(u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                 ;        (ri.r_up p (* x.l y.l)) ))
                 )
            l
            ) 

          ;; [x] <= 0.0 and [x] != [0.0] and [y] strictly contains 0.0
          (let ( (l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                         (ri.r_dn p (* x.l y.u)) ))
                 ;(u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                 ;        (ri.r_up p (* x.l y.l)) ))
                 )
            l
            ) ) )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] = [0.0]
          ;(ite (and (not (is_ninf p x.l)) (not (is_pinf p x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] strictly contains 0.0 and 0.0 <= [y]
          (let ( (l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                         (ri.r_dn p (* x.l y.u)) ))
                 ;(u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                 ;        (ri.r_up p (* x.u y.u)) ))
                 )
            l
            ) )

        (ite (<= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] <= 0.0
          (let ( (l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
                         (ri.r_dn p (* x.u y.l)) ))
                 ;(u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                 ;        (ri.r_up p (* x.l y.l)) ))
                 )
            l
            )

          ;; [x] and [y] strictly contains 0.0
          (let ( (l1 (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                          (ri.r_dn p (* x.l y.u)) ))
                 (l2 (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
                          (ri.r_dn p (* x.u y.l)) ))
                 ;(u1 (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                 ;         (ri.r_up p (* x.l y.l)) ))
                 ;(u2 (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                 ;         (ri.r_up p (* x.u y.u)) ))
                 )
          (ite (< l1 l2) 
            ;(ite (> u1 u2)
            ;  ;; l1 and u1
            ;  l1

            ;  ;; l1 and u2
            ;  l1
            ;  ) 
            l1

            ;(ite (> u1 u2)
            ;  ;; l2 and u1
            ;  l2

            ;  ;; l2 and u2
            ;  l2
            ;  ) 
            l2 ) ) ) ) ) ) )

(define-fun ri.mul.u ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (>= x.l 0.0)
    (ite (= x.u 0.0)
      ;(ite (and (not (is_ninf p y.l)) (not (is_pinf p y.u)) (not x.p_nan) (not y.p_nan))
      ;  ;; [x] = [0.0]
      ;  ri.zero.l

      ;  ;; [x] = [0.0] and (-inf = [y] or [y] = +inf)
      ;  ri.nai.l )
      ri.zero.l

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_pinf p x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; 0.0 <= [x] and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( ;(l (ri.r_dn p (* x.l y.l)))
                 (u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                         (ri.r_up p (* x.u y.u)) )))
            u
            ) )

        (ite (<= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( ;(l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
                 ;        (ri.r_dn p (* x.u y.l)) ))
                 (u (ri.r_up p (* x.l y.u))) )
            u 
            ) 

          ;;  0.0 <= [x] and [x] != [0.0] and [y] strictly contains 0.0
          (let ( ;(l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value) 
                 ;        (ri.r_dn p (* x.u y.l)) ))
                 (u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                         (ri.r_up p (* x.u y.u)) )))
            u
            ) ) ) )

    (ite (<= x.u 0.0)
      (ite (>= y.l 0.0)
        (ite (and (not (is_pinf p y.u)) (= y.u 0.0))
          ;; [x] <= 0.0 and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_ninf p x.l)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] <= 0.0 and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( ;(l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                 ;        (ri.r_dn p (* x.l y.u)) ))
                 (u (ri.r_up p (* x.u y.l))) )
            u
            ))

        (ite (<= y.u 0.0)
          ;; [x] <= 0.0 and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( ;(l (ri.r_dn p (* x.u y.u)))
                 (u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                         (ri.r_up p (* x.l y.l)) )))
            u
            ) 

          ;; [x] <= 0.0 and [x] != [0.0] and [y] strictly contains 0.0
          (let ( ;(l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                 ;        (ri.r_dn p (* x.l y.u)) ))
                 (u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                         (ri.r_up p (* x.l y.l)) )))
            u
            ) ) )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] = [0.0]
          ;(ite (and (not (is_ninf p x.l)) (not (is_pinf p x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] strictly contains 0.0 and 0.0 <= [y]
          (let ( ;(l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                 ;        (ri.r_dn p (* x.l y.u)) ))
                 (u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                         (ri.r_up p (* x.u y.u)) )))
            u
            ) )

        (ite (<= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] <= 0.0
          (let ( ;(l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
                 ;        (ri.r_dn p (* x.u y.l)) ))
                 (u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                         (ri.r_up p (* x.l y.l)) )))
            u
            )

          ;; [x] and [y] strictly contains 0.0
          (let ( (l1 (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
                          (ri.r_dn p (* x.l y.u)) ))
                 (l2 (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
                          (ri.r_dn p (* x.u y.l)) ))
                 (u1 (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
                          (ri.r_up p (* x.l y.l)) ))
                 (u2 (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
                          (ri.r_up p (* x.u y.u)) )))
          (ite (< l1 l2) 
            (ite (> u1 u2)
              ;; l1 and u1
              u1

              ;; l1 and u2
              u2
              ) 

            (ite (> u1 u2)
              ;; l2 and u1
              u1

              ;; l2 and u2
              u2
              ) ) ) ) ) ) ) )

(define-fun ri.mul.p_nan ( (p Int) 
                            (x.l Real) (x.u Real) (x.p_nan Bool)
                            (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ite (>= x.l 0.0)
    (ite (= x.u 0.0)
      (ite (and (not (is_ninf p y.l)) (not (is_pinf p y.u)) (not x.p_nan) (not y.p_nan))
        ;; [x] = [0.0]
        false

        ;; [x] = [0.0] and (-inf = [y] or [y] = +inf)
        true
        )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] = [0.0]
          (ite (and (not (is_pinf p x.u)) (not x.p_nan) (not y.p_nan))
            false
            true
            )

          ;; 0.0 <= [x] and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          ;(let ( (l (ri.r_dn p (* x.l y.l)))
          ;       (*u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
          ;               (ri.r_up p (* x.u y.u)) )*))
          ;  l
          ;  )
          false
          )

        ;(ite (<= y.u 0.0)
        ;  ;; 0.0 <= [x] and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
        ;  (let ( (l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
        ;                 (ri.r_dn p (* x.u y.l)) ))
        ;         (*u (ri.r_up p (* x.l y.u))*) )
        ;    l
        ;    ) 

        ;  ;;  0.0 <= [x] and [x] != [0.0] and [y] strictly contains 0.0
        ;  (let ( (l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value) 
        ;                 (ri.r_dn p (* x.u y.l)) ))
        ;         (*u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
        ;                 (ri.r_up p (* x.u y.u)) )*))
        ;    l
        ;    ) 
        ;  )
        false
        ) )

    (ite (<= x.u 0.0)
      (ite (>= y.l 0.0)
        (ite (and (not (is_pinf p y.u)) (= y.u 0.0))
          ;; [x] <= 0.0 and [x] != [0.0] and [y] = [0.0]
          (ite (and (not (is_ninf p x.l)) (not x.p_nan) (not y.p_nan))
            false
            true
            )

          ;; [x] <= 0.0 and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          ;(let ( (l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
          ;               (ri.r_dn p (* x.l y.u)) ))
          ;       (*u (ri.r_up p (* x.u y.l))*) )
          ;  l
          ;  )
          false
          )

        ;(ite (<= y.u 0.0)
        ;  ;; [x] <= 0.0 and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
        ;  (let ( (l (ri.r_dn p (* x.u y.u)))
        ;         (*u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
        ;                 (ri.r_up p (* x.l y.l)) )*))
        ;    l
        ;    ) 

        ;  ;; [x] <= 0.0 and [x] != [0.0] and [y] strictly contains 0.0
        ;  (let ( (l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
        ;                 (ri.r_dn p (* x.l y.u)) ))
        ;         (*u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
        ;                 (ri.r_up p (* x.l y.l)) )*))
        ;    l
        ;    ) ) 
        false
        )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] = [0.0]
          (ite (and (not (is_ninf p x.l)) (not (is_pinf p x.u)) (not x.p_nan) (not y.p_nan))
            false
            true )

          ;; [x] strictly contains 0.0 and 0.0 <= [y]
          ;(let ( (l (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
          ;               (ri.r_dn p (* x.l y.u)) ))
          ;       (*u (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
          ;               (ri.r_up p (* x.u y.u)) )*))
          ;  l
          ;  ) 
          false
          )

        ;(ite (<= y.u 0.0)
        ;  ;; [x] strictly contains 0.0 and [y] <= 0.0
        ;  (let ( (l (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
        ;                 (ri.r_dn p (* x.u y.l)) ))
        ;         (*u (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
        ;                 (ri.r_up p (* x.l y.l)) )*))
        ;    l
        ;    )

        ;  ;; [x] and [y] strictly contains 0.0
        ;  (let ( (l1 (ite (or (is_ninf p x.l) (is_pinf p y.u)) (- ri.large_value)
        ;                  (ri.r_dn p (* x.l y.u)) ))
        ;         (l2 (ite (or (is_pinf p x.u) (is_ninf p y.l)) (- ri.large_value)
        ;                  (ri.r_dn p (* x.u y.l)) ))
        ;         (*u1 (ite (or (is_ninf p x.l) (is_ninf p y.l)) ri.large_value
        ;                  (ri.r_up p (* x.l y.l)) )*)
        ;         (*u2 (ite (or (is_pinf p x.u) (is_pinf p y.u)) ri.large_value
        ;                  (ri.r_up p (* x.u y.u)) )*))
        ;  (ite (< l1 l2) 
        ;    (ite (> u1 u2)
        ;      ;; l1 and u1
        ;      l1

        ;      ;; l1 and u2
        ;      l1
        ;      ) 

        ;    (ite (> u1 u2)
        ;      ;; l2 and u1
        ;      l2

        ;      ;; l2 and u2
        ;      l2
        ;      ) ) ) ) 
        false
        ) ) ) )

;; div

(define-fun ri.div.l ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (> y.l 0.0)
    (ite (>= x.l 0.0)
      ;; 0.0 <= [x] and 0.0 < [y]
      (let ( (l (ite (is_pinf p y.u) 0.0 (ri.r_dn p (/ x.l y.u)))) 
             ;(u (ite (is_pinf p x.u) ri.large_value (ri.r_up p (/ x.u y.l)))) 
             )
        l
        )

      (ite (<= x.u 0.0)
        ;; [x] <= 0.0 and 0.0 < [y]
        (let ( (l (ite (is_ninf p x.l) (- ri.large_value) (ri.r_dn p (/ x.l y.l)))) 
               ;(u (ite (is_pinf p y.u) 0.0 (ri.r_up p (/ x.u y.u)))) 
               )
          l
          )

        ;; [x] is NaN or strictly contains 0.0 and 0.0 < [y]
        (let ( (l (ite (is_ninf p x.l) (- ri.large_value) (ri.r_dn p (/ x.l y.l)))) 
               ;(u (ite (is_pinf p x.u) ri.large_value (ri.r_up p (/ x.u y.l)))) 
               )
          l
          )))

    (ite (< y.u 0.0)
      (ite (>= x.l 0.0)
        ;; 0.0 <= [x] and [y] < 0.0
        (let ( (l (ite (is_pinf p x.u) (- ri.large_value) (ri.r_dn p (/ x.u y.u)))) 
               ;(u (ite (is_ninf p y.l) 0.0 (ri.r_up p (/ x.l y.l)))) 
               )
          l
          )

        (ite (<= x.u 0.0)
          ;; [x] <= 0.0 and [y] < 0.0
          (let ( (l (ite (is_ninf p y.l) 0.0 (ri.r_dn p (/ x.u y.l)))) 
                 ;(u (ite (is_ninf p x.l) ri.large_value (ri.r_up p (/ x.l y.u)))) 
                 )
            l
            )

          ;; [x] strictly contains 0.0 and [y] < 0.0
          (let ( (l (ite (is_pinf p x.u) (- ri.large_value) (ri.r_dn p (/ x.u y.u)))) 
                 ;(u (ite (is_ninf p x.l) ri.large_value (ri.r_up p (/ x.l y.u)))) 
                 )
            l
            )))

      ;; [y] contains 0.0; results in Entire
      (- ri.large_value)
      )))

(define-fun ri.div.u ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (> y.l 0.0)
    (ite (>= x.l 0.0)
      ;; 0.0 <= [x] and 0.0 < [y]
      (let ( ;(l (ite (is_pinf p y.u) 0.0 (ri.r_dn p (/ x.l y.u)))) 
             (u (ite (is_pinf p x.u) ri.large_value (ri.r_up p (/ x.u y.l)))) 
             )
        u
        )

      (ite (<= x.u 0.0)
        ;; [x] <= 0.0 and 0.0 < [y]
        (let ( ;(l (ite (is_ninf p x.l) (- ri.large_value) (ri.r_dn p (/ x.l y.l)))) 
               (u (ite (is_pinf p y.u) 0.0 (ri.r_up p (/ x.u y.u)))) 
               )
          u
          )

        ;; [x] is NaN or strictly contains 0.0 and 0.0 < [y]
        (let ( ;(l (ite (is_ninf p x.l) (- ri.large_value) (ri.r_dn p (/ x.l y.l)))) 
               (u (ite (is_pinf p x.u) ri.large_value (ri.r_up p (/ x.u y.l)))) 
               )
          u
          )))

    (ite (< y.u 0.0)
      (ite (>= x.l 0.0)
        ;; 0.0 <= [x] and [y] < 0.0
        (let ( ;(l (ite (is_pinf p x.u) (- ri.large_value) (ri.r_dn p (/ x.u y.u)))) 
               (u (ite (is_ninf p y.l) 0.0 (ri.r_up p (/ x.l y.l)))) 
               )
          u
          )

        (ite (<= x.u 0.0)
          ;; [x] <= 0.0 and [y] < 0.0
          (let ( ;(l (ite (is_ninf p y.l) 0.0 (ri.r_dn p (/ x.u y.l)))) 
                 (u (ite (is_ninf p x.l) ri.large_value (ri.r_up p (/ x.l y.u)))) 
                 )
            u
            )

          ;; [x] strictly contains 0.0 and [y] < 0.0
          (let ( ;(l (ite (is_pinf p x.u) (- ri.large_value) (ri.r_dn p (/ x.u y.u)))) 
                 (u (ite (is_ninf p x.l) ri.large_value (ri.r_up p (/ x.l y.u)))) 
                 )
            u
            )))

      ;; [y] contains 0.0; results in Entire
      ri.large_value
      )))

(define-fun ri.div.p_nan ( (p Int) 
                            (x.l Real) (x.u Real) (x.p_nan Bool) 
                            (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ite (> y.l 0.0)
    (ite (>= x.l 0.0)
      ;; 0.0 <= [x] and 0.0 < [y]
      (or x.p_nan y.p_nan (and (is_pinf p x.u) (is_pinf p y.u)))

      (ite (<= x.u 0.0)
        ;; [x] <= 0.0 and 0.0 < [y]
        (or x.p_nan y.p_nan (and (is_ninf p x.l) (is_pinf p y.u)))

        ;; [x] is NaN or strictly contains 0.0 and 0.0 < [y]
        (or x.p_nan y.p_nan (and (or (is_ninf p x.l) (is_pinf p x.u)) (is_pinf p y.u)))
        ))

    (ite (< y.u 0.0)
      (ite (>= x.l 0.0)
        ;; 0.0 <= [x] and [y] < 0.0
        (or x.p_nan y.p_nan (and (is_pinf p x.u) (is_ninf p y.l)))

        (ite (<= x.u 0.0)
          ;; [x] <= 0.0 and [y] < 0.0
          (or x.p_nan y.p_nan (and (is_ninf p x.l) (is_ninf p y.l)))

          ;; [x] strictly contains 0.0 and [y] < 0.0
          (or x.p_nan y.p_nan (and (or (is_ninf p x.l) (is_pinf p x.u)) (is_ninf p y.l)))
          ))

      ;; [y] contains 0.0; results in Entire
      (or x.p_nan y.p_nan (and (or (is_ninf p x.l) (is_pinf p x.u)) (or (is_ninf p y.l) (is_pinf p y.u))) 
          (and (<= x.l 0.0) (<= 0.0 x.u)) )
      )))

;;

;; Assignment for non-NaN values.
(define-fun ri.fpis ( (p Int)
                      (x.l Real) (x.u Real) (x.p_nan Bool)
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (not x.p_nan) (not y.p_nan)
       (and (= x.l y.l) (= x.u y.u) (= x.p_nan y.p_nan)) ) )

;; Assignment.
(define-fun ri.is ( (p Int)
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (= x.l y.l) (= x.u y.u) (= x.p_nan y.p_nan)) )
'''

rint_d_prologue_m = '''
;; For positive literals.

(define-fun ri.gt0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or (is_pinf p x.u) (> x.u 0.0)) )

(define-fun ri.geq0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or (is_pinf p x.u) (>= x.u 0.0)) )

(define-fun ri.gt ( (p Int) 
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
     (or (is_pinf p x.u) (is_ninf p y.l) 
         (ri.gt0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.geq ( (p Int) 
                      (x.l Real) (x.u Real) (x.p_nan Bool) 
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or (is_pinf p x.u) (is_ninf p y.l) 
        (ri.geq0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.fpeq ( (p Int) 
                      (x.l Real) (x.u Real) (x.p_nan Bool)
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (ri.geq p x.l x.u x.p_nan y.l y.u y.p_nan) 
       (ri.geq p y.l y.u y.p_nan x.l x.u x.p_nan) ) )

;; For negative literals.

(define-fun ri.lt0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or x.p_nan (is_ninf p x.l) (< x.l 0.0)) )

(define-fun ri.leq0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or x.p_nan (is_ninf p x.l) (<= x.l 0.0)) )

(define-fun ri.lt ( (p Int) 
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or x.p_nan y.p_nan
        (ri.lt0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.leq ( (p Int) 
                     (x.l Real) (x.u Real) (x.p_nan Bool) 
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or x.p_nan y.p_nan (is_pinf p x.u) (is_ninf p y.l) 
        (ri.leq0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.fpneq ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or (ri.lt p x.l x.u x.p_nan y.l y.u y.p_nan) 
      (ri.lt p y.l y.u y.p_nan x.l x.u x.p_nan) ) )

;; Syntactic equality.

(define-fun ri.eq ( (p Int)
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or (and x.p_nan y.p_nan)  
      (ri.fpeq p x.l x.u x.p_nan y.l y.u y.p_nan) ) )

(define-fun ri.neq ( (p Int)
                     (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ri.fpneq p x.l x.u x.p_nan y.l y.u y.p_nan) )
'''

rint_d_prologue_p = '''
;; For positive literals.

(define-fun ri.gt0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not x.p_nan) (not (is_ninf p x.l)) (> x.l 0.0)) )

(define-fun ri.geq0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not x.p_nan) (not (is_ninf p x.l)) (>= x.l 0.0)) )

(define-fun ri.gt ( (p Int) 
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not x.p_nan) (not y.p_nan)
      (ri.gt0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.geq ( (p Int) 
                     (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not x.p_nan) (not y.p_nan) 
         (ri.geq0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.fpeq ( (p Int) 
                      (x.l Real) (x.u Real) (x.p_nan Bool)
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (not x.p_nan) (not y.p_nan) 
       (= x.l x.u y.l y.u) ) )

;; For negative literals.

(define-fun ri.lt0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not (is_pinf p x.u)) (< x.u 0.0)) )

(define-fun ri.leq0 ( (p Int) (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not (is_ninf p x.l)) (<= x.u 0.0)) )

(define-fun ri.lt ( (p Int) 
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not (is_ninf p x.l)) (not (is_pinf p y.u)) 
      (ri.lt0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.leq ( (p Int) 
                     (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u p x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan p x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not (is_ninf p x.l)) (not (is_pinf p y.u)) 
         (ri.leq0 p s.l s.u s.p_nan) ) ) )

(define-fun ri.fpneq ( (p Int) 
                       (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or (ri.lt p x.l x.u x.p_nan y.l y.u y.p_nan) (ri.lt p y.l y.u y.p_nan x.l x.u x.p_nan) ) )

;; Syntactic equality.

(define-fun ri.eq ( (p Int)
                    (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ri.fpeq p x.l x.u x.p_nan y.l y.u y.p_nan) )

(define-fun ri.neq ( (p Int)
                     (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (or (not x.p_nan) (not y.p_nan))
    (not (ri.fpneq p x.l x.u x.p_nan y.l y.u y.p_nan)) ) )
'''

# eof
