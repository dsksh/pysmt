
rint_d_prologue = '''
(assert (> ri.large_value (* 2 ri.max_value)))

(define-fun ri.r_dn ((v Real)) Real
  (let ((w (- v (/ (abs v) ri.err_denom) ri.err_min)))
    (ite (>= w (- ri.max_value)) w
      (* (- 1.0) ri.large_value) ))
)

(define-fun ri.r_up ((v Real)) Real
  (let ((w (+ v (/ (abs v) ri.err_denom) ri.err_min)))
    (ite (<= w ri.max_value) w
      ri.large_value ))
)

(define-fun is_ninf ( (l Real) ) Bool (< l (- ri.max_value)))
(define-fun is_pinf ( (u Real) ) Bool (> u ri.max_value))
(define-fun p_nan ( (p_nan Bool) ) Bool p_nan)

(define-const ri.zero Real 0.0)
(define-const ri.zero.l Real 0.0)
(define-const ri.zero.u Real 0.0)
(define-const ri.zero.p_nan Bool false)

(define-const ri.zero_nan Real 0.0)
(define-const ri.zero_nan.l Real 0.0)
(define-const ri.zero_nan.u Real 0.0)
(define-const ri.zero_nan.p_nan Bool true)

(define-const ri.pinf Real ri.large_value)
(define-const ri.pinf.l Real ri.large_value)
(define-const ri.pinf.u Real ri.large_value)
(define-const ri.pinf.p_nan Bool false)

(define-const ri.ninf Real (- ri.large_value))
(define-const ri.ninf.l Real (- ri.large_value))
(define-const ri.ninf.u Real (- ri.large_value))
(define-const ri.ninf.p_nan Bool false)

(define-const ri.ninf_nan Real (- ri.large_value))
(define-const ri.ninf_nan.l Real (- ri.large_value))
(define-const ri.ninf_nan.u Real (- ri.large_value))
(define-const ri.ninf_nan.p_nan Bool true)

(define-const ri.entire.l Real (- ri.large_value))
(define-const ri.entire.u Real ri.large_value)
(define-const ri.entire.p_nan Bool true)

(define-fun ri_to_ri.l ( (l Real) ) Real (ri.r_dn l))
(define-fun ri_to_ri.u ( (u Real) ) Real (ri.r_up u))
(define-fun ri_to_ri.p_nan ( (p_nan Bool) ) Bool p_nan)

(define-fun real_to_ri.l ( (v Real) ) Real (ri.r_dn v))
(define-fun real_to_ri.u ( (v Real) ) Real (ri.r_up v))
(define-fun real_to_ri.p_nan ( (v Real) ) Bool false)

(define-fun ri.exact.l ( (v Real) ) Real v)
(define-fun ri.exact.u ( (v Real) ) Real v)
(define-fun ri.exact.p_nan ( (v Real) ) Bool false)

;; abs

(define-fun ri.abs.l ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (ite (>= x.l 0.0) x.l (ite (>= x.u 0.0) 0.0 (- x.u))) )

(define-fun ri.abs.u ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (ite (>= x.u (- x.l)) x.u (- x.l)) )

(define-fun ri.abs.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  x.p_nan )

;; neg

(define-fun ri.neg.l ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (- x.u) )

(define-fun ri.neg.u ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Real
  (- x.l) )

(define-fun ri.neg.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  x.p_nan )

;; add

(define-fun ri.add.l ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_dn (+ x.l y.l)) )

(define-fun ri.add.u ( (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_up (+ x.u y.u)) )

(define-fun ri.add.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                            (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or x.p_nan y.p_nan
      (and (is_ninf x.l) (is_pinf y.u)) (and (is_pinf x.u) (is_ninf y.l)) ))

;; sub

(define-fun ri.sub.l ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_dn (- x.l y.u)) ) 

(define-fun ri.sub.u ( (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ri.r_up (- x.u y.l)) )

(define-fun ri.sub.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                            (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or x.p_nan y.p_nan 
      (and (is_ninf x.l) (is_ninf y.u)) (and (is_pinf x.u) (is_pinf y.l)) ))

;; sub_exact

(define-fun ri.sub_exact.l ( (x.l Real) (x.u Real) (x.p_nan Bool)
                             (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (- x.l y.u) ) 

(define-fun ri.sub_exact.u ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                             (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (- x.u y.l) ) 

(define-fun ri.sub_exact.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool)
                                  (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or x.p_nan y.p_nan
      (and (is_ninf x.l) (is_ninf y.u)) (and (is_pinf x.u) (is_pinf y.l)) ))

;; mul

(define-fun ri.mul.l ( (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (>= x.l 0.0)
    (ite (= x.u 0.0)
      ;(ite (and (not (is_ninf y.l)) (not (is_pinf y.u)) (not x.p_nan) (not y.p_nan))
      ;  ;; [x] = [0.0]
      ;  ri.zero.l

      ;  ;; [x] = [0.0] and (-inf = [y] or [y] = +inf)
      ;  ri.nai.l )
      ri.zero.l

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_pinf x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; 0.0 <= [x] and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( (l (ri.r_dn (* x.l y.l)))
                 ;(u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                 ;        (ri.r_up (* x.u y.u)) ))
                 )
            l
            ) )

        (ite (<= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( (l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
                         (ri.r_dn (* x.u y.l)) ))
                 ;(u (ri.r_up (* x.l y.u)))
                 )
            l
            ) 

          ;;  0.0 <= [x] and [x] != [0.0] and [y] strictly contains 0.0
          (let ( (l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value) 
                         (ri.r_dn (* x.u y.l)) ))
                 ;(u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                 ;        (ri.r_up (* x.u y.u)) ))
                 )
            l
            ) ) ) )

    (ite (<= x.u 0.0)
      (ite (>= y.l 0.0)
        (ite (and (not (is_pinf y.u)) (= y.u 0.0))
          ;; [x] <= 0.0 and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_ninf x.l)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] <= 0.0 and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( (l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                         (ri.r_dn (* x.l y.u)) ))
                 ;(u (ri.r_up (* x.u y.l))) 
                 )
            l
            ))

        (ite (<= y.u 0.0)
          ;; [x] <= 0.0 and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( (l (ri.r_dn (* x.u y.u)))
                 ;(u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                 ;        (ri.r_up (* x.l y.l)) ))
                 )
            l
            ) 

          ;; [x] <= 0.0 and [x] != [0.0] and [y] strictly contains 0.0
          (let ( (l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                         (ri.r_dn (* x.l y.u)) ))
                 ;(u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                 ;        (ri.r_up (* x.l y.l)) ))
                 )
            l
            ) ) )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] = [0.0]
          ;(ite (and (not (is_ninf x.l)) (not (is_pinf x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] strictly contains 0.0 and 0.0 <= [y]
          (let ( (l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                         (ri.r_dn (* x.l y.u)) ))
                 ;(u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                 ;        (ri.r_up (* x.u y.u)) ))
                 )
            l
            ) )

        (ite (<= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] <= 0.0
          (let ( (l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
                         (ri.r_dn (* x.u y.l)) ))
                 ;(u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                 ;        (ri.r_up (* x.l y.l)) ))
                 )
            l
            )

          ;; [x] and [y] strictly contains 0.0
          (let ( (l1 (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                          (ri.r_dn (* x.l y.u)) ))
                 (l2 (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
                          (ri.r_dn (* x.u y.l)) ))
                 ;(u1 (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                 ;         (ri.r_up (* x.l y.l)) ))
                 ;(u2 (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                 ;         (ri.r_up (* x.u y.u)) ))
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

(define-fun ri.mul.u ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (>= x.l 0.0)
    (ite (= x.u 0.0)
      ;(ite (and (not (is_ninf y.l)) (not (is_pinf y.u)) (not x.p_nan) (not y.p_nan))
      ;  ;; [x] = [0.0]
      ;  ri.zero.l

      ;  ;; [x] = [0.0] and (-inf = [y] or [y] = +inf)
      ;  ri.nai.l )
      ri.zero.l

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_pinf x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; 0.0 <= [x] and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( ;(l (ri.r_dn (* x.l y.l)))
                 (u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                         (ri.r_up (* x.u y.u)) )))
            u
            ) )

        (ite (<= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( ;(l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
                 ;        (ri.r_dn (* x.u y.l)) ))
                 (u (ri.r_up (* x.l y.u))) )
            u 
            ) 

          ;;  0.0 <= [x] and [x] != [0.0] and [y] strictly contains 0.0
          (let ( ;(l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value) 
                 ;        (ri.r_dn (* x.u y.l)) ))
                 (u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                         (ri.r_up (* x.u y.u)) )))
            u
            ) ) ) )

    (ite (<= x.u 0.0)
      (ite (>= y.l 0.0)
        (ite (and (not (is_pinf y.u)) (= y.u 0.0))
          ;; [x] <= 0.0 and [x] != [0.0] and [y] = [0.0]
          ;(ite (and (not (is_ninf x.l)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] <= 0.0 and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          (let ( ;(l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                 ;        (ri.r_dn (* x.l y.u)) ))
                 (u (ri.r_up (* x.u y.l))) )
            u
            ))

        (ite (<= y.u 0.0)
          ;; [x] <= 0.0 and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
          (let ( ;(l (ri.r_dn (* x.u y.u)))
                 (u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                         (ri.r_up (* x.l y.l)) )))
            u
            ) 

          ;; [x] <= 0.0 and [x] != [0.0] and [y] strictly contains 0.0
          (let ( ;(l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                 ;        (ri.r_dn (* x.l y.u)) ))
                 (u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                         (ri.r_up (* x.l y.l)) )))
            u
            ) ) )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] = [0.0]
          ;(ite (and (not (is_ninf x.l)) (not (is_pinf x.u)) (not x.p_nan) (not y.p_nan))
          ;  ri.zero.l
          ;  ri.nai.l )
          ri.zero.l

          ;; [x] strictly contains 0.0 and 0.0 <= [y]
          (let ( ;(l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                 ;        (ri.r_dn (* x.l y.u)) ))
                 (u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                         (ri.r_up (* x.u y.u)) )))
            u
            ) )

        (ite (<= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] <= 0.0
          (let ( ;(l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
                 ;        (ri.r_dn (* x.u y.l)) ))
                 (u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                         (ri.r_up (* x.l y.l)) )))
            u
            )

          ;; [x] and [y] strictly contains 0.0
          (let ( (l1 (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
                          (ri.r_dn (* x.l y.u)) ))
                 (l2 (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
                          (ri.r_dn (* x.u y.l)) ))
                 (u1 (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
                          (ri.r_up (* x.l y.l)) ))
                 (u2 (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
                          (ri.r_up (* x.u y.u)) )))
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

(define-fun ri.mul.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool)
                           (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ite (>= x.l 0.0)
    (ite (= x.u 0.0)
      (ite (and (not (is_ninf y.l)) (not (is_pinf y.u)) (not x.p_nan) (not y.p_nan))
        ;; [x] = [0.0]
        false

        ;; [x] = [0.0] and (-inf = [y] or [y] = +inf)
        true
        )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; 0.0 <= [x] and [x] != [0.0] and [y] = [0.0]
          (ite (and (not (is_pinf x.u)) (not x.p_nan) (not y.p_nan))
            false
            true
            )

          ;; 0.0 <= [x] and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          ;(let ( (l (ri.r_dn (* x.l y.l)))
          ;       (*u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
          ;               (ri.r_up (* x.u y.u)) )*))
          ;  l
          ;  )
          false
          )

        ;(ite (<= y.u 0.0)
        ;  ;; 0.0 <= [x] and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
        ;  (let ( (l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
        ;                 (ri.r_dn (* x.u y.l)) ))
        ;         (*u (ri.r_up (* x.l y.u))*) )
        ;    l
        ;    ) 

        ;  ;;  0.0 <= [x] and [x] != [0.0] and [y] strictly contains 0.0
        ;  (let ( (l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value) 
        ;                 (ri.r_dn (* x.u y.l)) ))
        ;         (*u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
        ;                 (ri.r_up (* x.u y.u)) )*))
        ;    l
        ;    ) 
        ;  )
        false
        ) )

    (ite (<= x.u 0.0)
      (ite (>= y.l 0.0)
        (ite (and (not (is_pinf y.u)) (= y.u 0.0))
          ;; [x] <= 0.0 and [x] != [0.0] and [y] = [0.0]
          (ite (and (not (is_ninf x.l)) (not x.p_nan) (not y.p_nan))
            false
            true
            )

          ;; [x] <= 0.0 and [x] != [0.0] and 0.0 <= [y] and [y] != [0.0]
          ;(let ( (l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
          ;               (ri.r_dn (* x.l y.u)) ))
          ;       (*u (ri.r_up (* x.u y.l))*) )
          ;  l
          ;  )
          false
          )

        ;(ite (<= y.u 0.0)
        ;  ;; [x] <= 0.0 and [x] != [0.0] and [y] <= 0.0 and [y] != [0.0]
        ;  (let ( (l (ri.r_dn (* x.u y.u)))
        ;         (*u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
        ;                 (ri.r_up (* x.l y.l)) )*))
        ;    l
        ;    ) 

        ;  ;; [x] <= 0.0 and [x] != [0.0] and [y] strictly contains 0.0
        ;  (let ( (l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
        ;                 (ri.r_dn (* x.l y.u)) ))
        ;         (*u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
        ;                 (ri.r_up (* x.l y.l)) )*))
        ;    l
        ;    ) ) 
        false
        )

      (ite (>= y.l 0.0)
        (ite (= y.u 0.0)
          ;; [x] strictly contains 0.0 and [y] = [0.0]
          (ite (and (not (is_ninf x.l)) (not (is_pinf x.u)) (not x.p_nan) (not y.p_nan))
            false
            true )

          ;; [x] strictly contains 0.0 and 0.0 <= [y]
          ;(let ( (l (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
          ;               (ri.r_dn (* x.l y.u)) ))
          ;       (*u (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
          ;               (ri.r_up (* x.u y.u)) )*))
          ;  l
          ;  ) 
          false
          )

        ;(ite (<= y.u 0.0)
        ;  ;; [x] strictly contains 0.0 and [y] <= 0.0
        ;  (let ( (l (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
        ;                 (ri.r_dn (* x.u y.l)) ))
        ;         (*u (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
        ;                 (ri.r_up (* x.l y.l)) )*))
        ;    l
        ;    )

        ;  ;; [x] and [y] strictly contains 0.0
        ;  (let ( (l1 (ite (or (is_ninf x.l) (is_pinf y.u)) (- ri.large_value)
        ;                  (ri.r_dn (* x.l y.u)) ))
        ;         (l2 (ite (or (is_pinf x.u) (is_ninf y.l)) (- ri.large_value)
        ;                  (ri.r_dn (* x.u y.l)) ))
        ;         (*u1 (ite (or (is_ninf x.l) (is_ninf y.l)) ri.large_value
        ;                  (ri.r_up (* x.l y.l)) )*)
        ;         (*u2 (ite (or (is_pinf x.u) (is_pinf y.u)) ri.large_value
        ;                  (ri.r_up (* x.u y.u)) )*))
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

(define-fun ri.div.l ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (> y.l 0.0)
    (ite (>= x.l 0.0)
      ;; 0.0 <= [x] and 0.0 < [y]
      (let ( (l (ite (is_pinf y.u) 0.0 (ri.r_dn (/ x.l y.u)))) 
             ;(u (ite (is_pinf x.u) ri.large_value (ri.r_up (/ x.u y.l)))) 
             )
        l
        )

      (ite (<= x.u 0.0)
        ;; [x] <= 0.0 and 0.0 < [y]
        (let ( (l (ite (is_ninf x.l) (- ri.large_value) (ri.r_dn (/ x.l y.l)))) 
               ;(u (ite (is_pinf y.u) 0.0 (ri.r_up (/ x.u y.u)))) 
               )
          l
          )

        ;; [x] is NaN or strictly contains 0.0 and 0.0 < [y]
        (let ( (l (ite (is_ninf x.l) (- ri.large_value) (ri.r_dn (/ x.l y.l)))) 
               ;(u (ite (is_pinf x.u) ri.large_value (ri.r_up (/ x.u y.l)))) 
               )
          l
          )))

    (ite (< y.u 0.0)
      (ite (>= x.l 0.0)
        ;; 0.0 <= [x] and [y] < 0.0
        (let ( (l (ite (is_pinf x.u) (- ri.large_value) (ri.r_dn (/ x.u y.u)))) 
               ;(u (ite (is_ninf y.l) 0.0 (ri.r_up (/ x.l y.l)))) 
               )
          l
          )

        (ite (<= x.u 0.0)
          ;; [x] <= 0.0 and [y] < 0.0
          (let ( (l (ite (is_ninf y.l) 0.0 (ri.r_dn (/ x.u y.l)))) 
                 ;(u (ite (is_ninf x.l) ri.large_value (ri.r_up (/ x.l y.u)))) 
                 )
            l
            )

          ;; [x] strictly contains 0.0 and [y] < 0.0
          (let ( (l (ite (is_pinf x.u) (- ri.large_value) (ri.r_dn (/ x.u y.u)))) 
                 ;(u (ite (is_ninf x.l) ri.large_value (ri.r_up (/ x.l y.u)))) 
                 )
            l
            )))

      ;; [y] contains 0.0; results in Entire
      (- ri.large_value)
      )))

(define-fun ri.div.u ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Real
  (ite (> y.l 0.0)
    (ite (>= x.l 0.0)
      ;; 0.0 <= [x] and 0.0 < [y]
      (let ( ;(l (ite (is_pinf y.u) 0.0 (ri.r_dn (/ x.l y.u)))) 
             (u (ite (is_pinf x.u) ri.large_value (ri.r_up (/ x.u y.l)))) 
             )
        u
        )

      (ite (<= x.u 0.0)
        ;; [x] <= 0.0 and 0.0 < [y]
        (let ( ;(l (ite (is_ninf x.l) (- ri.large_value) (ri.r_dn (/ x.l y.l)))) 
               (u (ite (is_pinf y.u) 0.0 (ri.r_up (/ x.u y.u)))) 
               )
          u
          )

        ;; [x] is NaN or strictly contains 0.0 and 0.0 < [y]
        (let ( ;(l (ite (is_ninf x.l) (- ri.large_value) (ri.r_dn (/ x.l y.l)))) 
               (u (ite (is_pinf x.u) ri.large_value (ri.r_up (/ x.u y.l)))) 
               )
          u
          )))

    (ite (< y.u 0.0)
      (ite (>= x.l 0.0)
        ;; 0.0 <= [x] and [y] < 0.0
        (let ( ;(l (ite (is_pinf x.u) (- ri.large_value) (ri.r_dn (/ x.u y.u)))) 
               (u (ite (is_ninf y.l) 0.0 (ri.r_up (/ x.l y.l)))) 
               )
          u
          )

        (ite (<= x.u 0.0)
          ;; [x] <= 0.0 and [y] < 0.0
          (let ( ;(l (ite (is_ninf y.l) 0.0 (ri.r_dn (/ x.u y.l)))) 
                 (u (ite (is_ninf x.l) ri.large_value (ri.r_up (/ x.l y.u)))) 
                 )
            u
            )

          ;; [x] strictly contains 0.0 and [y] < 0.0
          (let ( ;(l (ite (is_pinf x.u) (- ri.large_value) (ri.r_dn (/ x.u y.u)))) 
                 (u (ite (is_ninf x.l) ri.large_value (ri.r_up (/ x.l y.u)))) 
                 )
            u
            )))

      ;; [y] contains 0.0; results in Entire
      ri.large_value
      )))

(define-fun ri.div.p_nan ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                          (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ite (> y.l 0.0)
    (ite (>= x.l 0.0)
      ;; 0.0 <= [x] and 0.0 < [y]
      (or x.p_nan y.p_nan (and (is_pinf x.u) (is_pinf y.u)))

      (ite (<= x.u 0.0)
        ;; [x] <= 0.0 and 0.0 < [y]
        (or x.p_nan y.p_nan (and (is_ninf x.l) (is_pinf y.u)))

        ;; [x] is NaN or strictly contains 0.0 and 0.0 < [y]
        (or x.p_nan y.p_nan (and (or (is_ninf x.l) (is_pinf x.u)) (is_pinf y.u)))
        ))

    (ite (< y.u 0.0)
      (ite (>= x.l 0.0)
        ;; 0.0 <= [x] and [y] < 0.0
        (or x.p_nan y.p_nan (and (is_pinf x.u) (is_ninf y.l)))

        (ite (<= x.u 0.0)
          ;; [x] <= 0.0 and [y] < 0.0
          (or x.p_nan y.p_nan (and (is_ninf x.l) (is_ninf y.l)))

          ;; [x] strictly contains 0.0 and [y] < 0.0
          (or x.p_nan y.p_nan (and (or (is_ninf x.l) (is_pinf x.u)) (is_ninf y.l)))
          ))

      ;; [y] contains 0.0; results in Entire
      (or x.p_nan y.p_nan (and (or (is_ninf x.l) (is_pinf x.u)) (or (is_ninf y.l) (is_pinf y.u))) 
          (and (<= x.l 0.0) (<= 0.0 x.u)) )
      )))

;;

;; Assignment for non-NaN values.
(define-fun ri.fpis ( (x.l Real) (x.u Real) (x.p_nan Bool)
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (not x.p_nan) (not y.p_nan)
       (and (= x.l y.l) (= x.u y.u) (= x.p_nan y.p_nan)) ) )

;; Assignment.
(define-fun ri.is ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (= x.l y.l) (= x.u y.u) (= x.p_nan y.p_nan)) )
'''

rint_d_prologue_m = '''
;; For positive literals.

(define-fun ri.gt0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or (is_pinf x.u) (> x.u 0.0)) )

(define-fun ri.geq0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or (is_pinf x.u) (>= x.u 0.0)) )

(define-fun ri.gt ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or (is_pinf x.u) (is_ninf y.l) 
        (ri.gt0 s.l s.u s.p_nan) ) ) )

(define-fun ri.geq ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or (is_pinf x.u) (is_ninf y.l) 
        (ri.geq0 s.l s.u s.p_nan) ) ) )

(define-fun ri.fpeq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (ri.geq x.l x.u x.p_nan y.l y.u y.p_nan) 
       (ri.geq y.l y.u y.p_nan x.l x.u x.p_nan) ) )

;; For negative literals.

(define-fun ri.lt0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or x.p_nan (is_ninf x.l) (< x.l 0.0)) )

(define-fun ri.leq0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (or x.p_nan (is_ninf x.l) (<= x.l 0.0)) )

(define-fun ri.lt ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or x.p_nan y.p_nan
        (ri.lt0 s.l s.u s.p_nan) ) ) )

(define-fun ri.leq ( (x.l Real) (x.u Real) (x.p_nan Bool) 
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (or x.p_nan y.p_nan
        (ri.leq0 s.l s.u s.p_nan) ) ) )

(define-fun ri.fpneq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or (ri.lt x.l x.u x.p_nan y.l y.u y.p_nan) 
      (ri.lt y.l y.u y.p_nan x.l x.u x.p_nan) ) )

;; Syntactic equality.

(define-fun ri.eq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or (and x.p_nan y.p_nan) 
      (ri.fpeq x.l x.u x.p_nan y.l y.u y.p_nan) ) )

(define-fun ri.neq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ri.fpneq x.l x.u x.p_nan y.l y.u y.p_nan) )
'''

rint_d_prologue_p = '''
;; For positive literals.

(define-fun ri.gt0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not x.p_nan) (not (is_ninf x.l)) (> x.l 0.0)) )

(define-fun ri.geq0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not x.p_nan) (not (is_ninf x.l)) (>= x.l 0.0)) )

(define-fun ri.gt ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not x.p_nan) (not y.p_nan)
         (ri.gt0 s.l s.u s.p_nan) ) ) )

(define-fun ri.geq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not x.p_nan) (not y.p_nan)
         (ri.geq0 s.l s.u s.p_nan) ) ) )

(define-fun ri.fpeq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                      (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (not x.p_nan) (not y.p_nan) 
       (= x.l x.u y.l y.u) ) )

;; For negative literals.

(define-fun ri.lt0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not (is_pinf x.u)) (< x.u 0.0)) )

(define-fun ri.leq0 ( (x.l Real) (x.u Real) (x.p_nan Bool) ) Bool
  (and (not (is_pinf x.u)) (<= x.u 0.0)) )

(define-fun ri.lt ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not (is_pinf x.u)) (not (is_ninf y.l)) 
         (ri.lt0 s.l s.u s.p_nan) ) ) )

(define-fun ri.leq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (let ( (s.l (ri.sub_exact.l x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.u (ri.sub_exact.u x.l x.u x.p_nan y.l y.u y.p_nan))
         (s.p_nan (ri.sub_exact.p_nan x.l x.u x.p_nan y.l y.u y.p_nan)) )
    (and (not (is_ninf x.l)) (not (is_pinf y.u)) 
         (ri.leq0 s.l s.u s.p_nan) ) ) )

(define-fun ri.fpneq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                       (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (or (ri.lt x.l x.u x.p_nan y.l y.u y.p_nan) (ri.lt y.l y.u y.p_nan x.l x.u x.p_nan) ) )

;; Syntactic equality.

(define-fun ri.eq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                    (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (ri.fpeq x.l x.u x.p_nan y.l y.u y.p_nan) )

(define-fun ri.neq ( (x.l Real) (x.u Real) (x.p_nan Bool)
                     (y.l Real) (y.u Real) (y.p_nan Bool) ) Bool
  (and (or (not x.p_nan) (not y.p_nan))
    (ri.fpneq x.l x.u x.p_nan y.l y.u y.p_nan) ) )
'''

# eof
