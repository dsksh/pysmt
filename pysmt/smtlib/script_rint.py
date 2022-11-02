
rint_param_decls = '''
(declare-const ri.max_value Real)
;(declare-const ri.normal_bound Real)
(declare-const ri.err_denom Real)
(declare-const ri.err_min Real)
(declare-const ri.large_value Real)
'''

def assert_rint_param_values(os, eb=11, sb=53):
    emax = 2**(eb-1)-1

    os.write('\n(assert (= ri.max_value %s))\n' % str((2**sb-1) * 2**(emax-sb+1)))

    normal_bound = 2**(emax-1)
    #os.write('(assert (= ri.normal_bound (/ 1 %d.)))\n' % normal_bound)

    err_denom = 2**(sb-1)
    os.write('(assert (= ri.err_denom %d))\n' % err_denom)

    err_min_1 = 2**(sb+emax-2)
    #os.write('(assert (= ri.err_min (/ %d %d)))\n' % (err_denom-1, normal_bound*err_denom))
    os.write('(assert (= ri.err_min (/ 1 %d)))\n' % err_min_1)

def define_rint_rnd_funs(os, prec, prpr=True):
    if prpr and len(prec) > 0 and prec[0][1] > 0:
        sb = prec[0][1]
        err_denom = str(2**(sb-1))
    else:
        err_denom = 'ri.err_denom'

    os.write('\n(define-fun ri.r_dn ((v Real)) Real\n')
    os.write('  (let ((w (- v (/ (ite (>= v 0) v (- v)) %s) ri.err_min)))\n' % err_denom)
    os.write('    (ite (>= w (* (- 1) ri.max_value)) w\n')
    os.write('      (* (- 1) ri.large_value) ))\n')
    os.write(')\n\n')

    os.write('(define-fun ri.r_up ((v Real)) Real\n')
    os.write('  (let ((w (+ v (/ (ite (>= v 0) v (- v)) %s) ri.err_min)))\n' % err_denom)
    os.write('    (ite (<= w ri.max_value) w\n')
    os.write('      ri.large_value ))\n')
    os.write(')\n\n')

rint_prologue = '''
(assert (> ri.large_value (* 2 ri.max_value)))

(declare-datatype RInt ((tpl (ri.l Real) (ri.u Real) (p_nan Bool) )))

(define-fun is_ninf ((v RInt)) Bool (< (ri.l v) (- ri.max_value)))
(define-fun is_pinf ((v RInt)) Bool (> (ri.u v) ri.max_value))

(define-const ri.zero RInt (tpl 0 0 false))
(define-const ri.zero_nan RInt (tpl 0 0 true))

(define-const ri.pinf RInt (tpl ri.large_value ri.large_value false))
(define-const ri.ninf RInt (tpl (- ri.large_value) (- ri.large_value) false))

(define-const ri.ninf_nan RInt (tpl (- ri.large_value) (- ri.large_value) true))

(define-const ri.entire RInt (tpl (- ri.large_value) ri.large_value true))

(define-fun ri_to_ri ((v RInt)) RInt
  (let ( (l (ri.r_dn (ri.l v))) 
         (u (ri.r_up (ri.u v))) )
    (tpl l u (p_nan v)) )
)

(define-fun real_to_ri ((v Real)) RInt
  (let ( (l (ri.r_dn v)) 
         (u (ri.r_up v)) )
    (tpl l u false) )
)

(define-fun ri.exact ((v Real)) RInt
  (tpl v v false)
)

(define-fun ri.abs ((x RInt)) RInt
  (let ( (l (ite (>= (ri.l x) 0) (ri.u x) (ite (> (ri.u x) (- (ri.l x))) (ri.u x) (- (ri.l x)))))
         (u (ite (>= (ri.l x) 0) (ri.l x) (ite (< (ri.u x) 0) (- (ri.u x)) 0))) )
    (tpl l u (p_nan x) ) ) )

(define-fun ri.neg ((x RInt)) RInt
  (tpl (- (ri.u x)) (- (ri.l x)) (p_nan x) ) )

(define-fun ri.add ((x RInt) (y RInt)) RInt
  (let ( (l (ri.r_dn (+ (ri.l x) (ri.l y)))) 
         (u (ri.r_up (+ (ri.u x) (ri.u y)))) )
    (tpl l u 
      (or (p_nan x) (p_nan y) (and (is_ninf x) (is_pinf y)) (and (is_pinf x) (is_ninf y))) ) ) )

(define-fun ri.sub ((x RInt) (y RInt)) RInt
  (let ( (l (ri.r_dn (- (ri.l x) (ri.u y)))) 
         (u (ri.r_up (- (ri.u x) (ri.l y)))) )
    (tpl l u 
      (or (p_nan x) (p_nan y) (and (is_ninf x) (is_ninf y)) (and (is_pinf x) (is_pinf y))) ) ) )

(define-fun ri.sub_exact ((x RInt) (y RInt)) RInt
  (let ( (l (- (ri.l x) (ri.u y))) 
         (u (- (ri.u x) (ri.l y))) )
    (tpl l u 
      (or (p_nan x) (p_nan y) (and (is_ninf x) (is_ninf y)) (and (is_pinf x) (is_pinf y))) ) ) )

(define-fun ri.mul ((x RInt) (y RInt)) RInt
  (ite (>= (ri.l x) 0)
    (ite (= (ri.u x) 0)
      (ite (and (not (is_ninf y)) (not (is_pinf y)) (not (p_nan x)) (not (p_nan y)))
        ;; [x] = [0]
        ri.zero
        ;; [x] = [0] and (-inf = [y] or [y] = +inf)
        ri.zero_nan )

      (ite (>= (ri.l y) 0)
        (ite (= (ri.u y) 0)
          ;; 0 <= [x] and [x] != [0] and [y] = [0]
          (ite (and (not (is_pinf x)) (not (p_nan x)) (not (p_nan y)))
            ri.zero
            ri.zero_nan )

          ;; 0 <= [x] and [x] != [0] and 0 <= [y] and [y] != [0]
          (let ( (l (ri.r_dn (* (ri.l x) (ri.l y))))
                 (u (ite (or (is_pinf x) (is_pinf y)) ri.large_value 
                         (ri.r_up (* (ri.u x) (ri.u y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.l x) 0) (is_pinf y)) 
                  (and (is_pinf x) (= (ri.l y) 0)) ))))

        (ite (<= (ri.u y) 0)
          ;; 0 <= [x] and [x] != [0] and [y] <= 0 and [y] != [0]
          (let ( (l (ite (or (is_pinf x) (is_ninf y)) (- ri.large_value) 
                         (ri.r_dn (* (ri.u x) (ri.l y))) ))
                 (u (ri.r_up (* (ri.l x) (ri.u y)))) )
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.l x) 0) (is_ninf y)) 
                  (and (is_pinf x) (= (ri.u y) 0) ))))

          ;;  0 <= [x] and [x] != [0] and [y] strictly contains 0
          (let ( (l (ite (or (is_pinf x) (is_ninf y)) (- ri.large_value) 
                         (ri.r_dn (* (ri.u x) (ri.l y))) ) )
                 (u (ite (or (is_pinf x) (is_pinf y)) ri.large_value
                         (ri.r_up (* (ri.u x) (ri.u y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_pinf x) 
                  (and (= (ri.l x) 0) (or (is_ninf y) (is_pinf y))) ))))))

    (ite (<= (ri.u x) 0)
      (ite (>= (ri.l y) 0)
        (ite (and (not (is_pinf y)) (= (ri.u y) 0))
          ;; [x] <= 0 and [x] != [0] and [y] = [0]
          (ite (and (not (is_ninf x)) (not (p_nan x)) (not (p_nan y)))
            ri.zero
            ri.zero_nan )

          ;; [x] <= 0 and [x] != [0] and 0 <= [y] and [y] != [0]
          (let ( (l (ite (or (is_ninf x) (is_pinf y)) (- ri.large_value) 
                         (ri.r_dn (* (ri.l x) (ri.u y))) ))
                 (u (ri.r_up (* (ri.u x) (ri.l y)))) )
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.u x) 0) (is_pinf y)) 
                  (and (is_ninf x) (= (ri.l y) 0))) ) ) )

        (ite (<= (ri.u y) 0)
          ;; [x] <= 0 and [x] != [0] and [y] <= 0 and [y] != [0]
          (let ( (l (ri.r_dn (* (ri.u x) (ri.u y))))
                 (u (ite (or (is_ninf x) (is_ninf y)) ri.large_value
                         (ri.r_up (* (ri.l x) (ri.l y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.u x) 0) (is_ninf y)) 
                  (and (is_ninf x) (= (ri.u y) 0)) ))) 

          ;; [x] <= 0 and [x] != [0] and [y] strictly contains 0
          (let ( (l (ite (or (is_ninf x) (is_pinf y)) (- ri.large_value) 
                         (ri.r_dn (* (ri.l x) (ri.u y))) ))
                 (u (ite (or (is_ninf x) (is_ninf y)) ri.large_value
                         (ri.r_up (* (ri.l x) (ri.l y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_ninf x) (and (= (ri.u x) 0) 
                  (or (is_ninf y) (is_pinf y))) )))))

      (ite (>= (ri.l y) 0)
        (ite (= (ri.u y) 0)
          ;; [x] strictly contains 0 and [y] = [0]
          (ite (and (not (is_ninf x)) (not (is_pinf x)) (not (p_nan x)) (not (p_nan y)))
            ri.zero
            ri.zero_nan )

          ;; [x] strictly contains 0 and 0 <= [y]
          (let ( (l (ite (or (is_ninf x) (is_pinf y)) (- ri.large_value) 
                         (ri.r_dn (* (ri.l x) (ri.u y))) ))
                 (u (ite (or (is_pinf x) (is_pinf y)) ri.large_value
                         (ri.r_up (* (ri.u x) (ri.u y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_pinf y) 
                  (and (or (is_ninf x) (is_pinf x)) (= (ri.l y) 0)) ))))

        (ite (<= (ri.u y) 0)
          ;; [x] strictly contains 0 and [y] <= 0
          (let ( (l (ite (or (is_pinf x) (is_ninf y)) (- ri.large_value) 
                         (ri.r_dn (* (ri.u x) (ri.l y))) ))
                 (u (ite (or (is_ninf x) (is_ninf y)) ri.large_value
                         (ri.r_up (* (ri.l x) (ri.l y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_ninf y) 
                  (and (or (is_ninf x) (is_pinf x)) (= (ri.u y) 0)) )))

          ;; [x] and [y] strictly contains 0
          (let ( (l1 (ite (or (is_ninf x) (is_pinf y)) (- ri.large_value) 
                          (ri.r_dn (* (ri.l x) (ri.u y))) ))
                 (l2 (ite (or (is_pinf x) (is_ninf y)) (- ri.large_value)
                          (ri.r_dn (* (ri.u x) (ri.l y))) ))
                 (u1 (ite (or (is_ninf x) (is_ninf y)) ri.large_value
                          (ri.r_up (* (ri.l x) (ri.l y))) ))
                 (u2 (ite (or (is_pinf x) (is_pinf y)) ri.large_value
                          (ri.r_up (* (ri.u x) (ri.u y))) )))
            (ite (< l1 l2) 
              (ite (> u1 u2)
                (tpl l1 u1 (or (p_nan x) (p_nan y) (is_ninf x)))

                (tpl l1 u2 (or (p_nan x) (p_nan y) (is_ninf x) (is_pinf y))))

              (ite (> u1 u2)
                (tpl l2 u1 (or (p_nan x) (p_nan y) (is_ninf x) (is_ninf y)))

                (tpl l2 u2
                  (or (p_nan x) (p_nan y) 
                      (is_ninf x) (is_pinf x) (is_ninf y) (is_pinf y)) )))))))))

(define-fun ri.div ((x RInt) (y RInt)) RInt
  (ite (> (ri.l y) 0)
    (ite (>= (ri.l x) 0)
      ;; 0 <= [x] and 0 < [y]
      (let ( (l (ite (is_pinf y) 0 (ri.r_dn (/ (ri.l x) (ri.u y)))))
             (u (ite (is_pinf x) ri.large_value (ri.r_up (/ (ri.u x) (ri.l y))))) )
        (tpl l u (or (p_nan x) (p_nan y) (and (is_pinf x) (is_pinf y)))) )

      (ite (<= (ri.u x) 0)
        ;; [x] <= 0 and 0 < [y]
        (let ( (l (ite (is_ninf x) (- ri.large_value) (ri.r_dn (/ (ri.l x) (ri.l y)))))
               (u (ite (is_pinf y) 0 (ri.r_up (/ (ri.u x) (ri.u y))))) )
          (tpl l u (or (p_nan x) (p_nan y) (and (is_ninf x) (is_pinf y)))) )

        ;; [x] strictly contains 0 and 0 < [y]
        (let ( (l (ite (is_ninf x) (- ri.large_value) (ri.r_dn (/ (ri.l x) (ri.l y)))))
               (u (ite (is_pinf x) ri.large_value (ri.r_up (/ (ri.u x) (ri.l y))))) )
          (tpl l u (or (p_nan x) (p_nan y) (and (or (is_ninf x) (is_pinf x)) (is_pinf y)))) )))

    (ite (< (ri.u y) 0)
      (ite (>= (ri.l x) 0)
        ;; 0 <= [x] and [y] < 0
        (let ( (l (ite (is_pinf x) (- ri.large_value) (ri.r_dn (/ (ri.u x) (ri.u y)))))
               (u (ite (is_ninf y) 0 (ri.r_up (/ (ri.l x) (ri.l y))))) )
          (tpl l u (or (p_nan x) (p_nan y) (and (is_pinf x) (is_ninf y)))))

        (ite (<= (ri.u x) 0)
          ;; [x] <= 0 and [y] < 0
          (let ( (l (ite (is_ninf y) 0 (ri.r_dn (/ (ri.u x) (ri.l y)))))
                 (u (ite (is_ninf x) ri.large_value (ri.r_up (/ (ri.l x) (ri.u y))))) )
            (tpl l u (or (p_nan x) (p_nan x) (and (is_ninf x) (is_ninf y)))) )

          ;; [x] strictly contains 0 and [y] < 0
          (let ( (l (ite (is_pinf x) (- ri.large_value) (ri.r_dn (/ (ri.u x) (ri.u y)))))
                 (u (ite (is_ninf x) ri.large_value (ri.r_up (/ (ri.l x) (ri.u y))))) )
            (tpl l u (or (p_nan x) (p_nan x) (and (or (is_ninf x) (is_pinf x)) (is_ninf y)))) )))

      ;; [y] contains 0; results in Entire
      (tpl (- ri.large_value) ri.large_value 
           (or (p_nan x) (p_nan y) (and (or (is_ninf x) (is_pinf x)) (or (is_ninf y) (is_pinf y))) 
               (and (<= (ri.l x) 0) (<= 0 (ri.u x))) )))))

;;

;; Assignment for non-NaN values.
(define-fun ri.fpis ((x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) 
       (= x y) )
) 

;; Assignment.
(define-fun ri.is ((x RInt) (y RInt)) Bool
  (= x y) 
) 
'''

rint_prologue_m = '''
;; For positive literals.

(define-fun ri.gt0 ((x RInt)) Bool
  (or (is_pinf x) (> (ri.u x) 0))
)

(define-fun ri.geq0 ((x RInt)) Bool
  (or (is_pinf x) (>= (ri.u x) 0))
)

(define-fun ri.gt ((x RInt) (y RInt)) Bool
  (or (is_pinf x) (is_ninf y) (ri.gt0 (ri.sub_exact x y)))
)

(define-fun ri.geq ((x RInt) (y RInt)) Bool
  (or (is_pinf x) (is_ninf y) (ri.geq0 (ri.sub_exact x y)))
) 

(define-fun ri.fpeq ((x RInt) (y RInt)) Bool
  (and (ri.geq x y) (ri.geq y x)) 
)

;; For negative literals.

(define-fun ri.lt0 ((x RInt)) Bool
  (or (p_nan x) (is_ninf x) (< (ri.l x) 0))
)

(define-fun ri.leq0 ((x RInt)) Bool
  (or (p_nan x) (is_ninf x) (<= (ri.l x) 0)) 
)

(define-fun ri.lt ((x RInt) (y RInt)) Bool
  (or (p_nan x) (p_nan y) (ri.lt0 (ri.sub_exact x y)))
)

(define-fun ri.leq ((x RInt) (y RInt)) Bool
  (or (p_nan x) (p_nan y) (ri.leq0 (ri.sub_exact x y)))
) 

(define-fun ri.fpneq ((x RInt) (y RInt)) Bool
  (or (ri.lt x y) (ri.lt y x))
)

;; Syntactic equality.

(define-fun ri.eq ((x RInt) (y RInt)) Bool
  (or (and (p_nan x) (p_nan y)) (ri.fpeq x y))
)

(define-fun ri.neq ((x RInt) (y RInt)) Bool
  (ri.fpneq x y)
)
'''

rint_prologue_p = '''
;; For positive literals.

(define-fun ri.gt0 ((x RInt)) Bool
  (and (not (p_nan x)) (not (is_ninf x)) (> (ri.l x) 0))
)

(define-fun ri.geq0 ((x RInt)) Bool
  (and (not (p_nan x)) (not (is_ninf x)) (>= (ri.l x) 0))
)

(define-fun ri.gt ((x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) (ri.gt0 (ri.sub_exact x y)))
)

(define-fun ri.geq ((x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) (ri.geq0 (ri.sub_exact x y)))
)

(define-fun ri.fpeq ((x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) 
       (= (ri.l x) (ri.u x) (ri.l y) (ri.u y)) )
)

;; For negative literals.

(define-fun ri.lt0 ((x RInt)) Bool
  (and (not (is_pinf x)) (< (ri.u x) 0))
)

(define-fun ri.leq0 ((x RInt)) Bool
  (and (not (is_pinf x)) (<= (ri.u x) 0)) 
)  

(define-fun ri.lt ((x RInt) (y RInt)) Bool
  (and (not (is_pinf x)) (not (is_ninf y)) 
       (ri.lt0 (ri.sub_exact x y)) )
)

(define-fun ri.leq ((x RInt) (y RInt)) Bool
  (and (not (is_pinf x)) (not (is_ninf y))  
       (ri.leq0 (ri.sub_exact x y)) )
)

(define-fun ri.fpneq((x RInt) (y RInt)) Bool
  (or (ri.lt x y) (ri.lt y x))
)

;; Syntactic equality.

(define-fun ri.eq ((x RInt) (y RInt)) Bool
  (ri.fpeq x y)
)

(define-fun ri.neq((x RInt) (y RInt)) Bool
  (and (or (not (p_nan x)) (not (p_nan y))) (ri.fpneq x y))
)
'''

# eof
