
rint_param_decls = '''
(declare-fun ri.max_value (Int) Real)
;(declare-fun ri.normal_bound (Int) Real)
(declare-fun ri.err_denom (Int) Real)
(declare-fun ri.err_min (Int) Real)
(declare-const ri.large_value Real)
'''

def assert_rint_param_values(os, precs):
    for p in range(len(precs)):
        eb, sb = precs[p]

        emax = 2**(eb-1)-1

        os.write('\n(assert (= (ri.max_value %d) %s))\n' % (p, str((2**sb-1) * 2**(emax-sb+1))))
        os.write('(assert (> ri.large_value (* 2 (ri.max_value %d))))\n' % p)
    
        normal_bound = 2**(emax-1)
        #os.write('(assert (= (ri.normal_bound %d) (/ 1 %d)))\n' % (p, normal_bound))
    
        err_denom = 2**(sb-1)
        os.write('(assert (= (ri.err_denom %d) %d))\n' % (p, err_denom))

        err_min_1 = 2**(sb+emax-2)
        #os.write('(assert (= (ri.err_min %d) (/ %d %d)))\n' % (p, err_denom-1, normal_bound*err_denom))
        os.write('(assert (= (ri.err_min %d) (/ 1 %d)))\n' % (p, err_min_1))

def define_rint_rnd_funs(os, precs, prpr):
    os.write('\n(define-fun ri.r_dn ((p Int) (v Real)) Real\n')

    for p in range(len(precs)):
        eb, sb = precs[p]

        if prpr:
            err_denom = str(2**(sb-1))
        else:
            err_denom = '(ri.err_denom %d)' % p
    
        #os.write('  (ite (= p %d) (- v (/ (ite (>= v 0) v (- v)) %s) (ri.err_min p))\n' % (p, err_denom))
        os.write('  (ite (= p %d) (let ((w (- v (/ (ite (>= v 0) v (- v)) %s) (ri.err_min %d))))\n' % (p, err_denom, p))
        os.write('    (ite (>= w (* (- 1) (ri.max_value p))) w\n')
        os.write('      (* (- 1) ri.large_value) ))\n')

    os.write('  (- ri.large_value) ') # Else (should not be used).

    for p in range(len(precs)):
        os.write(')')
    os.write(')\n\n')
    
    os.write('\n(define-fun ri.r_up ((p Int) (v Real)) Real\n')

    for p in range(len(precs)):
        eb, sb = precs[p]

        if prpr:
            err_denom = str(2**(sb-1))
        else:
            err_denom = '(ri.err_denom %d)' % p
    
        #os.write('  (ite (= p %d) (+ v (/ (ite (>= v 0) v (- v)) %s) (ri.err_min p))\n' % (p, err_denom))
        os.write('  (ite (= p %d) (let ((w (+ v (/ (ite (>= v 0) v (- v)) %s) (ri.err_min %d))))\n' % (p, err_denom, p))
        os.write('    (ite (<= w (ri.max_value p)) w\n')
        os.write('      ri.large_value ))\n')

    os.write('  ri.large_value ') # Else (should not be used).

    for p in range(len(precs)):
        os.write(')')
    os.write(')\n\n')

rint_prologue = '''
(declare-datatype RInt ((tpl (ri.l Real) (ri.u Real) (p_nan Bool) )))

(define-fun is_ninf ((p Int) (v RInt)) Bool (< (ri.l v) (- (ri.max_value p))))
(define-fun is_pinf ((p Int) (v RInt)) Bool (> (ri.u v) (ri.max_value p)))

(define-const ri.zero RInt (tpl 0 0 false))
(define-const ri.zero_nan RInt (tpl 0 0 true))
(define-const ri.ninf_nan RInt (tpl (- ri.large_value) (- ri.large_value) true))

(define-fun ri.pinf ((p Int)) RInt (tpl ri.large_value ri.large_value false))
(define-fun ri.ninf ((p Int)) RInt (tpl (- ri.large_value) (- ri.large_value) false))

(define-fun ri.entire ((p Int)) RInt (tpl (- ri.large_value) ri.large_value true))

(define-fun ri_to_ri ((p Int) (v RInt)) RInt
  (let ( (l (ri.r_dn p (ri.l v))) 
         (u (ri.r_up p (ri.u v))) )
    (tpl l u (p_nan v)) )
)

(define-fun real_to_ri ((p Int) (v Real)) RInt
  (let ( (l (ri.r_dn p v)) 
         (u (ri.r_up p v)) )
    (tpl l u false) )
)

(define-fun ri.exact ((p Int) (v Real)) RInt
  (tpl v v false)
)

(define-fun ri.abs ((p Int) (x RInt)) RInt
  (let ( (l (ite (>= (ri.l x) 0) (ri.u x) (ite (> (ri.u x) (- (ri.l x))) (ri.u x) (- (ri.l x)))))
         (u (ite (>= (ri.l x) 0) (ri.l x) (ite (< (ri.u x) 0) (- (ri.u x)) 0))) )
    (tpl l u (p_nan x) ) ) )

(define-fun ri.neg ((p Int) (x RInt)) RInt
  (tpl (- (ri.u x)) (- (ri.l x)) (p_nan x) ) )

(define-fun ri.add ((p Int) (x RInt) (y RInt)) RInt
  (let ( (l (ri.r_dn p (+ (ri.l x) (ri.l y)))) 
         (u (ri.r_up p (+ (ri.u x) (ri.u y)))) )
    (tpl l u 
      (or (p_nan x) (p_nan y) (and (is_ninf p x) (is_pinf p y)) (and (is_pinf p x) (is_ninf p y))) ) ) )

(define-fun ri.sub ((p Int) (x RInt) (y RInt)) RInt
  (let ( (l (ri.r_dn p (- (ri.l x) (ri.u y)))) 
         (u (ri.r_up p (- (ri.u x) (ri.l y)))) )
    (tpl l u 
      (or (p_nan x) (p_nan y) (and (is_ninf p x) (is_ninf p y)) (and (is_pinf p x) (is_pinf p y))) ) ) )

(define-fun ri.sub_exact ((p Int) (x RInt) (y RInt)) RInt
  (let ( (l (- (ri.l x) (ri.u y))) 
         (u (- (ri.u x) (ri.l y))) )
    (tpl l u 
      (or (p_nan x) (p_nan y) (and (is_ninf p x) (is_ninf p y)) (and (is_pinf p x) (is_pinf p y))) ) ) )

(define-fun ri.mul ((p Int) (x RInt) (y RInt)) RInt
  (ite (>= (ri.l x) 0)
    (ite (= (ri.u x) 0)
      (ite (and (not (is_ninf p y)) (not (is_pinf p y)) (not (p_nan x)) (not (p_nan y)))
        ;; [x] = [0]
        ri.zero
        ;; [x] = [0] and (-inf = [y] or [y] = +inf)
        ri.zero_nan )

      (ite (>= (ri.l y) 0)
        (ite (= (ri.u y) 0)
          ;; 0 <= [x] and [x] != [0] and [y] = [0]
          (ite (and (not (is_pinf p x)) (not (p_nan x)) (not (p_nan y)))
            ri.zero
            ri.zero_nan )

          ;; 0 <= [x] and [x] != [0] and 0 <= [y] and [y] != [0]
          (let ( (l (ri.r_dn p (* (ri.l x) (ri.l y))))
                 (u (ite (or (is_pinf p x) (is_pinf p y)) ri.large_value 
                         (ri.r_up p (* (ri.u x) (ri.u y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.l x) 0) (is_pinf p y)) 
                  (and (is_pinf p x) (= (ri.l y) 0)) ))))

        (ite (<= (ri.u y) 0)
          ;; 0 <= [x] and [x] != [0] and [y] <= 0 and [y] != [0]
          (let ( (l (ite (or (is_pinf p x) (is_ninf p y)) (- ri.large_value) 
                         (ri.r_dn p (* (ri.u x) (ri.l y))) ))
                 (u (ri.r_up p (* (ri.l x) (ri.u y)))) )
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.l x) 0) (is_ninf p y)) 
                  (and (is_pinf p x) (= (ri.u y) 0) ))))

          ;;  0 <= [x] and [x] != [0] and [y] strictly contains 0
          (let ( (l (ite (or (is_pinf p x) (is_ninf p y)) (- ri.large_value) 
                         (ri.r_dn p (* (ri.u x) (ri.l y))) ) )
                 (u (ite (or (is_pinf p x) (is_pinf p y)) ri.large_value
                         (ri.r_up p (* (ri.u x) (ri.u y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_pinf p x) 
                  (and (= (ri.l x) 0) (or (is_ninf p y) (is_pinf p y))) ))))))

    (ite (<= (ri.u x) 0)
      (ite (>= (ri.l y) 0)
        (ite (and (not (is_pinf p y)) (= (ri.u y) 0))
          ;; [x] <= 0 and [x] != [0] and [y] = [0]
          (ite (and (not (is_ninf p x)) (not (p_nan x)) (not (p_nan y)))
            ri.zero
            ri.zero_nan )

          ;; [x] <= 0 and [x] != [0] and 0 <= [y] and [y] != [0]
          (let ( (l (ite (or (is_ninf p x) (is_pinf p y)) (- ri.large_value) 
                         (ri.r_dn p (* (ri.l x) (ri.u y))) ))
                 (u (ri.r_up p (* (ri.u x) (ri.l y)))) )
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.u x) 0) (is_pinf p y)) 
                  (and (is_ninf p x) (= (ri.l y) 0))) ) ) )

        (ite (<= (ri.u y) 0)
          ;; [x] <= 0 and [x] != [0] and [y] <= 0 and [y] != [0]
          (let ( (l (ri.r_dn p (* (ri.u x) (ri.u y))))
                 (u (ite (or (is_ninf p x) (is_ninf p y)) ri.large_value
                         (ri.r_up p (* (ri.l x) (ri.l y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (and (= (ri.u x) 0) (is_ninf p y)) 
                  (and (is_ninf p x) (= (ri.u y) 0)) ))) 

          ;; [x] <= 0 and [x] != [0] and [y] strictly contains 0
          (let ( (l (ite (or (is_ninf p x) (is_pinf p y)) (- ri.large_value) 
                         (ri.r_dn p (* (ri.l x) (ri.u y))) ))
                 (u (ite (or (is_ninf p x) (is_ninf p y)) ri.large_value
                         (ri.r_up p (* (ri.l x) (ri.l y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_ninf p x) (and (= (ri.u x) 0) 
                  (or (is_ninf p y) (is_pinf p y))) )))))

      (ite (>= (ri.l y) 0)
        (ite (= (ri.u y) 0)
          ;; [x] strictly contains 0 and [y] = [0]
          (ite (and (not (is_ninf p x)) (not (is_pinf p x)) (not (p_nan x)) (not (p_nan y)))
            ri.zero
            ri.zero_nan )

          ;; [x] strictly contains 0 and 0 <= [y]
          (let ( (l (ite (or (is_ninf p x) (is_pinf p y)) (- ri.large_value) 
                         (ri.r_dn p (* (ri.l x) (ri.u y))) ))
                 (u (ite (or (is_pinf p x) (is_pinf p y)) ri.large_value
                         (ri.r_up p (* (ri.u x) (ri.u y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_pinf p y) 
                  (and (or (is_ninf p x) (is_pinf p x)) (= (ri.l y) 0)) ))))

        (ite (<= (ri.u y) 0)
          ;; [x] strictly contains 0 and [y] <= 0
          (let ( (l (ite (or (is_pinf p x) (is_ninf p y)) (- ri.large_value) 
                         (ri.r_dn p (* (ri.u x) (ri.l y))) ))
                 (u (ite (or (is_ninf p x) (is_ninf p y)) ri.large_value
                         (ri.r_up p (* (ri.l x) (ri.l y))) )))
            (tpl l u 
              (or (p_nan x) (p_nan y) (is_ninf p y) 
                  (and (or (is_ninf p x) (is_pinf p x)) (= (ri.u y) 0)) )))

          ;; [x] and [y] strictly contains 0
          (let ( (l1 (ite (or (is_ninf p x) (is_pinf p y)) (- ri.large_value) 
                          (ri.r_dn p (* (ri.l x) (ri.u y))) ))
                 (l2 (ite (or (is_pinf p x) (is_ninf p y)) (- ri.large_value)
                          (ri.r_dn p (* (ri.u x) (ri.l y))) ))
                 (u1 (ite (or (is_ninf p x) (is_ninf p y)) ri.large_value
                          (ri.r_up p (* (ri.l x) (ri.l y))) ))
                 (u2 (ite (or (is_pinf p x) (is_pinf p y)) ri.large_value
                          (ri.r_up p (* (ri.u x) (ri.u y))) )))
            (ite (< l1 l2) 
              (ite (> u1 u2)
                (tpl l1 u1 (or (p_nan x) (p_nan y) (is_ninf p x)))

                (tpl l1 u2 (or (p_nan x) (p_nan y) (is_ninf p x) (is_pinf p y))))

              (ite (> u1 u2)
                (tpl l2 u1 (or (p_nan x) (p_nan y) (is_ninf p x) (is_ninf p y)))

                (tpl l2 u2
                  (or (p_nan x) (p_nan y) 
                      (is_ninf p x) (is_pinf p x) (is_ninf p y) (is_pinf p y)) )))))))))

(define-fun ri.div ((p Int) (x RInt) (y RInt)) RInt
  (ite (> (ri.l y) 0)
    (ite (>= (ri.l x) 0)
      ;; 0 < [x] and 0 < [y]
      (let ( (l (ite (is_pinf p y) 0 (ri.r_dn p (/ (ri.l x) (ri.u y)))))
             (u (ite (is_pinf p x) ri.large_value (ri.r_up p (/ (ri.u x) (ri.l y))))) )
        (tpl l u (or (p_nan x) (p_nan y) (and (is_pinf p x) (is_pinf p y)))) )

      (ite (<= (ri.u x) 0)
        ;; [x] <= 0 and 0 < [y]
        (let ( (l (ite (is_ninf p x) (- ri.large_value) (ri.r_dn p (/ (ri.l x) (ri.l y)))))
               (u (ite (is_pinf p y) 0 (ri.r_up p (/ (ri.u x) (ri.u y))))) )
          (tpl l u (or (p_nan x) (p_nan y) (and (is_ninf p x) (is_pinf p y)))) )

        ;; [x] strictly contains 0 and 0 < [y]
        (let ( (l (ite (is_ninf p x) (- ri.large_value) (ri.r_dn p (/ (ri.l x) (ri.l y)))))
               (u (ite (is_pinf p x) ri.large_value (ri.r_up p (/ (ri.u x) (ri.l y))))) )
          (tpl l u (or (p_nan x) (p_nan y) (and (or (is_ninf p x) (is_pinf p x)) (is_pinf p y)))) )))

    (ite (< (ri.u y) 0)
      (ite (>= (ri.l x) 0)
        ;; 0 <= [x] and [y] < 0
        (let ( (l (ite (is_pinf p x) (- ri.large_value) (ri.r_dn p (/ (ri.u x) (ri.u y)))))
               (u (ite (is_ninf p y) 0 (ri.r_up p (/ (ri.l x) (ri.l y))))) )
          (tpl l u (or (p_nan x) (p_nan y) (and (is_pinf p x) (is_ninf p y)))))

        (ite (<= (ri.u x) 0)
          ;; [x] <= 0 and [y] < 0
          (let ( (l (ite (is_ninf p y) 0 (ri.r_dn p (/ (ri.u x) (ri.l y)))))
                 (u (ite (is_ninf p x) ri.large_value (ri.r_up p (/ (ri.l x) (ri.u y))))) )
            (tpl l u (or (p_nan x) (p_nan x) (and (is_ninf p x) (is_ninf p y)))) )

          ;; [x] strictly contains 0 and [y] < 0
          (let ( (l (ite (is_pinf p x) (- ri.large_value) (ri.r_dn p (/ (ri.u x) (ri.u y)))))
                 (u (ite (is_ninf p x) ri.large_value (ri.r_up p (/ (ri.l x) (ri.u y))))) )
            (tpl l u (or (p_nan x) (p_nan x) (and (or (is_ninf p x) (is_pinf p x)) (is_ninf p y)))) )))

      ;; [y] contains 0; results in Entire
      (tpl (- ri.large_value) ri.large_value 
           (or (p_nan x) (p_nan y) (and (or (is_ninf p x) (is_pinf p x)) (or (is_ninf p y) (is_pinf p y))) 
               (and (<= (ri.l x) 0) (<= 0 (ri.u x))) )))))

;;

;; Assignment for non-NaN values.
(define-fun ri.fpis ((p Int) (x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) 
       (= x y) )
) 

;; Assignment.
(define-fun ri.is ((p Int) (x RInt) (y RInt)) Bool
  (= x y) 
) 
'''

rint_prologue_m = '''
;; For positive literals.

(define-fun ri.gt0 ((p Int) (x RInt)) Bool
  (or (is_pinf p x) (> (ri.u x) 0))
)

(define-fun ri.geq0 ((p Int) (x RInt)) Bool
  (and (or (is_pinf p x) (>= (ri.u x) 0)))
)

(define-fun ri.gt ((p Int) (x RInt) (y RInt)) Bool
  (or (is_pinf p x) (is_ninf p y) (ri.gt0 p (ri.sub_exact p x y)))
)

(define-fun ri.geq ((p Int) (x RInt) (y RInt)) Bool
  (or (is_pinf p x) (is_ninf p y) (ri.geq0 p (ri.sub_exact p x y)))
) 

(define-fun ri.fpeq ((p Int) (x RInt) (y RInt)) Bool
  (and (ri.geq p x y) (ri.geq p y x)) 
)

;; For negative literals.

(define-fun ri.lt0 ((p Int) (x RInt)) Bool
  (or (p_nan x) (is_ninf p x) (< (ri.l x) 0))
)

(define-fun ri.leq0 ((p Int) (x RInt)) Bool
  (or (p_nan x) (is_ninf p x) (<= (ri.l x) 0)) 
)

(define-fun ri.lt ((p Int) (x RInt) (y RInt)) Bool
  (or (p_nan x) (p_nan y) (ri.lt0 p (ri.sub_exact p x y)))
)

(define-fun ri.leq ((p Int) (x RInt) (y RInt)) Bool
  (or (p_nan x) (p_nan y) (ri.leq0 p (ri.sub_exact p x y)))
) 

(define-fun ri.fpneq ((p Int) (x RInt) (y RInt)) Bool
  (or (ri.lt p x y) (ri.lt p y x))
)

;; Syntactic equality.

(define-fun ri.eq ((p Int) (x RInt) (y RInt)) Bool
  (or (and (p_nan x) (p_nan y)) (ri.fpeq p x y))
)

(define-fun ri.neq ((p Int) (x RInt) (y RInt)) Bool
  (ri.fpneq p x y)
)
'''

rint_prologue_p = '''
;; For positive literals.

(define-fun ri.gt0 ((p Int) (x RInt)) Bool
  (and (not (p_nan x)) (not (is_ninf p x)) (> (ri.l x) 0))
)

(define-fun ri.geq0 ((p Int) (x RInt)) Bool
  (and (not (p_nan x)) (not (is_ninf p x)) (>= (ri.l x) 0)) 
) 

(define-fun ri.gt ((p Int) (x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) (ri.gt0 p (ri.sub_exact p x y)))
)

(define-fun ri.geq ((p Int) (x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y)) (ri.geq0 p (ri.sub_exact p x y)))
)

(define-fun ri.fpeq ((p Int) (x RInt) (y RInt)) Bool
  (and (not (p_nan x)) (not (p_nan y))
       (= (ri.l x) (ri.u x) (ri.l y) (ri.u y)) )
)

;; For negative literals.

(define-fun ri.lt0 ((p Int) (x RInt)) Bool
  (and (not (is_pinf p x)) (< (ri.u x) 0))
)

(define-fun ri.leq0 ((p Int) (x RInt)) Bool
  (and (not (is_pinf p x)) (<= (ri.u x) 0)) 
) 

(define-fun ri.lt ((p Int) (x RInt) (y RInt)) Bool
  (and (not (is_pinf p x)) (not (is_ninf p y)) 
       (ri.lt0 p (ri.sub_exact p x y)) )
)

(define-fun ri.leq ((p Int) (x RInt) (y RInt)) Bool
  (and (not (is_pinf p x)) (not (is_ninf p y)) 
       (ri.leq0 p (ri.sub_exact p x y)) )
)

(define-fun ri.fpneq ((p Int) (x RInt) (y RInt)) Bool
  (or (ri.lt p x y) (ri.lt p y x))
)

;; Syntactic equality.

(define-fun ri.eq ((p Int) (x RInt) (y RInt)) Bool
  (ri.fpeq p x y)
)

(define-fun ri.neq ((p Int) (x RInt) (y RInt)) Bool
  (and (or (not (p_nan x)) (not (p_nan y))) (ri.fpneq p x y))
)
'''

# eof
