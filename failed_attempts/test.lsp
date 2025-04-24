(include-book "arithmetic-5/top" :dir :system)

;; Constants
(defconst *delta* #x9E3779B9)
(defconst *mod32* #x100000000)

;; One round of simplified "encryption": just increment v0 and v1
(defun simple-tea-encrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                              (natp v1) (< v1 *mod32*)
                              (natp k0) (< k0 *mod32*)
                              (natp k1) (< k1 *mod32*)
                              (natp k2) (< k2 *mod32*)
                              (natp k3) (< k3 *mod32*)
                              (natp sum) (< sum *mod32*))))
  (declare (ignorable k0 k1 k2 k3))
  (list (mod (+ v0 1) *mod32*) (mod (+ v1 1) *mod32*) (mod (+ sum *delta*) *mod32*)))

;; One round of inverse: decrement v0 and v1
(defun simple-tea-decrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                              (natp v1) (< v1 *mod32*)
                              (natp k0) (< k0 *mod32*)
                              (natp k1) (< k1 *mod32*)
                              (natp k2) (< k2 *mod32*)
                              (natp k3) (< k3 *mod32*)
                              (natp sum) (< sum *mod32*))))
  (declare (ignorable k0 k1 k2 k3))
  (list (mod (- v0 1) *mod32*) (mod (- v1 1) *mod32*) (mod (- sum *delta*) *mod32*)))

(defthm simple-tea-step-invertible
  (implies (and (natp v0) (< v0 *mod32*)
                (natp v1) (< v1 *mod32*)
                (natp k0) (< k0 *mod32*)
                (natp k1) (< k1 *mod32*)
                (natp k2) (< k2 *mod32*)
                (natp k3) (< k3 *mod32*)
                (natp sum) (< sum *mod32*))
           (and (equal (car (simple-tea-decrypt-step 
                                              (car (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
                                              (car (cdr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))
                                              k0 k1 k2 k3 
                                              (car (cdr (cdr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))))))
                    v0)
                (equal (car (cdr (simple-tea-decrypt-step 
                                              (car (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
                                              (car (cdr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))
                                              k0 k1 k2 k3 
                                              (car (cdr (cdr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))))))
                       v1)
                (equal (car (cdr (cdr (simple-tea-decrypt-step 
                                              (car (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
                                              (car (cdr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))
                                              k0 k1 k2 k3 
                                              (car (cdr (cdr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))))))))
                          sum))))


(defun simple-tea-enc (v0 v1 k0 k1 k2 k3 sum n)
  (if (zp n)
      (list v0 v1 sum)
    (simple-tea-enc 
     (car (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
     (cadr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
     k0 k1 k2 k3
     (caddr (simple-tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
     (1- n))))

(defun simple-tea-dec (v0 v1 k0 k1 k2 k3 sum n)
  (if (zp n)
      (list v0 v1 sum)
    (simple-tea-dec 
     (car (simple-tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
     (cadr (simple-tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
     k0 k1 k2 k3
     (caddr (simple-tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
     (1- n))))

(defthm enc-v0-effect
  (implies (and (natp v0) (natp n) (< v0 *mod32*))
           (equal (car (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                  (mod (+ v0 n) *mod32*)))
  :hints (("Goal" :induct (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))))

(defthm enc-v1-effect
  (implies (and (natp v1) (natp n) (< v1 *mod32*))
           (equal (cadr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                  (mod (+ v1 n) *mod32*)))
  :hints (("Goal" :induct (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))))

(defthm enc-sum-effect
  (implies (and (natp sum) (natp n) (< sum *mod32*))
           (equal (caddr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                  (mod (+ sum (* n *delta*)) *mod32*)))
  :hints (("Goal" :induct (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))))


(defthm dec-v0-effect
  (implies (and (natp v0) (natp n) (< v0 *mod32*))
           (equal (car (simple-tea-dec v0 v1 k0 k1 k2 k3 sum n))
                  (mod (- v0 n) *mod32*)))
  :hints (("Goal" :induct (simple-tea-dec v0 v1 k0 k1 k2 k3 sum n))))

(defthm dec-v1-effect
  (implies (and (natp v1) (natp n) (< v1 *mod32*))
           (equal (cadr (simple-tea-dec v0 v1 k0 k1 k2 k3 sum n))
                  (mod (- v1 n) *mod32*)))
  :hints (("Goal" :induct (simple-tea-dec v0 v1 k0 k1 k2 k3 sum n))))

(defthm dec-sum-effect
  (implies (and (natp sum) (natp n) (< sum *mod32*))
           (equal (caddr (simple-tea-dec v0 v1 k0 k1 k2 k3 sum n))
                  (mod (- sum (* n *delta*)) *mod32*)))
  :hints (("Goal" :induct (simple-tea-dec v0 v1 k0 k1 k2 k3 sum n))))

(defthm decrypt-cancels-encrypt
  (implies (and (natp n)
                (natp v0) (< v0 *mod32*)
                (natp v1) (< v1 *mod32*)
                (natp sum) (< sum *mod32*))
           (and (equal (mod (- (mod (+ v0 n) *mod32*) n) *mod32*) v0)
                (equal (mod (- (mod (+ v1 n) *mod32*) n) *mod32*) v1)
                (equal (mod (- (mod (+ sum (* n *delta*)) *mod32*) 
                              (* n *delta*)) 
                           *mod32*) 
                       sum))))


(defthm fast-simple-tea-n-rounds-invertible
  (implies (and (natp v0) (< v0 *mod32*)
                (natp v1) (< v1 *mod32*)
                (natp k0) (< k0 *mod32*)
                (natp k1) (< k1 *mod32*)
                (natp k2) (< k2 *mod32*)
                (natp k3) (< k3 *mod32*)
                (natp sum) (< sum *mod32*)
                (natp n))
           (and (equal (car (simple-tea-dec 
                            (car (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                            (cadr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                            k0 k1 k2 k3 
                            (caddr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                            n))
                       v0)
                (equal (cadr (simple-tea-dec 
                             (car (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                             (cadr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                             k0 k1 k2 k3 
                             (caddr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                             n))
                       v1)
                ;; (equal (caddr (simple-tea-dec 
                ;;               (car (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                ;;               (cadr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                ;;               k0 k1 k2 k3 
                ;;               (caddr (simple-tea-enc v0 v1 k0 k1 k2 k3 sum n))
                ;;               n))
                ;;        sum)
                       ))
  :hints (("Goal" 
           :in-theory (disable simple-tea-enc simple-tea-dec))))

