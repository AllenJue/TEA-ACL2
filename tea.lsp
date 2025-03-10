(include-book "arithmetic-5/top" :dir :system)

(include-book "kestrel/bv/logxor" :dir :system)   ;; Bitwise XOR
(include-book "kestrel/bv/bvshl" :dir :system)   ;; Bitwise Shift Left
(include-book "kestrel/bv/bvshr" :dir :system)   ;; Bitwise Shift Right


;; helpful lemmas
(defthm add-mod-preserves-invariant
  (implies (and (natp x) (< x #x100000000)
                (natp y) (< y #x100000000))
           (and (natp (mod (+ x y) #x100000000))
                (< (mod (+ x y) #x100000000) #x100000000))))

(defthm subtract-mod-preserves-invariant
  (implies (and (natp x) (< x #x100000000)
                (natp y) (< y #x100000000))
           (and (natp (mod (- x y) #x100000000))
                (< (mod (- x y) #x100000000) #x100000000))))

(defthm right-shift-is-non-negative
  (implies (and (natp x) (< x #x100000000)
                (natp n))
           (natp (mod (ash x (- n)) #x100000000))))

(defthm right-shift-is-bounded
  (implies (and (natp x) (< x #x100000000)
                (natp n))
           (< (mod (ash x (- n)) #x100000000) #x100000000)))

(defthm right-shift-preserves-invariant
  (implies (and (natp x) (< x #x100000000)
                (natp n))
           (and (natp (mod (ash x (- n)) #x100000000))
                (< (mod (ash x (- n)) #x100000000) #x100000000)))
  :hints (("Goal" :use ((:instance right-shift-is-non-negative
                                  (x x) (n n))
                        (:instance right-shift-is-bounded
                                  (x x) (n n))))))
(defthm left-shift-is-non-negative
  (implies (and (natp x) (< x #x100000000)
                (natp n))
           (natp (mod (ash x n) #x100000000))))

(defthm left-shift-is-bounded
  (implies (and (natp x) (< x #x100000000)
                (natp n))
           (< (mod (ash x n) #x100000000) #x100000000)))

(defthm left-shift-preserves-invariant
  (implies (and (natp x) (< x #x100000000)
                (natp n))
           (and (natp (mod (ash x n) #x100000000))
                (< (mod (ash x n) #x100000000) #x100000000)))
  :hints (("Goal" :use ((:instance left-shift-is-non-negative
                                  (x x) (n n))
                        (:instance left-shift-is-bounded
                                  (x x) (n n))))))

(defthm logxor-mod-preserves-invariant
  (implies (and (natp x) (< x #x100000000)
                (natp y) (< y #x100000000))
           (and (natp (mod (logxor x y) #x100000000))
                (< (mod (logxor x y) #x100000000) #x100000000))))

(defun tea-encrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp sum))))
  "Performs one step of TEA encryption."
  (let* ((sum  (mod (+ sum #x9E3779B9) #x100000000))
         (v0   (mod (+ v0 (logxor (+ (ash v1 4) k0)
                                  (+ v1 sum)
                                  (+ (ash v1 -5) k1)))
                    #x100000000))
         (v1   (mod (+ v1 (logxor (+ (ash v0 4) k2)
                                  (+ v0 sum)
                                  (+ (ash v0 -5) k3)))
                    #x100000000)))
    (mv v0 v1 sum)))

(defun tea-decrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp sum))))
  "Performs one step of TEA decryption."
  (let* ((v1 (mod (- v1 (logxor (+ (ash v0 4) k2)
                                (+ v0 sum)
                                (+ (ash v0 -5) k3)))
                  #x100000000))
         (v0 (mod (- v0 (logxor (+ (ash v1 4) k0)
                                (+ v1 sum)
                                (+ (ash v1 -5) k1)))
                  #x100000000))
         (sum (mod (- sum #x9E3779B9) #x100000000)))
    (mv v0 v1 sum)))

(defun tea-encrypt (v0 v1 k0 k1 k2 k3 rounds sum)
  "Recursive TEA encryption function, applying 32 rounds."
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds) (natp sum))))
  (if (zp rounds)
      (mv v0 v1)
    (mv-let (new-v0 new-v1 new-sum)
        (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)
      (tea-encrypt new-v0 new-v1 k0 k1 k2 k3 (- rounds 1) new-sum))))

(defun tea-decrypt (v0 v1 k0 k1 k2 k3 rounds sum)
  "Recursive TEA decryption function, applying 32 rounds."
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds) (natp sum))))
  (if (zp rounds)
      (mv v0 v1)
    (mv-let (new-v0 new-v1 new-sum)
        (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)
      (tea-decrypt new-v0 new-v1 k0 k1 k2 k3 (- rounds 1) new-sum))))

(defun tea-encrypt-wrapper (v0 v1 k0 k1 k2 k3)
  "Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key."
  (tea-encrypt v0 v1 k0 k1 k2 k3 32 0))  ;; Start with sum = 0

(defun tea-decrypt-wrapper (v0 v1 k0 k1 k2 k3)
  "Wrapper to decrypt a 64-bit block (v0, v1) with a 128-bit key."
  (tea-decrypt v0 v1 k0 k1 k2 k3 32 #xC6EF3720))  ;; Start with sum = 0xC6EF3720

(defthm test-case-1
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #x12345678 #x9ABCDEF0
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #x12345678 #x9ABCDEF0)))

(defthm test-case-1.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x12345678 #x9ABCDEF0
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x12345678 #x9ABCDEF0))))


(defthm test-case-2
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #xDEADBEEF #xCAFEBABE
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #xDEADBEEF #xCAFEBABE)))

(defthm test-case-2.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #xDEADBEEF #xCAFEBABE
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #xDEADBEEF #xCAFEBABE))))

(defthm test-case-3
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #x9ABCDEF0 #x12345678)))

(defthm test-case-3.3
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x9ABCDEF0 #x12345678))))

;;;; Need to show that encrypt + decrypt gives original value

(defthm tea-step-invertible
  (implies (and (natp v0) (< v0 #x100000000)
                (natp v1) (< v1 #x100000000)
                (natp k0) (< k0 #x100000000)
                (natp k1) (< k1 #x100000000)
                (natp k2) (< k2 #x100000000)
                (natp k3) (< k3 #x100000000)
                (natp sum) (< sum #x100000000))
           (mv-let (v0-new v1-new sum-new)
             (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)
             (mv-let (v0-final v1-final sum-final)
               (tea-decrypt-step v0-new v1-new k0 k1 k2 k3 sum-new)
               (and (equal v0-final v0)
                    (equal v1-final v1)
                    (equal sum-final sum))))))

;; (defthm tea-encrypt-preserves-32bit
;;   (implies (and (natp v0) (< v0 #x100000000)
;;                 (natp v1) (< v1 #x100000000)
;;                 (natp k0) (< k0 #x100000000)
;;                 (natp k1) (< k1 #x100000000)
;;                 (natp k2) (< k2 #x100000000)
;;                 (natp k3) (< k3 #x100000000)
;;                 (natp sum) (< sum #x100000000))
  
;;   (mv-let (cipher-l cipher-r)
;;             (tea-encrypt v0 v1 k0 k1 k2 k3 1 sum)
;;             (and (natp cipher-l) (< cipher-l #x100000000)
;;                  (natp cipher-r) (< cipher-r #x100000000)))))

;; ;; (defthm tea-decrypt-step-preserves-32bit-v0
;; ;;   (implies (and (natp v0) (< v0 #x100000000)
;; ;;                 (natp v1) (< v1 #x100000000)
;; ;;                 (natp k0) (< k0 #x100000000)
;; ;;                 (natp k1) (< k1 #x100000000)
;; ;;                 (natp k2) (< k2 #x100000000)
;; ;;                 (natp k3) (< k3 #x100000000)
;; ;;                 (natp sum) (< sum #x100000000))
;; ;;            (and (natp (mod (- v0 (logxor (+ (ash v1 4) k0)
;; ;;                                           (+ v1 sum)
;; ;;                                           (+ (ash v1 -5) k1)))
;; ;;                          #x100000000))
;; ;;                 (< (mod (- v0 (logxor (+ (ash v1 4) k0)
;; ;;                                       (+ v1 sum)
;; ;;                                       (+ (ash v1 -5) k1)))
;; ;;                         #x100000000) #x100000000))))

;; (defthm sum-update-preserves-32bit
;;   (implies (natp sum)
;;            (and (natp (mod (+ sum #x9E3779B9) #x100000000))
;;                 (< (mod (+ sum #x9E3779B9) #x100000000) #x100000000))))


;; (defthm xor-involution
;;   (implies (and (natp x) (< x #x100000000)
;;                 (natp y) (< y #x100000000))
;;            (equal (logxor (logxor x y) y) x)))


;; (defthm sum-cancellation
;;   (implies (and (natp sum) (< sum #x100000000)
;;                 (natp delta) (< delta #x100000000))
;;   (equal (- (+ sum delta) delta) sum)))

;; ;; try showing one round is invertible?
;; (defthm tea-step-invertible
;;   (implies (and (natp v0) (< v0 #x100000000)
;;                 (natp v1) (< v1 #x100000000)
;;                 (natp k0) (< k0 #x100000000)
;;                 (natp k1) (< k1 #x100000000)
;;                 (natp k2) (< k2 #x100000000)
;;                 (natp k3) (< k3 #x100000000)
;;                 (natp sum) (< sum #x100000000))
;;            (mv-let (cipher-l cipher-r)
;;             (tea-encrypt-wrapper v0 v1 k0 k1 k2 k3)
;;               (mv-let (plain-l plain-r)
;;                 (tea-decrypt-wrapper cipher-l cipher-r k0 k1 k2 k3)
;;                   (and (equal plain-l v0)
;;                       (equal plain-r v1))))))

;; ;; maybe try showing the rest is invertible
;; (defthm tea-invertible
;;   (implies (and (natp v0) (< v0 #x100000000)
;;                 (natp v1) (< v1 #x100000000)
;;                 (natp k0) (< k0 #x100000000)
;;                 (natp k1) (< k1 #x100000000)
;;                 (natp k2) (< k2 #x100000000)
;;                 (natp k3) (< k3 #x100000000)
;;                 (natp sum) (< sum #x100000000))
;;            (mv-let (cipher-l cipher-r)
;;             (tea-encrypt-wrapper v0 v1 k0 k1 k2 k3)
;;               (mv-let (plain-l plain-r)
;;                 (tea-decrypt-wrapper cipher-l cipher-r k0 k1 k2 k3)
;;                   (and (equal plain-l v0)
;;                       (equal plain-r v1))))))

