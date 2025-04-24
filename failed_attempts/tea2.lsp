(include-book "arithmetic-5/top" :dir :system)


(defun tea-encrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp sum) (< sum #x100000000))))
  ;; Performs one step of TEA encryption.
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
                              (natp sum) (< sum #x100000000))))
  ; Performs one step of TEA decryption.
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

;; (2654435755 3689468442 2654435769)


(defthm tea-step-invertible
  (implies (and (natp v0) (< v0 #x100000000)
                (natp v1) (< v1 #x100000000)
                (natp k0) (< k0 #x100000000)
                (natp k1) (< k1 #x100000000)
                (natp k2) (< k2 #x100000000)
                (natp k3) (< k3 #x100000000)
                (natp sum) (< sum #x100000000))
            ;; save the results of 1 step of encryption
           (mv-let (v0-new v1-new sum-new)
             (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)
             ;; save the results of 1 step of decryption with the new values
             (mv-let (v0-final v1-final sum-final)
               (tea-decrypt-step v0-new v1-new k0 k1 k2 k3 sum-new)
               (and (equal v0-final v0)
                    (equal v1-final v1)
                    (equal sum-final sum))))))

(defun tea-encrypt (v0 v1 k0 k1 k2 k3 rounds sum)
  (declare (xargs :measure (nfix rounds)
                  :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds)
                              (natp sum) (< sum #x100000000))))
  (if (zp rounds)
      (mv v0 v1 sum)
    (mv-let (new-v0 new-v1 new-sum)
      (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)
      (tea-encrypt new-v0 new-v1 k0 k1 k2 k3 (- rounds 1) new-sum))))

(defun tea-decrypt (v0 v1 k0 k1 k2 k3 rounds sum)
  (declare (xargs :measure (nfix rounds)
                  :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds)
                              (natp sum) (< sum #x100000000))
                  :verify-guards nil))
  (if (zp rounds)
      (mv v0 v1 sum)
    (mv-let (new-v0 new-v1 new-sum)
      ;; (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)
      ;; (tea-decrypt new-v0 new-v1 k0 k1 k2 k3 (- rounds 1) new-sum)
      (tea-decrypt v0 v1 k0 k1 k2 k3 (- rounds 1) sum)
      (tea-decrypt-step new-v0 new-v1 k0 k1 k2 k3 new-sum)
      )))


;; (defun tea-encrypt (v0 v1 k0 k1 k2 k3 rounds sum) ...)

(defun tea-encrypt-wrapper (v0 v1 k0 k1 k2 k3)
  ;; Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key and return the final step.
    (tea-encrypt v0 v1 k0 k1 k2 k3 32 0))


(defun tea-decrypt-wrapper (v0 v1 k0 k1 k2 k3)
  ;; Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key and return the final step.
    (tea-decrypt v0 v1 k0 k1 k2 k3 32 #xC6EF3720))


(defthmd test-case-1
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #x12345678 #x9ABCDEF0
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #x12345678 #x9ABCDEF0)))

;; Show that (enc #x12345678 #x9ABCDEF0) != #x12345678 #x9ABCDEF0
(defthmd test-case-1.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x12345678 #x9ABCDEF0
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x12345678 #x9ABCDEF0))))

;; Show that (enc (dec #xDEADBEEF #xCAFEBABE)) = #xDEADBEEF #xCAFEBABE
(defthmd test-case-2
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #xDEADBEEF #xCAFEBABE
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #xDEADBEEF #xCAFEBABE)))

;; Show that (enc #xDEADBEEF #xCAFEBABE) != #xDEADBEEF #xCAFEBABE
(defthmd test-case-2.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #xDEADBEEF #xCAFEBABE
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #xDEADBEEF #xCAFEBABE))))

;; Show that (enc (dec #x9ABCDEF0 #x12345678)) = #x9ABCDEF0 #x12345678
(defthmd test-case-3
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #x9ABCDEF0 #x12345678)))

;; Show that (enc #x9ABCDEF0 #x12345678) != #x9ABCDEF0 #x12345678
(defthmd test-case-3.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x9ABCDEF0 #x12345678))))

;; (in-theory (disable tea-encrypt-step))
;; (in-theory (disable tea-decrypt-step))

;; (in-theory (enable tea-encrypt-step))
;; (in-theory (enable tea-decrypt-step))


(defthm tea-encrypt-decrypt-inverse
  (implies (and (natp v0) (< v0 #x100000000)
                (natp v1) (< v1 #x100000000)
                (natp k0) (< k0 #x100000000)
                (natp k1) (< k1 #x100000000)
                (natp k2) (< k2 #x100000000)
                (natp k3) (< k3 #x100000000)
                (natp rounds)
                (natp sum) (< sum #x100000000))
    (mv-let (e0 e1 esum)
        (tea-encrypt v0 v1 k0 k1 k2 k3 rounds sum)
      (mv-let (d0 d1 dsum)
          (tea-decrypt e0 e1 k0 k1 k2 k3 rounds esum)
        (declare (ignorable dsum))
        (and (equal d0 v0)
             (equal d1 v1)))))
  :hints (("Goal" :induct (tea-encrypt v0 v1 k0 k1 k2 k3 rounds sum)))
  )
