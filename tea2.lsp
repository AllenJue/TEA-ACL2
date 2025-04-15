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

;; (defthm tea-decrypt-step-equivalence
;;   (implies (and (true-listp x) (= (len x) 7)
;;                 (natp (nth 0 x)) (< (nth 0 x) #x100000000)
;;                 (natp (nth 1 x)) (< (nth 1 x) #x100000000)
;;                 (natp (nth 2 x)) (< (nth 2 x) #x100000000)
;;                 (natp (nth 3 x)) (< (nth 3 x) #x100000000)
;;                 (natp (nth 4 x)) (< (nth 4 x) #x100000000)
;;                 (natp (nth 5 x)) (< (nth 5 x) #x100000000)
;;                 (natp (nth 6 x)) (< (nth 6 x) #x100000000))
;;            ;; Compare outputs of both implementations.
;;            (equal 
;;             ;; New implementation: list-based.
;;             (tea-decrypt-step x)
;;             ;; Original implementation: argument-based.
;;             (let ((v0  (nth 0 x))
;;                   (v1  (nth 1 x))
;;                   (k0  (nth 2 x))
;;                   (k1  (nth 3 x))
;;                   (k2  (nth 4 x))
;;                   (k3  (nth 5 x))
;;                   (sum (nth 6 x)))
;;               ;; Call the argument-based implementation with unpacked values.
;;               (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)))))

(defun tea-encrypt (v0 v1 k0 k1 k2 k3 rounds sum)
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
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
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds)
                              (natp sum) (< sum #x100000000))
                  :verify-guards t))
  (if (zp rounds)
      (mv v0 v1 sum)
    (mv-let (new-v0 new-v1 new-sum)
      (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)
      (tea-decrypt new-v0 new-v1 k0 k1 k2 k3 (- rounds 1) new-sum))))

;; (defun tea-encrypt (v0 v1 k0 k1 k2 k3 rounds sum) ...)

(defun tea-encrypt-wrapper (v0 v1 k0 k1 k2 k3)
  ;; Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key and return the final step.
    (tea-encrypt v0 v1 k0 k1 k2 k3 32 0))


(defun tea-decrypt-wrapper (v0 v1 k0 k1 k2 k3)
  ;; Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key and return the final step.
    (tea-decrypt v0 v1 k0 k1 k2 k3 32 #xC6EF3720))


(defthm test-case-1
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #x12345678 #x9ABCDEF0
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #x12345678 #x9ABCDEF0)))

;; Show that (enc #x12345678 #x9ABCDEF0) != #x12345678 #x9ABCDEF0
(defthm test-case-1.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x12345678 #x9ABCDEF0
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x12345678 #x9ABCDEF0))))

;; Show that (enc (dec #xDEADBEEF #xCAFEBABE)) = #xDEADBEEF #xCAFEBABE
(defthm test-case-2
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #xDEADBEEF #xCAFEBABE
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #xDEADBEEF #xCAFEBABE)))

;; Show that (enc #xDEADBEEF #xCAFEBABE) != #xDEADBEEF #xCAFEBABE
(defthm test-case-2.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #xDEADBEEF #xCAFEBABE
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #xDEADBEEF #xCAFEBABE))))

;; Show that (enc (dec #x9ABCDEF0 #x12345678)) = #x9ABCDEF0 #x12345678
(defthm test-case-3
  (equal (mv-let (cipher-l cipher-r)
            (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
          (mv-let (plain-l plain-r)
              (tea-decrypt-wrapper cipher-l cipher-r
                #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
            (list plain-l plain-r)))
          (list #x9ABCDEF0 #x12345678)))

;; Show that (enc #x9ABCDEF0 #x12345678) != #x9ABCDEF0 #x12345678
(defthm test-case-3.3
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x9ABCDEF0 #x12345678))))

(in-theory (disable tea-encrypt-step))
(in-theory (disable tea-decrypt-step))

;; (in-theory (enable tea-encrypt-step))
;; (in-theory (enable tea-decrypt-step))

(defthm tea-encrypt-decrypt-invertible
  (implies (and (natp v0) (< v0 #x100000000)
                (natp v1) (< v1 #x100000000)
                (natp k0) (< k0 #x100000000)
                (natp k1) (< k1 #x100000000)
                (natp k2) (< k2 #x100000000)
                (natp k3) (< k3 #x100000000)
                (natp rounds)
                (natp sum) (< sum #x100000000) (natp (- sum #x9E3779B9)))
           (mv-let (cipher-l cipher-r cipher-sum)
             (tea-encrypt v0 v1 0 0 0 0 rounds sum)
             (mv-let (plain-l plain-r plain-sum)
               (tea-decrypt cipher-l cipher-r 0 0 0 0 rounds cipher-sum)
               (declare (ignore plain-l plain-r)) 
               (equal plain-sum sum))))
  :hints (("Goal" :induct (tea-encrypt v0 v1 k0 k1 k2 k3 rounds sum))))

