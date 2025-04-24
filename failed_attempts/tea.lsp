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

(defun tea-encrypt (v0 v1 k0 k1 k2 k3 rounds sum history)
  ;; Recursive TEA encryption function, applying 32 rounds.
  ;; Saves the BEFORE-state at each step. At the end, saves final state.
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds) 
                              (natp sum) (< sum #x100000000)
                              (true-listp history))))
  (if (zp rounds)
      ;; Save final encrypted state explicitly at end
      (cons (list v0 v1 sum) history)
    ;; Save current BEFORE-state, then recurse
    (mv-let (new-v0 new-v1 new-sum)
        (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)
      (tea-encrypt new-v0 new-v1 k0 k1 k2 k3 
                   (- rounds 1) 
                   new-sum 
                   (cons (list v0 v1 sum) history)))))


(defun tea-decrypt (v0 v1 k0 k1 k2 k3 rounds sum history)
  ;; Recursive TEA decryption function, applying 32 rounds.
  ;; Saves the BEFORE-state at each step. At the end, saves final state.
  (declare (xargs :guard (and (natp v0) (< v0 #x100000000)
                              (natp v1) (< v1 #x100000000)
                              (natp k0) (< k0 #x100000000)
                              (natp k1) (< k1 #x100000000)
                              (natp k2) (< k2 #x100000000)
                              (natp k3) (< k3 #x100000000)
                              (natp rounds) 
                              (natp sum) (< sum #x100000000)
                              (true-listp history))))
  (if (zp rounds)
      ;; Save final decrypted state explicitly at end
      (cons (list v0 v1 sum) history)
    ;; Save current BEFORE-state, then recurse
    (mv-let (new-v0 new-v1 new-sum)
        (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)
      (tea-decrypt new-v0 new-v1 k0 k1 k2 k3 
                   (- rounds 1) 
                   new-sum 
                   (cons (list v0 v1 sum) history)))))


(defun tea-encrypt-wrapper (v0 v1 k0 k1 k2 k3)
  ;; Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key and return the final step.
  (let ((last-step (car (tea-encrypt v0 v1 k0 k1 k2 k3 32 0 nil))))
    (mv (first last-step) (second last-step))))


(defun tea-decrypt-wrapper (v0 v1 k0 k1 k2 k3)
  ;; Wrapper to decrypt a 64-bit block (v0, v1) with a 128-bit key.
  ;; Start with sum = 0xC6EF3720, it is 32x the delta added to the start
  (let ((last-step (car (tea-decrypt v0 v1 k0 k1 k2 k3 32 #xC6EF3720 nil)))) 
    (mv (first last-step) (second last-step)))) 

;; Show that (enc (dec #x12345678 #x9ABCDEF0)) = #x12345678 #x9ABCDEF0
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
(defthm test-case-3.2
  (not (equal (mv-let (cipher-l cipher-r)
                 (tea-encrypt-wrapper #x9ABCDEF0 #x12345678
                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
               (list cipher-l cipher-r))
              (list #x9ABCDEF0 #x12345678))))

;; (defthm tea-encrypt-decrypt-test
;;   (implies (and (natp v0) (< v0 #x100000000)
;;                 (natp v1) (< v1 #x100000000))
;;            (mv-let (cipher-l cipher-r)
;;                (tea-encrypt-wrapper v0 v1
;;                                     #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
;;              (mv-let (plain-l plain-r)
;;                  (tea-decrypt-wrapper cipher-l cipher-r
;;                                       #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)
;;                (equal (list plain-l plain-r)
;;                       (list v0 v1))))))


;;;; Need to show that encrypt + decrypt of a single step gives original value
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

;; UNPROVEN

(defthm tea-encrypt-decrypt-invertible
  (implies (and (natp v0) (< v0 #x100000000)
                (natp v1) (< v1 #x100000000)
                (natp k0) (< k0 #x100000000)
                (natp k1) (< k1 #x100000000)
                (natp k2) (< k2 #x100000000)
                (natp k3) (< k3 #x100000000))
           (mv-let (cipher-l cipher-r)
               (tea-encrypt-wrapper v0 v1 k0 k1 k2 k3)
             (mv-let (plain-l plain-r)
                 (tea-decrypt-wrapper cipher-l cipher-r k0 k1 k2 k3)
               (equal (list plain-l plain-r)
                      (list v0 v1))))))


;; (in-theory (disable tea-encrypt-step))
;; (in-theory (disable tea-decrypt-step))

;; want to maybe show unrolling encrypt, decrypt
;; then want to show that can undo the unrolled? Cancellation in the history...?
;; final theorem?


;; I'M pretty sure this is provable, but it just takes a long time...

;; (defthm tea-two-step-invertible
;;   (implies (and (natp v0) (< v0 #x100000000)
;;                 (natp v1) (< v1 #x100000000)
;;                 (natp k0) (< k0 #x100000000)
;;                 (natp k1) (< k1 #x100000000)
;;                 (natp k2) (< k2 #x100000000)
;;                 (natp k3) (< k3 #x100000000)
;;                 (natp sum) (< sum #x100000000))
;;            (mv-let (v0-step1 v1-step1 sum-step1)
;;                (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)
;;              (mv-let (v0-step2 v1-step2 sum-step2)
;;                  (tea-encrypt-step v0-step1 v1-step1 k0 k1 k2 k3 sum-step1)
;;                (mv-let (v0-step3 v1-step3 sum-step3)
;;                    (tea-decrypt-step v0-step2 v1-step2 k0 k1 k2 k3 sum-step2)
;;                  (mv-let (v0-final v1-final sum-final)
;;                      (tea-decrypt-step v0-step3 v1-step3 k0 k1 k2 k3 sum-step3)
;;                    (and (equal v0-final v0)
;;                         (equal v1-final v1)
;;                         (equal sum-final sum))))))))
