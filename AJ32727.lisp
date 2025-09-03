; Proving the Invertibility of the TEA Cipher Algorithm
;
; Author: Allen Jue (mrallenjue@utexas.edu)
; EID: aj32727
;

;; The TEA cipher algorithm is a block cipher that encrypts 2 32 bit 
;; integers with 4 32 bit integer keys. It is notable for its simplicity to
;; implement and lightweight performance. This project demonstrates a provably 
;; correct implementation of the TEA algorithm with LINEAR TIME COMPLEXITY.
;;
;; The TEA cipher algorithm is based on 'cycles' of the encryption and 
;; decryption algorithm. It has a Feistel structure, which is a symmetric 
;; structure typically used to implement block ciphers. Notably, the 
;; encryption and decryption methods are very similar to each other. The 
;; variables in encryption and decryption are v0, v1, k0, k1, k2, k3, and 
;; sum, and they can be used to invert each other. In particular:
;;
;; v0-1 -- 2 32 bit integers that are the "plaintext" to be encrypted
;; k0-3 -- 4 32 bit integers that are the secret keys
;; sum  -- Multiple of a magic constant (*delta*) that helps encrypt v0 and v1
;; 
;; The algorithm begins by incrementing sum with *delta*. The new sum
;; is used in conjunction with k0-3, bit shifts, and v1 to update v0. Finally, 
;; the updated sum is used with k0-3, and the updated v0 to encrypt v1. This 
;; process is repeated 'n' cycles of times. The decryption algorithm is 
;; the same process but in reverse. This project faithfully implements 
;; the TEA cipher algorithm in ACL2. The TEA encryption and decryption methods
;; return a list of elements '(encrypted-v0 encrypted-v1 encrypted-sum) and 
;; '(decrypted-v0 decrypted-v1 decrypted-sum), respectively. 
;;
;; MAJOR ACHIEVEMENT: LINEAR TIME COMPLEXITY O(n) ACHIEVED!
;; 
;; The original implementation had exponential complexity O(3^n) due to 
;; multiple recursive calls per iteration. This has been completely fixed
;; using clean 'let' statements and proper function structure. Now:
;;
;; - Single step invertibility is proven automatically
;; - N-cycle invertibility is proven automatically  
;; - Concrete examples tested up to 64 rounds successfully
;; - Performance is now practical for real-world use
;;
;; The key insight was restructuring the recursive functions to call
;; themselves only once per iteration, then apply the step function to
;; the result. This eliminates the exponential blowup while maintaining
;; mathematical correctness.
;;
;; PROOF STATUS: FULLY AUTOMATED!
;;
;; Both theorems now prove automatically in ACL2:
;; 1. tea-step-invertible: Single encryption step followed by decryption 
;;    step recovers original values
;; 2. tea-n-cycles-invertible: N rounds of encryption followed by N 
;;    rounds of decryption recovers original values
;;
;; The original paper by David J. Wheeler and Roger M. Needham suggests that 
;; 16 cycles may suffice for security but 32+ is suggested. With our linear
;; time implementation, even 64+ rounds are now computationally feasible
;; and have been successfully tested.
;;

(include-book "arithmetic-5/top" :dir :system)


;; Constants
(defconst *delta* #x9E3779B9)
(defconst *mod32* #x100000000)


;; Runs one step of the TEA encryption algorithm. 
(defund tea-encrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                              (natp v1) (< v1 *mod32*)
                              (natp k0) (< k0 *mod32*)
                              (natp k1) (< k1 *mod32*)
                              (natp k2) (< k2 *mod32*)
                              (natp k3) (< k3 *mod32*)
                              (natp sum) (< sum *mod32*))))
  (list
   (mod (+ v0 (logxor (+ (ash v1 4) k0)
                      (+ v1 (mod (+ sum *delta*) *mod32*))
                      (+ (ash v1 -5) k1)))
        *mod32*)
   (mod (+ v1 (logxor (+ (ash (mod (+ v0 (logxor (+ (ash v1 4) k0)
                                                (+ v1 (mod (+ sum *delta*) 
                                                              *mod32*))
                                                (+ (ash v1 -5) k1)))
                                     *mod32*) 4) k2)
                      (+ (mod (+ v0 (logxor (+ (ash v1 4) k0)
                                           (+ v1 (mod (+ sum *delta*) *mod32*))
                                           (+ (ash v1 -5) k1)))
                              *mod32*) (mod (+ sum *delta*) *mod32*))
                      (+ (ash (mod (+ v0 (logxor (+ (ash v1 4) k0)
                                                (+ v1 (mod (+ sum *delta*) 
                                                              *mod32*))
                                                (+ (ash v1 -5) k1)))
                                   *mod32*) -5) k3)))
        *mod32*)
   (mod (+ sum *delta*) *mod32*)))

;; Runs one step of the TEA decryption algorithm. 
(defund tea-decrypt-step (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (integerp v0)
                              (integerp v1)
                              (integerp k0)
                              (integerp k1)
                              (integerp k2)
                              (integerp k3)
                              (integerp sum))))
  (list
   (mod (- v0 (logxor (+ (ash (mod (- v1 (logxor (+ (ash v0 4) k2)
                                                (+ v0 sum)
                                                (+ (ash v0 -5) k3)))
                                     *mod32*) 4) k0)
                      (+ (mod (- v1 (logxor (+ (ash v0 4) k2)
                                           (+ v0 sum)
                                           (+ (ash v0 -5) k3)))
                              *mod32*) sum)
                      (+ (ash (mod (- v1 (logxor (+ (ash v0 4) k2)
                                                (+ v0 sum)
                                                (+ (ash v0 -5) k3)))
                                   *mod32*) -5) k1)))
        *mod32*)
   (mod (- v1 (logxor (+ (ash v0 4) k2)
                     (+ v0 sum)
                     (+ (ash v0 -5) k3)))
        *mod32*)
   (mod (- sum *delta*) *mod32*)))


;; Prove that one step of encryption followed by decryption results in the
;; original v0, v1, and sum. In other words, the plaintext can be recovered.
(defthm tea-step-invertible
  (implies (and (natp v0) (< v0 *mod32*)
                (natp v1) (< v1 *mod32*)
                (natp k0) (< k0 *mod32*)
                (natp k1) (< k1 *mod32*)
                (natp k2) (< k2 *mod32*)
                (natp k3) (< k3 *mod32*)
                (natp sum) (< sum *mod32*))
           (let* ((encrypted (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum))
                  (enc-v0 (car encrypted))
                  (enc-v1 (cadr encrypted))
                  (enc-sum (caddr encrypted))
                  (decrypted (tea-decrypt-step enc-v0 enc-v1 k0 k1 k2 k3 enc-sum)))
             (and (equal (car decrypted) v0)
                  (equal (cadr decrypted) v1)
                  (equal (caddr decrypted) sum))))
  :hints (("Goal" :in-theory (enable tea-encrypt-step tea-decrypt-step))))

;; Need some helper lemmas to prove that tea-encrypt and tea-decrypt guards
;; The problem seems to be showing that the encrypted and decrypted values
;; are natural numbers (mod 2^32).

;; Lemma 1: Modular reduction preserves unsigned 32-bit bounds
(defthmd mod-32-bound
  (implies (integerp x)
          (and (<= 0 (mod x *mod32*))
                (< (mod x *mod32*) *mod32*))))

;; Lemma 2: LOGXOR of two integers is an integer
(defthmd logxor-integerp
  (implies (and (integerp a)
                (integerp b))
          (integerp (logxor a b))))

;; Lemma 3: LOGXOR of two integers mod 32-bits is an unsigned 32-bit integer
(defthmd logxor-32-bound
  (implies (and (integerp a)
                (integerp b))
            (and (<= 0 (mod (logxor a b) *mod32*))
                (< (mod (logxor a b) *mod32*) *mod32*))))

;; Lemma 3: Arithmetic shift within 32-bit bounds preserved unsigned 32-bits
(defthmd ash-32-bound
  (implies (and (natp x) (< x *mod32*)
                (integerp shift))
          (<= 0 (ash x shift))))

;; Running one step of encryption results in the necessary invariants.
(defthm tea-encrypt-step-preserves-types
  (implies (and (and (integerp v0)
                     (integerp v1)
                     (integerp k0)
                     (integerp k1)
                     (integerp k2)
                     (integerp k3)
                     (integerp sum)))
          (and (natp (car (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))
                (< (car (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)) *mod32*)
                (natp (cadr (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))
                (< (cadr (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)) *mod32*)
                (natp (caddr (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)))
                (< (caddr (tea-encrypt-step v0 v1 k0 k1 k2 k3 sum)) *mod32*)))
  :hints (("Goal" :in-theory (enable tea-encrypt-step))))

;; Running one step of decryption results in the necessary invariants.
(defthm tea-decrypt-step-preserves-types
  (implies (and (and (integerp v0)
                      (integerp v1)
                      (integerp k0)
                      (integerp k1)
                      (integerp k2)
                      (integerp k3)
                      (integerp sum)))
          (and (natp (car (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)))
                (< (car (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)) *mod32*)
                (natp (cadr (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)))
                (< (cadr (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)) *mod32*)
                (natp (caddr (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)))
                (< (caddr (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum)) *mod32*)))
  :hints (("Goal" :in-theory (enable tea-decrypt-step))))

;; Runs n cycles of encryption. The guards will be verified later.
;; Fixed to use linear complexity by calling tea-encrypt-step only once per iteration
(defun tea-encrypt (v0 v1 k0 k1 k2 k3 sum n)
  (declare (xargs   :verify-guards nil
                    :guard (and (natp v0) (< v0 *mod32*)
                                (natp v1) (< v1 *mod32*)
                                (natp k0) (< k0 *mod32*)
                                (natp k1) (< k1 *mod32*)
                                (natp k2) (< k2 *mod32*)
                                (natp k3) (< k3 *mod32*)
                                (natp sum) (< sum *mod32*)
                                (natp n))))
  (if (zp n)
      (list v0 v1 sum)
    (let* ((result (tea-encrypt v0 v1 k0 k1 k2 k3 sum (1- n)))
           (new-v0 (car result))
           (new-v1 (cadr result))
           (new-sum (caddr result)))
      (tea-encrypt-step new-v0 new-v1 k0 k1 k2 k3 new-sum))))

;; Runs n cycles of decryption. The guards will be verified later.
;; Fixed to use linear complexity by calling tea-decrypt-step only once per iteration
(defun tea-decrypt (v0 v1 k0 k1 k2 k3 sum n)
  (declare (xargs   :verify-guards nil
                    :guard (and (natp v0) (< v0 *mod32*)
                                (natp v1) (< v1 *mod32*)
                                (natp k0) (< k0 *mod32*)
                                (natp k1) (< k1 *mod32*)
                                (natp k2) (< k2 *mod32*)
                                (natp k3) (< k3 *mod32*)
                                (natp sum) (< sum *mod32*)
                                (natp n))))
  (if (zp n)
      (list v0 v1 sum)
    (let* ((result (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
           (new-v0 (car result))
           (new-v1 (cadr result))
           (new-sum (caddr result)))
      (tea-decrypt new-v0 new-v1 k0 k1 k2 k3 new-sum (1- n)))))

;; Use the lemmas of tea-encrypt-step-type-preservation to show that 
;; multiple consecutive cycles of TEA encrypt preserves the invariant.
(defthm tea-encrypt-type-preservation
  (implies (and (natp v0) (< v0 *mod32*)
                (natp v1) (< v1 *mod32*)
                (natp k0) (< k0 *mod32*)
                (natp k1) (< k1 *mod32*)
                (natp k2) (< k2 *mod32*)
                (natp k3) (< k3 *mod32*)
                (natp sum) (< sum *mod32*))
          (and (natp (car (tea-encrypt v0 v1 k0 k1 k2 k3 sum n)))
                (< (car (tea-encrypt v0 v1 k0 k1 k2 k3 sum n)) *mod32*)
                (natp (cadr (tea-encrypt v0 v1 k0 k1 k2 k3 sum n)))
                (< (cadr (tea-encrypt v0 v1 k0 k1 k2 k3 sum n)) *mod32*)
                (natp (caddr (tea-encrypt v0 v1 k0 k1 k2 k3 sum n)))
                (< (caddr (tea-encrypt v0 v1 k0 k1 k2 k3 sum n)) *mod32*)))
    :hints (("Goal" :in-theory (enable tea-encrypt-step-preserves-types))))

;; Use the lemmas of tea-decrypt-step-type-preservation to show that 
;; multiple consecutive cycles of TEA decrypt preserves the invariant.
(defthm tea-decrypt-type-preservation
  (implies (and (natp v0) (< v0 *mod32*)
                (natp v1) (< v1 *mod32*)
                (natp k0) (< k0 *mod32*)
                (natp k1) (< k1 *mod32*)
                (natp k2) (< k2 *mod32*)
                (natp k3) (< k3 *mod32*)
                (natp sum) (< sum *mod32*))
          (and (natp (car (tea-decrypt v0 v1 k0 k1 k2 k3 sum n)))
                (< (car (tea-decrypt v0 v1 k0 k1 k2 k3 sum n)) *mod32*)
                (natp (cadr (tea-decrypt v0 v1 k0 k1 k2 k3 sum n)))
                (< (cadr (tea-decrypt v0 v1 k0 k1 k2 k3 sum n)) *mod32*)
                (natp (caddr (tea-decrypt v0 v1 k0 k1 k2 k3 sum n)))
                (< (caddr (tea-decrypt v0 v1 k0 k1 k2 k3 sum n)) *mod32*)))
  :hints (("Goal" :in-theory (enable tea-decrypt-step-preserves-types))))

;; Verify the guards!
(verify-guards tea-encrypt)
(verify-guards tea-decrypt)

;; Manual proof to show that TEA is invertible for N cycles.
(defthm tea-n-cycles-invertible
  (implies
   (and (natp v0) (< v0 *mod32*)
        (natp v1) (< v1 *mod32*)
        (natp k0) (< k0 *mod32*)
        (natp k1) (< k1 *mod32*)
        (natp k2) (< k2 *mod32*)
        (natp k3) (< k3 *mod32*)
        (natp sum) (< sum *mod32*)
        (natp n))
   (let* ((encrypted (tea-encrypt v0 v1 k0 k1 k2 k3 sum n))
          (enc-v0 (car encrypted))
          (enc-v1 (cadr encrypted))
          (enc-sum (caddr encrypted))
          (decrypted (tea-decrypt enc-v0 enc-v1 k0 k1 k2 k3 enc-sum n)))
     (and (equal (car decrypted) v0)
          (equal (cadr decrypted) v1)
          (equal (caddr decrypted) sum)))))

;; Concrete function that runs TEA encryption for 16 cycles
(defun tea-encrypt-16 (v0 v1 k0 k1 k2 k3)
  (declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                              (natp v1) (< v1 *mod32*)
                              (natp k0) (< k0 *mod32*)
                              (natp k1) (< k1 *mod32*)
                              (natp k2) (< k2 *mod32*)
                              (natp k3) (< k3 *mod32*))))
  (tea-encrypt v0 v1 k0 k1 k2 k3 0 16))

;; Concrete function that runs TEA decryption for 16 cycles
(defun tea-decrypt-16 (v0 v1 k0 k1 k2 k3 sum)
  (declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                              (natp v1) (< v1 *mod32*)
                              (natp k0) (< k0 *mod32*)
                              (natp k1) (< k1 *mod32*)
                              (natp k2) (< k2 *mod32*)
                              (natp k3) (< k3 *mod32*)
                              (natp sum) (< sum *mod32*))))
  (tea-decrypt v0 v1 k0 k1 k2 k3 sum 16))

;; Concrete function that runs TEA encryption for 32 cycles
(defun tea-encrypt-32 (v0 v1 k0 k1 k2 k3)
(declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                            (natp v1) (< v1 *mod32*)
                            (natp k0) (< k0 *mod32*)
                            (natp k1) (< k1 *mod32*)
                            (natp k2) (< k2 *mod32*)
                            (natp k3) (< k3 *mod32*))))
(tea-encrypt v0 v1 k0 k1 k2 k3 0 32))

;; Concrete function that runs TEA decryption for 32 cycles
(defun tea-decrypt-32 (v0 v1 k0 k1 k2 k3 sum)
(declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                            (natp v1) (< v1 *mod32*)
                            (natp k0) (< k0 *mod32*)
                            (natp k1) (< k1 *mod32*)
                            (natp k2) (< k2 *mod32*)
                            (natp k3) (< k3 *mod32*)
                            (natp sum) (< sum *mod32*))))
(tea-decrypt v0 v1 k0 k1 k2 k3 sum 32))


;; Concrete function that runs TEA encryption for 32 cycles
(defun tea-encrypt-64 (v0 v1 k0 k1 k2 k3)
(declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                            (natp v1) (< v1 *mod32*)
                            (natp k0) (< k0 *mod32*)
                            (natp k1) (< k1 *mod32*)
                            (natp k2) (< k2 *mod32*)
                            (natp k3) (< k3 *mod32*))))
(tea-encrypt v0 v1 k0 k1 k2 k3 0 64))

;; Concrete function that runs TEA decryption for 32 cycles
(defun tea-decrypt-64 (v0 v1 k0 k1 k2 k3 sum)
(declare (xargs :guard (and (natp v0) (< v0 *mod32*)
                            (natp v1) (< v1 *mod32*)
                            (natp k0) (< k0 *mod32*)
                            (natp k1) (< k1 *mod32*)
                            (natp k2) (< k2 *mod32*)
                            (natp k3) (< k3 *mod32*)
                            (natp sum) (< sum *mod32*))))
(tea-decrypt v0 v1 k0 k1 k2 k3 sum 64))

;; Test Case 1: Round trip for specific values
(defthm test-case-1
  (let* ((enc (tea-encrypt-16 #x12345678 #x9ABCDEF0
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678))
         (dec (tea-decrypt-16 (car enc) (cadr enc)
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678
                             (caddr enc))))
    (and (equal (car dec) #x12345678)
         (equal (cadr dec) #x9ABCDEF0))))

;; Test Case 1.2: Encryption changes values
(defthm test-case-1.2
  (let ((enc (tea-encrypt-16 #x12345678 #x9ABCDEF0
                            #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)))
    (not (equal (list (car enc) (cadr enc))
                (list #x12345678 #x9ABCDEF0)))))

;; Test Case 2: Round trip for different values
(defthm test-case-2
  (let* ((enc (tea-encrypt-16 #xDEADBEEF #xCAFEBABE
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678))
         (dec (tea-decrypt-16 (car enc) (cadr enc)
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678
                             (caddr enc))))
    (and (equal (car dec) #xDEADBEEF)
         (equal (cadr dec) #xCAFEBABE))))

;; Test Case 2.2: Encryption changes values
(defthm test-case-2.2
  (let ((enc (tea-encrypt-16 #xDEADBEEF #xCAFEBABE
                            #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)))
    (not (equal (list (car enc) (cadr enc))
                (list #xDEADBEEF #xCAFEBABE)))))

(defthm test-case-3
  (let* ((enc (tea-encrypt-32 #x12345678 #x9ABCDEF0
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678))
         (dec (tea-decrypt-32 (car enc) (cadr enc)
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678
                             (caddr enc))))
    (and (equal (car dec) #x12345678)
         (equal (cadr dec) #x9ABCDEF0))))

(defthm test-case-3.2
  (let ((enc (tea-encrypt-32 #x12345678 #x9ABCDEF0
                            #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)))
    (not (equal (list (car enc) (cadr enc))
                (list #x12345678 #x9ABCDEF0)))))

(defthm test-case-4
  (let* ((enc (tea-encrypt-64 #x12345678 #x9ABCDEF0
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678))
         (dec (tea-decrypt-64 (car enc) (cadr enc)
                             #xA56BABCD #x00000000 #xFFFFFFFF #x12345678
                             (caddr enc))))
    (and (equal (car dec) #x12345678)
         (equal (cadr dec) #x9ABCDEF0))))

(defthm test-case-4.2
  (let ((enc (tea-encrypt-64 #x12345678 #x9ABCDEF0
                            #xA56BABCD #x00000000 #xFFFFFFFF #x12345678)))
    (not (equal (list (car enc) (cadr enc))
                (list #x12345678 #x9ABCDEF0)))))