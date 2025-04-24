; Proving the Invertibility of the TEA Cipher Algorithm
;
; Author: Allen Jue (mrallenjue@utexas.edu)
; EID: aj32727
;

;; The TEA cipher algorithm is a block cipher that encrypts 2 32 bit 
;; integers with 4 32 bit integer keys. It is notable for its simplicity to
;; implement and lightweight performance. This project demonstrates a provably 
;; correct implementation of the TEA algorithm. 
;;
;; The TEA cipher algorithm is based on 'cycles' of the encryption and 
;; decryption algorithm. It has a Feistel structure, which is a symmetric 
;; structure typically used to implement block ciphers. Notably, the 
;; encryption and decryption methods are very similar to each other. The 
;; variables in encryption and decryption are v0, v1, k0, k1, k2, k3, k4, and 
;; sum, and they can be used to invert each other. In particular:
;;
;; v0-1 -- 2 32 bit integers that are the "plaintext" to be encrypted
;; k0-3 -- 4 32 bit integers that are the secret keys
;; sum  -- Multiple of a magic constant (*delta*) that helps encrypt v0 and v1
;; 
;; The algorithm begins by incrementing sum with *delta*. The the new sum
;; is used in conjunction with k0-3, bit shifts, and v1 to update v0. Finally, 
;; the updated sum is used with k0-3, and the updated v0 to encrypt v1. This 
;; process is repeated 'n' cycles of times. The decryption algorithm is 
;; the same process but in reverse. This project faithfully implements 
;; the TEA cipher algorithm in ACL2. The TEA encryption and decryption methods
;; return a list of elements '(encrypted-v0 encrypted-v1 encrypted-sum) and 
;; '(decrypted-v0 decrypted-v1 decrypted-sum), respectively. 
;;
;; To demonstrate the invertibility and correctness of the TEA cipher 
;; algorithm, all that remains is to prove that a single step is 
;; invertible. From this, it can be shown inductively that a variable number 
;; of encryption and decryption cycles are invertible.
;;
;; For the proof, the main step of showing one step is invertible was
;; fortunately provable with the inclusion of the arithmetic-5 book. Next,
;; I created a helper method that would recursively call encrypt and decrypt
;; steps for n cycles. In order to get these helper methods accepted, I had to
;; write helper lemmas to prove that the results of encryption and decryption
;; always resulted in v0-1 and sum that are unsigned 32 bit integers.
;;
;; The theorem prover was unable to automatically prove the final theorem of 
;; the invertibility of n cycles of TEA encryption followed by n cycles of 
;; decryption with the same secret keys in a reasonable time (if at all) even 
;; with hints and disabling unnecessary definitions. To remedy this, I 
;; manually proved this in the theorem prover. Intuitively, if I could unroll
;; the innermost call of encryption and decryption into steps, then I could
;; undo them, as it was shown that one step of TEA is invertible. Thus, I
;; entered the theorem prover, and expanded:
;;
;; < Consider the pesudocode of n cycles of encryption and decryption >
;; (tea-decrypt (tea-encrypt n) n) 
;;
;; < Unroll one step of tea-decrypt and tea-encrypt >
;; (tea-decrypt (tea-decrypt-step 
;;              (tea-encrypt-step (tea-encrypt (1- n)))) (1- n))
;;
;; < The steps can be inverted, and the rest can be proved inductively >
;; (tea-decrypt (tea-encrypt (1- n)) (1- n))
;;
;; The original paper by David J. Wheeler and Roger M. Needham suggests that 
;; 16 cycles may suffice for security but 32+ is suggested. I avoided using 
;; 'let' statements in my ACL2 code, which simplified the proof process. 
;; Instead, if I needed the result of a function call, I simply called
;; the function again. This comes with a performance impact, so for concrete 
;; examples, I demonstrate the TEA algorithm with only 16 cycles.
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
           (and (equal (car (tea-decrypt-step 
                                              (car (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))
                                              (cadr (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))
                                              k0 k1 k2 k3 
                                              (caddr (tea-encrypt-step v0 v1
                                                      k0 k1 k2 k3 sum))))
                    v0)
                (equal (cadr (tea-decrypt-step 
                                              (car (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))
                                              (cadr (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))
                                              k0 k1 k2 k3 
                                              (caddr (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))))
                       v1)
                (equal (caddr (tea-decrypt-step 
                                              (car (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))
                                              (cadr (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))
                                              k0 k1 k2 k3 
                                              (caddr (tea-encrypt-step v0 v1 
                                                      k0 k1 k2 k3 sum))))
                          sum)))
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
    (tea-encrypt-step
      (car (tea-encrypt v0 v1 k0 k1 k2 k3 sum (1- n)))
      (cadr (tea-encrypt v0 v1 k0 k1 k2 k3 sum (1- n)))
      k0 k1 k2 k3
      (caddr (tea-encrypt v0 v1 k0 k1 k2 k3 sum (1- n))))))

;; Runs n cycles of decryption. The guards will be verified later.
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
    (tea-decrypt 
     (car (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
     (cadr (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
     k0 k1 k2 k3
     (caddr (tea-decrypt-step v0 v1 k0 k1 k2 k3 sum))
     (1- n))))

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
(DEFTHM TEA-N-cycles-INVERTIBLE
 (IMPLIES
  (AND (NATP V0)
       (< V0 *MOD32*)
       (NATP V1)
       (< V1 *MOD32*)
       (NATP K0)
       (< K0 *MOD32*)
       (NATP K1)
       (< K1 *MOD32*)
       (NATP K2)
       (< K2 *MOD32*)
       (NATP K3)
       (< K3 *MOD32*)
       (NATP SUM)
       (< SUM *MOD32*)
       (NATP N))
  (AND
     (EQUAL (CAR (TEA-DECRYPT (CAR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                              (CADR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                              K0 K1 K2 K3
                              (CADDR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                              N))
            V0)
     (EQUAL (CADR (TEA-DECRYPT (CAR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                               (CADR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                               K0 K1 K2 K3
                               (CADDR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                               N))
            V1)
     (EQUAL (CADDR (TEA-DECRYPT (CAR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                                (CADR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                                K0 K1 K2 K3
                                (CADDR (TEA-ENCRYPT V0 V1 K0 K1 K2 K3 SUM N))
                                N))
            SUM)))
 :INSTRUCTIONS (:INDUCT (:CHANGE-GOAL NIL T)
                        :S (:DEMOTE 2)
                        (:DV 1)
                        :S :UP :PROMOTE :PROMOTE (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X :UP :UP :UP (:DV 7)
                        (:DV 1)
                        :X (:UP 3)
                        :UP :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP (:DV 2)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X :UP :UP :UP (:DV 7)
                        (:DV 1)
                        :X (:UP 3)
                        :UP
                        :UP :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP :UP (:DV 1)
                        (:DV 7)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X :UP :UP :UP (:DV 7)
                        (:DV 1)
                        :X (:UP 4)
                        :UP
                        :UP :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP :UP :UP :S :NX (:DV 1)
                        (:DV 1)
                        :X (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X (:UP 3)
                        (:DV 7)
                        (:DV 1)
                        :X (:UP 4)
                        :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP (:DV 2)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X (:UP 3)
                        (:DV 7)
                        (:DV 1)
                        :X (:UP 4)
                        :UP :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP (:DV 7)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X (:UP 3)
                        (:DV 7)
                        (:DV 1)
                        :X (:UP 4)
                        (:UP 2)
                        :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP :UP :UP :UP :UP :TOP (:DV 1)
                        :UP (:DV 2)
                        (:DV 1)
                        (:DV 1)
                        :UP :TOP :S (:DV 1)
                        (:DV 1)
                        :X :UP (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X (:UP 3)
                        (:DV 7)
                        (:DV 1)
                        :X (:UP 4)
                        :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP :UP :UP :UP (:DV 1)
                        (:DV 2)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X (:UP 3)
                        (:DV 7)
                        (:DV 1)
                        :X (:UP 4)
                        :UP :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        (:UP 3)
                        (:DV 1)
                        (:DV 7)
                        (:DV 1)
                        (:DV 1)
                        (:DV 1)
                        :X :UP :NX (:DV 1)
                        :X (:UP 3)
                        (:DV 7)
                        (:DV 1)
                        :X (:UP 5)
                        :UP :UP (:REWRITE TEA-STEP-INVERTIBLE)
                        :UP :UP :UP :UP :UP :S (:DV 1)
                        (:DV 1)
                        :TOP
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        :PROVE
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)
                        (:REWRITE TEA-ENCRYPT-TYPE-PRESERVATION)))

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

