# cs389r-final-proj

Proving the Invertibility of the TEA Cipher Algorithm

Author: Allen Jue (mrallenjue@utexas.edu)
EID: aj32727

The TEA cipher algorithm is a block cipher that encrypts 2 32 bit integers with 4 32 bit integer keys. It is notable for its simplicity to implement and lightweight performance. This project demonstrates a provably correct implementation of the TEA algorithm. 

The TEA cipher algorithm is based on 'cycles' of the encryption and decryption algorithm. It has a Feistel structure, which is a symmetric structure typically used to implement block ciphers. Notably, the encryption and decryption methods are very similar to each other. The variables in encryption and decryption are v0, v1, k0, k1, k2, k3, k4, and sum, and they can be used to invert each other. In particular:

v0-1 -- 2 32 bit integers that are the "plaintext" to be encrypted

k0-3 -- 4 32 bit integers that are the secret keys

sum  -- Multiple of a magic constant (*delta*) that helps encrypt v0 and v1

The algorithm begins by incrementing sum with *delta*. The the new sumis used in conjunction with k0-3, bit shifts, and v1 to update v0. Finally, the updated sum is used with k0-3, and the updated v0 to encrypt v1. This process is repeated 'n' cycles of times. The decryption algorithm is the same process but in reverse. This project faithfully implements the TEA cipher algorithm in ACL2. The TEA encryption and decryption methods return a list of elements '(encrypted-v0 encrypted-v1 encrypted-sum) and '(decrypted-v0 decrypted-v1 decrypted-sum), respectively. 

To demonstrate the invertibility and correctness of the TEA cipher algorithm, all that remains is to prove that a single step is invertible. From this, it can be shown inductively that a variable number of encryption and decryption cycles are invertible.

For the proof, the main step of showing one step is invertible was fortunately provable with the inclusion of the arithmetic-5 book. Next, I created a helper method that would recursively call encrypt and decrypt steps for n cycles. In order to get these helper methods accepted, I had to write helper lemmas to prove that the results of encryption and decryption always resulted in v0-1 and sum that are unsigned 32 bit integers.

The theorem prover was unable to automatically prove the final theorem of the invertibility of n cycles of TEA encryption followed by n cycles of decryption with the same secret keys in a reasonable time (if at all) even with hints and disabling unnecessary definitions. To remedy this, I manually proved this in the theorem prover. Intuitively, if I could unroll the innermost call of encryption and decryption into steps, then I could undo them, as it was shown that one step of TEA is invertible. Thus, I entered the theorem prover, and expanded:

< Consider the pesudocode of n cycles of encryption and decryption >
(tea-decrypt (tea-encrypt n) n) 

< Unroll one step of tea-decrypt and tea-encrypt >
(tea-decrypt (tea-decrypt-step 
             (tea-encrypt-step (tea-encrypt (1- n)))) (1- n))

< The steps can be inverted, and the rest can be proved inductively >
(tea-decrypt (tea-encrypt (1- n)) (1- n))

The original paper by David J. Wheeler and Roger M. Needham suggests that 16 cycles may suffice for security but 32+ is suggested. I avoided using 'let' statements in my ACL2 code, which simplified the proof process. Instead, if I needed the result of a function call, I simply called the function again. This comes with a performance impact, so for concrete examples, I demonstrate the TEA algorithm with only 16 cycles.