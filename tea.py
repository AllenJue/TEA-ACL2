MOD = 0x100000000

def tea_encrypt(v0, v1, k0, k1, k2, k3, rounds=32, sum=0):
    """Recursive TEA encryption function, applying 32 rounds."""
    if rounds == 0:
        print(f"Encryption complete. Final values: v0={v0:08x}, v1={v1:08x}")
        return v0, v1
    
    sum = (sum + 0x9E3779B9) % MOD
    v0 = (v0 + (((v1 << 4) + k0) ^ (v1 + sum) ^ ((v1 >> 5) + k1))) % MOD
    v1 = (v1 + (((v0 << 4) + k2) ^ (v0 + sum) ^ ((v0 >> 5) + k3))) % MOD
    
    print(f"Encryption round {33-rounds}: v0={v0:08x}, v1={v1:08x}, sum={sum:08x}")
    
    return tea_encrypt(v0, v1, k0, k1, k2, k3, rounds - 1, sum)

def tea_decrypt(v0, v1, k0, k1, k2, k3, rounds=32, sum=0xC6EF3720):
    """Recursive TEA decryption function, applying 32 rounds."""
    if rounds == 0:
        print(f"Decryption complete. Final values: v0={v0:08x}, v1={v1:08x}")
        return v0, v1
    
    v1 = (v1 - (((v0 << 4) + k2) ^ (v0 + sum) ^ ((v0 >> 5) + k3))) % MOD
    v0 = (v0 - (((v1 << 4) + k0) ^ (v1 + sum) ^ ((v1 >> 5) + k1))) % MOD
    sum = (sum - 0x9E3779B9) % MOD
    
    print(f"Decryption round {33-rounds}: v0={v0:08x}, v1={v1:08x}, sum={sum:08x}")
    
    return tea_decrypt(v0, v1, k0, k1, k2, k3, rounds - 1, sum)


def tea_encrypt_wrapper(v0, v1, k0, k1, k2, k3):
    """Wrapper to encrypt a 64-bit block (v0, v1) with a 128-bit key."""
    print("Starting encryption...")
    return tea_encrypt(v0, v1, k0, k1, k2, k3)

def tea_decrypt_wrapper(v0, v1, k0, k1, k2, k3):
    """Wrapper to decrypt a 64-bit block (v0, v1) with a 128-bit key."""
    print("Starting decryption...")
    return tea_decrypt(v0, v1, k0, k1, k2, k3)

# Test case
v0, v1 = 0x12345678, 0x9ABCDEF0
k0, k1, k2, k3 = 0xA56BABCD, 0x00000000, 0xFFFFFFFF, 0x12345678

print("Original values:")
print(f"v0 = {v0:08x}, v1 = {v1:08x}")
print(f"k0 = {k0:08x}, k1 = {k1:08x}, k2 = {k2:08x}, k3 = {k3:08x}")

cipher_l, cipher_r = tea_encrypt_wrapper(v0, v1, k0, k1, k2, k3)
print(f"\nEncrypted values: {cipher_l:08x} {cipher_r:08x}")

plain_l, plain_r = tea_decrypt_wrapper(cipher_l, cipher_r, k0, k1, k2, k3)
print(f"\nDecrypted values: {plain_l:08x} {plain_r:08x}")

assert (plain_l, plain_r) == (v0, v1), "Decryption failed to recover original values"
print("\nTest passed: Decryption successfully recovered the original values.")
