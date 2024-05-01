# Module: DafnyVMCPartMaterial

import secrets

class Random:
    def UniformPowerOfTwoSample(n):
        return secrets.randbits(n.bit_length()-1)
    
    def UniformSample32(n):
        return secrets.randbelow(n)