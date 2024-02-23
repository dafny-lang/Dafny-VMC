# Module: DafnyVMCPartMaterial

import secrets

class Random:
    def UniformSample(n):
        return secrets.randbelow(n)