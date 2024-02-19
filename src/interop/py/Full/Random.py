# Module: DafnyVMC

import secrets
import _dafny
import DafnyVMCPart

def ArrayFromList(l):
  arr = _dafny.Array(None, len(l))
  for i, e in enumerate(l):
      arr[i] = e
  return arr

class Random(DafnyVMCPart.Random):
  def Shuffle(self, xs):
    a = ArrayFromList(xs)
    DafnyVMCPart.Random.Shuffle(self, a)
    return list(a)
