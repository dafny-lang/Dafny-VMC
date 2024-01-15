import Mirror.H2

def t : ℕ := 2 * 1

def uniformP2 (k : Nat) : Hurd Nat :=
  if k = 0 then H.pure 0
  else do
    let flip ← Coin
    let v ← uniformP2 (k - 1)
    H.pure (v + if flip then 2 ^ (k - 1) else 0)

theorem uniformP2_indep (k : Nat) : strongly_independent (uniformP2 k) := sorry

theorem uniformP2_correct (k : Nat) (n : Nat) (_ : 0 ≤ n ∧ n < 2 ^ k) :
  Prob.volume { s : BitStream | Prod.fst (uniformP2 k s) = n } = 1 / 2 ^ k := sorry
