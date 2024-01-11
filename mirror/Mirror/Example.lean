import Mirror.Extract

-- Map a Lean concept to Dafny
attribute [align_dafny "nat"] Nat

-- Translate to Dafny
@[export_dafny "simple1D"]
theorem simple1 : 2 = 2 := by
  rfl

-- Get result
#print_dafny_exports
