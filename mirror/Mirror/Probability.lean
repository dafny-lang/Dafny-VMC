import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory Measure ENNReal

def BitStream : Type := Nat → Bool

def Events: Set BitStream → Prop := sorry

theorem A1: Events ∅ := sorry
theorem A2: ∀ (s : Set BitStream), Events s → Events sᶜ := sorry
theorem A3: ∀ (f : ℕ → Set BitStream), (∀ (i : ℕ), Events (f i)) → Events (⋃ i, f i) := sorry

instance Cl1 : MeasurableSpace BitStream :=
  by
    apply MeasurableSpace.mk Events
    apply A1
    apply A2
    apply A3

def Mu: Set BitStream → ℝ≥0∞ := sorry

theorem B1: Mu ∅ = 0 := sorry
theorem B2: ∀ {s₁ s₂ : Set BitStream}, s₁ ⊆ s₂ → Mu s₁ ≤ Mu s₂ := sorry
theorem B3: ∀ (s : ℕ → Set BitStream), Mu (⋃ i, s i) ≤ ∑' (i : ℕ), Mu (s i) := sorry

instance Cl2 : OuterMeasure BitStream :=
  by
    apply OuterMeasure.mk Mu
    apply B1
    apply B2
    apply B3

theorem C1: ∀ ⦃f : ℕ → Set BitStream⦄,
  (∀ (i : ℕ), MeasurableSet (f i)) → Pairwise (Disjoint on f) → Cl2 (⋃ i, f i) = ∑' (i : ℕ), Cl2 (f i) := sorry
theorem C2: OuterMeasure.trim Cl2 = Cl2 := sorry

instance Cl3 : Measure BitStream :=
  by
    apply Measure.mk Cl2
    apply C1
    apply C2

instance Cl4 : MeasureSpace BitStream :=
  by
    apply MeasureSpace.mk Cl3


#check OuterMeasure.caratheodory
#check OuterMeasure.toMeasure

def Head (s : BitStream) : Bool :=
  s 0

def Tail (s : BitStream) : BitStream :=
  λ n : Nat => s (n + 1)

theorem test: Cl3 { s : BitStream | Head s = True } = 1 / 2 := sorry
