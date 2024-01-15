import Mirror.H1
import Mathlib.Probability.Independence.Basic

open Set Function ProbabilityTheory

-- def Hurd (T : Type) : Type := BitStream → T × BitStream

--instance H : Monad Hurd where
--  pure := λ { T : Type } => λ x : T => λ s : BitStream => (x,s)
--  bind := λ { T U : Type } => λ f : Hurd T => λ g : T → Hurd U => λ s : BitStream => let (v,s') := f s ; (g v) s'

section Hurd

variable {T U : Type}
variable [MeasurableSpace T] [MeasurableSpace U]

def Hurd (T: Type) : Type := BitStream → T × BitStream

instance H : Monad Hurd where
  pure := λ { T : Type } => λ x : T => λ s : BitStream => (x,s)
  bind := λ { T U : Type } => λ f : Hurd T => λ g : T → Hurd U => λ s : BitStream => let (v,s') := f s ; (g v) s'


def Coin : Hurd Bool := λ s : BitStream => (s 0, λ n : Nat => s (n + 1))

-- 3.2.1

#check Countable


def strongly_measurable (f : Hurd T) : Prop :=
  Countable { y : T | exists x, y = (Prod.fst ∘ f) x } ∧ Measurable (Prod.fst ∘ f) ∧ Measurable (Prod.snd ∘ f)

theorem Meas1 (x : T) : strongly_measurable (H.pure x)  := sorry

theorem Meas2 (f: Hurd T) (g : T → Hurd U) :
  strongly_measurable f → ∀ x : T, strongly_measurable (g x) →
  strongly_measurable (H.bind f g) := sorry

def independent (f : Hurd T) : Prop :=
  IndepSets ((λ A : Set T => (Prod.fst ∘ f)⁻¹' A) '' univ) ((λ A : Set BitStream => (Prod.snd ∘ f)⁻¹' A) '' univ) Prob.volume

def prefix_cover (C : Set (List Bool)) : Prop :=
  (∀ l₁ l₂ : List Bool, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂ → ¬ l₁ <+: l₂)
  ∧ Prob.volume (⋃ l ∈ C, prefix_set l) = 1

def strongly_independent (f : Hurd T) : Prop :=
  strongly_measurable f
  ∧ exists C : Set (List Bool), prefix_cover C
    ∧ ∀ (l : List Bool) (s : BitStream), l ∈ C ∧ s ∈ prefix_set l
      → f s = (Prod.fst (f (prefix_seq l)), sdrop (List.length l) s)

@[simp]
theorem indep (f : Hurd T) : strongly_independent f → independent f := sorry

@[simp]
theorem Indep1 (x : T) : strongly_independent (H.pure x)  := sorry

@[simp]
theorem Indep2 (f: Hurd T) (g : T → Hurd U) :
  strongly_independent f → ∀ x : T, strongly_independent (g x) →
  strongly_independent (H.bind f g) := sorry

end Hurd
