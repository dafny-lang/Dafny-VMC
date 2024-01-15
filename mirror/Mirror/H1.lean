import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecificLimits.Basic

open Set Classical ENNReal Function
open MeasureTheory MeasurableSpace Measure

-- 2.3.1

def BitStream : Type := Nat → Bool

def shd (s : BitStream) : Bool := s 0
def stl (s : BitStream) : BitStream := λ n : Nat => s (n + 1)
def scons (a : Bool) (s : BitStream) : BitStream := λ n : Nat => if n = 0 then a else s (n - 1)
def stake (n : Nat) (s : BitStream) : List Bool := if n = 0 then [] else shd s :: stake (n - 1) (stl s)
def sdrop (n : Nat) (s : BitStream) : BitStream := if n = 0 then s else sdrop (n - 1) (stl s)
def sdest (s : BitStream) : Bool × BitStream := (shd s, stl s)
def mirror (s : BitStream) : BitStream := scons (! (shd s)) (stl s)

theorem Basic1 (h : Bool) (t : BitStream) : shd (scons h t) = h :=
  by
    unfold shd
    unfold scons
    simp

theorem Basic2 (h : Bool) (t : BitStream) : stl (scons h t) = t := sorry

theorem Basic3 (s : BitStream) : exists h : Bool, exists t : BitStream, s = scons h t := sorry

theorem Basic4 (s : BitStream) : scons (shd s) (stl s) = s := sorry

theorem Basic5 (h h' : Bool) (t t' : BitStream) : (scons h t = scons h' t) ↔ (h = h' ∧ t = t') := sorry

theorem Basic6 (s : BitStream) : mirror (mirror s) = s := sorry

theorem Basic7 (s : BitStream) : stl (mirror s) = stl s := sorry

-- 2.3.2

def prefix_set (l : List Bool) : Set BitStream := { s : BitStream | stake (List.length l) s = l }

def prefix_seq (l : List Bool) : BitStream :=
  match l with
  | [] => λ _ : Nat => False
  | hd :: tl => scons hd (prefix_seq tl)

def embed (l : List (List Bool)) : Set BitStream :=
  match l with
  | [] => ∅
  | hd :: tl => Set.union (prefix_set hd) (embed tl)

def BernoulliAlgebra : Set (Set BitStream) := { A : Set BitStream | exists l : List (List Bool), embed l = A}

noncomputable def μ₀ (l : List (List Bool)) : ℝ≥0∞ :=
  match l with
  | [] => 0
  | hd :: tl => 1 / 2 ^ ((List.length hd)) + μ₀ tl

-- 2.3.4

instance Eps : MeasurableSpace BitStream := generateFrom BernoulliAlgebra

noncomputable def μ' (A : Set BitStream) (_ : Eps.MeasurableSet' A) : ℝ≥0∞ := ⨅ (l : List (List Bool)) (_ : A = embed l) , μ₀ l

theorem Measure1' : μ' ∅ MeasurableSet.empty = 0 := sorry

theorem Measure3' : ∀ ⦃f : ℕ → Set BitStream⦄ (h : ∀ i, MeasurableSet (f i)),
  Pairwise (Disjoint on f) → μ' (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, μ' (f i) (h i) := sorry

noncomputable instance μ : Measure BitStream := ofMeasurable μ' Measure1' Measure3'

noncomputable instance Prob : MeasureSpace BitStream where
  volume := μ

-- 2.4.2

instance : Membership (Set BitStream) (MeasureSpace BitStream) where
  mem := λ (A : Set BitStream) (F : MeasureSpace BitStream) => F.MeasurableSet' A

theorem Event1 (b: Bool) : { s : BitStream | shd s = b } ∈ Prob := sorry

theorem Event2 (E : Set BitStream) : stl⁻¹' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Event3 (E : Set BitStream) : E ∈ Prob → stl '' E ∈ Prob := sorry

theorem Event4 (E : Set BitStream) (n : Nat) : (sdrop n) ⁻¹' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Event5 (E : Set BitStream) (n : Nat) : E ∈ Prob → (sdrop n) '' E ∈ Prob := sorry

theorem Event6 (b : Bool) : Measurable (scons b) := sorry

theorem Event7 (E : Set BitStream) (b : Bool) : (scons b) '' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Event8 (E : Set BitStream) : mirror ⁻¹' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Prob1 (b : Bool) : Prob.volume { s : BitStream | shd s = b } = 1 / 2 := sorry

def measure_preserving (f: BitStream → BitStream) : Prop :=
  Measurable f ∧ ∀ A : Set BitStream, A ∈ Prob → Prob.volume A = Prob.volume (f ⁻¹' A)

theorem Prob2 : measure_preserving stl := sorry

theorem Prob3 (n : Nat) : measure_preserving (sdrop n) := sorry

theorem Prob4 : measure_preserving mirror := sorry

theorem Prob5 (E : Set BitStream) : E ∈ Prob ∧ mirror '' E = E → Prob.volume (stl '' E) = Prob.volume E := sorry

theorem Final1 (n : Nat) : Prob.volume { s : BitStream | shd (sdrop n s) } = 1 /2 := sorry

theorem Final2 (m n : Nat) : Prob.volume { s : BitStream | shd (sdrop m s) = shd (sdrop n s)} = if m = n then 1 else 1 /2 := sorry
