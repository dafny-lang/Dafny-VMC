import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Set Classical ENNReal

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

theorem Basic5 (h h' : Bool) (t t' : BitStream) : (scons h t = scons h' t) = (h = h' ∧ t = t') := sorry

theorem Basic6 (s : BitStream) : mirror (mirror s) = s := sorry

theorem Basic7 (s : BitStream) : stl (mirror s) = stl s := sorry

-- Ask Leo: why do I need to import MeasuraSpace.Basic for the following to work?
def prefix_set (l : List Bool) : Set BitStream := { s : BitStream | stake (List.length l) s = l }

def embed (l : List (List Bool)) : Set BitStream :=
  match l with
  | [] => ∅
  | hd :: tl => Set.union (prefix_set hd) (embed tl)

def BernoulliAlgebra : Set (Set BitStream) := { A : Set BitStream | exists l : List (List Bool), embed l = A}

noncomputable def μ₀ (l : List (List Bool)) : ℝ≥0∞ :=
  match l with
  | [] => 0
  | hd :: tl => 1 / 2 ^ ((List.length hd)) + μ₀ tl

noncomputable def μ (A : Set BitStream) : ℝ≥0∞ := ⨅ (l : List (List Bool)) (_ : A = embed l) , μ₀ l
