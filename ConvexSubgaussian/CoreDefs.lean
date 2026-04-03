import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option autoImplicit false

noncomputable section

open scoped Topology BigOperators
open MeasureTheory
open ProbabilityTheory

open scoped Real
open Set Filter Topology

/-!
# Core Definitions

Basic definitions used throughout the formalization: the hinge function
`(x - u)₊`, the stop-loss transform, and the tail-sense sub-Gaussian
condition with zero mean.
-/

/-- The hinge function `(x - u)_+`. -/
def psi (u x : Real) : Real := max (x - u) 0

/-- A finite positive linear combination of hinge functions plus an affine term. -/
def IsSimpleConvex (f : Real → Real) : Prop :=
  ∃ (a b : Real) (s : Finset Real) (w : Real → Real),
    (∀ u ∈ s, 0 ≤ w u) ∧
    ∀ x, f x = a * x + b + Finset.sum s (fun u => w u * psi u x)

/-- Tail-sense one-sub-Gaussianity with zero mean. -/
def IsOneSubgaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Real) : Prop :=
  Integrable X P ∧
    (∫ ω, X ω ∂P) = 0 ∧
    (∀ t : Real, 0 ≤ t →
      (P {ω : Ω | |X ω| > t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 2))

namespace OneDimConvexDom

/-- Positive part. -/
def posPart (x : Real) : Real := max x 0

/-- Stop-loss hinge `(x - u)_+`, written with the threshold first. -/
def hinge (u x : Real) : Real := posPart (x - u)

@[simp] lemma posPart_def (x : Real) : posPart x = max x 0 := rfl
@[simp] lemma hinge_def (u x : Real) : hinge u x = max (x - u) 0 := rfl

lemma hinge_nonneg (u x : Real) : 0 <= hinge u x := by
  simp [hinge, posPart]

lemma posPart_add_eq (x v : Real) :
    posPart (x + v) = x + v + posPart (-x - v) := by
  by_cases h : x + v <= 0
  · have h1 : posPart (x + v) = 0 := by
      simp [posPart, h]
    have h2 : posPart (-x - v) = -x - v := by
      have h2' : 0 <= -x - v := by linarith
      simp [posPart, h2']
    linarith [h1, h2]
  · have hgt : 0 < x + v := lt_of_not_ge h
    have h1 : posPart (x + v) = x + v := by
      simp [posPart, le_of_lt hgt]
    have h2 : posPart (-x - v) = 0 := by
      have h2' : -x - v <= 0 := by linarith
      simp [posPart, h2']
    linarith [h1, h2]

lemma hinge_neg_threshold (x v : Real) :
    hinge (-v) x = x + v + hinge v (-x) := by
  simpa [hinge, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (posPart_add_eq x v)

/-- Stop-loss transform of a measure. -/
def stopLoss (mu : Measure Real) (u : Real) : Real :=
  ∫ x, hinge u x ∂mu

/-- Mean of a real-valued law. -/
def mean (mu : Measure Real) : Real :=
  ∫ x, x ∂mu

/-- One-dimensional stop-loss domination. -/
def StopLossDom (mu nu : Measure Real) : Prop :=
  mean mu = mean nu ∧ ∀ u : Real, stopLoss mu u <= stopLoss nu u

end OneDimConvexDom
