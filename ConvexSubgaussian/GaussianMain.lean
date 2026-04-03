import ConvexSubgaussian.GaussianAsymptotics

noncomputable section

open scoped Topology BigOperators
open MeasureTheory
open ProbabilityTheory

open scoped Real
open Set Filter Topology

namespace ConvexSubgaussian

/-!
# Paper-Facing Gaussian Theorem

This file is the public endpoint for the one-dimensional Gaussian comparison
result. It contains only the reader-facing final definition of the optimal
comparison scale and the final sharp theorem.
-/

/-- `AdmissibleScale c` is the statement
```lean
0 < c ∧
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Real), IsOneSubgaussian P X →
    ∀ {f : Real → Real}, ConvexOn Real Set.univ f →
      Integrable (fun ω => f (X ω)) P →
      Integrable f (gaussianScale c) →
      (∫ ω, f (X ω) ∂P) <= (∫ x, f x ∂(gaussianScale c))
```

In words: `c` is admissible iff `c > 0` and every tail-sense one-sub-Gaussian
real random variable is convex-dominated by the centered Gaussian law of scale
`c`, for every convex test function whose two expectations are finite. -/
def AdmissibleScale (c : Real) : Prop :=
  0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → Real), IsOneSubgaussian P X →
      ∀ {f : Real → Real}, ConvexOn Real Set.univ f →
        Integrable (fun ω => f (X ω)) P →
        Integrable f (gaussianScale c) →
        (∫ ω, f (X ω) ∂P) <= (∫ x, f x ∂(gaussianScale c))

/-- The sharp one-dimensional Gaussian convex-comparison constant, defined as
the infimum of admissible Gaussian scales. -/
def cStar : Real := sInf {c : Real | AdmissibleScale c}

private lemma c0_admissible : AdmissibleScale c0 := by
  refine ⟨by
    have h : (7 : Real) / 4 < c0 := OneDimConvexDom.c0_gt_seven_fourths
    linarith, ?_⟩
  intro Ω _ P _ X hX f hf hPX hG
  exact gaussianDomination_c0 P X hX hf hPX hG

private lemma integrable_psi_of_integrable_id
    {mu : Measure Real} [IsFiniteMeasure mu]
    (hInt : Integrable (fun x : Real => x) mu) (u : Real) :
    Integrable (fun x : Real => psi u x) mu := by
  unfold psi
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (MeasureTheory.Integrable.pos_part (hInt.sub (MeasureTheory.integrable_const u)))

private lemma psi_convex (u : Real) : ConvexOn Real Set.univ (fun x : Real => psi u x) := by
  have hAffine : ConvexOn Real Set.univ (fun x : Real => x + (-u)) :=
    (convexOn_id (convex_univ : Convex Real Set.univ)).add_const (-u)
  simpa [psi, sub_eq_add_neg] using
    hAffine.sup (convexOn_const (0 : Real) (convex_univ : Convex Real Set.univ))

private lemma c0_le_of_admissible {c : Real} (hc : AdmissibleScale c) : c0 ≤ c := by
  rcases hc with ⟨hc_pos, hc_dom⟩
  by_contra hlt
  have hc_lt : c < c0 := lt_of_not_ge hlt
  obtain ⟨hP, hSubg, u, _hu_nonneg, hFail⟩ := gaussianSharpness_below_c0 hc_pos hc_lt
  let P : Measure Real := OneDimConvexDom.muStar
  letI : IsProbabilityMeasure P := hP
  have hIntP : Integrable (fun x : Real => psi u x) P := by
    have hIntId : Integrable (fun x : Real => x) P := hSubg.1
    exact integrable_psi_of_integrable_id hIntId u
  have hIntG : Integrable (fun x : Real => psi u x) (gaussianScale c) := by
    letI : IsProbabilityMeasure (gaussianScale c) := OneDimConvexDom.gaussianScale_isProbability c
    exact integrable_psi_of_integrable_id (OneDimConvexDom.gaussianScale_integrable_id c) u
  have hDom :=
    hc_dom (Ω := Real) (P := P) (X := fun x : Real => x) hSubg
      (f := fun x : Real => psi u x) (psi_convex u) hIntP hIntG
  exact (not_lt_of_ge hDom) hFail

/-- Sharp one-dimensional convex sub-Gaussian comparison.

This theorem exposes the full reader-facing endpoint:

- `cStar = c0`
- `c0` is admissible
- every smaller positive scale fails, witnessed by an explicit hinge test
  against the canonical extremal law
-/
theorem sharp_convexSubgaussianComparison :
    cStar = c0 ∧
      (∀ {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω → Real), IsOneSubgaussian P X →
        ∀ {f : Real → Real}, ConvexOn Real Set.univ f →
          Integrable (fun ω => f (X ω)) P →
          Integrable f (gaussianScale c0) →
          (∫ ω, f (X ω) ∂P) <= (∫ x, f x ∂(gaussianScale c0))) ∧
      (∀ c : Real, 0 < c → c < c0 →
        IsProbabilityMeasure OneDimConvexDom.muStar ∧
          IsOneSubgaussian OneDimConvexDom.muStar (fun x : Real => x) ∧
          ∃ u : Real, 0 ≤ u ∧
            (∫ x, psi u x ∂OneDimConvexDom.muStar)
              > (∫ x, psi u x ∂(gaussianScale c))) := by
  let S : Set Real := {c : Real | AdmissibleScale c}
  have hnonempty : S.Nonempty := ⟨c0, c0_admissible⟩
  have hbdd : BddBelow S := ⟨0, by
    intro c hc
    exact hc.1.le⟩
  have hupper : cStar ≤ c0 := by
    exact csInf_le hbdd c0_admissible
  have hlower : c0 ≤ cStar := by
    refine le_csInf hnonempty ?_
    intro c hc
    exact c0_le_of_admissible hc
  refine ⟨le_antisymm hupper hlower, ?_, ?_⟩
  · intro Ω _ P _ X hX f hf hPX hG
    exact gaussianDomination_c0 P X hX hf hPX hG
  · intro c hc_pos hc_lt
    exact gaussianSharpness_below_c0 hc_pos hc_lt

end ConvexSubgaussian
