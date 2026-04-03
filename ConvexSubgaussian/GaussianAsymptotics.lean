import ConvexSubgaussian.Internal.GaussianProof

noncomputable section

open scoped Topology BigOperators
open MeasureTheory
open ProbabilityTheory

open scoped Real
open Set Filter Topology

namespace ConvexSubgaussian

/-!
# Gaussian Comparison Constants and Named Results

This file defines the explicit constants (`t0`, `A`, `B`, `a`, `p0`, `z`,
`c0`) and the two named results:

- `gaussianDomination_c0`: convex domination at the sharp scale
- `gaussianSharpness_below_c0`: failure below the sharp scale
-/

/-- The tail-cap transition point `sqrt (2 log 2)`. -/
abbrev t0 : Real := OneDimConvexDom.t0

/-- The total sub-Gaussian tail-envelope mass. -/
abbrev A : Real := OneDimConvexDom.A

/-- The half-mass constant `A / 2`. -/
abbrev B : Real := OneDimConvexDom.B

/-- The unique threshold solving `H(a) = B`. -/
abbrev a : Real := OneDimConvexDom.a

/-- The plateau height `p₀ = 2 exp (-a² / 2)`. -/
abbrev p0 : Real := OneDimConvexDom.p0

/-- The Gaussian tail quantile satisfying `PhiBar z = p₀`. -/
abbrev z : Real := OneDimConvexDom.z

/-- The optimal Gaussian comparison scale. -/
abbrev c0 : Real := OneDimConvexDom.c0

/-- The centered Gaussian law with standard deviation `c`. -/
abbrev gaussianScale (c : Real) : Measure Real := OneDimConvexDom.gaussianScale c

private lemma c0_pos : 0 < c0 := by
  have h : (7 : Real) / 4 < c0 := OneDimConvexDom.c0_gt_seven_fourths
  linarith

private lemma convex_continuous {f : Real → Real} (hf : ConvexOn Real Set.univ f) : Continuous f := by
  have hcontOn : ContinuousOn f Set.univ :=
    ConvexOn.continuousOn (C := Set.univ) isOpen_univ hf
  exact continuousOn_univ.mp hcontOn

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

private lemma mapped_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Real} (hX : Integrable X P) :
    IsProbabilityMeasure (Measure.map X P) := by
  refine ⟨?_⟩
  rw [Measure.map_apply_of_aemeasurable hX.aemeasurable MeasurableSet.univ]
  simp

private lemma mapped_subgaussian_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Real} (hX : IsOneSubgaussian P X) :
    OneDimConvexDom.subgaussianTail (Measure.map X P) := by
  intro t ht
  let S : Set Real := {x : Real | |x| > t}
  have hS : MeasurableSet S := by
    have hmeas_abs : Measurable (fun x : Real => |x|) := by
      simpa using (continuous_abs.measurable : Measurable (fun x : Real => |x|))
    simpa [S, Set.preimage] using (hmeas_abs measurableSet_Ioi)
  have hmap :
      (Measure.map X P S).toReal = (P {ω : Ω | |X ω| > t}).toReal := by
    rw [Measure.map_apply_of_aemeasurable hX.1.aemeasurable hS]
    rfl
  have htailReal :
      (P {ω : Ω | |X ω| > t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
    exact hX.2.2 t ht
  calc
    OneDimConvexDom.absTail (Measure.map X P) t = (Measure.map X P S).toReal := by
      rfl
    _ = (P {ω : Ω | |X ω| > t}).toReal := hmap
    _ ≤ 2 * Real.exp (-(t ^ 2) / 2) := htailReal

private lemma mapped_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Real} (hX : IsOneSubgaussian P X) :
    OneDimConvexDom.mean (Measure.map X P) = 0 := by
  unfold OneDimConvexDom.mean
  calc
    ∫ y, y ∂(Measure.map X P) = ∫ ω, X ω ∂P := by
      exact MeasureTheory.integral_map
        (μ := P) (φ := X) (f := fun y : Real => y)
        (hφ := hX.1.aemeasurable)
        (hfm := measurable_id'.aestronglyMeasurable)
    _ = 0 := hX.2.1

private lemma mapped_integrable_id
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Real} (hX : IsOneSubgaussian P X) :
    Integrable (fun x : Real => x) (Measure.map X P) := by
  refine
    (integrable_map_measure
      (μ := P) (f := X) (g := fun x : Real => x)
      measurable_id'.aestronglyMeasurable
      hX.1.aemeasurable).2 ?_
  simpa using hX.1

private lemma mapped_integrable_convex
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Real} (hX : IsOneSubgaussian P X)
    {f : Real → Real} (hf : ConvexOn Real Set.univ f)
    (hInt : Integrable (fun ω => f (X ω)) P) :
    Integrable f (Measure.map X P) := by
  have hmeas : AEStronglyMeasurable f (Measure.map X P) :=
    (convex_continuous hf).measurable.aestronglyMeasurable
  exact
    (integrable_map_measure
      (μ := P) (f := X) (g := f)
      hmeas
      hX.1.aemeasurable).2 hInt

/-- Convex domination at the sharp Gaussian scale `c₀`. -/
theorem gaussianDomination_c0
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Real) (hX : IsOneSubgaussian P X)
    {f : Real → Real} (hf : ConvexOn Real Set.univ f)
    (hPX : Integrable (fun ω => f (X ω)) P)
    (hG : Integrable f (gaussianScale c0)) :
    (∫ ω, f (X ω) ∂P) <= (∫ x, f x ∂(gaussianScale c0)) := by
  let μ : Measure Real := Measure.map X P
  have hProb : IsProbabilityMeasure μ := mapped_probability hX.1
  letI : IsProbabilityMeasure μ := hProb
  have hIntId : Integrable (fun x : Real => x) μ := mapped_integrable_id hX
  have hTail : OneDimConvexDom.subgaussianTail μ := mapped_subgaussian_tail hX
  have hMean : OneDimConvexDom.mean μ = 0 := mapped_mean_zero hX
  have hIntF : Integrable f μ := mapped_integrable_convex hX hf hPX
  have hMeasure :
      (∫ x, f x ∂μ) <= (∫ x, f x ∂(gaussianScale c0)) := by
    exact OneDimConvexDom.convexDomination_c0_via_reduction
      (mu := μ) hIntId hTail hMean hf hIntF hG
  have hMapIntegral :
      (∫ x, f x ∂μ) = (∫ ω, f (X ω) ∂P) := by
    exact MeasureTheory.integral_map
      (μ := P) (φ := X) (f := f)
      (hφ := hX.1.aemeasurable)
      (hfm := (convex_continuous hf).measurable.aestronglyMeasurable)
  rw [hMapIntegral] at hMeasure
  exact hMeasure

private lemma canonical_extremal_is_subgaussian :
    IsOneSubgaussian OneDimConvexDom.muStar (fun x : Real => x) := by
  letI : IsProbabilityMeasure OneDimConvexDom.muStar := OneDimConvexDom.muStar_isProbability
  refine ⟨OneDimConvexDom.integrable_id_muStar, ?_, ?_⟩
  · simpa [OneDimConvexDom.mean] using OneDimConvexDom.mean_muStar
  · intro t ht
    have hEq : OneDimConvexDom.absTail OneDimConvexDom.muStar t = OneDimConvexDom.s t :=
      OneDimConvexDom.absTail_muStar_eq_s t ht
    have hReal :
        (OneDimConvexDom.muStar {x : Real | |x| > t}).toReal
          ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
      calc
        (OneDimConvexDom.muStar {x : Real | |x| > t}).toReal
            = OneDimConvexDom.absTail OneDimConvexDom.muStar t := by
                rfl
        _ = OneDimConvexDom.s t := hEq
        _ ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
              unfold OneDimConvexDom.s
              exact min_le_right (1 : Real) (2 * Real.exp (-(t ^ 2) / 2))
    change (OneDimConvexDom.muStar {x : Real | |x| > t}).toReal
      ≤ 2 * Real.exp (-(t ^ 2) / 2)
    exact hReal

/-- Sharpness below `c₀`: the canonical extremal witness beats the Gaussian. -/
theorem gaussianSharpness_below_c0
    {c : Real} (hc : 0 < c) (hc_lt : c < c0) :
    IsProbabilityMeasure OneDimConvexDom.muStar ∧
      IsOneSubgaussian OneDimConvexDom.muStar (fun x : Real => x) ∧
      ∃ u : Real, 0 ≤ u ∧
        (∫ x, psi u x ∂OneDimConvexDom.muStar) > (∫ x, psi u x ∂(gaussianScale c)) := by
  let P : Measure Real := OneDimConvexDom.muStar
  letI : IsProbabilityMeasure P := OneDimConvexDom.muStar_isProbability
  have hSubg : IsOneSubgaussian P (fun x : Real => x) := canonical_extremal_is_subgaussian
  let u : Real := c * z
  have hu_nonneg : 0 ≤ u := mul_nonneg hc.le OneDimConvexDom.z_nonneg
  have hSLu : OneDimConvexDom.stopLoss P u = OneDimConvexDom.J u :=
    OneDimConvexDom.stopLoss_muStar_eq_J u hu_nonneg
  have hJlb : OneDimConvexDom.B - OneDimConvexDom.p0 * u ≤ OneDimConvexDom.J u :=
    OneDimConvexDom.J_ge_tangent_line u hu_nonneg
  have hGauss : OneDimConvexDom.stopLoss (gaussianScale c) u = OneDimConvexDom.gClosed c u := by
    simpa [OneDimConvexDom.gSL] using OneDimConvexDom.gSL_eq_gClosed c u hc
  have hu_div : u / c = z := by
    unfold u
    field_simp [hc.ne']
  have hEval : OneDimConvexDom.gClosed c u = c * OneDimConvexDom.phi z - u * OneDimConvexDom.p0 := by
    unfold OneDimConvexDom.gClosed
    rw [hu_div, OneDimConvexDom.z_spec]
  have hphi_pos : 0 < OneDimConvexDom.phi z := OneDimConvexDom.phi_pos z
  have hB_eq : c0 * OneDimConvexDom.phi z = OneDimConvexDom.B := by
    unfold c0 OneDimConvexDom.c0
    field_simp [hphi_pos.ne']
  have hB_gt : OneDimConvexDom.B - c * OneDimConvexDom.phi z > 0 := by
    have hcphi :
        c * OneDimConvexDom.phi z < c0 * OneDimConvexDom.phi z :=
      mul_lt_mul_of_pos_right hc_lt hphi_pos
    linarith [hcphi, hB_eq]
  have hStop :
      OneDimConvexDom.stopLoss P u > OneDimConvexDom.stopLoss (gaussianScale c) u := by
    calc
      OneDimConvexDom.stopLoss P u = OneDimConvexDom.J u := hSLu
      _ >= OneDimConvexDom.B - OneDimConvexDom.p0 * u := hJlb
      _ > c * OneDimConvexDom.phi z - u * OneDimConvexDom.p0 := by
          linarith [hB_gt]
      _ = OneDimConvexDom.gClosed c u := hEval.symm
      _ = OneDimConvexDom.stopLoss (gaussianScale c) u := hGauss.symm
  have hPsiP : (∫ x, psi u x ∂P) = OneDimConvexDom.stopLoss P u := by
    simp [OneDimConvexDom.stopLoss, OneDimConvexDom.hinge, OneDimConvexDom.posPart, psi]
  have hPsiG : (∫ x, psi u x ∂(gaussianScale c)) = OneDimConvexDom.stopLoss (gaussianScale c) u := by
    simp [OneDimConvexDom.stopLoss, OneDimConvexDom.hinge, OneDimConvexDom.posPart, psi]
  refine ⟨OneDimConvexDom.muStar_isProbability, hSubg, u, hu_nonneg, ?_⟩
  rw [hPsiP, hPsiG]
  exact hStop

end ConvexSubgaussian
