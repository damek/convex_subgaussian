import ConvexSubgaussian.CoreDefs

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option autoImplicit false
noncomputable section

open scoped Topology BigOperators
open MeasureTheory
open ProbabilityTheory

open scoped Real
open Set Filter Topology

namespace OneDimConvexDom

/-!
## Internal Gaussian Proof

This internal module contains the main body of the existing formal proof.

Reader-facing API wrappers live in:

- `ConvexSubgaussian.GaussianAsymptotics`
- `ConvexSubgaussian.GaussianMain`
-/

theorem stopLossDom_integral_convex
    {mu nu : Measure Real} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hDom : StopLossDom mu nu)
    {f : Real → Real} (hf : IsSimpleConvex f)
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (hIntNuId : Integrable (fun x : Real => x) nu)
    (_hmu : Integrable f mu) (_hnu : Integrable f nu) :
    (∫ x, f x ∂mu) <= (∫ x, f x ∂nu) := by
  rcases hf with ⟨a, b, s, w, hw, hf_repr⟩
  have hpsi_mu : ∀ u : Real, Integrable (fun x : Real => psi u x) mu := by
    intro u
    unfold psi
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part (hIntMuId.sub (MeasureTheory.integrable_const u)))
  have hpsi_nu : ∀ u : Real, Integrable (fun x : Real => psi u x) nu := by
    intro u
    unfold psi
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part (hIntNuId.sub (MeasureTheory.integrable_const u)))
  have hsum_mu_int :
      Integrable (fun x : Real => Finset.sum s (fun u => w u * psi u x)) mu := by
    refine MeasureTheory.integrable_finset_sum _ fun u hu => ?_
    exact (hpsi_mu u).const_mul (w u)
  have hsum_nu_int :
      Integrable (fun x : Real => Finset.sum s (fun u => w u * psi u x)) nu := by
    refine MeasureTheory.integrable_finset_sum _ fun u hu => ?_
    exact (hpsi_nu u).const_mul (w u)
  have h_repr_mu :
      ∫ x, f x ∂mu =
        ∫ x, (a * x + b) + (Finset.sum s (fun u => w u * psi u x)) ∂mu := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [hf_repr x, add_assoc, add_comm]
  have h_repr_nu :
      ∫ x, f x ∂nu =
        ∫ x, (a * x + b) + (Finset.sum s (fun u => w u * psi u x)) ∂nu := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [hf_repr x, add_assoc, add_comm]
  have hsum_mu :
      ∫ x, (Finset.sum s (fun u => w u * psi u x)) ∂mu
        = Finset.sum s (fun u => w u * (∫ x, psi u x ∂mu)) := by
    calc
      ∫ x, (Finset.sum s (fun u => w u * psi u x)) ∂mu
          = Finset.sum s (fun u => ∫ x, w u * psi u x ∂mu) := by
              simpa using
                (MeasureTheory.integral_finset_sum (s := s)
                  (f := fun u x => w u * psi u x)
                  (fun u hu => (hpsi_mu u).const_mul (w u)))
      _ = Finset.sum s (fun u => w u * (∫ x, psi u x ∂mu)) := by
            simp [MeasureTheory.integral_const_mul]
  have hsum_nu :
      ∫ x, (Finset.sum s (fun u => w u * psi u x)) ∂nu
        = Finset.sum s (fun u => w u * (∫ x, psi u x ∂nu)) := by
    calc
      ∫ x, (Finset.sum s (fun u => w u * psi u x)) ∂nu
          = Finset.sum s (fun u => ∫ x, w u * psi u x ∂nu) := by
              simpa using
                (MeasureTheory.integral_finset_sum (s := s)
                  (f := fun u x => w u * psi u x)
                  (fun u hu => (hpsi_nu u).const_mul (w u)))
      _ = Finset.sum s (fun u => w u * (∫ x, psi u x ∂nu)) := by
            simp [MeasureTheory.integral_const_mul]
  have hsum_le :
      (Finset.sum s (fun u => w u * (∫ x, psi u x ∂mu)))
        <= (Finset.sum s (fun u => w u * (∫ x, psi u x ∂nu))) := by
    refine Finset.sum_le_sum fun u hu => ?_
    have hsl_u : stopLoss mu u <= stopLoss nu u := hDom.2 u
    have hsl_u' : (∫ x, psi u x ∂mu) <= (∫ x, psi u x ∂nu) := by
      simpa [stopLoss, hinge, posPart, psi] using hsl_u
    exact mul_le_mul_of_nonneg_left hsl_u' (hw u hu)
  have h_aff_mu :
      ∫ x, (a * x + b) ∂mu = a * mean mu + b := by
    rw [MeasureTheory.integral_add (hIntMuId.const_mul a) (MeasureTheory.integrable_const b)]
    rw [MeasureTheory.integral_const_mul]
    simp [mean, mul_comm]
  have h_aff_nu :
      ∫ x, (a * x + b) ∂nu = a * mean nu + b := by
    rw [MeasureTheory.integral_add (hIntNuId.const_mul a) (MeasureTheory.integrable_const b)]
    rw [MeasureTheory.integral_const_mul]
    simp [mean, mul_comm]
  have hsplit_mu :
      ∫ x, a * x + b + Finset.sum s (fun u => w u * psi u x) ∂mu
        = (∫ x, (a * x + b) ∂mu) +
          ∫ x, (Finset.sum s (fun u => w u * psi u x)) ∂mu := by
    simpa [add_assoc] using
      (MeasureTheory.integral_add
        (((hIntMuId.const_mul a).add (MeasureTheory.integrable_const b)))
        hsum_mu_int)
  have hsplit_nu :
      ∫ x, a * x + b + Finset.sum s (fun u => w u * psi u x) ∂nu
        = (∫ x, (a * x + b) ∂nu) +
          ∫ x, (Finset.sum s (fun u => w u * psi u x)) ∂nu := by
    simpa [add_assoc] using
      (MeasureTheory.integral_add
        (((hIntNuId.const_mul a).add (MeasureTheory.integrable_const b)))
        hsum_nu_int)
  rw [h_repr_mu, h_repr_nu]
  rw [hsplit_mu, hsplit_nu]
  rw [h_aff_mu, h_aff_nu, hsum_mu, hsum_nu]
  calc
    a * mean mu + b + Finset.sum s (fun u => w u * (∫ x, psi u x ∂mu))
        = a * mean nu + b + Finset.sum s (fun u => w u * (∫ x, psi u x ∂mu)) := by
            simp [hDom.1]
    _ <= a * mean nu + b + Finset.sum s (fun u => w u * (∫ x, psi u x ∂nu)) := by
            linarith [hsum_le]

/-! ## 2. Tail cap and envelope constants -/

def s (t : Real) : Real := min 1 (2 * Real.exp (-(t ^ 2) / 2))

def t0 : Real := Real.sqrt (2 * Real.log 2)

def A : Real := ∫ t in Set.Ioi (0 : Real), s t ∂volume

def B : Real := A / 2

def H (x : Real) : Real := x * s x + ∫ t in Set.Ioi x, s t ∂volume

lemma H_strictAntiOn : StrictAntiOn H (Set.Ioi t0) := by
  have h_deriv : ∀ x ∈ Set.Ioi t0, deriv H x = -x ^ 2 * s x := by
    intro x hx
    have h_deriv :
        deriv (fun x => x * (2 * Real.exp (-(x ^ 2) / 2)) + ∫ t in Set.Ioi x, (2 * Real.exp (-(t ^ 2) / 2))) x =
          -x ^ 2 * (2 * Real.exp (-(x ^ 2) / 2)) := by
      have h_ftc : deriv (fun x => ∫ t in Set.Ioi x, (2 * Real.exp (-(t ^ 2) / 2))) x = -2 * Real.exp (-(x ^ 2) / 2) := by
        have h_ftc : deriv (fun x => ∫ t in Set.Iic x, (2 * Real.exp (-t ^ 2 / 2))) x = 2 * Real.exp (-x ^ 2 / 2) := by
          have h_ftc :
              deriv (fun x => ∫ t in Set.Iic x, 2 * Real.exp (-t ^ 2 / 2)) x =
                deriv (fun x => (∫ t in Set.Iic 0, 2 * Real.exp (-t ^ 2 / 2)) + (∫ t in (0 : Real)..x, 2 * Real.exp (-t ^ 2 / 2))) x := by
            refine' Filter.EventuallyEq.deriv_eq _
            filter_upwards [lt_mem_nhds (show x > 0 from lt_of_le_of_lt (Real.sqrt_nonneg _) hx)] with y hy
            rw [intervalIntegral.integral_of_le hy.le, ← MeasureTheory.setIntegral_union] <;> norm_num
            · rw [Set.Iic_union_Ioc_eq_Iic hy.le]
            · exact MeasureTheory.Integrable.integrableOn
                (by
                  exact MeasureTheory.Integrable.const_mul
                    (by simpa [div_eq_inv_mul] using (integrable_exp_neg_mul_sq (by norm_num)))
                    _)
            · exact Continuous.integrableOn_Ioc (by continuity)
          norm_num [h_ftc]
          apply_rules [Continuous.deriv_integral]
          continuity
        have h_split :
            ∀ x, ∫ t in Set.Ioi x, (2 * Real.exp (-t ^ 2 / 2)) =
              (∫ t in Set.univ, (2 * Real.exp (-t ^ 2 / 2))) - (∫ t in Set.Iic x, (2 * Real.exp (-t ^ 2 / 2))) := by
          intro x
          rw [← MeasureTheory.integral_diff] <;> norm_num
          · rcongr t
            aesop
          · exact MeasureTheory.Integrable.const_mul
              (by simpa [div_eq_inv_mul] using (integrable_exp_neg_mul_sq (by norm_num)))
              _
        rw [show (fun x => ∫ t in Set.Ioi x, 2 * Real.exp (-t ^ 2 / 2)) =
            fun x => (∫ t in Set.univ, 2 * Real.exp (-t ^ 2 / 2)) - ∫ t in Set.Iic x, 2 * Real.exp (-t ^ 2 / 2) from funext h_split]
        norm_num [h_ftc]
        rw [deriv_const_sub, h_ftc]
      convert HasDerivAt.deriv
          (HasDerivAt.add
            (HasDerivAt.mul (hasDerivAt_id x)
              (HasDerivAt.mul (hasDerivAt_const _ _) (HasDerivAt.exp (HasDerivAt.div_const (HasDerivAt.neg (hasDerivAt_pow 2 x)) _))))
            (h_ftc ▸ hasDerivAt_deriv_iff.mpr _)) using 1 <;> norm_num
      ring
      exact differentiableAt_of_deriv_ne_zero (by rw [h_ftc]; norm_num [Real.exp_ne_zero])
    have h_s_eq : ∀ x ∈ Set.Ioi t0, s x = 2 * Real.exp (-(x ^ 2) / 2) := by
      intro x hx
      simp [s]
      rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp]
      ring_nf
      norm_num
      rw [show t0 = Real.sqrt (2 * Real.log 2) by rfl] at hx
      rw [Set.mem_Ioi] at hx
      nlinarith [Real.sqrt_nonneg (2 * Real.log 2), Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]
    convert h_deriv using 1
    · refine' Filter.EventuallyEq.deriv_eq _
      filter_upwards [lt_mem_nhds hx] with y hy using by
        rw [show H y = y * s y + ∫ t in Set.Ioi y, s t ∂MeasureTheory.volume from rfl]
        rw [h_s_eq y hy]
        exact congr_arg₂ _ rfl
          (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => h_s_eq t <| hy.trans ht)
    · rw [h_s_eq x hx]
  have h_s_pos : ∀ x ∈ Set.Ioi t0, 0 < s x := by
    exact fun x hx => lt_min zero_lt_one <| mul_pos zero_lt_two <| Real.exp_pos _
  have h_deriv_neg : ∀ x ∈ Set.Ioi t0, deriv H x < 0 := by
    exact fun x hx =>
      h_deriv x hx ▸
        mul_neg_of_neg_of_pos
          (neg_neg_of_pos (sq_pos_of_pos (lt_trans (Real.sqrt_pos.mpr (show 0 < 2 * Real.log 2 by positivity)) hx)))
          (h_s_pos x hx)
  apply_rules [strictAntiOn_of_deriv_neg]
  · exact convex_Ioi _
  · exact continuousOn_of_forall_continuousAt fun x hx => by
      exact differentiableAt_of_deriv_ne_zero (ne_of_lt (h_deriv_neg x hx)) |>.continuousAt
  · aesop
lemma H_at_t0 : H t0 = A := by
  unfold H A t0
  have h_integral_s :
      ∫ t in Set.Ioi 0, s t =
        (∫ t in Set.Ioc 0 (Real.sqrt (2 * Real.log 2)), 1) +
        (∫ t in Set.Ioi (Real.sqrt (2 * Real.log 2)), 2 * Real.exp (-(t ^ 2) / 2)) := by
    have h_split :
        ∫ t in Set.Ioi 0, s t =
          (∫ t in Set.Ioc 0 (Real.sqrt (2 * Real.log 2)), s t) +
          (∫ t in Set.Ioi (Real.sqrt (2 * Real.log 2)), s t) := by
      rw [← MeasureTheory.setIntegral_union] <;> norm_num
      · exact Continuous.integrableOn_Ioc
          (by
            unfold s
            exact Continuous.min continuous_const
              (by
                exact Continuous.mul continuous_const
                  (Real.continuous_exp.comp (by continuity))))
      · have h_integrable :
            MeasureTheory.IntegrableOn (fun t => 2 * Real.exp (-t ^ 2 / 2))
              (Set.Ioi (Real.sqrt (2 * Real.log 2))) := by
          exact MeasureTheory.Integrable.const_mul
            (by
              simpa [div_eq_inv_mul] using
                (integrable_exp_neg_mul_sq (by norm_num) |>.integrableOn))
            _
        norm_num +zetaDelta at *
        refine' h_integrable.mono' _ _
        · exact Measurable.aestronglyMeasurable
            (by
              exact Measurable.min measurable_const
                (by
                  exact Measurable.mul measurable_const
                    (Real.continuous_exp.measurable.comp
                      (by
                        exact Measurable.div_const
                          (by exact Measurable.neg (measurable_id.pow_const 2)) _))))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using by
            rw [Real.norm_of_nonneg
              (by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))]
            exact min_le_right _ _
    rw [h_split]
    refine' congrArg₂ (· + ·) _ _
    · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _
      exact min_eq_left
        (by
          rw [show 2 * Real.exp (-(x ^ 2) / 2) =
              (Real.exp (Real.log 2)) * (Real.exp (-(x ^ 2) / 2)) by
                rw [Real.exp_log (by norm_num)]]
          rw [← Real.exp_add]
          ring_nf
          exact Real.one_le_exp
            (by
              nlinarith [hx.1, hx.2, Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]))
    · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _
      refine' min_eq_right _
      rw [← Real.log_le_log_iff (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_exp]
      norm_num
      nlinarith [hx.out, Real.sqrt_nonneg (2 * Real.log 2),
        Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]
  have h_integral_s_tail :
      ∫ t in Set.Ioi (Real.sqrt (2 * Real.log 2)), s t =
        ∫ t in Set.Ioi (Real.sqrt (2 * Real.log 2)), 2 * Real.exp (-(t ^ 2) / 2) := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _
    refine' min_eq_right _
    rw [← Real.log_le_log_iff (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    norm_num
    nlinarith [hx.out, Real.sqrt_nonneg (2 * Real.log 2),
      Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]
  simp_all +decide [le_of_lt, Real.sqrt_pos]
  unfold s
  norm_num [mul_pow, Real.sq_sqrt, Real.log_nonneg]
  ring_nf
  norm_num [Real.exp_neg, Real.exp_log]
lemma H_tendsto_zero : Filter.Tendsto H Filter.atTop (nhds (0 : Real)) := by
  suffices h_suff :
      Filter.Tendsto (fun x => x * s x) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun x => ∫ t in Set.Ioi x, s t ∂MeasureTheory.volume) Filter.atTop (nhds 0) by
    simpa [H] using h_suff.1.add h_suff.2
  constructor
  · unfold s
    have h_exp : Filter.Tendsto (fun x : Real => x * Real.exp (-x ^ 2 / 2)) Filter.atTop (nhds 0) := by
      have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
      refine' squeeze_zero_norm' _ this
      filter_upwards [Filter.eventually_ge_atTop 2] with x hx using by
        rw [Real.norm_of_nonneg (by positivity)]
        norm_num
        gcongr
        nlinarith
    refine' squeeze_zero_norm' _ (by simpa using h_exp.const_mul 2)
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by
      rw [Real.norm_of_nonneg (by positivity)]
      rw [min_def]
      split_ifs <;> nlinarith [Real.exp_pos (-x ^ 2 / 2)]
  · have h_integrable : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioi 0) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t => 2 * Real.exp (-(t ^ 2) / 2)) (Set.Ioi 0) := by
        exact MeasureTheory.Integrable.const_mul
          (by
            simpa [div_eq_inv_mul] using
              (integrable_exp_neg_mul_sq (by norm_num) |>.integrableOn))
          _
      refine' h_integrable.mono' _ _
      · exact Measurable.aestronglyMeasurable
          (by
            exact Measurable.min measurable_const
              (by
                exact Measurable.mul measurable_const
                  (Real.continuous_exp.measurable.comp
                    (by
                      exact Measurable.div_const
                        (by exact Measurable.neg (measurable_id.pow_const 2)) _))))
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using by
          rw [Real.norm_of_nonneg
            (by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))]
          exact min_le_right _ _
    have h_int_zero :
        Filter.Tendsto (fun x => ∫ t in Set.Ioi 0, s t * (if t > x then 1 else 0))
          Filter.atTop (nhds 0) := by
      have h_int_zero :
          Filter.Tendsto (fun x => ∫ t in Set.Ioi 0, s t * (if t > x then 1 else 0))
            Filter.atTop (nhds (∫ t in Set.Ioi 0, s t * 0)) := by
        refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _
        · exact fun t => |s t|
        · exact Filter.Eventually.of_forall fun n =>
            MeasureTheory.AEStronglyMeasurable.mul
              h_integrable.aestronglyMeasurable
              (Measurable.aestronglyMeasurable
                (by exact Measurable.ite measurableSet_Ioi measurable_const measurable_const))
        · filter_upwards [Filter.eventually_gt_atTop 0] with n hn using
            Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num [abs_mul]
        · exact h_integrable.abs
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using
            tendsto_const_nhds.congr'
              (by
                filter_upwards [Filter.eventually_gt_atTop x] with n hn
                split_ifs <;> linarith)
      aesop
    refine h_int_zero.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
    rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
    congr
    ext
    split_ifs <;> linarith
lemma exists_unique_a : ∃! a : Real, a > t0 ∧ H a = B := by
  obtain ⟨a, ha⟩ : ∃ a : Real, a > t0 ∧ H a = B := by
    have h_ivt : ∃ a ∈ Set.Ioi t0, H a ≤ B := by
      have h_lim : Filter.Tendsto H Filter.atTop (nhds 0) := H_tendsto_zero
      have hB_pos : 0 < B := by
        refine' div_pos _ zero_lt_two
        refine' lt_of_lt_of_le _ (MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioi fun x hx =>
          show s x ≥ Real.exp (-x ^ 2 / 2) from _)
        · exact (by
            have := integral_gaussian_Ioi (1 / 2)
            norm_num [div_eq_inv_mul] at *
            exact this.symm ▸ by positivity)
        · simpa [div_eq_inv_mul] using (integrable_exp_neg_mul_sq (by norm_num)).integrableOn
        · have h_integrable : MeasureTheory.IntegrableOn (fun x => 2 * Real.exp (-x ^ 2 / 2)) (Set.Ioi 0) := by
            exact MeasureTheory.Integrable.const_mul
              (by
                simpa [div_eq_inv_mul] using
                  (integrable_exp_neg_mul_sq (by norm_num) |>.integrableOn))
              _
          refine' h_integrable.mono' _ _
          · exact Measurable.aestronglyMeasurable
              (by
                exact Measurable.min measurable_const
                  (by
                    exact Measurable.mul measurable_const
                      (Real.continuous_exp.measurable.comp
                        (by
                          exact Measurable.div_const
                            (by exact Measurable.neg (measurable_id.pow_const 2)) _))))
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using by
              rw [Real.norm_of_nonneg (by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))]
              exact min_le_right _ _
        · exact le_min
            (Real.exp_le_one_iff.mpr <| by nlinarith)
            (by nlinarith [Real.exp_pos (-(x ^ 2) / 2)])
      have h_event_le : ∀ᶠ x in Filter.atTop, H x ≤ B := by
        exact h_lim.eventually (Iic_mem_nhds hB_pos)
      have h_event_gt : ∀ᶠ x in Filter.atTop, x ∈ Set.Ioi t0 := by
        simpa [Set.mem_Ioi] using (Filter.eventually_gt_atTop t0)
      obtain ⟨a, ha_gt, ha_le⟩ := (h_event_gt.and h_event_le).exists
      exact ⟨a, ha_gt, ha_le⟩
    obtain ⟨a, ha1, ha2⟩ : ∃ a ∈ Set.Ioi t0, H a ≤ B := h_ivt
    have h_ivt : ∃ c ∈ Set.Icc t0 a, H c = B := by
      apply_rules [intermediate_value_Icc']
      · exact le_of_lt ha1
      · refine' ContinuousOn.add _ _
        · refine' ContinuousOn.mul continuousOn_id _
          exact ContinuousOn.inf continuousOn_const <|
            ContinuousOn.mul continuousOn_const <|
              ContinuousOn.rexp <| ContinuousOn.div_const (ContinuousOn.neg <| continuousOn_pow 2) _
        · have h_cont : ContinuousOn (fun x => ∫ t in Set.Ioi 0, min 1 (2 * Real.exp (-(t + x) ^ 2 / 2))) (Set.Icc t0 a) := by
            intro x hx
            refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _
            · exact fun t => 2 * Real.exp (-t ^ 2 / 2)
            · exact Filter.Eventually.of_forall fun n =>
                Measurable.aestronglyMeasurable
                  (by
                    exact Measurable.min measurable_const <|
                      by
                        exact Measurable.mul measurable_const <|
                          Real.continuous_exp.measurable.comp <|
                            by
                              exact Measurable.div_const
                                (by exact Measurable.neg <| by exact Measurable.pow_const (measurable_id'.add_const _) _)
                                _)
            · filter_upwards [self_mem_nhdsWithin] with n hn
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
              rw [Real.norm_of_nonneg (by positivity)]
              exact le_trans (min_le_right _ _)
                (mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr <| by
                    nlinarith [ht.out, hn.1, hn.2, show 0 ≤ n by exact le_trans (by exact Real.sqrt_nonneg _) hn.1])
                  zero_le_two)
            · exact MeasureTheory.Integrable.const_mul
                (by
                  simpa [div_eq_inv_mul] using
                    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 2) |>.integrableOn))
                _
            · exact Filter.Eventually.of_forall fun y =>
                Filter.Tendsto.min tendsto_const_nhds <|
                  Filter.Tendsto.mul tendsto_const_nhds <|
                    Real.continuous_exp.continuousAt.tendsto.comp <|
                      Filter.Tendsto.div_const
                        (Filter.Tendsto.neg <| Filter.Tendsto.pow (tendsto_const_nhds.add <| Filter.tendsto_id.mono_left inf_le_left) _)
                        _
          refine' h_cont.congr fun x hx => _
          rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← MeasureTheory.integral_indicator measurableSet_Ioi]
          rw [← MeasureTheory.integral_add_right_eq_self _ x]
          congr
          ext y
          rw [Set.indicator_apply, Set.indicator_apply]
          aesop
      · exact ⟨ha2, by
          rw [H_at_t0]
          exact div_le_self
            (by exact MeasureTheory.integral_nonneg fun _ => by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))
            (by norm_num)⟩
    obtain ⟨c, hc1, hc2⟩ := h_ivt
    exact ⟨c, lt_of_le_of_ne hc1.1 (Ne.symm <| by
      rintro rfl
      exact absurd hc2 <| by
        linarith [show B < H t0 from by
          rw [H_at_t0]
          exact div_lt_self
            (show 0 < A from by
              refine' lt_of_lt_of_le _ (MeasureTheory.setIntegral_mono_set _ _ _)
              rotate_left
              exact Set.Ioc 0 1
              · have h_integrable : MeasureTheory.IntegrableOn (fun x => 2 * Real.exp (-x ^ 2 / 2)) (Set.Ioi 0) := by
                  exact MeasureTheory.Integrable.const_mul
                    (by
                      simpa [div_eq_inv_mul] using
                        (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 2) |>.integrableOn))
                    _
                refine' h_integrable.mono' _ _
                · exact Measurable.aestronglyMeasurable
                    (by
                      exact Measurable.min measurable_const
                        (by
                          exact Measurable.mul measurable_const
                            (Real.continuous_exp.measurable.comp
                              (by exact Measurable.div_const (by exact measurable_id.pow_const 2 |> Measurable.neg) _))))
                · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using by
                    rw [Real.norm_of_nonneg (by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))]
                    exact min_le_right _ _
              · exact Filter.Eventually.of_forall fun x => le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _))
              · exact MeasureTheory.ae_of_all _ fun x hx => hx.1
              · rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
                · simp +decide [Function.support, s]
                  exact lt_of_lt_of_le (by norm_num)
                    (MeasureTheory.measure_mono <| show Set.Ioc 0 1 ⊆ {x : Real | ¬Min.min 1 (2 * Real.exp (-x ^ 2 / 2)) = 0} ∩ Set.Ioc 0 1 from
                      fun x hx => ⟨ne_of_gt <| lt_min zero_lt_one <| mul_pos zero_lt_two <| Real.exp_pos _, hx⟩)
                · exact Filter.Eventually.of_forall fun x => le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _))
                · refine' MeasureTheory.Integrable.mono' _ _ _
                  · exact fun x => 1
                  · norm_num
                  · exact Measurable.aestronglyMeasurable
                      (by
                        exact Measurable.min measurable_const
                          (measurable_const.mul
                            (Real.continuous_exp.measurable.comp
                              (measurable_neg.comp (measurable_id.pow_const 2) |> Measurable.div_const <| 2))))
                  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using by
                      rw [Real.norm_of_nonneg (by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))]
                      exact min_le_left _ _) (by norm_num)]), hc2⟩
  refine' ⟨a, ha, fun b hb => _⟩
  have := H_strictAntiOn.eq_iff_eq hb.1 ha.1
  aesop

noncomputable def a : Real := Classical.choose exists_unique_a
lemma a_spec : a > t0 ∧ H a = B := (Classical.choose_spec exists_unique_a).1

def p0 : Real := s a

def J (u : Real) : Real :=
  if u <= a then B - p0 * u else ∫ t in Set.Ioi u, s t ∂volume

lemma J_of_le_a {u : Real} (hu : u <= a) : J u = B - p0 * u := by
  simp [J, hu]

lemma J_of_gt_a {u : Real} (hu : a < u) : J u = ∫ t in Set.Ioi u, s t ∂volume := by
  simp [J, not_le_of_gt hu]

lemma t0_pos : 0 < t0 := by
  unfold t0
  refine Real.sqrt_pos.mpr ?_
  positivity

lemma s_eq_gauss_tail_of_gt_t0 {x : Real} (hx : x > t0) :
    s x = 2 * Real.exp (-(x ^ 2) / 2) := by
  unfold s
  unfold t0 at hx
  refine min_eq_right ?_
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp]
  norm_num
  nlinarith [hx, Real.sqrt_nonneg (2 * Real.log 2),
    Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]

lemma s_integrableOn_Ioi_zero : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioi 0) := by
  have h_integrable : MeasureTheory.IntegrableOn (fun t => 2 * Real.exp (-(t ^ 2) / 2)) (Set.Ioi 0) := by
    exact MeasureTheory.Integrable.const_mul
      (by
        simpa [div_eq_inv_mul] using
          (integrable_exp_neg_mul_sq (by norm_num) |>.integrableOn))
      _
  refine h_integrable.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      (by
        exact Measurable.min measurable_const
          (by
            exact Measurable.mul measurable_const
              (Real.continuous_exp.measurable.comp
                (by
                  exact Measurable.div_const
                    (by exact Measurable.neg (measurable_id.pow_const 2)) _))))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using by
      rw [Real.norm_of_nonneg
        (by exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))]
      exact min_le_right _ _

lemma s_le_p0_of_ge_a {x : Real} (hx : a <= x) : s x <= p0 := by
  have ha_t0 : a > t0 := a_spec.1
  have hx_t0 : x > t0 := lt_of_lt_of_le ha_t0 hx
  rw [p0, s_eq_gauss_tail_of_gt_t0 hx_t0, s_eq_gauss_tail_of_gt_t0 ha_t0]
  have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
  have hsq : a ^ 2 <= x ^ 2 := by nlinarith [hx, ha_pos]
  have hexp : Real.exp (-(x ^ 2) / 2) <= Real.exp (-(a ^ 2) / 2) := by
    exact Real.exp_le_exp.mpr (by nlinarith [hsq])
  exact mul_le_mul_of_nonneg_left hexp zero_le_two

def t1 : Real := Real.sqrt (2 * Real.log 4)

lemma t1_pos : 0 < t1 := by
  unfold t1
  refine Real.sqrt_pos.mpr ?_
  positivity

lemma t0_lt_t1 : t0 < t1 := by
  unfold t0 t1
  gcongr
  norm_num

lemma two_exp_neg_t1_sq_div_two_eq_half : 2 * Real.exp (-(t1 ^ 2) / 2) = 1 / 2 := by
  unfold t1
  have hnonneg : 0 ≤ 2 * Real.log 4 := by positivity
  calc
    2 * Real.exp (-(Real.sqrt (2 * Real.log 4) ^ 2) / 2)
        = 2 * Real.exp (-(2 * Real.log 4) / 2) := by rw [Real.sq_sqrt hnonneg]
    _ = 2 * Real.exp (-Real.log 4) := by ring_nf
    _ = 2 * (Real.exp (Real.log 4))⁻¹ := by simp [Real.exp_neg]
    _ = 2 * ((4 : Real)⁻¹) := by rw [Real.exp_log (by norm_num : (0 : Real) < 4)]
    _ = 1 / 2 := by norm_num

lemma s_t1_eq_half : s t1 = 1 / 2 := by
  unfold s
  rw [two_exp_neg_t1_sq_div_two_eq_half]
  norm_num

lemma integral_s_Ioc_0_t1_lt_t1 :
    ∫ t in Set.Ioc 0 t1, s t ∂volume < t1 := by
  have hs_cont : Continuous (fun t : Real => s t) := by
    unfold s
    exact Continuous.min continuous_const
      (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
  have hs_int : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioc 0 t1) := by
    exact hs_cont.integrableOn_Ioc
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : Real => (1 : Real)) (Set.Ioc 0 t1) := by
    exact MeasureTheory.integrableOn_const (measure_Ioc_lt_top (μ := (volume : Measure Real))
      (a := (0 : Real)) (b := t1)).ne
  have hsub_eq :
      ∫ t in Set.Ioc 0 t1, (1 - s t) ∂volume
        = (∫ t in Set.Ioc 0 t1, (1 : Real) ∂volume) - ∫ t in Set.Ioc 0 t1, s t ∂volume := by
    rw [MeasureTheory.integral_sub hconst_int hs_int]
  have hconst :
      ∫ t in Set.Ioc 0 t1, (1 : Real) ∂volume = t1 := by
    simp [MeasureTheory.integral_const, smul_eq_mul, t1_pos.le]
  have hsub_pos_interval : 0 < ∫ t in (0 : Real)..t1, (1 - s t) := by
    refine intervalIntegral.integral_pos t1_pos ?_ ?_ ?_
    · exact (continuous_const.sub hs_cont).continuousOn
    · intro t ht
      exact sub_nonneg.mpr (by
        unfold s
        exact min_le_left _ _)
    · refine ⟨(t0 + t1) / 2, ?_, ?_⟩
      · constructor <;> nlinarith [t0_lt_t1, t0_pos]
      · have hmid_gt_t0 : t0 < (t0 + t1) / 2 := by nlinarith [t0_lt_t1]
        have hs_mid :
            s ((t0 + t1) / 2) = 2 * Real.exp (-(((t0 + t1) / 2) ^ 2) / 2) :=
          s_eq_gauss_tail_of_gt_t0 hmid_gt_t0
        have hmid_lt :
            2 * Real.exp (-(((t0 + t1) / 2) ^ 2) / 2) < 1 := by
          rw [← Real.log_lt_log_iff (by positivity) (by norm_num),
            Real.log_mul (by positivity) (by positivity), Real.log_exp]
          norm_num
          have hmid_gt : (t0 + t1) / 2 > Real.sqrt (2 * Real.log 2) := by
            simpa [t0] using hmid_gt_t0
          have hsq : 2 * Real.log 2 < ((t0 + t1) / 2) ^ 2 := by
            nlinarith [hmid_gt, Real.sqrt_nonneg (2 * Real.log 2),
              Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]
          nlinarith [hsq]
        have hs_lt_one : s ((t0 + t1) / 2) < 1 := by
          rw [hs_mid]
          exact hmid_lt
        linarith
  have hsub_pos :
      0 < ∫ t in Set.Ioc 0 t1, (1 - s t) ∂volume := by
    simpa [intervalIntegral.integral_of_le t1_pos.le] using hsub_pos_interval
  have hdiff_pos :
      0 < (∫ t in Set.Ioc 0 t1, (1 : Real) ∂volume) - ∫ t in Set.Ioc 0 t1, s t ∂volume := by
    simpa [hsub_eq] using hsub_pos
  linarith [hdiff_pos, hconst]

lemma H_t1_gt_B : H t1 > B := by
  have hs_cont : Continuous (fun t : Real => s t) := by
    unfold s
    exact Continuous.min continuous_const
      (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
  have hs_ioc : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioc 0 t1) := by
    exact hs_cont.integrableOn_Ioc
  have hs_iou : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioi t1) := by
    exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi t1_pos.le))
  have htail_nonneg : 0 ≤ ∫ t in Set.Ioi t1, s t ∂volume := by
    exact MeasureTheory.integral_nonneg (fun t => by
      unfold s
      exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _)))
  have hA_split :
      A = (∫ t in Set.Ioc 0 t1, s t ∂volume) + (∫ t in Set.Ioi t1, s t ∂volume) := by
    unfold A
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc hs_iou]
    rw [Set.Ioc_union_Ioi_eq_Ioi t1_pos.le]
  have hA_lt : A < t1 + ∫ t in Set.Ioi t1, s t ∂volume := by
    rw [hA_split]
    linarith [integral_s_Ioc_0_t1_lt_t1]
  have hB_lt : B < t1 / 2 + ∫ t in Set.Ioi t1, s t ∂volume := by
    unfold B
    nlinarith [hA_lt]
  have hHt1 : H t1 = t1 / 2 + ∫ t in Set.Ioi t1, s t ∂volume := by
    unfold H
    rw [s_t1_eq_half]
    ring
  linarith [hB_lt, hHt1]

lemma a_gt_t1 : a > t1 := by
  by_contra hnot
  have ha_le_t1 : a ≤ t1 := le_of_not_gt hnot
  have hanti := H_strictAntiOn.antitoneOn
  have hHt1_le_Ha : H t1 ≤ H a := hanti (Set.mem_Ioi.mpr a_spec.1)
    (Set.mem_Ioi.mpr t0_lt_t1) ha_le_t1
  linarith [hHt1_le_Ha, H_t1_gt_B, a_spec.2]

lemma p0_lt_half : p0 < 1 / 2 := by
  have hp0_eq : p0 = 2 * Real.exp (-(a ^ 2) / 2) := by
    simpa [p0] using s_eq_gauss_tail_of_gt_t0 a_spec.1
  have hsq : t1 ^ 2 < a ^ 2 := by
    have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
    nlinarith [a_gt_t1, ha_pos, t1_pos]
  have hexp_lt : Real.exp (-(a ^ 2) / 2) < Real.exp (-(t1 ^ 2) / 2) := by
    exact Real.exp_lt_exp.mpr (by nlinarith [hsq])
  have hmul_lt : 2 * Real.exp (-(a ^ 2) / 2) < 2 * Real.exp (-(t1 ^ 2) / 2) := by
    exact mul_lt_mul_of_pos_left hexp_lt (by norm_num : (0 : Real) < 2)
  linarith [hmul_lt, hp0_eq, two_exp_neg_t1_sq_div_two_eq_half]

/-! ## 3. Tail constraints and envelope -/

def prob (mu : Measure Real) (S : Set Real) : Real := (mu S).toReal

def absTail (mu : Measure Real) (t : Real) : Real := prob mu {x : Real | |x| > t}

def subgaussianTail (mu : Measure Real) : Prop :=
  ∀ t : Real, 0 <= t → absTail mu t <= 2 * Real.exp (-(t ^ 2) / 2)

lemma J_eq_integral_Ioi_of_ge_a (x : Real) (hx : a ≤ x) : J x = ∫ t in Set.Ioi x, s t ∂volume := by
  by_cases h : x > a
  · exact J_of_gt_a h
  · have heq : x = a := le_antisymm (le_of_not_gt h) hx
    subst heq
    have hB : B = a * p0 + ∫ t in Set.Ioi a, s t ∂volume := by
      have hHa : H a = B := a_spec.2
      have hHa' : B = a * s a + ∫ t in Set.Ioi a, s t ∂volume := by
        simpa [H] using hHa.symm
      simpa [p0] using hHa'
    calc
      J a = B - p0 * a := by simp [J]
      _ = ∫ t in Set.Ioi a, s t ∂volume := by linarith [hB]

lemma layer_cake_hinge
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → Real} (hY : Integrable Y P) (u : Real) :
    ∫ ω, hinge u (Y ω) ∂P = ∫ t in Set.Ioi u, (P {ω | Y ω > t}).toReal := by
  let f : Ω → Real := fun ω => hinge u (Y ω)
  have hIntf : Integrable f P := by
    unfold f hinge posPart
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part (hY.sub (MeasureTheory.integrable_const u)))
  have hnn : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall fun ω => by
    unfold f
    exact hinge_nonneg u (Y ω)
  have h0 : ∫ ω, f ω ∂P = ∫ t in Set.Ioi 0, (P {ω | t < f ω}).toReal := by
    simpa using (MeasureTheory.Integrable.integral_eq_integral_meas_lt (μ := P) hIntf hnn)
  have hset : ∀ t > 0, {ω | t < f ω} = {ω | u + t < Y ω} := by
    intro t ht
    ext ω
    constructor
    · intro h
      have h1 : t < max (Y ω - u) 0 := by simpa [f, hinge, posPart] using h
      have hYu : t < Y ω - u := by
        exact (lt_max_iff.mp h1).resolve_right ht.not_gt
      exact Set.mem_setOf.mpr (by linarith [hYu])
    · intro h
      have hux : u + t < Y ω := by simpa using h
      have hYu : t < Y ω - u := by linarith [hux]
      have hmax : t < max (Y ω - u) 0 := (lt_max_iff.mpr (Or.inl hYu))
      exact Set.mem_setOf.mpr (by simpa [f, hinge, posPart] using hmax)
  have h0' :
      ∫ t in Set.Ioi 0, (P {ω | t < f ω}).toReal
        = ∫ t in Set.Ioi 0, (P {ω | u + t < Y ω}).toReal := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    simpa using congrArg (fun S => (P S).toReal) (hset t ht)
  let g : Real → Real := fun t => (P {ω | t < Y ω}).toReal
  have hind :
      (fun t => Set.indicator (Set.Ioi 0) (fun x => g (u + x)) t)
        = fun t => Set.indicator (Set.Ioi u) g (t + u) := by
    funext t
    by_cases ht : t ∈ Set.Ioi 0
    · have htu : t + u ∈ Set.Ioi u := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp ht])
      have htu' : u + t ∈ Set.Ioi u := by simpa [add_comm] using htu
      simp [Set.indicator_of_mem, ht, htu', g, add_comm]
    · have hnot : t + u ∉ Set.Ioi u := by
        intro htu
        exact ht (Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp htu]))
      simp [Set.indicator_of_notMem, ht, hnot, g]
  have hshift :
      ∫ t in Set.Ioi 0, g (u + t)
        = ∫ t in Set.Ioi u, g t := by
    calc
      ∫ t in Set.Ioi 0, g (u + t)
          = ∫ t, Set.indicator (Set.Ioi 0) (fun x => g (u + x)) t := by
              rw [← MeasureTheory.integral_indicator (μ := (volume : Measure Real))
                (f := fun x => g (u + x)) (hs := measurableSet_Ioi)]
      _ = ∫ t, Set.indicator (Set.Ioi u) g (t + u) := by rw [hind]
      _ = ∫ t, Set.indicator (Set.Ioi u) g t := by
            simpa using
              (MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure Real))
                (f := fun t => Set.indicator (Set.Ioi u) g t) (g := u))
      _ = ∫ t in Set.Ioi u, g t := by
            rw [MeasureTheory.integral_indicator (μ := (volume : Measure Real)) (f := g)
              (hs := measurableSet_Ioi)]
  calc
    ∫ ω, hinge u (Y ω) ∂P = ∫ ω, f ω ∂P := rfl
    _ = ∫ t in Set.Ioi 0, (P {ω | t < f ω}).toReal := h0
    _ = ∫ t in Set.Ioi 0, (P {ω | u + t < Y ω}).toReal := h0'
    _ = ∫ t in Set.Ioi 0, g (u + t) := rfl
    _ = ∫ t in Set.Ioi u, g t := hshift
    _ = ∫ t in Set.Ioi u, (P {ω | Y ω > t}).toReal := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          simp [g]

lemma stopLoss_eq_integral_tail
    {μ : Measure Real} [IsProbabilityMeasure μ] (u : Real) :
    stopLoss μ u = ∫ t in Set.Ioi u, prob μ {x : Real | x > t} ∂MeasureTheory.volume := by
  have h_layer_cake :
      ∫ x, hinge u x ∂μ = ∫ t in Set.Ioi u, (μ {x : Real | x > t}).toReal ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
    · have h_integral_def :
          ∫⁻ x, ENNReal.ofReal (hinge u x) ∂μ =
            ∫⁻ t in Set.Ioi u, μ {x : Real | x > t} ∂MeasureTheory.volume := by
        rw [MeasureTheory.lintegral_eq_lintegral_meas_lt]
        · rw [← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator] <;>
            norm_num [Set.indicator]
          rw [← MeasureTheory.lintegral_add_right_eq_self]
          swap
          · exact -u
          · grind
        · exact Filter.Eventually.of_forall fun x => le_max_right _ _
        · exact Measurable.aemeasurable <|
            Measurable.max (measurable_id.sub measurable_const) measurable_const
      rw [h_integral_def, MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
      · rw [MeasureTheory.lintegral_congr_ae]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht using by
          rw [ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top _ _)]
      · exact Filter.Eventually.of_forall fun t => ENNReal.toReal_nonneg
      · have h_meas : Measurable (fun t => μ {x | x > t}) := by
          apply_rules [Antitone.measurable, measurable_const]
          exact fun t t' h => MeasureTheory.measure_mono fun x hx => lt_of_le_of_lt h hx
        exact h_meas.ennreal_toReal.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => le_max_right _ _
    · exact Measurable.aestronglyMeasurable <|
        Measurable.max (measurable_id.sub measurable_const) measurable_const
  unfold stopLoss prob
  simpa using h_layer_cake

lemma s_nonneg (t : Real) : 0 ≤ s t := by
  unfold s
  exact le_min zero_le_one (by positivity)

lemma first_moment_bound
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0) :
    ∫ x, |x| ∂mu ≤ A ∧ stopLoss mu 0 ≤ B := by
  have hIntAbs : Integrable (fun x : Real => |x|) mu := hIntMuId.norm
  have hLayerAbs :
      ∫ x, |x| ∂mu = ∫ t in Set.Ioi 0, (mu {x : Real | |x| > t}).toReal := by
    calc
      ∫ x, |x| ∂mu = ∫ x, hinge 0 (|x|) ∂mu := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun x => by
          simp [hinge, posPart])
      _ = ∫ t in Set.Ioi 0, (mu {x : Real | |x| > t}).toReal := by
        simpa [hinge, posPart] using
          (layer_cake_hinge (P := mu) (Y := fun x : Real => |x|) hIntAbs 0)
  have hAbsLeA : ∫ x, |x| ∂mu ≤ A := by
    rw [hLayerAbs, A]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => ENNReal.toReal_nonneg)
    · exact s_integrableOn_Ioi_zero
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have hprob_le_one : (mu {x : Real | |x| > t}).toReal ≤ 1 := by
        have hprob_le : mu {x : Real | |x| > t} ≤ (1 : ENNReal) := by
          calc
            mu {x : Real | |x| > t} ≤ mu Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
            _ = 1 := by simp
        simpa using ENNReal.toReal_mono (b := (1 : ENNReal)) (by simp) hprob_le
      have htail_t : (mu {x : Real | |x| > t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
        simpa [subgaussianTail, absTail, prob] using htail t (le_of_lt ht)
      exact le_min hprob_le_one htail_t
  have hStop0_repr : stopLoss mu 0 = (1 / 2 : Real) * ∫ x, |x| ∂mu := by
    have hrepr : ∀ x : Real, hinge 0 x = (x + |x|) / 2 := by
      intro x
      by_cases hx : 0 ≤ x
      · simp [hinge, posPart, hx, abs_of_nonneg hx]
      · have hx' : x < 0 := lt_of_not_ge hx
        simp [hinge, posPart, le_of_lt hx', abs_of_neg hx']
    have hIntPlus : Integrable (fun x : Real => (x + |x|) / 2) mu := (hIntMuId.add hIntAbs).div_const 2
    unfold stopLoss
    calc
      ∫ x, hinge 0 x ∂mu = ∫ x, (x + |x|) / 2 ∂mu := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall hrepr
      _ = (1 / 2 : Real) * (∫ x, x + |x| ∂mu) := by
        have hmul_repr : (fun x : Real => (x + |x|) / 2) = fun x => (1 / 2 : Real) * (x + |x|) := by
          funext x
          ring
        rw [hmul_repr, MeasureTheory.integral_const_mul]
      _ = ((∫ x, x ∂mu) + (∫ x, |x| ∂mu)) / 2 := by
        rw [MeasureTheory.integral_add hIntMuId hIntAbs]
        ring
      _ = (1 / 2 : Real) * ∫ x, |x| ∂mu := by
        have hmean0 : ∫ x, x ∂mu = 0 := by simpa [mean] using hmean
        rw [hmean0]
        ring
  have hStop0LeB : stopLoss mu 0 ≤ B := by
    rw [hStop0_repr, B]
    nlinarith [hAbsLeA]
  exact ⟨hAbsLeA, hStop0LeB⟩

lemma stopLoss_envelope_case_ge_a
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (u : Real) (hu : a ≤ u) :
    stopLoss mu u ≤ J u := by
  have hu0 : 0 < u := lt_trans t0_pos (lt_of_lt_of_le a_spec.1 hu)
  have hJ : J u = ∫ t in Set.Ioi u, s t ∂volume := J_eq_integral_Ioi_of_ge_a u hu
  calc
    stopLoss mu u = ∫ t in Set.Ioi u, (mu {x : Real | x > t}).toReal := by
      simpa [stopLoss, hinge, posPart] using
        (layer_cake_hinge (P := mu) (Y := fun x : Real => x) hIntMuId u)
    _ ≤ ∫ t in Set.Ioi u, s t ∂volume := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun t => ENNReal.toReal_nonneg)
      · exact s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi hu0.le)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have hprob_le_abs : (mu {x : Real | x > t}).toReal ≤ (mu {x : Real | |x| > t}).toReal := by
          refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top mu {x : Real | |x| > t}) ?_
          exact MeasureTheory.measure_mono (by
            intro x hx
            exact lt_of_lt_of_le hx (le_abs_self x))
        have hprob_le_one : (mu {x : Real | |x| > t}).toReal ≤ 1 := by
          have hprob_le : mu {x : Real | |x| > t} ≤ (1 : ENNReal) := by
            calc
              mu {x : Real | |x| > t} ≤ mu Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
              _ = 1 := by simp
          simpa using ENNReal.toReal_mono (b := (1 : ENNReal)) (by simp) hprob_le
        have htail_t : (mu {x : Real | |x| > t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
          have ht0 : 0 ≤ t := le_of_lt (lt_trans hu0 ht)
          simpa [subgaussianTail, absTail, prob] using htail t ht0
        have h_abs_le_s : (mu {x : Real | |x| > t}).toReal ≤ s t := le_min hprob_le_one htail_t
        exact le_trans hprob_le_abs h_abs_le_s
    _ = J u := hJ.symm

lemma hinge_convex_in_u (x : Real) : ConvexOn Real Set.univ (fun u : Real => hinge u x) := by
  unfold hinge posPart
  have h_aff : ConvexOn Real Set.univ (fun u : Real => x - u) := by
    refine ⟨convex_univ, ?_⟩
    intro u hu v hv a b ha hb hab
    dsimp
    ring_nf
    have habx : x * a + x * b = x := by
      calc
        x * a + x * b = x * (a + b) := by ring
        _ = x := by rw [hab, mul_one]
    linarith [habx]
  exact h_aff.sup (convexOn_const (0 : Real) convex_univ)

lemma stopLoss_convex
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu) :
    ConvexOn Real Set.univ (fun u : Real => stopLoss mu u) := by
  refine ⟨convex_univ, ?_⟩
  intro u hu v hv a b ha hb hab
  have hIntU : Integrable (fun x : Real => hinge u x) mu := by
    unfold hinge posPart
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part (hIntMuId.sub (MeasureTheory.integrable_const u)))
  have hIntV : Integrable (fun x : Real => hinge v x) mu := by
    unfold hinge posPart
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part (hIntMuId.sub (MeasureTheory.integrable_const v)))
  have hIntUV : Integrable (fun x : Real => hinge (a * u + b * v) x) mu := by
    unfold hinge posPart
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part
        (hIntMuId.sub (MeasureTheory.integrable_const (a * u + b * v))))
  have hIntRhs : Integrable (fun x : Real => a * hinge u x + b * hinge v x) mu :=
    (hIntU.const_mul a).add (hIntV.const_mul b)
  have hpoint :
      (fun x : Real => hinge (a * u + b * v) x) ≤ᵐ[mu]
        (fun x : Real => a * hinge u x + b * hinge v x) := by
    exact Filter.Eventually.of_forall (fun x => by
      have hconvx := hinge_convex_in_u x
      have hxineq : hinge (a * u + b * v) x ≤ a * hinge u x + b * hinge v x := by
        simpa using hconvx.2 (by simp) (by simp) ha hb hab
      exact hxineq)
  have hmono := MeasureTheory.integral_mono_ae hIntUV hIntRhs hpoint
  unfold stopLoss
  calc
    ∫ x, hinge (a * u + b * v) x ∂mu
      ≤ ∫ x, (a * hinge u x + b * hinge v x) ∂mu := hmono
    _ = a * (∫ x, hinge u x ∂mu) + b * (∫ x, hinge v x ∂mu) := by
      rw [MeasureTheory.integral_add (hIntU.const_mul a) (hIntV.const_mul b),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

lemma stopLoss_envelope_case_le_a
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0)
    (u : Real) (hu0 : 0 ≤ u) (hua : u ≤ a) :
    stopLoss mu u ≤ J u := by
  have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
  let θ : Real := u / a
  have hθ_nonneg : 0 ≤ θ := by
    exact div_nonneg hu0 ha_pos.le
  have hθ_le_one : θ ≤ 1 := by
    unfold θ
    exact (div_le_iff₀ ha_pos).2 (by simpa [one_mul] using hua)
  have hθsum : (1 - θ) + θ = 1 := by ring
  have hconv := stopLoss_convex (mu := mu) hIntMuId
  have hconv_ua :
      stopLoss mu u ≤ (1 - θ) * stopLoss mu 0 + θ * stopLoss mu a := by
    have htmp :
        stopLoss mu ((1 - θ) * (0 : Real) + θ * a) ≤
          (1 - θ) * stopLoss mu 0 + θ * stopLoss mu a := by
      exact hconv.2 (by simp) (by simp)
        (by nlinarith [hθ_nonneg, hθ_le_one]) hθ_nonneg hθsum
    have hu_expr : θ * a = u := by
      unfold θ
      field_simp [ha_pos.ne']
    simpa [hu_expr]
      using htmp
  have h0_bound : stopLoss mu 0 ≤ B := (first_moment_bound (mu := mu) hIntMuId htail hmean).2
  have ha_bound : stopLoss mu a ≤ J a := stopLoss_envelope_case_ge_a (mu := mu) hIntMuId htail a le_rfl
  have hJa : J a = B - p0 * a := J_of_le_a le_rfl
  have hrhs :
      (1 - θ) * stopLoss mu 0 + θ * stopLoss mu a ≤ B - p0 * u := by
    have h0_scaled :
        (1 - θ) * stopLoss mu 0 ≤ (1 - θ) * B := by
      exact mul_le_mul_of_nonneg_left h0_bound (by nlinarith [hθ_nonneg, hθ_le_one])
    have ha_scaled :
        θ * stopLoss mu a ≤ θ * (B - p0 * a) := by
      exact mul_le_mul_of_nonneg_left (by simpa [hJa] using ha_bound) hθ_nonneg
    have hu_expr : θ * a = u := by
      unfold θ
      field_simp [ha_pos.ne']
    have hcombine : (1 - θ) * B + θ * (B - p0 * a) = B - p0 * u := by
      calc
        (1 - θ) * B + θ * (B - p0 * a) = B - θ * p0 * a := by ring
        _ = B - p0 * (θ * a) := by ring
        _ = B - p0 * u := by rw [hu_expr]
    linarith [h0_scaled, ha_scaled, hcombine]
  have hJu : J u = B - p0 * u := J_of_le_a hua
  calc
    stopLoss mu u ≤ (1 - θ) * stopLoss mu 0 + θ * stopLoss mu a := hconv_ua
    _ ≤ B - p0 * u := hrhs
    _ = J u := hJu.symm

theorem stopLoss_envelope
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0) :
    (∀ u : Real, 0 <= u → stopLoss mu u <= J u) ∧
    (∀ u : Real, 0 <= u → stopLoss (Measure.map (fun x : Real => -x) mu) u <= J u) := by
  have hPos :
      ∀ u : Real, 0 ≤ u → stopLoss mu u ≤ J u := by
    intro u hu
    by_cases hua : u ≤ a
    · exact stopLoss_envelope_case_le_a (mu := mu) hIntMuId htail hmean u hu hua
    · exact stopLoss_envelope_case_ge_a (mu := mu) hIntMuId htail u (le_of_not_ge hua)
  have hProbMapNeg : IsProbabilityMeasure (Measure.map (fun x : Real => -x) mu) := by
    refine ⟨?_⟩
    rw [Measure.map_apply (Measurable.neg measurable_id') MeasurableSet.univ]
    simp
  letI : IsProbabilityMeasure (Measure.map (fun x : Real => -x) mu) := hProbMapNeg
  have hIntMapNeg :
      Integrable (fun x : Real => x) (Measure.map (fun x : Real => -x) mu) := by
    have hIntComp : Integrable ((fun x : Real => x) ∘ (fun x : Real => -x)) mu := by
      change Integrable (fun x : Real => -x) mu
      convert (hIntMuId.neg : Integrable (-fun x : Real => x) mu)
    refine
      (integrable_map_measure
        (μ := mu) (f := fun x : Real => -x) (g := fun x : Real => x)
        measurable_id'.aestronglyMeasurable
        (Measurable.neg measurable_id').aemeasurable).2 ?_
    exact hIntComp
  have hTailMapNeg : subgaussianTail (Measure.map (fun x : Real => -x) mu) := by
    intro t ht
    have hset :
        (fun x : Real => -x) ⁻¹' {x : Real | |x| > t} = {x : Real | |x| > t} := by
      ext x
      simp [abs_neg]
    have hmeas_abs : Measurable (fun x : Real => |x|) := by
      simpa using (continuous_abs.measurable : Measurable (fun x : Real => |x|))
    have hmeas : MeasurableSet {x : Real | |x| > t} := by
      simpa [Set.preimage] using (hmeas_abs measurableSet_Ioi)
    calc
      absTail (Measure.map (fun x : Real => -x) mu) t
          = (mu {x : Real | |x| > t}).toReal := by
              unfold absTail prob
              rw [Measure.map_apply (Measurable.neg measurable_id') hmeas, hset]
      _ ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
            simpa [subgaussianTail, absTail, prob] using htail t ht
  have hMeanMapNeg : mean (Measure.map (fun x : Real => -x) mu) = 0 := by
    unfold mean
    calc
      ∫ y, y ∂(Measure.map (fun x : Real => -x) mu)
          = ∫ x, -x ∂mu := by
              exact MeasureTheory.integral_map
                (μ := mu) (φ := fun x : Real => -x) (f := fun y : Real => y)
                (hφ := (Measurable.neg measurable_id').aemeasurable)
                (hfm := measurable_id'.aestronglyMeasurable)
      _ = -∫ x, x ∂mu := by
            simpa using (MeasureTheory.integral_neg (f := fun x : Real => x))
      _ = 0 := by
            have hmean0 : ∫ x, x ∂mu = 0 := by simpa [mean] using hmean
            simp [hmean0]
  have hNeg :
      ∀ u : Real, 0 ≤ u →
        stopLoss (Measure.map (fun x : Real => -x) mu) u ≤ J u := by
    intro u hu
    by_cases hua : u ≤ a
    · exact stopLoss_envelope_case_le_a
        (mu := Measure.map (fun x : Real => -x) mu) hIntMapNeg hTailMapNeg hMeanMapNeg u hu hua
    · exact stopLoss_envelope_case_ge_a
        (mu := Measure.map (fun x : Real => -x) mu) hIntMapNeg hTailMapNeg u (le_of_not_ge hua)
  exact ⟨hPos, hNeg⟩

lemma stopLoss_extend_all_u
    {mu nu : Measure Real} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hIntMu : Integrable (fun x : Real => x) mu)
    (hIntNu : Integrable (fun x : Real => x) nu)
    (hmean : mean mu = mean nu)
    (hpos : ∀ u : Real, 0 <= u → stopLoss mu u <= stopLoss nu u)
    (hneg : ∀ u : Real, 0 <= u →
      stopLoss (Measure.map (fun x : Real => -x) mu) u <=
      stopLoss (Measure.map (fun x : Real => -x) nu) u) :
    ∀ u : Real, stopLoss mu u <= stopLoss nu u
    := by
  intro u
  by_cases hu : 0 <= u
  · exact hpos u hu
  · have hv : 0 < -u := by linarith
    let v : Real := -u
    have hv0 : 0 <= v := le_of_lt hv
    have hIntHingeMu : Integrable (fun x : Real => hinge v (-x)) mu := by
      subst v
      unfold hinge posPart
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (MeasureTheory.Integrable.pos_part ((hIntMu.neg).sub (MeasureTheory.integrable_const (-u))))
    have hIntHingeNu : Integrable (fun x : Real => hinge v (-x)) nu := by
      subst v
      unfold hinge posPart
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (MeasureTheory.Integrable.pos_part ((hIntNu.neg).sub (MeasureTheory.integrable_const (-u))))
    have hsplit_mu : stopLoss mu u = -u + mean mu + stopLoss (Measure.map (fun x : Real => -x) mu) v := by
      have h_expansion : ∀ x : Real, hinge u x = x - u + hinge v (-x) := by
        intro x
        subst v
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hinge_neg_threshold x (-u)
      unfold stopLoss mean
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_expansion)]
      have hsplit_int :
          ∫ a, (a - u) + hinge v (-a) ∂mu
            = (∫ a, a - u ∂mu) + ∫ a, hinge v (-a) ∂mu :=
        MeasureTheory.integral_add (hIntMu.sub (MeasureTheory.integrable_const u)) hIntHingeMu
      rw [hsplit_int, MeasureTheory.integral_sub hIntMu (MeasureTheory.integrable_const u)]
      have hmap :
          ∫ y, hinge v y ∂(Measure.map (fun x : Real => -x) mu) =
            ∫ x, hinge v (-x) ∂mu := by
        exact MeasureTheory.integral_map
          (μ := mu) (φ := fun x : Real => -x) (f := hinge v)
          (hφ := (Measurable.neg measurable_id').aemeasurable)
          (hfm := (Measurable.max (measurable_id.sub_const v) measurable_const).aestronglyMeasurable)
      rw [← hmap]
      simp
      ring_nf
    have hsplit_nu : stopLoss nu u = -u + mean nu + stopLoss (Measure.map (fun x : Real => -x) nu) v := by
      have h_expansion : ∀ x : Real, hinge u x = x - u + hinge v (-x) := by
        intro x
        subst v
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hinge_neg_threshold x (-u)
      unfold stopLoss mean
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_expansion)]
      have hsplit_int :
          ∫ a, (a - u) + hinge v (-a) ∂nu
            = (∫ a, a - u ∂nu) + ∫ a, hinge v (-a) ∂nu :=
        MeasureTheory.integral_add (hIntNu.sub (MeasureTheory.integrable_const u)) hIntHingeNu
      rw [hsplit_int, MeasureTheory.integral_sub hIntNu (MeasureTheory.integrable_const u)]
      have hmap :
          ∫ y, hinge v y ∂(Measure.map (fun x : Real => -x) nu) =
            ∫ x, hinge v (-x) ∂nu := by
        exact MeasureTheory.integral_map
          (μ := nu) (φ := fun x : Real => -x) (f := hinge v)
          (hφ := (Measurable.neg measurable_id').aemeasurable)
          (hfm := (Measurable.max (measurable_id.sub_const v) measurable_const).aestronglyMeasurable)
      rw [← hmap]
      simp
      ring_nf
    have hnegv :
        stopLoss (Measure.map (fun x : Real => -x) mu) v <=
          stopLoss (Measure.map (fun x : Real => -x) nu) v := hneg v hv0
    rw [hsplit_mu, hsplit_nu]
    nlinarith [hnegv, hmean]

/-! ## 4. Gaussian objects and comparison -/

def phi (t : Real) : Real :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)

def PhiBar (t : Real) : Real := ∫ x in Set.Ioi t, phi x ∂volume

def R (c u : Real) : Real := PhiBar (u / c) / (2 * Real.exp (-u ^ 2 / 2))

lemma phi_pos (x : Real) : 0 < phi x := by
  unfold phi
  positivity

lemma phi_nonneg (x : Real) : 0 <= phi x := (phi_pos x).le

lemma phi_integrable : MeasureTheory.Integrable (fun x => phi x) := by
  unfold phi
  exact MeasureTheory.Integrable.const_mul
    (by
      simpa [div_eq_inv_mul] using
        (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 2)))
    _

lemma integral_phi_univ : ∫ x, phi x ∂MeasureTheory.volume = 1 := by
  have hgauss : ∫ x : Real, Real.exp (-(x ^ 2) / 2) ∂MeasureTheory.volume =
      Real.sqrt (Real.pi / (1 / 2 : Real)) := by
    simpa [div_eq_inv_mul] using (integral_gaussian (1 / 2 : Real))
  unfold phi
  rw [MeasureTheory.integral_const_mul]
  calc
    (1 / Real.sqrt (2 * Real.pi)) * ∫ x : Real, Real.exp (-(x ^ 2) / 2) ∂MeasureTheory.volume
        = (1 / Real.sqrt (2 * Real.pi)) * Real.sqrt (Real.pi / (1 / 2 : Real)) := by
          rw [hgauss]
    _ = (1 / Real.sqrt (2 * Real.pi)) * Real.sqrt (2 * Real.pi) := by
          congr 2
          ring_nf
    _ = 1 := by
          field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]

lemma phi_deriv (x : Real) : deriv phi x = -x * phi x := by
  have hExp :
      HasDerivAt (fun t : Real => Real.exp (t ^ 2 * (-(1 / 2 : Real))))
        (Real.exp (x ^ 2 * (-(1 / 2 : Real))) * ((2 * x) * (-(1 / 2 : Real)))) x := by
    simpa using
      (Real.hasDerivAt_exp (x ^ 2 * (-(1 / 2 : Real)))).comp x
        ((hasDerivAt_pow 2 x).mul_const (-(1 / 2 : Real)))
  have hMul :
      HasDerivAt
        (fun t : Real => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (t ^ 2 * (-(1 / 2 : Real))))
        ((1 / Real.sqrt (2 * Real.pi)) *
          (Real.exp (x ^ 2 * (-(1 / 2 : Real))) * ((2 * x) * (-(1 / 2 : Real)))) ) x := by
    exact hExp.const_mul (1 / Real.sqrt (2 * Real.pi))
  have h : HasDerivAt phi (-x * phi x) x := by
    unfold phi
    convert hMul using 1
    · ext t
      congr 1
      ring_nf
    · ring_nf
  exact h.deriv

lemma integral_Ioi_mul_exp_neg_sq_half (a : Real) :
    ∫ x in Set.Ioi a, x * (Real.exp (-(x ^ 2) / 2)) ∂MeasureTheory.volume =
      Real.exp (-(a ^ 2) / 2) := by
  have h_interval :
      ∀ b > a, ∫ x in a..b, x * (Real.exp (-(x ^ 2) / 2)) ∂MeasureTheory.volume =
        -Real.exp (-(b ^ 2) / 2) + Real.exp (-(a ^ 2) / 2) := by
    intro b hb
    rw [intervalIntegral.integral_deriv_eq_sub']
    rotate_left
    exacts
      [ fun x => -Real.exp (-(x ^ 2) / 2),
        funext fun x => by norm_num; ring,
        fun x hx => by norm_num,
        Continuous.continuousOn <| by continuity,
        by ring ]
  have h_tend :
      Filter.Tendsto
        (fun b => ∫ x in a..b, x * (Real.exp (-(x ^ 2) / 2)) ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in Set.Ioi a, x * (Real.exp (-(x ^ 2) / 2)) ∂MeasureTheory.volume)) := by
    apply_rules [MeasureTheory.intervalIntegral_tendsto_integral_Ioi]
    · have h_integrable : MeasureTheory.Integrable (fun x => x * (Real.exp (-(x ^ 2) / 2))) MeasureTheory.volume := by
        simpa [pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : Real)) (by norm_num) (s := (1 : Real)) (by norm_num))
      exact h_integrable.integrableOn
    · exact Filter.tendsto_id
  exact tendsto_nhds_unique h_tend
    (Filter.Tendsto.congr'
      (by
        filter_upwards [Filter.eventually_gt_atTop a] with b hb
        aesop)
      (by
        simpa using
          Filter.Tendsto.add
            (Filter.Tendsto.neg
              (Real.tendsto_exp_atBot.comp <|
                by
                  exact Filter.Tendsto.atBot_div_const (by positivity) <|
                    by simp))
            tendsto_const_nhds))

lemma integral_Ioi_mul_phi (a : Real) :
    ∫ x in Set.Ioi a, x * phi x ∂MeasureTheory.volume = phi a := by
  convert congrArg (fun x => x * (1 / Real.sqrt (2 * Real.pi)))
      (integral_Ioi_mul_exp_neg_sq_half a) using 1
  · rw [← MeasureTheory.integral_mul_const]
    congr
    ext x
    unfold phi
    ring
  · unfold phi
    ring

lemma PhiBar_strictAnti : StrictAnti PhiBar := by
  intro x y hxy
  have hdiff :
      PhiBar x - PhiBar y = ∫ t in Set.Ioc x y, phi t ∂MeasureTheory.volume := by
    rw [PhiBar, PhiBar, ← MeasureTheory.integral_diff measurableSet_Ioi
      (phi_integrable.integrableOn) (Set.Ioi_subset_Ioi hxy.le)]
    congr
    ext t
    constructor
    · intro ht
      exact ⟨ht.1, le_of_not_gt ht.2⟩
    · intro ht
      exact ⟨ht.1, not_lt_of_ge ht.2⟩
  have hpos_interval : 0 < ∫ t in x..y, phi t := by
    refine intervalIntegral.integral_pos hxy ?_ ?_ ?_
    · unfold phi
      exact Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)) |>.continuousOn
    · intro t ht
      exact phi_nonneg t
    · refine ⟨(x + y) / 2, ?_, ?_⟩
      · constructor <;> nlinarith
      · exact phi_pos ((x + y) / 2)
  have hpos_ioc : 0 < ∫ t in Set.Ioc x y, phi t ∂MeasureTheory.volume := by
    simpa [intervalIntegral.integral_of_le hxy.le] using hpos_interval
  linarith [hdiff, hpos_ioc]

lemma PhiBar_tendsto_atTop_zero : Filter.Tendsto PhiBar Filter.atTop (nhds (0 : Real)) := by
  unfold PhiBar
  have h_integrable : MeasureTheory.IntegrableOn (fun t => phi t) (Set.Ioi 0) := phi_integrable.integrableOn
  have h_int_zero :
      Filter.Tendsto (fun x => ∫ t in Set.Ioi 0, phi t * (if t > x then 1 else 0))
        Filter.atTop (nhds 0) := by
    have h_int_zero :
        Filter.Tendsto (fun x => ∫ t in Set.Ioi 0, phi t * (if t > x then 1 else 0))
          Filter.atTop (nhds (∫ t : Real in Set.Ioi 0, (0 : Real) ∂MeasureTheory.volume)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
        (l := Filter.atTop)
        (F := fun x t => phi t * (if t > x then 1 else 0))
        (f := fun _ => 0)
        (bound := fun t => |phi t|)
        ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun n =>
          MeasureTheory.AEStronglyMeasurable.mul
            h_integrable.aestronglyMeasurable
            (Measurable.aestronglyMeasurable
              (by exact Measurable.ite measurableSet_Ioi measurable_const measurable_const))
      · filter_upwards [Filter.eventually_gt_atTop 0] with n hn using
          Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num [abs_mul]
      · exact h_integrable.abs
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx using
          tendsto_const_nhds.congr'
            (by
              filter_upwards [Filter.eventually_gt_atTop x] with n hn
              split_ifs <;> linarith)
    simpa using h_int_zero
  refine h_int_zero.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
  rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
  congr
  ext
  split_ifs <;> linarith

lemma PhiBar_tendsto_atBot_one : Filter.Tendsto PhiBar Filter.atBot (nhds (1 : Real)) := by
  unfold PhiBar
  have h_int_one :
      Filter.Tendsto (fun x => ∫ t, phi t * (if t > x then 1 else 0) ∂MeasureTheory.volume)
        Filter.atBot (nhds (∫ t : Real, phi t ∂MeasureTheory.volume)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume)
      (l := Filter.atBot)
      (F := fun x t => phi t * (if t > x then 1 else 0))
      (f := fun t => phi t)
      (bound := fun t => |phi t|)
      ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun n =>
        MeasureTheory.AEStronglyMeasurable.mul
          phi_integrable.aestronglyMeasurable
          (Measurable.aestronglyMeasurable
            (by exact Measurable.ite measurableSet_Ioi measurable_const measurable_const))
    · filter_upwards [Filter.eventually_lt_atBot 0] with n hn using
        Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num [abs_mul]
    · exact phi_integrable.abs
    · exact Filter.Eventually.of_forall fun t =>
        tendsto_const_nhds.congr'
          (by
            filter_upwards [Filter.eventually_lt_atBot t] with x hx
            split_ifs <;> linarith)
  have h_int_one' :
      Filter.Tendsto (fun x => ∫ t, phi t * (if t > x then 1 else 0) ∂MeasureTheory.volume)
        Filter.atBot (nhds (1 : Real)) := by
    simpa [integral_phi_univ] using h_int_one
  refine h_int_one'.congr' ?_
  exact Filter.Eventually.of_forall fun x => by
    change (∫ t, phi t * (if t > x then 1 else 0) ∂MeasureTheory.volume) =
      ∫ t in Set.Ioi x, phi t ∂MeasureTheory.volume
    have hmul :
        (fun t : Real => phi t * (if t > x then 1 else 0))
          = (fun t : Real => (Set.Ioi x).indicator (fun t => phi t) t) := by
            funext t
            by_cases ht : t > x <;> simp [Set.indicator, ht]
    rw [hmul, MeasureTheory.integral_indicator measurableSet_Ioi]

lemma PhiBar_continuous : Continuous PhiBar := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  have h_tend :
      Filter.Tendsto (fun z => ∫ t, phi t * (if t > z then 1 else 0) ∂MeasureTheory.volume)
        (nhds x)
        (nhds (∫ t, phi t * (if t > x then 1 else 0) ∂MeasureTheory.volume)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume)
      (l := nhds x)
      (F := fun z t => phi t * (if t > z then 1 else 0))
      (f := fun t => phi t * (if t > x then 1 else 0))
      (bound := fun t => |phi t|)
      ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun n =>
        MeasureTheory.AEStronglyMeasurable.mul
          phi_integrable.aestronglyMeasurable
          (Measurable.aestronglyMeasurable
            (by exact Measurable.ite measurableSet_Ioi measurable_const measurable_const))
    · exact Filter.Eventually.of_forall fun n =>
        Filter.Eventually.of_forall fun t => by
          by_cases htn : t > n <;> simp [htn]
    · exact phi_integrable.abs
    · filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (MeasureTheory.measure_singleton x)] with t ht
      by_cases hxt : x < t
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Iio_mem_nhds hxt] with z hz
        have htz : t > z := hz
        simp [hxt, htz]
      · have htx_ne : t ≠ x := by simpa [Set.mem_singleton_iff] using ht
        have htx : t < x := lt_of_le_of_ne (le_of_not_gt hxt) htx_ne
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioi_mem_nhds htx] with z hz
        have htz : t < z := hz
        have htx' : ¬ t > x := not_lt_of_ge htx.le
        have htz' : ¬ t > z := not_lt_of_ge htz.le
        simp [htx', htz']
  have h_tend' :
      Filter.Tendsto (fun z => ∫ t in Set.Ioi z, phi t ∂MeasureTheory.volume)
        (nhds x)
        (nhds (∫ t, phi t * (if t > x then 1 else 0) ∂MeasureTheory.volume)) := by
    refine h_tend.congr' ?_
    exact Filter.Eventually.of_forall fun z => by
      change (∫ t, phi t * (if t > z then 1 else 0) ∂MeasureTheory.volume) =
        ∫ t in Set.Ioi z, phi t ∂MeasureTheory.volume
      have hmul :
          (fun t : Real => phi t * (if t > z then 1 else 0))
            = (fun t : Real => (Set.Ioi z).indicator (fun t => phi t) t) := by
              funext t
              by_cases htz : t > z <;> simp [Set.indicator, htz]
      rw [hmul, MeasureTheory.integral_indicator measurableSet_Ioi]
  have hx_eq :
      (∫ t, (if x < t then phi t else 0) ∂MeasureTheory.volume) =
        ∫ t in Set.Ioi x, phi t ∂MeasureTheory.volume := by
    simpa [Set.indicator] using
      (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
        (s := Set.Ioi x) (f := fun t : Real => phi t) measurableSet_Ioi)
  simpa [hx_eq, PhiBar] using h_tend'

lemma PhiBar_deriv (t : Real) : deriv PhiBar t = -phi t := by
  have h_ftc : deriv (fun t => ∫ x in Set.Ioi t, phi x ∂MeasureTheory.volume) t = -phi t := by
    have h_iic : deriv (fun t => ∫ x in Set.Iic t, phi x ∂MeasureTheory.volume) t = phi t := by
      have h_interval : ∀ a b : Real,
          deriv (fun t => ∫ x in a..t, phi x ∂MeasureTheory.volume) b = phi b := by
        intro a b
        apply_rules [Continuous.deriv_integral]
        unfold phi
        exact Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity))
      have h_eq : ∀ a t : Real, a < t →
          ∫ x in Set.Iic t, phi x ∂MeasureTheory.volume =
            (∫ x in a..t, phi x ∂MeasureTheory.volume) +
              ∫ x in Set.Iic a, phi x ∂MeasureTheory.volume := by
        intro a t hat
        rw [intervalIntegral.integral_of_le hat.le, ← MeasureTheory.setIntegral_union] <;> norm_num [hat.le]
        · rw [Set.union_comm, Set.Iic_union_Ioc_eq_Iic hat.le]
        · exact Set.disjoint_left.mpr fun x hx1 hx2 => hx1.1.not_ge hx2.out
        · unfold phi
          exact Continuous.integrableOn_Ioc
            (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
        · exact phi_integrable.integrableOn
      have h_ev :
          (fun x => ∫ u in Set.Iic x, phi u ∂MeasureTheory.volume)
            =ᶠ[nhds t]
              (fun x => (∫ u in (t - 1)..x, phi u ∂MeasureTheory.volume) +
                ∫ u in Set.Iic (t - 1), phi u ∂MeasureTheory.volume) := by
        exact Filter.eventuallyEq_of_mem
          (Ioi_mem_nhds (show t > t - 1 by linarith))
          (fun x hx => h_eq (t - 1) x hx)
      have h_deriv_alt :
          deriv (fun x => (∫ u in (t - 1)..x, phi u ∂MeasureTheory.volume) +
            ∫ u in Set.Iic (t - 1), phi u ∂MeasureTheory.volume) t = phi t := by
        rw [deriv_add_const]
        exact h_interval (t - 1) t
      calc
        deriv (fun t => ∫ x in Set.Iic t, phi x ∂MeasureTheory.volume) t
            = deriv (fun x => (∫ u in (t - 1)..x, phi u ∂MeasureTheory.volume) +
                ∫ u in Set.Iic (t - 1), phi u ∂MeasureTheory.volume) t :=
              Filter.EventuallyEq.deriv_eq h_ev
        _ = phi t := h_deriv_alt
    have h_split : ∀ t : Real,
        ∫ x in Set.Ioi t, phi x ∂MeasureTheory.volume =
          (∫ x in Set.univ, phi x ∂MeasureTheory.volume) -
            (∫ x in Set.Iic t, phi x ∂MeasureTheory.volume) := by
      intro t
      rw [← MeasureTheory.integral_diff measurableSet_Iic phi_integrable.integrableOn]
      · rcongr x
        aesop
      · intro x
        simp
    rw [show (fun t => ∫ x in Set.Ioi t, phi x ∂MeasureTheory.volume) =
      fun t => (∫ x in Set.univ, phi x ∂MeasureTheory.volume) -
        ∫ x in Set.Iic t, phi x ∂MeasureTheory.volume from funext h_split]
    rw [deriv_const_sub, h_iic]
  simpa [PhiBar] using h_ftc

def gaussianMeasure : Measure Real :=
  ProbabilityTheory.gaussianReal 0 (1 : NNReal)

lemma gaussian_isProbability : IsProbabilityMeasure gaussianMeasure := by
  dsimp [gaussianMeasure]
  infer_instance
instance : IsProbabilityMeasure gaussianMeasure := gaussian_isProbability

def gaussianScale (c : Real) : Measure Real :=
  Measure.map (fun x : Real => c * x) gaussianMeasure

lemma gaussianScale_isProbability (c : Real) : IsProbabilityMeasure (gaussianScale c) := by
  let sigma : NNReal := (⟨c ^ 2, sq_nonneg c⟩ * (1 : NNReal))
  have hscale : gaussianScale c = ProbabilityTheory.gaussianReal 0 sigma := by
    unfold gaussianScale gaussianMeasure sigma
    simpa [zero_mul] using
      (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : Real)) (v := (1 : NNReal)) (c := c))
  rw [hscale]
  infer_instance

def gClosed (c u : Real) : Real := c * phi (u / c) - u * PhiBar (u / c)
def gSL (c u : Real) : Real := stopLoss (gaussianScale c) u

lemma gaussian_call_closed_form (c u : Real) (hc : 0 < c) :
    (∫ x, hinge u (c * x) * phi x ∂MeasureTheory.volume) =
      c * phi (u / c) - u * PhiBar (u / c) := by
  simp [hinge, posPart]
  have h_integral :
      ∫ x, max (c * x - u) 0 * phi x ∂MeasureTheory.volume =
        ∫ x in Set.Ioi (u / c), (c * x - u) * phi x ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator, div_lt_iff₀, hc]
    grind
  rw [h_integral]
  have h_gauss_integral_x :
      ∫ x in Set.Ioi (u / c), x * phi x ∂MeasureTheory.volume = phi (u / c) := by
    exact integral_Ioi_mul_phi (u / c)
  have h_int_xphi :
      MeasureTheory.IntegrableOn (fun x => x * phi x) (Set.Ioi (u / c)) := by
    have h_int_exp : MeasureTheory.Integrable (fun x => x * Real.exp (-(x ^ 2) / 2)) := by
      simpa [pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : Real)) (by norm_num) (s := (1 : Real)) (by norm_num))
    have h_int_const :
        MeasureTheory.IntegrableOn
          (fun x => (1 / Real.sqrt (2 * Real.pi)) * (x * Real.exp (-(x ^ 2) / 2)))
          (Set.Ioi (u / c)) := h_int_exp.integrableOn.const_mul _
    convert h_int_const using 1
    funext x
    unfold phi
    ring
  have h_int_phi : MeasureTheory.IntegrableOn (fun x => phi x) (Set.Ioi (u / c)) :=
    phi_integrable.integrableOn
  have h_rewrite :
      (fun x => (c * x - u) * phi x) =
        (fun x => c * (x * phi x) - u * phi x) := by
    funext x
    ring
  rw [h_rewrite, MeasureTheory.integral_sub (h_int_xphi.const_mul c) (h_int_phi.const_mul u)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [h_gauss_integral_x, PhiBar]

theorem gSL_eq_gClosed (c u : Real) (hc : 0 < c) : gSL c u = gClosed c u := by
  unfold gSL stopLoss gaussianScale gaussianMeasure
  have hmap :
      (∫ y, hinge u y ∂Measure.map (fun x : Real => c * x) (ProbabilityTheory.gaussianReal 0 (1 : NNReal))) =
        ∫ x, hinge u (c * x) ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal) :=
    MeasureTheory.integral_map
      (μ := ProbabilityTheory.gaussianReal 0 (1 : NNReal))
      (φ := fun x : Real => c * x)
      (f := hinge u)
      (hφ := (measurable_id'.const_mul c).aemeasurable)
      (hfm := (Measurable.max (measurable_id.sub_const u) measurable_const).aestronglyMeasurable)
  rw [hmap]
  have hgauss :
      (∫ x, hinge u (c * x) ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal)) =
        ∫ x, ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x * hinge u (c * x) ∂MeasureTheory.volume := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (μ := (0 : Real)) (v := (1 : NNReal))
        (f := fun x : Real => hinge u (c * x))
        (by norm_num : (1 : NNReal) ≠ 0))
  rw [hgauss]
  have hpdf :
      (fun x : Real => ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x * hinge u (c * x)) =
        (fun x : Real => hinge u (c * x) * phi x) := by
    funext x
    unfold phi
    simp [ProbabilityTheory.gaussianPDFReal, mul_left_comm, mul_comm]
  rw [hpdf]
  simpa [gClosed, mul_assoc, mul_left_comm, mul_comm] using gaussian_call_closed_form c u hc

theorem gClosed_deriv (c : Real) (hc : 0 < c) :
  deriv (fun u => gClosed c u) = fun u => -PhiBar (u / c) := by
  funext u
  have hphi_diff : DifferentiableAt Real phi (u / c) := by
    unfold phi
    fun_prop
  have hphi_at : HasDerivAt phi (-(u / c) * phi (u / c)) (u / c) := by
    have hphi0 : HasDerivAt phi (deriv phi (u / c)) (u / c) := (hasDerivAt_deriv_iff).2 hphi_diff
    simpa [phi_deriv (u / c)] using hphi0
  have hPhi_diff : DifferentiableAt Real PhiBar (u / c) := by
    exact differentiableAt_of_deriv_ne_zero (by
      rw [PhiBar_deriv]
      exact neg_ne_zero.mpr (phi_pos _).ne')
  have hPhi_at : HasDerivAt PhiBar (-phi (u / c)) (u / c) := by
    have hPhi0 : HasDerivAt PhiBar (deriv PhiBar (u / c)) (u / c) := (hasDerivAt_deriv_iff).2 hPhi_diff
    simpa [PhiBar_deriv (u / c)] using hPhi0
  have h_first :
      HasDerivAt (fun u => c * phi (u / c)) (-(u / c) * phi (u / c)) u := by
    have hcomp :
        HasDerivAt (fun u => phi (u / c))
          ((-(u / c) * phi (u / c)) * (1 / c)) u := by
      have hdiv : HasDerivAt (fun u => u / c) (1 / c) u := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id u).mul_const (1 / c)
      have hcomp0 :
          HasDerivAt (phi ∘ fun u => u / c)
            ((-(u / c) * phi (u / c)) * (1 / c)) u := HasDerivAt.comp u hphi_at hdiv
      simpa [Function.comp] using hcomp0
    convert hcomp.const_mul c using 1
    field_simp [hc.ne']
  have h_second :
      HasDerivAt (fun u => u * PhiBar (u / c))
        (PhiBar (u / c) + u * ((-phi (u / c)) * (1 / c))) u := by
    have hcomp :
        HasDerivAt (fun u => PhiBar (u / c))
          ((-phi (u / c)) * (1 / c)) u := by
      have hdiv : HasDerivAt (fun u => u / c) (1 / c) u := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id u).mul_const (1 / c)
      have hcomp0 :
          HasDerivAt (PhiBar ∘ fun u => u / c)
            ((-phi (u / c)) * (1 / c)) u := HasDerivAt.comp u hPhi_at hdiv
      simpa [Function.comp] using hcomp0
    simpa [one_mul] using (hasDerivAt_id u).mul hcomp
  have h_all :
      HasDerivAt (fun u => gClosed c u)
        ((-(u / c) * phi (u / c)) -
          (PhiBar (u / c) + u * ((-phi (u / c)) * (1 / c)))) u := by
    unfold gClosed
    exact h_first.sub h_second
  have h_simpl :
      (-(u / c) * phi (u / c)) -
        (PhiBar (u / c) + u * ((-phi (u / c)) * (1 / c)))
        = -PhiBar (u / c) := by
    field_simp [hc.ne']
    ring
  exact h_simpl ▸ h_all.deriv
theorem gClosed_convex (c : Real) (hc : 0 < c) :
  ConvexOn Real Set.univ (fun u => gClosed c u) := by
  have hPhiDiff : Differentiable Real PhiBar := by
    intro x
    exact differentiableAt_of_deriv_ne_zero (by
      rw [PhiBar_deriv]
      exact neg_ne_zero.mpr (phi_pos _).ne')
  have hgDiff : Differentiable Real (fun u => gClosed c u) := by
    intro u
    unfold gClosed
    have hfirst : DifferentiableAt Real (fun u => c * phi (u / c)) u := by
      unfold phi
      fun_prop
    have hsecond : DifferentiableAt Real (fun u => u * PhiBar (u / c)) u := by
      refine DifferentiableAt.mul differentiableAt_id ?_
      exact (hPhiDiff (u / c)).comp u (differentiableAt_id.div_const c)
    exact hfirst.sub hsecond
  have hmono : Monotone (deriv (fun u => gClosed c u)) := by
    intro x y hxy
    have hdiv : x / c <= y / c := by
      have hInv : 0 <= c⁻¹ := inv_nonneg.mpr hc.le
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hxy hInv
    have hcmp : -PhiBar (x / c) <= -PhiBar (y / c) := by
      by_cases hEq : x / c = y / c
      · simp [hEq]
      · have hlt : x / c < y / c := lt_of_le_of_ne hdiv hEq
        have hPhi : PhiBar (y / c) < PhiBar (x / c) := PhiBar_strictAnti hlt
        linarith
    simpa [gClosed_deriv c hc] using hcmp
  exact hmono.convexOn_univ_of_deriv hgDiff

theorem exists_unique_z : ∃! z : Real, PhiBar z = p0 := by
  have hp0_pos : 0 < p0 := by
    unfold p0 s
    exact lt_min zero_lt_one (mul_pos zero_lt_two (Real.exp_pos _))
  have hp0_lt1 : p0 < 1 := by
    have hp0_eq : p0 = 2 * Real.exp (-(a ^ 2) / 2) := by
      simpa [p0] using s_eq_gauss_tail_of_gt_t0 a_spec.1
    have hlt : 2 * Real.exp (-(a ^ 2) / 2) < 1 := by
      rw [← Real.log_lt_log_iff (by positivity) (by norm_num),
        Real.log_mul (by positivity) (by positivity), Real.log_exp]
      norm_num
      have ha : a > Real.sqrt (2 * Real.log 2) := by simpa [t0] using a_spec.1
      have hsq : 2 * Real.log 2 < a ^ 2 := by
        nlinarith [ha, Real.sqrt_nonneg (2 * Real.log 2),
          Real.mul_self_sqrt (show 0 <= 2 * Real.log 2 by positivity)]
      nlinarith [hsq]
    exact hp0_eq ▸ hlt
  obtain ⟨xHi, hxHi⟩ : ∃ x : Real, PhiBar x < p0 := by
    exact (PhiBar_tendsto_atTop_zero.eventually (Iio_mem_nhds hp0_pos)).exists
  obtain ⟨xLo, hxLo⟩ : ∃ x : Real, p0 < PhiBar x := by
    exact (PhiBar_tendsto_atBot_one.eventually (Ioi_mem_nhds hp0_lt1)).exists
  have hconn : IsConnected (Set.range PhiBar) := isConnected_range PhiBar_continuous
  have hp0_mem : p0 ∈ Set.range PhiBar := by
    exact hconn.Icc_subset (Set.mem_range_self xHi) (Set.mem_range_self xLo)
      ⟨le_of_lt hxHi, le_of_lt hxLo⟩
  obtain ⟨z, hz⟩ := hp0_mem
  refine ⟨z, hz, ?_⟩
  intro y hy
  exact PhiBar_strictAnti.injective (hy.trans hz.symm)

noncomputable def z : Real := Classical.choose exists_unique_z
lemma z_spec : PhiBar z = p0 := (Classical.choose_spec exists_unique_z).1

lemma PhiBar_zero_eq_half : PhiBar 0 = 1 / 2 := by
  have h_half_gauss :
      ∫ x in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) ∂MeasureTheory.volume
        = (1 / 2) * (Real.sqrt 2 * Real.sqrt Real.pi) := by
    have hraw := integral_gaussian_Ioi (1 / 2)
    norm_num [div_eq_inv_mul] at hraw
    convert hraw using 2 with x
    ring_nf
  have hsqrt : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (show 0 ≤ (2 : Real) by norm_num)]
  unfold PhiBar phi
  rw [MeasureTheory.integral_const_mul, h_half_gauss]
  rw [← hsqrt]
  field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]

lemma z_pos : 0 < z := by
  have hPhi0_gt : PhiBar 0 > p0 := by
    linarith [PhiBar_zero_eq_half, p0_lt_half]
  by_contra hz
  have hz_le : z ≤ 0 := le_of_not_gt hz
  have hanti : Antitone PhiBar := PhiBar_strictAnti.antitone
  have hle : PhiBar 0 ≤ PhiBar z := hanti hz_le
  have hp0_ge : PhiBar 0 ≤ p0 := by simpa [z_spec] using hle
  linarith

noncomputable def c0 : Real := B / phi z
noncomputable def uStar : Real := c0 * z

lemma gaussian_tangent :
    deriv (fun u => gClosed c0 u) uStar = -p0 ∧
    gClosed c0 uStar = B - p0 * uStar := by
  have hs_pos : ∀ t : Real, 0 < s t := by
    intro t
    unfold s
    exact lt_min zero_lt_one (mul_pos zero_lt_two (Real.exp_pos _))
  have ht0_pos : 0 < t0 := by
    unfold t0
    refine Real.sqrt_pos.mpr ?_
    positivity
  have ha_pos : 0 < a := lt_trans ht0_pos a_spec.1
  have h_tail_nonneg : 0 <= ∫ t in Set.Ioi a, s t ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact (hs_pos t).le
  have hHapos : 0 < H a := by
    unfold H
    nlinarith [ha_pos, hs_pos a, h_tail_nonneg]
  have hB_pos : 0 < B := by
    simpa [a_spec.2] using hHapos
  have hphi_pos : 0 < phi z := by
    unfold phi
    positivity
  have hc0 : 0 < c0 := by
    unfold c0
    exact div_pos hB_pos hphi_pos
  have hratio : uStar / c0 = z := by
    unfold uStar
    field_simp [hc0.ne']
  have hderiv_eval :
      deriv (fun u => gClosed c0 u) uStar = -PhiBar z := by
    have hderiv_fn := congrArg (fun f => f uStar) (gClosed_deriv c0 hc0)
    simpa [hratio] using hderiv_fn
  have hderiv_final : deriv (fun u => gClosed c0 u) uStar = -p0 := by
    simpa [z_spec] using hderiv_eval
  have hBdef : c0 * phi z = B := by
    unfold c0
    field_simp [hphi_pos.ne']
  have hvalue :
      gClosed c0 uStar = B - p0 * uStar := by
    calc
      gClosed c0 uStar = c0 * phi z - uStar * PhiBar z := by
        simp [gClosed, hratio]
      _ = B - p0 * uStar := by
        simp [hBdef, z_spec, mul_comm]
  exact ⟨hderiv_final, hvalue⟩

lemma gaussian_above_tangent_line :
    ∀ u : Real, gClosed c0 u >= B - p0 * u := by
  have hs_pos : ∀ t : Real, 0 < s t := by
    intro t
    unfold s
    exact lt_min zero_lt_one (mul_pos zero_lt_two (Real.exp_pos _))
  have ht0_pos : 0 < t0 := by
    unfold t0
    refine Real.sqrt_pos.mpr ?_
    positivity
  have ha_pos : 0 < a := lt_trans ht0_pos a_spec.1
  have h_tail_nonneg : 0 <= ∫ t in Set.Ioi a, s t ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact (hs_pos t).le
  have hHapos : 0 < H a := by
    unfold H
    nlinarith [ha_pos, hs_pos a, h_tail_nonneg]
  have hB_pos : 0 < B := by
    simpa [a_spec.2] using hHapos
  have hphi_pos : 0 < phi z := by
    unfold phi
    positivity
  have hc0 : 0 < c0 := by
    unfold c0
    exact div_pos hB_pos hphi_pos
  have hconv : ConvexOn Real Set.univ (fun t => gClosed c0 t) := gClosed_convex c0 hc0
  have hp0_pos : 0 < p0 := by
    unfold p0
    exact hs_pos a
  have hfd : DifferentiableAt Real (fun t => gClosed c0 t) uStar := by
    apply differentiableAt_of_deriv_ne_zero
    have hderiv : deriv (fun t => gClosed c0 t) uStar = -p0 := gaussian_tangent.1
    rw [hderiv]
    exact neg_ne_zero.mpr (ne_of_gt hp0_pos)
  intro u
  by_cases hu : u = uStar
  · subst hu
    linarith [gaussian_tangent.2]
  · by_cases hlt : uStar < u
    · have hslope : deriv (fun t => gClosed c0 t) uStar <= slope (fun t => gClosed c0 t) uStar u := by
        exact hconv.deriv_le_slope (by simp) (by simp) hlt hfd
      have hslope' :
          deriv (fun t => gClosed c0 t) uStar <=
            (gClosed c0 u - gClosed c0 uStar) / (u - uStar) := by
        simpa [slope_def_field] using hslope
      have hmul :
          deriv (fun t => gClosed c0 t) uStar * (u - uStar) <=
            gClosed c0 u - gClosed c0 uStar := by
        exact (le_div_iff₀ (sub_pos.mpr hlt)).1 (by simpa using hslope')
      nlinarith [hmul, gaussian_tangent.1, gaussian_tangent.2]
    · have hlt' : u < uStar := lt_of_le_of_ne (le_of_not_gt hlt) hu
      have hslope :
          slope (fun t => gClosed c0 t) u uStar <= deriv (fun t => gClosed c0 t) uStar := by
        exact hconv.slope_le_deriv (by simp) (by simp) hlt' hfd
      have hslope' :
          (gClosed c0 uStar - gClosed c0 u) / (uStar - u) <=
            deriv (fun t => gClosed c0 t) uStar := by
        simpa [slope_def_field] using hslope
      have hmul :
          gClosed c0 uStar - gClosed c0 u <=
            deriv (fun t => gClosed c0 t) uStar * (uStar - u) := by
        exact (div_le_iff₀ (sub_pos.mpr hlt')).1 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hslope')
      nlinarith [hmul, gaussian_tangent.1, gaussian_tangent.2]

theorem lemma_gauss_ge_J_case1
    (_h_cond1 : a * (1 - 1 / c0 ^ 2) > 1) (_h_cond2 : c0 > 1)
    (u : Real) (_hu : 0 ≤ u) (hua : u ≤ a) :
    J u ≤ gClosed c0 u := by
  calc
    J u = B - p0 * u := J_of_le_a hua
    _ ≤ gClosed c0 u := gaussian_above_tangent_line u

theorem D_nonneg_at_a (_h_cond2 : c0 > 1) : gClosed c0 a ≥ J a := by
  calc
    gClosed c0 a ≥ B - p0 * a := gaussian_above_tangent_line a
    _ = J a := by symm; exact J_of_le_a le_rfl

lemma PhiBar_pos (t : Real) : 0 < PhiBar t := by
  unfold PhiBar
  have hpos_interval : 0 < ∫ x in t..(max t 1 + 1), phi x := by
    refine intervalIntegral.integral_pos (lt_of_le_of_lt (le_max_left t 1) (lt_add_one _)) ?_ ?_ ?_
    · unfold phi
      exact (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity))).continuousOn
    · intro x _; exact phi_nonneg x
    · refine ⟨(t + (max t 1 + 1)) / 2, ⟨?_, ?_⟩, ?_⟩
      · nlinarith [le_max_left t 1, le_of_lt (lt_add_one (max t 1))]
      · nlinarith [le_max_left t 1, le_of_lt (lt_add_one (max t 1))]
      · exact phi_pos _
  have hpos : 0 < ∫ x in Set.Ioc t (max t 1 + 1), phi x ∂volume := by
    simpa [intervalIntegral.integral_of_le (le_trans (le_max_left t 1) (le_of_lt (lt_add_one (max t 1))))] using hpos_interval
  have hsplit : ∫ x in Set.Ioi t, phi x ∂volume =
      ∫ x in Set.Ioc t (max t 1 + 1), phi x ∂volume + ∫ x in Set.Ioi (max t 1 + 1), phi x ∂volume := by
    have hdisj : Disjoint (Set.Ioc t (max t 1 + 1)) (Set.Ioi (max t 1 + 1)) :=
      Set.disjoint_iff_inter_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun x ⟨⟨_, hx⟩, hx'⟩ =>
        absurd hx (not_le_of_gt (Set.mem_Ioi.mp hx')))
    rw [← Set.Ioc_union_Ioi_eq_Ioi (le_trans (le_max_left t 1) (le_of_lt (lt_add_one (max t 1)))),
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (phi_integrable.integrableOn.mono_set (Set.subset_univ (Set.Ioc t (max t 1 + 1))))
        (phi_integrable.integrableOn.mono_set (Set.subset_univ (Set.Ioi (max t 1 + 1))))]
  rw [hsplit]
  exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (MeasureTheory.integral_nonneg fun x => phi_nonneg x))

/-- Numeric side condition kept as an explicit assumption. -/
lemma integral_Ioc_0_t0_eq_t0_for_s :
    ∫ t in Set.Ioc (0 : Real) t0, s t ∂volume = t0 := by
  have h_t0_eval : 2 * Real.exp (-(t0 ^ 2) / 2) = 1 := by
    unfold t0
    have hnonneg : 0 ≤ 2 * Real.log 2 := by positivity
    calc
      2 * Real.exp (-(Real.sqrt (2 * Real.log 2) ^ 2) / 2)
          = 2 * Real.exp (-(2 * Real.log 2) / 2) := by rw [Real.sq_sqrt hnonneg]
      _ = 2 * Real.exp (-Real.log 2) := by ring_nf
      _ = 2 * (Real.exp (Real.log 2))⁻¹ := by simp [Real.exp_neg]
      _ = 2 * ((2 : Real)⁻¹) := by rw [Real.exp_log (by norm_num : (0 : Real) < 2)]
      _ = 1 := by norm_num
  have h_s_eq_one : Set.EqOn s (fun _ : Real => 1) (Set.Ioc 0 t0) := by
    intro t ht
    have hsq_le : t ^ 2 ≤ t0 ^ 2 := by
      nlinarith [ht.1, ht.2, t0_pos]
    have hexp_ge : Real.exp (-(t0 ^ 2) / 2) ≤ Real.exp (-(t ^ 2) / 2) := by
      exact Real.exp_le_exp.mpr (by nlinarith [hsq_le])
    have hmul_ge : 2 * Real.exp (-(t0 ^ 2) / 2) ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
      exact mul_le_mul_of_nonneg_left hexp_ge (by norm_num : (0 : Real) ≤ 2)
    unfold s
    apply min_eq_left
    linarith [h_t0_eval, hmul_ge]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h_s_eq_one]
  simp [MeasureTheory.integral_const, smul_eq_mul, t0_pos.le]

lemma integral_Ioc_t0_t1_s_ge_half_len :
    (t1 - t0) / 2 ≤ ∫ t in Set.Ioc t0 t1, s t ∂volume := by
  have hs_cont : Continuous (fun t : Real => s t) := by
    unfold s
    exact Continuous.min continuous_const
      (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
  have hs_int : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioc t0 t1) := by
    exact hs_cont.integrableOn_Ioc
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : Real => (1 / 2 : Real)) (Set.Ioc t0 t1) := by
    exact MeasureTheory.integrableOn_const
      (measure_Ioc_lt_top (μ := (volume : Measure Real)) (a := t0) (b := t1)).ne
  have hpointwise : ∀ t ∈ Set.Ioc t0 t1, (1 / 2 : Real) ≤ s t := by
    intro t ht
    have ht_nonneg : 0 ≤ t := le_trans t0_pos.le ht.1.le
    have hsq_le : t ^ 2 ≤ t1 ^ 2 := by nlinarith [ht.2, ht_nonneg, t1_pos]
    have hexp_ge : Real.exp (-(t1 ^ 2) / 2) ≤ Real.exp (-(t ^ 2) / 2) := by
      exact Real.exp_le_exp.mpr (by nlinarith [hsq_le])
    have hmul_ge : 2 * Real.exp (-(t1 ^ 2) / 2) ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
      exact mul_le_mul_of_nonneg_left hexp_ge (by norm_num : (0 : Real) ≤ 2)
    unfold s
    apply le_min
    · norm_num
    · linarith [hmul_ge, two_exp_neg_t1_sq_div_two_eq_half]
  have hmono :
      ∫ t in Set.Ioc t0 t1, (1 / 2 : Real) ∂volume
        ≤ ∫ t in Set.Ioc t0 t1, s t ∂volume := by
    exact MeasureTheory.setIntegral_mono_on hconst_int hs_int measurableSet_Ioc hpointwise
  have hconst :
      ∫ t in Set.Ioc t0 t1, (1 / 2 : Real) ∂volume = (t1 - t0) / 2 := by
    calc
      ∫ t in Set.Ioc t0 t1, (1 / 2 : Real) ∂volume
          = (t1 - t0) * (1 / 2 : Real) := by
              simp [MeasureTheory.integral_const, smul_eq_mul, t0_lt_t1.le]
      _ = (t1 - t0) / 2 := by ring
  linarith [hmono, hconst]

lemma A_ge_t0_plus_half_t1_sub_t0 :
    t0 + (t1 - t0) / 2 ≤ A := by
  have hs_cont : Continuous (fun t : Real => s t) := by
    unfold s
    exact Continuous.min continuous_const
      (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
  have hs_ioc0 : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioc 0 t0) := by
    exact hs_cont.integrableOn_Ioc
  have hs_ioc1 : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioc t0 t1) := by
    exact hs_cont.integrableOn_Ioc
  have hs_iou0 : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioi t0) := by
    exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi t0_pos.le))
  have hs_iou1 : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioi t1) := by
    exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi t1_pos.le))
  have hA_split :
      A = (∫ t in Set.Ioc 0 t0, s t ∂volume) + (∫ t in Set.Ioi t0, s t ∂volume) := by
    unfold A
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc0 hs_iou0]
    rw [Set.Ioc_union_Ioi_eq_Ioi t0_pos.le]
  have htail_split :
      (∫ t in Set.Ioi t0, s t ∂volume) =
        (∫ t in Set.Ioc t0 t1, s t ∂volume) + (∫ t in Set.Ioi t1, s t ∂volume) := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc1 hs_iou1]
    rw [Set.Ioc_union_Ioi_eq_Ioi t0_lt_t1.le]
  have htail_nonneg : 0 ≤ ∫ t in Set.Ioi t1, s t ∂volume := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    unfold s
    exact le_min zero_le_one (mul_nonneg zero_le_two (Real.exp_nonneg _))
  have htail_ge : (t1 - t0) / 2 ≤ ∫ t in Set.Ioi t0, s t ∂volume := by
    rw [htail_split]
    linarith [integral_Ioc_t0_t1_s_ge_half_len, htail_nonneg]
  calc
    t0 + (t1 - t0) / 2
        = (∫ t in Set.Ioc 0 t0, s t ∂volume) + (t1 - t0) / 2 := by
            rw [integral_Ioc_0_t0_eq_t0_for_s]
    _ ≤ (∫ t in Set.Ioc 0 t0, s t ∂volume) + (∫ t in Set.Ioi t0, s t ∂volume) := by
          gcongr
    _ = A := by rw [hA_split]

lemma B_ge_sum_t0_t1_div_four : (t0 + t1) / 4 ≤ B := by
  have hA : t0 + (t1 - t0) / 2 ≤ A := A_ge_t0_plus_half_t1_sub_t0
  unfold B
  nlinarith [hA]

lemma t0_gt_117_div_100 : (117 : Real) / 100 < t0 := by
  unfold t0
  apply Real.lt_sqrt_of_sq_lt
  nlinarith [Real.log_two_gt_d9]

lemma t1_gt_166_div_100 : (166 : Real) / 100 < t1 := by
  unfold t1
  apply Real.lt_sqrt_of_sq_lt
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log (2 * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = 2 * Real.log 2 := by ring
  rw [hlog4]
  nlinarith [Real.log_two_gt_d9]

lemma phi_upper_uniform (t : Real) : phi t ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold phi
  have hexp_le : Real.exp (-(t ^ 2) / 2) ≤ 1 := by
    exact (Real.exp_le_one_iff).2 (by nlinarith [sq_nonneg t])
  calc
    (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)
        ≤ (1 / Real.sqrt (2 * Real.pi)) * 1 := by
          exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = 1 / Real.sqrt (2 * Real.pi) := by ring

lemma inv_sqrt_two_pi_lt_two_fifths : 1 / Real.sqrt (2 * Real.pi) < (2 : Real) / 5 := by
  have hsqrt : (5 : Real) / 2 < Real.sqrt (2 * Real.pi) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [Real.pi_gt_d2]
  simpa [div_eq_mul_inv] using
    (one_div_lt_one_div_of_lt (by positivity : (0 : Real) < (5 : Real) / 2) hsqrt)

lemma phi_le_two_fifths (t : Real) : phi t ≤ (2 : Real) / 5 := by
  exact (phi_upper_uniform t).trans (le_of_lt inv_sqrt_two_pi_lt_two_fifths)

lemma B_gt_283_div_400 : (283 : Real) / 400 < B := by
  have hsum : (283 : Real) / 400 < (t0 + t1) / 4 := by
    nlinarith [t0_gt_117_div_100, t1_gt_166_div_100]
  exact lt_of_lt_of_le hsum B_ge_sum_t0_t1_div_four

lemma c0_gt_seven_fourths : (7 : Real) / 4 < c0 := by
  have hB : (283 : Real) / 400 < B := B_gt_283_div_400
  have hphi_pos : 0 < phi z := phi_pos z
  have hphi_le : phi z ≤ (2 : Real) / 5 := phi_le_two_fifths z
  have hleft :
      ((283 : Real) / 400) / ((2 : Real) / 5) ≤ ((283 : Real) / 400) / phi z := by
    have hinv : 1 / ((2 : Real) / 5) ≤ 1 / phi z := one_div_le_one_div_of_le hphi_pos hphi_le
    have hmul : ((283 : Real) / 400) * (1 / ((2 : Real) / 5))
        ≤ ((283 : Real) / 400) * (1 / phi z) := by
      exact mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : Real) ≤ (283 : Real) / 400)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hright : ((283 : Real) / 400) / phi z < B / phi z := by
    have hmul : ((283 : Real) / 400) * (1 / phi z) < B * (1 / phi z) := by
      exact mul_lt_mul_of_pos_right hB (one_div_pos.mpr hphi_pos)
    simpa [div_eq_mul_inv] using hmul
  have hconst : ((283 : Real) / 400) / ((2 : Real) / 5) = (283 : Real) / 160 := by norm_num
  have hconst_gt : (7 : Real) / 4 < (283 : Real) / 160 := by norm_num
  have hmain : (7 : Real) / 4 < B / phi z := by
    calc
      (7 : Real) / 4 < (283 : Real) / 160 := hconst_gt
      _ = ((283 : Real) / 400) / ((2 : Real) / 5) := by symm; exact hconst
      _ ≤ ((283 : Real) / 400) / phi z := hleft
      _ < B / phi z := hright
  simpa [c0] using hmain

lemma a_gt_three_halves : (3 : Real) / 2 < a := by
  have h15 : (3 : Real) / 2 < (166 : Real) / 100 := by norm_num
  exact lt_trans h15 (lt_trans t1_gt_166_div_100 a_gt_t1)

theorem numerics_c0 : c0 > 1 ∧ a * (1 - 1 / c0^2) > 1 := by
  have hc0_gt : (7 : Real) / 4 < c0 := c0_gt_seven_fourths
  have hc0_gt_one : c0 > 1 := by linarith [hc0_gt]
  have hfac_gt : 1 - 1 / c0 ^ 2 > (33 : Real) / 49 := by
    have hc0_sq_gt : ((7 : Real) / 4) ^ 2 < c0 ^ 2 := by nlinarith [hc0_gt]
    have h_inv_lt : 1 / c0 ^ 2 < 1 / (((7 : Real) / 4) ^ 2) := by
      exact one_div_lt_one_div_of_lt (by positivity) hc0_sq_gt
    have h_inv_lt' : 1 / c0 ^ 2 < (16 : Real) / 49 := by
      norm_num [pow_two] at h_inv_lt ⊢
      exact h_inv_lt
    nlinarith [h_inv_lt']
  have ha_gt : (3 : Real) / 2 < a := a_gt_three_halves
  have hprod_gt : a * (1 - 1 / c0 ^ 2) > (99 : Real) / 98 := by
    nlinarith [ha_gt, hfac_gt]
  refine ⟨hc0_gt_one, ?_⟩
  nlinarith [hprod_gt]

/-- `G1` boundary for Gaussian-vs-envelope: tail limit of `J`. -/
theorem J_tendsto_zero : Filter.Tendsto J Filter.atTop (nhds (0 : Real)) := by
  let C : Real := ∫ t in Set.Ioi 0, s t ∂volume
  let F : Real → Real := fun x => C - ∫ t in (0 : Real)..x, s t
  have h_interval :
      Filter.Tendsto (fun x => ∫ t in (0 : Real)..x, s t ∂volume)
        Filter.atTop (nhds C) := by
    apply_rules [MeasureTheory.intervalIntegral_tendsto_integral_Ioi]
    · exact s_integrableOn_Ioi_zero
    · exact Filter.tendsto_id
  have hF_tend' :
      Filter.Tendsto (fun x => C - ∫ t in (0 : Real)..x, s t ∂volume)
        Filter.atTop (nhds (C - C)) := by
    exact tendsto_const_nhds.sub h_interval
  have hF_tend : Filter.Tendsto F Filter.atTop (nhds 0) := by
    simpa [F, C] using hF_tend'
  have htail_split :
      ∀ x : Real, 0 < x →
        (∫ t in Set.Ioi x, s t ∂volume) = F x := by
    intro x hx
    unfold F
    rw [eq_sub_iff_add_eq', intervalIntegral.integral_of_le hx.le]
    have hs_ioc : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioc 0 x) :=
      (s_integrableOn_Ioi_zero.mono_set Set.Ioc_subset_Ioi_self)
    have hs_iou : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioi x) :=
      (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi hx.le))
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc hs_iou]
    rw [Set.Ioc_union_Ioi_eq_Ioi hx.le]
  have htail_tend :
      Filter.Tendsto (fun x => ∫ t in Set.Ioi x, s t ∂volume) Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hF_tend
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    exact (htail_split x hx).symm
  refine Filter.Tendsto.congr' ?_ htail_tend
  filter_upwards [Filter.eventually_ge_atTop a] with x hx
  simpa using (J_eq_integral_Ioi_of_ge_a x hx).symm

/-- Canonical Mills-ratio upper bound: `phi / PhiBar ≤ x + 1/x` for `x>0`. -/
lemma integrableOn_phi_div_sq (x : Real) (hx : 0 < x) :
    MeasureTheory.IntegrableOn (fun t : Real => phi t / t ^ 2) (Set.Ioi x) := by
  have hbound : MeasureTheory.IntegrableOn (fun t : Real => (1 / x ^ 2) * phi t) (Set.Ioi x) := by
    exact (phi_integrable.const_mul (1 / x ^ 2)).integrableOn.mono_set (Set.subset_univ _)
  refine hbound.mono' ?_ ?_
  ·
    have hmeas : Measurable (fun t : Real => phi t / t ^ 2) := by
      unfold phi
      exact
        (Measurable.div
          (Measurable.mul measurable_const
            (Real.continuous_exp.measurable.comp
              (Measurable.div_const (Measurable.neg (measurable_id.pow_const 2)) 2)))
          (measurable_id.pow_const 2))
    exact hmeas.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht using by
      have hxt : x ≤ t := le_of_lt ht
      have hsq_le : x ^ 2 ≤ t ^ 2 := by nlinarith [hx, hxt]
      have hdiv_le : 1 / t ^ 2 ≤ 1 / x ^ 2 := one_div_le_one_div_of_le (by positivity) hsq_le
      have hphi_nonneg : 0 ≤ phi t := phi_nonneg t
      have hmul_le : phi t / t ^ 2 ≤ (1 / x ^ 2) * phi t := by
        have hmul_le' : (1 / t ^ 2) * phi t ≤ (1 / x ^ 2) * phi t :=
          mul_le_mul_of_nonneg_right hdiv_le hphi_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul_le'
      have hnonneg : 0 ≤ phi t / t ^ 2 := div_nonneg hphi_nonneg (sq_nonneg t)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hmul_le

lemma phi_tail_ibp_Ioi (x : Real) (hx : 0 < x) :
    PhiBar x = phi x / x - ∫ t in Set.Ioi x, phi t / t ^ 2 ∂volume := by
  let u : Real → Real := fun t => -(1 / t)
  let u' : Real → Real := fun t => 1 / t ^ 2
  let v : Real → Real := phi
  let v' : Real → Real := fun t => -t * phi t
  have hu : ∀ t ∈ Set.Ioi x, HasDerivAt u (u' t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hx ht)
    unfold u u'
    have hInv : HasDerivAt (fun y : Real => y⁻¹) (-(t⁻¹) ^ 2) t := by
      simpa using (hasDerivAt_inv ht0)
    have hInvNeg : HasDerivAt (fun y : Real => -(y⁻¹)) ((t⁻¹) ^ 2) t := by
      simpa using hInv.neg
    simpa [one_div, pow_two] using hInvNeg
  have hv : ∀ t ∈ Set.Ioi x, HasDerivAt v (v' t) t := by
    intro t _ht
    unfold v v'
    have hdiff : DifferentiableAt Real phi t := by
      unfold phi
      fun_prop
    have hphi : HasDerivAt phi (deriv phi t) t := (hasDerivAt_deriv_iff).2 hdiff
    simpa [phi_deriv t] using hphi
  have huv' : MeasureTheory.IntegrableOn (u * v') (Set.Ioi x) := by
    have hphi_iou : MeasureTheory.IntegrableOn phi (Set.Ioi x) :=
      phi_integrable.integrableOn.mono_set (Set.subset_univ _)
    refine hphi_iou.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hx ht)
    simp [u, v', Pi.mul_apply, div_eq_mul_inv, ht0, mul_comm, mul_left_comm]
  have hu'v : MeasureTheory.IntegrableOn (u' * v) (Set.Ioi x) := by
    have hdiv : MeasureTheory.IntegrableOn (fun t => phi t / t ^ 2) (Set.Ioi x) :=
      integrableOn_phi_div_sq x hx
    refine hdiv.congr_fun ?_ measurableSet_Ioi
    intro t _ht
    simp [u', v, Pi.mul_apply, div_eq_mul_inv, mul_comm]
  have h_zero : Filter.Tendsto (u * v) (𝓝[>] x) (𝓝 (-(phi x / x))) := by
    have hcont : ContinuousAt (fun t => (u * v) t) x := by
      have hu_cont : ContinuousAt (fun t : Real => -(1 / t)) x := by
        exact (continuousAt_const.div continuousAt_id hx.ne').neg
      have hv_cont : ContinuousAt phi x := by
        simpa [phi] using
          (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity))).continuousAt
      have hmul : ContinuousAt (fun t : Real => (-(1 / t)) * phi t) x := hu_cont.mul hv_cont
      simpa [Pi.mul_apply, u, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have ht : Filter.Tendsto (u * v) (nhds x) (nhds ((u * v) x)) := hcont.tendsto
    have ht' : Filter.Tendsto (u * v) (𝓝[>] x) (nhds ((u * v) x)) := ht.mono_left inf_le_left
    simpa [u, v, Pi.mul_apply, div_eq_mul_inv, mul_comm] using ht'
  have h_infty_div : Filter.Tendsto (fun t : Real => phi t / t) Filter.atTop (nhds (0 : Real)) := by
    have hpow : Filter.Tendsto (fun t : Real => t ^ 2) Filter.atTop Filter.atTop := by
      exact (tendsto_pow_atTop (α := Real) (n := 2) (by norm_num : (2 : Nat) ≠ 0))
    have hnegpow : Filter.Tendsto (fun t : Real => -(t ^ 2)) Filter.atTop Filter.atBot := by
      exact tendsto_neg_atTop_atBot.comp hpow
    have harg : Filter.Tendsto (fun t : Real => -(t ^ 2) / 2) Filter.atTop Filter.atBot := by
      exact Filter.Tendsto.atBot_div_const (by positivity) hnegpow
    have hexp : Filter.Tendsto (fun t : Real => Real.exp (-(t ^ 2) / 2)) Filter.atTop (nhds (0 : Real)) := by
      exact Real.tendsto_exp_atBot.comp harg
    have hnum :
        Filter.Tendsto
          (fun t : Real => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2))
          Filter.atTop (nhds (0 : Real)) := by
            simpa using tendsto_const_nhds.mul hexp
    unfold phi
    simpa using Filter.Tendsto.div_atTop hnum Filter.tendsto_id
  have h_infty : Filter.Tendsto (u * v) Filter.atTop (nhds (0 : Real)) := by
    have hfun : (u * v) = (fun t : Real => -(phi t / t)) := by
      funext t
      simp [u, v, Pi.mul_apply, div_eq_mul_inv, mul_comm]
    have h_infty_neg : Filter.Tendsto (fun t : Real => -(phi t / t)) Filter.atTop (nhds (0 : Real)) := by
      simpa using h_infty_div.neg
    exact hfun ▸ h_infty_neg
  have hibp :
      ∫ t in Set.Ioi x, u t * v' t ∂volume =
        (0 : Real) - (-(phi x / x)) - ∫ t in Set.Ioi x, u' t * v t ∂volume := by
    simpa [u, u', v, v'] using
      (MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
        (a := x) (u := u) (u' := u') (v := v) (v' := v') hu hv huv' hu'v h_zero h_infty)
  calc
    PhiBar x = ∫ t in Set.Ioi x, phi t ∂volume := by rfl
    _ = ∫ t in Set.Ioi x, u t * v' t ∂volume := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_trans hx ht)
      unfold u v'
      field_simp [ht0]
    _ = (0 : Real) - (-(phi x / x)) - ∫ t in Set.Ioi x, u' t * v t ∂volume := hibp
    _ = phi x / x - ∫ t in Set.Ioi x, u' t * v t ∂volume := by simp
    _ = phi x / x - ∫ t in Set.Ioi x, phi t / t ^ 2 ∂volume := by
      congr 1
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      simp [u', v, div_eq_mul_inv, mul_comm]

theorem mills_bounds (x : Real) (hx : 0 < x) :
    (x / (1 + x ^ 2)) * phi x ≤ PhiBar x ∧ PhiBar x ≤ (1 / x) * phi x := by
  have h_ibp : PhiBar x = phi x / x - ∫ t in Set.Ioi x, phi t / t ^ 2 ∂volume :=
    phi_tail_ibp_Ioi x hx
  have h_int_nonneg : 0 ≤ ∫ t in Set.Ioi x, phi t / t ^ 2 ∂volume := by
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t _ => div_nonneg (phi_nonneg t) (sq_nonneg t))
  have h_upper_div : PhiBar x ≤ phi x / x := by
    linarith [h_ibp, h_int_nonneg]
  have h_upper : PhiBar x ≤ (1 / x) * phi x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_upper_div
  have hIntF : MeasureTheory.IntegrableOn (fun t : Real => phi t / t ^ 2) (Set.Ioi x) :=
    integrableOn_phi_div_sq x hx
  have hIntG : MeasureTheory.IntegrableOn (fun t : Real => (1 / x ^ 2) * phi t) (Set.Ioi x) := by
    exact (phi_integrable.const_mul (1 / x ^ 2)).integrableOn.mono_set (Set.subset_univ _)
  have h_int_bound_raw :
      ∫ t in Set.Ioi x, phi t / t ^ 2 ∂volume ≤ ∫ t in Set.Ioi x, (1 / x ^ 2) * phi t ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hIntF hIntG measurableSet_Ioi ?_
    intro t ht
    have hxt : x ≤ t := le_of_lt ht
    have hsq_le : x ^ 2 ≤ t ^ 2 := by nlinarith [hx, hxt]
    have hdiv_le : 1 / t ^ 2 ≤ 1 / x ^ 2 := one_div_le_one_div_of_le (by positivity) hsq_le
    have hmul_le' : (1 / t ^ 2) * phi t ≤ (1 / x ^ 2) * phi t :=
      mul_le_mul_of_nonneg_right hdiv_le (phi_nonneg t)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul_le'
  have h_int_bound :
      ∫ t in Set.Ioi x, phi t / t ^ 2 ∂volume ≤ (1 / x ^ 2) * PhiBar x := by
    have hEq :
        (∫ t in Set.Ioi x, (1 / x ^ 2) * phi t ∂volume) = (1 / x ^ 2) * PhiBar x := by
      rw [MeasureTheory.integral_const_mul]
      simp [PhiBar]
    linarith [h_int_bound_raw, hEq]
  have h_lower_aux : phi x / x - (1 / x ^ 2) * PhiBar x ≤ PhiBar x := by
    linarith [h_ibp, h_int_bound]
  have h_lower_mul : x * phi x ≤ (1 + x ^ 2) * PhiBar x := by
    have hx2_pos : 0 < x ^ 2 := sq_pos_of_pos hx
    have hmul :
        x ^ 2 * (phi x / x - (1 / x ^ 2) * PhiBar x) ≤ x ^ 2 * PhiBar x :=
      mul_le_mul_of_nonneg_left h_lower_aux hx2_pos.le
    have hmul' : x * phi x - PhiBar x ≤ x ^ 2 * PhiBar x := by
      have hcalc : x ^ 2 * (phi x / x - (1 / x ^ 2) * PhiBar x) = x * phi x - PhiBar x := by
        field_simp [hx.ne']
      rw [hcalc] at hmul
      exact hmul
    nlinarith [hmul']
  have h_lower : (x / (1 + x ^ 2)) * phi x ≤ PhiBar x := by
    have h_lower' : (x * phi x) / (1 + x ^ 2) ≤ PhiBar x := by
      exact (div_le_iff₀ (show 0 < 1 + x ^ 2 by positivity)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_lower_mul)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_lower'
  exact ⟨h_lower, h_upper⟩

theorem mills_ratio_bound :
    ∀ x : Real, 0 < x → phi x / PhiBar x ≤ x + 1 / x := by
  intro x hx
  have h_lower : (x / (1 + x ^ 2)) * phi x ≤ PhiBar x := (mills_bounds x hx).1
  have hphi_le : phi x ≤ ((1 + x ^ 2) / x) * PhiBar x := by
    have hmul :
        ((1 + x ^ 2) / x) * ((x / (1 + x ^ 2)) * phi x)
          ≤ ((1 + x ^ 2) / x) * PhiBar x := by
      exact mul_le_mul_of_nonneg_left h_lower (by positivity)
    have hleft :
        ((1 + x ^ 2) / x) * ((x / (1 + x ^ 2)) * phi x) = phi x := by
      field_simp [hx.ne']
    rw [hleft] at hmul
    exact hmul
  have h_ratio : phi x / PhiBar x ≤ (1 + x ^ 2) / x := by
    exact (div_le_iff₀ (PhiBar_pos x)).2 hphi_le
  have hsum : (1 + x ^ 2) / x = x + 1 / x := by
    field_simp [hx.ne']
    ring
  simpa [hsum] using h_ratio

/-- Ratio monotonicity used in the Gaussian-vs-envelope comparison (`Rmono` in LaTeX). -/
theorem R_strict_mono_on
    (h_cond1 : a * (1 - 1 / c0 ^ 2) > 1) (h_cond2 : c0 > 1) :
    StrictMonoOn (fun u => R c0 u) (Set.Ici a) := by
  let f : Real → Real := fun u => PhiBar (u / c0) / (2 * Real.exp (-u ^ 2 / 2))
  have hf_eq : (fun u => R c0 u) = f := by
    funext u
    simp [f, R]
  have hcont : ContinuousOn f (Set.Ici a) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (PhiBar_continuous.comp (continuous_id.div_const c0)).continuousOn
    · exact (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity))).continuousOn
    · intro u hu
      positivity
  have hderiv_pos : ∀ u ∈ interior (Set.Ici a), 0 < deriv f u := by
    intro u hu_int
    have hu : a < u := by simpa using hu_int
    have hu_pos : 0 < u := lt_trans t0_pos (lt_trans a_spec.1 hu)
    have hc0_pos : 0 < c0 := lt_trans zero_lt_one h_cond2
    have hPhi_diff : DifferentiableAt Real PhiBar (u / c0) := by
      exact differentiableAt_of_deriv_ne_zero (by
        rw [PhiBar_deriv]
        exact neg_ne_zero.mpr (phi_pos _).ne')
    have hPhi_at : HasDerivAt PhiBar (-phi (u / c0)) (u / c0) := by
      have hPhi0 : HasDerivAt PhiBar (deriv PhiBar (u / c0)) (u / c0) := (hasDerivAt_deriv_iff).2 hPhi_diff
      simpa [PhiBar_deriv (u / c0)] using hPhi0
    have hnum_at : HasDerivAt (fun t => PhiBar (t / c0)) ((-phi (u / c0)) * (1 / c0)) u := by
      have hdiv : HasDerivAt (fun t => t / c0) (1 / c0) u := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id u).mul_const (1 / c0)
      have hcomp : HasDerivAt (PhiBar ∘ fun t => t / c0) ((-phi (u / c0)) * (1 / c0)) u :=
        HasDerivAt.comp u hPhi_at hdiv
      simpa [Function.comp] using hcomp
    have hden_at : HasDerivAt (fun t => 2 * Real.exp (-t ^ 2 / 2))
        (-(u * (2 * Real.exp (-u ^ 2 / 2)))) u := by
      have harg : HasDerivAt (fun t => -(t ^ 2) / 2) (-u) u := by
        convert (HasDerivAt.div_const (HasDerivAt.neg (hasDerivAt_pow 2 u)) (2 : Real)) using 1
        ring
      have hexp : HasDerivAt (fun t => Real.exp (-(t ^ 2) / 2))
          (Real.exp (-u ^ 2 / 2) * (-u)) u := (HasDerivAt.exp harg)
      convert hexp.const_mul 2 using 1
      ring
    have hden_ne : (2 * Real.exp (-u ^ 2 / 2)) ≠ 0 := by positivity
    have hderiv_formula :
        deriv f u =
          (u * PhiBar (u / c0) - (1 / c0) * phi (u / c0)) / (2 * Real.exp (-u ^ 2 / 2)) := by
      have hquot :
          HasDerivAt f
            ((((-phi (u / c0)) * (1 / c0)) * (2 * Real.exp (-u ^ 2 / 2)) -
              PhiBar (u / c0) * (-(u * (2 * Real.exp (-u ^ 2 / 2))))) /
              (2 * Real.exp (-u ^ 2 / 2)) ^ 2) u := by
        simpa [f] using hnum_at.div hden_at hden_ne
      have hderiv_raw : deriv f u =
          ((((-phi (u / c0)) * (1 / c0)) * (2 * Real.exp (-u ^ 2 / 2)) -
            PhiBar (u / c0) * (-(u * (2 * Real.exp (-u ^ 2 / 2))))) /
            (2 * Real.exp (-u ^ 2 / 2)) ^ 2) := hquot.deriv
      rw [hderiv_raw]
      field_simp [hden_ne]
      ring
    have h_mills : phi (u / c0) / PhiBar (u / c0) ≤ u / c0 + c0 / u := by
      have hu_div_pos : 0 < u / c0 := div_pos hu_pos hc0_pos
      simpa using mills_ratio_bound (u / c0) hu_div_pos
    have hPhi_pos : 0 < PhiBar (u / c0) := PhiBar_pos (u / c0)
    have h_phi_bound : (1 / c0) * phi (u / c0) ≤ (u / c0 ^ 2 + 1 / u) * PhiBar (u / c0) := by
      have h1 : phi (u / c0) ≤ (u / c0 + c0 / u) * PhiBar (u / c0) := by
        exact (div_le_iff₀ hPhi_pos).mp h_mills
      have h2 : (1 / c0) * phi (u / c0) ≤ (1 / c0) * ((u / c0 + c0 / u) * PhiBar (u / c0)) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      calc
        (1 / c0) * phi (u / c0) ≤ (1 / c0) * ((u / c0 + c0 / u) * PhiBar (u / c0)) := h2
        _ = (u / c0 ^ 2 + 1 / u) * PhiBar (u / c0) := by
              field_simp [hc0_pos.ne', (ne_of_gt hu_pos)]
    have hfac_pos : 0 < (1 - 1 / c0 ^ 2) := by
      have hc0sq_gt : 1 < c0 ^ 2 := by nlinarith [h_cond2]
      have hdiv_lt : 1 / c0 ^ 2 < 1 := by
        exact (one_div_lt (show 0 < c0 ^ 2 by positivity) zero_lt_one).2 (by simpa using hc0sq_gt)
      linarith
    have hu_mul_gt_one : u * (1 - 1 / c0 ^ 2) > 1 := by
      have hmul_gt : a * (1 - 1 / c0 ^ 2) < u * (1 - 1 / c0 ^ 2) :=
        mul_lt_mul_of_pos_right hu hfac_pos
      linarith
    have hfac_le_one : (1 - 1 / c0 ^ 2) ≤ 1 := by
      have hdiv_nonneg : 0 ≤ 1 / c0 ^ 2 := by positivity
      linarith
    have hu_gt_one : 1 < u := by
      have hmul_le : u * (1 - 1 / c0 ^ 2) ≤ u := by
        nlinarith [hu_pos, hfac_le_one]
      linarith
    have hgap : 0 < u - (u / c0 ^ 2 + 1 / u) := by
      have hu_ne : u ≠ 0 := ne_of_gt hu_pos
      have hprod_pos : 0 < u * (u - (u / c0 ^ 2 + 1 / u)) := by
        have hrewrite : u * (u - (u / c0 ^ 2 + 1 / u)) = u ^ 2 * (1 - 1 / c0 ^ 2) - 1 := by
          field_simp [hu_ne]
          ring
        rw [hrewrite]
        have hsq_gt : 1 < u ^ 2 * (1 - 1 / c0 ^ 2) := by
          nlinarith [hu_mul_gt_one, hu_gt_one]
        linarith
      rcases (mul_pos_iff.mp hprod_pos) with hcase | hcase
      · exact hcase.2
      · linarith [hu_pos, hcase.1]
    have hnum_lb :
        (u - (u / c0 ^ 2 + 1 / u)) * PhiBar (u / c0) ≤
          u * PhiBar (u / c0) - (1 / c0) * phi (u / c0) := by
      nlinarith [h_phi_bound]
    have hnum_pos :
        0 < u * PhiBar (u / c0) - (1 / c0) * phi (u / c0) := by
      exact lt_of_lt_of_le (mul_pos hgap hPhi_pos) hnum_lb
    have hden_pos : 0 < 2 * Real.exp (-u ^ 2 / 2) := by positivity
    have hfinal : 0 < (u * PhiBar (u / c0) - (1 / c0) * phi (u / c0)) / (2 * Real.exp (-u ^ 2 / 2)) :=
      div_pos hnum_pos hden_pos
    simpa [hderiv_formula, one_div] using hfinal
  have hmono_f : StrictMonoOn f (Set.Ici a) :=
    strictMonoOn_of_deriv_pos (hD := convex_Ici a) hcont hderiv_pos
  simpa [hf_eq] using hmono_f

theorem J_deriv_ge_a (u : Real) (hu : a < u) : deriv J u = -s u := by
  let C : Real := ∫ t in Set.Ioi 0, s t ∂volume
  let F : Real → Real := fun x => C - ∫ t in (0 : Real)..x, s t
  have hs_cont : Continuous s := by
    unfold s
    exact Continuous.min continuous_const
      (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
  have hF_deriv : deriv F u = -s u := by
    have hInt_deriv : deriv (fun x => ∫ t in (0 : Real)..x, s t ∂volume) u = s u := by
      exact (hs_cont.integral_hasStrictDerivAt (0 : Real) u).hasDerivAt.deriv
    unfold F
    rw [deriv_const_sub, hInt_deriv]
  have htail_split :
      ∀ x : Real, 0 < x →
        (∫ t in Set.Ioi x, s t ∂volume) = F x := by
    intro x hx
    unfold F
    rw [eq_sub_iff_add_eq', intervalIntegral.integral_of_le hx.le]
    have hs_ioc : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioc 0 x) :=
      (s_integrableOn_Ioi_zero.mono_set Set.Ioc_subset_Ioi_self)
    have hs_iou : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioi x) :=
      (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi hx.le))
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc hs_iou]
    rw [Set.Ioc_union_Ioi_eq_Ioi hx.le]
  have hJF_event :
      J =ᶠ[nhds u] F := by
    refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds hu) ?_
    intro x hx
    have hx0 : 0 < x := lt_trans t0_pos (lt_trans a_spec.1 hx)
    calc
      J x = ∫ t in Set.Ioi x, s t ∂volume := J_eq_integral_Ioi_of_ge_a x hx.le
      _ = F x := htail_split x hx0
  have h_deriv_eq : deriv J u = deriv F u := Filter.EventuallyEq.deriv_eq hJF_event
  rw [h_deriv_eq, hF_deriv]

theorem D_deriv_ge_a (h_cond2 : c0 > 1) (u : Real) (hu : a < u) :
    deriv (fun u => gClosed c0 u - J u) u = 2 * Real.exp (-u ^ 2 / 2) * (1 - R c0 u) := by
  have hc0 : 0 < c0 := lt_trans zero_lt_one h_cond2
  have hs_pos : 0 < s u := by
    unfold s
    exact lt_min zero_lt_one (mul_pos zero_lt_two (Real.exp_pos _))
  have hg_deriv : deriv (fun t => gClosed c0 t) u = -PhiBar (u / c0) := by
    simpa using congrArg (fun f => f u) (gClosed_deriv c0 hc0)
  have hJ_deriv : deriv J u = -s u := J_deriv_ge_a u hu
  have hg_diff : DifferentiableAt Real (fun t => gClosed c0 t) u := by
    exact differentiableAt_of_deriv_ne_zero (by
      rw [hg_deriv]
      exact neg_ne_zero.mpr (PhiBar_pos (u / c0)).ne')
  have hJ_diff : DifferentiableAt Real J u := by
    exact differentiableAt_of_deriv_ne_zero (by
      rw [hJ_deriv]
      exact neg_ne_zero.mpr hs_pos.ne')
  have hsub :
      deriv (fun t => gClosed c0 t - J t) u =
        deriv (fun t => gClosed c0 t) u - deriv J u := by
    exact HasDerivAt.deriv ((hasDerivAt_deriv_iff.mpr hg_diff).sub (hasDerivAt_deriv_iff.mpr hJ_diff))
  rw [hsub, hg_deriv, hJ_deriv]
  rw [s_eq_gauss_tail_of_gt_t0 (lt_trans a_spec.1 hu)]
  rw [R]
  field_simp [show 2 * Real.exp (-u ^ 2 / 2) ≠ 0 by positivity]
  ring

theorem g_c0_tendsto_zero (h_cond2 : c0 > 1) :
    Filter.Tendsto (fun u => gClosed c0 u) Filter.atTop (nhds 0) := by
  have hc0 : 0 < c0 := lt_trans zero_lt_one h_cond2
  have hIntAbsExp : MeasureTheory.Integrable (fun x : Real => |x| * Real.exp (-(x ^ 2) / 2)) := by
    have hIntSigned : MeasureTheory.Integrable (fun x : Real => x * Real.exp (-(x ^ 2) / 2)) := by
      simpa [pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : Real)) (by norm_num) (s := (1 : Real)) (by norm_num))
    convert hIntSigned.norm using 2 with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hIntAbsPhi : MeasureTheory.Integrable (fun x : Real => |x| * phi x) := by
    unfold phi
    convert hIntAbsExp.const_mul (1 / Real.sqrt (2 * Real.pi)) using 2 with x
    ring
  have hIntBound : MeasureTheory.Integrable (fun x : Real => |c0 * x| * phi x) := by
    convert hIntAbsPhi.const_mul |c0| using 2 with x
    rw [abs_mul]
    ring
  have h_int_tend :
      Filter.Tendsto (fun u => ∫ x, hinge u (c0 * x) * phi x ∂MeasureTheory.volume)
        Filter.atTop (nhds (0 : Real)) := by
    have h0 :
        Filter.Tendsto (fun u => ∫ x, hinge u (c0 * x) * phi x ∂MeasureTheory.volume)
          Filter.atTop
          (nhds (∫ x : Real, (0 : Real) ∂MeasureTheory.volume)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := MeasureTheory.volume)
        (l := Filter.atTop)
        (F := fun u x => hinge u (c0 * x) * phi x)
        (f := fun _ => 0)
        (bound := fun x => |c0 * x| * phi x)
        ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun u =>
          (Measurable.max ((measurable_id.const_mul c0).sub_const u) measurable_const).mul
            (by
              unfold phi
              exact Measurable.mul measurable_const
                (Real.continuous_exp.measurable.comp
                  (Measurable.div_const (Measurable.neg (measurable_id.pow_const 2)) 2)))
            |>.aestronglyMeasurable
      · filter_upwards [Filter.eventually_gt_atTop 0] with u hu using
          Filter.Eventually.of_forall fun x => by
            have hphi_nonneg : 0 ≤ phi x := phi_nonneg x
            have hhinge_nonneg : 0 ≤ hinge u (c0 * x) := hinge_nonneg u (c0 * x)
            have hhinge_le : hinge u (c0 * x) ≤ |c0 * x| := by
              unfold hinge posPart
              refine max_le ?_ (abs_nonneg _)
              have hcx : c0 * x ≤ |c0 * x| := le_abs_self (c0 * x)
              linarith [hcx, hu]
            have hmul : hinge u (c0 * x) * phi x ≤ |c0 * x| * phi x :=
              mul_le_mul_of_nonneg_right hhinge_le hphi_nonneg
            calc
              ‖hinge u (c0 * x) * phi x‖
                  = |hinge u (c0 * x)| * |phi x| := by
                      simp [Real.norm_eq_abs]
              _ = hinge u (c0 * x) * phi x := by
                    rw [abs_of_nonneg hhinge_nonneg, abs_of_nonneg hphi_nonneg]
              _ ≤ |c0 * x| * phi x := hmul
      · exact hIntBound
      · exact Filter.Eventually.of_forall fun x => by
          have hhinge_tend : Filter.Tendsto (fun u => hinge u (c0 * x)) Filter.atTop (nhds 0) := by
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [Filter.eventually_gt_atTop (c0 * x)] with u hu
            unfold hinge posPart
            simp [max_eq_right (by linarith : c0 * x - u ≤ 0)]
          have hmul_tend :
              Filter.Tendsto (fun u => hinge u (c0 * x) * phi x) Filter.atTop (nhds (0 * phi x)) :=
            hhinge_tend.mul tendsto_const_nhds
          simpa using hmul_tend
    simpa using h0
  have h_eq :
      (fun u => gClosed c0 u) = (fun u => ∫ x, hinge u (c0 * x) * phi x ∂MeasureTheory.volume) := by
    funext u
    simpa [gClosed] using (gaussian_call_closed_form c0 u hc0).symm
  simpa [h_eq] using h_int_tend

/-- Monotone-ratio principle used in the Gaussian-vs-envelope comparison. -/
theorem monotone_ratio_principle
    {a : Real} {D κ R : Real → Real}
    (hcont : ContinuousOn D (Set.Ici a))
    (hdiff : DifferentiableOn Real D (Set.Ioi a))
    (hderiv : ∀ u > a, deriv D u = κ u * (1 - R u))
    (hkappa_pos : ∀ u > a, 0 < κ u)
    (hR_mono : MonotoneOn R (Set.Ioi a))
    (h_start : 0 ≤ D a)
    (h_end : Filter.Tendsto D Filter.atTop (nhds 0)) :
    ∀ u ≥ a, 0 ≤ D u := by
  intro u hu
  by_cases hua : u = a
  · simpa [hua] using h_start
  · have hau : a < u := lt_of_le_of_ne hu (by intro h; exact hua h.symm)
    by_contra hu_nonneg
    have hu_neg : D u < 0 := lt_of_not_ge hu_nonneg
    have hDa_gt : D a > D u := by linarith [h_start, hu_neg]
    have h_event_D : ∀ᶠ x in Filter.atTop, D x > D u := h_end.eventually (Ioi_mem_nhds hu_neg)
    have h_event_u : ∀ᶠ x in Filter.atTop, u < x := Filter.eventually_gt_atTop u
    have h_event : ∀ᶠ x in Filter.atTop, D x > D u ∧ u < x := h_event_D.and h_event_u
    rcases (Filter.eventually_atTop.mp h_event) with ⟨v, hv⟩
    have hvDu : D v > D u := (hv v le_rfl).1
    have huv : u < v := (hv v le_rfl).2
    have hcont_au : ContinuousOn D (Set.Icc a u) := hcont.mono (by intro x hx; exact hx.1)
    have hdiff_au : DifferentiableOn Real D (Set.Ioo a u) := hdiff.mono (by intro x hx; exact hx.1)
    obtain ⟨xL, hxL_mem, hxL_deriv⟩ := exists_deriv_eq_slope D hau hcont_au hdiff_au
    have hslopeL_neg : (D u - D a) / (u - a) < 0 := by
      have hnum_neg : D u - D a < 0 := by linarith [hDa_gt]
      exact div_neg_of_neg_of_pos hnum_neg (sub_pos.mpr hau)
    have hderivL_neg : deriv D xL < 0 := by simpa [hxL_deriv] using hslopeL_neg
    have hxL_gt_a : a < xL := hxL_mem.1
    have hkL : 0 < κ xL := hkappa_pos xL hxL_gt_a
    have hEqL : deriv D xL = κ xL * (1 - R xL) := hderiv xL hxL_gt_a
    have hR_xL_gt_one : 1 < R xL := by
      have hmul : κ xL * (1 - R xL) < κ xL * 0 := by
        simpa [hEqL] using hderivL_neg
      have h1m_neg : 1 - R xL < 0 := (mul_lt_mul_iff_right₀ hkL).mp hmul
      linarith
    have hcont_uv : ContinuousOn D (Set.Icc u v) := hcont.mono (by intro x hx; exact le_trans hu hx.1)
    have hdiff_uv : DifferentiableOn Real D (Set.Ioo u v) := hdiff.mono (by intro x hx; exact lt_of_le_of_lt hu hx.1)
    obtain ⟨xR, hxR_mem, hxR_deriv⟩ := exists_deriv_eq_slope D huv hcont_uv hdiff_uv
    have hslopeR_pos : 0 < (D v - D u) / (v - u) := by
      have hnum_pos : 0 < D v - D u := by linarith [hvDu]
      exact div_pos hnum_pos (sub_pos.mpr huv)
    have hderivR_pos : 0 < deriv D xR := by simpa [hxR_deriv] using hslopeR_pos
    have hxR_gt_a : a < xR := lt_of_le_of_lt hu hxR_mem.1
    have hkR : 0 < κ xR := hkappa_pos xR hxR_gt_a
    have hEqR : deriv D xR = κ xR * (1 - R xR) := hderiv xR hxR_gt_a
    have hR_xR_lt_one : R xR < 1 := by
      have hmul : κ xR * 0 < κ xR * (1 - R xR) := by
        simpa [hEqR, zero_mul] using hderivR_pos
      have h1m_pos : 0 < 1 - R xR := (mul_lt_mul_iff_right₀ hkR).mp hmul
      linarith
    have hxL_le_xR : xL ≤ xR := le_of_lt (lt_trans hxL_mem.2 hxR_mem.1)
    have hR_mono_lr : R xL ≤ R xR :=
      hR_mono (Set.mem_Ioi.mpr hxL_gt_a) (Set.mem_Ioi.mpr hxR_gt_a) hxL_le_xR
    linarith [hR_mono_lr, hR_xL_gt_one, hR_xR_lt_one]

theorem gaussian_dominates_J :
    ∀ u : Real, 0 <= u → J u <= gClosed c0 u := by
  have ⟨hc0_gt_one, hnum⟩ := numerics_c0
  intro u hu
  by_cases hua : u ≤ a
  · exact lemma_gauss_ge_J_case1 hnum hc0_gt_one u hu hua
  · have hau : a < u := lt_of_not_ge hua
    let D : Real → Real := fun x => gClosed c0 x - J x
    have hD_start : 0 ≤ D a := by
      unfold D
      exact sub_nonneg.mpr (by simpa [ge_iff_le] using D_nonneg_at_a hc0_gt_one)
    have hD_end : Filter.Tendsto D Filter.atTop (nhds 0) := by
      unfold D
      simpa using (g_c0_tendsto_zero hc0_gt_one).sub J_tendsto_zero
    have hD_deriv : ∀ x > a, deriv D x = (2 * Real.exp (-x ^ 2 / 2)) * (1 - R c0 x) := by
      intro x hx
      unfold D
      simpa using (D_deriv_ge_a hc0_gt_one x hx)
    have hkappa_pos : ∀ x > a, 0 < (2 * Real.exp (-x ^ 2 / 2)) := by
      intro x hx
      positivity
    have hR_strict : StrictMonoOn (fun x => R c0 x) (Set.Ici a) :=
      R_strict_mono_on hnum hc0_gt_one
    have hR_mono : MonotoneOn (fun x => R c0 x) (Set.Ioi a) := by
      intro x hx y hy hxy
      exact (StrictMonoOn.monotoneOn hR_strict)
        (Set.mem_Ici.mpr (le_of_lt hx))
        (Set.mem_Ici.mpr (le_of_lt hy))
        hxy
    have hs_cont : Continuous s := by
      unfold s
      exact Continuous.min continuous_const
        (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
    have htail_split :
        ∀ x : Real, 0 < x →
          (∫ t in Set.Ioi x, s t ∂volume) =
            (∫ t in Set.Ioi 0, s t ∂volume) - ∫ t in (0 : Real)..x, s t := by
      intro x hx
      rw [eq_sub_iff_add_eq', intervalIntegral.integral_of_le hx.le]
      have hs_ioc : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioc 0 x) :=
        (s_integrableOn_Ioi_zero.mono_set Set.Ioc_subset_Ioi_self)
      have hs_iou : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioi x) :=
        (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi hx.le))
      rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc hs_iou]
      rw [Set.Ioc_union_Ioi_eq_Ioi hx.le]
    let F : Real → Real := fun x => (∫ t in Set.Ioi 0, s t ∂volume) - ∫ t in (0 : Real)..x, s t
    have hJ_eq_on_Ici : EqOn J F (Set.Ici a) := by
      intro x hx
      have hx0 : 0 < x := lt_trans t0_pos (lt_of_lt_of_le a_spec.1 hx)
      calc
        J x = ∫ t in Set.Ioi x, s t ∂volume := J_eq_integral_Ioi_of_ge_a x hx
        _ = F x := htail_split x hx0
    have hF_diff : Differentiable Real F := by
      intro x
      exact ((hs_cont.integral_hasStrictDerivAt (0 : Real) x).hasDerivAt.differentiableAt).const_sub
        (∫ t in Set.Ioi 0, s t ∂volume)
    have hJ_cont : ContinuousOn J (Set.Ici a) := by
      exact (hF_diff.continuous.continuousOn : ContinuousOn F (Set.Ici a)).congr hJ_eq_on_Ici
    have hJ_diff : DifferentiableOn Real J (Set.Ioi a) := by
      exact (hF_diff.differentiableOn : DifferentiableOn Real F (Set.Ioi a)).congr
        (by
          intro x hx
          exact hJ_eq_on_Ici (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hx))))
    have hg_diff : Differentiable Real (fun x => gClosed c0 x) := by
      intro x
      have hderivx : deriv (fun t => gClosed c0 t) x = -PhiBar (x / c0) := by
        simpa using congrArg (fun f => f x) (gClosed_deriv c0 (lt_trans zero_lt_one hc0_gt_one))
      have hderiv_ne : deriv (fun t => gClosed c0 t) x ≠ 0 := by
        rw [hderivx]
        exact neg_ne_zero.mpr (PhiBar_pos (x / c0)).ne'
      exact differentiableAt_of_deriv_ne_zero hderiv_ne
    have hD_cont : ContinuousOn D (Set.Ici a) := by
      unfold D
      exact (hg_diff.continuous.continuousOn).sub hJ_cont
    have hD_diff : DifferentiableOn Real D (Set.Ioi a) := by
      unfold D
      exact hg_diff.differentiableOn.sub hJ_diff
    have hDu_nonneg : 0 ≤ D u :=
      monotone_ratio_principle
        (a := a)
        (D := D)
        (κ := fun x => 2 * Real.exp (-x ^ 2 / 2))
        (R := fun x => R c0 x)
        hD_cont hD_diff hD_deriv hkappa_pos hR_mono hD_start hD_end u hau.le
    have hDu_nonneg' : 0 ≤ gClosed c0 u - J u := by simpa [D] using hDu_nonneg
    linarith

/-! ## 5. Convex domination at scale c0 -/

lemma mean_gaussianScale (c : Real) : mean (gaussianScale c) = 0 := by
  unfold mean gaussianScale gaussianMeasure
  rw [ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : Real)) (v := (1 : NNReal)) (c := c)]
  simp

theorem J_ge_tangent_line :
    ∀ u : Real, 0 <= u → (B - p0 * u) <= J u := by
  intro u hu0
  by_cases hua : u <= a
  · simp [J_of_le_a hua]
  · have hau : a < u := lt_of_not_ge hua
    rw [J_of_gt_a hau]
    have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
    have hs_ioc : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioc a u) := by
      exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi ha_pos.le)).mono_set Set.Ioc_subset_Ioi_self
    have hs_iou : MeasureTheory.IntegrableOn (fun t => s t) (Set.Ioi u) := by
      exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi ha_pos.le)).mono_set (Set.Ioi_subset_Ioi hau.le)
    have hsplit :
        ∫ t in Set.Ioi a, s t ∂MeasureTheory.volume =
          (∫ t in Set.Ioc a u, s t ∂MeasureTheory.volume) +
            (∫ t in Set.Ioi u, s t ∂MeasureTheory.volume) := by
      rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hs_ioc hs_iou]
      rw [Set.Ioc_union_Ioi_eq_Ioi hau.le]
    have hs_ioc_const : MeasureTheory.IntegrableOn (fun _ : Real => p0) (Set.Ioc a u) := by
      exact MeasureTheory.integrableOn_const (measure_Ioc_lt_top (μ := MeasureTheory.volume) (a := a) (b := u)).ne
    have hbound_ioc :
        ∫ t in Set.Ioc a u, s t ∂MeasureTheory.volume <=
          ∫ t in Set.Ioc a u, p0 ∂MeasureTheory.volume := by
      refine MeasureTheory.setIntegral_mono_on hs_ioc hs_ioc_const measurableSet_Ioc ?_
      intro t ht
      exact s_le_p0_of_ge_a (le_of_lt ht.1)
    have hioc_const :
        ∫ t in Set.Ioc a u, p0 ∂MeasureTheory.volume = p0 * (u - a) := by
      simp [MeasureTheory.integral_const, smul_eq_mul, hau.le, mul_comm]
    have hB :
        B = a * p0 + ∫ t in Set.Ioi a, s t ∂MeasureTheory.volume := by
      have hHa : H a = B := a_spec.2
      have hHa' : B = a * s a + ∫ t in Set.Ioi a, s t ∂MeasureTheory.volume := by
        simpa [H] using hHa.symm
      simpa [p0] using hHa'
    have hlhs :
        B - p0 * u =
          (∫ t in Set.Ioi a, s t ∂MeasureTheory.volume) - p0 * (u - a) := by
      rw [hB]
      ring
    calc
      B - p0 * u
          = (∫ t in Set.Ioi a, s t ∂MeasureTheory.volume) - p0 * (u - a) := hlhs
      _ <= (∫ t in Set.Ioi a, s t ∂MeasureTheory.volume) -
            (∫ t in Set.Ioc a u, s t ∂MeasureTheory.volume) := by
            linarith [hbound_ioc, hioc_const]
      _ = ∫ t in Set.Ioi u, s t ∂MeasureTheory.volume := by
            linarith [hsplit]

/-! ## 6a. Extremal measure construction -/


noncomputable def fStar (x : Real) : Real :=
  if x < -a then 0
  else if x <= -t0 then -2 * x * Real.exp (-(x ^ 2) / 2)
  else if x < a then 0
  else 2 * x * Real.exp (-(x ^ 2) / 2)

noncomputable def muStar : Measure Real :=
  Measure.withDensity volume (fun x => ENNReal.ofReal (fStar x))

lemma fStar_nonneg (x : Real) : 0 <= fStar x := by
  unfold fStar
  split_ifs with h1 h2 h3
  · norm_num
  · have hx_neg : x < 0 := by
      have ht0neg : -t0 < 0 := by
        exact neg_lt_zero.mpr t0_pos
      linarith
    have hfac : 0 ≤ -2 * x := by nlinarith [hx_neg]
    exact mul_nonneg hfac (by positivity)
  · norm_num
  · have hx_pos : 0 < x := by linarith [a_spec.1]
    positivity

lemma fStar_measurable : Measurable fStar := by
  have hcore : Measurable (fun x : Real => x * Real.exp (-(x ^ 2) / 2)) := by
    exact Measurable.mul measurable_id
      (Real.continuous_exp.measurable.comp
        (Measurable.div_const (Measurable.neg (measurable_id.pow_const 2)) 2))
  have hneg : Measurable (fun x : Real => -2 * x * Real.exp (-(x ^ 2) / 2)) := by
    convert hcore.const_mul (-2) using 1 with x
    ring_nf
  have hpos : Measurable (fun x : Real => 2 * x * Real.exp (-(x ^ 2) / 2)) := by
    convert hcore.const_mul 2 using 1 with x
    ring_nf
  unfold fStar
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) hneg ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const hpos

lemma integral_Ioi_fStar_of_ge_a {t : Real} (ht : a ≤ t) :
    ∫ x in Set.Ioi t, fStar x ∂volume = 2 * Real.exp (-(t ^ 2) / 2) := by
  have hEq :
      Set.EqOn fStar (fun x : Real => 2 * x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi t) := by
    intro x hx
    have hxa : a < x := lt_of_le_of_lt ht hx
    have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
    have hnot1 : ¬ x < -a := by linarith [hxa, ha_pos]
    have hnot2 : ¬ x ≤ -t0 := by linarith [hxa, a_spec.1, t0_pos]
    have hnot3 : ¬ x < a := not_lt_of_ge hxa.le
    simp [fStar, hnot1, hnot2, hnot3]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq]
  calc
    ∫ x in Set.Ioi t, 2 * x * Real.exp (-(x ^ 2) / 2) ∂volume
        = 2 * (∫ x in Set.Ioi t, x * Real.exp (-(x ^ 2) / 2) ∂volume) := by
          rw [← MeasureTheory.integral_const_mul]
          congr with x
          ring
    _ = 2 * Real.exp (-(t ^ 2) / 2) := by rw [integral_Ioi_mul_exp_neg_sq_half]

lemma integral_Ioi_fStar_of_lt_a {t : Real} (ht : t < a) (ht0 : 0 ≤ t) :
    ∫ x in Set.Ioi t, fStar x ∂volume = 2 * Real.exp (-(a ^ 2) / 2) := by
  have hEqIoo :
      Set.EqOn fStar (fun _ : Real => 0) (Set.Ioo t a) := by
    intro x hx
    have hx_nonneg : 0 ≤ x := le_trans ht0 hx.1.le
    have hnot1 : ¬ x < -a := by linarith [hx_nonneg, a_spec.1]
    have hnot2 : ¬ x ≤ -t0 := by linarith [hx_nonneg, t0_pos]
    have hx_lt_a : x < a := hx.2
    simp [fStar, hnot1, hnot2, hx_lt_a]
  have hIntIoo : MeasureTheory.IntegrableOn fStar (Set.Ioo t a) := by
    exact (MeasureTheory.integrableOn_zero).congr_fun hEqIoo.symm measurableSet_Ioo
  have hIntExpRaw : MeasureTheory.IntegrableOn
      (fun x : Real => 2 * (x * Real.exp (-(x ^ 2) / 2))) (Set.Ioi a) := by
    have hIntBase : MeasureTheory.Integrable (fun x : Real => x * Real.exp (-(x ^ 2) / 2)) := by
      simpa [pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : Real)) (by norm_num) (s := (1 : Real)) (by norm_num))
    exact (hIntBase.const_mul 2).integrableOn.mono_set (Set.Ioi_subset_Ioi le_rfl)
  have hIntExp : MeasureTheory.IntegrableOn
      (fun x : Real => 2 * x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi a) := by
    convert hIntExpRaw using 1 with x
    ring_nf
  have hEqIoi :
      Set.EqOn fStar (fun x : Real => 2 * x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi a) := by
    intro x hx
    have hxa : a < x := hx
    have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
    have hnot1 : ¬ x < -a := by linarith [hxa, ha_pos]
    have hnot2 : ¬ x ≤ -t0 := by linarith [hxa, a_spec.1, t0_pos]
    have hnot3 : ¬ x < a := not_lt_of_ge hxa.le
    simp [fStar, hnot1, hnot2, hnot3]
  have hIntIoiA : MeasureTheory.IntegrableOn fStar (Set.Ioi a) := by
    exact hIntExp.congr_fun hEqIoi.symm measurableSet_Ioi
  have hIntIciA : MeasureTheory.IntegrableOn fStar (Set.Ici a) := by
    exact hIntIoiA.congr_set_ae (Ioi_ae_eq_Ici.symm)
  have hdisj : Disjoint (Set.Ioo t a) (Set.Ici a) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx1 hx2
    exact (not_lt_of_ge hx2) hx1.2
  have hsplit :
      ∫ x in Set.Ioi t, fStar x ∂volume =
        ∫ x in Set.Ioo t a, fStar x ∂volume + ∫ x in Set.Ici a, fStar x ∂volume := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ici hIntIoo hIntIciA]
    have hset : Set.Ioo t a ∪ Set.Ici a = Set.Ioi t := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hx.1
        · exact lt_of_lt_of_le ht hx
      · intro hx
        by_cases hxa : x < a
        · exact Or.inl ⟨hx, hxa⟩
        · exact Or.inr (le_of_not_gt hxa)
    rw [hset]
  have hIoo_zero : ∫ x in Set.Ioo t a, fStar x ∂volume = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hEqIoo]
    simp
  have hIci_eq : ∫ x in Set.Ici a, fStar x ∂volume = ∫ x in Set.Ioi a, fStar x ∂volume := by
    simpa using (MeasureTheory.integral_Ici_eq_integral_Ioi (f := fStar) (x := a) (μ := (volume : Measure Real)))
  have hIoiA : ∫ x in Set.Ioi a, fStar x ∂volume = 2 * Real.exp (-(a ^ 2) / 2) :=
    integral_Ioi_fStar_of_ge_a le_rfl
  calc
    ∫ x in Set.Ioi t, fStar x ∂volume
        = ∫ x in Set.Ioo t a, fStar x ∂volume + ∫ x in Set.Ici a, fStar x ∂volume := hsplit
    _ = 0 + ∫ x in Set.Ici a, fStar x ∂volume := by rw [hIoo_zero]
    _ = ∫ x in Set.Ioi a, fStar x ∂volume := by simp [hIci_eq]
    _ = 2 * Real.exp (-(a ^ 2) / 2) := hIoiA

lemma integral_Ioi_muStar_meas_gt_eq (t : Real) :
    prob muStar (Set.Ioi t) = ∫ x in Set.Ioi t, fStar x ∂volume := by
  unfold prob muStar
  rw [MeasureTheory.withDensity_apply _ measurableSet_Ioi]
  symm
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => fStar_nonneg x)
    fStar_measurable.aestronglyMeasurable

theorem rightTail_muStar :
    ∀ t : Real, 0 <= t →
      prob muStar {x : Real | x > t} = if t < a then p0 else 2 * Real.exp (-(t ^ 2) / 2) := by
  intro t ht
  change prob muStar (Set.Ioi t) = if t < a then p0 else 2 * Real.exp (-(t ^ 2) / 2)
  have hprob : prob muStar (Set.Ioi t) = ∫ x in Set.Ioi t, fStar x ∂volume :=
    integral_Ioi_muStar_meas_gt_eq t
  by_cases ht_a : t < a
  · rw [if_pos ht_a, hprob, integral_Ioi_fStar_of_lt_a ht_a ht, p0]
    exact (s_eq_gauss_tail_of_gt_t0 a_spec.1).symm
  · rw [if_neg ht_a, hprob, integral_Ioi_fStar_of_ge_a (le_of_not_gt ht_a)]

lemma hasDerivAt_two_exp_neg_sq_half (x : Real) :
    HasDerivAt (fun x => 2 * Real.exp (-(x ^ 2) / 2))
      (-2 * x * Real.exp (-(x ^ 2) / 2)) x := by
  have harg : HasDerivAt (fun t => -(t ^ 2) / 2) (-x) x := by
    convert (HasDerivAt.div_const (HasDerivAt.neg (hasDerivAt_pow 2 x)) (2 : Real)) using 1
    ring
  have hexp : HasDerivAt (fun t => Real.exp (-(t ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * (-x)) x := (HasDerivAt.exp harg)
  convert hexp.const_mul 2 using 1
  ring

lemma integral_Icc_neg_a_neg_t_fStar {t : Real} (ht0 : t0 ≤ t) (hta : t ≤ a) :
    ∫ x in Set.Icc (-a) (-t), fStar x ∂volume = 2 * Real.exp (-(t ^ 2) / 2) - p0 := by
  let g : Real → Real := fun x => -2 * x * Real.exp (-(x ^ 2) / 2)
  have hEqIcc : Set.EqOn fStar g (Set.Icc (-a) (-t)) := by
    intro x hx
    have hnot1 : ¬ x < -a := not_lt_of_ge hx.1
    have hle_t0 : x ≤ -t0 := by
      linarith [hx.2, ht0]
    simp [g, fStar, hnot1, hle_t0]
  have hab : -a ≤ -t := by
    nlinarith [hta]
  have hInterval :
      ∫ x in (-a)..(-t), g x =
        (2 * Real.exp (-((-t) ^ 2) / 2)) - (2 * Real.exp (-((-a) ^ 2) / 2)) := by
    have hderiv : ∀ x ∈ Set.uIcc (-a) (-t), HasDerivAt (fun x => 2 * Real.exp (-(x ^ 2) / 2)) (g x) x := by
      intro x hx
      simpa [g] using hasDerivAt_two_exp_neg_sq_half x
    have hint : IntervalIntegrable g volume (-a) (-t) := by
      exact (by continuity : Continuous g).intervalIntegrable _ _
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hp0 : p0 = 2 * Real.exp (-(a ^ 2) / 2) := by
    simpa [p0] using s_eq_gauss_tail_of_gt_t0 a_spec.1
  calc
    ∫ x in Set.Icc (-a) (-t), fStar x ∂volume
        = ∫ x in Set.Icc (-a) (-t), g x ∂volume := by
            rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hEqIcc]
    _ = ∫ x in Set.Ioc (-a) (-t), g x ∂volume := by
          simpa using
            (MeasureTheory.integral_Icc_eq_integral_Ioc (f := g) (x := (-a)) (y := (-t))
              (μ := (volume : Measure Real)))
    _ = ∫ x in (-a)..(-t), g x := by
          symm
          simpa using
            (intervalIntegral.integral_of_le hab :
              ∫ x in (-a)..(-t), g x = ∫ x in Set.Ioc (-a) (-t), g x ∂volume)
    _ = 2 * Real.exp (-(t ^ 2) / 2) - p0 := by
          rw [hInterval]
          have hsq_t : (-t) ^ 2 = t ^ 2 := by ring
          have hsq_a : (-a) ^ 2 = a ^ 2 := by ring
          rw [hsq_t, hsq_a, hp0]

lemma integral_Iio_fStar_of_ge_t0_lt_a {t : Real} (ht0 : t0 ≤ t) (hta : t < a) :
    ∫ x in Set.Iio (-t), fStar x ∂volume = 2 * Real.exp (-(t ^ 2) / 2) - p0 := by
  let g : Real → Real := fun x => -2 * x * Real.exp (-(x ^ 2) / 2)
  have hdisj : Disjoint (Set.Iio (-a)) (Set.Ico (-a) (-t)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx1 hx2
    exact (not_lt_of_ge hx2.1) hx1
  have hset : Set.Iio (-t) = Set.Iio (-a) ∪ Set.Ico (-a) (-t) := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x < -a
      · exact Or.inl hxa
      · exact Or.inr ⟨le_of_not_gt hxa, hx⟩
    · intro hx
      rcases hx with hx | hx
      · have hxlt : x < -a := hx
        exact lt_trans hxlt (by nlinarith [hta])
      · exact hx.2
  have hEqLeft : Set.EqOn fStar (fun _ : Real => 0) (Set.Iio (-a)) := by
    intro x hx
    have hxlt : x < -a := hx
    simp [fStar, hxlt]
  have hIntLeft : MeasureTheory.IntegrableOn fStar (Set.Iio (-a)) := by
    exact (MeasureTheory.integrableOn_zero).congr_fun hEqLeft.symm measurableSet_Iio
  have hEqRight : Set.EqOn fStar g (Set.Ico (-a) (-t)) := by
    intro x hx
    have hnot1 : ¬ x < -a := not_lt_of_ge hx.1
    have hle_t0 : x ≤ -t0 := by
      linarith [hx.2, ht0]
    simp [g, fStar, hnot1, hle_t0]
  have hIntgIcc : MeasureTheory.IntegrableOn g (Set.Icc (-a) (-t)) := by
    exact (by continuity : Continuous g).integrableOn_Icc
  have hIntgIco : MeasureTheory.IntegrableOn g (Set.Ico (-a) (-t)) := by
    exact hIntgIcc.mono_set Set.Ico_subset_Icc_self
  have hIntRight : MeasureTheory.IntegrableOn fStar (Set.Ico (-a) (-t)) := by
    exact hIntgIco.congr_fun hEqRight.symm measurableSet_Ico
  have hleft_zero : ∫ x in Set.Iio (-a), fStar x ∂volume = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iio hEqLeft]
    simp
  have hright :
      ∫ x in Set.Ico (-a) (-t), fStar x ∂volume =
        ∫ x in Set.Icc (-a) (-t), fStar x ∂volume := by
    symm
    simpa using
      (MeasureTheory.integral_Icc_eq_integral_Ico (f := fStar) (x := (-a)) (y := (-t))
        (μ := (volume : Measure Real)))
  rw [hset, MeasureTheory.setIntegral_union hdisj measurableSet_Ico hIntLeft hIntRight]
  rw [hleft_zero, hright, integral_Icc_neg_a_neg_t_fStar ht0 hta.le, zero_add]

lemma integral_Iio_fStar_of_ge_a {t : Real} (hta : a ≤ t) :
    ∫ x in Set.Iio (-t), fStar x ∂volume = 0 := by
  have hEq : Set.EqOn fStar (fun _ : Real => 0) (Set.Iio (-t)) := by
    intro x hx
    have hneg_le : -t ≤ -a := by nlinarith [hta]
    have hxlt : x < -a := lt_of_lt_of_le hx hneg_le
    simp [fStar, hxlt]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iio hEq]
  simp

lemma integral_Iio_muStar_meas_lt_eq (t : Real) :
    prob muStar (Set.Iio t) = ∫ x in Set.Iio t, fStar x ∂volume := by
  unfold prob muStar
  rw [MeasureTheory.withDensity_apply _ measurableSet_Iio]
  symm
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => fStar_nonneg x)
    fStar_measurable.aestronglyMeasurable

lemma integral_Iio_fStar_of_lt_t0 {t : Real} (ht : t < t0) (ht0_nonneg : 0 ≤ t) :
    ∫ x in Set.Iio (-t), fStar x ∂volume = 1 - p0 := by
  let S1 : Set Real := Set.Iio (-a)
  let S2 : Set Real := Set.Icc (-a) (-t0)
  let S3 : Set Real := Set.Ioo (-t0) (-t)
  let g : Real → Real := fun x => -2 * x * Real.exp (-(x ^ 2) / 2)
  have hdisj12 : Disjoint S1 S2 := by
    refine Set.disjoint_left.mpr ?_
    intro x hx1 hx2
    exact (not_lt_of_ge hx2.1) hx1
  have hdisj123 : Disjoint (S1 ∪ S2) S3 := by
    refine Set.disjoint_left.mpr ?_
    intro x hx12 hx3
    rcases hx12 with hx1 | hx2
    · have hxa : x < -a := hx1
      have hxa_t0 : -a < -t0 := by linarith [a_spec.1]
      have hx3' : -t0 < x := hx3.1
      linarith
    · have hx2' : x ≤ -t0 := hx2.2
      have hx3' : -t0 < x := hx3.1
      linarith
  have hset : Set.Iio (-t) = (S1 ∪ S2) ∪ S3 := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x < -a
      · exact Or.inl (Or.inl hxa)
      · have hxa_le : -a ≤ x := le_of_not_gt hxa
        by_cases hxt0 : x ≤ -t0
        · exact Or.inl (Or.inr ⟨hxa_le, hxt0⟩)
        · have hxt0_lt : -t0 < x := lt_of_not_ge hxt0
          exact Or.inr ⟨hxt0_lt, hx⟩
    · intro hx
      rcases hx with hx12 | hx3
      · rcases hx12 with hx1 | hx2
        · have hxa : x < -a := hx1
          have hxa_t : -a < -t := by linarith [a_spec.1, ht]
          exact lt_trans hxa hxa_t
        · have hxt0 : x ≤ -t0 := hx2.2
          have ht0_t : -t0 < -t := by linarith [ht]
          exact lt_of_le_of_lt hxt0 ht0_t
      · exact hx3.2
  have hEqS1 : Set.EqOn fStar (fun _ : Real => 0) S1 := by
    intro x hx
    have hxlt : x < -a := hx
    simp [fStar, hxlt]
  have hEqS2 : Set.EqOn fStar g S2 := by
    intro x hx
    have hnot1 : ¬ x < -a := not_lt_of_ge hx.1
    have hle_t0 : x ≤ -t0 := hx.2
    simp [g, fStar, hnot1, hle_t0]
  have hEqS3 : Set.EqOn fStar (fun _ : Real => 0) S3 := by
    intro x hx
    have hxgt_t0 : -t0 < x := hx.1
    have hxlt_a : x < a := by linarith [hx.2, ht0_nonneg, a_spec.1]
    have hnot1 : ¬ x < -a := by
      have hxa_t0 : -a < -t0 := by linarith [a_spec.1]
      linarith [hxgt_t0, hxa_t0]
    have hnot2 : ¬ x ≤ -t0 := not_le_of_gt hxgt_t0
    simp [fStar, hnot1, hnot2, hxlt_a]
  have hIntS1 : MeasureTheory.IntegrableOn fStar S1 := by
    exact (MeasureTheory.integrableOn_zero).congr_fun hEqS1.symm measurableSet_Iio
  have hIntgS2 : MeasureTheory.IntegrableOn g S2 := by
    exact (by continuity : Continuous g).integrableOn_Icc
  have hIntS2 : MeasureTheory.IntegrableOn fStar S2 := by
    exact hIntgS2.congr_fun hEqS2.symm measurableSet_Icc
  have hIntS3 : MeasureTheory.IntegrableOn fStar S3 := by
    exact (MeasureTheory.integrableOn_zero).congr_fun hEqS3.symm measurableSet_Ioo
  have hIntS12 : MeasureTheory.IntegrableOn fStar (S1 ∪ S2) := by
    exact (MeasureTheory.integrableOn_union).2 ⟨hIntS1, hIntS2⟩
  have hsplit :
      ∫ x in Set.Iio (-t), fStar x ∂volume =
        ∫ x in (S1 ∪ S2), fStar x ∂volume + ∫ x in S3, fStar x ∂volume := by
    rw [hset, MeasureTheory.setIntegral_union hdisj123 measurableSet_Ioo hIntS12 hIntS3]
  have hsplit12 :
      ∫ x in (S1 ∪ S2), fStar x ∂volume =
        ∫ x in S1, fStar x ∂volume + ∫ x in S2, fStar x ∂volume := by
    rw [MeasureTheory.setIntegral_union hdisj12 measurableSet_Icc hIntS1 hIntS2]
  have hS1_zero : ∫ x in S1, fStar x ∂volume = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iio hEqS1]
    simp
  have hS3_zero : ∫ x in S3, fStar x ∂volume = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hEqS3]
    simp
  have hS2 : ∫ x in S2, fStar x ∂volume = 2 * Real.exp (-(t0 ^ 2) / 2) - p0 := by
    simpa [S2] using integral_Icc_neg_a_neg_t_fStar (t := t0) le_rfl a_spec.1.le
  have htwo : 2 * Real.exp (-(t0 ^ 2) / 2) = 1 := by
    unfold t0
    have hnonneg : 0 ≤ 2 * Real.log 2 := by positivity
    calc
      2 * Real.exp (-(Real.sqrt (2 * Real.log 2) ^ 2) / 2)
          = 2 * Real.exp (-(2 * Real.log 2) / 2) := by rw [Real.sq_sqrt hnonneg]
      _ = 2 * Real.exp (-Real.log 2) := by ring_nf
      _ = 2 * (Real.exp (Real.log 2))⁻¹ := by simp [Real.exp_neg]
      _ = 2 * ((2 : Real)⁻¹) := by rw [Real.exp_log (by norm_num : (0 : Real) < 2)]
      _ = 1 := by norm_num
  calc
    ∫ x in Set.Iio (-t), fStar x ∂volume
        = ∫ x in (S1 ∪ S2), fStar x ∂volume + ∫ x in S3, fStar x ∂volume := hsplit
    _ = (∫ x in S1, fStar x ∂volume + ∫ x in S2, fStar x ∂volume) + ∫ x in S3, fStar x ∂volume := by
          rw [hsplit12]
    _ = (0 + (2 * Real.exp (-(t0 ^ 2) / 2) - p0)) + 0 := by rw [hS1_zero, hS2, hS3_zero]
    _ = 1 - p0 := by
          rw [htwo]
          ring

theorem leftTail_muStar :
    ∀ t : Real, 0 <= t →
      prob muStar {x : Real | x < -t} =
        if t < t0 then 1 - p0 else if t < a then 2 * Real.exp (-(t ^ 2) / 2) - p0 else 0 := by
  intro t ht
  change prob muStar (Set.Iio (-t)) =
    if t < t0 then 1 - p0 else if t < a then 2 * Real.exp (-(t ^ 2) / 2) - p0 else 0
  rw [integral_Iio_muStar_meas_lt_eq]
  by_cases ht0 : t < t0
  · rw [if_pos ht0, integral_Iio_fStar_of_lt_t0 ht0 ht]
  · have ht0le : t0 ≤ t := le_of_not_gt ht0
    rw [if_neg ht0]
    by_cases hta : t < a
    · rw [if_pos hta, integral_Iio_fStar_of_ge_t0_lt_a ht0le hta]
    · rw [if_neg hta, integral_Iio_fStar_of_ge_a (le_of_not_gt hta)]

theorem muStar_isProbability : IsProbabilityMeasure muStar := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have hright : prob muStar (Set.Ioi (0 : Real)) = p0 := by
    have h0a : (0 : Real) < a := lt_trans t0_pos a_spec.1
    simpa [if_pos h0a] using rightTail_muStar 0 (by norm_num)
  have hleft : prob muStar (Set.Iio (0 : Real)) = 1 - p0 := by
    simpa [if_pos t0_pos] using leftTail_muStar 0 (by norm_num)
  have hp0_pos : 0 < p0 := by
    unfold p0 s
    exact lt_min zero_lt_one (mul_pos zero_lt_two (Real.exp_pos _))
  have hOne_sub_p0_pos : 0 < 1 - p0 := by
    linarith [p0_lt_half]
  let S : Set Real := Set.Ioi (0 : Real) ∪ Set.Iio (0 : Real)
  have hS_prob : prob muStar S = 1 := by
    have hdisj : Disjoint (Set.Ioi (0 : Real)) (Set.Iio (0 : Real)) := by
      refine Set.disjoint_left.mpr ?_
      intro x hx1 hx2
      have hx1' : 0 < x := hx1
      have hx2' : x < 0 := hx2
      linarith [hx1', hx2']
    have hIoi_ne_top : muStar (Set.Ioi (0 : Real)) ≠ ⊤ := by
      intro htop
      have hzero : prob muStar (Set.Ioi (0 : Real)) = 0 := by simp [prob, htop]
      linarith [hzero, hright, hp0_pos]
    have hIio_ne_top : muStar (Set.Iio (0 : Real)) ≠ ⊤ := by
      intro htop
      have hzero : prob muStar (Set.Iio (0 : Real)) = 0 := by simp [prob, htop]
      linarith [hzero, hleft, hOne_sub_p0_pos]
    have hright' : (muStar (Set.Ioi (0 : Real))).toReal = p0 := by
      simpa [prob] using hright
    have hleft' : (muStar (Set.Iio (0 : Real))).toReal = 1 - p0 := by
      simpa [prob] using hleft
    have hsum :
        (muStar (Set.Ioi (0 : Real))).toReal + (muStar (Set.Iio (0 : Real))).toReal = 1 := by
      calc
        (muStar (Set.Ioi (0 : Real))).toReal + (muStar (Set.Iio (0 : Real))).toReal
            = p0 + (1 - p0) := by rw [hright', hleft']
        _ = 1 := by ring
    unfold prob S
    rw [MeasureTheory.measure_union hdisj measurableSet_Iio]
    rw [ENNReal.toReal_add hIoi_ne_top hIio_ne_top]
    simpa using hsum
  have hsingle : muStar ({0} : Set Real) = 0 := by
    have h_ac : muStar ≪ MeasureTheory.volume :=
      MeasureTheory.withDensity_absolutelyContinuous _ _
    exact h_ac (by simp)
  have hS_disj_single : Disjoint S ({0} : Set Real) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxS hx0
    rcases hxS with hxgt | hxlt
    · exact (ne_of_gt hxgt) (by simpa using hx0)
    · exact (ne_of_lt hxlt) (by simpa using hx0)
  have hS_univ : S ∪ ({0} : Set Real) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hx0 : x = 0
      · right
        simp [hx0]
      · by_cases hxlt : x < 0
        · left
          exact Or.inr hxlt
        · left
          exact Or.inl (lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm hx0))
  have hS_ne_top : muStar S ≠ ⊤ := by
    intro htop
    have hzero : prob muStar S = 0 := by simp [prob, htop]
    linarith [hzero, hS_prob]
  have hprob_univ : prob muStar Set.univ = 1 := by
    unfold prob
    calc
      (muStar Set.univ).toReal = (muStar (S ∪ ({0} : Set Real))).toReal := by simp [hS_univ]
      _ = (muStar S + muStar ({0} : Set Real)).toReal := by
            rw [MeasureTheory.measure_union hS_disj_single (measurableSet_singleton (0 : Real))]
      _ = (muStar S).toReal + (muStar ({0} : Set Real)).toReal := by
            rw [ENNReal.toReal_add hS_ne_top (by simp [hsingle])]
      _ = (muStar S).toReal := by simp [hsingle]
      _ = 1 := hS_prob
  simpa [prob] using hprob_univ

lemma z_nonneg : 0 <= z := (le_of_lt z_pos)

lemma two_exp_neg_t0_sq_div_two_eq_one : 2 * Real.exp (-(t0 ^ 2) / 2) = 1 := by
  unfold t0
  have hnonneg : 0 ≤ 2 * Real.log 2 := by positivity
  calc
    2 * Real.exp (-(Real.sqrt (2 * Real.log 2) ^ 2) / 2)
        = 2 * Real.exp (-(2 * Real.log 2) / 2) := by rw [Real.sq_sqrt hnonneg]
    _ = 2 * Real.exp (-Real.log 2) := by ring_nf
    _ = 2 * (Real.exp (Real.log 2))⁻¹ := by simp [Real.exp_neg]
    _ = 2 * ((2 : Real)⁻¹) := by rw [Real.exp_log (by norm_num : (0 : Real) < 2)]
    _ = 1 := by norm_num

lemma s_eq_one_of_nonneg_lt_t0 {t : Real} (ht0 : 0 ≤ t) (ht : t < t0) : s t = 1 := by
  unfold s
  have hsq_lt : t ^ 2 < t0 ^ 2 := by nlinarith [ht, ht0, t0_pos]
  have hexp_gt : Real.exp (-(t ^ 2) / 2) > Real.exp (-(t0 ^ 2) / 2) := by
    exact Real.exp_lt_exp.mpr (by nlinarith [hsq_lt])
  have hmul_gt :
      2 * Real.exp (-(t ^ 2) / 2) > 2 * Real.exp (-(t0 ^ 2) / 2) := by
    exact mul_lt_mul_of_pos_left hexp_gt (by norm_num : (0 : Real) < 2)
  have hge1 : 1 ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
    linarith [hmul_gt, two_exp_neg_t0_sq_div_two_eq_one]
  exact min_eq_left hge1

lemma s_eq_gauss_tail_of_ge_t0 {t : Real} (ht : t0 ≤ t) :
    s t = 2 * Real.exp (-(t ^ 2) / 2) := by
  by_cases hEq : t0 = t
  · subst hEq
    unfold s
    rw [two_exp_neg_t0_sq_div_two_eq_one]
    simp
  · have hgt : t0 < t := lt_of_le_of_ne ht hEq
    exact s_eq_gauss_tail_of_gt_t0 hgt

theorem absTail_muStar_eq_s : ∀ t : Real, 0 <= t → absTail muStar t = s t := by
  letI : IsProbabilityMeasure muStar := muStar_isProbability
  intro t ht
  have hsplit :
      absTail muStar t
        = prob muStar (Set.Ioi t) + prob muStar (Set.Iio (-t)) := by
    have hset :
        {x : Real | |x| > t} = Set.Ioi t ∪ Set.Iio (-t) := by
      ext x
      constructor
      · intro hx
        by_cases hx0 : 0 ≤ x
        · left
          have hxabs : |x| = x := abs_of_nonneg hx0
          have hxt : t < |x| := by simpa using hx
          have hxt' : t < x := by simpa [hxabs] using hxt
          exact hxt'
        · right
          have hxneg : x < 0 := lt_of_not_ge hx0
          have hxabs : |x| = -x := abs_of_neg hxneg
          have hxt : t < |x| := by simpa using hx
          have hxt' : x < -t := by linarith [hxt, hxabs]
          exact hxt'
      · intro hx
        rcases hx with hxt | hxt
        · have habs : x ≤ |x| := le_abs_self x
          have hxt' : t < x := hxt
          have habs_gt : |x| > t := lt_of_lt_of_le hxt' habs
          exact habs_gt
        · have habs : -x ≤ |x| := neg_le_abs x
          have hxt' : x < -t := hxt
          have hneg_gt : -x > t := by linarith [hxt']
          have habs_gt : |x| > t := lt_of_lt_of_le hneg_gt habs
          exact habs_gt
    have hdisj : Disjoint (Set.Ioi t) (Set.Iio (-t)) := by
      refine Set.disjoint_left.mpr ?_
      intro x hx1 hx2
      have hx1' : x > t := Set.mem_Ioi.mp hx1
      have hx2' : x < -t := Set.mem_Iio.mp hx2
      linarith [hx1', hx2', ht]
    have hfin_gt : muStar (Set.Ioi t) ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    have hfin_lt : muStar (Set.Iio (-t)) ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    unfold absTail prob
    rw [hset, MeasureTheory.measure_union hdisj measurableSet_Iio]
    rw [ENNReal.toReal_add hfin_gt hfin_lt]
  have hright : prob muStar (Set.Ioi t) = if t < a then p0 else 2 * Real.exp (-(t ^ 2) / 2) := by
    simpa using rightTail_muStar t ht
  have hleft :
      prob muStar (Set.Iio (-t)) =
        if t < t0 then 1 - p0 else if t < a then 2 * Real.exp (-(t ^ 2) / 2) - p0 else 0 := by
    simpa using leftTail_muStar t ht
  by_cases ht0 : t < t0
  · have hta : t < a := lt_trans ht0 a_spec.1
    rw [if_pos hta] at hright
    rw [if_pos ht0] at hleft
    calc
      absTail muStar t = p0 + (1 - p0) := by rw [hsplit, hright, hleft]
      _ = 1 := by ring
      _ = s t := (s_eq_one_of_nonneg_lt_t0 ht ht0).symm
  · have ht0le : t0 ≤ t := le_of_not_gt ht0
    by_cases hta : t < a
    · rw [if_pos hta] at hright
      rw [if_neg ht0, if_pos hta] at hleft
      calc
        absTail muStar t = p0 + (2 * Real.exp (-(t ^ 2) / 2) - p0) := by rw [hsplit, hright, hleft]
        _ = 2 * Real.exp (-(t ^ 2) / 2) := by ring
        _ = s t := (s_eq_gauss_tail_of_ge_t0 ht0le).symm
    · rw [if_neg hta] at hright
      rw [if_neg ht0, if_neg hta] at hleft
      calc
        absTail muStar t = (2 * Real.exp (-(t ^ 2) / 2)) + 0 := by rw [hsplit, hright, hleft]
        _ = 2 * Real.exp (-(t ^ 2) / 2) := by ring
        _ = s t := (s_eq_gauss_tail_of_ge_t0 ht0le).symm

theorem stopLoss_muStar_eq_J : ∀ u : Real, 0 <= u → stopLoss muStar u = J u := by
  letI : IsProbabilityMeasure muStar := muStar_isProbability
  intro u hu0
  have ha_pos : 0 < a := lt_trans t0_pos a_spec.1
  have hlayer :
      stopLoss muStar u = ∫ t in Set.Ioi u, prob muStar {x : Real | x > t} := by
    simpa using stopLoss_eq_integral_tail (μ := muStar) u
  by_cases hua : u ≤ a
  · have hEqIoc :
        Set.EqOn (fun t : Real => prob muStar {x : Real | x > t}) (fun _ : Real => p0) (Set.Ioc u a) := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans hu0 ht.1.le
      have htail := rightTail_muStar t ht0
      by_cases hta : t < a
      · rw [if_pos hta] at htail
        exact htail
      · rw [if_neg hta] at htail
        have hta_eq : t = a := le_antisymm ht.2 (le_of_not_gt hta)
        subst hta_eq
        have hs_a : s a = 2 * Real.exp (-(a ^ 2) / 2) :=
          s_eq_gauss_tail_of_gt_t0 (x := a) a_spec.1
        simpa [p0, hs_a] using htail
    have hEqIoiA :
        Set.EqOn (fun t : Real => prob muStar {x : Real | x > t}) (fun t : Real => s t) (Set.Ioi a) := by
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt (lt_trans ha_pos ht)
      have htail := rightTail_muStar t ht0
      have hnot : ¬ t < a := not_lt_of_ge ht.le
      rw [if_neg hnot] at htail
      calc
        prob muStar {x : Real | x > t} = 2 * Real.exp (-(t ^ 2) / 2) := htail
        _ = s t := (s_eq_gauss_tail_of_gt_t0 (lt_trans a_spec.1 ht)).symm
    have hIntConstIoc : MeasureTheory.IntegrableOn (fun _ : Real => p0) (Set.Ioc u a) := by
      exact MeasureTheory.integrableOn_const (measure_Ioc_lt_top (μ := (volume : Measure Real))
        (a := u) (b := a)).ne
    have hIntProbIoc : MeasureTheory.IntegrableOn (fun t : Real => prob muStar {x : Real | x > t}) (Set.Ioc u a) := by
      exact hIntConstIoc.congr_fun hEqIoc.symm measurableSet_Ioc
    have hIntSIoiA : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioi a) := by
      exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi ha_pos.le))
    have hIntProbIoiA : MeasureTheory.IntegrableOn (fun t : Real => prob muStar {x : Real | x > t}) (Set.Ioi a) := by
      exact hIntSIoiA.congr_fun hEqIoiA.symm measurableSet_Ioi
    have hsplit :
        ∫ t in Set.Ioi u, prob muStar {x : Real | x > t} ∂volume =
          (∫ t in Set.Ioc u a, prob muStar {x : Real | x > t} ∂volume) +
            (∫ t in Set.Ioi a, prob muStar {x : Real | x > t} ∂volume) := by
      rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIntProbIoc hIntProbIoiA]
      rw [Set.Ioc_union_Ioi_eq_Ioi hua]
    have hioc_const :
        ∫ t in Set.Ioc u a, prob muStar {x : Real | x > t} ∂volume = p0 * (a - u) := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hEqIoc]
      simp [MeasureTheory.integral_const, smul_eq_mul, hua, mul_comm]
    have hiou_s :
        ∫ t in Set.Ioi a, prob muStar {x : Real | x > t} ∂volume =
          ∫ t in Set.Ioi a, s t ∂volume := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoiA]
    have hB : B = p0 * a + ∫ t in Set.Ioi a, s t ∂volume := by
      have hHa : H a = B := a_spec.2
      have hHa' : B = a * s a + ∫ t in Set.Ioi a, s t ∂volume := by
        simpa [H] using hHa.symm
      simpa [p0, mul_comm] using hHa'
    have hJu : J u = B - p0 * u := J_of_le_a hua
    calc
      stopLoss muStar u = ∫ t in Set.Ioi u, prob muStar {x : Real | x > t} ∂volume := hlayer
      _ = (∫ t in Set.Ioc u a, prob muStar {x : Real | x > t} ∂volume) +
            (∫ t in Set.Ioi a, prob muStar {x : Real | x > t} ∂volume) := hsplit
      _ = p0 * (a - u) + ∫ t in Set.Ioi a, s t ∂volume := by rw [hioc_const, hiou_s]
      _ = B - p0 * u := by
            linarith [hB]
      _ = J u := hJu.symm
  · have hau : a < u := lt_of_not_ge hua
    have hEqIoiU :
        Set.EqOn (fun t : Real => prob muStar {x : Real | x > t}) (fun t : Real => s t) (Set.Ioi u) := by
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hu0 ht)
      have htail := rightTail_muStar t ht0
      have hnot : ¬ t < a := not_lt_of_ge (le_trans hau.le ht.le)
      rw [if_neg hnot] at htail
      calc
        prob muStar {x : Real | x > t} = 2 * Real.exp (-(t ^ 2) / 2) := htail
        _ = s t := (s_eq_gauss_tail_of_gt_t0 (lt_trans a_spec.1 (lt_trans hau ht))).symm
    have hIntSIoiU : MeasureTheory.IntegrableOn (fun t : Real => s t) (Set.Ioi u) := by
      exact (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi hu0))
    have hIntProbIoiU :
        MeasureTheory.IntegrableOn (fun t : Real => prob muStar {x : Real | x > t}) (Set.Ioi u) := by
      exact hIntSIoiU.congr_fun hEqIoiU.symm measurableSet_Ioi
    have hJu : J u = ∫ t in Set.Ioi u, s t ∂volume := J_of_gt_a hau
    calc
      stopLoss muStar u = ∫ t in Set.Ioi u, prob muStar {x : Real | x > t} ∂volume := hlayer
      _ = ∫ t in Set.Ioi u, s t ∂volume := by
            rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoiU]
      _ = J u := hJu.symm

lemma fStar_le_two_abs_mul_exp (x : Real) :
    fStar x ≤ 2 * |x| * Real.exp (-(x ^ 2) / 2) := by
  unfold fStar
  split_ifs with h1 h2 h3
  · positivity
  · have hx_neg : x < 0 := by linarith [h2, t0_pos]
    have hx_abs : |x| = -x := abs_of_neg hx_neg
    calc
      -2 * x * Real.exp (-(x ^ 2) / 2) = 2 * |x| * Real.exp (-(x ^ 2) / 2) := by
        rw [hx_abs]
        ring
      _ ≤ 2 * |x| * Real.exp (-(x ^ 2) / 2) := le_rfl
  · positivity
  · have hx_nonneg : 0 ≤ x := by
      linarith [a_spec.1, h3]
    have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
    calc
      2 * x * Real.exp (-(x ^ 2) / 2) = 2 * |x| * Real.exp (-(x ^ 2) / 2) := by
        rw [hx_abs]
      _ ≤ 2 * |x| * Real.exp (-(x ^ 2) / 2) := le_rfl

lemma integrable_abs_mul_fStar : Integrable (fun x : Real => |x| * fStar x) := by
  have hIntBase : MeasureTheory.Integrable (fun x : Real => x ^ 2 * Real.exp (-(x ^ 2) / 2)) := by
    simpa [pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : Real)) (by norm_num)
        (s := (2 : Real)) (by norm_num))
  have hIntBound : MeasureTheory.Integrable (fun x : Real => 2 * (x ^ 2 * Real.exp (-(x ^ 2) / 2))) := by
    exact hIntBase.const_mul 2
  refine MeasureTheory.Integrable.mono' hIntBound ((measurable_abs.mul fStar_measurable).aestronglyMeasurable) ?_
  filter_upwards with x
  have hf_le : fStar x ≤ 2 * |x| * Real.exp (-(x ^ 2) / 2) := fStar_le_two_abs_mul_exp x
  have hmul_le :
      |x| * fStar x ≤ |x| * (2 * |x| * Real.exp (-(x ^ 2) / 2)) :=
    mul_le_mul_of_nonneg_left hf_le (abs_nonneg x)
  have hmul_eq :
      |x| * (2 * |x| * Real.exp (-(x ^ 2) / 2)) =
        2 * (x ^ 2 * Real.exp (-(x ^ 2) / 2)) := by
    have habs_sq : |x| * |x| = x ^ 2 := by
      calc
        |x| * |x| = |x| ^ 2 := by ring
        _ = x ^ 2 := by rw [sq_abs]
    calc
      |x| * (2 * |x| * Real.exp (-(x ^ 2) / 2))
          = 2 * ((|x| * |x|) * Real.exp (-(x ^ 2) / 2)) := by ring
      _ = 2 * (x ^ 2 * Real.exp (-(x ^ 2) / 2)) := by rw [habs_sq]
  have hnorm_eq : ‖|x| * fStar x‖ = |x| * fStar x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg x) (fStar_nonneg x))]
  calc
    ‖|x| * fStar x‖ = |x| * fStar x := hnorm_eq
    _ ≤ |x| * (2 * |x| * Real.exp (-(x ^ 2) / 2)) := hmul_le
    _ = 2 * (x ^ 2 * Real.exp (-(x ^ 2) / 2)) := hmul_eq

lemma integrable_id_muStar : Integrable (fun x : Real => x) muStar := by
  have hIntXf : MeasureTheory.Integrable (fun x : Real => x * fStar x) := by
    refine MeasureTheory.Integrable.mono' integrable_abs_mul_fStar
      ((measurable_id.mul fStar_measurable).aestronglyMeasurable) ?_
    filter_upwards with x
    have hnonneg : 0 ≤ fStar x := fStar_nonneg x
    calc
      ‖x * fStar x‖ = |x| * fStar x := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
      _ ≤ |x| * fStar x := le_rfl
  unfold muStar
  rw [MeasureTheory.integrable_withDensity_iff
    (hf := Measurable.ennreal_ofReal fStar_measurable)
    (hflt := Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simpa [ENNReal.toReal_ofReal (fStar_nonneg _)] using hIntXf

lemma integral_leftTail_muStar_eq_B :
    ∫ t in Set.Ioi 0, prob muStar {x : Real | x < -t} ∂volume = B := by
  have hs_cont : Continuous s := by
    unfold s
    exact Continuous.min continuous_const
      (Continuous.mul continuous_const (Real.continuous_exp.comp (by continuity)))
  let L : Real → Real := fun t => prob muStar {x : Real | x < -t}
  have hEqL0 : Set.EqOn L (fun _ : Real => 1 - p0) (Set.Ioc 0 t0) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    by_cases htt : t < t0
    · have htail := leftTail_muStar t ht0
      simpa [L, htt] using htail
    · have hteq : t = t0 := le_antisymm ht.2 (le_of_not_gt htt)
      subst hteq
      have htail := leftTail_muStar t0 t0_pos.le
      calc
        L t0 = 2 * Real.exp (-(t0 ^ 2) / 2) - p0 := by
          simpa [L, a_spec.1, lt_irrefl] using htail
        _ = 1 - p0 := by rw [two_exp_neg_t0_sq_div_two_eq_one]
  have hEqL1 : Set.EqOn L (fun t : Real => s t - p0) (Set.Ioc t0 a) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans t0_pos.le ht.1.le
    have hnot_t0 : ¬ t < t0 := not_lt_of_ge ht.1.le
    by_cases hta : t < a
    · have htail := leftTail_muStar t ht0
      simpa [L, hnot_t0, hta, s_eq_gauss_tail_of_gt_t0 ht.1] using htail
    · have hteq : t = a := le_antisymm ht.2 (le_of_not_gt hta)
      subst hteq
      have ha0 : 0 ≤ a := le_of_lt (lt_trans t0_pos a_spec.1)
      have htail := leftTail_muStar a ha0
      have hs_a : s a = p0 := by simp [p0]
      calc
        L a = 0 := by
          simpa [L, not_lt_of_ge a_spec.1.le, lt_irrefl] using htail
        _ = s a - p0 := by simp [hs_a]
  have hEqL2 : Set.EqOn L (fun _ : Real => 0) (Set.Ioi a) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_trans t0_pos (lt_trans a_spec.1 ht))
    have htail := leftTail_muStar t ht0
    have hnot_t0 : ¬ t < t0 := not_lt_of_ge (le_trans a_spec.1.le ht.le)
    have hnot_a : ¬ t < a := not_lt_of_ge ht.le
    rw [if_neg hnot_t0, if_neg hnot_a] at htail
    simpa [L] using htail
  have hIntConst0 : MeasureTheory.IntegrableOn (fun _ : Real => 1 - p0) (Set.Ioc 0 t0) := by
    exact MeasureTheory.integrableOn_const
      (measure_Ioc_lt_top (μ := (volume : Measure Real)) (a := (0 : Real)) (b := t0)).ne
  have hIntConst1 : MeasureTheory.IntegrableOn (fun _ : Real => p0) (Set.Ioc t0 a) := by
    exact MeasureTheory.integrableOn_const
      (measure_Ioc_lt_top (μ := (volume : Measure Real)) (a := t0) (b := a)).ne
  have hIntS0 : MeasureTheory.IntegrableOn s (Set.Ioc 0 t0) := hs_cont.integrableOn_Ioc
  have hIntS1 : MeasureTheory.IntegrableOn s (Set.Ioc t0 a) := hs_cont.integrableOn_Ioc
  have hIntL0 : MeasureTheory.IntegrableOn L (Set.Ioc 0 t0) := by
    exact hIntConst0.congr_fun hEqL0.symm measurableSet_Ioc
  have hIntL1 : MeasureTheory.IntegrableOn L (Set.Ioc t0 a) := by
    have hIntS1Sub : MeasureTheory.IntegrableOn (fun t : Real => s t - p0) (Set.Ioc t0 a) := by
      exact hIntS1.sub hIntConst1
    exact hIntS1Sub.congr_fun hEqL1.symm measurableSet_Ioc
  have hIntL2 : MeasureTheory.IntegrableOn L (Set.Ioi a) := by
    exact (MeasureTheory.integrableOn_zero).congr_fun hEqL2.symm measurableSet_Ioi
  have hIntLt0 : MeasureTheory.IntegrableOn L (Set.Ioi t0) := by
    have hIntLt0' : MeasureTheory.IntegrableOn L (Set.Ioc t0 a ∪ Set.Ioi a) := by
      exact (MeasureTheory.integrableOn_union).2 ⟨hIntL1, hIntL2⟩
    simpa [Set.Ioc_union_Ioi_eq_Ioi a_spec.1.le] using hIntLt0'
  have hsplit0 :
      ∫ t in Set.Ioi 0, L t ∂volume =
        (∫ t in Set.Ioc 0 t0, L t ∂volume) + (∫ t in Set.Ioi t0, L t ∂volume) := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIntL0 hIntLt0]
    rw [Set.Ioc_union_Ioi_eq_Ioi t0_pos.le]
  have hsplit1 :
      ∫ t in Set.Ioi t0, L t ∂volume =
        (∫ t in Set.Ioc t0 a, L t ∂volume) + (∫ t in Set.Ioi a, L t ∂volume) := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIntL1 hIntL2]
    rw [Set.Ioc_union_Ioi_eq_Ioi a_spec.1.le]
  have hL0 :
      ∫ t in Set.Ioc 0 t0, L t ∂volume = (1 - p0) * t0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hEqL0]
    simp [MeasureTheory.integral_const, smul_eq_mul, t0_pos.le, mul_comm]
  have hL1 :
      ∫ t in Set.Ioc t0 a, L t ∂volume =
        (∫ t in Set.Ioc t0 a, s t ∂volume) - p0 * (a - t0) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hEqL1]
    rw [MeasureTheory.integral_sub hIntS1 hIntConst1]
    have hConst :
        ∫ t in Set.Ioc t0 a, (fun _ : Real => p0) t ∂volume = p0 * (a - t0) := by
      simp [MeasureTheory.integral_const, smul_eq_mul, a_spec.1.le, mul_comm]
    rw [hConst]
  have hL2 : ∫ t in Set.Ioi a, L t ∂volume = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqL2]
    simp
  have hA_split0 :
      A = (∫ t in Set.Ioc 0 t0, s t ∂volume) + (∫ t in Set.Ioi t0, s t ∂volume) := by
    unfold A
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIntS0
      (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi t0_pos.le))]
    rw [Set.Ioc_union_Ioi_eq_Ioi t0_pos.le]
  have hA_split1 :
      (∫ t in Set.Ioi t0, s t ∂volume) =
        (∫ t in Set.Ioc t0 a, s t ∂volume) + (∫ t in Set.Ioi a, s t ∂volume) := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIntS1
      (s_integrableOn_Ioi_zero.mono_set (Set.Ioi_subset_Ioi (le_of_lt (lt_trans t0_pos a_spec.1))))]
    rw [Set.Ioc_union_Ioi_eq_Ioi a_spec.1.le]
  have hS0_eq :
      ∫ t in Set.Ioc 0 t0, s t ∂volume = t0 := by
    have hEqS0 : Set.EqOn s (fun _ : Real => 1) (Set.Ioc 0 t0) := by
      intro t ht
      by_cases htt : t < t0
      · exact s_eq_one_of_nonneg_lt_t0 ht.1.le htt
      · have hteq : t = t0 := le_antisymm ht.2 (le_of_not_gt htt)
        subst hteq
        unfold s
        rw [two_exp_neg_t0_sq_div_two_eq_one]
        simp
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hEqS0]
    simp [MeasureTheory.integral_const, smul_eq_mul, t0_pos.le]
  have hA_split :
      A = t0 + (∫ t in Set.Ioc t0 a, s t ∂volume) + (∫ t in Set.Ioi a, s t ∂volume) := by
    rw [hA_split0, hA_split1, hS0_eq]
    ring
  have hB_form : B = p0 * a + ∫ t in Set.Ioi a, s t ∂volume := by
    have hHa : H a = B := a_spec.2
    have hHa' : B = a * s a + ∫ t in Set.Ioi a, s t ∂volume := by
      simpa [H] using hHa.symm
    simpa [p0, mul_comm] using hHa'
  calc
    ∫ t in Set.Ioi 0, prob muStar {x : Real | x < -t} ∂volume
        = ∫ t in Set.Ioi 0, L t ∂volume := rfl
    _ = (∫ t in Set.Ioc 0 t0, L t ∂volume) + (∫ t in Set.Ioi t0, L t ∂volume) := hsplit0
    _ = (∫ t in Set.Ioc 0 t0, L t ∂volume) +
          ((∫ t in Set.Ioc t0 a, L t ∂volume) + (∫ t in Set.Ioi a, L t ∂volume)) := by
            rw [hsplit1]
    _ = ((1 - p0) * t0) + ((∫ t in Set.Ioc t0 a, s t ∂volume) - p0 * (a - t0) + 0) := by
          rw [hL0, hL1, hL2]
    _ = (t0 + (∫ t in Set.Ioc t0 a, s t ∂volume)) - p0 * a := by ring
    _ = A - (p0 * a + ∫ t in Set.Ioi a, s t ∂volume) := by
          linarith [hA_split]
    _ = A - B := by rw [hB_form]
    _ = B := by
          unfold B
          ring

theorem mean_muStar : mean muStar = 0 := by
  letI : IsProbabilityMeasure muStar := muStar_isProbability
  have hIntId : Integrable (fun x : Real => x) muStar := integrable_id_muStar
  have hIntAbs : Integrable (fun x : Real => |x|) muStar := hIntId.norm
  have hIntPos : Integrable (fun x : Real => hinge 0 x) muStar := by
    refine MeasureTheory.Integrable.mono' hIntAbs
      ((Measurable.max (measurable_id.sub_const 0) measurable_const).aestronglyMeasurable) ?_
    filter_upwards with x
    have hnonneg : 0 ≤ hinge 0 x := hinge_nonneg 0 x
    have hle : hinge 0 x ≤ |x| := by
      unfold hinge posPart
      refine max_le ?_ (abs_nonneg x)
      simpa using (le_abs_self x)
    calc
      ‖hinge 0 x‖ = hinge 0 x := by
        simp [Real.norm_eq_abs]
      _ ≤ |x| := hle
  have hIntNeg : Integrable (fun x : Real => hinge 0 (-x)) muStar := by
    refine MeasureTheory.Integrable.mono' hIntAbs
      ((Measurable.max ((Measurable.neg measurable_id).sub_const 0) measurable_const).aestronglyMeasurable) ?_
    filter_upwards with x
    have hnonneg : 0 ≤ hinge 0 (-x) := hinge_nonneg 0 (-x)
    have hle : hinge 0 (-x) ≤ |x| := by
      unfold hinge posPart
      refine max_le ?_ (abs_nonneg x)
      simpa using (neg_le_abs x)
    calc
      ‖hinge 0 (-x)‖ = hinge 0 (-x) := by
        simp [Real.norm_eq_abs]
      _ ≤ |x| := hle
  have hsplit_id : ∀ x : Real, x = hinge 0 x - hinge 0 (-x) := by
    intro x
    by_cases hnonneg : 0 ≤ x
    · have hneg_nonpos : -x ≤ 0 := by linarith
      simp [hinge, posPart, hnonneg, hneg_nonpos]
    · have hxlt : x < 0 := lt_of_not_ge hnonneg
      have hneg_nonneg : 0 ≤ -x := by linarith
      simp [hinge, posPart, hneg_nonneg, hxlt.le]
  have hmean_split :
      mean muStar = (∫ x, hinge 0 x ∂muStar) - (∫ x, hinge 0 (-x) ∂muStar) := by
    unfold mean
    calc
      ∫ x, x ∂muStar = ∫ x, (hinge 0 x - hinge 0 (-x)) ∂muStar := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall hsplit_id
      _ = (∫ x, hinge 0 x ∂muStar) - (∫ x, hinge 0 (-x) ∂muStar) := by
        exact MeasureTheory.integral_sub hIntPos hIntNeg
  have hpos_B : ∫ x, hinge 0 x ∂muStar = B := by
    have hSL0 : stopLoss muStar 0 = J 0 := stopLoss_muStar_eq_J 0 (by norm_num)
    have hJ0 : J 0 = B := by
      have h0a : (0 : Real) ≤ a := le_trans t0_pos.le a_spec.1.le
      simp [J_of_le_a h0a]
    simpa [stopLoss] using hSL0.trans hJ0
  have hneg_tail0 :
      ∫ x, hinge 0 (-x) ∂muStar =
        ∫ t in Set.Ioi 0, prob muStar {x : Real | -x > t} ∂volume := by
    simpa [prob] using
      (layer_cake_hinge (P := muStar) (Y := fun x : Real => -x) hIntId.neg 0)
  have hneg_tail :
      ∫ x, hinge 0 (-x) ∂muStar =
        ∫ t in Set.Ioi 0, prob muStar {x : Real | x < -t} ∂volume := by
    rw [hneg_tail0]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hset : {x : Real | -x > t} = {x : Real | x < -t} := by
      ext x
      constructor
      · intro hx
        simp at hx
        have hx' : -x > t := hx
        simp
        linarith
      · intro hx
        simp at hx
        have hx' : x < -t := hx
        simp
        linarith
    simp [hset]
  have hneg_B : ∫ x, hinge 0 (-x) ∂muStar = B := by
    rw [hneg_tail, integral_leftTail_muStar_eq_B]
  linarith [hmean_split, hpos_B, hneg_B]

theorem exists_extremal_measure :
    ∃ (muStar : Measure Real), IsProbabilityMeasure muStar ∧
      mean muStar = 0 ∧
      (∀ t : Real, 0 <= t → absTail muStar t = s t) ∧
      (∀ u : Real, 0 <= u → stopLoss muStar u = J u) := by
  refine ⟨muStar, muStar_isProbability, mean_muStar, absTail_muStar_eq_s, stopLoss_muStar_eq_J⟩

theorem optimality_c0 :
    (∀ (c : Real), 0 < c → c < c0 →
      ∃ (muStar : Measure Real), IsProbabilityMeasure muStar ∧
        mean muStar = 0 ∧
        subgaussianTail muStar ∧
        ∃ (u : Real), stopLoss muStar u > stopLoss (gaussianScale c) u) := by
  intro c hc0 hc_lt
  obtain ⟨muStar0, hP, hmean0, hTailEq, hSL_nonneg⟩ := exists_extremal_measure
  refine ⟨muStar0, hP, hmean0, ?_, ?_⟩
  · intro t ht
    rw [hTailEq t ht]
    unfold s
    exact min_le_right _ _
  · let u : Real := c * z
    have hu_nonneg : 0 <= u := mul_nonneg hc0.le z_nonneg
    have hSLu : stopLoss muStar0 u = J u := hSL_nonneg u hu_nonneg
    have hJlb : B - p0 * u <= J u := J_ge_tangent_line u hu_nonneg
    have hGauss : stopLoss (gaussianScale c) u = gClosed c u := by
      simpa [gSL] using gSL_eq_gClosed c u hc0
    have hu_div : u / c = z := by
      unfold u
      field_simp [hc0.ne']
    have hEval : gClosed c u = c * phi z - u * p0 := by
      unfold gClosed
      rw [hu_div, z_spec]
    have hphi_pos : 0 < phi z := phi_pos z
    have hB_eq : c0 * phi z = B := by
      unfold c0
      field_simp [hphi_pos.ne']
    have hB_gt : B - c * phi z > 0 := by
      have hcphi : c * phi z < c0 * phi z := mul_lt_mul_of_pos_right hc_lt hphi_pos
      linarith [hcphi, hB_eq]
    refine ⟨u, ?_⟩
    calc
      stopLoss muStar0 u = J u := hSLu
      _ >= B - p0 * u := hJlb
      _ > c * phi z - u * p0 := by linarith [hB_gt]
      _ = gClosed c u := hEval.symm
      _ = stopLoss (gaussianScale c) u := hGauss.symm


/-! ## Main Convex-Domination Pipeline (Grouped API) -/

theorem stopLossDom_c0
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0) :
    StopLossDom mu (gaussianScale c0) := by
  refine ⟨?_, ?_⟩
  · simp [hmean, mean_gaussianScale c0]
  · intro u
    letI : IsProbabilityMeasure (gaussianScale c0) := gaussianScale_isProbability c0
    have hs_pos : ∀ t : Real, 0 < s t := by
      intro t
      unfold s
      exact lt_min zero_lt_one (mul_pos zero_lt_two (Real.exp_pos _))
    have ht0_pos : 0 < t0 := by
      unfold t0
      refine Real.sqrt_pos.mpr ?_
      positivity
    have ha_pos : 0 < a := lt_trans ht0_pos a_spec.1
    have h_tail_nonneg : 0 <= ∫ t in Set.Ioi a, s t ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_nonneg ?_
      intro t
      exact (hs_pos t).le
    have hHapos : 0 < H a := by
      unfold H
      nlinarith [ha_pos, hs_pos a, h_tail_nonneg]
    have hB_pos : 0 < B := by
      simpa [a_spec.2] using hHapos
    have hphi_pos : 0 < phi z := by
      unfold phi
      positivity
    have hc0 : 0 < c0 := by
      unfold c0
      exact div_pos hB_pos hphi_pos
    have hEnv := stopLoss_envelope (mu := mu) hIntMuId htail hmean
    have hPos_nonneg : ∀ v : Real, 0 <= v → stopLoss mu v <= stopLoss (gaussianScale c0) v := by
      intro v hv
      calc
        stopLoss mu v <= J v := hEnv.1 v hv
        _ <= gClosed c0 v := gaussian_dominates_J v hv
        _ = stopLoss (gaussianScale c0) v := (gSL_eq_gClosed c0 v hc0).symm
    have hgauss_reflect : Measure.map (fun x : Real => -x) (gaussianScale c0) = gaussianScale c0 := by
      let sigma : NNReal := (⟨c0 ^ 2, sq_nonneg c0⟩ * (1 : NNReal))
      have hscale : gaussianScale c0 = ProbabilityTheory.gaussianReal 0 sigma := by
        unfold gaussianScale gaussianMeasure sigma
        simpa [zero_mul] using
          (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : Real)) (v := (1 : NNReal)) (c := c0))
      calc
        Measure.map (fun x : Real => -x) (gaussianScale c0)
            = Measure.map (fun x : Real => -x) (ProbabilityTheory.gaussianReal 0 sigma) := by
              rw [hscale]
        _ = ProbabilityTheory.gaussianReal (-0) sigma := by
              simpa using (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : Real)) (v := sigma))
        _ = gaussianScale c0 := by
              simpa using hscale.symm
    have hNeg_nonneg :
        ∀ v : Real, 0 <= v →
          stopLoss (Measure.map (fun x : Real => -x) mu) v <=
            stopLoss (Measure.map (fun x : Real => -x) (gaussianScale c0)) v := by
      intro v hv
      calc
        stopLoss (Measure.map (fun x : Real => -x) mu) v <= J v := hEnv.2 v hv
        _ <= gClosed c0 v := gaussian_dominates_J v hv
        _ = stopLoss (gaussianScale c0) v := (gSL_eq_gClosed c0 v hc0).symm
        _ = stopLoss (Measure.map (fun x : Real => -x) (gaussianScale c0)) v := by
          simp [hgauss_reflect]
    have hAll :
        ∀ v : Real, stopLoss mu v <= stopLoss (gaussianScale c0) v :=
      stopLoss_extend_all_u (mu := mu) (nu := gaussianScale c0)
        hIntMuId
        (by
          let sigma : NNReal := (⟨c0 ^ 2, sq_nonneg c0⟩ * (1 : NNReal))
          have hscale : gaussianScale c0 = ProbabilityTheory.gaussianReal 0 sigma := by
            unfold gaussianScale gaussianMeasure sigma
            simpa [zero_mul] using
              (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : Real)) (v := (1 : NNReal))
                (c := c0))
          rw [hscale]
          simpa using
            (ProbabilityTheory.IsGaussian.integrable_fun_id
              (μ := ProbabilityTheory.gaussianReal 0 sigma)))
        (by simp [hmean, mean_gaussianScale c0])
        hPos_nonneg hNeg_nonneg
    exact hAll u

theorem convexDomination_c0
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0)
    {f : Real → Real} (hf : IsSimpleConvex f)
    (hmu : Integrable f mu) (hG : Integrable f (gaussianScale c0)) :
    (∫ x, f x ∂mu) <= (∫ x, f x ∂(gaussianScale c0)) := by
  letI : IsProbabilityMeasure (gaussianScale c0) := gaussianScale_isProbability c0
  have hDom : StopLossDom mu (gaussianScale c0) := stopLossDom_c0 (mu := mu) hIntMuId htail hmean
  exact stopLossDom_integral_convex hDom hf hIntMuId
    (by
      let sigma : NNReal := (⟨c0 ^ 2, sq_nonneg c0⟩ * (1 : NNReal))
      have hscale : gaussianScale c0 = ProbabilityTheory.gaussianReal 0 sigma := by
        unfold gaussianScale gaussianMeasure sigma
        simpa [zero_mul] using
          (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : Real)) (v := (1 : NNReal))
            (c := c0))
      rw [hscale]
      simpa using
        (ProbabilityTheory.IsGaussian.integrable_fun_id
          (μ := ProbabilityTheory.gaussianReal 0 sigma)))
    hmu hG

/-- Simple-convex endpoint at scale `c0` (renamed interface). -/
theorem convexDomination_c0_simple
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0)
    {f : Real → Real} (hf : IsSimpleConvex f)
    (hmu : Integrable f mu) (hG : Integrable f (gaussianScale c0)) :
    (∫ x, f x ∂mu) <= (∫ x, f x ∂(gaussianScale c0)) :=
  convexDomination_c0 hIntMuId htail hmean hf hmu hG

/--
The only remaining missing ingredient for full convex domination:
reduce an arbitrary convex integrand to the simple-convex case.
-/
lemma simpleConvex_integrable
    {mu : Measure Real} [IsFiniteMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    {f : Real → Real} (hf : IsSimpleConvex f) :
    Integrable f mu := by
  rcases hf with ⟨a, b, s, w, hw, hrepr⟩
  have hpsi : ∀ u : Real, Integrable (fun x : Real => psi u x) mu := by
    intro u
    unfold psi
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (MeasureTheory.Integrable.pos_part (hIntMuId.sub (MeasureTheory.integrable_const u)))
  have hsum :
      Integrable (fun x : Real => Finset.sum s (fun u => w u * psi u x)) mu := by
    refine MeasureTheory.integrable_finset_sum _ ?_
    intro u hu
    exact (hpsi u).const_mul (w u)
  have hrepr' : f = fun x => a * x + b + Finset.sum s (fun u => w u * psi u x) := by
    funext x
    exact hrepr x
  rw [hrepr']
  exact (hIntMuId.const_mul a).add (MeasureTheory.integrable_const b) |>.add hsum

lemma gaussianScale_integrable_id (c : Real) :
    Integrable (fun x : Real => x) (gaussianScale c) := by
  let sigma : NNReal := (⟨c ^ 2, sq_nonneg c⟩ * (1 : NNReal))
  have hscale : gaussianScale c = ProbabilityTheory.gaussianReal 0 sigma := by
    unfold gaussianScale gaussianMeasure sigma
    simpa [zero_mul] using
      (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : Real)) (v := (1 : NNReal))
        (c := c))
  rw [hscale]
  simpa using
    (ProbabilityTheory.IsGaussian.integrable_fun_id
      (μ := ProbabilityTheory.gaussianReal 0 sigma))

set_option linter.unusedSimpArgs false

/-! ## Aristotle finite max-affine proof (in-file) -/

/--
In-file Aristotle proof: MaxAffineIsSimpleStatement.psi through max_affine_is_simple.
Transport to this file's `IsSimpleConvex`/`psi` via the bridge theorem below.
-/

def MaxAffineIsSimpleStatement.psi (u x : Real) : Real := max (x - u) 0

def MaxAffineIsSimpleStatement.IsSimpleConvex (f : Real → Real) : Prop :=
  ∃ (a b : Real) (s : Finset Real) (w : Real → Real),
    (∀ u ∈ s, 0 ≤ w u) ∧
    ∀ x, f x = a * x + b + Finset.sum s (fun u => w u * MaxAffineIsSimpleStatement.psi u x)

lemma MaxAffineIsSimpleStatement.IsSimpleConvex_affine (a b : Real) : MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => a * x + b) := by
  use a, b, ∅, fun _ => 0; simp [MaxAffineIsSimpleStatement.IsSimpleConvex]

lemma MaxAffineIsSimpleStatement.IsSimpleConvex_add {f g : Real → Real} (hf : MaxAffineIsSimpleStatement.IsSimpleConvex f) (hg : MaxAffineIsSimpleStatement.IsSimpleConvex g) : MaxAffineIsSimpleStatement.IsSimpleConvex (f + g) := by
  obtain ⟨ a₁, b₁, s₁, w₁, hw₁, hf ⟩ := hf
  obtain ⟨ a₂, b₂, s₂, w₂, hw₂, hg ⟩ := hg
  use a₁ + a₂, b₁ + b₂, s₁ ∪ s₂, fun u => (if u ∈ s₁ then w₁ u else 0) + (if u ∈ s₂ then w₂ u else 0)
  simp_all +decide [Finset.sum_union];
  constructor;
  · bound;
  · simp +decide [ add_mul, Finset.sum_add_distrib, Finset.sum_union ];
    exact fun x => by ring_nf;

lemma MaxAffineIsSimpleStatement.max_affine_pair_is_simple (a b c d : Real) : MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => max (a * x + b) (c * x + d)) := by
  by_cases h : a = c;
  · have h_affine : MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => a * x + max b d) := by
      exact MaxAffineIsSimpleStatement.IsSimpleConvex_affine a (max b d)
    grind;
  · obtain ⟨u, hu⟩ : ∃ u : ℝ, a * u + b = c * u + d := by
      exact ⟨ ( d - b ) / ( a - c ), by linarith [ mul_div_cancel₀ ( d - b ) ( sub_ne_zero_of_ne h ) ] ⟩;
    by_cases h_pos : a - c > 0;
    · use c, d, { u }, fun v => if v = u then a - c else 0;
      simp [hu];
      exact ⟨ by linarith, fun x => by unfold MaxAffineIsSimpleStatement.psi; cases max_cases ( a * x + b ) ( c * x + d ) <;> cases max_cases ( x - u ) 0 <;> nlinarith ⟩;
    · set w : ℝ := c - a
      have hw_pos : 0 < w := by
        exact sub_pos.mpr ( lt_of_le_of_ne ( by linarith ) h );
      have h_max : ∀ x, max (a * x + b) (c * x + d) = a * x + b + w * max (x - u) 0 := by
        intro x; rw [ max_def, max_def ] ; split_ifs <;> nlinarith;
      use a, b, {u}, fun _ => w; aesop;

lemma MaxAffineIsSimpleStatement.IsSimpleConvex_add_affine {f : Real → Real} (hf : MaxAffineIsSimpleStatement.IsSimpleConvex f) (a b : Real) : MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => f x + (a * x + b)) := by
  apply MaxAffineIsSimpleStatement.IsSimpleConvex_add hf (MaxAffineIsSimpleStatement.IsSimpleConvex_affine a b)

lemma MaxAffineIsSimpleStatement.IsSimpleConvex_induction
    {P : (Real → Real) → Prop}
    (h_affine : ∀ a b, P (fun x => a * x + b))
    (h_add_hinge : ∀ f u w, P f → 0 ≤ w → P (fun x => f x + w * MaxAffineIsSimpleStatement.psi u x)) :
    ∀ f, MaxAffineIsSimpleStatement.IsSimpleConvex f → P f := by
      have h_induction : ∀ (n : ℕ) (a b : ℝ) (s : Finset ℝ) (w : ℝ → ℝ), (∀ u ∈ s, 0 ≤ w u) → s.card = n → P (fun x => a * x + b + Finset.sum s (fun u => w u * (max (x - u) 0))) := by
        intro n
        induction' n with n ih;
        · aesop;
        · intro a b s w hw hs
          obtain ⟨u, hu⟩ : ∃ u ∈ s, True := by
            exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, trivial ⟩;
          convert h_add_hinge ( fun x => a * x + b + ∑ u ∈ s.erase u, w u * Max.max ( x - u ) 0 ) u ( w u ) ( ih a b ( s.erase u ) w ( fun v hv => hw v ( Finset.mem_of_mem_erase hv ) ) ( by rw [ Finset.card_erase_of_mem hu.1, hs ] ; simp +decide ) ) ( hw u hu.1 ) using 1 ; simp +decide [ Finset.sum_erase, hu.1 ] ; ring_nf;
          exact funext fun x => by rw [ show MaxAffineIsSimpleStatement.psi u x = Max.max ( x - u ) 0 by rfl ] ; ring_nf;
      intro f hf
      obtain ⟨a, b, s, w, hw_nonneg, hf_eq⟩ := hf;
      convert h_induction s.card a b s w hw_nonneg rfl using 1 ; ext x ; rw [ hf_eq ] ; rfl;

def MaxAffineIsSimpleStatement.slope_left (a : Real) (s : Finset Real) (w : Real → Real) (x : Real) : Real :=
  a + s.sum (fun v => if v < x then w v else 0)

def MaxAffineIsSimpleStatement.slope_right (a : Real) (s : Finset Real) (w : Real → Real) (x : Real) : Real :=
  a + s.sum (fun v => if v ≤ x then w v else 0)

def MaxAffineIsSimpleStatement.glue_s (s t : Finset Real) (u : Real) : Finset Real :=
  (s.filter (fun v => v < u)) ∪ (t.filter (fun v => v > u)) ∪ {u}

def MaxAffineIsSimpleStatement.glue_w (s t : Finset Real) (w z : Real → Real) (u a c : Real) (v : Real) : Real :=
  if v < u then w v
  else if v > u then z v
  else (c + t.sum (fun k => if k ≤ u then z k else 0)) - (a + s.sum (fun k => if k < u then w k else 0))

lemma MaxAffineIsSimpleStatement.glue_w_nonneg (s t : Finset Real) (w z : Real → Real) (u a b c d : Real)
  (hw : ∀ v ∈ s, 0 ≤ w v)
  (hz : ∀ v ∈ t, 0 ≤ z v)
  (f : Real → Real) (hf : ∀ x, f x = a * x + b + s.sum (fun v => w v * MaxAffineIsSimpleStatement.psi v x))
  (g : Real → Real) (hg : ∀ x, g x = c * x + d + t.sum (fun v => z v * MaxAffineIsSimpleStatement.psi v x))
  (h_eq : f u = g u)
  (h_le : ∀ x ≤ u, g x ≤ f x)
  (h_ge : ∀ x ≥ u, f x ≤ g x) :
  ∀ v ∈ MaxAffineIsSimpleStatement.glue_s s t u, 0 ≤ MaxAffineIsSimpleStatement.glue_w s t w z u a c v := by
    intro v hv
    simp [MaxAffineIsSimpleStatement.glue_w];
    split_ifs;
    · have hv_s_or_t : v ∈ s ∨ v ∈ t := by
        unfold MaxAffineIsSimpleStatement.glue_s at hv; aesop;
      cases hv_s_or_t <;> simp_all +decide [ MaxAffineIsSimpleStatement.glue_s ];
      grind;
    · unfold MaxAffineIsSimpleStatement.glue_s at hv; aesop;
    · have h_slope_right : ∀ ε > 0, f (u + ε) - f u = (a + ∑ k ∈ s, if k < u then w k else 0) * ε + ∑ k ∈ s, if k ≥ u then w k * max (ε - (k - u)) 0 else 0 := by
        intro ε hε; rw [ hf, hf ] ; simp +decide [ mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, MaxAffineIsSimpleStatement.psi ] ; ring_nf;
        rw [ ← Finset.sum_sub_distrib ] ; rw [ add_assoc ] ; rw [ ← Finset.sum_add_distrib ] ; refine' congr_arg _ ( Finset.sum_congr rfl fun x hx => _ ) ; split_ifs <;> cases max_cases ( u + ( ε - x ) ) 0 <;> cases max_cases ( u - x ) 0 <;> nlinarith [ hw x hx ] ;
      have h_slope_right : ∀ ε > 0, g (u + ε) - g u = (c + ∑ k ∈ t, if k ≤ u then z k else 0) * ε + ∑ k ∈ t, if k > u then z k * max (ε - (k - u)) 0 else 0 := by
        intro ε hε_pos
        simp [hg, MaxAffineIsSimpleStatement.psi];
        simp +decide [ add_mul, Finset.sum_add_distrib, Finset.sum_mul _ _ _, sub_mul, mul_sub, max_def' ] ; ring_nf;
        simp +decide [ add_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg ];
        rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; split_ifs <;> linarith;
      contrapose! h_ge;
      obtain ⟨ε, hε_pos, hε_small⟩ : ∃ ε > 0, ∀ k ∈ t, k > u → ε < k - u := by
        by_cases ht_empty : t.filter (fun k => k > u) = ∅;
        · exact ⟨ 1, zero_lt_one, fun k hk hk' => False.elim <| Finset.notMem_empty k <| ht_empty ▸ Finset.mem_filter.mpr ⟨ hk, hk' ⟩ ⟩;
        · obtain ⟨k, hk⟩ : ∃ k ∈ t.filter (fun k => k > u), ∀ j ∈ t.filter (fun k => k > u), k ≤ j := by
            exact ⟨ Finset.min' _ <| Finset.nonempty_of_ne_empty ht_empty, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj ⟩;
          exact ⟨ ( k - u ) / 2, half_pos ( sub_pos.mpr ( Finset.mem_filter.mp hk.1 |>.2 ) ), fun j hj hj' => by linarith [ hk.2 j ( Finset.mem_filter.mpr ⟨ hj, hj' ⟩ ) ] ⟩;
      use u + ε;
      simp_all +decide [ Finset.sum_ite ];
      have h_sum_zero : ∑ x ∈ t with u < x, z x * Max.max (ε - (x - u)) 0 = 0 := by
        exact Finset.sum_eq_zero fun x hx => by rw [ max_eq_right ( by linarith [ hε_small x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) ] ) ] ; ring_nf;
      exact ⟨ hε_pos.le, by nlinarith [ h_slope_right ε hε_pos, ‹∀ ε : ℝ, 0 < ε → a * ( u + ε ) + b + ∑ v ∈ s, w v * MaxAffineIsSimpleStatement.psi v ( u + ε ) - ( c * u + d + ∑ v ∈ t, z v * MaxAffineIsSimpleStatement.psi v u ) = ( a + ∑ x ∈ s with x < u, w x ) * ε + ∑ x ∈ s with u ≤ x, w x * Max.max ( ε - ( x - u ) ) 0› ε hε_pos, show 0 ≤ ∑ x ∈ s with u ≤ x, w x * Max.max ( ε - ( x - u ) ) 0 from Finset.sum_nonneg fun x hx => mul_nonneg ( hw x <| Finset.mem_filter.mp hx |>.1 ) ( le_max_right _ _ ) ] ⟩

lemma MaxAffineIsSimpleStatement.glue_eq (s t : Finset Real) (w z : Real → Real) (u a b c d : Real)
  (f : Real → Real) (hf : ∀ x, f x = a * x + b + s.sum (fun v => w v * MaxAffineIsSimpleStatement.psi v x))
  (g : Real → Real) (hg : ∀ x, g x = c * x + d + t.sum (fun v => z v * MaxAffineIsSimpleStatement.psi v x))
  (h_eq : f u = g u) :
  ∀ x, (if x ≤ u then f x else g x) =
    a * x + b + (MaxAffineIsSimpleStatement.glue_s s t u).sum (fun v => MaxAffineIsSimpleStatement.glue_w s t w z u a c v * MaxAffineIsSimpleStatement.psi v x) := by
      intro x
      by_cases hx : x ≤ u;
      · rw [ show MaxAffineIsSimpleStatement.glue_s s t u = ( s.filter ( fun v => v < u ) ) ∪ ( t.filter ( fun v => v > u ) ) ∪ { u } by rfl, Finset.sum_union, Finset.sum_union ] <;> norm_num [ Finset.sum_filter, MaxAffineIsSimpleStatement.glue_w ];
        · unfold MaxAffineIsSimpleStatement.psi at *;
          simp_all +decide [ Finset.sum_ite, hx ];
          rw [ ← Finset.sum_subset ( show s.filter ( fun v => v < u ) ⊆ s from Finset.filter_subset _ _ ) ];
          · simp +decide [ Finset.sum_filter, not_lt_of_ge hx ];
            have h_zero : ∀ a ∈ t, (if u < a then if a < u then w a * Max.max (x - a) 0 else 0 else 0) = 0 ∧ (if u < a then if u ≤ a then z a * Max.max (x - a) 0 else 0 else 0) = 0 := by
              intro a ha; split_ifs <;> norm_num ; linarith;
              · linarith;
              · exact Or.inr ( by linarith );
            rw [ Finset.sum_eq_zero fun x hx => h_zero x hx |>.1, Finset.sum_eq_zero fun x hx => h_zero x hx |>.2, zero_add ];
          · grind;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_filter.mp hx₁, Finset.mem_filter.mp hx₂ ] ;
      · have h_split : ∑ v ∈ MaxAffineIsSimpleStatement.glue_s s t u, MaxAffineIsSimpleStatement.glue_w s t w z u a c v * MaxAffineIsSimpleStatement.psi v x = ∑ v ∈ s.filter (fun v => v < u), w v * MaxAffineIsSimpleStatement.psi v x + ∑ v ∈ t.filter (fun v => v > u), z v * MaxAffineIsSimpleStatement.psi v x + (c + t.sum (fun k => if k ≤ u then z k else 0)) * MaxAffineIsSimpleStatement.psi u x - (a + s.sum (fun k => if k < u then w k else 0)) * MaxAffineIsSimpleStatement.psi u x := by
          have h_split : ∑ v ∈ MaxAffineIsSimpleStatement.glue_s s t u, MaxAffineIsSimpleStatement.glue_w s t w z u a c v * MaxAffineIsSimpleStatement.psi v x = ∑ v ∈ s.filter (fun v => v < u), w v * MaxAffineIsSimpleStatement.psi v x + ∑ v ∈ t.filter (fun v => v > u), z v * MaxAffineIsSimpleStatement.psi v x + MaxAffineIsSimpleStatement.glue_w s t w z u a c u * MaxAffineIsSimpleStatement.psi u x := by
            have h_expand : ∑ v ∈ MaxAffineIsSimpleStatement.glue_s s t u, MaxAffineIsSimpleStatement.glue_w s t w z u a c v * MaxAffineIsSimpleStatement.psi v x = ∑ v ∈ (s.filter (fun v => v < u)) ∪ (t.filter (fun v => v > u)), MaxAffineIsSimpleStatement.glue_w s t w z u a c v * MaxAffineIsSimpleStatement.psi v x + MaxAffineIsSimpleStatement.glue_w s t w z u a c u * MaxAffineIsSimpleStatement.psi u x := by
              rw [ show MaxAffineIsSimpleStatement.glue_s s t u = ( s.filter ( fun v => v < u ) ) ∪ ( t.filter ( fun v => v > u ) ) ∪ { u } by rfl, Finset.sum_union ] <;> norm_num;
            rw [ h_expand, Finset.sum_union ];
            · congr! 2;
              · refine' Finset.sum_congr rfl fun v hv => _;
                unfold MaxAffineIsSimpleStatement.glue_w; aesop;
              · refine' Finset.sum_congr rfl fun v hv => _;
                simp [MaxAffineIsSimpleStatement.glue_w, hv];
                rw [ if_neg ( by linarith [ Finset.mem_filter.mp hv ] ), if_pos ( by linarith [ Finset.mem_filter.mp hv ] ) ];
            · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_filter.mp hx₁, Finset.mem_filter.mp hx₂ ] ;
          convert h_split using 1;
          unfold MaxAffineIsSimpleStatement.glue_w; simp +decide [ Finset.sum_ite ] ; ring_nf;
        have h_g_simplified : g x = c * x + d + ∑ v ∈ t.filter (fun v => v > u), z v * MaxAffineIsSimpleStatement.psi v x + ∑ v ∈ t.filter (fun v => v ≤ u), z v * MaxAffineIsSimpleStatement.psi v x := by
          simp +decide [ hg, Finset.sum_filter, add_assoc ];
          simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by split_ifs <;> linarith;
        simp_all +decide [ Finset.sum_ite ];
        rw [ if_neg (not_le_of_gt hx) ] ; ring_nf;
        unfold MaxAffineIsSimpleStatement.psi at *;
        rw [ max_eq_left ( by linarith ) ] at *;
        rw [ show ∑ v ∈ t, z v * Max.max ( u - v ) 0 = ∑ v ∈ t with v ≤ u, z v * Max.max ( u - v ) 0 from ?_, show ∑ v ∈ s, w v * Max.max ( u - v ) 0 = ∑ v ∈ s with v < u, w v * Max.max ( u - v ) 0 from ?_ ] at h_eq;
        · rw [ show ∑ v ∈ t with v ≤ u, z v * Max.max ( x - v ) 0 = ∑ v ∈ t with v ≤ u, z v * ( x - u ) + ∑ v ∈ t with v ≤ u, z v * Max.max ( u - v ) 0 from ?_ ];
          · rw [ show ∑ v ∈ s with v < u, w v * Max.max ( x - v ) 0 = ∑ v ∈ s with v < u, w v * ( x - u ) + ∑ v ∈ s with v < u, w v * Max.max ( u - v ) 0 from ?_ ];
            · norm_num [ ← Finset.sum_mul _ _ _ ] at * ; linarith;
            · rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun v hv => _ ; rw [ max_def, max_def ] ; split_ifs <;> ring_nf;
              · linarith [ Finset.mem_filter.mp hv ];
              · linarith [ Finset.mem_filter.mp hv ];
              · linarith [ Finset.mem_filter.mp hv ];
          · rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun v hv => _ ; rw [ max_def, max_def ] ; split_ifs <;> ring_nf;
            · linarith [ Finset.mem_filter.mp hv ];
            · linarith [ Finset.mem_filter.mp hv ];
            · norm_num [ show v = u by linarith [ Finset.mem_filter.mp hv ] ];
        · rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
        · have h_zero : ∀ v ∈ t, v > u → z v * max (u - v) 0 = 0 := by
            exact fun v hv hv' => by rw [ max_eq_right ( by linarith ) ] ; ring_nf;
          rw [ Finset.sum_filter, Finset.sum_congr rfl ] ; aesop

lemma MaxAffineIsSimpleStatement.IsSimpleConvex_glue (f g : Real → Real) (u : Real)
    (hf : MaxAffineIsSimpleStatement.IsSimpleConvex f)
    (hg : MaxAffineIsSimpleStatement.IsSimpleConvex g)
    (h_eq : f u = g u)
    (h_le : ∀ x ≤ u, g x ≤ f x)
    (h_ge : ∀ x ≥ u, f x ≤ g x) :
    MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => if x ≤ u then f x else g x) := by
  obtain ⟨a, b, s, w, hw, hf_eq⟩ := hf
  obtain ⟨c, d, t, z, hz, hg_eq⟩ := hg
  use a, b, MaxAffineIsSimpleStatement.glue_s s t u, MaxAffineIsSimpleStatement.glue_w s t w z u a c
  constructor
  · apply MaxAffineIsSimpleStatement.glue_w_nonneg s t w z u a b c d hw hz f hf_eq g hg_eq h_eq h_le h_ge
  · apply MaxAffineIsSimpleStatement.glue_eq s t w z u a b c d f hf_eq g hg_eq h_eq

def MaxAffineIsSimpleStatement.flatten_s (s : Finset Real) (u v : Real) : Finset Real :=
  (s.filter (fun x => x ≤ u ∨ x ≥ v)) ∪ {u, v}

def MaxAffineIsSimpleStatement.flatten_w (s : Finset Real) (w : Real → Real) (u v : Real) (x : Real) : Real :=
  if x = u then (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (v - k) else 0)
  else if x = v then (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (k - u) else 0)
  else if u < x ∧ x < v then 0
  else w x

lemma MaxAffineIsSimpleStatement.flatten_w_nonneg (s : Finset Real) (w : Real → Real) (u v : Real)
  (hw : ∀ x ∈ s, 0 ≤ w x)
  (h_uv : u < v) :
  ∀ x ∈ MaxAffineIsSimpleStatement.flatten_s s u v, 0 ≤ MaxAffineIsSimpleStatement.flatten_w s w u v x := by
    intros x hx
    simp [MaxAffineIsSimpleStatement.flatten_w];
    split_ifs;
    · exact mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 h_uv.le ) ) ( Finset.sum_nonneg fun x hx => by split_ifs <;> nlinarith [ hw x hx ] );
    · exact mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 h_uv.le ) ) ( Finset.sum_nonneg fun x hx => by split_ifs <;> nlinarith [ hw x hx ] );
    · simp [le_refl];
    · unfold MaxAffineIsSimpleStatement.flatten_s at hx; aesop;

def MaxAffineIsSimpleStatement.flatten_w_v2 (s : Finset Real) (w : Real → Real) (u v : Real) (x : Real) : Real :=
  if x = u then w u + (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (v - k) else 0)
  else if x = v then w v + (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (k - u) else 0)
  else if u < x ∧ x < v then 0
  else w x

def MaxAffineIsSimpleStatement.flatten_w_v3 (s : Finset Real) (w : Real → Real) (u v : Real) (x : Real) : Real :=
  if x = u then (if u ∈ s then w u else 0) + (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (v - k) else 0)
  else if x = v then (if v ∈ s then w v else 0) + (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (k - u) else 0)
  else if u < x ∧ x < v then 0
  else w x

lemma MaxAffineIsSimpleStatement.flatten_w_v3_nonneg (s : Finset Real) (w : Real → Real) (u v : Real)
  (hw : ∀ x ∈ s, 0 ≤ w x)
  (h_uv : u < v) :
  ∀ x ∈ MaxAffineIsSimpleStatement.flatten_s s u v, 0 ≤ MaxAffineIsSimpleStatement.flatten_w_v3 s w u v x := by
    intros x hx
    simp [MaxAffineIsSimpleStatement.flatten_w_v3];
    split_ifs <;> norm_num [ h_uv.le ];
    · exact add_nonneg ( hw u ‹_› ) ( mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 h_uv.le ) ) ( Finset.sum_nonneg fun x hx => by split_ifs <;> nlinarith [ hw x hx, h_uv ] ) );
    · exact mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 h_uv.le ) ) ( Finset.sum_nonneg fun x hx => by split_ifs <;> nlinarith [ hw x hx ] );
    · exact add_nonneg ( hw _ ‹_› ) ( mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 h_uv.le ) ) ( Finset.sum_nonneg fun x hx => by split_ifs <;> nlinarith [ hw x hx ] ) );
    · exact mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 h_uv.le ) ) ( Finset.sum_nonneg fun x hx => by split_ifs <;> nlinarith [ hw x hx ] );
    · unfold MaxAffineIsSimpleStatement.flatten_s at hx; aesop;

def MaxAffineIsSimpleStatement.Cu (s : Finset Real) (w : Real → Real) (u v : Real) : Real :=
  (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (v - k) else 0)

def MaxAffineIsSimpleStatement.Cv (s : Finset Real) (w : Real → Real) (u v : Real) : Real :=
  (1 / (v - u)) * s.sum (fun k => if u < k ∧ k < v then w k * (k - u) else 0)

lemma MaxAffineIsSimpleStatement.Cu_add_Cv (s : Finset Real) (w : Real → Real) (u v : Real) (h_ne : u ≠ v) :
  MaxAffineIsSimpleStatement.Cu s w u v + MaxAffineIsSimpleStatement.Cv s w u v = s.sum (fun k => if u < k ∧ k < v then w k else 0) := by
    have h_combined : (1 / (v - u)) * (∑ k ∈ s, if u < k ∧ k < v then w k * (v - k) else 0) + (1 / (v - u)) * (∑ k ∈ s, if u < k ∧ k < v then w k * (k - u) else 0) = (1 / (v - u)) * (∑ k ∈ s, if u < k ∧ k < v then w k * (v - u) else 0) := by
      rw [ ← mul_add, ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> linarith;
    have h_simplified : (1 / (v - u)) * (∑ k ∈ s, if u < k ∧ k < v then w k * (v - u) else 0) = ∑ k ∈ s, if u < k ∧ k < v then w k else 0 := by
      field_simp [sub_ne_zero.mpr h_ne.symm];
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring_nf;
    exact h_combined.trans h_simplified

lemma MaxAffineIsSimpleStatement.u_Cu_add_v_Cv (s : Finset Real) (w : Real → Real) (u v : Real) (h_ne : u ≠ v) :
  u * MaxAffineIsSimpleStatement.Cu s w u v + v * MaxAffineIsSimpleStatement.Cv s w u v = s.sum (fun k => if u < k ∧ k < v then w k * k else 0) := by
    have h_expand : u * MaxAffineIsSimpleStatement.Cu s w u v + v * MaxAffineIsSimpleStatement.Cv s w u v = (1 / (v - u)) * ∑ k ∈ s, (if u < k ∧ k < v then w k * (u * (v - k) + v * (k - u)) else 0) := by
      simp [MaxAffineIsSimpleStatement.Cu, MaxAffineIsSimpleStatement.Cv];
      simp +decide only [Finset.mul_sum _ _ _, ← mul_assoc, mul_add];
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> ring_nf;
    rw [ h_expand, Finset.mul_sum _ _ _ ];
    grind

lemma MaxAffineIsSimpleStatement.flatten_w_v3_sum (s : Finset Real) (w : Real → Real) (u v : Real) (h_uv : u < v) :
  (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k) = s.sum w := by
    unfold MaxAffineIsSimpleStatement.flatten_s MaxAffineIsSimpleStatement.flatten_w_v3;
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> simp_all +decide [ Finset.sum_union, Finset.sum_ite ];
    · simp +decide [ Finset.filter_eq', Finset.filter_ne', Finset.sum_filter, Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm, add_comm ];
      rw [ show ( ∑ a ∈ s, if u < a ∧ a < v then w a * ( a - u ) else 0 ) = ∑ a ∈ s.filter ( fun x => u < x ∧ x < v ), w a * ( a - u ) by rw [ Finset.sum_filter ] ] ; rw [ show ( ∑ a ∈ s, if u < a ∧ a < v then w a * ( v - a ) else 0 ) = ∑ a ∈ s.filter ( fun x => u < x ∧ x < v ), w a * ( v - a ) by rw [ Finset.sum_filter ] ] ; simp +decide [ *, Finset.sum_erase ] ; ring_nf;
      have h_sum_eq : ∑ x ∈ ({x ∈ s | x ≤ u ∨ v ≤ x}.erase u).erase v, (if u < x → v ≤ x then w x else 0) = ∑ x ∈ s \ ({u, v} ∪ {x ∈ s | u < x ∧ x < v}), w x := by
        refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
        · grind;
        · exact fun x hx hxu hxv hx' => Classical.or_iff_not_imp_left.2 fun hx'' => hx' <| lt_of_not_ge hx'';
        · grind;
      rw [ h_sum_eq, ← Finset.sum_sdiff <| show { u, v } ∪ { x ∈ s | u < x ∧ x < v } ⊆ s from Finset.union_subset ( Finset.insert_subset hu <| Finset.singleton_subset_iff.mpr hv ) <| Finset.filter_subset _ _ ] ; simp +decide [ *, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_mul, mul_sub, add_mul, mul_add, Finset.sum_ite ] ; ring_nf;
      rw [ Finset.sum_insert, Finset.sum_insert ] <;> norm_num [ h_uv.ne' ] ; ring_nf;
      · norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_uv.ne' ] ; ring_nf;
        nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( -u + v ) ≠ 0 ) ( ∑ i ∈ s with u < i ∧ i < v, w i ) ];
      · linarith;
    · simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ];
      rw [ show ( ( Insert.insert v ( { x ∈ s | x ≤ u ∨ v ≤ x } ) ).erase u ).erase v = s.filter ( fun x => x ≤ u ∨ v ≤ x ) \ { u } from ?_, Finset.sum_eq_sum_diff_singleton_add hu ] ; ring_nf;
      · rw [ show ( s \ { u } ) = ( s.filter ( fun x => x ≤ u ∨ v ≤ x ) \ { u } ) ∪ ( s.filter ( fun x => u < x ∧ x < v ) ) from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, h_uv.ne', h_uv.ne ] ; ring_nf;
        · rw [ show ( Finset.filter ( fun x => u < x → v ≤ x ) ( Finset.filter ( fun x => x ≤ u ∨ v ≤ x ) s \ { u } ) ) = Finset.filter ( fun x => x ≤ u ∨ v ≤ x ) s \ { u } from ?_, add_assoc ];
          · simpa [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using by nlinarith [ inv_mul_cancel_left₀ ( sub_ne_zero_of_ne h_uv.ne' ) ( ∑ x ∈ s with u < x ∧ x < v, w x ) ] ;
          · grind;
        · by_contra h_not_disjoint;
          exact h_not_disjoint <| Finset.disjoint_left.mpr fun x hx₁ hx₂ => by cases Finset.mem_sdiff.mp hx₁ |>.1 |> Finset.mem_filter.mp |>.2 <;> cases Finset.mem_filter.mp hx₂ |>.2 <;> linarith;
        · grind;
      · grind;
    · simp_all +decide [ Finset.filter_eq', Finset.filter_ne', Finset.sum_filter ];
      simp +decide [ Finset.sum_ite, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm, sub_eq_add_neg, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, Finset.sum_ite, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm, sub_eq_add_neg, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
      rw [ ← add_assoc, ← Finset.sum_add_distrib ];
      rw [ ← Finset.sum_subset ( show s.filter ( fun x => u < x ∧ x < v ) ∪ ( s.filter ( fun x => x ≤ u ∨ v ≤ x ) |> Finset.filter fun x => u < x → v ≤ x ) ⊆ s from Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _ ) ) ];
      · rw [ Finset.sum_union ];
        · exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun x hx => by nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( v + -u ) ≠ 0 ) ( w x ) ] ) rfl;
        · rw [ Finset.disjoint_left ] ; aesop;
      · grind;
    · simp_all +decide [ Finset.filter_eq', Finset.filter_ne', Finset.sum_filter ];
      split_ifs <;> simp_all +decide [ Finset.sum_ite, Finset.filter_or, Finset.filter_and ];
      rw [ show ( Finset.filter ( LT.lt u ) s ∩ { a ∈ s | a < v } ) = Finset.filter ( fun x => u < x ∧ x < v ) s by ext; aesop ] ; rw [ show ( ( Insert.insert v ( { a ∈ s | a ≤ u } ∪ Finset.filter ( LE.le v ) s ) ).erase u ).erase v = Finset.filter ( fun x => x ≤ u ∨ v ≤ x ) s by ext; aesop ] ; simp +decide [ Finset.sum_filter, Finset.sum_union, Finset.sum_add_distrib, mul_sub, sub_mul, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, h_uv.ne' ] ; ring_nf;
      rw [ ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib ] ; congr ; ext x ; by_cases hx : u < x <;> by_cases hx' : x < v <;> simp +decide [ hx, hx' ] ; ring_nf;
      · rw [ if_neg ( by rintro ( h | h ) <;> linarith ) ] ; nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( v - u ) ≠ 0 ) ( w x ) ];
      · grind

lemma MaxAffineIsSimpleStatement.flatten_w_v3_moment (s : Finset Real) (w : Real → Real) (u v : Real) (h_uv : u < v) :
  (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * k) = s.sum (fun k => w k * k) := by
    have h_split : ∑ k ∈ (s.filter (fun x => x ≤ u ∨ x ≥ v)) ∪ {u, v}, MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * k =
                   ∑ k ∈ s.filter (fun x => x ≤ u ∨ x ≥ v), w k * k +
                   MaxAffineIsSimpleStatement.Cu s w u v * u +
                   MaxAffineIsSimpleStatement.Cv s w u v * v := by
                     by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> simp +decide [ hu, hv, Finset.sum_union ];
                     · unfold MaxAffineIsSimpleStatement.flatten_w_v3 MaxAffineIsSimpleStatement.Cu MaxAffineIsSimpleStatement.Cv; simp +decide [ Finset.sum_ite, Finset.filter_or, Finset.filter_and, * ] ; ring_nf;
                       simp +decide [ Finset.filter_eq', Finset.filter_ne', Finset.sum_filter, Finset.sum_union, * ] ; ring_nf;
                       split_ifs <;> simp_all +decide [ Finset.sum_erase ] ; ring_nf;
                       congr! 2;
                       grind;
                     · unfold MaxAffineIsSimpleStatement.flatten_w_v3 MaxAffineIsSimpleStatement.Cu MaxAffineIsSimpleStatement.Cv;
                       simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ];
                       rw [ if_neg ( by linarith ) ] ; rw [ show ( Finset.filter ( fun x => x ≤ u ∨ v ≤ x ) s ).erase u = Finset.filter ( fun x => x ≤ u ∨ v ≤ x ) s \ { u } by ext; aesop ] ; rw [ Finset.sum_eq_sum_diff_singleton_add ( show u ∈ Finset.filter ( fun x => x ≤ u ∨ v ≤ x ) s from Finset.mem_filter.mpr ⟨ hu, Or.inl <| by linarith ⟩ ) ] ; ring_nf;
                       congr! 2;
                       grind;
                     · unfold MaxAffineIsSimpleStatement.flatten_w_v3 MaxAffineIsSimpleStatement.Cu MaxAffineIsSimpleStatement.Cv;
                       simp +decide [ hu, hv, Finset.sum_ite, Finset.filter_union, Finset.filter_inter, Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring_nf;
                       simp +decide [ Finset.filter_ne', Finset.filter_and, Finset.sum_filter, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, hv, hu, ne_of_gt h_uv ] ; ring_nf;
                       grind;
                     · rw [ Finset.sum_insert, Finset.sum_insert ] <;> norm_num [ hu, hv ];
                       · unfold MaxAffineIsSimpleStatement.flatten_w_v3 MaxAffineIsSimpleStatement.Cu MaxAffineIsSimpleStatement.Cv; ring_nf;
                         simp_all +decide [ ne_of_gt, Finset.sum_ite ];
                         simp_all +decide [ Finset.filter_eq', Finset.filter_ne', Finset.sum_ite ];
                         simp +decide [ mul_assoc, Finset.sum_filter ];
                         grind;
                       · linarith;
    have h_simplify : ∑ k ∈ s.filter (fun x => x ≤ u ∨ x ≥ v), w k * k + MaxAffineIsSimpleStatement.Cu s w u v * u + MaxAffineIsSimpleStatement.Cv s w u v * v =
                       ∑ k ∈ s, w k * k := by
                         have h_simplify : ∑ k ∈ s, w k * k = ∑ k ∈ s.filter (fun x => x ≤ u ∨ x ≥ v), w k * k + ∑ k ∈ s.filter (fun x => u < x ∧ x < v), w k * k := by
                           rw [ ← Finset.sum_union ] ; congr ; ext x ; by_cases hx₁ : x ≤ u <;> by_cases hx₂ : v ≤ x <;> aesop;
                           exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
                             have h_or := (Finset.mem_filter.mp hx₁).2
                             have h_and := (Finset.mem_filter.mp hx₂).2
                             cases h_or <;> linarith [h_and.1, h_and.2]
                         have := MaxAffineIsSimpleStatement.u_Cu_add_v_Cv s w u v ( ne_of_lt h_uv ) ; simp_all +decide [ Finset.sum_ite ] ; linarith;
    exact h_split.trans h_simplify

lemma MaxAffineIsSimpleStatement.flatten_w_v3_moment' (s : Finset Real) (w : Real → Real) (u v : Real) (h_uv : u < v) :
  (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * k) = s.sum (fun k => w k * k) := by
    convert MaxAffineIsSimpleStatement.flatten_w_v3_moment s w u v h_uv using 1

lemma MaxAffineIsSimpleStatement.flatten_w_v3_moment_eq (s : Finset Real) (w : Real → Real) (u v : Real) (h_uv : u < v) :
  (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * k) = s.sum (fun k => w k * k) := by
    apply MaxAffineIsSimpleStatement.flatten_w_v3_moment' s w u v h_uv

lemma MaxAffineIsSimpleStatement.sum_psi_eq_of_moments_eq
    (s1 s2 : Finset Real) (w1 w2 : Real → Real) (v : Real)
    (h_sum : s1.sum w1 = s2.sum w2)
    (h_moment : s1.sum (fun k => w1 k * k) = s2.sum (fun k => w2 k * k))
    (h_supp : ∀ k ≥ v, (k ∈ s1 ↔ k ∈ s2) ∧ (k ∈ s1 → w1 k = w2 k)) :
    ∀ x ≥ v, s1.sum (fun k => w1 k * MaxAffineIsSimpleStatement.psi k x) = s2.sum (fun k => w2 k * MaxAffineIsSimpleStatement.psi k x) := by
      intro x hx;
      have h_split : ∑ k ∈ s1, w1 k * MaxAffineIsSimpleStatement.psi k x = ∑ k ∈ s1.filter (fun k => k < x), w1 k * (x - k) ∧ ∑ k ∈ s2, w2 k * MaxAffineIsSimpleStatement.psi k x = ∑ k ∈ s2.filter (fun k => k < x), w2 k * (x - k) := by
        constructor <;> rw [ Finset.sum_filter ];
        · refine' Finset.sum_congr rfl fun k hk => _;
          unfold MaxAffineIsSimpleStatement.psi; split_ifs <;> simp +decide [ *, le_of_lt ] ;
          exact Or.inr ( le_of_not_gt ‹_› );
        · refine' Finset.sum_congr rfl fun k hk => _;
          unfold MaxAffineIsSimpleStatement.psi; split_ifs <;> simp_all +decide [ mul_comm ] ;
          exact Or.inl <| le_of_lt ‹_›;
      have h_sum_eq : ∑ k ∈ s1.filter (fun k => k < x), w1 k = ∑ k ∈ s2.filter (fun k => k < x), w2 k := by
        have h_sum_eq : ∑ k ∈ s1.filter (fun k => k ≥ x), w1 k = ∑ k ∈ s2.filter (fun k => k ≥ x), w2 k := by
          apply Finset.sum_bij (fun k hk => k);
          · grind;
          · aesop;
          · grind;
          · exact fun k hk => h_supp k ( le_trans hx ( Finset.mem_filter.mp hk |>.2 ) ) |>.2 ( Finset.mem_filter.mp hk |>.1 );
        have h_sum_eq : ∑ k ∈ s1, w1 k = ∑ k ∈ s1.filter (fun k => k < x), w1 k + ∑ k ∈ s1.filter (fun k => k ≥ x), w1 k ∧ ∑ k ∈ s2, w2 k = ∑ k ∈ s2.filter (fun k => k < x), w2 k + ∑ k ∈ s2.filter (fun k => k ≥ x), w2 k := by
          exact ⟨ by rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext k ; split_ifs <;> linarith, by rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext k ; split_ifs <;> linarith ⟩;
        linarith;
      have h_sum_eq : ∑ k ∈ s1.filter (fun k => k < x), w1 k * k = ∑ k ∈ s2.filter (fun k => k < x), w2 k * k := by
        have h_sum_eq : ∑ k ∈ s1.filter (fun k => k ≥ x), w1 k * k = ∑ k ∈ s2.filter (fun k => k ≥ x), w2 k * k := by
          apply Finset.sum_bij (fun k hk => k);
          · grind;
          · aesop;
          · grind;
          · field_simp;
            exact fun k hk => by rw [ mul_comm, h_supp k ( by linarith [ Finset.mem_filter.mp hk ] ) |>.2 ( Finset.mem_filter.mp hk |>.1 ) ] ;
        have h_sum_eq : ∑ k ∈ s1, w1 k * k = ∑ k ∈ s1.filter (fun k => k < x), w1 k * k + ∑ k ∈ s1.filter (fun k => k ≥ x), w1 k * k ∧ ∑ k ∈ s2, w2 k * k = ∑ k ∈ s2.filter (fun k => k < x), w2 k * k + ∑ k ∈ s2.filter (fun k => k ≥ x), w2 k * k := by
          exact ⟨ by rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext k ; split_ifs <;> linarith, by rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext k ; split_ifs <;> linarith ⟩;
        linarith;
      simp_all +decide [ mul_sub, Finset.sum_mul _ _ _ ];
      simp_all +decide [ ← Finset.sum_mul _ _ _ ]

lemma MaxAffineIsSimpleStatement.sum_psi_eq_ge_v
    (s1 s2 : Finset Real) (w1 w2 : Real → Real) (v : Real)
    (h_sum : s1.sum w1 = s2.sum w2)
    (h_moment : s1.sum (fun k => w1 k * k) = s2.sum (fun k => w2 k * k))
    (h_eq : ∀ k > v, (k ∈ s1 ↔ k ∈ s2) ∧ (k ∈ s1 → w1 k = w2 k)) :
    ∀ x ≥ v, s1.sum (fun k => w1 k * MaxAffineIsSimpleStatement.psi k x) = s2.sum (fun k => w2 k * MaxAffineIsSimpleStatement.psi k x) := by
      have h_split : ∀ x ≥ v, ∑ k ∈ s1, w1 k * MaxAffineIsSimpleStatement.psi k x = ∑ k ∈ s1.filter (fun k => k ≤ v), w1 k * MaxAffineIsSimpleStatement.psi k x + ∑ k ∈ s1.filter (fun k => k > v), w1 k * MaxAffineIsSimpleStatement.psi k x ∧ ∑ k ∈ s2, w2 k * MaxAffineIsSimpleStatement.psi k x = ∑ k ∈ s2.filter (fun k => k ≤ v), w2 k * MaxAffineIsSimpleStatement.psi k x + ∑ k ∈ s2.filter (fun k => k > v), w2 k * MaxAffineIsSimpleStatement.psi k x := by
        exact fun x hx => ⟨ by rw [ ← Finset.sum_union ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ) ] ; congr; ext; by_cases h : ( ‹_› : ℝ ) ≤ v <;> aesop, by rw [ ← Finset.sum_union ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ) ] ; congr; ext; by_cases h : ( ‹_› : ℝ ) ≤ v <;> aesop ⟩;
      intros x hx
      rw [h_split x hx |>.left, h_split x hx |>.right];
      refine' congrArg₂ ( · + · ) _ _;
      · have h_sum_le_v : ∑ k ∈ s1, w1 k * (if k ≤ v then 1 else 0) = ∑ k ∈ s2, w2 k * (if k ≤ v then 1 else 0) := by
          have h_sum_le_v : ∑ k ∈ s1, w1 k * (if k > v then 1 else 0) = ∑ k ∈ s2, w2 k * (if k > v then 1 else 0) := by
            rw [ ← Finset.sum_subset ( show s1.filter ( fun k => k > v ) ⊆ s2 from fun x hx => by aesop ) ];
            · rw [ Finset.sum_filter ] ; exact Finset.sum_congr rfl fun x hx => by specialize h_eq x ; aesop;
            · grind;
          simp +zetaDelta at *;
          rw [ show ( ∑ x ∈ s1, if x ≤ v then w1 x else 0 ) = ( ∑ x ∈ s1, w1 x ) - ( ∑ x ∈ s1, if v < x then w1 x else 0 ) by rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> linarith, show ( ∑ x ∈ s2, if x ≤ v then w2 x else 0 ) = ( ∑ x ∈ s2, w2 x ) - ( ∑ x ∈ s2, if v < x then w2 x else 0 ) by rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> linarith ] ; linarith;
        have h_moment_le_v : ∑ k ∈ s1, w1 k * k * (if k ≤ v then 1 else 0) = ∑ k ∈ s2, w2 k * k * (if k ≤ v then 1 else 0) := by
          have h_moment_le_v : ∑ k ∈ s1, w1 k * k * (if k > v then 1 else 0) = ∑ k ∈ s2, w2 k * k * (if k > v then 1 else 0) := by
            rw [ ← Finset.sum_subset ( show s1.filter ( fun k => k > v ) ⊆ s2 from fun x hx => by aesop ) ];
            · rw [ Finset.sum_filter ];
              exact Finset.sum_congr rfl fun x hx => by specialize h_eq x; aesop;
            · grind;
          have h_moment_le_v : ∑ k ∈ s1, w1 k * k * (if k ≤ v then 1 else 0) + ∑ k ∈ s1, w1 k * k * (if k > v then 1 else 0) = ∑ k ∈ s2, w2 k * k * (if k ≤ v then 1 else 0) + ∑ k ∈ s2, w2 k * k * (if k > v then 1 else 0) := by
            convert h_moment using 1 <;> rw [ ← Finset.sum_add_distrib ] <;> congr <;> ext <;> split_ifs <;> linarith;
          linarith;
        convert congr_arg₂ ( · * x - · ) h_sum_le_v h_moment_le_v using 1 <;> simp +decide [ Finset.sum_ite, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, MaxAffineIsSimpleStatement.psi ] ; ring_nf;
        · rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun y hy => by rw [ max_eq_left ( by linarith [ Finset.mem_filter.mp hy ] ) ] ; ring_nf;
        · rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun i hi => by rw [ max_eq_left ( by linarith [ Finset.mem_filter.mp hi ] ) ] ; ring_nf;
      · refine' Finset.sum_bij ( fun k hk => k ) _ _ _ _ <;> aesop

lemma MaxAffineIsSimpleStatement.flatten_eq_le_u (s : Finset Real) (w : Real → Real) (u v a b : Real)
  (f : Real → Real) (hf : ∀ x, f x = a * x + b + s.sum (fun k => w k * MaxAffineIsSimpleStatement.psi k x))
  (h_uv : u < v) :
  ∀ x ≤ u, (a * x + b + (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * MaxAffineIsSimpleStatement.psi k x)) = f x := by
    intro x hx
    rw [hf];
    unfold MaxAffineIsSimpleStatement.flatten_s MaxAffineIsSimpleStatement.flatten_w_v3 MaxAffineIsSimpleStatement.psi;
    simp +decide [ Finset.sum_union, Finset.sum_ite, hx ];
    simp +decide [ Finset.sum_filter, hx ];
    rw [ max_eq_right ( by linarith ) ] ; ring_nf;
    grind

lemma MaxAffineIsSimpleStatement.flatten_eq_ge_v (s : Finset Real) (w : Real → Real) (u v a b : Real)
  (f : Real → Real) (hf : ∀ x, f x = a * x + b + s.sum (fun k => w k * MaxAffineIsSimpleStatement.psi k x))
  (h_uv : u < v) :
  ∀ x ≥ v, (a * x + b + (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * MaxAffineIsSimpleStatement.psi k x)) = f x := by
    intro x hx;
    have h_sum_eq : ∑ k ∈ s, w k * MaxAffineIsSimpleStatement.psi k x = ∑ k ∈ MaxAffineIsSimpleStatement.flatten_s s u v, MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * MaxAffineIsSimpleStatement.psi k x := by
      exact MaxAffineIsSimpleStatement.sum_psi_eq_ge_v s (MaxAffineIsSimpleStatement.flatten_s s u v) w (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k) v
        (Eq.symm (MaxAffineIsSimpleStatement.flatten_w_v3_sum s w u v h_uv))
        (Eq.symm (MaxAffineIsSimpleStatement.flatten_w_v3_moment_eq s w u v h_uv))
        (fun k hk => by simp [MaxAffineIsSimpleStatement.flatten_s, MaxAffineIsSimpleStatement.flatten_w_v3]; grind)
        x hx
    rw [ hf, h_sum_eq ]

lemma MaxAffineIsSimpleStatement.flatten_eq_ge_v' (s : Finset Real) (w : Real → Real) (u v a b : Real)
  (f : Real → Real) (hf : ∀ x, f x = a * x + b + s.sum (fun k => w k * MaxAffineIsSimpleStatement.psi k x))
  (h_uv : u < v) :
  ∀ x ≥ v, (a * x + b + (MaxAffineIsSimpleStatement.flatten_s s u v).sum (fun k => MaxAffineIsSimpleStatement.flatten_w_v3 s w u v k * MaxAffineIsSimpleStatement.psi k x)) = f x := by
    apply MaxAffineIsSimpleStatement.flatten_eq_ge_v s w u v a b f hf h_uv

lemma MaxAffineIsSimpleStatement.IsSimpleConvex_max_affine_simple (f : Real → Real) (hf : MaxAffineIsSimpleStatement.IsSimpleConvex f) (a b : Real) :
    MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => max (a * x + b) (f x)) := by
      by_contra hc;
      have h_ind : ∀ f, MaxAffineIsSimpleStatement.IsSimpleConvex f → (∀ a b, MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => max (a * x + b) (f x))) := by
        apply MaxAffineIsSimpleStatement.IsSimpleConvex_induction;
        · exact fun a b c d => MaxAffineIsSimpleStatement.max_affine_pair_is_simple c d a b;
        · intro f u w hf hw a b;
          set F : ℝ → ℝ := fun x => max (a * x + b) (f x)
          set G : ℝ → ℝ := fun x => max (a * x + b) (f x + w * (x - u));
          have hF : MaxAffineIsSimpleStatement.IsSimpleConvex F := by
            exact hf a b
          have hG : MaxAffineIsSimpleStatement.IsSimpleConvex G := by
            have hG_rewrite : ∀ x, G x = max ((a - w) * x + (b + w * u)) (f x) + w * (x - u) := by
              grind;
            convert MaxAffineIsSimpleStatement.IsSimpleConvex_add_affine ( hf ( a - w ) ( b + w * u ) ) w ( -w * u ) using 1 ; ext x ; rw [ hG_rewrite ] ; ring_nf;
          have hH : MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => if x ≤ u then F x else G x) := by
            apply MaxAffineIsSimpleStatement.IsSimpleConvex_glue F G u hF hG;
            · aesop;
            · exact fun x hx => max_le_iff.mpr ⟨ by cases max_cases ( a * x + b ) ( f x ) <;> nlinarith, by cases max_cases ( a * x + b ) ( f x ) <;> nlinarith ⟩;
            · exact fun x hx => max_le_max_left _ ( by nlinarith );
          convert hH using 2;
          unfold MaxAffineIsSimpleStatement.psi; split_ifs <;> simp +decide [ *, max_def ] ;
          · grind;
          · grind;
      exact hc <| h_ind f hf a b

lemma MaxAffineIsSimpleStatement.max_affine_is_simple
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (L : ι → Real →L[Real] Real) (c : ι → Real) :
    MaxAffineIsSimpleStatement.IsSimpleConvex (fun x => s.sup' hs (fun i => L i x + c i)) := by
      induction' s using Finset.induction with i s hi ih generalizing L c;
      · exact False.elim ( Finset.not_nonempty_empty hs );
      · by_cases hs : s.Nonempty <;> simp_all +decide [ Finset.sup'_insert ];
        · convert MaxAffineIsSimpleStatement.IsSimpleConvex_max_affine_simple _ ( ih L c ) ( L i 1 ) ( c i ) using 1;
          simp only [mul_comm]
          exact funext fun x => by rw [show (L i) x = x * (L i) 1 from by simpa using (L i).map_smul x 1]
        · use (L i) 1, c i, ∅, fun _ => 0
          constructor
          · simp
          · intro x; simp; exact (by simpa [mul_comm] using (L i).map_smul x 1)

/-- Bridge: transport Aristotle's max_affine_is_simple to this file's IsSimpleConvex/psi. -/
theorem max_affine_is_simple
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (L : ι → Real →L[Real] Real) (c : ι → Real) :
    IsSimpleConvex (fun x => s.sup' hs (fun i => L i x + c i)) := by
  classical
  simpa [IsSimpleConvex, psi, MaxAffineIsSimpleStatement.IsSimpleConvex,
    MaxAffineIsSimpleStatement.psi] using
    (MaxAffineIsSimpleStatement.max_affine_is_simple (s := s) (hs := hs) (L := L) (c := c))

set_option linter.unusedSimpArgs true

theorem real_univ_sSup_of_nat_affine_le_eq
    {f : Real → Real} (hLsc : LowerSemicontinuous f) (hConv : ConvexOn Real Set.univ f) :
    ∃ (l : Nat → Real →L[Real] Real) (c : Nat → Real),
      (∀ i x, l i x + c i ≤ f x) ∧
      (⨆ i, (l i) + Function.const Real (c i) = f) := by
  let 𝓕 : Set (Real → Real) :=
    {g | g ≤ f ∧ ∃ (L : Real →L[Real] Real) (b : Real), g = L + Function.const Real b}
  have hLUB : IsLUB 𝓕 f := by
    refine (hConv.real_univ_sSup_affine_eq hLsc) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨L, b, hLb⟩ := ConvexOn.exists_affine_le_of_lt
        (𝕜 := Real) (s := Set.univ) (φ := f) (x := (0 : Real)) (a := f 0 - 1)
        (hx := by simp) (hax := by linarith) isClosed_univ
        (lowerSemicontinuousOn_univ_iff.2 hLsc) hConv
      refine ⟨L + Function.const Real b, ?_⟩
      refine ⟨?_, ⟨L, b, rfl⟩⟩
      intro x
      simpa using hLb.1 ⟨x, by simp⟩
    · exact ⟨f, fun g hg => hg.1⟩
  have hLower (g : Real → Real) (hg : g ∈ 𝓕) : LowerSemicontinuous g := by
    obtain ⟨L, b, hEq⟩ := hg.2
    exact Continuous.lowerSemicontinuous (hEq ▸ by fun_prop)
  obtain ⟨𝓕', hsub, hcount, hLUB'⟩ := exists_countable_lowerSemicontinuous_isLUB hLower hLUB
  have hne : 𝓕'.Nonempty := by
    by_contra hne
    have hempty : 𝓕' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hbot : IsBot f := (isLUB_empty_iff.1 (hempty ▸ hLUB'))
    have hcontra : f ≤ fun x => f x - 1 := hbot (fun x => f x - 1)
    have h0 : ¬f ≤ fun x => f x - 1 := by
      intro hf_le
      have h0' := hf_le 0
      linarith
    exact h0 hcontra
  obtain ⟨g, hg_range⟩ := hcount.exists_eq_range hne
  have hAff (i : Nat) : ∃ (L : Real →L[Real] Real) (b : Real), g i = L + Function.const Real b := by
    have hmem : g i ∈ 𝓕' := by
      rw [hg_range]
      exact ⟨i, rfl⟩
    exact (hsub hmem).2
  choose l c hlc using hAff
  refine ⟨l, c, ?_, ?_⟩
  · intro i x
    have hmem : g i ∈ 𝓕' := by
      rw [hg_range]
      exact ⟨i, rfl⟩
    have hle_fun : g i ≤ f := (hsub hmem).1
    have hEq : g i = l i + Function.const Real (c i) := hlc i
    simpa [hEq, Function.const_apply] using hle_fun x
  · calc
      (⨆ i, (l i) + Function.const Real (c i))
          = ⨆ i, g i := by
              congr with i x
              exact congrFun (hlc i).symm x
      _ = sSup (Set.range g) := by rw [← sSup_range]
      _ = sSup 𝓕' := by rw [← hg_range]
      _ = f := hLUB'.csSup_eq hne

theorem convex_simpleApprox_exists
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) :
    ∃ fn : Nat → Real → Real,
      (∀ n, IsSimpleConvex (fn n)) ∧
      (∀ x, Monotone (fun n => fn n x)) ∧
      (∀ x, Tendsto (fun n => fn n x) Filter.atTop (nhds (f x))) := by
  have hcontOn : ContinuousOn f Set.univ :=
    ConvexOn.continuousOn (C := Set.univ) isOpen_univ hfConv
  have hcont : Continuous f := (continuousOn_univ.mp hcontOn)
  have hlsc : LowerSemicontinuous f := hcont.lowerSemicontinuous
  rcases real_univ_sSup_of_nat_affine_le_eq hlsc hfConv with ⟨l, c, hle, hsup⟩
  let fn : Nat → Real → Real := fun n x =>
    (Finset.range (n + 1)).sup' ⟨0, by simp⟩ (fun i => l i x + c i)
  refine ⟨fn, ?_, ?_, ?_⟩
  · intro n
    simpa [fn] using
      (max_affine_is_simple (s := Finset.range (n + 1)) (hs := ⟨0, by simp⟩) (L := l) (c := c))
  · intro x m n hmn
    have hsubset : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      exact lt_of_lt_of_le hi (Nat.succ_le_succ hmn)
    have hne : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
    simpa [fn] using
      (Finset.sup'_mono (f := fun i => l i x + c i) hsubset hne)
  · intro x
    let a : Nat → Real := fun i => l i x + c i
    have hmonoFn : Monotone (fun n => fn n x) := by
      intro m n hmn
      have hsubset : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        exact lt_of_lt_of_le hi (Nat.succ_le_succ hmn)
      have hne : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
      simpa [fn] using
        (Finset.sup'_mono (f := fun i => l i x + c i) hsubset hne)
    have hbddA : BddAbove (Set.range a) := by
      refine ⟨f x, ?_⟩
      rintro y ⟨i, rfl⟩
      exact hle i x
    have hfn_le_fx : ∀ n, fn n x ≤ f x := by
      intro n
      unfold fn
      have hneRange : (Finset.range (n + 1)).Nonempty := by
        exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
      exact Finset.sup'_le (s := Finset.range (n + 1)) (f := fun i : Nat => l i x + c i)
        hneRange (fun i hi => hle i x)
    have hbddFn : BddAbove (Set.range (fun n => fn n x)) := by
      refine ⟨f x, ?_⟩
      rintro y ⟨n, rfl⟩
      exact hfn_le_fx n
    have hfn_le_iSupA : ∀ n, fn n x ≤ ⨆ i, a i := by
      intro n
      unfold fn
      have hneRange : (Finset.range (n + 1)).Nonempty := by
        exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
      exact Finset.sup'_le (s := Finset.range (n + 1)) (f := fun i : Nat => l i x + c i)
        hneRange (fun i hi => le_ciSup hbddA i)
    have hiSupA_le_iSupFn : (⨆ i, a i) ≤ ⨆ n, fn n x := by
      refine ciSup_le ?_
      intro i
      have hmem : i ∈ Finset.range (i + 1) := by
        rw [Finset.mem_range]
        exact Nat.lt_succ_self i
      have hle_i : a i ≤ fn i x := by
        unfold fn
        exact Finset.le_sup' (s := Finset.range (i + 1)) (f := fun j => l j x + c j) hmem
      exact hle_i.trans (le_ciSup hbddFn i)
    have hiSupFn_eq_iSupA : (⨆ n, fn n x) = (⨆ i, a i) := by
      exact le_antisymm (ciSup_le hfn_le_iSupA) hiSupA_le_iSupFn
    have hsupx : (⨆ i, a i) = f x := by
      have hfun := congrArg (fun g : Real → Real => g x) hsup
      simpa [a, Function.const_apply] using hfun
    have ht :
        Tendsto (fun n => fn n x) Filter.atTop (nhds (⨆ n, fn n x)) :=
      tendsto_atTop_ciSup hmonoFn hbddFn
    simpa [hiSupFn_eq_iSupA, hsupx] using ht

noncomputable def simpleApproxSeq
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) : Nat → Real → Real :=
  Classical.choose (convex_simpleApprox_exists hfConv)

lemma simpleApproxSeq_isSimple
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) :
    ∀ n, IsSimpleConvex (simpleApproxSeq hfConv n) := by
  exact (Classical.choose_spec (convex_simpleApprox_exists hfConv)).1

lemma simpleApproxSeq_mono
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) :
    ∀ x, Monotone (fun n => simpleApproxSeq hfConv n x) := by
  exact (Classical.choose_spec (convex_simpleApprox_exists hfConv)).2.1

lemma simpleApproxSeq_tendsto
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) :
    ∀ x, Tendsto (fun n => simpleApproxSeq hfConv n x) Filter.atTop (nhds (f x)) := by
  exact (Classical.choose_spec (convex_simpleApprox_exists hfConv)).2.2

lemma simpleApproxSeq_integrable_mu
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) :
    ∀ n, Integrable (simpleApproxSeq hfConv n) mu := by
  intro n
  exact simpleConvex_integrable (mu := mu) hIntMuId (simpleApproxSeq_isSimple hfConv n)

lemma simpleApproxSeq_integrable_gaussian
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f) :
    ∀ n, Integrable (simpleApproxSeq hfConv n) (gaussianScale c0) := by
  letI : IsProbabilityMeasure (gaussianScale c0) := gaussianScale_isProbability c0
  have hIntNuId : Integrable (fun x : Real => x) (gaussianScale c0) :=
    gaussianScale_integrable_id c0
  intro n
  exact simpleConvex_integrable (mu := gaussianScale c0) hIntNuId (simpleApproxSeq_isSimple hfConv n)

lemma simpleApproxSeq_integral_le
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f)
    (hSimpleStep :
      ∀ {g : Real → Real}, IsSimpleConvex g →
        Integrable g mu → Integrable g (gaussianScale c0) →
          (∫ x, g x ∂mu) <= (∫ x, g x ∂(gaussianScale c0))) :
    ∀ n, (∫ x, simpleApproxSeq hfConv n x ∂mu) ≤
      (∫ x, simpleApproxSeq hfConv n x ∂(gaussianScale c0)) := by
  intro n
  exact hSimpleStep
    (simpleApproxSeq_isSimple hfConv n)
    (simpleApproxSeq_integrable_mu hIntMuId hfConv n)
    (simpleApproxSeq_integrable_gaussian hfConv n)

theorem convexReduction_to_simple_c0
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (_htail : subgaussianTail mu)
    (_hmean : mean mu = 0)
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f)
    (hmu : Integrable f mu) (hG : Integrable f (gaussianScale c0))
    (hSimpleStep :
      ∀ {g : Real → Real}, IsSimpleConvex g →
        Integrable g mu → Integrable g (gaussianScale c0) →
          (∫ x, g x ∂mu) <= (∫ x, g x ∂(gaussianScale c0))) :
    (∫ x, f x ∂mu) <= (∫ x, f x ∂(gaussianScale c0)) := by
  letI : IsProbabilityMeasure (gaussianScale c0) := gaussianScale_isProbability c0
  let fn : Nat → Real → Real := simpleApproxSeq hfConv
  have hIntFnMu : ∀ n, Integrable (fn n) mu := by
    intro n
    simpa [fn] using (simpleApproxSeq_integrable_mu hIntMuId hfConv n)
  have hIntFnNu : ∀ n, Integrable (fn n) (gaussianScale c0) := by
    intro n
    simpa [fn] using (simpleApproxSeq_integrable_gaussian hfConv n)
  have hineq : ∀ n, (∫ x, fn n x ∂mu) ≤ (∫ x, fn n x ∂(gaussianScale c0)) := by
    intro n
    simpa [fn] using (simpleApproxSeq_integral_le hIntMuId hfConv hSimpleStep n)
  have hlim_mu :
      Tendsto (fun n => ∫ x, fn n x ∂mu) Filter.atTop (nhds (∫ x, f x ∂mu)) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone hIntFnMu hmu ?_ ?_
    · exact Filter.Eventually.of_forall (simpleApproxSeq_mono hfConv)
    · exact Filter.Eventually.of_forall (simpleApproxSeq_tendsto hfConv)
  have hlim_nu :
      Tendsto (fun n => ∫ x, fn n x ∂(gaussianScale c0)) Filter.atTop
        (nhds (∫ x, f x ∂(gaussianScale c0))) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone hIntFnNu hG ?_ ?_
    · exact Filter.Eventually.of_forall (simpleApproxSeq_mono hfConv)
    · exact Filter.Eventually.of_forall (simpleApproxSeq_tendsto hfConv)
  exact le_of_tendsto_of_tendsto hlim_mu hlim_nu (Filter.Eventually.of_forall hineq)

/--
Two-step interface theorem:
1) reduce convex `f` to simple-convex test functions,
2) invoke the already-proved `c0` simple-convex bound.
-/
theorem convexDomination_c0_via_reduction
    {mu : Measure Real} [IsProbabilityMeasure mu]
    (hIntMuId : Integrable (fun x : Real => x) mu)
    (htail : subgaussianTail mu)
    (hmean : mean mu = 0)
    {f : Real → Real} (hfConv : ConvexOn Real Set.univ f)
    (hmu : Integrable f mu) (hG : Integrable f (gaussianScale c0)) :
    (∫ x, f x ∂mu) <= (∫ x, f x ∂(gaussianScale c0)) := by
  refine convexReduction_to_simple_c0 hIntMuId htail hmean hfConv hmu hG ?_
  intro g hgSimple hgmu hgG
  exact convexDomination_c0_simple hIntMuId htail hmean hgSimple hgmu hgG

end OneDimConvexDom
