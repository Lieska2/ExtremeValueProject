/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.CumulativeDistributionFunction
import ExtremeValueProject.AffineTransformation
import Mathlib

section weak_convergence_cdf

open Filter Topology NNReal ENNReal Set

/-- Lemma 4.3 (cdf-tight) in blueprint. -/
lemma CumulativeDistributionFunction.forall_pos_exists_lt_gt_continuousAt
    (F : CumulativeDistributionFunction) {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (a b : ℝ), a < b ∧ F a < ε ∧ 1 - ε < F b ∧ ContinuousAt F a ∧ ContinuousAt F b := by
  sorry -- **Issue #16**

/-- Lemma 4.4 (subdivision-dense) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that the consecutive
differences are smaller than a given `δ > 0`. -/
lemma forall_exists_subdivision_diff_lt_of_dense {D : Set ℝ} (D_dense : Dense D)
    {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b) {δ : ℝ} (δ_pos : 0 < δ) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), cs j.succ - cs j < δ) := by
  sorry -- **Issue #22**

/-- Lemma 4.5 (continuous-function-approximation-subdivision) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that for a given
continuous function `f` the function values on the parts of the subdivision are smaller than
a given `ε > 0`. -/
lemma forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous {D : Set ℝ} (D_dense : Dense D)
    {f : ℝ → ℝ} (f_cont : Continuous f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b)
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), ∀ x ∈ Icc (cs j) (cs j.succ), ∀ y ∈ Icc (cs j) (cs j.succ),
        dist (f x) (f y) < ε) := by
  let I : Set ℝ := Icc a b
  have hI_compact : IsCompact I := isCompact_Icc
  have hI_nonempty : I.Nonempty := nonempty_Icc.mpr (le_of_lt a_lt_b)
  have hf_cont_I : ContinuousOn f I := f_cont.continuousOn
  have hf_unif_cont : UniformContinuousOn f I :=
    hI_compact.uniformContinuousOn_of_continuous hf_cont_I
  have h_δ : ∃ δ > 0, ∀ x ∈ I, ∀ y ∈ I, dist x y < δ → dist (f x) (f y) < ε := by
    rw [Metric.uniformContinuousOn_iff] at hf_unif_cont
    exact hf_unif_cont ε ε_pos
  obtain ⟨δ, hδ_pos, hδ⟩ := h_δ
  obtain ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_diff⟩ :=
    forall_exists_subdivision_diff_lt_of_dense D_dense ha hb a_lt_b hδ_pos
  have h_cs_bound : ∀ i : Fin k, ∀ x ∈ Icc (cs i) (cs i.succ), ∀ y ∈ Icc (cs i) (cs i.succ), dist (f x) (f y) < ε := by
    intro i x hx y hy
    have hx_I : x ∈ I := by
      have h_lower : a ≤ cs i := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hx
    have hy_I : y ∈ I := by
      have h_lower : a ≤ cs i := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hy
    have h_dist_xy : dist x y < δ := by
      have h_bound : dist x y ≤ cs i.succ - cs i := by exact Real.dist_le_of_mem_Icc hx hy
      exact lt_of_le_of_lt h_bound (h_cs_diff i)
    exact hδ x hx_I y hy_I h_dist_xy
  exact ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_bound⟩

/-- Preliminary to Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (a_le_b : a ≤ b) (α : E) :
    ∫ x, (indicator (Ioc a b) (fun _ ↦ α)) x ∂ F.measure =
      (F b - F a) • α := by
  have h_meas : MeasurableSet (Ioc a b) := measurableSet_Ioc
  rw [MeasureTheory.integral_indicator h_meas, MeasureTheory.integral_const]
  have h_cdf : F.measure (Ioc a b) = ENNReal.ofReal (F b - F a) :=
    F.toStieltjesFunction.measure_Ioc a b
  congr
  simp [h_cdf, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono a_le_b))]

/-- Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_sum_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {κ : Type*} {s : Finset κ} (as : κ → ℝ) (bs : κ → ℝ) (h : ∀ j, as j ≤ bs j) (α : κ → E) :
    ∫ x, ((∑ j ∈ s, indicator (Ioc (as j) (bs j)) (fun _ ↦ α j)) x) ∂ F.measure =
      ∑ j in s, (F (bs j) - F (as j)) • α j := by
  -- It may be worthwhile to think about an improved phrasing of this.
  -- The previous lemma `CumulativeDistributionFunction.integral_indicator_eq` should be
  -- the key anyway.
  have h_int_sum_change : ∫ (x : ℝ), (∑ j ∈ s, (Ioc (as j) (bs j)).indicator (fun x => α j)) x ∂F.measure  = ∑ j ∈ s, ∫ (x : ℝ), (Ioc (as j) (bs j)).indicator (fun x => α j) x ∂F.measure  := by
    rw [← MeasureTheory.integral_finset_sum]
    simp_all only [measurableSet_Ioc, implies_true, Finset.sum_apply, MeasureTheory.integral_indicator_const]
    intro j _
    exact (MeasureTheory.integrable_const (α j)).indicator measurableSet_Ioc
  rw [h_int_sum_change]
  congr
  ext j
  exact F.integral_indicator_eq (h j) _

open MeasureTheory Topology

/-- Theorem 4.8 (convergence-in-distribution-with-cdf) in blueprint:
Convergence of a sequence of c.d.f.s pointwise at all continuity points of the limit c.d.f. imply
convergence in distribution of the corresponding Borel probability measures on `ℝ`. -/
theorem tendsto_of_forall_continuousAt_tendsto_cdf
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (h : ∀ x, ContinuousAt μ.cdf x → Tendsto (fun n ↦ (μs n).cdf x) atTop (𝓝 (μ.cdf x))) :
    Tendsto μs atTop (𝓝 μ) := by
  -- Use portmanteau theorem: show ∫f dμn → ∫f dμ for all bounded continuous f
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]

  intros f

  -- Let D be the set of continuity points of μ.cdf
  let D := {x : ℝ | ContinuousAt μ.cdf x}

  have D_dense : Dense D := by
    -- D = {x : ℝ | ContinuousAt μ.cdf x} is the complement of discontinuity points
    let S := {x : ℝ | ¬ContinuousAt μ.cdf x}

    -- S is countable by the given theorem
    have S_countable : S.Countable := Monotone.countable_not_continuousAt μ.cdf.mono'

    -- D = Sᶜ, so we need to show Sᶜ is dense
    have D_eq : D = Sᶜ := by
      ext x
      simp [D, S]

    rw [D_eq]
    exact Set.Countable.dense_compl ℝ S_countable

  -- Convert tendsto to epsilon-delta form
  rw [Metric.tendsto_atTop]
  -- Now introduce epsilon and its positivity
  intros ε ε_pos

  -- Choose points a,b ∈ D with specific properties using Lemma 4.3
  obtain ⟨a, b, a_lt_b, Fa_small, Fb_large, ha_cont, hb_cont⟩ :=
    μ.cdf.forall_pos_exists_lt_gt_continuousAt ε_pos

  have ha_in_D : a ∈ D := ha_cont
  have hb_in_D : b ∈ D := hb_cont

  -- Use convergence at continuity points a and b
  have h_conv_a : Tendsto (fun n => (μs n).cdf.toStieltjesFunction a) atTop (𝓝 (μ.cdf.toStieltjesFunction a)) :=
    h a ha_cont
  have h_conv_b : Tendsto (fun n => (μs n).cdf.toStieltjesFunction b) atTop (𝓝 (μ.cdf.toStieltjesFunction b)) :=
    h b hb_cont

  -- First show that F(b) - F(a) > 1 - 2ε
  have target_ineq : μ.cdf.toStieltjesFunction b - μ.cdf.toStieltjesFunction a > 1 - 2*ε := by
    linarith [Fa_small, Fb_large]

  -- The difference F_n(b) - F_n(a) converges to F(b) - F(a)
  have h_conv_diff : Tendsto (fun n => (μs n).cdf.toStieltjesFunction b - (μs n).cdf.toStieltjesFunction a) atTop
      (𝓝 (μ.cdf.toStieltjesFunction b - μ.cdf.toStieltjesFunction a)) :=
    Tendsto.sub h_conv_b h_conv_a

  -- Since the limit is > 1 - 2ε, eventually the sequence is > 1 - 2ε
  -- Choose δ as half the gap above 1 - 2ε
  let δ := (μ.cdf.toStieltjesFunction b - μ.cdf.toStieltjesFunction a - (1 - 2*ε)) / 2
  have δ_pos : δ > 0 := by
    simp only [δ]
    linarith [target_ineq]

  -- Get N₁ from convergence
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp h_conv_diff δ δ_pos

  have cdf_bound : ∀ n ≥ N₁, (μs n).cdf.toStieltjesFunction b - (μs n).cdf.toStieltjesFunction a > 1 - 2*ε := by
    intro n hn
    by_contra h_not
    push_neg at h_not
    -- So we have F_n(b) - F_n(a) ≤ 1 - 2ε

    -- From convergence, we know the difference is close
    have close := hN₁ n hn
    rw [dist_eq_norm] at close

    -- This gives us |F_n(b) - F_n(a) - (F(b) - F(a))| < δ
    -- which means F_n(b) - F_n(a) - (F(b) - F(a)) > -δ
    have lower_bound : (μs n).cdf.toStieltjesFunction b - (μs n).cdf.toStieltjesFunction a -
                      (μ.cdf.toStieltjesFunction b - μ.cdf.toStieltjesFunction a) > -δ := by linarith [abs_lt.mp close]

    -- But from our assumption h_not and target_ineq:
    -- F_n(b) - F_n(a) ≤ 1 - 2ε and F(b) - F(a) > 1 - 2ε
    -- So F_n(b) - F_n(a) - (F(b) - F(a)) < (1 - 2ε) - (1 - 2ε + 2δ) = -2δ
    have upper_bound : (μs n).cdf.toStieltjesFunction b - (μs n).cdf.toStieltjesFunction a -
                      (μ.cdf.toStieltjesFunction b - μ.cdf.toStieltjesFunction a) ≤ -2*δ := by
      simp only [δ] at target_ineq ⊢
      linarith [h_not, target_ineq]
    linarith


  -- Use Lemma 4.5 to subdivide [a,b] with points from D
  obtain ⟨k, cs, cs_0, cs_last, cs_mono, cs_in_D, cs_approx⟩ :=
    forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous D_dense f.continuous
    ha_in_D hb_in_D a_lt_b ε_pos

  -- Define simple function h
  let h : ℝ → ℝ := fun x => ∑ j : Fin k, f (cs j.succ) * (Set.indicator (Ioc (cs ↑↑j) (cs j.succ)) 1 x)
  -- let h : ℝ → ℝ := fun x => ∑ j : Fin k, f (cs j.succ) * if x ∈ Ioc (cs ↑↑j) (cs j.succ) then 1 else 0
  -- let h : ℝ → ℝ := fun x ↦ ∑ j : Fin k, f (cs j.succ) * (indicator (Ioc (cs j) (cs j.succ)) 1 x)

  -- Show |f(x) - h(x)| < ε for x ∈ (a,b]
  have f_h_close : ∀ x ∈ Ioc a b, |f x - h x| < ε := by
    intros x hx

    -- Every x ∈ (a,b] is covered by some interval (cs_j, cs_{j+1}]
    obtain ⟨j, hj⟩ : ∃ j : Fin k, x ∈ Ioc (cs j) (cs j.succ) := by

      -- Define S as subset of Fin (k + 1)
      let S : Set (Fin (k + 1)) := {j | cs j < x}

      -- S is nonempty since cs 0 = a < x
      have S_nonempty : S.Nonempty := by
        use 0
        simp [S, cs_0]
        rw [Set.mem_Ioc] at hx
        linarith

      -- Convert to finset nonemptiness
      have S_toFinset_nonempty : S.toFinset.Nonempty := Set.toFinset_nonempty.mpr S_nonempty

      -- Get the maximum element
      let j_max := S.toFinset.max' S_toFinset_nonempty

      -- Show j_max ≠ Fin.last k
      have h_not_last : j_max ≠ Fin.last k := by
        intro h_eq
        have j_max_in_S : j_max ∈ S := by
          rw [← Set.mem_toFinset]
          exact S.toFinset.max'_mem S_toFinset_nonempty
        have : cs (Fin.last k) < x := by
          rw [← h_eq]
          exact j_max_in_S  -- Now j_max_in_S : j_max ∈ S means cs j_max < x

        rw [cs_last] at this
        rw [Set.mem_Ioc] at hx
        linarith

      -- Convert to Fin k using the new theorem
      have h_lt : j_max < Fin.last k := Fin.lt_last_iff_ne_last.mpr h_not_last
      have h_val_lt : j_max.val < k := h_lt

      let j : Fin k := ⟨j_max.val, h_val_lt⟩

      use j
      constructor
      · -- cs ↑↑j < x
        have j_max_in_S : j_max ∈ S := by
          rw [← Set.mem_toFinset]
          exact S.toFinset.max'_mem S_toFinset_nonempty
        simp [S] at j_max_in_S  -- This gives us cs j_max < x
        convert j_max_in_S
        simp [j]

      · -- x ≤ cs j.succ
        by_contra h_not
        push_neg at h_not
        have succ_in_S : j.succ ∈ S := by
          simp [S]
          exact h_not
        have succ_le_max : j.succ ≤ j_max := by
          apply S.toFinset.le_max'
          rwa [Set.mem_toFinset]
        have max_lt_succ : j_max < j.succ := by
          rw [Fin.lt_iff_val_lt_val]
          simp [j]
        omega

    -- Simplify h x to f (cs j.succ)
    have h_eq : h x = f (cs j.succ) := by
      simp only [h]
      -- The sum reduces to just the j-th term since intervals are disjoint
      rw [Finset.sum_eq_single j]
      · -- The j-th term equals f (cs j.succ)
        change f (cs j.succ) * ((Ioc (cs ↑↑j) (cs j.succ)).indicator 1) x = f (cs j.succ)
        rw [Set.indicator_of_mem hj]
        simp
      · -- All other terms are zero

        intro b _ hne
        -- Show x ∉ Ioc (cs ↑↑b) (cs b.succ) when b ≠ j
        have x_not_in_b : x ∉ Ioc (cs ↑↑b) (cs b.succ) := by
          intro h_in_b
          -- Use trichotomy: either b < j or j < b
          cases' lt_or_gt_of_ne hne with h_lt h_gt
          · -- Case: b < j
            have b_succ_le_j_cast : b.succ ≤ j.castSucc := by
              rw [Fin.succ_le_castSucc_iff]
              exact h_lt

            have cs_ineq : cs b.succ ≤ cs ↑↑j := by
              simp
              apply cs_mono b_succ_le_j_cast
            have x_gt_cs_j : cs ↑↑j < x := hj.1
            have x_le_cs_b : x ≤ cs b.succ := h_in_b.2
            linarith [cs_ineq, x_gt_cs_j, x_le_cs_b]
          · -- Case: j < b
            have j_succ_le_b_cast : j.succ ≤ b.castSucc := by
              rw [Fin.succ_le_castSucc_iff]
              exact h_gt
            have cs_ineq : cs j.succ ≤ cs ↑↑b := by
              simp
              apply cs_mono j_succ_le_b_cast
            have x_le_cs_j : x ≤ cs j.succ := hj.2
            have x_gt_cs_b : cs ↑↑b < x := h_in_b.1
            linarith [cs_ineq, x_le_cs_j, x_gt_cs_b]

        -- Use indicator_of_not_mem and mul_zero
        rw [Set.indicator_of_not_mem x_not_in_b, mul_zero]
      · -- j is in the range
        simp

    -- Now use cs_approx to bound |f x - f (cs j.succ)|
    rw [h_eq]
    have x_in_Icc : x ∈ Icc (cs ↑↑j) (cs j.succ) := by
      exact Ioc_subset_Icc_self hj

    have cs_succ_in_Icc : cs j.succ ∈ Icc (cs ↑↑j) (cs j.succ) := by
      constructor
      · simp
        apply cs_mono (Fin.castSucc_le_succ j)
      · rfl

    have := cs_approx j x x_in_Icc (cs j.succ) cs_succ_in_Icc
    exact this

  -- Get boundedness constant for f
  obtain ⟨C, hC⟩ := BoundedContinuousFunction.bounded f
  -- Fix a point (say 0) to get a bound on the norm
  let K := ‖f 0‖ + C
  have norm_bound : ∀ x, ‖f x‖ ≤ K := by
    unfold K
    intro x
    have : dist (f x) (f 0) ≤ C := hC x 0
    rw [dist_eq_norm] at this

    have ineq : ‖f x‖  ≤  ‖ f 0‖ + ‖ f x - f 0‖ := by
      exact norm_le_norm_add_norm_sub' (f x) (f 0)
    linarith

  clear hN₁ h_conv_diff Fa_small Fb_large

  use N₁
  intro n hn

  -- First, use the triangle inequality: |∫ f dμₙ - ∫ h dμₙ| = |∫ (f - h) dμₙ| ≤ ∫ |f - h| dμₙ
  have triangle_ineq : |∫ (ω : ℝ), f ω ∂↑(μs n) - ∫ (ω : ℝ), h ω ∂↑(μs n)| ≤
    ∫ (ω : ℝ), |f ω - h ω| ∂↑(μs n) := by
    rw [← integral_sub]
    apply MeasureTheory.abs_integral_le_integral_abs
    · haveI : IsFiniteMeasure (μs n).toMeasure := MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure (μs n).toMeasure
      exact BoundedContinuousFunction.integrable (μs n).toMeasure f
    · -- Goal 2: ⊢ Integrable h ↑(μs n)
      -- First rewrite h to make the finset explicit
      unfold h
      apply MeasureTheory.integrable_finset_sum'
      intro j _
      -- Need to show each term f(cs j.succ) * indicator is integrable
      apply Integrable.const_mul
      apply integrable_indicator_const
      exact measurableSet_Ioc
    · apply integrable_finsum_of_finite
      intro j
      apply integrable_indicator_const
      exact measurableSet_Ioc
    · exact BoundedContinuousFunction.integrable f

    exact intervalIntegral.abs_integral_le_integral_abs _ _

  -- Now split the integral over (a,b] and its complement
  have integral_split : ∫ (ω : ℝ), |f ω - h ω| ∂↑(μs n) =
    ∫ (ω : ℝ) in (Set.Ioc a b), |f ω - h ω| ∂↑(μs n) +
    ∫ (ω : ℝ) in (Set.Ioc a b)ᶜ, |f ω - h ω| ∂↑(μs n) := by
    rw [← integral_add_compl (measurableSet_Ioc) (integrable_abs_sub _ _)]
    -- where integrable_abs_sub comes from f and h being integrable

  -- Since h vanishes outside (a,b], we have f - h = f on (a,b]ᶜ
  have h_vanishes : ∀ x ∉ Set.Ioc a b, h x = 0 := by
    intro x hx
    -- This follows from the definition of h as a sum over indicators
    simp [h]
    sorry

  -- Therefore |f - h| = |f| on (a,b]ᶜ
  have eq_on_compl : ∫ (ω : ℝ) in (Set.Ioc a b)ᶜ, |f ω - h ω| ∂↑(μs n) =
    ∫ (ω : ℝ) in (Set.Ioc a b)ᶜ, |f ω| ∂↑(μs n) := by
    apply integral_congr_ae
    filter_upwards [ae_of_all _ h_vanishes] with x hx
    simp [hx, sub_zero]

  -- Combine everything
  rw [integral_split, eq_on_compl] at triangle_ineq








  -- Apply triangle inequality using the blueprint strategy
  have key_ineq : dist (∫ ω, f ω ∂(μs n : Measure ℝ)) (∫ ω, f ω ∂(μ : Measure ℝ)) ≤
    ∫ ω in Ioc a b, |f ω - h ω| ∂(μs n : Measure ℝ) +
    ∫ ω in (Ioc a b)ᶜ, ‖f ω‖ ∂(μs n : Measure ℝ) := by
    rw [dist_eq_norm, ← integral_sub]
    · apply norm_integral_le_of_le_forall
      intro ω
      by_cases h_mem : ω ∈ Ioc a b
      · -- Inside [a,b]: use f_h_close
        simp [Set.indicator_of_mem h_mem, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr h_mem)]
        rw [add_zero]
        exact le_abs_self _
      · -- Outside [a,b]: h vanishes, so |f - h| = |f - 0| = |f|
        simp [Set.indicator_of_not_mem h_mem, Set.indicator_of_mem (Set.mem_compl h_mem)]
        rw [zero_add, sub_zero]
        rfl
    · exact BoundedContinuousFunction.integrable f
    · exact BoundedContinuousFunction.integrable f

  -- Bound the first integral by ε
  have bound₁ : ∫ ω in Ioc a b, |f ω - h ω| ∂(μs n : Measure ℝ) ≤ ε / 2 := by
    apply integral_le_of_forall_le
    · exact ae_of_all _ (fun ω => abs_nonneg _)
    · intro ω h_mem
      exact le_of_lt (f_h_close ω h_mem)

  -- Bound the second integral using CDF bounds
  have bound₂ : ∫ ω in (Ioc a b)ᶜ, ‖f ω‖ ∂(μs n : Measure ℝ) ≤ ε / 2 := by
    have decomp : (Ioc a b)ᶜ = Set.Iic a ∪ Set.Ioi b := by
      ext ω
      simp [Set.Ioc, Set.compl_def]
      tauto
    rw [decomp, Set.integral_union]
    · have bound_left : ∫ ω in Set.Iic a, ‖f ω‖ ∂(μs n : Measure ℝ) ≤
          K * (μs n : Measure ℝ) (Set.Iic a) := by
        apply integral_le_measure_mul_sup_norm
        exact hK_bound
      have bound_right : ∫ ω in Set.Ioi b, ‖f ω‖ ∂(μs n : Measure ℝ) ≤
          K * (μs n : Measure ℝ) (Set.Ioi b) := by
        apply integral_le_measure_mul_sup_norm
        exact hK_bound
      -- Use CDF bounds and the choice of N₁
      sorry -- Complete using Fa_small, Fb_large, and hN₁
    · exact Set.disjoint_Iic_Ioi_of_lt a_lt_b

  -- Combine bounds
  linarith [key_ineq, bound₁, bound₂]





  -- Bound |∫f dμ - ∫h dμ| and |∫f dμn - ∫h dμn|
  have bound_μ : |∫ x, f x ∂μ - ∫ x, h x ∂μ| ≤ (1 + 2 * ‖f‖_∞) * ε := by
    sorry -- Use triangle inequality and boundedness

  have bound_μs : ∀ n, |∫ x, f x ∂(μs n) - ∫ x, h x ∂(μs n)| ≤ (1 + 2 * ‖f‖_∞) * ε := by
    sorry -- Similar bound for μs n

  -- Express ∫h dμ and ∫h dμn using Lemma 4.6
  have h_integral_μ : ∫ x, h x ∂μ = ∑ j : Fin k, f (cs j.succ) * (μ.cdf (cs j.succ) - μ.cdf (cs j)) := by
    sorry -- Use Lemma 4.6

  have h_integral_μs : ∀ n, ∫ x, h x ∂(μs n) =
    ∑ j : Fin k, f (cs j.succ) * ((μs n).cdf (cs j.succ) - (μs n).cdf (cs j)) := by
    sorry -- Use Lemma 4.6

  -- Use convergence at continuity points
  have h_conv : Tendsto (fun n ↦ ∫ x, h x ∂(μs n)) atTop (𝓝 (∫ x, h x ∂μ)) := by
    rw [h_integral_μ]
    simp_rw [h_integral_μs]
    -- Each term converges since cs j ∈ D and cs j.succ ∈ D
    apply tendsto_finset_sum
    intro j _
    apply Tendsto.const_mul
    apply Tendsto.sub
    · exact h (cs j.succ) (cs_in_D j.succ)
    · exact h (cs j) (cs_in_D j)

  -- Combine all bounds
  rw [tendsto_atTop_nhds]
  intros δ δ_pos

  -- Choose N large enough for h convergence
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (tendsto_atTop_nhds.mp h_conv δ δ_pos)

  use N₁
  intros n hn

  -- Triangle inequality
  calc |∫ x, f x ∂(μs n) - ∫ x, f x ∂μ|
    ≤ |∫ x, f x ∂(μs n) - ∫ x, h x ∂(μs n)| +
      |∫ x, h x ∂(μs n) - ∫ x, h x ∂μ| +
      |∫ x, h x ∂μ - ∫ x, f x ∂μ| := by
        sorry -- Triangle inequality
    _ ≤ (1 + 2 * ‖f‖_∞) * ε + δ + (1 + 2 * ‖f‖_∞) * ε := by
        sorry -- Apply bounds
    _ < δ + 2 * (1 + 2 * ‖f‖_∞) * ε := by
        sorry -- Arithmetic

end weak_convergence_cdf


section levy_prokhorov_metric

open MeasureTheory Filter Topology

variable (F G :CumulativeDistributionFunction)

namespace CumulativeDistributionFunction

lemma tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto (fun i ↦ (Fs i).probabilityMeasure) atTop (𝓝 G.probabilityMeasure)
      ↔ ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  constructor
  · intro h x hGx
    have key := @tendsto_apply_of_tendsto_of_continuousAt ℕ atTop
                (fun i ↦ (Fs i).probabilityMeasure) G.probabilityMeasure h x
    simp_all
  · intro h
    apply tendsto_of_forall_continuousAt_tendsto_cdf
    simpa using h

noncomputable def equiv_levyProkhorov :
    CumulativeDistributionFunction ≃ LevyProkhorov (ProbabilityMeasure ℝ) :=
  equiv_probabilityMeasure.trans (LevyProkhorov.equiv (ProbabilityMeasure ℝ)).symm

noncomputable instance : MetricSpace CumulativeDistributionFunction := by
  apply MetricSpace.induced equiv_levyProkhorov
  · intro F G h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using h
  · exact levyProkhorovDist_metricSpace_probabilityMeasure

noncomputable def homeomorph_levyProkhorov :
    CumulativeDistributionFunction ≃ₜ LevyProkhorov (ProbabilityMeasure ℝ) :=
  Equiv.toHomeomorphOfIsInducing equiv_levyProkhorov ⟨rfl⟩

noncomputable def homeomorph_probabilityMeasure :
    CumulativeDistributionFunction ≃ₜ ProbabilityMeasure ℝ :=
  homeomorph_levyProkhorov.trans homeomorph_probabilityMeasure_levyProkhorov.symm

lemma homeomorph_probabilityMeasure_apply_eq (F : CumulativeDistributionFunction) :
    homeomorph_probabilityMeasure F = F.probabilityMeasure :=
  rfl

/-- The standard characterization of convergence of cumulative distribution functions. -/
lemma tendsto_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto Fs atTop (𝓝 G) ↔
      ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  rw [← tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto]
  constructor
  · intro h
    simp_rw [← homeomorph_probabilityMeasure_apply_eq]
    apply homeomorph_probabilityMeasure.continuous.continuousAt.tendsto.comp h
  · intro h
    convert homeomorph_probabilityMeasure.symm.continuous.continuousAt.tendsto.comp h
    · ext1 i
      exact EquivLike.inv_apply_eq_iff_eq_apply.mp rfl
    · exact EquivLike.inv_apply_eq_iff_eq_apply.mp rfl

end CumulativeDistributionFunction

end levy_prokhorov_metric



section continuous_mulAction

namespace CumulativeDistributionFunction

lemma continuous_mulAction :
    Continuous fun (⟨A, F⟩ : AffineIncrEquiv × CumulativeDistributionFunction) ↦ A • F := by
  rw [continuous_iff_seqContinuous]
  intro AFs BG h_lim
  rw [tendsto_iff_forall_continuousAt_tendsto]
  intro x hBGx
  simp only [Function.comp_apply, mulAction_apply_eq]
  sorry -- **Issue #54** (action-on-cdf-continuous)

end CumulativeDistributionFunction

end continuous_mulAction
