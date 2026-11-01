import Mathlib
import Architect

namespace SkolemMahlerLechTheorem

/-- The arithmetic progression `{a + d * n | n : ℕ}`. -/
def arithProg (a d : ℕ) : Set ℕ :=
  Set.range fun n : ℕ => a + d * n

end SkolemMahlerLechTheorem

open Filter Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜} {r : ENNReal}

/-- An accumulation point of zeros at the center forces vanishing on the whole series ball.
The isolated zeros principle makes the series vanish locally, and coefficient uniqueness
propagates vanishing across its convergence ball. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem zero_on_series_ball (hp : HasFPowerSeriesOnBall f p x r)
    (hz : ∃ᶠ z in 𝓝[≠] x, f z = 0) : ∀ z ∈ Metric.eball x r, f z = 0 := by
  have he : ∀ᶠ z in 𝓝 x, f z = 0 :=
    hp.analyticAt.frequently_zero_iff_eventually_zero.mp hz
  have h0 : HasFPowerSeriesAt (0 : 𝕜 → E) p x := hp.hasFPowerSeriesAt.congr he
  intro z hz
  have A := hp.hasSum_sub hz
  have B : HasSum (fun n : ℕ => p n fun _ : Fin n => z - x) 0 := by
    convert hasSum_zero (α := E) using 1
    ext n
    exact h0.apply_eq_zero n _
  exact A.unique B


/-- A compact zero set in a common domain obeys the finite-or-identically-zero dichotomy
when every recentered series ball contains that domain. An infinite compact zero set has
an accumulation point, so the preceding lemma forces vanishing throughout the domain. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem compact_zeros_finite_or_all {s : Set 𝕜}
    (hc : IsCompact {x ∈ s | f x = 0})
    (hs : ∀ x ∈ s, ∃ (q : FormalMultilinearSeries 𝕜 𝕜 E) (r : ENNReal),
      HasFPowerSeriesOnBall f q x r ∧ s ⊆ Metric.eball x r) :
    {x ∈ s | f x = 0}.Finite ∨ ∀ x ∈ s, f x = 0 := by
  classical
  by_cases hfin : {x ∈ s | f x = 0}.Finite
  · exact Or.inl hfin
  · right
    have hi : {x ∈ s | f x = 0}.Infinite := hfin
    obtain ⟨x, hx, hacc⟩ := exists_nhds_ne_inf_principal_neBot hc hi
    have hz : ∃ᶠ z in 𝓝[≠] x, f z = 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨z, hzU, hzs, hzf⟩ := (Filter.inf_principal_neBot_iff.mp hacc) U hU
      exact ⟨z, hzU, hzf⟩
    obtain ⟨q, r, hq, hsub⟩ := hs x hx.1
    exact fun z hzs => zero_on_series_ball hq hz z (hsub hzs)

/-- An injectively indexed sequence in the common domain either has finitely many zero values or
is identically zero there. This is the compact zero dichotomy pulled back along the sequence. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem compact_indexed_zeros_finite_or_all {s : Set 𝕜} (a : ℕ → 𝕜)
    (ha : Function.Injective a) (has : ∀ n, a n ∈ s)
    (hc : IsCompact {x ∈ s | f x = 0})
    (hs : ∀ x ∈ s, ∃ (q : FormalMultilinearSeries 𝕜 𝕜 E) (r : ENNReal),
      HasFPowerSeriesOnBall f q x r ∧ s ⊆ Metric.eball x r) :
    {n | f (a n) = 0}.Finite ∨ ∀ n, f (a n) = 0 := by
  rcases compact_zeros_finite_or_all hc hs with h | h
  · left
    have hpre : (a ⁻¹' {x ∈ s | f x = 0}).Finite := h.preimage ha.injOn
    convert hpre using 1
    ext n
    simp [has n]
  · exact Or.inr fun n => h (a n) (has n)

/-- On the p-adic unit ball, sufficiently large local analytic expansions give the
finite-or-total zero dichotomy for natural indices. Compactness follows from properness,
and the ultrametric inequality puts the whole unit ball in each expansion ball. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem padic_indexed_zeros_finite_or_all (p : ℕ) [Fact (Nat.Prime p)]
    (f : ℚ_[p] → ℚ_[p])
    (hs : ∀ x ∈ Metric.closedBall (0 : ℚ_[p]) 1,
      ∃ (q : FormalMultilinearSeries ℚ_[p] ℚ_[p] ℚ_[p]) (r : ENNReal),
        HasFPowerSeriesOnBall f q x r ∧ (1 : ENNReal) < r) :
    {n : ℕ | f n = 0}.Finite ∨ ∀ n : ℕ, f n = 0 := by
  let s := Metric.closedBall (0 : ℚ_[p]) 1
  have hs' : ∀ x ∈ s, ∃ (q : FormalMultilinearSeries ℚ_[p] ℚ_[p] ℚ_[p]) (r : ENNReal),
      HasFPowerSeriesOnBall f q x r ∧ s ⊆ Metric.eball x r := by
    intro x hx
    obtain ⟨q, r, hq, hr⟩ := hs x hx
    refine ⟨q, r, hq, ?_⟩
    intro y hy
    rw [Metric.mem_eball, edist_dist]
    apply lt_of_le_of_lt _ hr
    have hd : dist y x ≤ 1 := by
      change dist x 0 ≤ 1 at hx
      change dist y 0 ≤ 1 at hy
      apply (IsUltrametricDist.dist_triangle_max y 0 x).trans
      apply max_le
      · exact hy
      · simpa [dist_comm] using hx
    simpa using ENNReal.ofReal_le_ofReal hd
  have hcont : ContinuousOn f s := by
    intro x hx
    obtain ⟨q, r, hq, _⟩ := hs' x hx
    exact hq.analyticAt.continuousAt.continuousWithinAt
  have hc : IsCompact {x ∈ s | f x = 0} := by
    have hclosed : IsClosed {x ∈ s | f x = 0} := by
      simpa using hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton
    exact (isCompact_closedBall (0 : ℚ_[p]) 1).of_isClosed_subset hclosed (fun _ h => h.1)
  apply compact_indexed_zeros_finite_or_all (a := fun n : ℕ => (n : ℚ_[p]))
      Nat.cast_injective _ hc hs'
  intro n
  change dist (n : ℚ_[p]) 0 ≤ 1
  rw [dist_zero_right]
  simpa [PadicInt.norm_def, PadicInt.coe_natCast] using PadicInt.norm_le_one (n : ℤ_[p])

/-- Auxiliary padic single ball dichotomy step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem padic_single_ball_dichotomy (p : ℕ) [Fact (Nat.Prime p)]
    (f : ℚ_[p] → ℚ_[p]) (q : FormalMultilinearSeries ℚ_[p] ℚ_[p] ℚ_[p])
    (r : ENNReal) (hf : HasFPowerSeriesOnBall f q 0 r) (hr : (3 : ENNReal) ≤ r) :
    {n : ℕ | f n = 0}.Finite ∨ ∀ n : ℕ, f n = 0 := by
  apply padic_indexed_zeros_finite_or_all p f
  intro x hx
  have hx' : (‖x‖₊ : ENNReal) ≤ 1 := by
    have h : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact_mod_cast h
  have h3 : (‖x‖₊ : ENNReal) < 3 := lt_of_le_of_lt hx' (by norm_num)
  have hf3 := hf.mono (by norm_num : (0 : ENNReal) < 3) hr
  have hfx := hf3.changeOrigin h3
  refine ⟨q.changeOrigin x, 3 - ‖x‖₊, ?_, ?_⟩
  · simpa using hfx
  · have hle : (2 : ENNReal) ≤ 3 - ‖x‖₊ := by
      calc
        (2 : ENNReal) = 3 - 1 := by symm; exact ENNReal.sub_eq_of_eq_add (by simp) (by norm_num)
        _ ≤ 3 - ‖x‖₊ := tsub_le_tsub_left hx' _
    exact lt_of_lt_of_le (by norm_num) hle

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
  [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- Auxiliary exp scalar series step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem exp_scalar_series (a : 𝔸) (L : 𝔸 →L[𝕂] 𝕂)
    (hpos : 0 < (NormedSpace.expSeries 𝕂 𝔸).radius) :
    ∃ (q : FormalMultilinearSeries 𝕂 𝕂 𝕂),
      HasFPowerSeriesOnBall (fun x : 𝕂 => L (NormedSpace.exp (x • a))) q 0
        ((NormedSpace.expSeries 𝕂 𝔸).radius / ‖(ContinuousLinearMap.id 𝕂 𝕂).smulRight a‖ₑ) := by
  let u : 𝕂 →L[𝕂] 𝔸 := (ContinuousLinearMap.id 𝕂 𝕂).smulRight a
  have h := NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos (𝕂 := 𝕂) (𝔸 := 𝔸) hpos
  have h' := L.comp_hasFPowerSeriesOnBall (HasFPowerSeriesOnBall.compContinuousLinearMap (u := u) (x := 0) (by simpa using h))
  refine ⟨L.compFormalMultilinearSeries ((NormedSpace.expSeries 𝕂 𝔸).compContinuousLinearMap u), ?_⟩
  simpa [u, Function.comp_def] using h'

/-- Auxiliary padic exp index dichotomy step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem padic_exp_index_dichotomy (p : ℕ) [Fact (Nat.Prime p)]
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    (a : A) (L : A →L[ℚ_[p]] ℚ_[p])
    (hpos : 0 < (NormedSpace.expSeries ℚ_[p] A).radius)
    (hlarge : (3 : ENNReal) ≤ (NormedSpace.expSeries ℚ_[p] A).radius /
      ‖(ContinuousLinearMap.id ℚ_[p] ℚ_[p]).smulRight a‖ₑ) :
    {n : ℕ | L (NormedSpace.exp ((n : ℚ_[p]) • a)) = 0}.Finite ∨
      ∀ n : ℕ, L (NormedSpace.exp ((n : ℚ_[p]) • a)) = 0 := by
  obtain ⟨q, hq⟩ := exp_scalar_series a L hpos
  exact padic_single_ball_dichotomy p _ q _ hq hlarge

/-- Auxiliary padic exp power dichotomy step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem padic_exp_power_dichotomy (p : ℕ) [Fact (Nat.Prime p)]
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    (a : A) (L : A →L[ℚ_[p]] ℚ_[p])
    (hpos : 0 < (NormedSpace.expSeries ℚ_[p] A).radius)
    (hlarge : (3 : ENNReal) ≤ (NormedSpace.expSeries ℚ_[p] A).radius /
      ‖(ContinuousLinearMap.id ℚ_[p] ℚ_[p]).smulRight a‖ₑ)
    (hball : ∀ n : ℕ, n • a ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℚ_[p] A).radius) :
    {n : ℕ | L (NormedSpace.exp a ^ n) = 0}.Finite ∨
      ∀ n : ℕ, L (NormedSpace.exp a ^ n) = 0 := by
  have hp : ∀ n : ℕ, NormedSpace.exp (n • a) = NormedSpace.exp a ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball
        ((Commute.refl a).smul_left n) (hball n) (by simpa using hball 1), ih, pow_succ]
  simpa only [Nat.cast_smul_eq_nsmul, hp] using padic_exp_index_dichotomy p a L hpos hlarge

open scoped Padic NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- Auxiliary factorial inv bound step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
lemma factorial_inv_bound (n : ℕ) :
    ‖((n.factorial : ℚ_[p])⁻¹)‖ ≤ (p : ℝ) ^ n := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr n.factorial_ne_zero),
    Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]
  exact pow_le_pow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) (padicValNat_factorial_le p n)

/-- Auxiliary padic exp radius pos step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
lemma padic_exp_radius_pos {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A] :
    0 < (NormedSpace.expSeries ℚ_[p] A).radius := by
  let r : ℝ≥0 := (p : ℝ≥0)⁻¹
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : 0 < (r : ℝ≥0∞) := by
    simp [r, (Fact.out : p.Prime).ne_zero]
  refine hr.trans_le ((NormedSpace.expSeries ℚ_[p] A).le_radius_of_bound (max 1 ‖(1 : A)‖) ?_)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [NormedSpace.expSeries, ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero]
  · have hcoef : ‖NormedSpace.expSeries ℚ_[p] A n‖ ≤ (p : ℝ)^n := by
      rw [NormedSpace.expSeries_eq_ofScalars]
      exact (FormalMultilinearSeries.ofScalars_norm_le A _ n (Nat.pos_of_ne_zero hn)).trans (factorial_inv_bound p n)
    calc
      ‖NormedSpace.expSeries ℚ_[p] A n‖ * (r : ℝ)^n ≤ (p : ℝ)^n * (r : ℝ)^n :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg (NNReal.coe_nonneg _) _)
      _ = 1 := by simp [r, ← mul_pow, hp.ne']
      _ ≤ max 1 ‖(1 : A)‖ := le_max_left _ _
open Set Filter Topology
open scoped ENNReal NNReal

/-- Auxiliary small exp data step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
 theorem small_exp_data (p : ℕ) [Fact p.Prime] {A : Type*}
    [NormedRing A] [NormedAlgebra ℚ_[p] A]
    (hpos : 0 < (NormedSpace.expSeries ℚ_[p] A).radius) :
    ∃ s ∈ 𝓝 (0 : A), ∀ a ∈ s,
      (3 : ℝ≥0∞) ≤ (NormedSpace.expSeries ℚ_[p] A).radius /
        ‖(ContinuousLinearMap.id ℚ_[p] ℚ_[p]).smulRight a‖ₑ ∧
      ∀ n : ℕ, n • a ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℚ_[p] A).radius := by
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  let q : ℝ≥0 := r / 4
  have hq0 : 0 < (q : ℝ≥0∞) := by
    simp only [ENNReal.coe_pos, q, div_pos_iff_of_pos_right (by norm_num : (0:ℝ≥0) < 4)]
    exact_mod_cast hr0
  refine ⟨Metric.eball 0 q, Metric.eball_mem_nhds 0 hq0, ?_⟩
  intro a ha
  have ha' : ‖a‖ₑ < q := by simpa [Metric.mem_eball, edist_eq_enorm_sub] using ha
  have hn : ‖(ContinuousLinearMap.id ℚ_[p] ℚ_[p]).smulRight a‖ₑ = ‖a‖ₑ := by
    change (‖(ContinuousLinearMap.id ℚ_[p] ℚ_[p]).smulRight a‖₊ : ℝ≥0∞) = (‖a‖₊ : ℝ≥0∞)
    rw [ContinuousLinearMap.nnnorm_smulRight_apply]
    simp
  constructor
  · rw [hn]
    apply (ENNReal.le_div_iff_mul_le (Or.inr (ne_of_gt hpos)) (Or.inl (enorm_ne_top (x := a)))).2
    have : (3 : ℝ≥0∞) * ‖a‖ₑ ≤ (r : ℝ≥0∞) := by
      calc
        _ ≤ 3 * (q : ℝ≥0∞) := mul_le_mul_left' ha'.le _
        _ ≤ (r : ℝ≥0∞) := by
          rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
          dsimp [q]
          apply NNReal.coe_le_coe.mp
          simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
          have hrnon : (0 : ℝ) ≤ (r : ℝ) := r.property
          linarith
    exact this.trans hr.le
  · intro n
    rw [Metric.mem_eball, edist_zero_right]
    have hnorm : ‖n • a‖ ≤ ‖a‖ := by
      rw [← Nat.cast_smul_eq_nsmul ℚ_[p], norm_smul]
      calc
        _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one ℚ_[p] n) (norm_nonneg _)
        _ = _ := one_mul _
    have henorm : ‖n • a‖ₑ ≤ ‖a‖ₑ := by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
    exact henorm.trans_lt (ha'.trans_le (by
      calc
        (q : ℝ≥0∞) ≤ r := by exact_mod_cast (div_le_self (show (0:ℝ≥0) ≤ r by positivity) (by norm_num : (1:ℝ≥0) ≤ 4))
        _ ≤ _ := hr.le))

open Filter Set
open scoped Topology

/-- Auxiliary exp local surj step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem exp_local_surj (p : ℕ) [Fact p.Prime] {A : Type*} [NormedRing A]
    [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    (hpos : 0 < (NormedSpace.expSeries ℚ_[p] A).radius)
    (s : Set A) (hs : s ∈ 𝓝 (0 : A)) :
    ∃ t ∈ 𝓝 (1 : A), ∀ x ∈ t, ∃ a ∈ s, NormedSpace.exp a = x := by
  have hd : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℚ_[p]] A) 0 :=
    hasStrictFDerivAt_exp_zero_of_radius_pos hpos
  have hm : Filter.map (NormedSpace.exp : A → A) (𝓝 0) = 𝓝 (1 : A) := by
    simpa using hd.map_nhds_eq_of_surj (by change LinearMap.id.range = ⊤; exact LinearMap.range_id)
  refine ⟨NormedSpace.exp '' s, ?_, ?_⟩
  · rw [← hm]
    exact image_mem_map hs
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

example (p : ℕ) [Fact p.Prime] {A : Type*} [NormedRing A]
    [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    (hpos : 0 < (NormedSpace.expSeries ℚ_[p] A).radius)
    (H : Subgroup Aˣ) (hH : IsCompact (H : Set Aˣ)) (x : H)
    (s : Set A) (hs : s ∈ 𝓝 (0 : A)) :
    ∃ n : ℕ, 0 < n ∧ ∃ a ∈ s, NormedSpace.exp a = ((x : Aˣ) : A)^n := by
  obtain ⟨t, ht, hp⟩ := exp_local_surj p hpos s hs
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hc : Continuous (fun x : H => ((x : Aˣ) : A)) := by fun_prop
  have ht' : (fun x : H => ((x : Aˣ) : A)) ⁻¹' t ∈ 𝓝 (1 : H) := by
    apply hc.continuousAt.tendsto
    simpa using ht
  have hf := (mapClusterPt_one_atTop_pow x).frequently ht'
  obtain ⟨n, hn, hx⟩ := frequently_atTop.mp hf 1
  refine ⟨n, hn, ?_⟩
  apply hp
  simpa using hx
/-- Auxiliary compact power dichotomy step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem compact_power_dichotomy (p : ℕ) [Fact p.Prime] {A : Type*} [NormedRing A]
    [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    (H : Subgroup Aˣ) (hH : IsCompact (H : Set Aˣ)) (x : H) :
    ∃ d : ℕ, 0 < d ∧ ∀ L : A →L[ℚ_[p]] ℚ_[p],
      {n : ℕ | L ((((x : Aˣ) : A) ^ d) ^ n) = 0}.Finite ∨
      ∀ n : ℕ, L ((((x : Aˣ) : A) ^ d) ^ n) = 0 := by
  have hpos := padic_exp_radius_pos p (A := A)
  obtain ⟨s, hs, hsmall⟩ := small_exp_data p (A := A) hpos
  obtain ⟨t, ht, hp⟩ := exp_local_surj p hpos s hs
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hc : Continuous (fun x : H => ((x : Aˣ) : A)) := by fun_prop
  have ht' : (fun x : H => ((x : Aˣ) : A)) ⁻¹' t ∈ 𝓝 (1 : H) := by
    apply hc.continuousAt.tendsto
    simpa using ht
  have hf := (mapClusterPt_one_atTop_pow x).frequently ht'
  obtain ⟨d, hd, hxd⟩ := frequently_atTop.mp hf 1
  obtain ⟨a, ha, he⟩ := hp _ (by simpa using hxd)
  refine ⟨d, hd, ?_⟩
  intro L
  obtain ⟨hlarge, hball⟩ := hsmall a ha
  simpa [he] using padic_exp_power_dichotomy p a L hpos hlarge hball

open Set

/-- Auxiliary compact units of compact monoid image step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
lemma compact_units_of_compact_monoid_image
    {R A : Type*} [Monoid R] [TopologicalSpace R] [CompactSpace R]
    [Monoid A] [TopologicalSpace A] [T1Space A] [ContinuousMul A]
    (f : R →* A) (hf : Continuous f) (u : Aˣ)
    (hu : (u : A) ∈ Set.range f) (hui : (↑u⁻¹ : A) ∈ Set.range f) :
    ∃ H : Subgroup Aˣ, IsCompact (H : Set Aˣ) ∧ u ∈ H := by
  let S : Submonoid A := (⊤ : Submonoid R).map f
  have hs : IsCompact (S : Set A) := by
    have : (S : Set A) = Set.range f := by ext x; simp [S]
    rw [this]
    exact isCompact_range hf
  refine ⟨S.units, Submonoid.units_isCompact hs, ?_⟩
  change (u : A) ∈ S ∧ (↑u⁻¹ : A) ∈ S
  constructor
  · simpa [S] using hu
  · simpa [S] using hui


open scoped Padic

/-- Auxiliary compact padic matrix units step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
lemma compact_padic_matrix_units (p : ℕ) [Fact p.Prime] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι ℚ_[p])ˣ)
    (hu : ∀ i j, ‖(u : Matrix ι ι ℚ_[p]) i j‖ ≤ 1)
    (hui : ∀ i j, ‖(↑u⁻¹ : Matrix ι ι ℚ_[p]) i j‖ ≤ 1) :
    ∃ H : Subgroup (Matrix ι ι ℚ_[p])ˣ, IsCompact (H : Set (Matrix ι ι ℚ_[p])ˣ) ∧ u ∈ H := by
  let f : Matrix ι ι ℤ_[p] →* Matrix ι ι ℚ_[p] := (PadicInt.Coe.ringHom (p := p)).mapMatrix.toMonoidHom
  letI : CompactSpace (Matrix ι ι ℤ_[p]) := by
    change CompactSpace (ι → ι → ℤ_[p])
    infer_instance
  refine compact_units_of_compact_monoid_image f ?_ u ?_ ?_
  · exact continuous_id.matrix_map continuous_subtype_val
  · refine ⟨fun i j => ⟨(u : Matrix ι ι ℚ_[p]) i j, hu i j⟩, ?_⟩
    rfl
  · refine ⟨fun i j => ⟨(↑u⁻¹ : Matrix ι ι ℚ_[p]) i j, hui i j⟩, ?_⟩
    rfl

open scoped Padic

/-- A finite set of rational numbers is integral at a common prime. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem finite_rat_integral_prime (s : Finset ℚ) :
    ∃ p : ℕ, ∃ hp : p.Prime, ∀ q ∈ s,
      letI : Fact p.Prime := ⟨hp⟩
      ‖(q : ℚ_[p])‖ ≤ 1 := by
  classical
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes ((s.sup fun q => q.den) + 1)
  refine ⟨p, hp, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro q hq
  apply Padic.norm_rat_le_one
  intro hdvd
  have hden : q.den ≤ s.sup (fun q => q.den) := Finset.le_sup (f := fun q => q.den) hq
  have hpos : 0 < q.den := Rat.den_pos q
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- Every rational matrix unit has a prime at which its image lies in a compact subgroup. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem rational_matrix_compact_prime (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι ℚ)ˣ) :
    ∃ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∃ H : Subgroup (Matrix ι ι ℚ_[p])ˣ, IsCompact (H : Set (Matrix ι ι ℚ_[p])ˣ) ∧
        Units.map (Rat.castHom ℚ_[p]).mapMatrix.toMonoidHom u ∈ H := by
  classical
  let s : Finset ℚ := (Finset.univ.image fun ij : ι × ι => (u : Matrix ι ι ℚ) ij.1 ij.2) ∪
    (Finset.univ.image fun ij : ι × ι => (↑u⁻¹ : Matrix ι ι ℚ) ij.1 ij.2)
  obtain ⟨p, hp, hs⟩ := finite_rat_integral_prime s
  refine ⟨p, hp, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  apply compact_padic_matrix_units
  · intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hs ((u : Matrix ι ι ℚ) i j) (by simp [s])
  · intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hs ((↑u⁻¹ : Matrix ι ι ℚ) i j) (by simp [s])

open scoped Matrix.Norms.Operator

/-- A rational matrix unit has a prime and a power with a uniform p-adic zero dichotomy. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem rational_matrix_power_dichotomy (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι ℚ)ˣ) :
    ∃ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∃ d : ℕ, 0 < d ∧ ∀ L : Matrix ι ι ℚ_[p] →L[ℚ_[p]] ℚ_[p],
        {n : ℕ | L ((((Units.map (Rat.castHom ℚ_[p]).mapMatrix.toMonoidHom u :
          (Matrix ι ι ℚ_[p])ˣ) : Matrix ι ι ℚ_[p]) ^ d) ^ n) = 0}.Finite ∨
        ∀ n : ℕ, L ((((Units.map (Rat.castHom ℚ_[p]).mapMatrix.toMonoidHom u :
          (Matrix ι ι ℚ_[p])ˣ) : Matrix ι ι ℚ_[p]) ^ d) ^ n) = 0 := by
  classical
  obtain ⟨p, hp, H, hH, hu⟩ := rational_matrix_compact_prime ι u
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, ?_⟩
  exact compact_power_dichotomy p H hH ⟨_, hu⟩

/-- Rational scalar linear outputs of matrix powers have a uniform residue dichotomy. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem embedded_matrix_scalar_dichotomy (F : Type*) [Field F] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι F)ˣ) (c : ι → ι → F) (p : ℕ) [Fact p.Prime] (φ : F →+* ℚ_[p])
    (H : Subgroup (Matrix ι ι ℚ_[p])ˣ) (hH : IsCompact (H : Set (Matrix ι ι ℚ_[p])ˣ))
    (hu : Units.map φ.mapMatrix.toMonoidHom u ∈ H) :
    ∃ d : ℕ, 0 < d ∧ ∀ r : ℕ,
      {n : ℕ | (∑ i, ∑ j, c i j * ((u : Matrix ι ι F) ^ (r+d*n)) i j) = 0}.Finite ∨
      ∀ n : ℕ, (∑ i, ∑ j, c i j * ((u : Matrix ι ι F) ^ (r+d*n)) i j) = 0 := by
  classical
  obtain ⟨d, hd, h⟩ := compact_power_dichotomy p H hH ⟨_, hu⟩
  refine ⟨d, hd, ?_⟩
  intro r
  let A : Matrix ι ι ℚ_[p] := ((Units.map (φ).mapMatrix.toMonoidHom u :
          (Matrix ι ι ℚ_[p])ˣ) : Matrix ι ι ℚ_[p])
  let l : Matrix ι ι ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] := {
    toFun := fun M => ∑ i, ∑ j, φ (c i j) * (A^r * M) i j
    map_add' := by intro M N; simp [mul_add, Finset.sum_add_distrib, mul_add]
    map_smul' := by intro a M; simp [Matrix.mul_smul, Finset.mul_sum, mul_left_comm] }
  let L : Matrix ι ι ℚ_[p] →L[ℚ_[p]] ℚ_[p] := l.toContinuousLinearMap
  have heq : ∀ n, L ((A^d)^n) = φ (∑ i, ∑ j, c i j * ((u : Matrix ι ι F) ^ (r+d*n)) i j : F) := by
    intro n
    dsimp [L, l]
    rw [← pow_mul, ← pow_add]
    change (∑ i, ∑ j, φ (c i j) * (((φ).mapMatrix (u : Matrix ι ι F)) ^ (r+d*n)) i j) = _
    rw [← map_pow]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul]
  have hz : ∀ n, L ((A^d)^n) = 0 ↔ (∑ i, ∑ j, c i j * ((u : Matrix ι ι F) ^ (r+d*n)) i j) = 0 := by
    intro n
    rw [heq, map_eq_zero_iff φ φ.injective]
  rcases h L with hf | ha
  · left
    convert hf using 1
    ext n
    exact (hz n).symm
  · right
    intro n
    exact (hz n).mp (ha n)


noncomputable section
universe u
variable {K : Type u} [Field K]

/-- Auxiliary recShift step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
def recShift (E : LinearRecurrence K) : Module.End K E.solSpace where
  toFun x := ⟨fun n => x.val (n+1), by
    intro n
    simpa only [show ∀ n d : ℕ, n + d + 1 = (n + 1) + d by omega] using x.property (n+1)⟩
  map_add' x y := by ext n; rfl
  map_smul' a x := by ext n; rfl

/-- Auxiliary recEval step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
def recEval (E : LinearRecurrence K) : E.solSpace →ₗ[K] K where
  toFun x := x.val 0
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Auxiliary rec orbit step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem rec_orbit (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (f : Module.End K V) (v : V) (q : V →ₗ[K] K), ∀ n, u n = q ((f^n) v) := by
  letI : FiniteDimensional K E.solSpace := FiniteDimensional.of_injective E.toInit.toLinearMap E.toInit.injective
  refine ⟨E.solSpace, inferInstance, inferInstance, inferInstance, recShift E, ⟨u, hu⟩, recEval E, ?_⟩
  intro n
  have h : ∀ n (x : E.solSpace) m, ((recShift E ^ n) x).val m = x.val (m+n) := by
    intro n
    induction n with
    | zero => intro x m; simp
    | succ n ih =>
      intro x m
      rw [pow_succ']
      change ((recShift E) ((recShift E ^ n) x)).val m = _
      change ((recShift E ^ n) x).val (m+1) = _
      rw [ih]
      rw [show m + 1 + n = m + (n + 1) by omega]
  change u n = ((recShift E ^ n) ⟨u,hu⟩).val 0
  rw [h]
  simp
open Filter

/-- Auxiliary stable restriction step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
 theorem stable_restriction {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ (N : ℕ) (S : Submodule K V) (e : S ≃ₗ[K] S),
      (∀ x : S, (e x : V) = f x) ∧ ∀ n x, (f ^ (N+n)) x ∈ S := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp f.eventually_iInf_range_pow_eq
  let S := LinearMap.range (f ^ N)
  have heq : LinearMap.range (f ^ (N+1)) = S := by
    dsimp [S]
    rw [← hN (N+1) (by omega), ← hN N (le_refl N)]
  have hinv : ∀ x ∈ S, f x ∈ S := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    rw [← heq]
    apply LinearMap.mem_range.mpr
    refine ⟨y, ?_⟩
    simp [pow_succ', Module.End.mul_apply]
  let g : S →ₗ[K] S := f.restrict hinv
  have hsurj : Function.Surjective g := by
    intro x
    have hx : (x : V) ∈ LinearMap.range (f ^ (N+1)) := by rw [heq]; exact x.property
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    let z : S := ⟨(f ^ N) y, LinearMap.mem_range_self _ _⟩
    refine ⟨z, Subtype.ext ?_⟩
    change f ((f ^ N) y) = x
    simpa [pow_succ', Module.End.mul_apply] using hy
  have hinj : Function.Injective g := LinearMap.injective_iff_surjective.mpr hsurj
  refine ⟨N, S, LinearEquiv.ofBijective g ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro x; rfl
  · intro n x
    have he : LinearMap.range (f ^ (N+n)) = S := by
      dsimp [S]
      rw [← hN (N+n) (by omega), ← hN N (le_refl N)]
    rw [← he]
    exact LinearMap.mem_range_self _ _

/-- Auxiliary stable orbit step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
 theorem stable_orbit {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (f : Module.End K V) (v : V) (l : V →ₗ[K] W) :
    ∃ (N : ℕ) (S : Submodule K V) (e : S ≃ₗ[K] S) (w : S) (q : S →ₗ[K] W),
      ∀ n, l ((f ^ (N+n)) v) = q ((e ^ n) w) := by
  obtain ⟨N, S, e, he, hs⟩ := stable_restriction f
  have hw : (f ^ N) v ∈ S := by simpa using hs 0 v
  let w : S := ⟨(f ^ N) v, hw⟩
  refine ⟨N, S, e, w, l.comp S.subtype, ?_⟩
  intro n
  have hh : ((e ^ n) w : V) = (f ^ n) ((f ^ N) v) := by
    induction n with
    | zero => simp [w]
    | succ n ih =>
      rw [pow_succ']
      change (e ((e ^ n) w) : V) = (f ^ (n+1)) ((f ^ N) v)
      rw [he, ih, pow_succ']
      rfl
  change l ((f ^ (N+n)) v) = l ((e ^ n) w : V)
  rw [hh, Nat.add_comm N n, pow_add]
  rfl

/-- Auxiliary rec stable orbit step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem rec_stable_orbit (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (N : ℕ) (e : V ≃ₗ[K] V) (v : V) (q : V →ₗ[K] K),
      ∀ n, u (N+n) = q ((e^n) v) := by
  obtain ⟨V, hV, hM, hF, f, v, q, h⟩ := rec_orbit E u hu
  letI := hV
  letI := hM
  letI := hF
  obtain ⟨N, S, e, w, l, hs⟩ := stable_orbit f v q
  refine ⟨S, inferInstance, inferInstance, inferInstance, N, e, w, l, ?_⟩
  intro n
  rw [h, hs]

/-- Auxiliary residue dichotomy eventual step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
lemma residue_dichotomy_eventual (P : ℕ → Prop) (d : ℕ) (hd : 0 < d)
    (h : ∀ r < d, {k : ℕ | P (r + d*k)}.Finite ∨ ∀ k, P (r+d*k)) :
    ∃ N, ∀ n, N ≤ n → (P (n+d) ↔ P n) := by
  classical
  have hbound : ∀ r < d, ∃ N, ∀ k ≥ N, (P (r+d*(k+1)) ↔ P (r+d*k)) := by
    intro r hr
    rcases h r hr with hf | ha
    · obtain ⟨b, hb⟩ := hf.bddAbove
      refine ⟨b+1, ?_⟩
      intro k hk
      have h1 : ¬ P (r+d*k) := by
        intro hp
        have := hb (show k ∈ {k : ℕ | P (r+d*k)} from hp)
        omega
      have h2 : ¬ P (r+d*(k+1)) := by
        intro hp
        have := hb (show k+1 ∈ {k : ℕ | P (r+d*k)} from hp)
        omega
      simp [h1,h2]
    · exact ⟨0, fun k _ => iff_of_true (ha (k+1)) (ha k)⟩
  choose B hB using hbound
  let B' : ℕ → ℕ := fun r => if hr : r < d then B r hr else 0
  let M := (Finset.range d).sup B'
  refine ⟨d*M, ?_⟩
  intro n hn
  have hr : n % d < d := Nat.mod_lt n hd
  have hBM : B (n%d) hr ≤ M := by
    have hle := Finset.le_sup (f := B') (Finset.mem_range.mpr hr)
    simpa [B', hr] using hle
  have hq : M ≤ n/d := by
    apply (Nat.le_div_iff_mul_le hd).2
    simpa [Nat.mul_comm] using hn
  have hh := hB (n%d) hr (n/d) (le_trans hBM hq)
  have heq : n % d + d * (n/d) = n := Nat.mod_add_div n d
  have heq' : n % d + d * (n/d+1) = n+d := by rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, heq]
  simpa only [heq, heq'] using hh

namespace SkolemMahlerLechTheorem

/-- Auxiliary periodic to progressions step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
lemma periodic_to_progressions (P : ℕ → Prop) [DecidablePred P] (N d : ℕ)
    (hd : 0 < d) (hper : ∀ n, N ≤ n → (P (n+d) ↔ P n)) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n | P n} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)), arithProg p.1 p.2 := by
  let s := (Finset.range N).filter P
  let bases := (Finset.range (N+d)).filter (fun a => N ≤ a ∧ P a)
  let t := bases.image (fun a => (a,d))
  have hstep : ∀ a, N ≤ a → ∀ k, (P (a + d*k) ↔ P a) := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hper _ (by omega), ih]
  refine ⟨s,t,?_⟩
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_union, Finset.mem_coe, Set.mem_iUnion]
  constructor
  · intro hn
    by_cases hN : n < N
    · left; simp [s, hN, hn]
    · right
      let a := N + (n-N)%d
      have haN : N ≤ a := by dsimp [a]; omega
      have hal : a < N+d := by dsimp [a]; have := Nat.mod_lt (n-N) hd; omega
      have heq : n = a + d*((n-N)/d) := by
        dsimp [a]
        have h := Nat.mod_add_div (n-N) d
        omega
      have haP : P a := by rw [heq, hstep a haN] at hn; exact hn
      refine ⟨(a,d), ?_, ?_⟩
      · simp [t, bases, hal, haN, haP]
      · exact ⟨(n-N)/d, heq.symm⟩
  · rintro (hs | ⟨⟨a,b⟩, ht, hp⟩)
    · exact (Finset.mem_filter.mp hs).2
    · simp only [t, Finset.mem_image] at ht
      obtain ⟨c, hc, heq⟩ := ht
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl,rfl⟩ := heq
      have hc' : N ≤ c ∧ P c := (Finset.mem_filter.mp hc).2
      obtain ⟨k, rfl⟩ := hp
      exact (hstep c hc'.1 k).2 hc'.2
end SkolemMahlerLechTheorem
noncomputable section
open scoped BigOperators

/-- Auxiliary generic scalar orbit matrix step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem generic_scalar_orbit_matrix {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : V ≃ₗ[F] V) (v : V) (q : V →ₗ[F] F) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (u : (Matrix ι ι F)ˣ)
      (c : ι → ι → F), ∀ n, q ((e ^ n) v) = ∑ i, ∑ j, c i j * ((u : Matrix ι ι F) ^ n) i j := by
  classical
  let b := Module.finBasis F V
  let f : Module.End F V := e.toLinearMap
  let U : (Module.End F V)ˣ := ⟨f, e.symm.toLinearMap, by ext x; simp [f], by ext x; simp [f]⟩
  let A := LinearMap.toMatrixAlgEquiv b
  let u := Units.map A.toRingEquiv.toMonoidHom U
  refine ⟨_, inferInstance, inferInstance, u, fun i j => q (b i) * b.repr v j, ?_⟩
  intro n
  have hv : (e ^ n) v = (f ^ n) v := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change e ((e ^ n) v) = f ((f ^ n) v)
      rw [ih]; rfl
  have hmat : (u : Matrix _ _ F) ^ n = A (f ^ n) := by simp [u, U, A, f, ← map_pow]
  rw [hv, hmat]
  have hq (x : V) : q x = ∑ i, b.repr x i * q (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hq ((f ^ n) (b _)), Finset.mul_sum]
  dsimp [A, LinearMap.toMatrixAlgEquiv_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.toMatrixAlgEquiv_apply]
  ring


/-- Auxiliary embedded recurrence sml step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
 theorem embedded_recurrence_sml (F : Type*) [Field F] (E : LinearRecurrence F) (u : ℕ → F)
    (hu : E.IsSolution u)
    (hrealize : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : (Matrix ι ι F)ˣ),
      ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
        ∃ (φ : F →+* ℚ_[p]) (H : Subgroup (Matrix ι ι ℚ_[p])ˣ),
          IsCompact (H : Set (Matrix ι ι ℚ_[p])ˣ) ∧ Units.map φ.mapMatrix.toMonoidHom A ∈ H) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  classical
  obtain ⟨V, hV, hM, hF, N, e, v, q, horbit⟩ := rec_stable_orbit E u hu
  letI := hV
  letI := hM
  letI := hF
  obtain ⟨ι, hι, hdι, A, c, hm⟩ := generic_scalar_orbit_matrix e v q
  letI := hι
  letI := hdι
  obtain ⟨p, hp, φ, H, hH, hA⟩ := hrealize ι A
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hres⟩ := embedded_matrix_scalar_dichotomy F ι A c p φ H hH hA
  have hres' : ∀ r < d, {k : ℕ | u (N + (r + d*k)) = 0}.Finite ∨
      ∀ k, u (N + (r + d*k)) = 0 := by
    intro r hr
    simpa only [horbit, hm] using hres r
  obtain ⟨M, hM⟩ := residue_dichotomy_eventual (fun n => u (N+n) = 0) d hd hres'
  apply SkolemMahlerLechTheorem.periodic_to_progressions (fun n => u n = 0) (N+M) d hd
  intro n hn
  have hh := hM (n-N) (by omega)
  have heq : N + (n-N) = n := by omega
  have heq2 : N + (n-N+d) = n+d := by omega
  simpa only [heq, heq2] using hh


open Finset

variable {K : Type*} [Field K]

/-- Auxiliary recurrence mem subfield step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem recurrence_mem_subfield (E : LinearRecurrence K) (u : ℕ → K)
    (hu : E.IsSolution u) (F : Subfield K)
    (hc : ∀ i, E.coeffs i ∈ F) (hi : ∀ i : Fin E.order, u i ∈ F) :
    ∀ n, u n ∈ F := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < E.order
    · exact hi ⟨n, hn⟩
    · have he : n - E.order + E.order = n := Nat.sub_add_cancel (Nat.le_of_not_gt hn)
      rw [← he, hu]
      apply F.sum_mem
      intro i _
      apply F.mul_mem (hc i)
      apply ih
      have := i.isLt
      omega

/-- Auxiliary recurrence lift subfield step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem recurrence_lift_subfield (E : LinearRecurrence K) (u : ℕ → K)
    (hu : E.IsSolution u) (F : Subfield K)
    (hc : ∀ i, E.coeffs i ∈ F) (hi : ∀ i : Fin E.order, u i ∈ F) :
    ∃ (E' : LinearRecurrence F) (v : ℕ → F), E'.IsSolution v ∧
      ∀ n, (v n : K) = u n := by
  let hm := recurrence_mem_subfield E u hu F hc hi
  let E' : LinearRecurrence F := ⟨E.order, fun i => ⟨E.coeffs i, hc i⟩⟩
  let v : ℕ → F := fun n => ⟨u n, hm n⟩
  refine ⟨E', v, ?_, fun _ => rfl⟩
  intro n
  apply Subtype.ext
  simpa [E', v] using hu n

/-- Auxiliary recurrence finitely generated subfield step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem recurrence_finitely_generated_subfield (E : LinearRecurrence K) (u : ℕ → K)
    (hu : E.IsSolution u) :
    ∃ (S : Finset K) (E' : LinearRecurrence (Subfield.closure (S : Set K)))
      (v : ℕ → Subfield.closure (S : Set K)), E'.IsSolution v ∧
      ∀ n, (v n : K) = u n := by
  classical
  let S : Finset K := Finset.univ.image E.coeffs ∪ Finset.univ.image (fun i : Fin E.order => u i)
  have hc : ∀ i, E.coeffs i ∈ Subfield.closure (S : Set K) := by
    intro i
    apply Subfield.subset_closure
    simp [S]
  have hi : ∀ i : Fin E.order, u i ∈ Subfield.closure (S : Set K) := by
    intro i
    apply Subfield.subset_closure
    simp [S]
  obtain ⟨E', v, hv, hval⟩ := recurrence_lift_subfield E u hu _ hc hi
  exact ⟨S, E', v, hv, hval⟩

/-- Auxiliary periodicity reduces to fg subfields step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem periodicity_reduces_to_fg_subfields [CharZero K]
    (hfg : ∀ (S : Finset K) (E : LinearRecurrence (Subfield.closure (S : Set K)))
      (v : ℕ → Subfield.closure (S : Set K)), E.IsSolution v →
        ∃ N d, 0 < d ∧ ∀ n, N ≤ n → (v (n+d) = 0 ↔ v n = 0))
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ N d, 0 < d ∧ ∀ n, N ≤ n → (u (n+d) = 0 ↔ u n = 0) := by
  obtain ⟨S, E', v, hv, hval⟩ := recurrence_finitely_generated_subfield E u hu
  obtain ⟨N, d, hd, hp⟩ := hfg S E' v hv
  refine ⟨N, d, hd, fun n hn => ?_⟩
  have hz : ∀ k, v k = 0 ↔ u k = 0 := by
    intro k
    constructor
    · intro h
      rw [← hval k, h]
      rfl
    · intro h
      apply Subtype.ext
      simpa [hval k] using h
  rw [← hz (n+d), ← hz n]
  exact hp n hn

/-- Auxiliary sml of finitely generated padic integrality step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
 theorem sml_of_finitely_generated_padic_integrality (K : Type*) [Field K]
    (hint : ∀ (S : Finset K) (T : Finset (Subfield.closure (S : Set K))),
       ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
        ∃ φ : Subfield.closure (S : Set K) →+* ℚ_[p], ∀ x ∈ T, ‖φ x‖ ≤ 1)
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  classical
  obtain ⟨S, E', v, hv, hval⟩ := recurrence_finitely_generated_subfield E u hu
  let F := Subfield.closure (S : Set K)
  have hrealize : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : (Matrix ι ι F)ˣ),
      ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
        ∃ (φ : F →+* ℚ_[p]) (H : Subgroup (Matrix ι ι ℚ_[p])ˣ),
          IsCompact (H : Set (Matrix ι ι ℚ_[p])ˣ) ∧ Units.map φ.mapMatrix.toMonoidHom A ∈ H := by
    intro ι _ _ A
    let T : Finset F := (Finset.univ.image fun ij : ι × ι => (A : Matrix ι ι F) ij.1 ij.2) ∪
      (Finset.univ.image fun ij : ι × ι => (↑A⁻¹ : Matrix ι ι F) ij.1 ij.2)
    obtain ⟨p, hp, φ, hφ⟩ := hint S T
    letI : Fact p.Prime := ⟨hp⟩
    refine ⟨p, hp, φ, ?_⟩
    apply compact_padic_matrix_units
    · intro i j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hφ ((A : Matrix ι ι F) i j) (by simp [T])
    · intro i j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hφ ((↑A⁻¹ : Matrix ι ι F) i j) (by simp [T])
  obtain ⟨s, t, ht⟩ := embedded_recurrence_sml F E' v hv hrealize
  refine ⟨s, t, ?_⟩
  convert ht using 1
  ext n
  change u n = 0 ↔ v n = 0
  constructor
  · intro h; apply Subtype.ext; simpa [hval n] using h
  · intro h; rw [← hval n, h]; rfl

open scoped Polynomial Padic

/-- A finite set of rational functions has a simultaneous regular point over any infinite field. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem ratfunc_finite_regular (F : Type*) [Field F] [Infinite F] (T : Finset (RatFunc F)) :
    ∃ a : F, ∀ t ∈ T, Polynomial.eval a t.denom ≠ 0 := by
  classical
  let P : F[X] := ∏ t ∈ T, t.denom
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t ht => RatFunc.denom_ne_zero t)
  obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card P hP
    ((Cardinal.nat_lt_aleph0 _).trans_le (Cardinal.aleph0_le_mk F))
  refine ⟨a, ?_⟩
  have hprod : ∏ t ∈ T, Polynomial.eval a t.denom ≠ 0 := by
    simpa only [P, Polynomial.eval_prod] using ha
  exact Finset.prod_ne_zero_iff.mp hprod

/-- A finite set of rational numbers is integral at a common prime. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem finite_rat_integral_prime' (s : Finset ℚ) :
    ∃ p : ℕ, ∃ hp : p.Prime, ∀ q ∈ s,
      letI : Fact p.Prime := ⟨hp⟩
      ‖(q : ℚ_[p])‖ ≤ 1 := by
  classical
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes ((s.sup fun q => q.den) + 1)
  refine ⟨p, hp, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro q hq
  apply Padic.norm_rat_le_one
  intro hdvd
  have hden : q.den ≤ s.sup (fun q => q.den) := Finset.le_sup (f := fun q => q.den) hq
  have hpos : 0 < q.den := Rat.den_pos q
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- A rational point and a common p-adic place make any finite family of rational
functions regular and integral. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem ratfunc_rat_regular_integral (T : Finset (RatFunc ℚ)) :
    ∃ (a : ℚ) (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      (∀ t ∈ T, Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (a : ℚ_[p]) t.denom ≠ 0) ∧
      (∀ t ∈ T, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) (a : ℚ_[p]) t‖ ≤ 1) := by
  classical
  obtain ⟨a, ha⟩ := ratfunc_finite_regular ℚ T
  obtain ⟨p, hp, hi⟩ := finite_rat_integral_prime' (T.image (RatFunc.eval (RingHom.id ℚ) a))
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨a, p, hp, ?_, ?_⟩
  · intro t ht
    change Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) ((algebraMap ℚ ℚ_[p]) a) _ ≠ 0
    rw [Polynomial.eval₂_at_apply]
    exact (map_ne_zero (algebraMap ℚ ℚ_[p])).2 (ha t ht)
  · intro t ht
    have h := hi (RatFunc.eval (RingHom.id ℚ) a t) (Finset.mem_image_of_mem _ ht)
    convert h using 1
    unfold RatFunc.eval
    change ‖Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) ((algebraMap ℚ ℚ_[p]) a) t.num / Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) ((algebraMap ℚ ℚ_[p]) a) t.denom‖ = _
    simp only [Polynomial.eval₂_at_apply, Polynomial.eval₂_id, map_div₀]
    change ‖(algebraMap ℚ ℚ_[p]) _ / (algebraMap ℚ ℚ_[p]) _‖ = ‖(algebraMap ℚ ℚ_[p]) (_ / _)‖
    rw [map_div₀]

/-- A finite set of multivariate nonzero polynomials has a common regular point over an
infinite field, even when there are infinitely many variables. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem mvpoly_finite_regular (F σ : Type*) [Field F] [Infinite F]
    (T : Finset (MvPolynomial σ F)) (hT : ∀ t ∈ T, t ≠ 0) :
    ∃ a : σ → F, ∀ t ∈ T, MvPolynomial.eval a t ≠ 0 := by
  classical
  let P : MvPolynomial σ F := ∏ t ∈ T, t
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr hT
  have hex : ∃ a : σ → F, MvPolynomial.eval a P ≠ 0 := by
    by_contra h
    push_neg at h
    apply hP
    apply MvPolynomial.funext
    intro a
    simpa using h a
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  have hprod : ∏ t ∈ T, MvPolynomial.eval a t ≠ 0 := by
    simpa only [P, MvPolynomial.eval_prod] using ha
  exact Finset.prod_ne_zero_iff.mp hprod

/-- Any finite family of quotients of multivariate rational polynomials admits a common
regular rational specialization whose values are integral in some p-adic field. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem mvpoly_quotients_regular_integral (σ ι : Type*) (T : Finset ι)
    (num den : ι → MvPolynomial σ ℚ) (hd : ∀ i ∈ T, den i ≠ 0) :
    ∃ (a : σ → ℚ) (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      (∀ i ∈ T, MvPolynomial.eval a (den i) ≠ 0) ∧
      (∀ i ∈ T, ‖((MvPolynomial.eval a (num i) / MvPolynomial.eval a (den i) : ℚ) : ℚ_[p])‖ ≤ 1) := by
  classical
  have hn : ∀ q ∈ T.image den, q ≠ 0 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact hd i hi
  obtain ⟨a, ha⟩ := mvpoly_finite_regular ℚ σ (T.image den) hn
  let v : ι → ℚ := fun i => MvPolynomial.eval a (num i) / MvPolynomial.eval a (den i)
  obtain ⟨p, hp, hv⟩ := finite_rat_integral_prime' (T.image v)
  refine ⟨a, p, hp, ?_, ?_⟩
  · intro i hi
    exact ha (den i) (Finset.mem_image_of_mem _ hi)
  · intro i hi
    exact hv (v i) (Finset.mem_image_of_mem _ hi)
open Set
open scoped Padic Topology

/-- The nonvanishing locus of any nonzero multivariate polynomial over a
nontrivially normed field is dense, with product topology on the tuple space. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem mvpoly_dense_nonzero (L ι : Type*) [NontriviallyNormedField L]
    (q : MvPolynomial ι L) (hq : q ≠ 0) :
    Dense {x : ι → L | MvPolynomial.eval x q ≠ 0} := by
  classical
  rw [dense_iff_inter_open]
  intro U hU ⟨x, hx⟩
  have hu : U ∈ 𝓝 x := hU.mem_nhds hx
  rw [nhds_pi, Filter.mem_pi] at hu
  obtain ⟨I, hI, t, ht, hsub⟩ := hu
  have hti : ∀ i, (t i).Infinite := fun i => infinite_of_mem_nhds (x i) (ht i)
  have hex : ∃ y : ι → L, y ∈ Set.pi Set.univ t ∧ MvPolynomial.eval y q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hq
    apply MvPolynomial.funext_set t hti
    intro y hy
    simpa using h y hy
  obtain ⟨y, hy, hyq⟩ := hex
  exact ⟨y, hsub (fun i hi => hy i (Set.mem_univ i)), hyq⟩

/-- Every nonempty open set of a finite-dimensional p-adic coordinate space
contains a tuple algebraically independent over Q. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem padic_independent_in_open (p : ℕ) [Fact p.Prime] (ι : Type*) [Finite ι] [Countable ι]
    (U : Set (ι → ℚ_[p])) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, AlgebraicIndependent ℚ x := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Countable (MvPolynomial ι ℚ) := by
    change Countable ((ι →₀ ℕ) →₀ ℚ)
    infer_instance
  let S := {q : MvPolynomial ι ℚ // q ≠ 0}
  let f : S → Set (ι → ℚ_[p]) := fun q =>
    {x | MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℚ_[p]) q.1) ≠ 0}
  have ho (q : S) : IsOpen (f q) := by
    exact isOpen_ne.preimage (MvPolynomial.continuous_eval _)
  have hd (q : S) : Dense (f q) := by
    apply mvpoly_dense_nonzero
    intro he
    apply q.2
    apply (MvPolynomial.map_injective (algebraMap ℚ ℚ_[p]) (RingHom.injective _))
    simpa using he
  have h := dense_iInter_of_isOpen ho hd
  obtain ⟨x, hx, hxU⟩ := h.exists_mem_open hU hne
  refine ⟨x, hxU, algebraicIndependent_iff.mpr ?_⟩
  intro q hq
  by_contra hqn
  have hxq := Set.mem_iInter.mp hx ⟨q, hqn⟩
  apply hxq
  change MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℚ_[p]) q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
  exact hq

/-- Every finite set in a finitely generated purely transcendental extension of Q
is integral under an embedding into a p-adic field. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem mv_fraction_integral (ι : Type*) [Finite ι] (T : Finset (FractionRing (MvPolynomial ι ℚ))) :
    ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ f : FractionRing (MvPolynomial ι ℚ) →+* ℚ_[p], ∀ t ∈ T, ‖f t‖ ≤ 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Countable ι := inferInstance
  let A := MvPolynomial ι ℚ
  let K := FractionRing A
  have hrepr (t : K) := IsFractionRing.div_surjective (A := A) t
  choose num den hden hrepr using hrepr
  have hdn (t : K) : den t ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (hden t)
  obtain ⟨a, p, hp, ha, hv⟩ := mvpoly_quotients_regular_integral ι K T num den
    (fun t ht => hdn t)
  letI : Fact p.Prime := ⟨hp⟩
  let j : ℚ →+* ℚ_[p] := algebraMap ℚ ℚ_[p]
  let F (q : A) (x : ι → ℚ_[p]) : ℚ_[p] := MvPolynomial.eval x (MvPolynomial.map j q)
  have hF (q : A) : F q (fun i => j (a i)) = j (MvPolynomial.eval a q) := by
    exact (MvPolynomial.map_eval j a q).symm
  have hzero (t : K) (ht : t ∈ T) : F (den t) (fun i => j (a i)) ≠ 0 := by
    rw [hF]
    exact (map_ne_zero j).2 (ha t ht)
  have heach (t : K) (ht : t ∈ T) :
      ∀ᶠ x in 𝓝 (fun i => j (a i)), ‖F (num t) x / F (den t) x‖ ≤ 1 := by
    have hc : ContinuousAt (fun x => F (num t) x / F (den t) x) (fun i => j (a i)) := by
      exact (MvPolynomial.continuous_eval _).continuousAt.div
        (MvPolynomial.continuous_eval _).continuousAt (hzero t ht)
    have ho : IsOpen (Metric.closedBall (0 : ℚ_[p]) 1) :=
      IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
    have hval : ‖F (num t) (fun i => j (a i)) / F (den t) (fun i => j (a i))‖ ≤ 1 := by
      rw [hF, hF, ← map_div₀]
      exact hv t ht
    have hm := hc (ho.mem_nhds (by simpa [Metric.mem_closedBall, dist_zero_right] using hval))
    filter_upwards [hm] with x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hall : ∀ᶠ x in 𝓝 (fun i => j (a i)), ∀ t ∈ T, ‖F (num t) x / F (den t) x‖ ≤ 1 :=
    (Filter.eventually_all_finset T).mpr heach
  obtain ⟨U, hUs, hUo, haU⟩ := mem_nhds_iff.mp hall
  obtain ⟨x, hxU, hxi⟩ := padic_independent_in_open p ι U hUo ⟨_, haU⟩
  let g : A →+* ℚ_[p] := (MvPolynomial.aeval x).toRingHom
  have hg : Function.Injective g := algebraicIndependent_iff_injective_aeval.mp hxi
  let f : K →+* ℚ_[p] := IsFractionRing.lift hg
  refine ⟨p, hp, f, ?_⟩
  intro t ht
  have hft : f t = F (num t) x / F (den t) x := by
    conv_lhs => rw [← hrepr t, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    change (MvPolynomial.aeval x) (num t) / (MvPolynomial.aeval x) (den t) = _
    simp only [F, j, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  rw [hft]
  exact hUs hxU t ht

/-- Skolem–Mahler–Lech for finite-type purely transcendental extensions of Q. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem mv_fraction_recurrence_sml (σ : Type) [Finite σ]
    (E : LinearRecurrence (FractionRing (MvPolynomial σ ℚ)))
    (u : ℕ → FractionRing (MvPolynomial σ ℚ)) (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  classical
  let F := FractionRing (MvPolynomial σ ℚ)
  apply embedded_recurrence_sml F E u hu
  intro ι _ _ A
  let T : Finset F := (Finset.univ.image fun ij : ι × ι => (A : Matrix ι ι F) ij.1 ij.2) ∪
    (Finset.univ.image fun ij : ι × ι => (↑A⁻¹ : Matrix ι ι F) ij.1 ij.2)
  obtain ⟨p, hp, φ, hφ⟩ := mv_fraction_integral σ T
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, φ, ?_⟩
  apply compact_padic_matrix_units
  · intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hφ ((A : Matrix ι ι F) i j) (by simp [T])
  · intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hφ ((↑A⁻¹ : Matrix ι ι F) i j) (by simp [T])
/-- Auxiliary finite eventually periodic step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem finite_eventually_periodic {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ N d : ℕ, 0 < d ∧ ∀ n ≥ N, (P i (n+d) ↔ P i n)) :
    ∃ N d : ℕ, 0 < d ∧ ∀ n ≥ N, ((∀ i ∈ s, P i (n+d)) ↔ ∀ i ∈ s, P i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,1,by omega, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨N,d,hd,hp⟩ := h a (by simp)
    obtain ⟨M,e,he,hq⟩ := ih (by intro i hi; exact h i (by simp [hi]))
    have hmult {Q : ℕ → Prop} {b c : ℕ} (hb : ∀ n ≥ b, Q (n+c) ↔ Q n)
        (k : ℕ) : ∀ n ≥ b, Q (n+c*k) ↔ Q n := by
      intro n hn
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, hb _ (by omega), ih]
    refine ⟨max N M, d*e, Nat.mul_pos hd he, ?_⟩
    intro n hn
    simp only [Finset.mem_insert, forall_eq_or_imp]
    rw [hmult hp e n (by omega)]
    have hh := hmult (Q := fun n => ∀ i ∈ s, P i n) (b := M) (c := e) hq d n (by omega)
    rw [Nat.mul_comm e d] at hh
    exact and_congr Iff.rfl hh

/-- Skolem–Mahler–Lech over a finite extension of the rational numbers. -/

@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem finite_extension_realized_sml (F : Type) (K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (hrealize : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : (Matrix ι ι F)ˣ),
      ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
        ∃ (φ : F →+* ℚ_[p]) (H : Subgroup (Matrix ι ι ℚ_[p])ˣ),
          IsCompact (H : Set (Matrix ι ι ℚ_[p])ˣ) ∧ Units.map φ.mapMatrix.toMonoidHom A ∈ H) (E : LinearRecurrence K) (u : ℕ → K)
    (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  classical
  obtain ⟨V, hV, hM, hF, N, e, v, q, horbit⟩ := rec_stable_orbit E u hu
  letI := hV
  letI := hM
  letI := hF
  letI : Module F V := Module.compHom V (algebraMap F K)
  letI : IsScalarTower F K V := IsScalarTower.of_compHom F K V
  letI : FiniteDimensional F V := FiniteDimensional.trans F K V
  let b := Module.finBasis F K
  let P : Fin (Module.finrank F K) → ℕ → Prop := fun i n => b.repr (u (N+n)) i = 0
  have hP : ∀ i ∈ Finset.univ, ∃ N d : ℕ, 0 < d ∧ ∀ n ≥ N, (P i (n+d) ↔ P i n) := by
    intro i _
    let qi : V →ₗ[F] F := (Finsupp.lapply i).comp (b.repr.toLinearMap.comp (q.restrictScalars F))
    obtain ⟨ι, hι, hdι, A, c, hm⟩ := generic_scalar_orbit_matrix (e.restrictScalars F) v qi
    letI := hι
    letI := hdι
    obtain ⟨p, hp, φ, H, hH, hA⟩ := hrealize ι A
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨d, hd, hres⟩ := embedded_matrix_scalar_dichotomy F ι A c p φ H hH hA
    have hpow (n : ℕ) : ((e.restrictScalars F) ^ n) v = (e ^ n) v := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ']
        change e (((e.restrictScalars F) ^ n) v) = e ((e ^ n) v)
        rw [ih]
    have heq (n : ℕ) : P i n = (∑ x, ∑ y, c x y * ((A : Matrix ι ι F)^n) x y = 0) := by
      dsimp [P, qi]
      rw [horbit]
      have hh := hm n
      rw [hpow] at hh
      exact propext (by simpa [qi] using congrArg (fun x : F => x = 0) hh)
    obtain ⟨M, hM⟩ := residue_dichotomy_eventual (P i) d hd (by
      intro r hr
      simpa only [heq] using hres r)
    exact ⟨M,d,hd,hM⟩
  obtain ⟨M,d,hd,hper⟩ := finite_eventually_periodic Finset.univ P hP
  have hz (n : ℕ) : (∀ i ∈ Finset.univ, P i n) ↔ u (N+n) = 0 := by
    simp only [Finset.mem_univ, true_implies, P]
    constructor
    · intro h
      apply b.repr.injective
      apply Finsupp.ext
      intro i
      simpa using h i
    · intro h; simp [h]
  apply SkolemMahlerLechTheorem.periodic_to_progressions (fun n => u n = 0) (N+M) d hd
  intro n hn
  have hh := hper (n-N) (by omega)
  rw [hz, hz] at hh
  have h1 : N + (n-N) = n := by omega
  have h2 : N + (n-N+d) = n+d := by omega
  simpa only [h1,h2] using hh


/-- Every finite extension of a finite-type purely transcendental field has SML. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem mv_fraction_finite_extension_sml (σ : Type) (K : Type*) [Finite σ] [Field K]
    [Algebra (FractionRing (MvPolynomial σ ℚ)) K]
    [FiniteDimensional (FractionRing (MvPolynomial σ ℚ)) K]
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  classical
  let F := FractionRing (MvPolynomial σ ℚ)
  apply finite_extension_realized_sml F K ?_ E u hu
  · intro ι _ _ A
    let T : Finset F := (Finset.univ.image fun ij : ι × ι => (A : Matrix ι ι F) ij.1 ij.2) ∪
      (Finset.univ.image fun ij : ι × ι => (↑A⁻¹ : Matrix ι ι F) ij.1 ij.2)
    obtain ⟨p, hp, φ, hφ⟩ := mv_fraction_integral σ T
    letI : Fact p.Prime := ⟨hp⟩
    refine ⟨p, hp, φ, ?_⟩
    apply compact_padic_matrix_units
    · intro i j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hφ ((A : Matrix ι ι F) i j) (by simp [T])
    · intro i j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hφ ((↑A⁻¹ : Matrix ι ι F) i j) (by simp [T])
section basis_glue
variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.EssFiniteType F K]
example : ∃ (s : Finset K), ∃ t ⊆ (s : Set K), IsTranscendenceBasis F ((↑) : t → K) := by
  classical
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F K
  haveI : Algebra.IsAlgebraic (Algebra.adjoin F (s : Set K)) K := by
    constructor
    intro x
    have hx : x ∈ IntermediateField.adjoin F (s : Set K) := by rw [hs]; trivial
    induction hx using IntermediateField.adjoin_induction F with
    | mem x hx => exact isAlgebraic_algebraMap (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin F (s : Set K))
    | algebraMap x =>
      exact isAlgebraic_algebraMap (algebraMap F (Algebra.adjoin F (s : Set K)) x)
    | add x y hx hy ix iy => exact ix.add iy
    | inv x hx ix => exact ix.inv
    | mul x y hx hy ix iy => exact ix.mul iy
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := F) (A := K) (s : Set K)
  exact ⟨s, t, ht, hb⟩

/-- Auxiliary finite transcendence basis step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
 theorem finite_transcendence_basis :
    ∃ (s : Set K), s.Finite ∧ IsTranscendenceBasis F ((↑) : s → K) ∧
      FiniteDimensional (IntermediateField.adjoin F s) K := by
  classical
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F K
  haveI : Algebra.IsAlgebraic (Algebra.adjoin F (s : Set K)) K := by
    constructor
    intro x
    have hx : x ∈ IntermediateField.adjoin F (s : Set K) := by rw [hs]; trivial
    induction hx using IntermediateField.adjoin_induction F with
    | mem x hx => exact isAlgebraic_algebraMap (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin F (s : Set K))
    | algebraMap x =>
      exact isAlgebraic_algebraMap (algebraMap F (Algebra.adjoin F (s : Set K)) x)
    | add x y hx hy ix iy => exact ix.add iy
    | inv x hx ix => exact ix.inv
    | mul x y hx hy ix iy => exact ix.mul iy
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := F) (A := K) (s : Set K)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin F t) K := by
    have heq : Set.range ((↑) : t → K) = t := by ext x; simp
    rw [← heq]; exact hb.isAlgebraic_field
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin F t) K :=
    Algebra.EssFiniteType.of_comp F _ K
  exact ⟨t, s.finite_toSet.subset ht, hb, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩

/-- Auxiliary pure field equiv step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem pure_field_equiv (s : Set K) (hi : AlgebraicIndependent F ((↑) : s → K)) :
    Nonempty (FractionRing (MvPolynomial s F) ≃ₐ[F] IntermediateField.adjoin F s) := by
  classical
  let A := IntermediateField.adjoin F s
  let x : s → A := fun i => ⟨i.1, IntermediateField.subset_adjoin F s i.2⟩
  let g : MvPolynomial s F →ₐ[F] A := MvPolynomial.aeval x
  have hg : Function.Injective g := by
    apply (algebraicIndependent_iff_injective_aeval).mp
    apply (AlgebraicIndependent.of_comp A.val)
    simpa [x, A] using hi
  let h : FractionRing (MvPolynomial s F) →+* A := IsFractionRing.lift hg
  have hc (z : F) : h (algebraMap F (FractionRing (MvPolynomial s F)) z) = algebraMap F A z := by
    rw [IsScalarTower.algebraMap_apply F (MvPolynomial s F), MvPolynomial.algebraMap_eq]
    exact (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z)
  let f : FractionRing (MvPolynomial s F) →ₐ[F] A := { h with commutes' := hc }
  have hs : f.fieldRange = ⊤ := by
    apply top_unique
    have H : ∀ y (hy : y ∈ IntermediateField.adjoin F s), (⟨y, hy⟩ : A) ∈ f.fieldRange := by
      intro y hy
      induction hy using IntermediateField.adjoin_induction F with
      | mem y hy =>
        change ∃ b, f b = ⟨y, _⟩
        refine ⟨algebraMap (MvPolynomial s F) (FractionRing (MvPolynomial s F)) (MvPolynomial.X (⟨y,hy⟩ : s)), ?_⟩
        apply Subtype.ext
        change ((h (algebraMap _ _ _)) : K) = y
        rw [IsFractionRing.lift_algebraMap]
        simp [g, x]
      | algebraMap y => exact f.fieldRange.algebraMap_mem y
      | add y z hy hz iy iz => exact add_mem iy iz
      | inv y hy iy => exact inv_mem iy
      | mul y z hy hz iy iz => exact mul_mem iy iz
    intro a _
    exact H a a.2
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, by
    intro a
    have : a ∈ f.fieldRange := by rw [hs]; trivial
    exact this⟩⟩

/-- Auxiliary finite pure field equiv step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem finite_pure_field_equiv (s : Set K) (hs : s.Finite)
    (hi : AlgebraicIndependent F ((↑) : s → K)) :
    ∃ n : ℕ, Nonempty (FractionRing (MvPolynomial (Fin n) F) ≃ₐ[F] IntermediateField.adjoin F s) := by
  letI : Finite s := hs
  let e := (Finite.equivFin s).symm
  obtain ⟨f⟩ := pure_field_equiv F K s hi
  exact ⟨Nat.card s, ⟨(IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv F e)).trans f⟩⟩

/-- Auxiliary fg transfer step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem fg_transfer (K : Type*) [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K]
    (P : Prop)
    (hbase : ∀ (n : ℕ) (alg : Algebra (FractionRing (MvPolynomial (Fin n) ℚ)) K),
      letI := alg
      FiniteDimensional (FractionRing (MvPolynomial (Fin n) ℚ)) K → P) : P := by
  classical
  obtain ⟨s, hs, hb, hfin⟩ := finite_transcendence_basis ℚ K
  letI : Finite s := hs.to_subtype
  let e : Fin (Nat.card s) ≃ s := (Finite.equivFin s).symm
  let x : Fin (Nat.card s) → K := Subtype.val ∘ e
  have hx : AlgebraicIndependent ℚ x := hb.1.comp e e.injective
  have hr : Set.range x = s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hy
      obtain ⟨i, hi⟩ := e.surjective ⟨y,hy⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  let A := IntermediateField.adjoin ℚ s
  letI : Algebra ℚ (FractionRing (MvPolynomial (Fin (Nat.card s)) ℚ)) := OreLocalization.instAlgebra
  let f : FractionRing (MvPolynomial (Fin (Nat.card s)) ℚ) ≃+* A := by
    exact hx.aevalEquivField.toRingEquiv.trans
      (IntermediateField.equivOfEq (congrArg (IntermediateField.adjoin ℚ) hr)).toRingEquiv
  letI : FiniteDimensional A K := hfin
  letI : Algebra (FractionRing (MvPolynomial (Fin (Nat.card s)) ℚ)) K :=
    ((algebraMap A K).comp f.toRingHom).toAlgebra
  have hf : FiniteDimensional (FractionRing (MvPolynomial (Fin (Nat.card s)) ℚ)) K := by
    apply Module.Finite.of_equiv_equiv f.symm (RingEquiv.refl K)
    ext z
    change (algebraMap A K) (f (f.symm z)) = (algebraMap A K) z
    rw [f.apply_symm_apply]
  exact hbase (Nat.card s) inferInstance hf
end basis_glue

/-- Auxiliary fg recurrence sml step. The result follows from the preceding algebraic and topological reductions. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem fg_recurrence_sml (K : Type*) [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K]
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  apply fg_transfer K
  intro n alg hf
  letI := alg
  letI := hf
  exact mv_fraction_finite_extension_sml (Fin n) K E u hu

/-- Full Skolem–Mahler–Lech theorem over arbitrary characteristic zero fields. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem general_sml (K : Type*) [Field K] [CharZero K]
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)),
        SkolemMahlerLechTheorem.arithProg p.1 p.2 := by
  classical
  let S : Finset K := Finset.univ.image E.coeffs ∪ Finset.univ.image (fun i : Fin E.order => u i)
  let F := IntermediateField.adjoin ℚ (S : Set K)
  letI : Algebra.EssFiniteType ℚ F := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_finset (F := ℚ) S)
  have hc : ∀ i, E.coeffs i ∈ F.toSubfield := by
    intro i
    apply IntermediateField.subset_adjoin
    simp [S]
  have hi : ∀ i : Fin E.order, u i ∈ F.toSubfield := by
    intro i
    apply IntermediateField.subset_adjoin
    simp [S]
  have hm := recurrence_mem_subfield E u hu F.toSubfield hc hi
  let E' : LinearRecurrence F := ⟨E.order, fun i => ⟨E.coeffs i, hc i⟩⟩
  let v : ℕ → F := fun n => ⟨u n, hm n⟩
  have hv : E'.IsSolution v := by
    intro n
    apply Subtype.ext
    simpa [E', v] using hu n
  obtain ⟨s,t,ht⟩ := fg_recurrence_sml F E' v hv
  refine ⟨s,t, ?_⟩
  convert ht using 1
  ext n
  constructor
  · intro hn; apply Subtype.ext; simpa [v] using hn
  · intro hn; simpa [v] using congrArg Subtype.val hn


namespace SkolemMahlerLechTheorem

/-- Skolem-Mahler-Lech theorem: the zero set of a linear recurrence sequence over a characteristic
zero field is a finite union of arithmetic progressions plus a finite exceptional set. The proof
descends to a finitely generated field and uses p-adic analytic interpolation. -/
@[blueprint "SkolemMahlerLechTheorem.MainTheorem"]
theorem MainTheorem (K : Type*) [Field K] [CharZero K] (E : LinearRecurrence K) (u : ℕ → K)
    (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)), arithProg p.1 p.2 := by
  exact general_sml K E u hu

end SkolemMahlerLechTheorem
