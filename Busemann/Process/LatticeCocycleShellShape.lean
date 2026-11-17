/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RecoveryAE
public import Busemann.Process.LatticeMeshCellAverages
public import Busemann.Probability.RealShortWeightWindows
import Busemann.Process.ShellLowerComparison
import Busemann.Process.ShellUpperComparison
import Mathlib.Tactic

/-! Recovering cocycle shape for a lattice action. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal NNReal Topology
namespace LPP.Busemann

private theorem card_actual_product (T U : Finset ℤ) :
    (T.product U).card = T.card * U.card := Finset.card_product T U

private theorem sum_axis_product (T : Finset ℤ) (g : Lattice → ℝ) :
    (∑ z ∈ T.product {0}, g z) = ∑ k ∈ T, g (k • finiteEdgeStep 0) := by
  calc
    _ = ∑ k ∈ T, ∑ l ∈ ({0} : Finset ℤ), g (k, l) := Finset.sum_product _ _ _
    _ = _ := by simp [finiteEdgeStep]

private theorem sum_product_axis (T : Finset ℤ) (g : Lattice → ℝ) :
    (∑ z ∈ ({0} : Finset ℤ).product T, g z) = ∑ k ∈ T, g (k • finiteEdgeStep 1) := by
  calc
    _ = ∑ k ∈ T, ∑ l ∈ ({0} : Finset ℤ), g (l, k) := Finset.sum_product_right _ _ _
    _ = _ := by simp [finiteEdgeStep]

/-- A recovering cocycle has sublinear centered fluctuations uniformly on each nonnegative shell. This is JR arXiv:1810.03580v3, Appendix B, Theorem B.3. -/
theorem ae_uniform_recovering_cocycle_shell_shape_of_action
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → Environment) (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hzero : ∀ ω, T 0 ω = ω) (hadd : ∀ z w ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ) (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) (hRec : recovers_weight_map_ae P weights B) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    letI : MeasurableSpace Ω := mΩ0
    let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
    let S : ℕ → Finset Lattice := fun n => insert ((n : ℤ), 0)
      (((Finset.Icc (0 : ℤ) (n : ℤ)).product (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 = (n : ℤ)))
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _)
        (fun x => |B 0 x ω - (u 0 ω * (x.1 : ℝ) + u 1 ω * (x.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let S : ℕ → Finset Lattice := fun n => insert ((n : ℤ), 0)
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product (Finset.Icc (0 : ℤ) (n : ℤ))).filter
      (fun x => x.1 + x.2 = (n : ℤ)))
  let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
  let Fbar : Lattice → Ω → ℝ := fun x s =>
    B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let a : ℕ → ℕ → ℕ → ℤ := fun j k n => ⌊(n : ℝ) * (k : ℝ) * δ j / 8⌋
  let R₁ : ℕ → ℕ → ℕ → Finset ℤ := fun j k n => Finset.Ico (a j k n) (a j (k + 1) n)
  let R₂ : ℕ → (ℕ × ℕ) → ℕ → Finset Lattice := fun j k n =>
    (R₁ j k.1 n).product (R₁ j k.2 n)
  let C : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
      (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
        (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
  let K : ℕ → Finset (ℕ × ℕ) := fun j =>
    (Finset.range (⌈8 / δ j⌉₊ + 1)).product (Finset.range (⌈8 / δ j⌉₊ + 1))
  let J : Finset (Finset (Fin 2)) := (Finset.univ : Finset (Fin 2)).powerset.erase ∅
  let G : ℕ → Finset (Finset (Fin 2) × (ℕ × ℕ)) := fun j => J.product (K j)
  let Rmask : ℕ → (Finset (Fin 2) × (ℕ × ℕ)) → ℕ → Finset Lattice := fun j p n =>
    (if (0 : Fin 2) ∈ p.1 then R₁ j p.2.1 n else {0}).product
      (if (1 : Fin 2) ∈ p.1 then R₁ j p.2.2 n else {0})
  change ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
    (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) /
        (n : ℝ)) atTop (𝓝 0)
  -- One event contains every mesh label and every real window tolerance.
  have hCells := ae_tendsto_mesh_centered_cell_averages_of_action P T hzero hadd hShift B hB hInt
  have hWindows := ae_eventually_small_real_short_weight_windows_of_weight_map μ hmoment P weights hWeightsMeas hMarginal
  filter_upwards [hCells, hWindows, hB.2.2, hRec] with s hcells hw hadd hrec
  change (∀ (j k : ℕ) (i : Fin 2), Tendsto (fun n : ℕ =>
      (∑ t ∈ R₁ j k n, Fbar (t • finiteEdgeStep i) s) /
        ((n : ℝ) * ((R₁ j k n).card : ℝ))) atTop (𝓝 0)) ∧
    (∀ (j : ℕ) (k : ℕ × ℕ), Tendsto (fun n : ℕ =>
      (∑ z ∈ R₂ j k n, Fbar z s) / ((n : ℝ) * ((R₂ j k n).card : ℝ)))
        atTop (𝓝 0)) at hcells
  let W : Fin 2 → ℝ → ℕ → ℝ := fun i d n =>
    (C n).sup' (by dsimp [C]; exact Finset.insert_nonempty _ _) (fun z =>
      (∑ t ∈ Finset.range (⌊(n : ℝ) * d⌋₊ + 1),
        |weights s (z + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
  change ∀ η : ℝ, 0 < η → ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ i : Fin 2,
      ∀ᶠ n : ℕ in atTop, W i d n < 2 * η at hw
  -- Recovery bounds the outgoing edges of -B; -B need not recover.
  let A : Lattice → Lattice → ℝ := fun x y => -B x y s
  let m : Fin 2 → ℝ := fun i => -u i s
  let V : Fin 2 → Lattice → ℝ := fun _ z => -weights s z
  let g : Lattice → ℝ := fun x =>
    -(B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ)))
  have hA : is_additive A := by
    intro x y z
    dsimp only [A]
    rw [← neg_add, hadd x y z]
  have hUpper (z : Lattice) (i : Fin 2) : A z (z + finiteEdgeStep i) ≤ V i z := by
    have hr := hrec z
    fin_cases i
    · have hh := min_le_left (B z (z + ((1 : ℤ), (0 : ℤ))) s)
        (B z (z + ((0 : ℤ), (1 : ℤ))) s)
      rw [hr] at hh
      simpa [A, V, finiteEdgeStep] using neg_le_neg hh
    · have hh := min_le_right (B z (z + ((1 : ℤ), (0 : ℤ))) s)
        (B z (z + ((0 : ℤ), (1 : ℤ))) s)
      rw [hr] at hh
      simpa [A, V, finiteEdgeStep] using neg_le_neg hh
  have hCenter (x : Lattice) :
      A 0 x - (m 0 * ((x.1 - (0 : Lattice).1 : ℤ) : ℝ) +
        m 1 * ((x.2 - (0 : Lattice).2 : ℤ) : ℝ)) = g x := by
    simp only [A, m, g, Prod.fst_zero, Prod.snd_zero, sub_zero]
    ring
  have hRaw (x : Lattice) : Fbar x s = -g x := by
    simp [Fbar, coord, Fin.sum_univ_two, g]
  have hRay (j k : ℕ) (i : Fin 2) : Tendsto (fun n : ℕ =>
      (∑ t ∈ R₁ j k n, g (t • finiteEdgeStep i)) /
        ((n : ℝ) * ((R₁ j k n).card : ℝ))) atTop (𝓝 0) := by
    have h := hcells.1 j k i
    simp_rw [hRaw] at h
    simpa only [Finset.sum_neg_distrib, neg_div, neg_neg, neg_zero] using h.neg
  have hRect (j : ℕ) (k : ℕ × ℕ) : Tendsto (fun n : ℕ =>
      (∑ z ∈ R₂ j k n, g z) / ((n : ℝ) * ((R₂ j k n).card : ℝ))) atTop (𝓝 0) := by
    have h := hcells.2 j k
    simp_rw [hRaw] at h
    simpa only [Finset.sum_neg_distrib, neg_div, neg_neg, neg_zero] using h.neg
  -- Every nonempty coordinate mask is genuinely one- or two-dimensional.
  have hMask (j : ℕ) (p : Finset (Fin 2) × (ℕ × ℕ)) (hp : p.1.Nonempty) :
      Tendsto (fun n : ℕ => (∑ z ∈ Rmask j p n, g z) /
        ((n : ℝ) * ((Rmask j p n).card : ℝ))) atTop (𝓝 0) := by
    by_cases h0 : (0 : Fin 2) ∈ p.1
    · by_cases h1 : (1 : Fin 2) ∈ p.1
      · simpa only [Rmask, h0, h1, ite_true, R₂] using hRect j p.2
      · have heq (n : ℕ) : (∑ z ∈ Rmask j p n, g z) /
            ((n : ℝ) * ((Rmask j p n).card : ℝ)) =
          (∑ t ∈ R₁ j p.2.1 n, g (t • finiteEdgeStep 0)) /
            ((n : ℝ) * ((R₁ j p.2.1 n).card : ℝ)) := by
          simp only [Rmask, h0, h1, ite_true, ite_false, sum_axis_product,
            card_actual_product, Finset.card_singleton, mul_one]
        exact (hRay j p.2.1 0).congr' (Eventually.of_forall (fun n => (heq n).symm))
    · have h1 : (1 : Fin 2) ∈ p.1 := by
        obtain ⟨i, hi⟩ := hp
        fin_cases i
        · exact (h0 hi).elim
        · exact hi
      have heq (n : ℕ) : (∑ z ∈ Rmask j p n, g z) /
            ((n : ℝ) * ((Rmask j p n).card : ℝ)) =
          (∑ t ∈ R₁ j p.2.2 n, g (t • finiteEdgeStep 1)) /
            ((n : ℝ) * ((R₁ j p.2.2 n).card : ℝ)) := by
        simp only [Rmask, h0, h1, ite_true, ite_false, sum_product_axis,
          card_actual_product, Finset.card_singleton, one_mul]
      exact (hRay j p.2.2 1).congr' (Eventually.of_forall (fun n => (heq n).symm))
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδ1 (j : ℕ) : δ j ≤ 1 := by
    dsimp only [δ]
    have hden : (1 : ℝ) ≤ (j : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg j)
    exact (div_le_one (by positivity : (0 : ℝ) < (j : ℝ) + 1)).2 hden
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / 16
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨d₀, hd₀, hd₀1, hsmall⟩ := hw η hη
  let M : ℝ := max |u 0 s| |u 1 s|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have htol : 0 < min d₀ (ε / (4 * (M + 1))) := lt_min hd₀ (by positivity)
  obtain ⟨j, hj⟩ := (hδlim.eventually (gt_mem_nhds htol)).exists
  have hj₀ : δ j ≤ d₀ := (hj.trans_le (min_le_left _ _)).le
  have hjε : δ j < ε / (4 * (M + 1)) := hj.trans_le (min_le_right _ _)
  have hDrift : δ j * M < ε / 4 := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (M + 1))).1 hjε
    have hd := hδ j
    nlinarith only [hh, hd]
  -- First bound all cells in both finite families, before selecting any cell.
  have hLowCells : ∀ᶠ n : ℕ in atTop, ∀ k ∈ K j,
      |(∑ z ∈ R₂ j k n, g z) / ((n : ℝ) * ((R₂ j k n).card : ℝ))| < η := by
    apply (K j).eventually_all.mpr
    intro k _
    have hh := (hRect j k).abs
    exact hh.eventually (by simpa only [abs_zero] using gt_mem_nhds hη)
  have hHighCells : ∀ᶠ n : ℕ in atTop, ∀ p ∈ G j,
      |(∑ z ∈ Rmask j p n, g z) / ((n : ℝ) * ((Rmask j p n).card : ℝ))| < η := by
    apply (G j).eventually_all.mpr
    intro p hp
    have hpJ := (Finset.mem_product.mp hp).1
    have hpne : p.1 ≠ ∅ := (Finset.mem_erase.mp hpJ).1
    have hh := (hMask j p (Finset.nonempty_iff_ne_empty.mpr hpne)).abs
    exact hh.eventually (by simpa only [abs_zero] using gt_mem_nhds hη)
  have hSize : ∀ᶠ n : ℕ in atTop, 8 ≤ (n : ℝ) * δ j := by
    have hh := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (8 / δ j))
    filter_upwards [hh] with n hn
    exact (div_le_iff₀ (hδ j)).1 hn
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hAll := hLowCells.and (hHighCells.and (hSize.and
    (hNpos.and ((hsmall (δ j) (hδ j) hj₀ 0).and (hsmall (δ j) (hδ j) hj₀ 1)))))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hAll
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hlow, hhigh, hsize, hnpos, hw0, hw1⟩ := hN n hn
  have hPoint (x : Lattice) (hx0 : 0 ≤ x.1) (hx1 : 0 ≤ x.2)
      (hxsum : x.1 + x.2 = (n : ℤ)) : |g x / (n : ℝ)| < ε := by
    obtain ⟨k, hk, _, _, hLower⟩ :=
      shell_point_lower_bound_by_rectangle A hA V hUpper m n (δ j) (hδ j) (hδ1 j) hsize x hx0 hx1 hxsum
    obtain ⟨p, hp, _, _, _, _, _, hUpper'⟩ :=
      shell_point_upper_bound_by_masked_rectangle A hA V hUpper m n (δ j) (hδ j) (hδ1 j) hsize x hx0 hx1 hxsum
    simp only [hCenter] at hLower hUpper'
    simp only [V, abs_neg, m] at hLower hUpper'
    change g x / (n : ℝ) ≥
      (∑ y ∈ R₂ j k n, g y) / ((n : ℝ) * ((R₂ j k n).card : ℝ)) -
        W 0 (δ j) n - W 1 (δ j) n - δ j * M at hLower
    change g x / (n : ℝ) ≤
      (∑ y ∈ Rmask j p n, g y) / ((n : ℝ) * ((Rmask j p n).card : ℝ)) +
        W 0 (δ j) n + W 1 (δ j) n + δ j * M at hUpper'
    have hL := (abs_lt.mp (hlow k hk)).1
    have hH := (abs_lt.mp (hhigh p hp)).2
    apply abs_lt.mpr
    constructor <;> dsimp only [η] at hw0 hw1 hL hH <;>
      linarith only [hLower, hUpper', hL, hH, hw0, hw1, hDrift, hε]
  -- Convert uniform pointwise bounds into the actual finite real supremum.
  have hShell (x : Lattice) (hx : x ∈ S n) :
      0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 = (n : ℤ) := by
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      simp
    · obtain ⟨hxprod, hxsum⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx0, hx1⟩ := Finset.mem_product.mp hxprod
      exact ⟨(Finset.mem_Icc.mp hx0).1, (Finset.mem_Icc.mp hx1).1, hxsum⟩
  have hSup : (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) <
        ε * (n : ℝ) := by
    apply (Finset.sup'_lt_iff (by dsimp [S]; exact Finset.insert_nonempty _ _)).mpr
    intro x hx
    obtain ⟨hx0, hx1, hxsum⟩ := hShell x hx
    have hh := hPoint x hx0 hx1 hxsum
    rw [abs_div, abs_of_pos hnpos] at hh
    have hh' := (div_lt_iff₀ hnpos).1 hh
    simpa only [g, abs_neg] using hh'
  have hSup0 : 0 ≤ (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) := by
    have hmem : ((n : ℤ), 0) ∈ S n := Finset.mem_insert_self _ _
    have hh := Finset.le_sup' (fun x : Lattice =>
      |B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) hmem
    exact (abs_nonneg _).trans hh
  have hResult := (div_lt_iff₀ hnpos).2 hSup
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hSup0 hnpos.le)] using hResult

end LPP.Busemann
