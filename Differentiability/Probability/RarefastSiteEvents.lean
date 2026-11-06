/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GeneralIntervals
public import LPP_Foundations.Analysis.ShapeSupportingFunctionals
public import LPP_Foundations.Probability.DisjointSupportEvents
public import Differentiability.Model.CoarsePercolationRegions
import Differentiability.Probability.RarefastConnectors
import Differentiability.Model.FiniteLevelStripCardinality
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Model.Paths.Translate
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-!
# Good coarse sites for rare fast crossings

Steps 1–5 of the proof of Proposition 3.4 of the differentiability preprint: good coarse
sites carry a heavy crossing in one of `T` disjoint translated blocks and connectors to both
forward neighbours; they are local to the coarse regions and independent at sup-distance
above ten.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- Equal weights at the vertices give equal path weights. -/
private theorem pathWeight_congr_vertices {u : Lattice} {e : ℕ × ℕ} (q : Path u e)
    (ω ω' : Environment) (h : ∀ i, ω (q.vertex i) = ω' (q.vertex i)) :
    pathWeight ω q = pathWeight ω' q := by
  unfold pathWeight
  exact Finset.sum_congr rfl fun i _ => h _

/-- A lattice vertex on a given level within `1/2` of a transverse target. -/
private theorem exists_level_vertex_near (a ρ : ℝ) (I : ℤ) :
    ∃ z : Lattice, z.1 + z.2 = I ∧ |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ 1 / 2 := by
  refine ⟨(⌊ρ + a * (I : ℝ) + 1 / 2⌋, I - ⌊ρ + a * (I : ℝ) + 1 / 2⌋), by dsimp only; omega, ?_⟩
  have h1 := Int.floor_le (ρ + a * (I : ℝ) + 1 / 2)
  have h2 := Int.lt_floor_add_one (ρ + a * (I : ℝ) + 1 / 2)
  show |(1 - a) * ((⌊ρ + a * (I : ℝ) + 1 / 2⌋ : ℤ) : ℝ) -
      a * (((I - ⌊ρ + a * (I : ℝ) + 1 / 2⌋ : ℤ)) : ℝ) - ρ| ≤ 1 / 2
  rw [Int.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Steps 1–5 of the proof of Proposition 3.4 of the differentiability preprint: from a positive
lower bound on the rare-fast crossing probability, good coarse sites with the required
witnesses. -/
theorem exists_rarefast_coarse_site_events
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t)) ^ (1/2:ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (R ε σ : ℝ) (hR : 0 < R) (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let slope : ℝ :=
      if σ = 1 then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
    let rho : Lattice → ℝ := fun z => (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    let f : Lattice → ℝ := fun z => H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) + slope * rho z
    let E : ℝ → ℕ → Set Environment := fun s n => {ω | ∃ u : Lattice,
      u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |rho (q.vertex i)| ≤ R * s) ∧
        f (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q < -(ε * s)}
    ∀ ζ : ℝ, 0 < ζ → ∀ p₀ : ℝ, 0 < p₀ →
    ∃ T : ℕ, 1 ≤ T ∧ ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∃ s₂ : ℝ, 1 ≤ s₂ ∧
    ∀ (s : ℝ) (n : ℕ), s₂ ≤ s → p₀ ≤ (environmentLaw μ).real (E s n) →
      let S : ℝ := 100 * (T : ℝ) * (R + 1) * (⌈s⌉₊ : ℝ)
      let L : ℕ := n + ⌈D₀ * s⌉₊
      let t : ℕ × ℕ → ℕ := fun v => v.1 + v.2
      let Y : ℕ × ℕ → ℝ := fun v => σ * ((v.1 + 2 * v.2 : ℕ) : ℝ) * S
      let Reg : ℕ × ℕ → Set Lattice := fun v =>
        {z | ((t v * L : ℕ) : ℤ) ≤ z.1 + z.2 ∧
          z.1 + z.2 ≤ (((t v + 1) * L : ℕ) : ℤ) ∧
          |rho z - Y v| ≤ 4 * S}
      ∃ G : ℕ × ℕ → Set Environment,
        (∀ v, MeasurableSet (G v)) ∧
        (∀ v, (environmentLaw μ).real ((G v)ᶜ) ≤ ζ) ∧
        (∀ F : Finset (ℕ × ℕ),
          (∀ u ∈ F, ∀ v ∈ F, u ≠ v →
            10 < Nat.dist u.1 v.1 ∨ 10 < Nat.dist u.2 v.2) →
          iIndepSet (fun v : {u : ℕ × ℕ // u ∈ F} => G v.1) (environmentLaw μ)) ∧
        (∀ v (ω ω' : Environment), (∀ z ∈ Reg v, ω z = ω' z) →
          (ω ∈ G v ↔ ω' ∈ G v)) ∧
        ∀ v, ∀ ω ∈ G v,
          (∃ c : ℝ, |c - Y v| + R * s ≤ S / 4 ∧
            ∃ u : Lattice, u.1 + u.2 = ((t v * L : ℕ) : ℤ) ∧
            ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
              (∀ i, |rho (q.vertex i) - c| ≤ R * s) ∧
              f (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q <
                -(ε * s)) ∧
          (∀ v' : ℕ × ℕ, (v' = v + (1, 0) ∨ v' = v + (0, 1)) →
            ∀ u u' : Lattice,
              u.1 + u.2 = ((t v * L + n : ℕ) : ℤ) → |rho u - Y v| ≤ S / 4 →
              u'.1 + u'.2 = (((t v + 1) * L : ℕ) : ℤ) → |rho u' - Y v'| ≤ S / 4 →
              ∃ e : ℕ × ℕ, ∃ q : Path u e,
                q.vertex (Fin.last (e.1 + e.2)) = u' ∧
                f (u' - u) - pathWeight ω q ≤ ε * s / 2 ∧
                ∀ i, |rho (q.vertex i) - Y v| ≤ 4 * S) := by
  intro H slope rho f E ζ hζ p₀ hp₀
  have hrho : ∀ z : Lattice, rho z = (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) := fun _ => rfl
  -- Step 1: the number of trials `T` with `(1 - p₀)^T < ζ/2`.
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hζ)
    (max_lt (by norm_num) (by linarith) : max 0 (1 - p₀) < 1)
  have hy0 : 0 ≤ max 0 (1 - p₀) := le_max_left _ _
  have hy1 : max 0 (1 - p₀) ≤ 1 := max_le (by norm_num) (by linarith)
  have hT : max 0 (1 - p₀) ^ (N + 1) < ζ / 2 :=
    (pow_le_pow_of_le_one hy0 hy1 (Nat.le_succ N)).trans_lt hN
  -- Steps 3–4: the connector scale for `C₀ = 200 T (R+1)`.
  have hT1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
  have hTR : 1 ≤ ((N + 1 : ℕ) : ℝ) * (R + 1) :=
    one_le_mul_of_one_le_of_one_le hT1 (by linarith)
  have hC₀ : 1 ≤ 200 * ((N + 1 : ℕ) : ℝ) * (R + 1) := by linarith
  obtain ⟨D₀, hDC, s₁, -, p, -, hpt, hconn⟩ :=
    exists_rarefast_connector_scale μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁
      ε σ (200 * ((N + 1 : ℕ) : ℝ) * (R + 1)) hε hσ hC₀
  have hD1 : 1 ≤ D₀ := by linarith
  obtain ⟨s₃, hs₃⟩ := eventually_atTop.1 (hpt.eventually (lt_mem_nhds
    (by linarith : 1 - ζ / 4 < (1 : ℝ))))
  refine ⟨N + 1, Nat.succ_pos N, D₀, hD1, max s₁ (max s₃ 1),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro s n hs hP S L t Y Reg
  -- Elementary scale facts.
  have hs1 : s₁ ≤ s := (le_max_left _ _).trans hs
  have hs3 : s₃ ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have hs0 : 1 ≤ s := ((le_max_right _ _).trans (le_max_right _ _)).trans hs
  have hspos : 0 < s := by linarith
  have hcs : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hcs2 : (⌈s⌉₊ : ℝ) ≤ 2 * s := by linarith [Nat.ceil_lt_add_one hspos.le]
  have hSdef : S = 100 * ((N + 1 : ℕ) : ℝ) * (R + 1) * (⌈s⌉₊ : ℝ) := rfl
  have hB0 : 0 ≤ (R + 1) * (⌈s⌉₊ : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hB3 : (0 : ℝ) ≤ 3 * ((R + 1) * (⌈s⌉₊ : ℝ)) := mul_nonneg (by norm_num) hB0
  have hRsB : R * s + 1 / 2 ≤ (R + 1) * (⌈s⌉₊ : ℝ) := by
    have := mul_le_mul_of_nonneg_left hcs hR.le
    linarith
  have hTB : (R + 1) * (⌈s⌉₊ : ℝ) ≤ ((N + 1 : ℕ) : ℝ) * ((R + 1) * (⌈s⌉₊ : ℝ)) :=
    le_mul_of_one_le_left hB0 hT1
  have hRc : 0 ≤ R * (⌈s⌉₊ : ℝ) := mul_nonneg hR.le (Nat.cast_nonneg _)
  have hSs : s ≤ S := by linarith
  have hSC : S ≤ 200 * ((N + 1 : ℕ) : ℝ) * (R + 1) * s := by
    rw [hSdef]
    have := mul_le_mul_of_nonneg_left hcs2
      (mul_nonneg (by positivity) (by linarith) : (0 : ℝ) ≤ 100 * ((N + 1 : ℕ) : ℝ) * (R + 1))
    linarith
  have hS0 : 0 < S := by linarith
  have hdpos : 0 < ⌈D₀ * s⌉₊ := Nat.ceil_pos.mpr (mul_pos (by linarith) hspos)
  have hL1 : 1 ≤ L := by show 1 ≤ n + ⌈D₀ * s⌉₊; omega
  have hlev : ∀ v : ℕ × ℕ, (((t v + 1) * L : ℕ) : ℤ) =
      ((t v * L + n : ℕ) : ℤ) + (⌈D₀ * s⌉₊ : ℤ) := by
    intro v
    show (((t v + 1) * (n + ⌈D₀ * s⌉₊) : ℕ) : ℤ) =
      ((t v * (n + ⌈D₀ * s⌉₊) + n : ℕ) : ℤ) + (⌈D₀ * s⌉₊ : ℤ)
    push_cast
    ring
  -- The base block `K` of the crossing event and its locality.
  obtain ⟨K, hKmem, -⟩ := exists_finset_signed_level_tube a (R * s) (fun _ => 0) 0 n
    (mul_pos hR hspos).le
  have hK : ∀ z, z ∈ K ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ (n : ℤ) ∧ |rho z| ≤ R * s := by
    intro z
    rw [hKmem z, hrho]
    simp only [sub_zero, zero_add, iff_self]
  have hEm : MeasurableSet (E s n) := by
    refine measurableSet_setOfPred.mpr ?_
    refine Measurable.exists fun u => Measurable.and measurable_const ?_
    refine Measurable.exists fun e => Measurable.and measurable_const ?_
    refine Measurable.exists fun q => Measurable.and measurable_const ?_
    exact measurableSet_setOfPred.mp
      (measurableSet_lt (measurable_const.sub (measurable_pathWeight q)) measurable_const)
  have hEdir : ∀ ω ω' : Environment, (∀ z ∈ K, ω z = ω' z) → ω ∈ E s n → ω' ∈ E s n := by
    intro ω ω' hag hω
    simp only [E, Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨u, hu, e, he, q, hq, hdef⟩ := hω
    refine ⟨u, hu, e, he, q, hq, ?_⟩
    rw [← pathWeight_congr_vertices q ω ω' fun i => hag _ ((hK _).mpr
      ⟨by have := q.level i; omega, by have := q.level i; have := i.isLt; omega, hq i⟩)]
    exact hdef
  have hEloc : ∀ ω ω' : Environment, (∀ z ∈ K, ω z = ω' z) → (ω ∈ E s n ↔ ω' ∈ E s n) :=
    fun ω ω' h => ⟨hEdir ω ω' h, hEdir ω' ω fun z hz => (h z hz).symm⟩
  -- Step 2: the centres `z_{v,j}` and their blocks.
  obtain ⟨hj, hhj⟩ : ∃ hj : Fin (N + 1) → ℝ, ∀ j, hj j =
      (2 * (j.val : ℝ) + 1 - ((N + 1 : ℕ) : ℝ)) * (3 * ((R + 1) * (⌈s⌉₊ : ℝ))) :=
    ⟨_, fun _ => rfl⟩
  have hjb : ∀ j, -(((N + 1 : ℕ) : ℝ) * (3 * ((R + 1) * (⌈s⌉₊ : ℝ)))) ≤ hj j ∧
      hj j ≤ ((N + 1 : ℕ) : ℝ) * (3 * ((R + 1) * (⌈s⌉₊ : ℝ))) := by
    intro j
    have hjN : (j.val : ℝ) + 1 ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast j.isLt
    have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    rw [hhj]
    exact ⟨by nlinarith, mul_le_mul_of_nonneg_right (by linarith) hB3⟩
  have hcz : ∀ (v : ℕ × ℕ) (j : Fin (N + 1)), ∃ z : Lattice,
      z.1 + z.2 = ((t v * L : ℕ) : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - (Y v + hj j)| ≤ 1 / 2 :=
    fun v j => exists_level_vertex_near a _ _
  choose cz hczl hczr using hcz
  have hF4 : ∀ v j, |rho (cz v j) - Y v| + R * s ≤ S / 4 := by
    intro v j
    have h1 := abs_le.mp (hczr v j)
    rw [hrho]
    have h2 : |(1 - a) * ((cz v j).1 : ℝ) - a * ((cz v j).2 : ℝ) - Y v| ≤
        1 / 2 + ((N + 1 : ℕ) : ℝ) * (3 * ((R + 1) * (⌈s⌉₊ : ℝ))) :=
      abs_le.mpr ⟨by linarith [h1.1, (hjb j).1], by linarith [h1.2, (hjb j).2]⟩
    rw [hSdef]
    linarith
  have hdisjv : ∀ v, Pairwise fun i j : Fin (N + 1) =>
      Disjoint (K.map (addLeftEmbedding (cz v i))) (K.map (addLeftEmbedding (cz v j))) := by
    intro v i j hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hwi
    obtain ⟨k', hk', hkk⟩ := Finset.mem_map.mp hwj
    have hkk' : cz v j + k' = cz v i + k := hkk
    have f1 := congrArg Prod.fst hkk'; have f2 := congrArg Prod.snd hkk'
    simp only [Prod.fst_add, Prod.snd_add] at f1 f2
    have e1 : ((cz v j).1 : ℝ) + (k'.1 : ℝ) = ((cz v i).1 : ℝ) + (k.1 : ℝ) := by exact_mod_cast f1
    have e2 : ((cz v j).2 : ℝ) + (k'.2 : ℝ) = ((cz v i).2 : ℝ) + (k.2 : ℝ) := by exact_mod_cast f2
    have hk1 := abs_le.mp ((hK k).mp hk).2.2; have hk2 := abs_le.mp ((hK k').mp hk').2.2
    rw [hrho] at hk1 hk2
    have hsum : ((1 - a) * ((cz v j).1 : ℝ) - a * ((cz v j).2 : ℝ)) -
        ((1 - a) * ((cz v i).1 : ℝ) - a * ((cz v i).2 : ℝ)) =
        ((1 - a) * (k.1 : ℝ) - a * (k.2 : ℝ)) - ((1 - a) * (k'.1 : ℝ) - a * (k'.2 : ℝ)) := by
      linear_combination (1 - a) * e1 - a * e2
    have hci := abs_le.mp (hczr v i); have hcj := abs_le.mp (hczr v j)
    have hRs : 0 ≤ R * s := (mul_pos hR hspos).le
    rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hlt | hlt
    · have hlt' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
      have hm := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ (j.val : ℝ) - i.val) hB3
      have hdiff : hj j - hj i = 2 * (((j.val : ℝ) - i.val) * (3 * ((R + 1) * (⌈s⌉₊ : ℝ)))) := by
        rw [hhj, hhj]; ring
      linarith [hci.1, hci.2, hcj.1, hcj.2, hk1.1, hk1.2, hk2.1, hk2.2]
    · have hlt' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hlt
      have hm := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ (i.val : ℝ) - j.val) hB3
      have hdiff : hj i - hj j = 2 * (((i.val : ℝ) - j.val) * (3 * ((R + 1) * (⌈s⌉₊ : ℝ)))) := by
        rw [hhj, hhj]; ring
      linarith [hci.1, hci.2, hcj.1, hcj.2, hk1.1, hk1.2, hk2.1, hk2.2]
  -- Membership in the region of a site.
  have hmemReg : ∀ v (z : Lattice), ((t v * L : ℕ) : ℤ) ≤ z.1 + z.2 →
      z.1 + z.2 ≤ ((t v * L + n : ℕ) : ℤ) + (⌈D₀ * s⌉₊ : ℤ) → |rho z - Y v| ≤ 4 * S →
      z ∈ Reg v := by
    intro v z h1 h2 h3
    show _ ∧ _ ∧ _
    exact ⟨h1, by rw [hlev]; exact h2, h3⟩
  -- Translated blocks lie in the region of the site.
  have hblock : ∀ v j z, z ∈ K → cz v j + z ∈ Reg v := by
    intro v j z hz
    obtain ⟨hz0, hzn, hzr⟩ := (hK z).mp hz
    have hl := hczl v j
    have hF := hF4 v j
    rw [hrho] at hzr hF
    refine hmemReg v _ ?_ ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]; omega
    · simp only [Prod.fst_add, Prod.snd_add]; omega
    · rw [hrho]
      simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
      have hzr' := abs_le.mp hzr
      have hF' : |(1 - a) * ((cz v j).1 : ℝ) - a * ((cz v j).2 : ℝ) - Y v| ≤ S / 4 - R * s := by
        linarith
      have hF'' := abs_le.mp hF'
      exact abs_le.mpr ⟨by linarith [hzr'.1, hF''.1], by linarith [hzr'.2, hF''.2]⟩
  -- Steps 3–4: the connection events.
  let Conn : ℕ × ℕ → ℕ × ℕ → Set Environment := fun v v' => {ω | ∀ u u' : Lattice,
    u.1 + u.2 = ((t v * L + n : ℕ) : ℤ) → |rho u - Y v| ≤ S / 4 →
    u'.1 + u'.2 = ((t v * L + n : ℕ) : ℤ) + (⌈D₀ * s⌉₊ : ℤ) → |rho u' - Y v'| ≤ S / 4 →
    ∃ e : ℕ × ℕ, ∃ q : Path u e, q.vertex (Fin.last (e.1 + e.2)) = u' ∧
      f (u' - u) - pathWeight ω q ≤ ε * s / 2 ∧
      ∀ i, |rho (q.vertex i) - Y v| ≤ 4 * S}
  have hConn : ∀ v v', (v' = v + (1, 0) ∨ v' = v + (0, 1)) →
      MeasurableSet (Conn v v') ∧ p s ≤ (environmentLaw μ).real (Conn v v') := by
    intro v v' hv'
    have hY : Y v' = Y v + σ * S ∨ Y v' = Y v + 2 * σ * S := by
      rcases hv' with rfl | rfl
      · exact Or.inl (by simp only [Y, Prod.fst_add, Prod.snd_add]; push_cast; ring)
      · exact Or.inr (by simp only [Y, Prod.fst_add, Prod.snd_add]; push_cast; ring)
    exact hconn s S (Y v) (Y v') ((t v * L + n : ℕ) : ℤ) hs1 hSs hSC hY
  -- Step 5: good sites.
  let G : ℕ × ℕ → Set Environment := fun v =>
    (⋃ j, (environmentTranslationEquiv (cz v j)) ⁻¹' E s n) ∩
      Conn v (v + (1, 0)) ∩ Conn v (v + (0, 1))
  have hGm : ∀ v, MeasurableSet (G v) := fun v =>
    ((MeasurableSet.iUnion fun j => (environmentTranslationEquiv (cz v j)).measurable hEm).inter
      (hConn v _ (Or.inl rfl)).1).inter (hConn v _ (Or.inr rfl)).1
  -- Locality on the region `Reg v`.
  have hConnDir : ∀ v v' (ω ω' : Environment), (∀ z ∈ Reg v, ω z = ω' z) →
      ω ∈ Conn v v' → ω' ∈ Conn v v' := by
    intro v v' ω ω' hag hω
    simp only [Conn, Set.mem_ofPred_eq] at hω ⊢
    intro u u' hu hur hu' hur'
    obtain ⟨e, q, hend, hdef, htube⟩ := hω u u' hu hur hu' hur'
    refine ⟨e, q, hend, ?_, htube⟩
    have hlast := q.level (Fin.last (e.1 + e.2))
    rw [hend] at hlast
    simp only [Fin.val_last] at hlast
    rw [← pathWeight_congr_vertices q ω ω' fun i => hag _ (hmemReg v _
      (by have := q.level i; omega)
      (by have := q.level i; have := i.isLt; omega) (htube i))]
    exact hdef
  have hGdir : ∀ v (ω ω' : Environment), (∀ z ∈ Reg v, ω z = ω' z) →
      ω ∈ G v → ω' ∈ G v := by
    intro v ω ω' hag hω
    simp only [G, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage] at hω ⊢
    obtain ⟨⟨⟨j, hj'⟩, h1⟩, h2⟩ := hω
    refine ⟨⟨⟨j, (hEloc _ _ fun z hz => ?_).mp hj'⟩, hConnDir v _ ω ω' hag h1⟩,
      hConnDir v _ ω ω' hag h2⟩
    exact hag _ (hblock v j z hz)
  have hGloc : ∀ v (ω ω' : Environment), (∀ z ∈ Reg v, ω z = ω' z) → (ω ∈ G v ↔ ω' ∈ G v) :=
    fun v ω ω' h => ⟨hGdir v ω ω' h, hGdir v ω' ω fun z hz => (h z hz).symm⟩
  -- Finite regions and independence at sup-distance greater than ten.
  have hRegEx : ∀ v, ∃ Q : Finset Lattice, ∀ z, z ∈ Q ↔ z ∈ Reg v := by
    intro v
    obtain ⟨Q, hQ, -⟩ := exists_finset_signed_level_tube a (4 * S) (fun _ => Y v)
      ((t v * L : ℕ) : ℤ) L (by linarith)
    refine ⟨Q, fun z => ?_⟩
    rw [hQ z]
    have hcast : (((t v + 1) * L : ℕ) : ℤ) = ((t v * L : ℕ) : ℤ) + (L : ℤ) := by
      push_cast; ring
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact hmemReg v z h1 (by rw [← hlev, hcast]; exact h2) h3
    · intro hz
      obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hz
      exact ⟨h1, by rw [← hcast]; exact h2, h3⟩
  choose RegF hRegF using hRegEx
  have hRegions := coarse_percolation_regions_radius_ten a σ S L hL1 hS0 hσ
  refine ⟨G, hGm, ?_, ?_, hGloc, ?_⟩
  · -- The bad-site bound `(1-p₀)^T + 2(1 - p s) ≤ ζ`.
    intro v
    have hsub : (G v)ᶜ ⊆ ((⋂ j, ((environmentTranslationEquiv (cz v j)) ⁻¹' E s n)ᶜ) ∪
        (Conn v (v + (1, 0)))ᶜ) ∪ (Conn v (v + (0, 1)))ᶜ := by
      intro ω hω
      rw [Set.mem_compl_iff] at hω
      by_contra hcon
      apply hω
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iInter, not_or, not_forall,
        not_not] at hcon
      obtain ⟨⟨⟨j, hj'⟩, h1⟩, h2⟩ := hcon
      simp only [G, Set.mem_inter_iff]
      exact ⟨⟨Set.mem_iUnion.mpr ⟨j, hj'⟩, h1⟩, h2⟩
    have hprod := environmentLaw_iInter_translate_compl μ (E s n) K hEm hEloc (N + 1) (cz v)
      (hdisjv v)
    have hc1 := probReal_compl_eq_one_sub (μ := environmentLaw μ) (hConn v _ (Or.inl rfl)).1
    have hc2 := probReal_compl_eq_one_sub (μ := environmentLaw μ) (hConn v _ (Or.inr rfl)).1
    have hp1 := (hConn v _ (Or.inl rfl)).2
    have hp2 := (hConn v _ (Or.inr rfl)).2
    have hpow : (1 - (environmentLaw μ).real (E s n)) ^ (N + 1) ≤ max 0 (1 - p₀) ^ (N + 1) :=
      pow_le_pow_left₀ (by linarith [measureReal_le_one (μ := environmentLaw μ) (s := E s n)])
        (le_max_of_le_right (by linarith)) _
    have hps := hs₃ s hs3
    calc (environmentLaw μ).real (G v)ᶜ
        ≤ (environmentLaw μ).real (((⋂ j, ((environmentTranslationEquiv (cz v j)) ⁻¹' E s n)ᶜ) ∪
            (Conn v (v + (1, 0)))ᶜ) ∪ (Conn v (v + (0, 1)))ᶜ) := measureReal_mono hsub
      _ ≤ (environmentLaw μ).real (⋂ j, ((environmentTranslationEquiv (cz v j)) ⁻¹' E s n)ᶜ) +
            (environmentLaw μ).real (Conn v (v + (1, 0)))ᶜ +
            (environmentLaw μ).real (Conn v (v + (0, 1)))ᶜ :=
          (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
      _ ≤ ζ := by rw [hprod, hc1, hc2]; linarith
  · -- Independence of separated good-site events.
    intro F hF
    refine iIndepSet_environment_of_disjoint_supports μ (fun v : {u // u ∈ F} => G v.1)
      (fun v => RegF v.1) (fun v => hGm v.1)
      (fun v ω ω' h => hGloc v.1 ω ω' fun z hz => h z ((hRegF v.1 z).mpr hz)) ?_
    intro v w hvw
    have hdisj := hRegions.2 v.1 w.1 (hF v.1 v.2 w.1 w.2 fun h => hvw (Subtype.ext h))
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact Set.disjoint_left.mp hdisj ((hRegF v.1 z).mp hz) ((hRegF w.1 z).mp hz')
  · -- The witness predicate `W`.
    intro v ω hω
    simp only [G, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage] at hω
    obtain ⟨⟨⟨j, hj'⟩, h1⟩, h2⟩ := hω
    refine ⟨?_, ?_⟩
    · simp only [E, Set.mem_ofPred_eq] at hj'
      obtain ⟨u₀, hu₀, e, he, q, hq, hdef⟩ := hj'
      refine ⟨rho (cz v j), hF4 v j, cz v j + u₀, ?_, e, he, q.translate (cz v j), ?_, ?_⟩
      · have := hczl v j
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      · intro i
        have hqi := abs_le.mp (hq i)
        rw [hrho] at hqi
        simp only [hrho, Path.translate_vertex, Prod.fst_add, Prod.snd_add, Int.cast_add]
        exact abs_le.mpr ⟨by linarith [hqi.1], by linarith [hqi.2]⟩
      · have hsub : (q.translate (cz v j)).vertex (Fin.last (e.1 + e.2)) - (cz v j + u₀) =
            q.vertex (Fin.last (e.1 + e.2)) - u₀ := by
          rw [Path.translate_vertex]; abel
        rw [hsub, pathWeight_translate]
        exact hdef
    · intro v' hv' u u' hu hur hu' hur'
      rcases hv' with rfl | rfl
      · simp only [Conn, Set.mem_ofPred_eq] at h1
        exact h1 u u' hu hur (by rw [← hlev]; exact hu') hur'
      · simp only [Conn, Set.mem_ofPred_eq] at h2
        exact h2 u u' hu hur (by rw [← hlev]; exact hu') hur'

end LPPDifferentiability
