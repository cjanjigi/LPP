/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Model.Paths.Coalescence
public import LPP_Foundations.Model.Paths.UpRightRay
public import Mathlib.Topology.Instances.Real.Lemmas
import LPP_Foundations.Model.LastPassage.GradientOrder
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

-- Coordinate escape supplies an entry time for every signed lattice site.
private theorem ray_entry (γ : ℕ → Lattice)
    (hfirst : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hsecond : Tendsto (fun n : ℕ => (γ n).2) atTop atTop)
    (x : Lattice) : ∃ N : ℕ, x ≤ γ N := by
  obtain ⟨N₁, hN₁⟩ :=
    Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 hfirst) x.1)
  obtain ⟨N₂, hN₂⟩ :=
    Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 hsecond) x.2)
  refine ⟨max N₁ N₂, ?_⟩
  constructor
  · exact hN₁ _ (le_max_left _ _)
  · exact hN₂ _ (le_max_right _ _)

-- Each edge from x lies below the northeast corner x+(1,1).
private theorem site_le_diagonal (x : Lattice) :
    x ≤ x + ((1 : ℤ), (1 : ℤ)) := by
  constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

private theorem edge_le_diagonal (x : Lattice) (i : Fin 2) :
    x + finiteEdgeStep i ≤ x + ((1 : ℤ), (1 : ℤ)) := by
  fin_cases i
  · change x + ((1 : ℤ), (0 : ℤ)) ≤ x + ((1 : ℤ), (1 : ℤ))
    constructor
    · rfl
    · simp only [Prod.snd_add]
      omega
  · change x + ((0 : ℤ), (1 : ℤ)) ≤ x + ((1 : ℤ), (1 : ℤ))
    constructor
    · simp only [Prod.fst_add]
      omega
    · rfl

/-- Eventual shared-level order of two ordinary coordinate-escaping rays
orders their supplied real passage-limit fields: horizontal increments reverse
and vertical increments preserve the order. Aligned coalescence separately
identifies the entire fields. Strong Existence, asymptotic
order/coalescence lines 177–179, field order line 182 and Lemma B-order,
lines 1703–1712. This conditional bridge does not produce the real fields. -/
theorem geodesic_limit_fields_order_and_eq_of_coalescing
    (ω : LPPDifferentiability.Environment) (u v : Lattice)
    (γ π : ℕ → Lattice)
    (Cγ Cπ : Lattice → Lattice → ℝ)
    (hγstart : γ 0 = u) (hπstart : π 0 = v)
    (hγsteps : IsUpRightRay γ)
    (hπsteps : IsUpRightRay π)
    (_hγsegments : has_maximizing_segments ω γ)
    (_hπsegments : has_maximizing_segments ω π)
    (hγescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hγescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop)
    (hπescape₁ : Tendsto (fun n : ℕ => (π n).1) atTop atTop)
    (hπescape₂ : Tendsto (fun n : ℕ => (π n).2) atTop atTop)
    (hγLimit : has_passage_difference_limits ω γ Cγ)
    (hπLimit : has_passage_difference_limits ω π Cπ) :
    ((∃ L : ℤ, u.1 + u.2 ≤ L ∧ v.1 + v.2 ≤ L ∧
      ∀ m n : ℕ, L ≤ u.1 + u.2 + (m : ℤ) →
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) →
        (γ m).1 ≤ (π n).1 ∧ (π n).2 ≤ (γ m).2) →
      ∀ x : Lattice,
        Cπ x (x + ((1 : ℤ), (0 : ℤ))) ≤ Cγ x (x + ((1 : ℤ), (0 : ℤ))) ∧
        Cγ x (x + ((0 : ℤ), (1 : ℤ))) ≤ Cπ x (x + ((0 : ℤ), (1 : ℤ)))) ∧
    (paths_coalesce u v γ π → Cγ = Cπ) := by
  -- Record monotonicity and the exact absolute level of each ray.
  have hγmono : Monotone γ := hγsteps.monotone
  have hπmono : Monotone π := hπsteps.monotone
  have hγlevel (n : ℕ) :
      (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
    simpa only [hγstart] using hγsteps.level n
  have hπlevel (n : ℕ) :
      (π n).1 + (π n).2 = v.1 + v.2 + (n : ℤ) := by
    simpa only [hπstart] using hπsteps.level n
  constructor
  · -- For a fixed site, start both limit sequences after the site and both edge neighbors.
    intro horder
    rcases horder with ⟨L, huL, hvL, horder⟩
    intro x
    obtain ⟨Nγ, hγentry⟩ :=
      ray_entry γ hγescape₁ hγescape₂ (x + ((1 : ℤ), (1 : ℤ)))
    obtain ⟨Nπ, hπentry⟩ :=
      ray_entry π hπescape₁ hπescape₂ (x + ((1 : ℤ), (1 : ℤ)))
    -- One absolute level lies beyond the order threshold and both entry times.
    let q : ℤ := max L
      (max (u.1 + u.2 + (Nγ : ℤ)) (v.1 + v.2 + (Nπ : ℤ)))
    have hLq : L ≤ q := by
      dsimp only [q]
      exact le_max_left _ _
    have hqγ : u.1 + u.2 + (Nγ : ℤ) ≤ q := by
      dsimp only [q]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hqπ : v.1 + v.2 + (Nπ : ℤ) ≤ q := by
      dsimp only [q]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have huq : u.1 + u.2 ≤ q := le_trans huL hLq
    have hvq : v.1 + v.2 ≤ q := le_trans hvL hLq
    -- Convert the two level differences to natural ray offsets.
    let m₀ : ℕ := (q - (u.1 + u.2)).toNat
    let n₀ : ℕ := (q - (v.1 + v.2)).toNat
    have hmcast : (m₀ : ℤ) = q - (u.1 + u.2) := by
      dsimp only [m₀]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr huq)
    have hncast : (n₀ : ℤ) = q - (v.1 + v.2) := by
      dsimp only [n₀]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hvq)
    have hmlevel : u.1 + u.2 + (m₀ : ℤ) = q := by omega
    have hnlevel : v.1 + v.2 + (n₀ : ℤ) = q := by omega
    have hmentry : Nγ ≤ m₀ := by omega
    have hnentry : Nπ ≤ n₀ := by omega
    -- Every later aligned endpoint stays in both required domains.
    have hγpoint (k : ℕ) : x + ((1 : ℤ), (1 : ℤ)) ≤ γ (m₀ + k) :=
      le_trans hγentry (hγmono (by omega))
    have hπpoint (k : ℕ) : x + ((1 : ℤ), (1 : ℤ)) ≤ π (n₀ + k) :=
      le_trans hπentry (hπmono (by omega))
    -- The endpoints have the same absolute level, and their order is eventual.
    have hγendpointLevel (k : ℕ) :
        (γ (m₀ + k)).1 + (γ (m₀ + k)).2 = q + (k : ℤ) := by
      rw [hγlevel, Nat.cast_add, ← add_assoc, hmlevel]
    have hπendpointLevel (k : ℕ) :
        (π (n₀ + k)).1 + (π (n₀ + k)).2 = q + (k : ℤ) := by
      rw [hπlevel, Nat.cast_add, ← add_assoc, hnlevel]
    have hγindexLevel (k : ℕ) :
        u.1 + u.2 + ((m₀ + k : ℕ) : ℤ) = q + (k : ℤ) := by
      rw [Nat.cast_add, ← add_assoc, hmlevel]
    have hπindexLevel (k : ℕ) :
        v.1 + v.2 + ((n₀ + k : ℕ) : ℤ) = q + (k : ℤ) := by
      rw [Nat.cast_add, ← add_assoc, hnlevel]
    have hendpointOrder (k : ℕ) :
        (γ (m₀ + k)).1 ≤ (π (n₀ + k)).1 ∧
          (π (n₀ + k)).2 ≤ (γ (m₀ + k)).2 := by
      apply horder (m₀ + k) (n₀ + k)
      · rw [hγindexLevel]
        omega
      · rw [hγindexLevel, hπindexLevel]
    -- Finite antidiagonal order applies with the actual reachable endpoints.
    have hfinite (i : Fin 2) (k : ℕ) :
        let a := γ (m₀ + k)
        let b := π (n₀ + k)
        let ha : x ≤ a ∧ x + finiteEdgeStep i ≤ a := by
          exact ⟨le_trans (site_le_diagonal x) (hγpoint k),
            le_trans (edge_le_diagonal x i) (hγpoint k)⟩
        let hb : x ≤ b ∧ x + finiteEdgeStep i ≤ b := by
          exact ⟨le_trans (site_le_diagonal x) (hπpoint k),
            le_trans (edge_le_diagonal x i) (hπpoint k)⟩
        if i = 0 then
          orderedPassage ω ⟨(x, b), hb.1⟩ -
              orderedPassage ω ⟨(x + finiteEdgeStep i, b), hb.2⟩ ≤
            orderedPassage ω ⟨(x, a), ha.1⟩ -
              orderedPassage ω ⟨(x + finiteEdgeStep i, a), ha.2⟩
        else
          orderedPassage ω ⟨(x, a), ha.1⟩ -
              orderedPassage ω ⟨(x + finiteEdgeStep i, a), ha.2⟩ ≤
            orderedPassage ω ⟨(x, b), hb.1⟩ -
              orderedPassage ω ⟨(x + finiteEdgeStep i, b), hb.2⟩ := by
      let a := γ (m₀ + k)
      let b := π (n₀ + k)
      let ha : x ≤ a ∧ x + finiteEdgeStep i ≤ a := by
        exact ⟨le_trans (site_le_diagonal x) (hγpoint k),
          le_trans (edge_le_diagonal x i) (hγpoint k)⟩
      let hb : x ≤ b ∧ x + finiteEdgeStep i ≤ b := by
        exact ⟨le_trans (site_le_diagonal x) (hπpoint k),
          le_trans (edge_le_diagonal x i) (hπpoint k)⟩
      exact LPP.passage_difference_antidiagonal_order ω x i a b ha hb
        ((hγendpointLevel k).trans (hπendpointLevel k).symm)
        (hendpointOrder k).1
    -- Name the horizontal difference sequences from the full limit fields.
    let Hγ : ℕ → ℝ := fun k =>
      lastPassage ω x (((γ (m₀ + k)).1 - x.1).toNat,
        ((γ (m₀ + k)).2 - x.2).toNat) -
      lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
        (((γ (m₀ + k)).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
          ((γ (m₀ + k)).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat)
    let Hπ : ℕ → ℝ := fun k =>
      lastPassage ω x (((π (n₀ + k)).1 - x.1).toNat,
        ((π (n₀ + k)).2 - x.2).toNat) -
      lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
        (((π (n₀ + k)).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
          ((π (n₀ + k)).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat)
    have hHpointwise (k : ℕ) : Hπ k ≤ Hγ k := by
      have h := hfinite 0 k
      simpa [Hγ, Hπ, finiteEdgeStep, orderedPassage] using h
    have hHγlimit :
        Tendsto Hγ atTop (𝓝 (Cγ x (x + ((1 : ℤ), (0 : ℤ))))) := by
      exact hγLimit x (x + ((1 : ℤ), (0 : ℤ))) m₀
        (le_trans (site_le_diagonal x) (hγpoint 0))
        (le_trans (edge_le_diagonal x 0) (hγpoint 0))
    have hHπlimit :
        Tendsto Hπ atTop (𝓝 (Cπ x (x + ((1 : ℤ), (0 : ℤ))))) := by
      exact hπLimit x (x + ((1 : ℤ), (0 : ℤ))) n₀
        (le_trans (site_le_diagonal x) (hπpoint 0))
        (le_trans (edge_le_diagonal x 0) (hπpoint 0))
    have hHorizontal :
        Cπ x (x + ((1 : ℤ), (0 : ℤ))) ≤ Cγ x (x + ((1 : ℤ), (0 : ℤ))) :=
      le_of_tendsto_of_tendsto hHπlimit hHγlimit
        (Filter.Eventually.of_forall hHpointwise)
    -- The vertical edge has the other orientation in the finite comparison.
    let Vγ : ℕ → ℝ := fun k =>
      lastPassage ω x (((γ (m₀ + k)).1 - x.1).toNat,
        ((γ (m₀ + k)).2 - x.2).toNat) -
      lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
        (((γ (m₀ + k)).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
          ((γ (m₀ + k)).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat)
    let Vπ : ℕ → ℝ := fun k =>
      lastPassage ω x (((π (n₀ + k)).1 - x.1).toNat,
        ((π (n₀ + k)).2 - x.2).toNat) -
      lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
        (((π (n₀ + k)).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
          ((π (n₀ + k)).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat)
    have hVpointwise (k : ℕ) : Vγ k ≤ Vπ k := by
      have h := hfinite 1 k
      simpa [Vγ, Vπ, finiteEdgeStep, orderedPassage] using h
    have hVγlimit :
        Tendsto Vγ atTop (𝓝 (Cγ x (x + ((0 : ℤ), (1 : ℤ))))) := by
      exact hγLimit x (x + ((0 : ℤ), (1 : ℤ))) m₀
        (le_trans (site_le_diagonal x) (hγpoint 0))
        (le_trans (edge_le_diagonal x 1) (hγpoint 0))
    have hVπlimit :
        Tendsto Vπ atTop (𝓝 (Cπ x (x + ((0 : ℤ), (1 : ℤ))))) := by
      exact hπLimit x (x + ((0 : ℤ), (1 : ℤ))) n₀
        (le_trans (site_le_diagonal x) (hπpoint 0))
        (le_trans (edge_le_diagonal x 1) (hπpoint 0))
    have hVertical :
        Cγ x (x + ((0 : ℤ), (1 : ℤ))) ≤ Cπ x (x + ((0 : ℤ), (1 : ℤ))) :=
      le_of_tendsto_of_tendsto hVγlimit hVπlimit
        (Filter.Eventually.of_forall hVpointwise)
    exact ⟨hHorizontal, hVertical⟩
  · -- Coalescence alone identifies the whole fields, pair by pair.
    rintro ⟨m, n, _hlevel, hcoalescing⟩
    funext x
    funext y
    obtain ⟨Nx, hNx⟩ := ray_entry γ hγescape₁ hγescape₂ x
    obtain ⟨Ny, hNy⟩ := ray_entry γ hγescape₁ hγescape₂ y
    let N := max Nx Ny
    have hxN : x ≤ γ N := le_trans hNx (hγmono (by dsimp only [N]; exact le_max_left _ _))
    have hyN : y ≤ γ N := le_trans hNy (hγmono (by dsimp only [N]; exact le_max_right _ _))
    -- Shift the common tail far enough to enter the chosen pair's domain.
    let j := max N m - m
    have hj : m + j = max N m := by
      dsimp only [j]
      omega
    have hNj : N ≤ m + j := by
      rw [hj]
      exact le_max_left _ _
    have hxγ : x ≤ γ (m + j) := le_trans hxN (hγmono hNj)
    have hyγ : y ≤ γ (m + j) := le_trans hyN (hγmono hNj)
    have hbase : γ (m + j) = π (n + j) := hcoalescing j
    have hxπ : x ≤ π (n + j) := by
      rw [← hbase]
      exact hxγ
    have hyπ : y ≤ π (n + j) := by
      rw [← hbase]
      exact hyγ
    have htail (k : ℕ) : γ (m + j + k) = π (n + j + k) := by
      simpa only [Nat.add_assoc] using hcoalescing (j + k)
    -- The two full passage-difference sequences now agree term by term.
    let Fγ : ℕ → ℝ := fun k =>
      lastPassage ω x (((γ (m + j + k)).1 - x.1).toNat,
        ((γ (m + j + k)).2 - x.2).toNat) -
      lastPassage ω y (((γ (m + j + k)).1 - y.1).toNat,
        ((γ (m + j + k)).2 - y.2).toNat)
    let Fπ : ℕ → ℝ := fun k =>
      lastPassage ω x (((π (n + j + k)).1 - x.1).toNat,
        ((π (n + j + k)).2 - x.2).toNat) -
      lastPassage ω y (((π (n + j + k)).1 - y.1).toNat,
        ((π (n + j + k)).2 - y.2).toNat)
    have hseq : Fγ = Fπ := by
      funext k
      dsimp only [Fγ, Fπ]
      rw [htail k]
    have hγlimit' : Tendsto Fγ atTop (𝓝 (Cγ x y)) :=
      hγLimit x y (m + j) hxγ hyγ
    have hπlimit' : Tendsto Fπ atTop (𝓝 (Cπ x y)) :=
      hπLimit x y (n + j) hxπ hyπ
    rw [← hseq] at hπlimit'
    exact tendsto_nhds_unique hγlimit' hπlimit'

end LPP.Busemann
