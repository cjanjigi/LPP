/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
import Busemann.Finite.GibbsArrowCylinder
import Busemann.Finite.PartitionDerivative
import Busemann.Finite.ZeroTemperatureLimit
import Busemann.Finite.TiltShift
import Busemann.Finite.PartitionRecursion
import LPP_Foundations.Probability.ArrowEndpointExpectation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Finite tilt order via the common-arrow positive-temperature coupling. -/

@[expose] public section

open MeasureTheory LPPDifferentiability Filter
open scoped BigOperators ENNReal unitInterval Topology

namespace LPP.Busemann

private theorem finite_east_count_sandwich (ω : Environment) (h : ℝ × ℝ)
    (β : ℝ) (hβ : 0 < β) (N : ℕ) (x : Lattice) :
    let Z : ℕ → Lattice → ℝ := fun n y =>
      ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))
    let M : ℕ → Lattice → ℝ := fun n y =>
      (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
        (k.val : ℝ) * Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))) / Z n y
    M N (x + (0, 1)) ≤ M (N + 1) x ∧
      M (N + 1) x ≤ M N (x + (1, 0)) + 1 := by
  classical
  let Z : ℕ → Lattice → ℝ := fun n y =>
    ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
      Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ)))
  let M : ℕ → Lattice → ℝ := fun n y =>
    (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
      (k.val : ℝ) * Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ)))) / Z n y
  let L : ℤ := x.1 + x.2 + ((N + 1 : ℕ) : ℤ)
  let Q : Measure (Lattice → unitInterval) :=
    Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
  obtain ⟨a, ha, hmass⟩ := exists_finite_gibbs_arrow_cylinder_field ω h β hβ L
  let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
    if θ y < a y then y + (1, 0) else y + (0, 1)
  let E : ℕ → Lattice → (Lattice → unitInterval) → ℝ := fun n y θ =>
    (((A θ)^[n] y).1 : ℝ) - (y.1 : ℝ)
  let Gamma : (n : ℕ) → (y : Lattice) →
      (Σ k : Fin (n + 1), LPPDifferentiability.Path y (k.val, n - k.val)) →
      Set (Lattice → unitInterval) := fun n y q =>
    {θ | ∀ j : ℕ, ∀ hj : j < q.1.val + (n - q.1.val) + 1,
      q.2.vertex ⟨j, hj⟩ = (A θ)^[j] y}
  have hExpect := uniform_arrow_endpoint_expectation a
  have hcount (n : ℕ) (y : Lattice) (hy : y.1 + y.2 + (n : ℤ) = L) :
      (∫ θ, E n y θ ∂Q) = M n y := by
    have hZpos : 0 < Z n y := (finite_tilted_partition_zero_pos_succ ω h β hβ n y).2.1
    have hpath (k : Fin (n + 1)) (p : LPPDifferentiability.Path y (k.val, n - k.val)) :
        (Q (Gamma n y ⟨k, p⟩)).toReal =
          Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
            h.2 * ((n - k.val : ℕ) : ℝ))) / Z n y := by
      have hlen : k.val + (n - k.val) = n := by have hk := k.isLt; omega
      have hlevel : y.1 + y.2 + ((k.val + (n - k.val) : ℕ) : ℤ) = L := by
        rw [hlen]
        exact hy
      have hm := (hmass y (k.val, n - k.val) hlevel p).2
      have hevent : Gamma n y ⟨k, p⟩ =
          {θ | ∀ j : Fin (k.val + (n - k.val) + 1),
            ((A θ)^[j.val]) y = p.vertex j} := by
        ext θ
        constructor
        · intro ht j
          exact (ht j.val j.isLt).symm
        · intro ht j hj
          exact (ht ⟨j, hj⟩).symm
      rw [hevent, hm]
      change (ENNReal.ofReal (Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ))) / Z (k.val + (n - k.val)) y)).toReal = _
      rw [hlen, ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZpos.le)]
    calc
      (∫ θ, E n y θ ∂Q) =
          ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
            (k.val : ℝ) * (Q (Gamma n y ⟨k, p⟩)).toReal := (hExpect.1 n y).2
      _ = (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
            (k.val : ℝ) * Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
              h.2 * ((n - k.val : ℕ) : ℝ)))) / Z n y := by
        simp only [hpath, mul_div_assoc, Finset.sum_div]
      _ = M n y := rfl
  have hp : x.1 + x.2 + ((N + 1 : ℕ) : ℤ) = L := rfl
  have he : (x + (1, 0)).1 + (x + (1, 0)).2 + (N : ℤ) = L := by dsimp only [L]; simp; omega
  have hn : (x + (0, 1)).1 + (x + (0, 1)).2 + (N : ℤ) = L := by dsimp only [L]; simp; omega
  change M N (x + (0, 1)) ≤ M (N + 1) x ∧ M (N + 1) x ≤ M N (x + (1, 0)) + 1
  constructor
  · rw [← hcount N (x + (0, 1)) hn, ← hcount (N + 1) x hp]
    exact hExpect.2.1 N x
  · rw [← hcount (N + 1) x hp, ← hcount N (x + (1, 0)) he]
    exact hExpect.2.2 N x

end LPP.Busemann

namespace LPP.Busemann

private theorem finite_beta_tilt_order (ω : Environment) (h k : ℝ × ℝ)
    (hfirst : h.1 ≤ k.1) (hsecond : k.2 ≤ h.2)
    (β : ℝ) (hβ : 0 < β) (N : ℕ) (x : Lattice) :
    let Z : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y =>
      ∑ j : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (j.val, n - j.val),
        Real.exp (β * (pathWeight ω p + u.1 * (j.val : ℝ) +
          u.2 * ((n - j.val : ℕ) : ℝ)))
    let F : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y => Real.log (Z u n y) / β
    (F k (N + 1) x - F k N (x + finiteEdgeStep 0) - finiteTiltCoordinate k 0 ≤
      F h (N + 1) x - F h N (x + finiteEdgeStep 0) - finiteTiltCoordinate h 0) ∧
    (F h (N + 1) x - F h N (x + finiteEdgeStep 1) - finiteTiltCoordinate h 1 ≤
      F k (N + 1) x - F k N (x + finiteEdgeStep 1) - finiteTiltCoordinate k 1) := by
  classical
  let Z : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y =>
    ∑ j : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (j.val, n - j.val),
      Real.exp (β * (pathWeight ω p + u.1 * (j.val : ℝ) +
        u.2 * ((n - j.val : ℕ) : ℝ)))
  let F : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y => Real.log (Z u n y) / β
  let M : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y =>
    (∑ j : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (j.val, n - j.val),
      (j.val : ℝ) * Real.exp (β * (pathWeight ω p + u.1 * (j.val : ℝ) +
        u.2 * ((n - j.val : ℕ) : ℝ)))) / Z u n y
  let U : ℝ → ℝ × ℝ := fun t => (h.1 + t, h.2)
  let G0 : ℝ → ℝ := fun t => F (U t) (N + 1) x - F (U t) N (x + (1, 0)) - (h.1 + t)
  let G1 : ℝ → ℝ := fun t => F (U t) (N + 1) x - F (U t) N (x + (0, 1)) - h.2
  let D0 : ℝ → ℝ := fun t => M (U t) (N + 1) x - M (U t) N (x + (1, 0)) - 1
  let D1 : ℝ → ℝ := fun t => M (U t) (N + 1) x - M (U t) N (x + (0, 1))
  have hder (t : ℝ) (n : ℕ) (y : Lattice) :
      HasDerivAt (fun s => F (U s) n y) (M (U t) n y) t := by
    have hbase : HasDerivAt (fun s : ℝ => F ((h.1 + t) + s, h.2) n y)
        (M (U t) n y) 0 := by
      have hb := hasDerivAt_finite_tilted_partition_east_count ω (U t) β hβ n y
      dsimp only at hb
      simpa only [F, M, Z, U, Prod.fst, Prod.snd, add_zero] using hb
    have hbase' : HasDerivAt (fun s : ℝ => F ((h.1 + t) + s, h.2) n y)
        (M (U t) n y) (t - t) := by simpa only [sub_self] using hbase
    have hin : HasDerivAt (fun s : ℝ => s - t) 1 t := by
      simpa only [id_eq] using ((hasDerivAt_id t).sub_const t)
    have hcomp := hbase'.comp t (h := fun s : ℝ => s - t) hin
    have hfun : (fun s : ℝ => F ((h.1 + t) + (s - t), h.2) n y) =
        (fun s => F (U s) n y) := by
      funext s
      apply congrArg (fun u : ℝ × ℝ => F u n y)
      apply Prod.ext
      · ring
      · rfl
    simpa only [Function.comp_def, mul_one, hfun] using hcomp
  have hD0 (t : ℝ) : HasDerivAt G0 (D0 t) t := by
    dsimp only [G0, D0]
    simpa only [id_eq] using
      ((hder t (N + 1) x).fun_sub (hder t N (x + (1, 0)))).fun_sub
        ((hasDerivAt_id t).const_add h.1)
  have hD1 (t : ℝ) : HasDerivAt G1 (D1 t) t := by
    dsimp only [G1, D1]
    exact ((hder t (N + 1) x).sub (hder t N (x + (0, 1)))).sub_const h.2
  have hsign0 (t : ℝ) : D0 t ≤ 0 := by
    have hs := finite_east_count_sandwich ω (U t) β hβ N x
    change M (U t) N (x + (0, 1)) ≤ M (U t) (N + 1) x ∧
      M (U t) (N + 1) x ≤ M (U t) N (x + (1, 0)) + 1 at hs
    dsimp only [D0]
    linarith only [hs.2]
  have hsign1 (t : ℝ) : 0 ≤ D1 t := by
    have hs := finite_east_count_sandwich ω (U t) β hβ N x
    change M (U t) N (x + (0, 1)) ≤ M (U t) (N + 1) x ∧
      M (U t) (N + 1) x ≤ M (U t) N (x + (1, 0)) + 1 at hs
    dsimp only [D1]
    linarith only [hs.1]
  have hanti : Antitone G0 := antitone_of_hasDerivAt_nonpos hD0 hsign0
  have hmono : Monotone G1 := monotone_of_hasDerivAt_nonneg hD1 hsign1
  let c : ℝ := k.2 - h.2
  let t : ℝ := (k.1 - h.1) - c
  have ht : 0 ≤ t := by dsimp only [t, c]; linarith only [hfirst, hsecond]
  have hUk : ((U t).1 + c, (U t).2 + c) = k := by
    apply Prod.ext <;> dsimp only [U, t, c] <;> ring
  have hshift := finite_tilted_partition_equal_tilt_shift ω (U t) c β hβ
  have hshift0 := hshift.2.2 N x 0
  have hshift1 := hshift.2.2 N x 1
  change F ((U t).1 + c, (U t).2 + c) (N + 1) x -
      F ((U t).1 + c, (U t).2 + c) N (x + finiteEdgeStep 0) -
        finiteTiltCoordinate ((U t).1 + c, (U t).2 + c) 0 = _ at hshift0
  change F ((U t).1 + c, (U t).2 + c) (N + 1) x -
      F ((U t).1 + c, (U t).2 + c) N (x + finiteEdgeStep 1) -
        finiteTiltCoordinate ((U t).1 + c, (U t).2 + c) 1 = _ at hshift1
  rw [hUk] at hshift0 hshift1
  change (F k (N + 1) x - F k N (x + finiteEdgeStep 0) - finiteTiltCoordinate k 0 ≤
      F h (N + 1) x - F h N (x + finiteEdgeStep 0) - finiteTiltCoordinate h 0) ∧
    (F h (N + 1) x - F h N (x + finiteEdgeStep 1) - finiteTiltCoordinate h 1 ≤
      F k (N + 1) x - F k N (x + finiteEdgeStep 1) - finiteTiltCoordinate k 1)
  have hshift0' : F k (N + 1) x - F k N (x + finiteEdgeStep 0) -
      finiteTiltCoordinate k 0 = G0 t := by
    change F k (N + 1) x - F k N (x + finiteEdgeStep 0) -
      finiteTiltCoordinate k 0 = G0 t at hshift0
    exact hshift0
  have hshift1' : F k (N + 1) x - F k N (x + finiteEdgeStep 1) -
      finiteTiltCoordinate k 1 = G1 t := by
    change F k (N + 1) x - F k N (x + finiteEdgeStep 1) -
      finiteTiltCoordinate k 1 = G1 t at hshift1
    exact hshift1
  have hstart0 : G0 0 = F h (N + 1) x - F h N (x + finiteEdgeStep 0) -
      finiteTiltCoordinate h 0 := by
    simp [G0, U, finiteEdgeStep, finiteTiltCoordinate]
  have hstart1 : G1 0 = F h (N + 1) x - F h N (x + finiteEdgeStep 1) -
      finiteTiltCoordinate h 1 := by
    simp [G1, U, finiteEdgeStep, finiteTiltCoordinate]
  constructor
  · rw [hshift0', ← hstart0]
    exact hanti ht
  · rw [← hstart1, hshift1']
    exact hmono ht

/-- Oppositely ordered tilt coordinates order both exact finite Busemann edges
at every signed site and terminal level. This is JR1810.03580v3, Lemma 4.11,
with the departure-site Gibbs-kernel correction. -/
theorem finiteBusemannEdge_order_of_tilt (ω : Environment) (h k : ℝ × ℝ)
    (hfirst : h.1 ≤ k.1) (hsecond : k.2 ≤ h.2) (x : Lattice) (L : ℤ) :
    finiteBusemannEdge ω k x L 0 ≤ finiteBusemannEdge ω h x L 0 ∧
    finiteBusemannEdge ω h x L 1 ≤ finiteBusemannEdge ω k x L 1 := by
  classical
  by_cases hactive : x.1 + x.2 < L
  · let N : ℕ := (L - (x.1 + x.2) - 1).toNat
    have hlevel : x.1 + x.2 + ((N + 1 : ℕ) : ℤ) = L := by dsimp only [N]; omega
    let Z : ℝ → (ℝ × ℝ) → ℕ → Lattice → ℝ := fun β u n y =>
      ∑ j : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (j.val, n - j.val),
        Real.exp (β * (pathWeight ω p + u.1 * (j.val : ℝ) +
          u.2 * ((n - j.val : ℕ) : ℝ)))
    let F : ℝ → (ℝ × ℝ) → ℕ → Lattice → ℝ := fun β u n y => Real.log (Z β u n y) / β
    let H : ℝ → (ℝ × ℝ) → Fin 2 → ℝ := fun β u i =>
      F β u (N + 1) x - F β u N (x + finiteEdgeStep i) - finiteTiltCoordinate u i
    have hlim (u : ℝ × ℝ) (i : Fin 2) :
        Tendsto (fun β : ℝ => H β u i) atTop (𝓝 (finiteBusemannEdge ω u x L i)) := by
      have hu := (finite_partition_and_edge_zero_temperature_limits ω u).2 N x i
      rw [hlevel] at hu
      exact hu
    have horder : ∀ᶠ β : ℝ in atTop, H β k 0 ≤ H β h 0 ∧ H β h 1 ≤ H β k 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
      exact finite_beta_tilt_order ω h k hfirst hsecond β hβ N x
    constructor
    · exact le_of_tendsto_of_tendsto (hlim k 0) (hlim h 0) (horder.mono fun _ hh => hh.1)
    · exact le_of_tendsto_of_tendsto (hlim h 1) (hlim k 1) (horder.mono fun _ hh => hh.2)
  · simp [finiteBusemannEdge, hactive]

end LPP.Busemann
