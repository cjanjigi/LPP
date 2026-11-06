/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GeodesicDefect
public import Differentiability.Probability.LongPathWitnessBound
public import Differentiability.Model.Paths.StageDefectTotal
public import Differentiability.Analysis.CornerDefectContradiction
public import LPP_Foundations.Analysis.ShapeProfileCalculus
import LPP_Foundations.Probability.CoordinateLaw
import Mathlib.Tactic

/-!
# The corner contradiction at a fixed scale (bounded weights)

Sections 6.2 and 6.3 of the differentiability preprint. Under a corner `c = (dl - dr)/2 > 0`, a
scale satisfying (6.4) (an explicit hypothesis here), (6.5) and (6.6), and an
upper bound `M0` on the weights, the geodesics to the floor endpoints have
`f`-defect at least a positive multiple of their length
(`Path.total_defect_disjoint_witnesses` and `long_path_disjoint_witnesses_ae`),
contradicting the sublinear geodesic defect. The shape is identified by uniqueness.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Sections 6.2 and 6.3 and (6.4)-(6.6).
-/

public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- An almost sure upper bound on one weight gives it at every site. -/
private theorem ae_environment_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (M0 : ℝ)
    (h : ∀ᵐ x ∂μ, x ≤ M0) : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, ω z ≤ M0 := by
  rw [ae_all_iff]
  intro z
  have hmap : ∀ᵐ x ∂((environmentLaw μ).map (fun ω : Environment => ω z)), x ≤ M0 := by
    rw [environmentLaw_map_eval μ z]
    exact h
  exact (ae_map_iff (measurable_environment_eval z).aemeasurable
    (measurableSet_le measurable_id measurable_const)).1 hmap

/-- The stage lengths of the first-cut producer bound the length of the path: the
`N+1` stages have length at most `2m`, so the path has length at most `2m(N+1)`. -/
private theorem length_le_of_stage_lengths (N m L : ℕ) (cuts : Fin (N+2) → Fin (L+1))
    (h0 : cuts 0 = 0) (hlast : cuts (Fin.last (N+1)) = Fin.last L)
    (hstep : ∀ i : Fin (N+1), (cuts i.succ).val - (cuts i.castSucc).val ≤ 2*m) :
    L ≤ 2*m*(N+1) := by
  have key : ∀ j (hj : j < N+2), (cuts ⟨j, hj⟩).val ≤ 2*m*j := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h : (⟨0, hj⟩ : Fin (N+2)) = 0 := Fin.ext (by simp)
      rw [h, h0]
      simp
    | succ j ih =>
      intro hj
      have h1 : (cuts ⟨j+1, hj⟩).val - (cuts ⟨j, by omega⟩).val ≤ 2*m := hstep ⟨j, by omega⟩
      have h2 := ih (by omega)
      have h3 : (cuts ⟨j+1, hj⟩).val ≤ (cuts ⟨j, by omega⟩).val + 2*m := by omega
      nlinarith
  have := key (N+1) (by omega)
  rw [show (⟨N+1, by omega⟩ : Fin (N+2)) = Fin.last (N+1) from rfl, hlast] at this
  simpa using this

/-- The corner contradiction at a fixed scale (Sections 6.2 and 6.3 of the differentiability
preprint), for weights bounded above by `M0`. The rare-event bound (6.4) is the hypothesis `hrare`,
copied from `long_path_disjoint_witnesses_ae`; `hstep` is (6.5) with the upper bound `M0` and
`hK` is (6.6). -/
theorem corner_excluded_at_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (M0 : ℝ) (hM0 : ∀ᵐ x ∂μ, x ≤ M0)
    (g : Quadrant → ℝ) (hg1 : Continuous g)
    (hg2 : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hg3 : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hg4 : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (H : ℝ → ℝ) (hH : H = fun h => quadrantExtension g (a + h, 1 - a - h))
    (dl dr c η G0 : ℝ) (hdl : dl = derivWithin H (Iio 0) 0)
    (hdr : dr = derivWithin H (Ioi 0) 0) (hc : c = (dl - dr) / 2) (hcpos : 0 < c)
    (hη : η = min 1 (c / 2)) (hG0 : G0 = H 0)
    (s : ℝ) (hs : 2 ≤ s) (m : ℕ) (hm : 1 ≤ m) (K q0 : ℝ) (hq0 : 0 < q0)
    (hsmall : 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2)
    (hK : 3*η*s+|(dl+dr)/2| * (2*s+2) < K*s)
    (hstep : |G0|+|(dl+dr)/2|+M0 ≤ η*s/2)
    (hrare : ∀ b : Lattice, (environmentLaw μ).real {ω : Environment |
      let v : Lattice → Lattice := fun b =>
        let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
        (j,b.1*m-j)
      let block : Lattice → Lattice → Prop := fun b z =>
        (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
          |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
      let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
        (∀ i, block b (q.vertex i)) ∧
          min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
            (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
      let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
        fun b u e q =>
          u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
            (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
              ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
            G0*(m : ℝ)-K*s < pathWeight ω q
      ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        defectWitness b u e q ∨ crossingWitness b u e q} ≤ 2*q0) :
    False := by
  have hs0 : 0 < s := by linarith
  have hη0 : 0 < η := by rw [hη]; exact lt_min one_pos (by linarith)
  have hηc : 2 * η ≤ (dl - dr) / 2 := by
    have := min_le_right 1 (c / 2)
    rw [← hc]
    rw [hη]
    linarith
  -- The shape of the hypotheses is the unique shape, which has the geodesic defect.
  obtain ⟨g', hg', -⟩ :=
    exists_unique_shape_with_sublinear_geodesic_defect_of_negative_moment_and_positive_tail
      μ hneg hpos
  obtain ⟨g0, -, hu0⟩ := exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  have e1 : g = g0 := hu0 g ⟨hg1, hg2, hg3, hg4⟩
  have e2 : g' = g0 := hu0 g' ⟨hg'.1, hg'.2.1, hg'.2.2.1, by
    filter_upwards [hg'.2.2.2] with ω hω using hω.1⟩
  have e : g' = g := e2.trans e1.symm
  rw [e] at hg'
  have hlong := long_path_disjoint_witnesses_ae μ a s m η G0 dl dr K q0 hq0 hsmall hrare
  have hbd := ae_environment_le μ M0 hM0
  have hae : ∀ᵐ ω ∂environmentLaw μ, False := by
    filter_upwards [hlong, hbd, hg'.2.2.2] with ω hl hb hsh
    obtain ⟨N0, hN0⟩ := hl
    -- The geodesic defect is `o(n)` ((2.17) of the preprint).
    have htend : Tendsto (fun n : ℕ =>
        (fun d : ℕ × ℕ => G0 * ((d.1 : ℝ) + (d.2 : ℝ)) +
          ((dl + dr) / 2) * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)) - lastPassage ω 0 d)
          (⌊(n : ℝ) * a⌋₊, n - ⌊(n : ℝ) * a⌋₊) / (n : ℝ)) atTop (𝓝 0) := by
      subst hH hdl hdr hG0
      exact hsh.2 a ha ha1
    -- One geodesic, with its stages: (6.16), Proposition 6.7 and (6.17) of the preprint.
    have key : ∀ (n : ℕ) (d : ℕ × ℕ), d = (⌊(n : ℝ) * a⌋₊, n - ⌊(n : ℝ) * a⌋₊) →
        d.1 + d.2 = n → ∃ N : ℕ, n ≤ 2 * m * (N + 1) ∧
          (max N0 3 ≤ N → η * s / 2 * (N : ℝ) ≤ G0 * ((d.1 : ℝ) + (d.2 : ℝ)) +
            ((dl + dr) / 2) * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)) - lastPassage ω 0 d) := by
      intro n d _ hdn
      obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω 0 d
      obtain ⟨N, cuts, hprod, capacity, time, start, disp, paths, hmem, hdisj, hineq⟩ :=
        p.total_defect_disjoint_witnesses ω a ha ha1 m hm s hs η G0 dl dr K M0 hη0 hηc hstep hK
      refine ⟨N, ?_, fun hN => ?_⟩
      · obtain ⟨h0, hlast, -, -, -, -, hlen, -⟩ := hprod
        rw [← hdn]
        exact length_le_of_stage_lengths N m (d.1 + d.2) cuts h0 hlast (fun i => (hlen i).1)
      · have hcap := hN0 d p N (le_trans (le_max_left _ _) hN) cuts hprod capacity time start
          disp paths hmem hdisj
        have hE : ∑ z ∈ p.collectedSites, max (ω z - M0) 0 ≤ 0 :=
          (Finset.sum_eq_zero fun z _ => max_eq_right (by linarith [hb z])).le
        have hlin := linear_defect_of_few_witnesses η s _ _ N _ (mul_nonneg hη0.le hs0.le)
          (le_trans (le_max_right _ _) hN) hcap hE hineq
        rw [hp] at hlin
        linarith
    refine corner_defect_contradiction _ m (max N0 3) hm (η * s / 2)
      (by have := mul_pos hη0 hs0; linarith) (fun n => ?_) htend
    have hgeom := floor_direction_endpoint_geometry a ha ha1 n
    dsimp only at hgeom
    exact key n _ rfl hgeom.1
  obtain ⟨ω, hω⟩ := hae.exists
  exact hω

/-- The contrapositive form: under the same hypotheses without `c > 0`, the two
one-sided derivatives of the profile agree. The inequality `dr ≤ dl` is concavity. -/
theorem profile_derivatives_eq_of_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (M0 : ℝ) (hM0 : ∀ᵐ x ∂μ, x ≤ M0)
    (g : Quadrant → ℝ) (hg1 : Continuous g)
    (hg2 : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hg3 : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hg4 : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (H : ℝ → ℝ) (hH : H = fun h => quadrantExtension g (a + h, 1 - a - h))
    (dl dr c η G0 : ℝ) (hdl : dl = derivWithin H (Iio 0) 0)
    (hdr : dr = derivWithin H (Ioi 0) 0) (hc : c = (dl - dr) / 2)
    (hη : η = min 1 (c / 2)) (hG0 : G0 = H 0)
    (s : ℝ) (hs : 2 ≤ s) (m : ℕ) (hm : 1 ≤ m) (K q0 : ℝ) (hq0 : 0 < q0)
    (hsmall : 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2)
    (hK : 3*η*s+|(dl+dr)/2| * (2*s+2) < K*s)
    (hstep : |G0|+|(dl+dr)/2|+M0 ≤ η*s/2)
    (hrare : ∀ b : Lattice, (environmentLaw μ).real {ω : Environment |
      let v : Lattice → Lattice := fun b =>
        let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
        (j,b.1*m-j)
      let block : Lattice → Lattice → Prop := fun b z =>
        (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
          |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
      let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
        (∀ i, block b (q.vertex i)) ∧
          min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
            (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
      let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
        fun b u e q =>
          u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
            (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
              ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
            G0*(m : ℝ)-K*s < pathWeight ω q
      ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        defectWitness b u e q ∨ crossingWitness b u e q} ≤ 2*q0) :
    dl = dr := by
  by_contra hne
  have hle : dr ≤ dl := by
    rw [hdl, hdr, hH]
    exact profile_rightDeriv_le_leftDeriv g hg3 a ha ha1
  have hcpos : 0 < c := by
    rw [hc]
    have : dr < dl := lt_of_le_of_ne hle (Ne.symm hne)
    linarith
  exact corner_excluded_at_scale μ hneg hpos M0 hM0 g hg1 hg2 hg3 hg4 a ha ha1 H hH dl dr c η G0
    hdl hdr hc hcpos hη hG0 s hs m hm K q0 hq0 hsmall hK hstep hrare

end LPPDifferentiability
