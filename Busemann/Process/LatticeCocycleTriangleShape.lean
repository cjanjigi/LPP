/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeCocycleShellShape
public import ProbabilityBasics.Analysis.PrefixMaximum
public import ProbabilityBasics.Combinatorics.TriangleShellMaximum

/-! Recovering cocycle shape for a lattice action. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal NNReal Topology
namespace LPP.Busemann

/-- The shell estimate gives sublinear centered fluctuations uniformly on the origin triangle. This is the extension of JR arXiv:1810.03580v3, Appendix B, Theorem B.3. -/
theorem ae_uniform_recovering_cocycle_triangle_shape_of_action
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
    let Δ : ℕ → Finset Lattice := fun n => insert 0
      (((Finset.Icc (0 : ℤ) (n : ℤ)).product (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (n : ℤ)))
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
        (fun x => |B 0 x ω - (u 0 ω * (x.1 : ℝ) + u 1 ω * (x.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (n : ℤ)))
  let S : ℕ → Finset Lattice := fun n => insert ((n : ℤ), 0)
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 = (n : ℤ)))
  let f : Ω → Lattice → ℝ := fun s x =>
    |B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|
  change ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _) (f s) /
      (n : ℝ)) atTop (𝓝 0)
  filter_upwards
    [ae_uniform_recovering_cocycle_shell_shape_of_action μ hmoment P T weights hWeightsMeas hMarginal hzero hadd hShift B hB hInt hRec]
    with s hs
  change Tendsto (fun n : ℕ =>
    (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) (f s) /
      (n : ℝ)) atTop (𝓝 0) at hs
  have hPrefix := ProbabilityBasics.tendsto_prefix_max_div_atTop_zero
    (fun n : ℕ => (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) (f s)) hs
  have hTriangle (n : ℕ) :
      (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _) (f s) =
        (Finset.range (n + 1)).sup'
          ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
          (fun r => (S r).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) (f s)) := by
    exact ProbabilityBasics.sup_triangle_eq_sup_shell_prefix (f s) n
  refine hPrefix.congr' (Filter.Eventually.of_forall fun n => ?_)
  rw [← hTriangle n]

end LPP.Busemann
