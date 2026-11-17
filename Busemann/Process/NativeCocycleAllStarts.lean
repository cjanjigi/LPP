/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeCocycleTriangleShape
import Busemann.Process.InvariantConditionalDrifts
import Busemann.Process.ShiftTopology
import Mathlib.Tactic

/-! Canonical centered triangle estimates at every fixed signed start. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal BigOperators Topology

namespace LPP.Busemann

/-- The native triangle estimate holds at every fixed signed start with the
same canonical full-action conditional means. This is the stationary
translation step after JR1810.03580v3, Appendix B, Theorem B.3. -/
theorem ae_uniform_recovering_cocycle_triangle_shape_all_starts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let Δ : ℕ → Finset Lattice := fun n =>
      insert 0 (((Finset.Icc (0 : ℤ) (n : ℤ)).product
        (Finset.Icc (0 : ℤ) (n : ℤ))).filter
          (fun x => x.1 + x.2 ≤ (n : ℤ)))
    ∀ᵐ s ∂P, ∀ z : Lattice, Tendsto (fun n : ℕ =>
      (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
        (fun x => |B z (z + x) s -
          (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) := by
  classical
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  let u : Fin 2 → ProcessSample → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (n : ℤ)))
  change ∀ᵐ s ∂P, ∀ z : Lattice, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun x => |B z (z + x) s -
        (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) / (n : ℝ)) atTop (𝓝 0)
  -- Pull back one origin event under all countably many signed shifts.
  have hOrigin := ae_uniform_recovering_cocycle_triangle_shape
    μ hmoment P hMarginal hShift B hB hInt hRec
  change ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x s -
        (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) / (n : ℝ)) atTop (𝓝 0) at hOrigin
  have hShiftOrigin : ∀ᵐ s ∂P, ∀ z : Lattice, Tendsto (fun n : ℕ =>
      (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
        (fun x => |B 0 x (processShift z s) -
          (u 0 (processShift z s) * (x.1 : ℝ) +
            u 1 (processShift z s) * (x.2 : ℝ))|) / (n : ℝ)) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro z
    exact (hShift z).quasiMeasurePreserving.ae hOrigin
  -- One globally invariant representative transfers the literal canonical means.
  obtain ⟨U, hU, hUEq⟩ := exists_full_action_directional_drifts_condExp P hShift B hB hInt
  have hMeans : ∀ᵐ s ∂P, ∀ (i : Fin 2) (z : Lattice),
      u i (processShift z s) = U i s := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro z
    have he : U i =ᵐ[P] u i := hUEq i
    have hp := (hShift z).quasiMeasurePreserving.ae he.symm
    filter_upwards [hp] with s hs
    exact hs.trans (hU.2 i z s)
  have hCov : ∀ᵐ s ∂P, ∀ z x : Lattice,
      B z (z + x) s = B 0 x (processShift z s) := by
    apply ae_all_iff.mpr
    intro z
    apply ae_all_iff.mpr
    intro x
    simpa only [zero_add, add_comm x z] using hB.2.1 0 x z
  filter_upwards [hShiftOrigin, hMeans, hCov] with s hs hm hc
  have hInvariant (i : Fin 2) (z : Lattice) : u i (processShift z s) = u i s := by
    have hz : u i s = U i s := by
      simpa only [processShift_zero] using hm i 0
    exact (hm i z).trans hz.symm
  intro z
  -- The actual finite maxima agree for every horizon, including zero.
  refine (hs z).congr' (Eventually.of_forall fun n => ?_)
  congr 1
  apply Finset.sup'_congr (by dsimp [Δ]; exact Finset.insert_nonempty _ _) rfl
  intro x _
  rw [← hc z x, hInvariant 0 z, hInvariant 1 z]

end LPP.Busemann
