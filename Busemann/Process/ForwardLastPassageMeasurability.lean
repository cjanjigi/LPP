/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.ForwardWeightSigma
public import LPP_Foundations.Frozen.Model.LastPassage
import LPP_Foundations.Model.Paths.Geometry

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem measurable_forward_coordinate (u y : Lattice) (hy : u ≤ y) :
    Measurable[forwardWeightSigma u] (fun ω : Environment => ω y) := by
  have hcone : Measurable[forwardWeightSigma u]
      (fun ω : Environment => fun z : {z : Lattice // u ≤ z} => ω z.val) :=
    comap_measurable _
  exact (measurable_pi_apply ⟨y, hy⟩).comp hcone

private theorem measurable_forward_pathWeight {u x : Lattice} {d : ℕ × ℕ}
    (hux : u ≤ x) (p : Path x d) :
    Measurable[forwardWeightSigma u] (fun ω : Environment => pathWeight ω p) := by
  classical
  simp only [pathWeight]
  exact Finset.univ.measurable_fun_sum fun j _ =>
    measurable_forward_coordinate u (p.vertex j.castSucc)
      (hux.trans (p.vertex_mem_Icc j.castSucc).1)

/-- A finite last-passage value from x uses only weights northeast of any
u ≤ x. This is the fixed-displacement measurability step needed after the
ray-version conclusion in public Strong Existence, line 999. -/
theorem measurable_forward_lastPassage_of_le
    (u x : Lattice) (hux : u ≤ x) (d : ℕ × ℕ) :
    @Measurable Environment ℝ (forwardWeightSigma u) inferInstance
      (fun ω => lastPassage ω x d) := by
  classical
  let : MeasurableSpace Environment := forwardWeightSigma u
  have hsup : Measurable[forwardWeightSigma u]
      (Finset.univ.sup' Finset.univ_nonempty
        (fun p : Path x d => fun ω : Environment => pathWeight ω p)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ =>
      measurable_forward_pathWeight hux p
  have heq : (fun ω : Environment => lastPassage ω x d) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Path x d => fun ω : Environment => pathWeight ω p) := by
    funext ω
    simp [lastPassage, Finset.max'_eq_sup', Finset.sup'_image]
  rw [heq]
  exact hsup

end LPP.Busemann
