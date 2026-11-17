/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Frozen.Definitions.ForwardWeightSigma
public import Busemann.Frozen.Definitions.FiniteEdgeStep
import Busemann.Geometry.GeodesicOpenEdgePaths
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-! Forward-measurable open edges are exactly those traversed by an actual locally rightmost ray. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem measurable_forward_coordinate (u y : Lattice) (hy : u ≤ y) :
    Measurable[forwardWeightSigma u] (fun ω : Environment => ω y) := by
  have hcone : Measurable[forwardWeightSigma u]
      (fun ω : Environment => fun z : {z : Lattice // u ≤ z} => ω z.val) :=
    comap_measurable _
  exact (measurable_pi_apply ⟨y, hy⟩).comp hcone

private theorem measurable_forward_pathWeight {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    Measurable[forwardWeightSigma u] (fun ω : Environment => pathWeight ω p) := by
  classical
  simp only [pathWeight]
  exact Finset.univ.measurable_fun_sum fun j _ =>
    measurable_forward_coordinate u (p.vertex j.castSucc) (p.vertex_mem_Icc j.castSucc).1

private theorem measurable_forward_lastPassage (u : Lattice) (d : ℕ × ℕ) :
    Measurable[forwardWeightSigma u] (fun ω : Environment => lastPassage ω u d) := by
  classical
  let : MeasurableSpace Environment := forwardWeightSigma u
  have hsup : Measurable[forwardWeightSigma u]
      (Finset.univ.sup' Finset.univ_nonempty
        (fun p : Path u d => fun ω : Environment => pathWeight ω p)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => measurable_forward_pathWeight p
  have heq : (fun ω : Environment => lastPassage ω u d) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Path u d => fun ω : Environment => pathWeight ω p) := by
    funext ω
    simp [lastPassage, Finset.max'_eq_sup', Finset.sup'_image]
  rw [heq]
  exact hsup

private theorem measurable_open_geodesic_edge (u x : Lattice) (i : Fin 2) :
    @MeasurableSet Environment (forwardWeightSigma u) {ω |
      ∀ N : ℕ,
        x.1 + x.2 + 1 ≤ u.1 + u.2 + (N : ℤ) →
        ∃ (d : ℕ × ℕ) (p : Path u d),
          d.1 + d.2 = N ∧
          pathWeight ω p = lastPassage ω u d ∧
          (∀ q : Path u d,
            pathWeight ω q = lastPassage ω u d →
            ∀ j : Fin (d.1 + d.2 + 1),
              (q.vertex j).1 ≤ (p.vertex j).1) ∧
          ∃ k : Fin (d.1 + d.2),
            p.vertex k.castSucc = x ∧
              p.vertex k.succ = x + finiteEdgeStep i} := by
  classical
  let : MeasurableSpace Environment := forwardWeightSigma u
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro N
  apply (MeasurableSet.const _).imp
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro d
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  have hmax : MeasurableSet {ω : Environment |
      pathWeight ω p = lastPassage ω u d} :=
    measurableSet_eq_fun (measurable_forward_pathWeight p) (measurable_forward_lastPassage u d)
  have hgreat : MeasurableSet {ω : Environment |
      ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
        ∀ j : Fin (d.1 + d.2 + 1), (q.vertex j).1 ≤ (p.vertex j).1} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    exact (measurableSet_eq_fun (measurable_forward_pathWeight q)
      (measurable_forward_lastPassage u d)).imp (MeasurableSet.const _)
  exact (MeasurableSet.const _).inter (hmax.inter (hgreat.inter (MeasurableSet.const _)))

private theorem locallyRightmostGeodesic_level (ω : Environment) (u : Lattice)
    (γ : ℕ → Lattice) (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
    (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
  induction n with
  | zero => simp only [hγ.1, Nat.cast_zero, add_zero]
  | succ n ih =>
    rcases hγ.2.1 n with h | h
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [Prod.fst_add, Prod.snd_add] at hx hy
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [Prod.fst_add, Prod.snd_add] at hx hy
      simp only [Nat.cast_add, Nat.cast_one]
      omega

private theorem open_geodesic_edge_of_ray (u x : Lattice) (i : Fin 2)
    (ω : Environment) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hedge : ∃ k : ℕ, γ k = x ∧ γ (k + 1) = x + finiteEdgeStep i) :
    ∀ N : ℕ,
      x.1 + x.2 + 1 ≤ u.1 + u.2 + (N : ℤ) →
      ∃ (d : ℕ × ℕ) (p : Path u d),
        d.1 + d.2 = N ∧
        pathWeight ω p = lastPassage ω u d ∧
        (∀ q : Path u d,
          pathWeight ω q = lastPassage ω u d →
          ∀ j : Fin (d.1 + d.2 + 1),
            (q.vertex j).1 ≤ (p.vertex j).1) ∧
        ∃ k : Fin (d.1 + d.2),
          p.vertex k.castSucc = x ∧
            p.vertex k.succ = x + finiteEdgeStep i := by
  intro N hN
  obtain ⟨k, hk, hkstep⟩ := hedge
  have hlevel := locallyRightmostGeodesic_level ω u γ hγ k
  rw [hk] at hlevel
  have hkN : k + 1 ≤ N := by omega
  have hpos : 0 < N := by omega
  -- The actual positive root segment supplies the finite greatest witness.
  have hseg : ∃ (d : ℕ × ℕ) (p : Path u d),
      d.1 + d.2 = N ∧
      (∀ j : Fin (d.1 + d.2 + 1), p.vertex j = γ j.val) ∧
      pathWeight ω p = lastPassage ω u d ∧
      ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
        ∀ j : Fin (d.1 + d.2 + 1),
          (q.vertex j).1 ≤ (p.vertex j).1 ∧ (p.vertex j).2 ≤ (q.vertex j).2 := by
    have hs := hγ.2.2 0 N hpos
    rw [hγ.1] at hs
    simpa only [Nat.zero_add] using hs
  obtain ⟨d, p, hlen, htrace, hweight, hgreat⟩ := hseg
  let j : Fin (d.1 + d.2) := ⟨k, by omega⟩
  refine ⟨d, p, hlen, hweight, fun q hq a => (hgreat q hq a).1, j, ?_, ?_⟩
  · exact (htrace j.castSucc).trans hk
  · exact (htrace j.succ).trans hkstep

/-- An edge is open at every eligible finite horizon exactly when a genuine locally
rightmost ray traverses it. The event is measurable for the weights northeast of
its original signed root. Strong Existence, lines 1439–1449. -/
theorem measurable_open_geodesic_edge_iff_exists_ray
    (u x : Lattice) (hux : u ≤ x) (i : Fin 2) :
    let A : Set Environment := {ω |
      ∀ N : ℕ,
        x.1 + x.2 + 1 ≤ u.1 + u.2 + (N : ℤ) →
        ∃ (d : ℕ × ℕ) (p : Path u d),
          d.1 + d.2 = N ∧
          pathWeight ω p = lastPassage ω u d ∧
          (∀ q : Path u d,
            pathWeight ω q = lastPassage ω u d →
            ∀ j : Fin (d.1 + d.2 + 1),
              (q.vertex j).1 ≤ (p.vertex j).1) ∧
          ∃ k : Fin (d.1 + d.2),
            p.vertex k.castSucc = x ∧
              p.vertex k.succ = x + finiteEdgeStep i}
    @MeasurableSet Environment (forwardWeightSigma u) A ∧
      ∀ ω : Environment,
        ω ∈ A ↔
          ∃ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ ∧
              ∃ k : ℕ,
                γ k = x ∧ γ (k + 1) = x + finiteEdgeStep i
 := by
  -- Finite weights and comparisons use only the original forward field.
  refine ⟨measurable_open_geodesic_edge u x i, ?_⟩
  intro ω
  constructor
  · intro hOpen
    -- The finite compatibility and open-child recursion produce an actual ray.
    exact exists_locallyRightmostGeodesic_of_open_edge u x hux i ω hOpen
  · rintro ⟨γ, hγ, hedge⟩
    -- Every eligible positive root segment retains this same edge.
    exact open_geodesic_edge_of_ray u x i ω γ hγ hedge

end LPP.Busemann
