/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicOpenEdges
public import Busemann.Geometry.GeodesicPrefixOrder
import LPP_Foundations.Model.LastPassage.Axes
import Mathlib.Tactic

/-! Forward measurability of realized finite geodesic prefixes. -/

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem ray_level (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
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

private theorem exists_root_ray (ω : Environment) (u : Lattice) :
    ∃ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ := by
  have hopen := measurable_open_geodesic_edge_iff_exists_ray u u le_rfl (0 : Fin 2)
  have hmem : ω ∈ (let A : Set Environment := {ω |
      ∀ N : ℕ, u.1 + u.2 + 1 ≤ u.1 + u.2 + (N : ℤ) →
        ∃ (d : ℕ × ℕ) (p : Path u d), d.1 + d.2 = N ∧
          pathWeight ω p = lastPassage ω u d ∧
          (∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
            ∀ j : Fin (d.1 + d.2 + 1), (q.vertex j).1 ≤ (p.vertex j).1) ∧
          ∃ k : Fin (d.1 + d.2), p.vertex k.castSucc = u ∧
            p.vertex k.succ = u + finiteEdgeStep (0 : Fin 2)}; A) := by
    intro N hN
    have hpos : 0 < N := by omega
    obtain ⟨p, ⟨hp, hg⟩, _⟩ := exists_unique_rightmost_maximizing_path ω u (N, 0)
    let k : Fin (N + 0) := ⟨0, by omega⟩
    refine ⟨(N, 0), p, by simp, hp, hg, k, ?_, ?_⟩
    · simp only [Path.vertex_horizontal, Fin.val_castSucc, k, Nat.cast_zero, add_zero,
        Prod.mk.eta]
    · rw [p.vertex_horizontal]
      simp [k, finiteEdgeStep, Prod.ext_iff]
  obtain ⟨γ, hγ, _⟩ := (hopen.2 ω).1 hmem
  exact ⟨γ, hγ⟩

/-- Realization of an actual fixed finite prefix is measurable from the weights
northeast of its signed root, including prefixes of length zero. -/
theorem measurableSet_realized_locallyRightmostGeodesic_prefix
    (u : LPPDifferentiability.Lattice) (d : ℕ × ℕ)
    (p : LPPDifferentiability.Path u d) :
    @MeasurableSet LPPDifferentiability.Environment (forwardWeightSigma u)
      {ω | ∃ γ : ℕ → LPPDifferentiability.Lattice,
        IsLocallyRightmostGeodesic ω u γ ∧
          ∀ j : Fin (d.1 + d.2 + 1), p.vertex j = γ j.val}
 := by
  classical
  let L := d.1 + d.2
  let edge (j : Fin L) : Fin 2 :=
    if p.vertex j.succ = p.vertex j.castSucc + ((1 : ℤ), (0 : ℤ)) then 0 else 1
  have hstep (j : Fin L) :
      p.vertex j.succ = p.vertex j.castSucc + finiteEdgeStep (edge j) := by
    dsimp only [edge]
    split_ifs with h
    · simpa [finiteEdgeStep] using h
    · have hs := p.step j
      rcases hs with he | hn
      · exact (h he).elim
      · simpa [finiteEdgeStep] using hn
  let E (j : Fin L) : Set Environment := {ω |
    ∀ N : ℕ,
      (p.vertex j.castSucc).1 + (p.vertex j.castSucc).2 + 1 ≤
          u.1 + u.2 + (N : ℤ) →
      ∃ (e : ℕ × ℕ) (q : Path u e), e.1 + e.2 = N ∧
        pathWeight ω q = lastPassage ω u e ∧
        (∀ r : Path u e, pathWeight ω r = lastPassage ω u e →
          ∀ i : Fin (e.1 + e.2 + 1), (r.vertex i).1 ≤ (q.vertex i).1) ∧
        ∃ i : Fin (e.1 + e.2), q.vertex i.castSucc = p.vertex j.castSucc ∧
          q.vertex i.succ = p.vertex j.castSucc + finiteEdgeStep (edge j)}
  have hEdge (j : Fin L) :=
    measurable_open_geodesic_edge_iff_exists_ray u (p.vertex j.castSucc)
      ((p.vertex_mem_Icc j.castSucc).1) (edge j)
  have hmeas : @MeasurableSet Environment (forwardWeightSigma u) (⋂ j, E j) :=
    MeasurableSet.iInter fun j => (hEdge j).1
  have hevent : {ω : Environment | ∃ γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u γ ∧
        ∀ j : Fin (d.1 + d.2 + 1), p.vertex j = γ j.val} = ⋂ j, E j := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro ⟨γ, hγ, htrace⟩ j
      apply ((hEdge j).2 ω).2
      refine ⟨γ, hγ, j.val, ?_, ?_⟩
      · exact (htrace j.castSucc).symm
      · simpa only [Fin.val_succ] using (htrace j.succ).symm.trans (hstep j)
    · intro hAll
      -- Inductively replace the current ray by the ray containing the next edge.
      have hglue (t : ℕ) (ht : t ≤ L) :
          ∃ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ ∧
            ∀ j : ℕ, ∀ hj : j ≤ t, p.vertex ⟨j, by omega⟩ = γ j := by
        induction t with
        | zero =>
          obtain ⟨γ, hγ⟩ := exists_root_ray ω u
          refine ⟨γ, hγ, ?_⟩
          intro j hj
          have hj0 : j = 0 := by omega
          subst j
          exact p.start.trans hγ.1.symm
        | succ t ih =>
          have ht' : t ≤ L := by omega
          obtain ⟨γ, hγ, htrace⟩ := ih ht'
          let j : Fin L := ⟨t, by omega⟩
          obtain ⟨δ, hδ, m, hm, hmnext⟩ := ((hEdge j).2 ω).1 (hAll j)
          have hlδ := ray_level ω u δ hδ m
          have hlp := p.level j.castSucc
          simp only [Fin.val_castSucc] at hlp
          rw [hm] at hlδ
          have hmt : m = t := by dsimp only [j] at *; omega
          subst m
          have hmeet : γ t = δ t := (htrace t (le_refl t)).symm.trans hm.symm
          have hprefix := locallyRightmostGeodesic_eq_prefix_of_meet ω u γ δ hγ hδ t hmeet
          refine ⟨δ, hδ, ?_⟩
          intro n hn
          by_cases hnt : n ≤ t
          · exact (htrace n hnt).trans (hprefix n hnt)
          · have hn' : n = t + 1 := by omega
            subst n
            exact (hstep j).trans hmnext.symm
      obtain ⟨γ, hγ, htrace⟩ := hglue L le_rfl
      refine ⟨γ, hγ, ?_⟩
      intro j
      exact htrace j.val (by have := j.isLt; dsimp only [L] at *; omega)
  rw [hevent]
  exact hmeas

end LPP.Busemann
