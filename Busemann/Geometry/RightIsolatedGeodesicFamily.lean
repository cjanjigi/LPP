/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.MeasurableGreatestGeodesicExtension
import LPP_Foundations.Model.Paths.HorizontalFirst
import LPP_Foundations.Model.LastPassage.Axes
import Mathlib.Tactic

/-! A countable family of right-isolated locally rightmost geodesics. -/

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem east_ray (ω : Environment) (u : Lattice) :
    IsLocallyRightmostGeodesic ω u (fun n => u + ((n : ℤ), (0 : ℤ))) := by
  constructor
  · simp
  constructor
  · intro n
    left
    apply Prod.ext <;> simp [Nat.cast_add, add_assoc]
  · intro m N hN
    let v : Lattice := u + ((m : ℤ), (0 : ℤ))
    let p : LPPDifferentiability.Path v (N, 0) := horizontalFirst v (N, 0)
    refine ⟨(N, 0), p, by simp, ?_, ?_, ?_⟩
    · intro i
      rw [p.vertex_horizontal]
      dsimp only [v]
      apply Prod.ext <;> simp [Nat.cast_add, add_assoc]
    · rw [lastPassage_horizontal, pathWeight_horizontal]
    · intro q hq i
      rw [q.vertex_horizontal, p.vertex_horizontal]
      exact ⟨le_rfl, le_rfl⟩

private theorem ray_le_east (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) :
    pathSoutheastLE γ (fun n => u + ((n : ℤ), (0 : ℤ))) := by
  have hb (n : ℕ) : (γ n).1 ≤ u.1 + (n : ℤ) ∧ u.2 ≤ (γ n).2 := by
    induction n with
    | zero => simp [hγ.1]
    | succ n ih =>
      rcases hγ.2.1 n with h | h <;> rw [h] <;>
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> omega
  intro m n hm
  have hroot := hγ.1
  simp only [hroot, Prod.fst_add, Prod.snd_add, Nat.cast_zero, add_zero] at hm
  have hmn : m = n := by omega
  subst n
  simpa only [Prod.fst_add, Prod.snd_add, add_zero] using hb m

private theorem same_root_antisymm (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ)
    (hγδ : pathSoutheastLE γ δ) (hδγ : pathSoutheastLE δ γ) : γ = δ := by
  funext n
  have ha := hγδ n n (by rw [hγ.1, hδ.1])
  have hb := hδγ n n (by rw [hγ.1, hδ.1])
  exact Prod.ext (le_antisymm ha.1 hb.1) (le_antisymm hb.2 ha.2)

private theorem actual_prefix (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) (N : ℕ) :
    ∃ (e : ℕ × ℕ) (q : Path u e), e.1 + e.2 = N ∧
      ∀ j : Fin (e.1 + e.2 + 1), γ j.val = q.vertex j := by
  by_cases hN : N = 0
  · subst N
    refine ⟨(0, 0), horizontalFirst u (0, 0), rfl, ?_⟩
    intro j
    have hj : j = 0 := by apply Fin.ext; have := j.isLt; omega
    subst j
    exact hγ.1.trans (horizontalFirst u (0, 0)).start.symm
  · have hs := hγ.2.2 0 N (Nat.pos_of_ne_zero hN)
    rw [hγ.1] at hs
    obtain ⟨e, q, hl, ht, _⟩ := hs
    exact ⟨e, q, hl, fun j => by simpa only [Nat.zero_add] using (ht j).symm⟩

/-- A single forward-measurable family enumerates the source's greatest
realized-prefix rays, including the east axis, and is right-dense.
Strong Existence, lines 205, 725–736 and 1439–1506. -/
theorem exists_unique_measurable_right_isolated_geodesic_family
    (u : Lattice) :
    ∃! R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice),
      (∀ i : Σ d : ℕ × ℕ, Path u d,
        @Measurable Environment (ℕ → Lattice) (forwardWeightSigma u)
          (inferInstance : MeasurableSpace (ℕ → Lattice)) (R i)) ∧
      (∀ (i : Σ d : ℕ × ℕ, Path u d) (ω : Environment),
        let A : Prop := ∃ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ ∧
          ∀ k : Fin (i.1.1 + i.1.2 + 1), i.2.vertex k = γ k.val
        (A → IsLocallyRightmostGeodesic ω u (R i ω) ∧
          (∀ k : Fin (i.1.1 + i.1.2 + 1), R i ω k.val = i.2.vertex k) ∧
          ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
            (∀ k : Fin (i.1.1 + i.1.2 + 1), γ k.val = i.2.vertex k) →
            pathSoutheastLE γ (R i ω)) ∧
        (¬ A → ∀ n : ℕ, R i ω n = u + ((n : ℤ), (0 : ℤ)))) ∧
      (∀ (i : Σ d : ℕ × ℕ, Path u d) (ω : Environment),
        ∃ (e : ℕ × ℕ) (q : Path u e),
          IsLocallyRightmostGeodesic ω u (R i ω) ∧
          (∀ k : Fin (e.1 + e.2 + 1), (R i ω) k.val = q.vertex k) ∧
          ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
            (∀ k : Fin (e.1 + e.2 + 1), γ k.val = q.vertex k) →
            pathSoutheastLE γ (R i ω)) ∧
      (∀ (ω : Environment) (γ : ℕ → Lattice),
        IsLocallyRightmostGeodesic ω u γ →
        ¬ (∀ n : ℕ, γ n = u + ((n : ℤ), (0 : ℤ))) →
        ¬ (∀ n : ℕ, γ n = u + ((0 : ℤ), (n : ℤ))) →
        ((∃ N : ℕ, ∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          pathSoutheastLE γ δ → δ ≠ γ →
          ∃ k : ℕ, k ≤ N ∧ γ k ≠ δ k) ↔
          ∃ i : Σ d : ℕ × ℕ, Path u d, R i ω = γ)) ∧
      (∀ (ω : Environment) (γ : ℕ → Lattice),
        IsLocallyRightmostGeodesic ω u γ →
        ∀ N : ℕ, ∃ i : Σ d : ℕ × ℕ, Path u d,
          pathSoutheastLE γ (R i ω) ∧
          ∀ k : ℕ, k ≤ N → R i ω k = γ k)
 := by
  classical
  let I := Σ d : ℕ × ℕ, Path u d
  let R : I → Environment → (ℕ → Lattice) := fun i =>
    Classical.choose (exists_unique_measurable_greatest_geodesic_prefix_extension u i.1 i.2)
  have hR (i : I) :=
    (Classical.choose_spec (exists_unique_measurable_greatest_geodesic_prefix_extension u i.1 i.2)).1
  have hRuniq (i : I) :=
    (Classical.choose_spec (exists_unique_measurable_greatest_geodesic_prefix_extension u i.1 i.2)).2
  have hclass (i : I) (ω : Environment) :
      ∃ (e : ℕ × ℕ) (q : Path u e),
        IsLocallyRightmostGeodesic ω u (R i ω) ∧
        (∀ k : Fin (e.1 + e.2 + 1), (R i ω) k.val = q.vertex k) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (∀ k : Fin (e.1 + e.2 + 1), γ k.val = q.vertex k) →
          pathSoutheastLE γ (R i ω) := by
    by_cases hA : ∃ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ ∧
        ∀ k : Fin (i.1.1 + i.1.2 + 1), i.2.vertex k = γ k.val
    · exact ⟨i.1, i.2, (hR i).2 ω |>.1 hA⟩
    · have haxis : R i ω = fun (n : ℕ) => u + ((n : ℤ), (0 : ℤ)) := by
        funext n
        exact (hR i).2 ω |>.2 hA n
      refine ⟨(0, 0), horizontalFirst u (0, 0), ?_, ?_, ?_⟩
      · rw [haxis]
        exact east_ray ω u
      · intro k
        have hk : k = 0 := by apply Fin.ext; have := k.isLt; omega
        subst k
        rw [haxis]
        change u + (0 : Lattice) = (horizontalFirst u (0, 0)).vertex 0
        simpa only [add_zero] using (horizontalFirst u (0, 0)).start.symm
      · intro γ hγ _
        rw [haxis]
        exact ray_le_east ω u γ hγ
  have happrox (ω : Environment) (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) (N : ℕ) :
      ∃ i : I, pathSoutheastLE γ (R i ω) ∧
        ∀ k : ℕ, k ≤ N → R i ω k = γ k := by
    obtain ⟨e, q, hlen, htrace⟩ := actual_prefix ω u γ hγ N
    let i : I := ⟨e, q⟩
    have hA : ∃ δ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u δ ∧
        ∀ k : Fin (e.1 + e.2 + 1), q.vertex k = δ k.val :=
      ⟨γ, hγ, fun k => (htrace k).symm⟩
    have hgood := (hR i).2 ω |>.1 hA
    refine ⟨i, hgood.2.2 γ hγ htrace, ?_⟩
    intro k hk
    let j : Fin (e.1 + e.2 + 1) := ⟨k, by omega⟩
    exact (hgood.2.1 j).trans (htrace j).symm
  refine ⟨R, ⟨fun i => (hR i).1, fun i ω => (hR i).2 ω, hclass, ?_, happrox⟩, ?_⟩
  · intro ω γ hγ _hneEast _hneNorth
    constructor
    · rintro ⟨N, hIso⟩
      obtain ⟨i, horder, hsame⟩ := happrox ω γ hγ N
      by_cases heq : R i ω = γ
      · exact ⟨i, heq⟩
      · obtain ⟨_e, _q, hreal, _htrace, _hgreat⟩ := hclass i ω
        obtain ⟨k, hk, hneq⟩ := hIso (R i ω) hreal horder heq
        exact (hneq (hsame k hk).symm).elim
    · rintro ⟨i, rfl⟩
      obtain ⟨e, q, hreal, htrace, hgreat⟩ := hclass i ω
      refine ⟨e.1 + e.2, ?_⟩
      intro δ hδ horder hne
      by_contra hnot
      push Not at hnot
      have hδtrace : ∀ k : Fin (e.1 + e.2 + 1), δ k.val = q.vertex k := by
        intro k
        have hk : k.val ≤ e.1 + e.2 := by have := k.isLt; omega
        exact (hnot k.val hk).symm.trans (htrace k)
      have hreverse := hgreat δ hδ hδtrace
      exact hne (same_root_antisymm ω u δ (R i ω) hδ hreal hreverse horder)
  · intro S hS
    funext i
    exact hRuniq i (S i) ⟨hS.1 i, hS.2.1 i⟩

end LPP.Busemann
