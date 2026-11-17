/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Frozen.Definitions.FiniteEdgeStep
import LPP_Foundations.Model.LastPassage.RightmostFinite
import LPP_Foundations.Model.LastPassage.RightmostSegments
import LPP_Foundations.Model.Paths.Split
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! Infinite continuation along the source's open geodesic edges. -/

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

private abbrev Greatest (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : Prop :=
  pathWeight ω p = lastPassage ω u d ∧
    ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
      ∀ j : Fin (d.1 + d.2 + 1), (q.vertex j).1 ≤ (p.vertex j).1

private def OpenEdge (ω : Environment) (u x : Lattice) (i : Fin 2) : Prop :=
  ∀ N : ℕ, x.1 + x.2 + 1 ≤ u.1 + u.2 + (N : ℤ) →
    ∃ (d : ℕ × ℕ) (p : Path u d),
      d.1 + d.2 = N ∧ pathWeight ω p = lastPassage ω u d ∧
      (∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
        ∀ j : Fin (d.1 + d.2 + 1), (q.vertex j).1 ≤ (p.vertex j).1) ∧
      ∃ k : Fin (d.1 + d.2),
        p.vertex k.castSucc = x ∧ p.vertex k.succ = x + finiteEdgeStep i

private theorem step_cases (i : Fin 2) :
    finiteEdgeStep i = ((1 : ℤ), (0 : ℤ)) ∨
      finiteEdgeStep i = ((0 : ℤ), (1 : ℤ)) := by
  fin_cases i <;> simp [finiteEdgeStep]

private theorem step_level (x : Lattice) (i : Fin 2) :
    (x + finiteEdgeStep i).1 + (x + finiteEdgeStep i).2 = x.1 + x.2 + 1 := by
  rcases step_cases i with h | h <;> rw [h] <;>
    simp only [Prod.fst_add, Prod.snd_add] <;> omega

private theorem step_le (x : Lattice) (i : Fin 2) : x ≤ x + finiteEdgeStep i := by
  rcases step_cases i with h | h <;> rw [h] <;> constructor <;>
    simp only [Prod.fst_add, Prod.snd_add] <;> omega

-- Restriction keeps both the actual edge and the greatestness property.
private theorem restrict_edge (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (hp : Greatest ω p) (N : ℕ) (hN : N ≤ d.1 + d.2)
    (k : Fin (d.1 + d.2)) (hkN : k.val < N)
    (x : Lattice) (i : Fin 2)
    (hx : p.vertex k.castSucc = x) (hy : p.vertex k.succ = x + finiteEdgeStep i) :
    ∃ (e : ℕ × ℕ) (q : Path u e),
      e.1 + e.2 = N ∧ pathWeight ω q = lastPassage ω u e ∧
      (∀ r : Path u e, pathWeight ω r = lastPassage ω u e →
        ∀ j : Fin (e.1 + e.2 + 1), (r.vertex j).1 ≤ (q.vertex j).1) ∧
      ∃ j : Fin (e.1 + e.2),
        q.vertex j.castSucc = x ∧ q.vertex j.succ = x + finiteEdgeStep i := by
  let cut : Fin (d.1 + d.2 + 1) := ⟨N, by omega⟩
  have hlen : (p.splitDisplacement cut).1 + (p.splitDisplacement cut).2 = N :=
    p.splitDisplacement_length cut
  have hg := (p.rightmost_maximizing_segments ω hp.1 hp.2 cut).1
  refine ⟨p.splitDisplacement cut, p.prefixPath cut, hlen, hg.1, hg.2,
    ⟨k.val, by omega⟩, ?_, ?_⟩
  · change p.vertex _ = x
    exact hx
  · change p.vertex _ = x + finiteEdgeStep i
    exact hy

-- Two failed child horizons contradict an incoming witness at their maximum.
private theorem open_has_child (ω : Environment) (u x : Lattice)
    (i : Fin 2) (hOpen : OpenEdge ω u x i) :
    ∃ j : Fin 2, OpenEdge ω u (x + finiteEdgeStep i) j := by
  classical
  let y := x + finiteEdgeStep i
  by_contra hNo
  have hNo0 : ¬ OpenEdge ω u y 0 := fun h => hNo ⟨0, h⟩
  have hNo1 : ¬ OpenEdge ω u y 1 := fun h => hNo ⟨1, h⟩
  unfold OpenEdge at hNo0 hNo1
  obtain ⟨N0, h0⟩ := not_forall.mp hNo0
  obtain ⟨N1, h1⟩ := not_forall.mp hNo1
  obtain ⟨hGuard0, hFail0⟩ := not_imp.mp h0
  obtain ⟨hGuard1, hFail1⟩ := not_imp.mp h1
  let M := max N0 N1
  have hM0 : N0 ≤ M := Nat.le_max_left _ _
  have hM1 : N1 ≤ M := Nat.le_max_right _ _
  have hyLevel : y.1 + y.2 = x.1 + x.2 + 1 := step_level x i
  have hM : x.1 + x.2 + 1 ≤ u.1 + u.2 + (M : ℤ) := by omega
  obtain ⟨d, p, hlen, hp, hg, k, hx, hy⟩ := hOpen M hM
  have hkLevel := p.level k.succ
  rw [hy] at hkLevel
  change y.1 + y.2 = u.1 + u.2 + ((k.val + 1 : ℕ) : ℤ) at hkLevel
  have hk0 : k.val + 1 < N0 := by omega
  have hk1 : k.val + 1 < N1 := by omega
  let j : Fin (d.1 + d.2) := ⟨k.val + 1, by omega⟩
  have hj : p.vertex j.castSucc = y := by
    exact hy
  rcases p.step j with hEast | hNorth
  · apply hFail0
    apply restrict_edge ω p ⟨hp, hg⟩ N0 (by omega) j hk0 y 0 hj
    rw [hEast, hj]
    rfl
  · apply hFail1
    apply restrict_edge ω p ⟨hp, hg⟩ N1 (by omega) j hk1 y 1 hj
    rw [hNorth, hj]
    rfl

-- This is finite uniqueness, including the displacement forced by a signed endpoint.
private theorem greatest_endpoint_vertices (ω : Environment) {u : Lattice}
    {d e : ℕ × ℕ} (p : Path u d) (q : Path u e)
    (hp : Greatest ω p) (hq : Greatest ω q)
    (hend : p.vertex (Fin.last (d.1 + d.2)) =
      q.vertex (Fin.last (e.1 + e.2)))
    (a : Fin (d.1 + d.2 + 1)) (b : Fin (e.1 + e.2 + 1))
    (hab : a.val = b.val) : p.vertex a = q.vertex b := by
  have hde : d = e := by
    rw [p.finish, q.finish] at hend
    have hx := congrArg Prod.fst hend
    have hy := congrArg Prod.snd hend
    simp only [Prod.fst_add, Prod.snd_add] at hx hy
    apply Prod.ext <;> omega
  subst e
  have hpq : p = q := (exists_unique_rightmost_maximizing_path ω u d).unique hp hq
  rw [hpq]
  exact congrArg q.vertex (Fin.ext hab)

/-- Geometry-only forward implication of the exact open-edge target.
All finite-horizon greatest witnesses are actual u-rooted Paths. -/
theorem exists_locallyRightmostGeodesic_of_open_edge
    (u x : Lattice) (hux : u ≤ x) (i : Fin 2) (ω : Environment)
    (hOpen : ∀ N : ℕ,
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
            p.vertex k.succ = x + finiteEdgeStep i) :
    ∃ γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u γ ∧
        ∃ k : ℕ, γ k = x ∧ γ (k + 1) = x + finiteEdgeStep i := by
  classical
  change OpenEdge ω u x i at hOpen
  -- The first eligible signed horizon fixes the initial finite prefix.
  let L : ℕ := (x.1 + x.2 + 1 - (u.1 + u.2)).toNat
  have hL : u.1 + u.2 + (L : ℤ) = x.1 + x.2 + 1 := by
    have hx1 := hux.1
    have hx2 := hux.2
    have hcast : (L : ℤ) = x.1 + x.2 + 1 - (u.1 + u.2) :=
      Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨d0, p0, hlen0, hw0, hg0, k0, hx0, hy0⟩ := hOpen L (by omega)
  have hkLast : k0.val + 1 = d0.1 + d0.2 := by
    have hk := p0.level k0.castSucc
    rw [hx0] at hk
    simp only [Fin.val_castSucc] at hk
    omega
  have hEnd0 : p0.vertex (Fin.last (d0.1 + d0.2)) = x + finiteEdgeStep i := by
    have hidx : k0.succ = Fin.last (d0.1 + d0.2) := by
      apply Fin.ext
      simpa only [Fin.val_succ, Fin.val_last] using hkLast
    rw [← hidx]
    exact hy0
  -- Every state is an actual open outgoing edge. Choice is proof-local.
  let S := {a : Lattice × Fin 2 // u ≤ a.1 ∧ OpenEdge ω u a.1 a.2}
  let initial : S := ⟨(x, i), hux, hOpen⟩
  let f : S → S := fun a =>
    ⟨(a.val.1 + finiteEdgeStep a.val.2,
      Classical.choose (open_has_child ω u a.val.1 a.val.2 a.property.2)),
      le_trans a.property.1 (step_le a.val.1 a.val.2),
      Classical.choose_spec (open_has_child ω u a.val.1 a.val.2 a.property.2)⟩
  let e : ℕ → S := fun n => f^[n] (f initial)
  let θ : ℕ → Lattice := fun n => (e n).val.1
  have heNext (n : ℕ) : e (n + 1) = f (e n) :=
    Function.iterate_succ_apply' f n (f initial)
  have hθ0 : θ 0 = x + finiteEdgeStep i := by rfl
  have hθStep (n : ℕ) : θ (n + 1) = θ n + finiteEdgeStep (e n).val.2 := by
    change (e (n + 1)).val.1 = _
    rw [heNext]
  have hθOpen (n : ℕ) : OpenEdge ω u (θ n) (e n).val.2 := (e n).property.2
  let γ : ℕ → Lattice := fun n =>
    if hn : n ≤ L then p0.vertex ⟨n, by omega⟩ else θ (n - L)
  have hInitial (n : ℕ) (hn : n ≤ L) :
      γ n = p0.vertex ⟨n, by omega⟩ := by simp only [γ, dite_eq_left hn]
  have hTail (n : ℕ) : γ (L + n) = θ n := by
    cases n with
    | zero =>
      simp only [Nat.add_zero]
      rw [hInitial L (by omega)]
      convert hEnd0.trans hθ0.symm using 1
      congr 1
      apply Fin.ext
      simpa only [Fin.val_last] using hlen0.symm
    | succ n =>
      dsimp only [γ]
      rw [dite_eq_right (by omega)]
      congr 1
      omega
  have hStart : γ 0 = u := (hInitial 0 (by omega)).trans p0.start
  have hStep (n : ℕ) :
      γ (n + 1) = γ n + (1, 0) ∨ γ (n + 1) = γ n + (0, 1) := by
    by_cases hn : n < L
    · rw [hInitial n (by omega), hInitial (n + 1) (by omega)]
      exact p0.step ⟨n, by omega⟩
    · let t := n - L
      rw [show n = L + t by dsimp [t]; omega,
        show L + t + 1 = L + (t + 1) by omega, hTail, hTail, hθStep]
      rcases step_cases (e t).val.2 with h | h <;> simp only [h] <;> tauto
  have hLevel (n : ℕ) : (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
    induction n with
    | zero => simp only [hStart, Nat.cast_zero, add_zero]
    | succ n ih =>
      rcases hStep n with h | h <;> rw [h] <;>
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> omega
  -- Each root prefix is an actual greatest path; no ray-extension assertion is used.
  have hPrefix (N : ℕ) : ∃ (d : ℕ × ℕ) (p : Path u d),
      d.1 + d.2 = N ∧ Greatest ω p ∧
        ∀ j : Fin (d.1 + d.2 + 1), p.vertex j = γ j.val := by
    induction N using Nat.strong_induction_on with
    | h N ih =>
      by_cases hNL : N ≤ L
      · let cut : Fin (d0.1 + d0.2 + 1) := ⟨N, by omega⟩
        have hlen : (p0.splitDisplacement cut).1 + (p0.splitDisplacement cut).2 = N :=
          p0.splitDisplacement_length cut
        have hgreat := (p0.rightmost_maximizing_segments ω hw0 hg0 cut).1
        refine ⟨p0.splitDisplacement cut, p0.prefixPath cut, hlen, hgreat, ?_⟩
        intro j
        change p0.vertex _ = γ j.val
        exact (hInitial j.val (by have hj := j.isLt; omega)).symm
      · have hNpos : 0 < N := by omega
        let t := N - 1 - L
        have hprev : N - 1 = L + t := by dsimp [t]; omega
        have hcur : N = L + (t + 1) := by dsimp [t]; omega
        have hγprev : γ (N - 1) = θ t := by rw [hprev, hTail]
        have hγcur : γ N = θ (t + 1) := by rw [hcur, hTail]
        have hlev : (θ t).1 + (θ t).2 = u.1 + u.2 + ((N - 1 : ℕ) : ℤ) := by
          rw [← hγprev]
          exact hLevel (N - 1)
        obtain ⟨d, q, hlen, hw, hg, k, hx, hy⟩ :=
          hθOpen t N (by omega)
        have hk : k.val = N - 1 := by
          have hklev := q.level k.castSucc
          rw [hx] at hklev
          simp only [Fin.val_castSucc] at hklev
          omega
        have hEnd : q.vertex (Fin.last (d.1 + d.2)) = γ N := by
          have hidx : k.succ = Fin.last (d.1 + d.2) := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_last]
            omega
          rw [← hidx, hy, ← hθStep, ← hγcur]
        obtain ⟨a, p, hplen, hpg, hptrace⟩ := ih (N - 1) (by omega)
        let cut := k.castSucc
        have hprelen : (q.splitDisplacement cut).1 + (q.splitDisplacement cut).2 =
            N - 1 := (q.splitDisplacement_length cut).trans hk
        have hpre := (q.rightmost_maximizing_segments ω hw hg cut).1
        have hEndPre : (q.prefixPath cut).vertex
            (Fin.last ((q.splitDisplacement cut).1 + (q.splitDisplacement cut).2)) =
              γ (N - 1) := by
          exact (q.prefixPath cut).finish.trans
            ((q.split_vertex cut).symm.trans (hx.trans hγprev.symm))
        have hEndP : p.vertex (Fin.last (a.1 + a.2)) = γ (N - 1) := by
          rw [hptrace]
          simp only [Fin.val_last, hplen]
        refine ⟨d, q, hlen, ⟨hw, hg⟩, ?_⟩
        intro j
        by_cases hj : j.val < N
        · let b : Fin ((q.splitDisplacement cut).1 + (q.splitDisplacement cut).2 + 1) :=
            ⟨j.val, by omega⟩
          let c : Fin (a.1 + a.2 + 1) := ⟨j.val, by omega⟩
          have heq := greatest_endpoint_vertices ω (q.prefixPath cut) p hpre hpg
            (hEndPre.trans hEndP.symm) b c rfl
          change q.vertex _ = p.vertex c at heq
          have hindex :
              (⟨b.val, j.isLt⟩ :
                Fin (d.1 + d.2 + 1)) = j := Fin.ext rfl
          rw [hindex] at heq
          exact heq.trans (hptrace c)
        · have hjLast : j = Fin.last (d.1 + d.2) := by
            apply Fin.ext
            simp only [Fin.val_last]
            have hji := j.isLt
            omega
          rw [hjLast]
          simpa only [Fin.val_last, hlen] using hEnd
  refine ⟨γ, ⟨hStart, hStep, ?_⟩, ?_⟩
  · intro m N _hN
    obtain ⟨d, p, hlen, hp, htrace⟩ := hPrefix (m + N)
    let cut : Fin (d.1 + d.2 + 1) := ⟨m, by omega⟩
    let e := d - p.splitDisplacement cut
    have hslen : e.1 + e.2 = N := by
      have h : e.1 + e.2 = d.1 + d.2 - m := p.suffix_length cut
      omega
    have hs := (p.rightmost_maximizing_segments ω hp.1 hp.2 cut).2
    have hroot : p.vertex cut = γ m := htrace cut
    refine ⟨e, ?_⟩
    rw [← hroot]
    refine ⟨p.suffix cut, hslen, ?_, hs.1, ?_⟩
    · intro j
      change p.vertex _ = γ (m + j.val)
      exact htrace ⟨m + j.val, by have hj := j.isLt; omega⟩
    · intro q hq j
      have hx := hs.2 q hq j
      have hpl := (p.suffix cut).level j
      have hql := q.level j
      exact ⟨hx, by omega⟩
  · refine ⟨k0.val, ?_, ?_⟩
    · exact (hInitial k0.val (by have hk := k0.isLt; omega)).trans hx0
    · exact (hInitial (k0.val + 1) (by omega)).trans hy0

end LPP.Busemann
