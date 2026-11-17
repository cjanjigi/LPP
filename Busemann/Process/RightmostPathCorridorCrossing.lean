/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathOuterContact
import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Last west entry and first north exit of a ray meeting the preserved middle tail. -/

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

private theorem crossing_step (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (1, 0) ∨
      rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (0, 1) := by
  simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
    rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n)

private theorem crossing_level (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    (rightmostCocyclePath C x n).1 + (rightmostCocyclePath C x n).2 =
      x.1 + x.2 + (n : ℤ) := by
  induction n with
  | zero => simp only [rightmostCocyclePath, Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n ih =>
      rcases crossing_step C x n with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

private theorem crossing_monotone (C : Lattice → Lattice → ℝ) (x : Lattice) :
    Monotone (fun n => (rightmostCocyclePath C x n).1) ∧
      Monotone (fun n => (rightmostCocyclePath C x n).2) := by
  constructor
  · apply monotone_nat_of_le_succ
    intro n
    rcases crossing_step C x n with h | h <;> simp only [h, Prod.fst_add] <;> omega
  · apply monotone_nat_of_le_succ
    intro n
    rcases crossing_step C x n with h | h <;> simp only [h, Prod.snd_add] <;> omega

private theorem crossing_restart (C : Lattice → Lattice → ℝ) (x : Lattice) (a b : ℕ) :
    rightmostCocyclePath C (rightmostCocyclePath C x a) b =
      rightmostCocyclePath C x (a + b) := by
  change (rightmostCocycleSuccessor C)^[b] ((rightmostCocycleSuccessor C)^[a] x) =
    (rightmostCocycleSuccessor C)^[a + b] x
  rw [Nat.add_comm a b, Function.iterate_add_apply]

private theorem crossing_first_hit
    (f : ℕ → ℤ) (hUnit : ∀ n, f n ≤ f (n + 1) ∧ f (n + 1) ≤ f n + 1)
    (K : ℤ) (N : ℕ) (hStart : f 0 < K) (hEnd : K ≤ f N) :
    ∃ s : ℕ, 0 < s ∧ s ≤ N ∧ f s = K ∧ ∀ t : ℕ, t < s → f t < K := by
  have hex : ∃ s : ℕ, K ≤ f s := ⟨N, hEnd⟩
  let s := Nat.find hex
  have hs : K ≤ f s := Nat.find_spec hex
  have hsN : s ≤ N := Nat.find_min' hex hEnd
  have hsPos : 0 < s := by
    by_contra hNot
    have hsZero : s = 0 := by omega
    rw [hsZero] at hs
    omega
  have hBefore (t : ℕ) (ht : t < s) : f t < K :=
    lt_of_not_ge (Nat.find_min hex ht)
  have hPrevious := hBefore (s - 1) (by omega)
  have hStep := hUnit (s - 1)
  have hSucc : s - 1 + 1 = s := by omega
  rw [hSucc] at hStep
  exact ⟨s, hsPos, hsN, by omega, hBefore⟩

private theorem crossing_height_backwards
    (p q : ℕ → Lattice)
    (hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1))
    (hq : ∀ n, q (n + 1) = q n + (1, 0) ∨ q (n + 1) = q n + (0, 1))
    (a b d : ℕ)
    (hLevel : (p a).1 + (p a).2 = (q b).1 + (q b).2)
    (hAvoid : ∀ n, n ≤ d → p (a + n) ≠ q (b + n))
    (hEnd : (p (a + d)).2 < (q (b + d)).2) : (p a).2 < (q b).2 := by
  have hpShift (n : ℕ) :
      p (a + (n + 1)) = p (a + n) + (1, 0) ∨
        p (a + (n + 1)) = p (a + n) + (0, 1) := by
    simpa only [Nat.add_assoc] using hp (a + n)
  have hqShift (n : ℕ) :
      q (b + (n + 1)) = q (b + n) + (1, 0) ∨
        q (b + (n + 1)) = q (b + n) + (0, 1) := by
    simpa only [Nat.add_assoc] using hq (b + n)
  have hInitial :
      (p (a + 0)).1 + (p (a + 0)).2 = (q (b + 0)).1 + (q (b + 0)).2 := by
    simpa only [Nat.add_zero] using hLevel
  have hOrder := (up_right_paths_strict_height_order_iff_of_disjoint
    (fun n => p (a + n)) (fun n => q (b + n)) d
    hpShift hqShift hInitial hAvoid).mpr hEnd
  simpa only [Nat.add_zero] using hOrder

/-- A prohibited outside ray meeting the preserved middle tail has a last west
entry and a first north exit strictly between the old outer north endpoints.
Every intermediate vertex lies in the literal guarded corridor. This derives
the finite geometry in GRS, arXiv:1510.00860v1, Appendix A.4, lines 1616–1632. -/
theorem exists_rightmost_corridor_entry_exit
    (C D : Lattice → Lattice → ℝ)
    (m ell : ℕ) (hm : 0 < m) (hmell : m < ell)
    (M1 M2 a1 a2 : ℤ) (hTop : (ell : ℤ) < M2)
    (nL nM nU : ℕ)
    (hNorthL : rightmostCocyclePath C 0 nL = (M1, M2))
    (hNorthM : rightmostCocyclePath C (0, (m : ℤ)) nM = (a2, M2))
    (hNorthU : rightmostCocyclePath C (0, (ell : ℤ)) nU = (a1, M2))
    (hDisjointLM : ∀ r s : ℕ,
      rightmostCocyclePath C 0 r ≠
        rightmostCocyclePath C (0, (m : ℤ)) s)
    (hDisjointMU : ∀ r s : ℕ,
      rightmostCocyclePath C (0, (m : ℤ)) r ≠
        rightmostCocyclePath C (0, (ell : ℤ)) s)
    (hMiddleTail : ∀ r : ℕ,
      rightmostCocyclePath D (a2, M2) r =
        rightmostCocyclePath C (a2, M2) r)
    (hLowerBarrier : ∀ r s : ℕ,
      (rightmostCocyclePath D (rightmostCocyclePath C 0 r) s).2 ≤
        (rightmostCocyclePath C (rightmostCocyclePath C 0 r) s).2)
    (hUpperBarrier : ∀ r s : ℕ,
      (rightmostCocyclePath C
        (rightmostCocyclePath C (0, (ell : ℤ)) r) s).2 ≤
      (rightmostCocyclePath D
        (rightmostCocyclePath C (0, (ell : ℤ)) r) s).2)
    (R : Finset Lattice)
    (hR : ∀ z : Lattice, z ∈ R ↔
      0 < z.1 ∧ z.2 < M2 ∧
      ∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
        (rightmostCocyclePath C 0 n).2 < z.2 ∧
        (n < ell ∨ z.2 <
          (rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2))
    (v : Lattice)
    (hOutside : v ∉ Set.Icc (0 : Lattice) (M1, M2))
    (hWestOrSouth : v.1 ≤ 0 ∨ v.2 ≤ 0)
    (N k : ℕ)
    (hMeet : rightmostCocyclePath D v N =
      rightmostCocyclePath D (a2, M2) k) :
    ∃ entry exit : ℕ, ∃ j i : ℤ,
      0 < entry ∧ entry < exit ∧ exit ≤ N ∧
      0 < j ∧ j < (ell : ℤ) ∧
      a1 < i ∧ i < M1 ∧ 0 < i ∧
      rightmostCocyclePath D v entry = (0, j) ∧
      rightmostCocyclePath D v (entry + 1) = (1, j) ∧
      rightmostCocyclePath D v exit = (i, M2) ∧
      (∀ t : ℕ, entry < t →
        0 < (rightmostCocyclePath D v t).1) ∧
      (∀ t : ℕ, t < exit →
        (rightmostCocyclePath D v t).2 < M2) ∧
      (∀ t : ℕ, entry < t → t < exit →
        rightmostCocyclePath D v t ∈ R) := by
  let Q := rightmostCocyclePath D v
  let L := rightmostCocyclePath C 0
  let U := rightmostCocyclePath C (0, (ell : ℤ))
  have hQZero : Q 0 = v := by rfl
  have hQStep (n : ℕ) : Q (n + 1) = Q n + (1, 0) ∨ Q (n + 1) = Q n + (0, 1) :=
    crossing_step D v n
  have hLStep (n : ℕ) : L (n + 1) = L n + (1, 0) ∨ L (n + 1) = L n + (0, 1) :=
    crossing_step C 0 n
  have hUStep (n : ℕ) : U (n + 1) = U n + (1, 0) ∨ U (n + 1) = U n + (0, 1) :=
    crossing_step C (0, (ell : ℤ)) n
  have hQMono : Monotone (fun n => (Q n).1) ∧ Monotone (fun n => (Q n).2) :=
    crossing_monotone D v
  have hLMono : Monotone (fun n => (L n).1) ∧ Monotone (fun n => (L n).2) :=
    crossing_monotone C 0
  have hUMono : Monotone (fun n => (U n).1) ∧ Monotone (fun n => (U n).2) :=
    crossing_monotone C (0, (ell : ℤ))
  have hLHit : L nL = (M1, M2) := hNorthL
  have hUHit : U nU = (a1, M2) := hNorthU
  -- The actual producers give old order and avoidance of both outer traces.
  obtain ⟨hLM, hMU, ha1, ha1a2, ha2M1⟩ :=
    rightmostCocyclePath_height_order_and_north_hit_order
      C m ell hm hmell M1 M2 a1 a2 hTop nL nM nU
      hNorthL hNorthM hNorthU hDisjointLM hDisjointMU
  have hAvoid : ∀ t, t ≤ N → ∀ r, Q t ≠ L r ∧ Q t ≠ U r :=
    rightmostCocyclePath_prefix_avoids_outer_of_meets_middle
      C D m ell hm hmell M1 M2 a1 a2 hTop nL nM nU
      hNorthL hNorthM hNorthU hDisjointLM hDisjointMU
      hMiddleTail hLowerBarrier hUpperBarrier v N k hMeet
  have hOldMiddle : Q N = rightmostCocyclePath C (0, (m : ℤ)) (nM + k) := by
    calc
      Q N = rightmostCocyclePath D (a2, M2) k := hMeet
      _ = rightmostCocyclePath C (a2, M2) k := hMiddleTail k
      _ = rightmostCocyclePath C (rightmostCocyclePath C (0, (m : ℤ)) nM) k := by
        rw [hNorthM]
      _ = rightmostCocyclePath C (0, (m : ℤ)) (nM + k) :=
        crossing_restart C (0, (m : ℤ)) nM k
  have hQLevel (t : ℕ) : (Q t).1 + (Q t).2 = v.1 + v.2 + (t : ℤ) :=
    crossing_level D v t
  have hLLevel (n : ℕ) : (L n).1 + (L n).2 = (n : ℤ) := by
    simpa only [L, Prod.fst_zero, Prod.snd_zero, zero_add] using crossing_level C 0 n
  have hULevel (n : ℕ) : (U n).1 + (U n).2 = (ell : ℤ) + (n : ℤ) := by
    simpa only [U, zero_add] using crossing_level C (0, (ell : ℤ)) n
  have hEndLevel : (Q N).1 + (Q N).2 = (m : ℤ) + ((nM + k : ℕ) : ℤ) := by
    rw [hOldMiddle]
    simpa only [zero_add] using crossing_level C (0, (m : ℤ)) (nM + k)
  have hEndX : 0 < (Q N).1 := by
    have hMono := (crossing_monotone D (a2, M2)).1 (Nat.zero_le k)
    have hStart : a2 ≤ (Q N).1 := by
      rw [show Q N = rightmostCocyclePath D (a2, M2) k from hMeet]
      simpa only [rightmostCocyclePath, Function.iterate_zero_apply] using hMono
    omega
  have hEndY : M2 ≤ (Q N).2 := by
    have hMono := (crossing_monotone D (a2, M2)).2 (Nat.zero_le k)
    rw [show Q N = rightmostCocyclePath D (a2, M2) k from hMeet]
    simpa only [rightmostCocyclePath, Function.iterate_zero_apply] using hMono
  have hXUnit (t : ℕ) : (Q t).1 ≤ (Q (t + 1)).1 ∧ (Q (t + 1)).1 ≤ (Q t).1 + 1 := by
    rcases hQStep t with h | h <;> simp only [h, Prod.fst_add] <;> omega
  have hYUnit (t : ℕ) : (Q t).2 ≤ (Q (t + 1)).2 ∧ (Q (t + 1)).2 ≤ (Q t).2 + 1 := by
    rcases hQStep t with h | h <;> simp only [h, Prod.snd_add] <;> omega
  -- Strict order at the meeting propagates backwards at every available absolute level.
  have hBounds (t n : ℕ) (ht : t ≤ N) (hn : (n : ℤ) = (Q t).1 + (Q t).2) :
      (L n).2 < (Q t).2 ∧ (ell ≤ n → (Q t).2 < (U (n - ell)).2) := by
    have hIndex : n + (N - t) = m + (nM + k) := by
      have hAtT := hQLevel t
      have hAtN := hQLevel N
      omega
    have hMiddleIndex : n + (N - t) - m = nM + k := by omega
    have hCut : t + (N - t) = N := Nat.add_sub_of_le ht
    constructor
    · have hInitial : (L n).1 + (L n).2 = (Q t).1 + (Q t).2 :=
        (hLLevel n).trans hn
      have hNoMeet (s : ℕ) (hs : s ≤ N - t) : L (n + s) ≠ Q (t + s) :=
        ((hAvoid (t + s) (by omega) (n + s)).1).symm
      have hTerminal : (L (n + (N - t))).2 < (Q (t + (N - t))).2 := by
        have h := hLM (n + (N - t)) (by omega)
        rw [hMiddleIndex] at h
        rw [hCut, hOldMiddle]
        exact h
      exact crossing_height_backwards L Q hLStep hQStep n t (N - t)
        hInitial hNoMeet hTerminal
    · intro helln
      have hInitial : (Q t).1 + (Q t).2 = (U (n - ell)).1 + (U (n - ell)).2 := by
        have h := hULevel (n - ell)
        omega
      have hNoMeet (s : ℕ) (hs : s ≤ N - t) : Q (t + s) ≠ U (n - ell + s) :=
        (hAvoid (t + s) (by omega) (n - ell + s)).2
      have hUpperIndex : n + (N - t) - ell = n - ell + (N - t) := by omega
      have hTerminal : (Q (t + (N - t))).2 < (U (n - ell + (N - t))).2 := by
        have h := hMU (n + (N - t)) (by omega)
        rw [hMiddleIndex, hUpperIndex] at h
        rw [hCut, hOldMiddle]
        exact h
      exact crossing_height_backwards Q U hQStep hUStep t (n - ell) (N - t)
        hInitial hNoMeet hTerminal
  have hLNonneg (n : ℕ) : 0 ≤ (L n).2 := by
    have h := hLMono.2 (Nat.zero_le n)
    simpa only [L, rightmostCocyclePath, Function.iterate_zero_apply, Prod.snd_zero] using h
  -- A signed start is advanced to an actual zero-height site before using a natural old index.
  have hNoBottom (t : ℕ) (ht : t ≤ N) (hx : 0 < (Q t).1) (hy : (Q t).2 ≤ 0) : False := by
    have hZero : ∃ u : ℕ, u ≤ N ∧ (Q u).2 = 0 ∧ 0 < (Q u).1 := by
      by_cases hz : (Q t).2 = 0
      · exact ⟨t, ht, hz, hx⟩
      · have hNegative : (Q t).2 < 0 := by omega
        have hShiftEnd : 0 ≤ (Q (t + (N - t))).2 := by
          rw [Nat.add_sub_of_le ht]
          omega
        have hShiftUnit (s : ℕ) :
            (Q (t + s)).2 ≤ (Q (t + (s + 1))).2 ∧
              (Q (t + (s + 1))).2 ≤ (Q (t + s)).2 + 1 := by
          simpa only [Nat.add_assoc] using hYUnit (t + s)
        obtain ⟨u, _, hu, huZero, _⟩ := crossing_first_hit
          (fun s => (Q (t + s)).2) hShiftUnit 0 (N - t) hNegative hShiftEnd
        refine ⟨t + u, by omega, huZero, ?_⟩
        have hMono : (Q t).1 ≤ (Q (t + u)).1 :=
          hQMono.1 (show t ≤ t + u by omega)
        omega
    obtain ⟨u, huN, huZero, huX⟩ := hZero
    have hCast : (((Q u).1.toNat : ℕ) : ℤ) = (Q u).1 :=
      Int.toNat_of_nonneg (le_of_lt huX)
    have hn : (((Q u).1.toNat : ℕ) : ℤ) = (Q u).1 + (Q u).2 := by omega
    have hBelow := (hBounds u (Q u).1.toNat huN hn).1
    have hNonneg := hLNonneg (Q u).1.toNat
    omega
  have hStartX : (Q 0).1 ≤ 0 := by
    rcases hWestOrSouth with hx | hy
    · rw [hQZero]
      exact hx
    · by_contra hNot
      have hx : 0 < (Q 0).1 := by omega
      have hy' : (Q 0).2 ≤ 0 := by rw [hQZero]; exact hy
      exact hNoBottom 0 (Nat.zero_le N) hx hy'
  -- First positive x gives the preceding last west contact and its east departure.
  obtain ⟨s, hsPos, hsN, hsX, hBeforeX⟩ := crossing_first_hit
    (fun t => (Q t).1) hXUnit 1 N (by omega) (by omega)
  let entry := s - 1
  have hEntrySucc : entry + 1 = s := by dsimp [entry]; omega
  have hEntryX : (Q entry).1 = 0 := by
    have hBefore := hBeforeX entry (by omega)
    have hUnit := hXUnit entry
    rw [hEntrySucc] at hUnit
    omega
  let j := (Q entry).2
  have hEntry : Q entry = (0, j) := Prod.ext hEntryX rfl
  have hNext : Q (entry + 1) = (1, j) := by
    rcases hQStep entry with h | h
    · rw [h, hEntry]
      apply Prod.ext
      · change (0 : ℤ) + 1 = 1
        omega
      · change j + 0 = j
        omega
    · have hX := congrArg Prod.fst h
      change (Q (entry + 1)).1 = (Q entry).1 + 0 at hX
      rw [hEntrySucc] at hX
      omega
  have hAfterX (t : ℕ) (ht : entry < t) : 0 < (Q t).1 := by
    have hMono : (Q s).1 ≤ (Q t).1 := hQMono.1 (show s ≤ t by omega)
    omega
  have hj : 0 < j := by
    by_contra hNot
    have hx := hAfterX (entry + 1) (by omega)
    have hy : (Q (entry + 1)).2 ≤ 0 := by rw [hNext]; change j ≤ 0; omega
    exact hNoBottom (entry + 1) (by omega) hx hy
  have hjell : j < (ell : ℤ) := by
    by_contra hNot
    have hCast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
    have hn : ((j.toNat : ℕ) : ℤ) = (Q entry).1 + (Q entry).2 := by
      rw [hEntry]
      change ((j.toNat : ℕ) : ℤ) = 0 + j
      omega
    have hUpper := (hBounds entry j.toNat (by omega) hn).2 (by omega)
    have hUpperLevel := hULevel (j.toNat - ell)
    have hNonneg : 0 ≤ (U (j.toNat - ell)).1 := by
      have hMono := hUMono.1 (Nat.zero_le (j.toNat - ell))
      simpa only [U, rightmostCocyclePath, Function.iterate_zero_apply] using hMono
    change j < (U (j.toNat - ell)).2 at hUpper
    omega
  have hEntryPos : 0 < entry := by
    by_contra hNot
    have hZero : entry = 0 := by omega
    have hv : v = (0, j) := by
      calc
        v = Q 0 := hQZero.symm
        _ = Q entry := by rw [hZero]
        _ = (0, j) := hEntry
    apply hOutside
    rw [hv]
    simp only [Set.mem_Icc, Prod.le_def, Prod.fst_zero, Prod.snd_zero]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  -- The first north hit is global: every earlier height is below M2.
  have hStartY : (Q 0).2 < M2 := by
    have hMono := hQMono.2 (Nat.zero_le entry)
    change (Q 0).2 ≤ j at hMono
    omega
  obtain ⟨exit, _, hExitN, hExitY, hBeforeY⟩ := crossing_first_hit
    (fun t => (Q t).2) hYUnit M2 N hStartY hEndY
  have hEntryExit : entry < exit := by
    by_contra hNot
    have hMono : (Q exit).2 ≤ (Q entry).2 :=
      hQMono.2 (show exit ≤ entry by omega)
    rw [hExitY] at hMono
    change M2 ≤ j at hMono
    omega
  let i := (Q exit).1
  have hExit : Q exit = (i, M2) := Prod.ext rfl hExitY
  have hi : 0 < i := hAfterX exit hEntryExit
  let nE := (i + M2).toNat
  have hExitCast : (nE : ℤ) = i + M2 := Int.toNat_of_nonneg (by omega)
  have hExitLevel : (nE : ℤ) = (Q exit).1 + (Q exit).2 := by
    rw [hExit]
    exact hExitCast
  obtain ⟨hBelowExit, hAboveExit⟩ := hBounds exit nE hExitN hExitLevel
  have hAbove : M2 < (U (nE - ell)).2 := by
    have h := hAboveExit (by omega)
    rw [hExitY] at h
    exact h
  have hBelow : (L nE).2 < M2 := by rw [← hExitY]; exact hBelowExit
  have hLowerHitLevel : M1 + M2 = (nL : ℤ) := by
    have h := hLLevel nL
    rw [hLHit] at h
    exact h
  have hUpperHitLevel : a1 + M2 = (ell : ℤ) + (nU : ℤ) := by
    have h := hULevel nU
    rw [hUHit] at h
    exact h
  have hiM1 : i < M1 := by
    by_contra hNot
    have hMono : (L nL).2 ≤ (L nE).2 := hLMono.2 (show nL ≤ nE by omega)
    rw [hLHit] at hMono
    change M2 ≤ (L nE).2 at hMono
    omega
  have ha1i : a1 < i := by
    by_contra hNot
    have hMono : (U (nE - ell)).2 ≤ (U nU).2 :=
      hUMono.2 (show nE - ell ≤ nU by omega)
    rw [hUHit] at hMono
    change (U (nE - ell)).2 ≤ M2 at hMono
    omega
  -- Insert every genuine intermediate point into the literal guarded corridor.
  have hInside (t : ℕ) (hEt : entry < t) (htX : t < exit) : Q t ∈ R := by
    apply (hR (Q t)).mpr
    refine ⟨hAfterX t hEt, hBeforeY t htX, ?_⟩
    let n := j.toNat + (t - entry)
    have hJCast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (le_of_lt hj)
    have hn : (n : ℤ) = (Q t).1 + (Q t).2 := by
      have hAtT := hQLevel t
      have hAtEntry := hQLevel entry
      rw [hEntry] at hAtEntry
      dsimp only [n]
      omega
    have hBound := hBounds t n (by omega) hn
    refine ⟨n, hn, hBound.1, ?_⟩
    by_cases hBeforeUpper : n < ell
    · exact Or.inl hBeforeUpper
    · exact Or.inr (hBound.2 (by omega))
  exact ⟨entry, exit, j, i, hEntryPos, hEntryExit, hExitN, hj, hjell,
    ha1i, hiM1, hi, hEntry, hNext, hExit, hAfterX, hBeforeY, hInside⟩

end LPP.Busemann
