/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Path
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Card
import Differentiability.Model.NeighborClusterCount
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Trapped components are small

Item (i) of Lemma B.5 of the differentiability preprint. On the event that every cluster of
very bad sites has at most `K1` sites and every finite reachable set has fewer than `m1 ^ 2`
elements, a chain of interfering trapped sites (or of sites of `V ∪ V̄←`) in the collar has at
most `K1 * (2 * m1 ^ 2 + 1) ^ 2` sites.

The argument follows the differentiability preprint. A trapped site `y` has a very bad site within
distance `m1 ^ 2`: the first very bad site on the ray `y + t e₁`. For a site of `V ∪ V̄←` the very
bad site is the first one on the ray `y - t e₁` (or `y` itself). A chain of interfering sites gives
a connected set of very bad sites, hence one cluster, hence at most `K1` very bad sites, and
each very bad site serves at most `(2 * m1 ^ 2 + 1) ^ 2` sites of the chain.
-/

public section

namespace LPPDifferentiability

/-- Private copy of the forward reachable set of the statement. -/
private abbrev reachSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

/-- Private copy of the backward reachable set of the statement. -/
private abbrev reachBackSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

/-- Private copy of the collar of the statement. -/
private abbrev collarSet (Q : Set Lattice) (c : ℕ) : Set Lattice :=
  {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}

/-- The relation "within `d0`, inside `S`", the one of the cluster extraction theorem. -/
private abbrev NearIn (S : Finset Lattice) (d0 : ℕ) (a b : Lattice) : Prop :=
  a ∈ S ∧ b ∈ S ∧ |a.1 - b.1| + |a.2 - b.2| ≤ (d0 : ℤ)

/-- The straight path of `k` steps `e₁` from `u`. -/
private def hpath (u : Lattice) (k : ℕ) : Path u (k, 0) where
  vertex i := u + ((i.val : ℤ), 0)
  start := by simp
  finish := by
    apply Prod.ext <;> simp
  step i := by
    left
    apply Prod.ext <;> simp [add_assoc]

private theorem l1_triangle (a b c : Lattice) :
    |a.1 - c.1| + |a.2 - c.2| ≤ (|a.1 - b.1| + |a.2 - b.2|) + (|b.1 - c.1| + |b.2 - c.2|) := by
  have h1 := abs_sub_le a.1 b.1 c.1
  have h2 := abs_sub_le a.2 b.2 c.2
  linarith

private theorem l1_comm (a b : Lattice) :
    |a.1 - b.1| + |a.2 - b.2| = |b.1 - a.1| + |b.2 - a.2| := by
  rw [abs_sub_comm a.1, abs_sub_comm a.2]

private theorem l1_ray_fwd (z : Lattice) (k : ℕ) :
    |z.1 - (z + ((k : ℤ), 0)).1| + |z.2 - (z + ((k : ℤ), 0)).2| = (k : ℤ) := by
  simp

private theorem l1_ray_bwd (z : Lattice) (k : ℕ) :
    |z.1 - (z - ((k : ℤ), 0)).1| + |z.2 - (z - ((k : ℤ), 0)).2| = (k : ℤ) := by
  simp

private theorem collar_mono {Q : Set Lattice} {c m : ℕ} {y b : Lattice} (hy : y ∈ collarSet Q c)
    (hb : |y.1 - b.1| + |y.2 - b.2| ≤ (m : ℤ)) : b ∈ collarSet Q (c + m) := by
  obtain ⟨q, hq, hqd⟩ := hy
  refine ⟨q, hq, ?_⟩
  have h1 := l1_triangle b y q
  have h2 := l1_comm b y
  push_cast
  linarith

/-- The first very bad site on the ray `z + t e₁`, `t ≤ M`, if the reachable set is small. -/
private theorem forward_bad (ω : Environment) (T : ℝ) (z : Lattice) (M : ℕ)
    (hfin : (reachSet ω T z).Finite) (hcard : (reachSet ω T z).ncard ≤ M) :
    ∃ k : ℕ, k ≤ M ∧ ω (z + ((k : ℤ), 0)) < -T := by
  by_contra hno
  push Not at hno
  have hsub : (((Finset.range (M + 1)).image (fun k : ℕ => z + ((k : ℤ), 0)) : Finset Lattice) :
      Set Lattice) ⊆ reachSet ω T z := by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    refine ⟨(k, 0), hpath z k, by simp, ?_⟩
    intro i hi
    have hik : i.val < k := by simpa using hi
    exact hno i.val (by omega)
  have hinj : Function.Injective (fun k : ℕ => z + ((k : ℤ), 0)) := by
    intro a b h
    have := congrArg Prod.fst h
    simpa using this
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, Finset.card_range] at this
  omega

/-- The first very bad site on the ray `z - t e₁`, `1 ≤ t ≤ M`, if the backward set is small. -/
private theorem backward_bad (ω : Environment) (T : ℝ) (z : Lattice) (M : ℕ)
    (hfin : (reachBackSet ω T z).Finite) (hcard : (reachBackSet ω T z).ncard ≤ M) :
    ∃ k : ℕ, k ≤ M ∧ ω (z - ((k : ℤ), 0)) < -T := by
  by_contra hno
  push Not at hno
  have hsub : (((Finset.range (M + 1)).image (fun k : ℕ => z - ((k : ℤ), 0)) : Finset Lattice) :
      Set Lattice) ⊆ reachBackSet ω T z := by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    refine ⟨(k, 0), hpath _ k, by simp, ?_⟩
    intro i hi
    have hik : i.val < k := by simpa using hi
    have hv : z - ((k : ℤ), 0) + ((i.val : ℤ), 0) = z - (((k - i.val : ℕ) : ℤ), 0) := by
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_sub]
        omega
      · simp
    show -T ≤ ω (z - ((k : ℤ), 0) + ((i.val : ℤ), 0))
    rw [hv]
    exact hno (k - i.val) (by omega)
  have hinj : Function.Injective (fun k : ℕ => z - ((k : ℤ), 0)) := by
    intro a b h
    have := congrArg Prod.fst h
    simpa using this
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, Finset.card_range] at this
  omega

private theorem forward_point (ω : Environment) (T : ℝ) (Q : Set Lattice) (c m : ℕ) (y : Lattice)
    (hy : y ∈ collarSet Q c) (hfin : (reachSet ω T y).Finite)
    (hcard : (reachSet ω T y).ncard ≤ m) :
    ∃ b, ω b < -T ∧ |y.1 - b.1| + |y.2 - b.2| ≤ (m : ℤ) ∧ b ∈ collarSet Q (c + m) := by
  obtain ⟨k, hk, hbad⟩ := forward_bad ω T y m hfin hcard
  have hd : |y.1 - (y + ((k : ℤ), 0)).1| + |y.2 - (y + ((k : ℤ), 0)).2| ≤ (m : ℤ) := by
    rw [l1_ray_fwd]
    exact_mod_cast hk
  exact ⟨_, hbad, hd, collar_mono hy hd⟩

private theorem backward_point (ω : Environment) (T : ℝ) (Q : Set Lattice) (c m : ℕ)
    (y : Lattice) (hy : y ∈ collarSet Q c)
    (hcase : ω y < -T ∨ (reachBackSet ω T y).Finite)
    (hcard : (reachBackSet ω T y).Finite → (reachBackSet ω T y).ncard ≤ m) :
    ∃ b, ω b < -T ∧ |y.1 - b.1| + |y.2 - b.2| ≤ (m : ℤ) ∧ b ∈ collarSet Q (c + m) := by
  rcases hcase with hbad | hfin
  · have hd : |y.1 - y.1| + |y.2 - y.2| ≤ (m : ℤ) := by simp
    exact ⟨y, hbad, hd, collar_mono hy hd⟩
  · obtain ⟨k, hk, hbad⟩ := backward_bad ω T y m hfin (hcard hfin)
    have hd : |y.1 - (y - ((k : ℤ), 0)).1| + |y.2 - (y - ((k : ℤ), 0)).2| ≤ (m : ℤ) := by
      rw [l1_ray_bwd]
      exact_mod_cast hk
    exact ⟨_, hbad, hd, collar_mono hy hd⟩

/-- A chain of sites, each with a very bad site of `Q'` within `m`, gives few very bad sites,
and each very bad site serves at most `(2 * m + 1) ^ 2` sites of the chain. -/
private theorem chain_card_le (ω : Environment) (T : ℝ) (Q' : Set Lattice)
    (K1 m D1 d0 N : ℕ) (hd0 : D1 + 2 * m ≤ d0) (hN : K1 * (2 * m + 1) ^ 2 ≤ N)
    (hcl : ¬ ∃ g : Fin (K1 + 1) → Lattice, Function.Injective g ∧
        (∀ i, g i ∈ Q' ∧ ω (g i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(g i).1 - (g j).1| + |(g i).2 - (g j).2| ≤ (d0 : ℤ))
    (f c : Fin (N + 1) → Lattice) (hf : Function.Injective f)
    (hchain : ∀ i : Fin (N + 1), 0 < i.val → ∃ j : Fin (N + 1), j.val < i.val ∧
        |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (D1 : ℤ))
    (hcQ : ∀ i, c i ∈ Q') (hcbad : ∀ i, ω (c i) < -T)
    (hcd : ∀ i, |(f i).1 - (c i).1| + |(f i).2 - (c i).2| ≤ (m : ℤ)) : False := by
  classical
  let S : Finset Lattice := Finset.univ.image c
  have mem_S : ∀ i, c i ∈ S := fun i => Finset.mem_image_of_mem c (Finset.mem_univ i)
  have hdist : ∀ i j : Fin (N + 1),
      |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (D1 : ℤ) →
      |(c j).1 - (c i).1| + |(c j).2 - (c i).2| ≤ (d0 : ℤ) := by
    intro i j h
    have a := l1_triangle (c j) (f j) (c i)
    have b := l1_triangle (f j) (f i) (c i)
    have c1 := l1_comm (c j) (f j)
    have c2 := l1_comm (f i) (f j)
    have e1 := hcd j
    have e2 := hcd i
    have e3 : (D1 : ℤ) + 2 * m ≤ d0 := by exact_mod_cast hd0
    linarith
  have hreach : ∀ i : Fin (N + 1), Relation.ReflTransGen (NearIn S d0) (c 0) (c i) := by
    have key : ∀ n : ℕ, ∀ i : Fin (N + 1), i.val = n →
        Relation.ReflTransGen (NearIn S d0) (c 0) (c i) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi
        by_cases h0 : 0 < i.val
        · obtain ⟨j, hj, hd⟩ := hchain i h0
          have := ih j.val (by omega) j rfl
          exact this.tail ⟨mem_S j, mem_S i, hdist i j hd⟩
        · have hi0 : i.val = 0 := by omega
          have : i = 0 := Fin.ext (by simpa using hi0)
          subst this
          exact Relation.ReflTransGen.refl
    exact fun i => key i.val i rfl
  have hsymm : ∀ x y, Relation.ReflTransGen (NearIn S d0) x y →
      Relation.ReflTransGen (NearIn S d0) y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨ha, hb, hd⟩ := hbc
      exact Relation.ReflTransGen.head ⟨hb, ha, by rw [l1_comm]; exact hd⟩ ih
  have hconn : ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (NearIn S d0) x y := by
    intro x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact (hsymm _ _ (hreach i)).trans (hreach j)
  have hSK : S.card ≤ K1 := by
    by_contra h
    push Not at h
    obtain ⟨g, hginj, hg, hgchain⟩ := exists_close_chain_of_connected_card_gt d0 K1 ω T S S
      (Finset.Subset.refl S)
      (fun z hz => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
        exact hcbad i)
      hconn h
    refine hcl ⟨g, hginj, fun i => ⟨?_, (hg i).2⟩, hgchain⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (hg i).1
    rw [← hj]
    exact hcQ j
  have hlt : S.card * (2 * m + 1) ^ 2 < (Finset.univ : Finset (Fin (N + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc S.card * (2 * m + 1) ^ 2 ≤ K1 * (2 * m + 1) ^ 2 := Nat.mul_le_mul_right _ hSK
      _ ≤ N := hN
      _ < N + 1 := Nat.lt_succ_self N
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := c) (s := Finset.univ) (t := S) (fun i _ => mem_S i) hlt
  let F : Finset (Fin (N + 1)) := Finset.univ.filter (fun x => c x = y)
  let box : Finset Lattice :=
    Finset.Icc (y.1 - (m : ℤ)) (y.1 + m) ×ˢ Finset.Icc (y.2 - (m : ℤ)) (y.2 + m)
  have hbox : box.card = (2 * m + 1) ^ 2 := by
    simp only [box, Finset.card_product, Int.card_Icc]
    have h1 : (y.1 + (m : ℤ) + 1 - (y.1 - m)).toNat = 2 * m + 1 := by omega
    have h2 : (y.2 + (m : ℤ) + 1 - (y.2 - m)).toNat = 2 * m + 1 := by omega
    rw [h1, h2]
    ring
  have hsub : F.image f ⊆ box := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hci : c i = y := (Finset.mem_filter.mp hi).2
    have e := hcd i
    rw [hci] at e
    have n1 := abs_nonneg ((f i).1 - y.1)
    have n2 := abs_nonneg ((f i).2 - y.2)
    have b1 := abs_le.mp (show |(f i).1 - y.1| ≤ (m : ℤ) by linarith)
    have b2 := abs_le.mp (show |(f i).2 - y.2| ≤ (m : ℤ) by linarith)
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    omega
  have hle : F.card ≤ box.card := by
    rw [← Finset.card_image_of_injective F hf]
    exact Finset.card_le_card hsub
  have hy' : (2 * m + 1) ^ 2 < F.card := hy
  omega

/-- **Trapped components are small** (item (i) of Lemma B.5): on the event `Egeo`, no chain of
`Ntr + 1` distinct trapped sites of the collar `𝒬⁺`, each after the first within `D1` of an
earlier one, exists, and likewise for the sites of `V ∪ V̄←`. -/
theorem stair_trapped_components_le (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
  let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let r0 : ℕ := K1 * (2 * L + 1) + Ntr
  let D1 : ℕ := ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8
  let d0 : ℕ := D1 + 2 * m1 ^ 2
  let c0 : ℕ := W0 + 2 * L + 1
  let collar : Set Lattice → ℕ → Set Lattice := fun Q c =>
    {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}
  let Egeo : Environment → ℝ → Set Lattice → Prop := fun ω T Q =>
    (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
    ∀ z ∈ collar Q c0,
      ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
      ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2)
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q →
    (¬ ∃ f : Fin (Ntr + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q c0 ∧ (reach ω T (f i)).Finite) ∧
        ∀ i : Fin (Ntr + 1), 0 < i.val → ∃ j : Fin (Ntr + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ D1) ∧
    (¬ ∃ f : Fin (Ntr + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q c0 ∧ (ω (f i) < -T ∨ (reachBack ω T (f i)).Finite)) ∧
        ∀ i : Fin (Ntr + 1), 0 < i.val → ∃ j : Fin (Ntr + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ D1) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo _ _ _ _ hE
  obtain ⟨hcl, hreach⟩ := hE
  have hd0 : D1 + 2 * m1 ^ 2 ≤ d0 := le_refl _
  constructor
  · rintro ⟨f, hinj, hmem, hchain⟩
    have hb : ∀ i, ∃ b, ω b < -T ∧ |(f i).1 - b.1| + |(f i).2 - b.2| ≤ ((m1 ^ 2 : ℕ) : ℤ) ∧
        b ∈ collarSet Q (c0 + m1 ^ 2) := fun i =>
      forward_point ω T Q c0 (m1 ^ 2) (f i) (hmem i).1 (hmem i).2
        (((hreach (f i) (hmem i).1).1 (hmem i).2).le)
    choose b hbbad hbd hbQ using hb
    exact chain_card_le ω T (collar Q (c0 + m1 ^ 2)) K1 (m1 ^ 2) D1 d0 Ntr hd0 le_rfl hcl f b
      hinj hchain hbQ hbbad hbd
  · rintro ⟨f, hinj, hmem, hchain⟩
    have hb : ∀ i, ∃ b, ω b < -T ∧ |(f i).1 - b.1| + |(f i).2 - b.2| ≤ ((m1 ^ 2 : ℕ) : ℤ) ∧
        b ∈ collarSet Q (c0 + m1 ^ 2) := fun i =>
      backward_point ω T Q c0 (m1 ^ 2) (f i) (hmem i).1 (hmem i).2
        (fun hfin => ((hreach (f i) (hmem i).1).2 hfin).le)
    choose b hbbad hbd hbQ using hb
    exact chain_card_le ω T (collar Q (c0 + m1 ^ 2)) K1 (m1 ^ 2) D1 d0 Ntr hd0 le_rfl hcl f b
      hinj hchain hbQ hbbad hbd

end LPPDifferentiability
