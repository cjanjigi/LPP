/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ExcessAnimalBound
public import Differentiability.Model.Paths.StageIndexSets
import Mathlib.Tactic

/-!
# Excess along a stage itinerary

The total excess of a path is bounded by the block excesses along its stage itinerary,
and, almost surely, by `N η s / 32` once the scale satisfies a growth condition.
-/

public section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace LPPDifferentiability

private theorem sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset β) (box : β → Finset α) (f : α → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ A.biUnion box, f z ≤ ∑ b ∈ A, ∑ z ∈ box b, f z := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert b A hb ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hb]
    have hu := Finset.sum_union_inter (s₁ := box b) (s₂ := A.biUnion box) (f := f)
    have hi : 0 ≤ ∑ z ∈ box b ∩ A.biUnion box, f z :=
      Finset.sum_nonneg fun z _ => hf z
    linarith only [hu, hi, ih]

/-- The total excess of the collected sites of a path is at most the sum, over the stage indices
`A`, of the block excesses `Z`, when the stages cover the collected sites and every stage lies in
the block of its index. -/
theorem Path.collected_excess_le_itinerary_sum {d : ℕ × ℕ} (ω : Environment) (q : Path 0 d)
    (a s eta : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1)
    (N : ℕ) (cuts : Fin (N+2) → Fin (d.1+d.2+1)) :
    let rho (t : Fin (d.1+d.2+1)) : ℝ := (1-a)*(q.vertex t).1-a*(q.vertex t).2
    let pi (t : Fin (d.1+d.2+1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
    let idx (t : Fin (d.1+d.2+1)) : ℤ := ⌊rho t/s⌋
    let c (i : Fin (N+1)) : Lattice := (pi (cuts i.castSucc), idx (cuts i.castSucc))
    let A := Finset.univ.image c
    let v : Lattice → Lattice := fun b =>
      let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
      (j,b.1*m-j)
    let Z : Lattice → ℝ := fun b =>
      ∑ z ∈ Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩,
        max (ω z-eta*s/4) 0
    (⋃ i : Fin (N+1), q.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ}) =
        (↑q.collectedSites : Set Lattice) →
    (∀ i : Fin (N+1), ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
      (pi (cuts i.castSucc) : ℝ)*(m : ℝ) ≤ (q.vertex t).1+(q.vertex t).2 ∧
      (q.vertex t).1+(q.vertex t).2 ≤ (pi (cuts i.castSucc) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
      |rho t-(idx (cuts i.castSucc) : ℝ)*s| ≤ 4*s) →
    ∑ z ∈ q.collectedSites, max (ω z-eta*s/4) 0 ≤ ∑ b ∈ A, Z b := by
  classical
  intro rho pi idx c A v Z hunion hblock
  have hcover : q.collectedSites ⊆ A.biUnion
      (fun b => Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩) := by
    intro z hz
    have hz' : z ∈ (↑q.collectedSites : Set Lattice) := Finset.mem_coe.mpr hz
    rw [← hunion] at hz'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz'
    obtain ⟨t, ⟨hkt, htl⟩, rfl⟩ := hi
    obtain ⟨h1, h2, h3⟩ := hblock i t hkt htl.le
    refine Finset.mem_biUnion.mpr ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i), ?_⟩
    rw [Finset.mem_map]
    refine ⟨q.vertex t - v (c i), (hQ _).mpr ?_, ?_⟩
    · have h1' : (pi (cuts i.castSucc))*(m:ℤ) ≤ (q.vertex t).1+(q.vertex t).2 := by
        exact_mod_cast h1
      have h2' : (q.vertex t).1+(q.vertex t).2 ≤ (pi (cuts i.castSucc))*(m:ℤ)+3*(m:ℤ) := by
        exact_mod_cast h2
      have hv1 : (v (c i)).1 = ⌊(idx (cuts i.castSucc) : ℝ)*s+
          a*((pi (cuts i.castSucc)*(m:ℤ) : ℤ) : ℝ)⌋ := rfl
      have hv2 : (v (c i)).2 = pi (cuts i.castSucc)*(m:ℤ) - (v (c i)).1 := rfl
      have hfl := Int.floor_le ((idx (cuts i.castSucc) : ℝ)*s+
        a*((pi (cuts i.castSucc)*(m:ℤ) : ℤ) : ℝ))
      have hfl' := Int.lt_floor_add_one ((idx (cuts i.castSucc) : ℝ)*s+
        a*((pi (cuts i.castSucc)*(m:ℤ) : ℤ) : ℝ))
      rw [← hv1] at hfl hfl'
      have hrho : rho t = (1-a)*((q.vertex t).1:ℝ)-a*((q.vertex t).2:ℝ) := rfl
      refine ⟨?_, ?_, ?_⟩
      · change 0 ≤ ((q.vertex t).1 - (v (c i)).1)+((q.vertex t).2 - (v (c i)).2)
        omega
      · change ((q.vertex t).1 - (v (c i)).1)+((q.vertex t).2 - (v (c i)).2) ≤ 3*(m:ℤ)
        omega
      · change |(1-a)*(((q.vertex t).1 - (v (c i)).1 : ℤ) : ℝ)-
          a*(((q.vertex t).2 - (v (c i)).2 : ℤ) : ℝ)| ≤ 4*s+1
        rw [hv2]
        push_cast at hfl hfl' ⊢
        rw [hrho] at h3
        have h3' := abs_le.mp h3
        apply abs_le.mpr
        constructor <;> nlinarith only [hfl, hfl', h3']
    · exact add_sub_cancel _ _
  calc ∑ z ∈ q.collectedSites, max (ω z-eta*s/4) 0
      ≤ ∑ z ∈ A.biUnion
          (fun b => Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩),
          max (ω z-eta*s/4) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => le_max_right _ _)
    _ ≤ ∑ b ∈ A, Z b :=
        sum_biUnion_le_of_nonneg A _ (fun z => max (ω z-eta*s/4) 0)
          (fun _ => le_max_right _ _)

/-- The actual first cuts of a path, with every producer fact, give the itinerary image `A` and
the bound of the total excess by the block excesses along `A`. -/
theorem Path.exists_first_stage_index_image_excess_le {d : ℕ × ℕ} (ω : Environment)
    (q : Path 0 d) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 2 ≤ s) (eta : ℝ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) :
    let rho (t : Fin (d.1 + d.2 + 1)) : ℝ :=
      (1-a)*(q.vertex t).1-a*(q.vertex t).2
    let pi (t : Fin (d.1 + d.2 + 1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
    let idx (t : Fin (d.1 + d.2 + 1)) : ℤ := ⌊rho t/s⌋
    ∃ N : ℕ, ∃ cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1),
      (cuts 0 = 0 ∧ cuts (Fin.last (N + 1)) = Fin.last (d.1 + d.2) ∧
      Monotone cuts ∧ N ≤ d.1 + d.2 ∧
      (∀ i : Fin N,
        let k := cuts ⟨i.val, by omega⟩
        let l := cuts ⟨i.val + 1, by omega⟩
        k < l ∧ (2*m ≤ l.val-k.val ∨ s ≤ |rho l-rho k|) ∧
        ∀ t, k < t → t < l → t.val-k.val < 2*m ∧ |rho t-rho k| < s) ∧
      (∀ t, cuts ⟨N, by omega⟩ < t →
        t.val-(cuts ⟨N, by omega⟩).val < 2*m ∧
          |rho t-rho (cuts ⟨N, by omega⟩)| < s) ∧
      (∀ i : Fin (N + 1),
        (cuts i.succ).val-(cuts i.castSucc).val ≤ 2*m ∧
        ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
          |rho t-rho (cuts i.castSucc)| ≤ s+1) ∧
      (∀ i : Fin N,
        |rho (cuts ⟨i.val + 1, by omega⟩)-rho (cuts ⟨i.val, by omega⟩)| < s →
          (cuts ⟨i.val + 1, by omega⟩).val-(cuts ⟨i.val, by omega⟩).val = 2*m) ∧
      (⋃ i : Fin (N + 1),
        q.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ}) =
          (↑q.collectedSites : Set Lattice) ∧
      (∀ i j : Fin (N + 1), i ≠ j → Disjoint
        (q.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ})
        (q.vertex '' {t | cuts j.castSucc ≤ t ∧ t < cuts j.succ})) ∧
      (∀ i : Fin (N + 1), ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
        (pi (cuts i.castSucc) : ℝ)*(m : ℝ) ≤ (q.vertex t).1+(q.vertex t).2 ∧
        (q.vertex t).1+(q.vertex t).2 ≤ (pi (cuts i.castSucc) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
        |rho t-(idx (cuts i.castSucc) : ℝ)*s| ≤ 4*s) ∧
      (∀ i : Fin N,
        (pi (cuts ⟨i.val + 1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 0 ∨
          pi (cuts ⟨i.val + 1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 1 ∨
          pi (cuts ⟨i.val + 1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 2) ∧
        |idx (cuts ⟨i.val + 1, by omega⟩)-idx (cuts ⟨i.val, by omega⟩)| ≤ 2) ∧
      pi (cuts 0) = 0 ∧ idx (cuts 0) = 0) ∧
      (let c (i : Fin (N + 1)) : Lattice :=
        (pi (cuts i.castSucc), idx (cuts i.castSucc))
       let A := Finset.univ.image c
       A.card ≤ N + 1 ∧
       (0 : Lattice) ∈ A ∧
       ((SimpleGraph.fromRel (fun x y : Lattice =>
         |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected) ∧
      (let c (i : Fin (N + 1)) : Lattice :=
        (pi (cuts i.castSucc), idx (cuts i.castSucc))
       let A := Finset.univ.image c
       let v : Lattice → Lattice := fun b =>
         let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
         (j,b.1*m-j)
       let Z : Lattice → ℝ := fun b =>
         ∑ z ∈ Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩,
           max (ω z-eta*s/4) 0
       ∑ z ∈ q.collectedSites, max (ω z-eta*s/4) 0 ≤ ∑ b ∈ A, Z b) := by
  intro rho pi idx
  obtain ⟨N, cuts, hP, hA⟩ := q.exists_first_stage_index_image a ha ha1 m hm s hs
  refine ⟨N, cuts, hP, hA, ?_⟩
  rcases hP with ⟨_, _, _, _, _, _, _, _, hunion, _, hblock, _, _, _⟩
  exact Path.collected_excess_le_itinerary_sum ω q a s eta m Q hQ N cuts hunion hblock

/-- Almost surely, once the scale satisfies the condition `C0 s^(2-p/4) ≤ η s / 64`,
every path whose stages have the stage geometry and `N` full stages plus a remainder has total
excess at most `N η s / 32`, for all large `N`. -/
theorem exists_stage_excess_total_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p eta : ℝ}
    (hp : 4 < p) (heta : 0 < eta)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^p) ∂μ) < ∞) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (a s : ℝ), 3 ≤ s → ∀ m : ℕ,
      1 ≤ m → (m:ℝ) ≤ s^3 → C0*s^(2-p/4) ≤ eta*s/64 →
      ∀ᵐ ω ∂environmentLaw μ, ∀ᶠ N : ℕ in atTop,
        ∀ (d : ℕ × ℕ) (q : Path 0 d) (cuts : Fin (N+2) → Fin (d.1+d.2+1)),
        let rho (t : Fin (d.1+d.2+1)) : ℝ := (1-a)*(q.vertex t).1-a*(q.vertex t).2
        let pi (t : Fin (d.1+d.2+1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
        let idx (t : Fin (d.1+d.2+1)) : ℤ := ⌊rho t/s⌋
        (⋃ i : Fin (N+1), q.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ}) =
          (↑q.collectedSites : Set Lattice) →
        (∀ i : Fin (N+1), ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
          (pi (cuts i.castSucc) : ℝ)*(m : ℝ) ≤ (q.vertex t).1+(q.vertex t).2 ∧
          (q.vertex t).1+(q.vertex t).2 ≤ (pi (cuts i.castSucc) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
          |rho t-(idx (cuts i.castSucc) : ℝ)*s| ≤ 4*s) →
        (∀ i : Fin N,
          (pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 0 ∨
            pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 1 ∨
            pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 2) ∧
          |idx (cuts ⟨i.val+1, by omega⟩)-idx (cuts ⟨i.val, by omega⟩)| ≤ 2) →
        pi (cuts 0) = 0 → idx (cuts 0) = 0 →
        ∑ z ∈ q.collectedSites, max (ω z-eta*s/4) 0 ≤ (N:ℝ)*eta*s/32 := by
  classical
  obtain ⟨C0, hC0, hbound⟩ := exists_excess_animal_bound μ hp heta hmoment
  refine ⟨C0, hC0, ?_⟩
  intro a s hs m hm hms hscale
  obtain ⟨Q, hQ, _, _, hae⟩ := hbound a s hs m hm hms
  have hs0 : 0 < s := by linarith only [hs]
  have hε : 0 < eta*s/64 := by positivity
  filter_upwards [hae] with ω hω
  obtain ⟨_, hω2⟩ := hω
  filter_upwards [hω2 (eta*s/64) hε, eventually_ge_atTop 1] with N hN hN1
  intro d q cuts rho pi idx hunion hblock hstep hpi0 hidx0
  let c (i : Fin (N+1)) : Lattice := (pi (cuts i.castSucc), idx (cuts i.castSucc))
  have hc0 : c 0 = 0 := by
    have hcast : (0 : Fin (N+1)).castSucc = (0 : Fin (N+2)) := Fin.ext rfl
    refine Prod.ext ?_ ?_
    · change pi (cuts ((0 : Fin (N+1)).castSucc)) = 0
      rw [hcast]
      exact hpi0
    · change idx (cuts ((0 : Fin (N+1)).castSucc)) = 0
      rw [hcast]
      exact hidx0
  have hcstep : ∀ i : Fin N,
      |(c i.succ).1 - (c i.castSucc).1| ≤ 2 ∧
      |(c i.succ).2 - (c i.castSucc).2| ≤ 2 := by
    intro i
    obtain ⟨hpi, hidx⟩ : (pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc) = 0 ∨
          pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc) = 1 ∨
          pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc) = 2) ∧
        |idx (cuts i.succ.castSucc) - idx (cuts i.castSucc.castSucc)| ≤ 2 := hstep i
    constructor
    · change |pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc)| ≤ 2
      exact abs_le.mpr ⟨by omega, by omega⟩
    · exact hidx
  obtain ⟨hcard, hzero, hconn⟩ := stage_index_image_connected c hc0 hcstep
  have hsum := hN _ hzero hcard hconn
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hlt := (div_lt_iff₀ hNpos).mp hsum
  have hcore := Path.collected_excess_le_itinerary_sum ω q a s eta m Q hQ N cuts hunion hblock
  have h2 : C0*s^(2-p/4)+eta*s/64 ≤ eta*s/32 := by linarith only [hscale]
  refine hcore.trans (hlt.le.trans ?_)
  calc _ ≤ (eta*s/32)*(N:ℝ) := mul_le_mul_of_nonneg_right h2 hNpos.le
    _ = _ := by ring

end LPPDifferentiability
