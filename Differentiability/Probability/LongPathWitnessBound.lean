/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.StageWitnessPathEvents
public import LPP_Foundations.Probability.EnvironmentLaw
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import Differentiability.Probability.PathEventBK
import Differentiability.Model.WitnessSubselection
import Differentiability.Model.StageItineraryCount
import Differentiability.Model.WitnessAllocations
import Differentiability.Analysis.LongPathDecaySummability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Long paths contain few disjoint witnesses

This is Proposition 6.7 of the differentiability preprint, at a fixed scale. Under the
scale hypothesis (6.4), which says `P(A_b) ≤ 2 q0` for every block `b`, and under (6.1),
almost surely there is `N0` such that for every path from the origin, every `N ≥ N0`,
every cut sequence with the properties of the first cut and `N` full stages, and every
family of disjoint stage witnesses with the properties of statement (d), the family has
fewer than `⌊N/32⌋` members.

Proof as in Section 6.4 of the preprint: for each itinerary `c` and allocation `m` the
disjoint-occurrence event `D_{c,m}` has probability at most `(2q0)^{t_N}` by the
path-event extension of van den Berg and Kesten (1985), Theorem 3.3. A long path
with a large family lies in some `D_{c,m}` ((6.13)); the union bound over at most
`15^N` itineraries and `4^N` allocations is summable; Borel-Cantelli for arbitrary
sets finishes the proof.
-/

public section

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- Proposition 6.7 of the differentiability preprint at a fixed scale, in the family form. -/
theorem long_path_disjoint_witnesses_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a s : ℝ) (m : ℕ) (η G0 dl dr K q0 : ℝ) (hq0 : 0 < q0)
    (hsmall : 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2)
    (hrare : ∀ b : Lattice, (environmentLaw μ).real {ω : Environment |
      let v : Lattice → Lattice := fun b =>
        let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
        (j,b.1*m-j)
      let block : Lattice → Lattice → Prop := fun b z =>
        (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
          |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
      let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
        (∀ i, block b (q.vertex i)) ∧
          min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
            (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
      let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
        fun b u e q =>
          u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
            (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
              ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
            G0*(m : ℝ)-K*s < pathWeight ω q
      ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        defectWitness b u e q ∨ crossingWitness b u e q} ≤ 2*q0) :
    ∀ᵐ ω ∂environmentLaw μ, ∃ N0 : ℕ, ∀ (d : ℕ × ℕ) (p : Path 0 d),
      let rho (t : Fin (d.1+d.2+1)) : ℝ := (1-a)*(p.vertex t).1-a*(p.vertex t).2
      let pi (t : Fin (d.1+d.2+1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
      let eta (t : Fin (d.1+d.2+1)) : ℤ := ⌊rho t/s⌋
      let v : Lattice → Lattice := fun b =>
        let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
        (j,b.1*m-j)
      let segment : ℕ → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun k0 _ e q =>
        k0+(e.1+e.2) ≤ d.1+d.2 ∧
          ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)), t.val = k0+i.val → q.vertex i = p.vertex t
      let block : Lattice → Lattice → Prop := fun b z =>
        (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
          |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
      let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
        (∀ i, block b (q.vertex i)) ∧
          min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
            (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
      let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
        fun b u e q =>
          u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
            (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
              ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
            G0*(m : ℝ)-K*s < pathWeight ω q
      ∀ N : ℕ, N0 ≤ N → ∀ cuts : Fin (N+2) → Fin (d.1+d.2+1),
      (cuts 0 = 0 ∧ cuts (Fin.last (N+1)) = Fin.last (d.1+d.2) ∧
      Monotone cuts ∧ N ≤ d.1+d.2 ∧
      (∀ i : Fin N,
        let k := cuts ⟨i.val, by omega⟩
        let l := cuts ⟨i.val+1, by omega⟩
        k < l ∧ (2*m ≤ l.val-k.val ∨ s ≤ |rho l-rho k|) ∧
        ∀ t, k < t → t < l → t.val-k.val < 2*m ∧ |rho t-rho k| < s) ∧
      (∀ t, cuts ⟨N, by omega⟩ < t →
        t.val-(cuts ⟨N, by omega⟩).val < 2*m ∧ |rho t-rho (cuts ⟨N, by omega⟩)| < s) ∧
      (∀ i : Fin (N+1),
        (cuts i.succ).val-(cuts i.castSucc).val ≤ 2*m ∧
        ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
          |rho t-rho (cuts i.castSucc)| ≤ s+1) ∧
      (∀ i : Fin N, |rho (cuts ⟨i.val+1, by omega⟩)-rho (cuts ⟨i.val, by omega⟩)| < s →
        (cuts ⟨i.val+1, by omega⟩).val-(cuts ⟨i.val, by omega⟩).val = 2*m) ∧
      (⋃ i : Fin (N+1), p.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ}) =
        (↑p.collectedSites : Set Lattice) ∧
      (∀ i j : Fin (N+1), i ≠ j → Disjoint
        (p.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ})
        (p.vertex '' {t | cuts j.castSucc ≤ t ∧ t < cuts j.succ})) ∧
      (∀ i : Fin (N+1), ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
        (pi (cuts i.castSucc) : ℝ)*(m : ℝ) ≤ (p.vertex t).1+(p.vertex t).2 ∧
        (p.vertex t).1+(p.vertex t).2 ≤ (pi (cuts i.castSucc) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
        |rho t-(eta (cuts i.castSucc) : ℝ)*s| ≤ 4*s) ∧
      (∀ i : Fin N,
        (pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 0 ∨
          pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 1 ∨
          pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 2) ∧
        |eta (cuts ⟨i.val+1, by omega⟩)-eta (cuts ⟨i.val, by omega⟩)| ≤ 2) ∧
      pi (cuts 0) = 0 ∧ eta (cuts 0) = 0) →
      ∀ (capacity : Fin (N+1) → ℕ)
        (time : (Σ i : Fin (N+1), Fin (capacity i)) → ℕ)
        (start : (Σ i : Fin (N+1), Fin (capacity i)) → Lattice)
        (displacement : (Σ i : Fin (N+1), Fin (capacity i)) → ℕ × ℕ)
        (paths : (j : Σ i : Fin (N+1), Fin (capacity i)) → Path (start j) (displacement j)),
      (∀ j, (cuts j.1.castSucc).val ≤ time j ∧
        time j+((displacement j).1+(displacement j).2) ≤ (cuts j.1.succ).val ∧
        segment (time j) (start j) (displacement j) (paths j) ∧
        (defectWitness (pi (cuts j.1.castSucc), eta (cuts j.1.castSucc))
            (start j) (displacement j) (paths j) ∨
          crossingWitness (pi (cuts j.1.castSucc), eta (cuts j.1.castSucc))
            (start j) (displacement j) (paths j))) →
      (∀ j j', j ≠ j' → Disjoint (paths j).collectedSites (paths j').collectedSites) →
      ∑ i, capacity i < N / 32 := by
  classical
  -- The block events as finite path events (`StageWitnessPathEvents`).
  choose I hI st dp pa thr hchar hset using fun b : Lattice =>
    exists_stage_witness_path_event a s m η G0 dl dr K b
  -- (6.4) for the listed events.
  have hA : ∀ b : Lattice,
      environmentLaw μ {ω | ∃ i : I b, thr b i < pathWeight ω (pa b i)} ≤
        ENNReal.ofReal (2*q0) := by
    intro b
    rw [hset b, ← ofReal_measureReal (measure_ne_top (environmentLaw μ) _)]
    exact ENNReal.ofReal_le_ofReal (hrare b)
  -- `D_{c,m}`: slots enumerated by `finSigmaFinEquiv`, slot `j` in stage `(e.symm j).1`.
  let D : (N : ℕ) → (Fin (N+1) → Lattice) → (Fin (N+1) → ℕ) → Set Environment :=
    fun _ c mm => {ω | ∃ i : ∀ j : Fin (∑ τ, mm τ), I (c (finSigmaFinEquiv.symm j).1),
      (∀ j, thr _ (i j) < pathWeight ω (pa _ (i j))) ∧
      Pairwise (fun j k => Disjoint (pa _ (i j)).collectedSites (pa _ (i k)).collectedSites)}
  -- (6.12), from the path-event extension of van den Berg and Kesten (1985), Theorem 3.3.
  have hD : ∀ (N : ℕ) (c : Fin (N+1) → Lattice) (mm : Fin (N+1) → ℕ),
      environmentLaw μ (D N c mm) ≤ ENNReal.ofReal (2*q0) ^ (∑ τ, mm τ) := by
    intro N c mm
    let σ : Fin (∑ τ, mm τ) → Lattice := fun j => c (finSigmaFinEquiv.symm j).1
    let V : Finset Lattice := Finset.univ.biUnion fun j : Fin (∑ τ, mm τ) =>
      (@Finset.univ _ (hI (σ j))).biUnion fun i => (pa (σ j) i).collectedSites
    have hV : ∀ j (i : I (σ j)), (pa (σ j) i).collectedSites ⊆ V := by
      intro j i z hz
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨i, @Finset.mem_univ _ (hI (σ j)) i, hz⟩⟩
    calc environmentLaw μ (D N c mm)
        ≤ ∏ j, environmentLaw μ {ω | ∃ i : I (σ j), thr (σ j) i < pathWeight ω (pa (σ j) i)} :=
          @path_event_bk μ _ (∑ τ, mm τ) (fun j => I (σ j)) (fun j => hI (σ j))
            (fun j => st (σ j)) (fun j => dp (σ j)) (fun j => pa (σ j)) (fun j => thr (σ j))
      _ ≤ ENNReal.ofReal (2*q0) ^ (Finset.univ : Finset (Fin (∑ τ, mm τ))).card :=
          Finset.prod_le_pow_card _ _ _ fun j _ => hA (σ j)
      _ = ENNReal.ofReal (2*q0) ^ (∑ τ, mm τ) := by rw [Finset.card_univ, Fintype.card_fin]
  -- Itineraries and allocations.
  choose C hC hCcard using exists_stage_itinerary_finset
  choose Al hAl hAlcard using witness_allocations_card_le_four_pow_div32
  let E : ℕ → Set Environment := fun N => ⋃ c ∈ C N, ⋃ mm ∈ Al N, D N c mm
  let f : ℕ → ℝ := fun N => 15 ^ N * 4 ^ N * (2 * q0) ^ ((N / 32 : ℕ) : ℝ)
  have hf0 : ∀ N, 0 ≤ f N := fun N =>
    mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
  -- Union bound.
  have hE : ∀ N, environmentLaw μ (E N) ≤ ENNReal.ofReal (f N) := by
    intro N
    calc environmentLaw μ (E N)
        ≤ ∑ c ∈ C N, environmentLaw μ (⋃ mm ∈ Al N, D N c mm) := measure_biUnion_finset_le _ _
      _ ≤ ∑ c ∈ C N, ∑ mm ∈ Al N, environmentLaw μ (D N c mm) :=
          Finset.sum_le_sum fun c _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ C N, ∑ _mm ∈ Al N, ENNReal.ofReal (2*q0) ^ (N / 32) := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun mm hmm => ?_
          rw [← (hAl N mm).mp hmm]
          exact hD N c mm
      _ = ((C N).card * (Al N).card : ℕ) * ENNReal.ofReal (2*q0) ^ (N / 32) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul,
            mul_assoc]
      _ ≤ ((15 ^ N * 4 ^ N : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2*q0) ^ (N / 32) := by
          refine mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?_) zero_le
          rw [hCcard N]
          exact Nat.mul_le_mul_left _ (hAlcard N)
      _ = ENNReal.ofReal (f N) := by
          have h1 : (15 : ℝ) ^ N * 4 ^ N = ((15 ^ N * 4 ^ N : ℕ) : ℝ) := by norm_num
          change _ = ENNReal.ofReal (15 ^ N * 4 ^ N * (2 * q0) ^ ((N / 32 : ℕ) : ℝ))
          rw [Real.rpow_natCast, ENNReal.ofReal_mul (p := (15 : ℝ) ^ N * 4 ^ N) (by positivity), h1,
            ENNReal.ofReal_natCast, ENNReal.ofReal_pow (p := 2 * q0) (by linarith)]
  -- Summability and Borel-Cantelli.
  have hsum : ∑' N, environmentLaw μ (E N) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' N, f N)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hf0 (long_path_decay_summable q0 hq0 hsmall)]
    exact ENNReal.tsum_le_tsum hE
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hω
  refine ⟨N0, fun d p => ?_⟩
  intro _ pi eta _ _ _ _ _ N hN cuts hcuts capacity _ start displacement paths hmem hdisj
  by_contra hlt0
  have hlt : N / 32 ≤ ∑ i, capacity i := not_lt.mp hlt0
  apply hN0 N hN
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsteps, hpi0, heta0⟩ := hcuts
  -- The itinerary of the path ((6.8) of the preprint).
  let c : Fin (N+1) → Lattice := fun τ => (pi (cuts τ.castSucc), eta (cuts τ.castSucc))
  have hc : c ∈ C N := (hC N c).mpr ⟨Prod.ext hpi0 heta0, fun i => hsteps i⟩
  -- An allocation below the stage capacities ((6.13) of the preprint).
  obtain ⟨mm, hmmle, hmmsum, -⟩ := exists_witness_subselection_enumeration capacity hlt
  have hmm : mm ∈ Al N := (hAl N mm).mpr hmmsum
  let J : Fin (∑ τ, mm τ) → Σ τ : Fin (N+1), Fin (capacity τ) := fun j =>
    ⟨(finSigmaFinEquiv.symm j).1, ⟨(finSigmaFinEquiv.symm j).2.val,
      lt_of_lt_of_le (finSigmaFinEquiv.symm j).2.isLt (hmmle _)⟩⟩
  have hJ : Function.Injective J := by
    intro j k hjk
    apply finSigmaFinEquiv.symm.injective
    have h1 : (J j).1 = (J k).1 := congrArg Sigma.fst hjk
    have h2 : (J j).2.val = (J k).2.val :=
      congrArg (fun x : Σ τ : Fin (N+1), Fin (capacity τ) => x.2.val) hjk
    exact Sigma.ext h1 ((Fin.heq_ext_iff (congrArg mm h1)).mpr h2)
  -- Each kept witness is a listed path of its stage event, above its threshold.
  have hpick : ∀ j : Fin (∑ τ, mm τ), ∃ i : I (c (finSigmaFinEquiv.symm j).1),
      (pa _ i).collectedSites = (paths (J j)).collectedSites ∧
        thr _ i < pathWeight ω (pa _ i) :=
    fun j => (hchar (c (finSigmaFinEquiv.symm j).1) ω).2 (start (J j)) (displacement (J j))
      (paths (J j)) (hmem (J j)).2.2.2
  choose i hi using hpick
  refine Set.mem_iUnion₂.mpr ⟨c, hc, Set.mem_iUnion₂.mpr ⟨mm, hmm, ?_⟩⟩
  refine ⟨i, fun j => (hi j).2, fun j k hjk => ?_⟩
  change Disjoint (pa _ (i j)).collectedSites (pa _ (i k)).collectedSites
  rw [(hi j).1, (hi k).1]
  exact hdisj _ _ (hJ.ne hjk)

end LPPDifferentiability
