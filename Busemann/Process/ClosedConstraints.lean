/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import LPP_Foundations.Probability.EnvironmentLaw
public import Busemann.Frozen.Definitions.ProcessSample
public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
public import Busemann.Frozen.Definitions.FiniteBusemannArrayAtSharedHorizon
import Busemann.Finite.EdgeSquare
import Busemann.Finite.Recovery
import Busemann.Finite.Measurability
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! Closed square and recovery constraints for a finite-horizon weak limit. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

private theorem ae_closed_of_horizon_cutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℕ → ℝ × ℝ)
    (P : ProbabilityMeasure ProcessSample) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak :
      let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
        (show ProbabilityMeasure (Environment × Fin (n + 1)) from
          ⟨finiteBusemannSharedHorizonLaw μ n, by
            change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
            infer_instance⟩).map
          (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n h p))
      Tendsto (ν ∘ φ) atTop (𝓝 P))
    (C : Set ProcessSample) (hC : IsClosed C) (K : ℕ)
    (hgood : ∀ n (p : Environment × Fin (n + 1)), K ≤ p.2.val →
      (p.1, finiteBusemannArrayAtSharedHorizon n h p) ∈ C) :
    ∀ᵐ s ∂(P : Measure ProcessSample), s ∈ C := by
  classical
  let S (n : ℕ) (p : Environment × Fin (n + 1)) : ProcessSample :=
    (p.1, finiteBusemannArrayAtSharedHorizon n h p)
  let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
    (show ProbabilityMeasure (Environment × Fin (n + 1)) from
      ⟨finiteBusemannSharedHorizonLaw μ n, by
        change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
        infer_instance⟩).map (S n)
  have hS (n : ℕ) : Measurable (S n) :=
    measurable_fst.prodMk (measurable_finiteBusemannArrayAtSharedHorizon n h)
  have hbound (n : ℕ) :
      (ν n : Measure ProcessSample) Cᶜ ≤
        (K : ℝ≥0∞) * (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
    let U : Set (Fin (n + 1)) := {u | u.val < K}
    have hU : MeasurableSet U := MeasurableSet.of_discrete
    have hcard : Fintype.card U ≤ K := by
      let inject : U → Fin K := fun u => ⟨u.1.val, u.2⟩
      have hinj : Function.Injective inject := by
        intro a b hab
        apply Subtype.ext
        apply Fin.ext
        exact congrArg (fun t : Fin K => t.val) hab
      simpa using Fintype.card_le_of_injective inject hinj
    have hmeasure : uniformOriginLaw n U ≤
        (K : ℝ≥0∞) * (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      rw [uniformOriginLaw, PMF.toMeasure_uniformOfFintype_apply U hU]
      simp only [Fintype.card_fin, div_eq_mul_inv]
      have hc : (Fintype.card U : ℝ≥0∞) ≤ (K : ℝ≥0∞) := by exact_mod_cast hcard
      simpa only [mul_comm] using mul_le_mul_right hc (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
    calc
      (ν n : Measure ProcessSample) Cᶜ =
          (finiteBusemannSharedHorizonLaw μ n) (S n ⁻¹' Cᶜ) := by
        rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (hS n) hC.measurableSet.compl]
        rfl
      _ ≤ (finiteBusemannSharedHorizonLaw μ n) (Prod.snd ⁻¹' U) := by
        apply measure_mono
        intro p hp
        by_contra hnot
        have hk : K ≤ p.2.val := by
          simp only [Set.mem_preimage, U, Set.mem_ofPred_eq, not_lt] at hnot
          exact hnot
        exact hp (hgood n p hk)
      _ = uniformOriginLaw n U := by
        exact (uniformOriginProduct_snd (environmentLaw μ) n).measure_preimage hU.nullMeasurableSet
      _ ≤ _ := hmeasure
  have hboundzero : Tendsto
      (fun n : ℕ => (K : ℝ≥0∞) * (((φ n + 1 : ℕ) : ℝ≥0∞)⁻¹)) atTop (𝓝 0) := by
    have hinv := ENNReal.tendsto_inv_nat_nhds_zero.comp
      ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
    simpa using ENNReal.Tendsto.const_mul hinv (Or.inr (by simp : (K : ℝ≥0∞) ≠ ∞))
  have hbadzero : Tendsto (fun n => (ν (φ n) : Measure ProcessSample) Cᶜ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundzero
      (fun _ => bot_le) (fun n => hbound (φ n))
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hweak hC.isOpen_compl
  change (P : Measure ProcessSample) Cᶜ ≤
    liminf (fun n => (ν (φ n) : Measure ProcessSample) Cᶜ) atTop at hle
  have hzero : (P : Measure ProcessSample) Cᶜ = 0 := by
    apply le_antisymm
    · simpa only [hbadzero.liminf_eq] using hle
    · exact bot_le
  rw [ae_iff]
  exact hzero

/-- Every weak limit of the actual shared-horizon laws has all finite square
identities and outgoing weight recovery, as in JR arXiv:1810.03580v3
(4.14)-(4.15). -/
theorem ae_square_and_recovery_of_finiteBusemann_weak_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℕ → ℝ × ℝ)
    (P : ProbabilityMeasure ProcessSample) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak :
      let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
        (show ProbabilityMeasure (Environment × Fin (n + 1)) from
          ⟨finiteBusemannSharedHorizonLaw μ n, by
            change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
            infer_instance⟩).map
          (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n h p))
      Tendsto (ν ∘ φ) atTop (𝓝 P)) :
    ∀ᵐ s ∂(P : Measure ProcessSample),
      (∀ j x i k, s.2 j x i + s.2 j (x + finiteEdgeStep i) k =
        s.2 j x k + s.2 j (x + finiteEdgeStep k) i) ∧
      (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x) := by
  classical
  have hsquare (j : ℕ) (x : Lattice) (i k : Fin 2) :
      ∀ᵐ s ∂(P : Measure ProcessSample),
        s.2 j x i + s.2 j (x + finiteEdgeStep i) k =
          s.2 j x k + s.2 j (x + finiteEdgeStep k) i := by
    let C : Set ProcessSample := {s |
      s.2 j x i + s.2 j (x + finiteEdgeStep i) k =
        s.2 j x k + s.2 j (x + finiteEdgeStep k) i}
    have heval (a : Lattice) (b : Fin 2) :
        Continuous (fun s : ProcessSample => s.2 j a b) :=
      (continuous_apply b).comp ((continuous_apply a).comp
        ((continuous_apply j).comp continuous_snd))
    have hC : IsClosed C :=
      isClosed_eq ((heval x i).add (heval (x + finiteEdgeStep i) k))
        ((heval x k).add (heval (x + finiteEdgeStep k) i))
    let K : ℕ := (x.1 + x.2 + 1).toNat + 1
    have hK : x.1 + x.2 + 1 < (K : ℤ) := by
      dsimp [K]
      omega
    apply ae_closed_of_horizon_cutoff μ h P φ hφ hweak C hC K
    intro n p hp
    change finiteBusemannEdge p.1 (h j) x ((p.2.val + 1 : ℕ) : ℤ) i +
        finiteBusemannEdge p.1 (h j) (x + finiteEdgeStep i)
          ((p.2.val + 1 : ℕ) : ℤ) k =
      finiteBusemannEdge p.1 (h j) x ((p.2.val + 1 : ℕ) : ℤ) k +
        finiteBusemannEdge p.1 (h j) (x + finiteEdgeStep k)
          ((p.2.val + 1 : ℕ) : ℤ) i
    apply finiteBusemannEdge_square
    have hp' : (K : ℤ) ≤ (p.2.val : ℤ) := by exact_mod_cast hp
    omega
  have hrecovery (j : ℕ) (x : Lattice) :
      ∀ᵐ s ∂(P : Measure ProcessSample), min (s.2 j x 0) (s.2 j x 1) = s.1 x := by
    let C : Set ProcessSample := {s | min (s.2 j x 0) (s.2 j x 1) = s.1 x}
    have heval (b : Fin 2) : Continuous (fun s : ProcessSample => s.2 j x b) :=
      (continuous_apply b).comp ((continuous_apply x).comp
        ((continuous_apply j).comp continuous_snd))
    have hC : IsClosed C :=
      isClosed_eq ((heval 0).min (heval 1)) ((continuous_apply x).comp continuous_fst)
    let K : ℕ := (x.1 + x.2 + 1).toNat + 1
    have hK : x.1 + x.2 + 1 < (K : ℤ) := by
      dsimp [K]
      omega
    apply ae_closed_of_horizon_cutoff μ h P φ hφ hweak C hC K
    intro n p hp
    change min (finiteBusemannEdge p.1 (h j) x ((p.2.val + 1 : ℕ) : ℤ) 0)
      (finiteBusemannEdge p.1 (h j) x ((p.2.val + 1 : ℕ) : ℤ) 1) = p.1 x
    apply finiteBusemannEdge_min_of_active
    have hp' : (K : ℤ) ≤ (p.2.val : ℤ) := by exact_mod_cast hp
    omega
  filter_upwards [ae_all_iff.2 (fun j => ae_all_iff.2 (fun x =>
      ae_all_iff.2 (fun i => ae_all_iff.2 (fun k => hsquare j x i k)))),
    ae_all_iff.2 (fun j => ae_all_iff.2 (fun x => hrecovery j x))] with s hs hr
  exact ⟨hs, hr⟩

end LPP.Busemann
