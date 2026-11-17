/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.ConditionalPathKernel
public import Busemann.Frozen.Definitions.CoalescingRightmostPaths
import Busemann.Process.RightmostPathMeasurability

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace LPP.Busemann

/-- The conditional law of two original rightmost rays from the same process
sample has the two one-ray conditional laws as its marginals and is supported
on coalescing pairs. Strong Existence, lines 904–928. -/
theorem conditional_joint_rightmost_rays_coalesce
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun s : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y s) u)
        processEnvironment P
    let κ₂ : Lattice → Lattice →
        Kernel Environment ((ℕ → Lattice) × (ℕ → Lattice)) :=
      fun u v => condDistrib
        (fun s : ProcessSample =>
          (rightmostCocyclePath (fun x y => B x y s) u,
           rightmostCocyclePath (fun x y => B x y s) v))
        processEnvironment P
    ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      ((κ₂ u v) ω).map Prod.fst = (κ u) ω ∧
      ((κ₂ u v) ω).map Prod.snd = (κ v) ω ∧
      (κ₂ u v) ω
        {p | ∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)} = 1 := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun s : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let κ₂ : Lattice → Lattice →
      Kernel Environment ((ℕ → Lattice) × (ℕ → Lattice)) :=
    fun u v => condDistrib
      (fun s : ProcessSample =>
        (rightmostCocyclePath (fun x y => B x y s) u,
         rightmostCocyclePath (fun x y => B x y s) v))
      processEnvironment P
  change ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
    ((κ₂ u v) ω).map Prod.fst = (κ u) ω ∧
    ((κ₂ u v) ω).map Prod.snd = (κ v) ω ∧
    (κ₂ u v) ω
      {p | ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)} = 1

  have hProcessEnvironment : Measurable processEnvironment := by
    change Measurable (fun s : ProcessSample => s.1)
    exact measurable_fst

  -- The path-measurability theorem applies to each actual ray.
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun s : ProcessSample => ((x, y), s)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.1.comp hArg
  let ray (u : Lattice) (s : ProcessSample) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => B x y s) u
  have hRay (u : Lattice) : Measurable (ray u) := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_rightmostCocyclePath B hBMeas u n
  have hPairMeas (u v : Lattice) :
      Measurable (fun s : ProcessSample => (ray u s, ray v s)) :=
    (hRay u).prodMk (hRay v)

  -- Mapping the pair conditional law to either coordinate gives that ray's
  -- original conditional law.
  have hFirstMarginal (u v : Lattice) :
      (κ₂ u v).map Prod.fst =ᵐ[environmentLaw μ] κ u := by
    rw [← hMarginal]
    simpa only [κ, κ₂, ray, Function.comp_def] using
      (condDistrib_comp
        (X := processEnvironment)
        (Y := fun s : ProcessSample => (ray u s, ray v s))
        (μ := P) hProcessEnvironment.aemeasurable
        (hPairMeas u v).aemeasurable
        (f := Prod.fst) measurable_fst).symm
  have hSecondMarginal (u v : Lattice) :
      (κ₂ u v).map Prod.snd =ᵐ[environmentLaw μ] κ v := by
    rw [← hMarginal]
    simpa only [κ, κ₂, ray, Function.comp_def] using
      (condDistrib_comp
        (X := processEnvironment)
        (Y := fun s : ProcessSample => (ray u s, ray v s))
        (μ := P) hProcessEnvironment.aemeasurable
        (hPairMeas u v).aemeasurable
        (f := Prod.snd) measurable_snd).symm

  -- The aligned tail event is a countable union of countable intersections of
  -- measurable coordinate equalities on the pair-path space.
  let tailPiece (u v : Lattice) (m n : ℕ) :
      Set ((ℕ → Lattice) × (ℕ → Lattice)) :=
    {p | u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)}
  let tailEvent (u v : Lattice) :
      Set ((ℕ → Lattice) × (ℕ → Lattice)) :=
    {p | ∃ m n : ℕ,
      u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)}
  have hCoordinateEq (m n k : ℕ) :
      MeasurableSet
        {p : (ℕ → Lattice) × (ℕ → Lattice) |
          p.1 (m + k) = p.2 (n + k)} := by
    apply measurableSet_eq_fun
    · exact (measurable_pi_apply (m + k)).comp measurable_fst
    · exact (measurable_pi_apply (n + k)).comp measurable_snd
  have hTailPieceMeas (u v : Lattice) (m n : ℕ) :
      MeasurableSet (tailPiece u v m n) := by
    by_cases hAlign : u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ)
    · have hEq : tailPiece u v m n =
          {p : (ℕ → Lattice) × (ℕ → Lattice) |
            ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)} := by
        ext p
        simp [tailPiece, hAlign]
      rw [hEq]
      simpa only [Set.ofPred_forall] using
        (MeasurableSet.iInter fun k => hCoordinateEq m n k)
    · have hEq : tailPiece u v m n = ∅ := by
        ext p
        simp [tailPiece, hAlign]
      rw [hEq]
      exact MeasurableSet.empty
  have hTailUnion (u v : Lattice) :
      tailEvent u v = ⋃ m : ℕ, ⋃ n : ℕ, tailPiece u v m n := by
    ext p
    simp [tailEvent, tailPiece]
  have hTailEventMeas (u v : Lattice) :
      MeasurableSet (tailEvent u v) := by
    rw [hTailUnion]
    exact MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun n => hTailPieceMeas u v m n

  intro u v
  have hCoalPair : ∀ᵐ s ∂P, (ray u s, ray v s) ∈ tailEvent u v := by
    filter_upwards [hCoal] with s hs
    obtain ⟨m, n, hAlign, hEqual⟩ := hs u v
    refine ⟨m, n, hAlign, ?_⟩
    intro k
    exact hEqual k

  -- The joint conditional law reconstructs the actual environment-pair law.
  have hJoint :
      (environmentLaw μ) ⊗ₘ κ₂ u v =
        P.map (fun s : ProcessSample =>
          (processEnvironment s, (ray u s, ray v s))) := by
    rw [← hMarginal]
    simpa only [κ₂, ray] using
      compProd_map_condDistrib hProcessEnvironment.aemeasurable
        (hPairMeas u v).aemeasurable

  have hTailProductMeas :
      MeasurableSet
        {q : Environment × ((ℕ → Lattice) × (ℕ → Lattice)) |
          q.2 ∈ tailEvent u v} :=
    (hTailEventMeas u v).preimage measurable_snd
  have hTailActual : ∀ᵐ s ∂P,
      (processEnvironment s, (ray u s, ray v s)) ∈
        {q : Environment × ((ℕ → Lattice) × (ℕ → Lattice)) |
          q.2 ∈ tailEvent u v} := by
    filter_upwards [hCoalPair] with s hs
    exact hs
  have hTailProduct :
      ∀ᵐ q ∂(environmentLaw μ) ⊗ₘ κ₂ u v,
        q.2 ∈ tailEvent u v := by
    rw [hJoint]
    exact (ae_map_iff
      (hProcessEnvironment.prodMk (hPairMeas u v)).aemeasurable
      hTailProductMeas).2 hTailActual
  have hTailFibre : ∀ᵐ ω ∂environmentLaw μ,
      ∀ᵐ p ∂κ₂ u v ω, p ∈ tailEvent u v :=
    Measure.ae_ae_of_ae_compProd hTailProduct
  have hTailMass : ∀ᵐ ω ∂environmentLaw μ,
      (κ₂ u v) ω (tailEvent u v) = 1 := by
    filter_upwards [hTailFibre] with ω hω
    exact (mem_ae_iff_prob_eq_one (hTailEventMeas u v)).mp hω

  filter_upwards [hFirstMarginal u v, hSecondMarginal u v, hTailMass]
    with ω hFirst hSecond hTail
  exact ⟨by simpa only [Kernel.map_apply _ measurable_fst] using hFirst,
    by simpa only [Kernel.map_apply _ measurable_snd] using hSecond, hTail⟩

end LPP.Busemann
