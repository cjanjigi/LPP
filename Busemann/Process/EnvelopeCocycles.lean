/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.UnitEnvelopes
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Model.LatticeEdgeRegularity
public import LPP_Foundations.Model.LatticeEdgeTranslation
import Mathlib.Tactic

/-! Deterministic signed cocycles reconstructed from unit-envelope limits. -/

public section

open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

/-- The two real unit-envelope fields extend to signed additive cocycles on one
measurable invariant set. This is the deterministic reconstruction step in
JR1810.03580v3, proof of Theorem 4.8 after (4.18). -/
theorem envelope_signed_cocycle_reconstruction
    (g : Quadrant → ℝ) (D : ℕ → SupportTilt g)
    (happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) ∧
      StrictAnti (fun n => (D (b n)).1.1) ∧
      (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1)) :
    let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
      fun j x i s => s.2 j x i
    let Q : Set ProcessSample := {s | ∀ j k x,
      (D j).1.1 ≤ (D k).1.1 →
        X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
    let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
      fun h x i s => if i = 0 then
        ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
      else ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
    let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
      fun h x i s => if i = 0 then
        ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
      else ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
    let eMinus := fun h x i s => (Eminus h x i s).toReal
    let ePlus := fun h x i s => (Eplus h x i s).toReal
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
      fun h x y s =>
        S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
          S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
    let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
      fun h x y s =>
        S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
          S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
    let C0 : Set ProcessSample := {s |
      (∀ j x, X j x 0 s + X j (x + (1, 0)) 1 s =
        X j x 1 s + X j (x + (0, 1)) 0 s) ∧
      (∀ j x, min (X j x 0 s) (X j x 1 s) = s.1 x)}
    let C : Set ProcessSample := C0 ∩ Q
    MeasurableSet C ∧
    (∀ z s, processShift z s ∈ C ↔ s ∈ C) ∧
    Measurable (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
      Rminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
      Rplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ s h x, Rminus h x (x + (1, 0)) s = eMinus h x 0 s ∧
      Rminus h x (x + (0, 1)) s = eMinus h x 1 s) ∧
    (∀ s h x, Rplus h x (x + (1, 0)) s = ePlus h x 0 s ∧
      Rplus h x (x + (0, 1)) s = ePlus h x 1 s) ∧
    ∀ s ∈ C, ∀ h,
      (∀ x y z, Rminus h (x + z) (y + z) s =
        Rminus h x y (processShift z s)) ∧
      (∀ x y z, Rplus h (x + z) (y + z) s =
        Rplus h x y (processShift z s)) ∧
      (∀ x y z, Rminus h x y s + Rminus h y z s = Rminus h x z s) ∧
      (∀ x y z, Rplus h x y s + Rplus h y z s = Rplus h x z s) ∧
      recovers_environment s.1 (fun x y => Rminus h x y s) ∧
      recovers_environment s.1 (fun x y => Rplus h x y s) := by
  classical
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
    fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
    (D j).1.1 ≤ (D k).1.1 →
      X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
  let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
    fun h x i s => if i = 0 then
      ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
    else ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
  let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
    fun h x i s => if i = 0 then
      ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
    else ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
  let eMinus := fun h x i s => (Eminus h x i s).toReal
  let ePlus := fun h x i s => (Eplus h x i s).toReal
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
  let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
  let Rpath : (Lattice → Fin 2 → ℝ) → Lattice → Lattice → ℝ :=
    fun E x y =>
      S (fun k => E (k, x.2) 0) x.1 y.1 +
        S (fun k => E (y.1, k) 1) x.2 y.2
  let C0 : Set ProcessSample := {s |
    (∀ j x, X j x 0 s + X j (x + (1, 0)) 1 s =
      X j x 1 s + X j (x + (0, 1)) 0 s) ∧
    (∀ j x, min (X j x 0 s) (X j x 1 s) = s.1 x)}
  let C : Set ProcessSample := C0 ∩ Q
  change MeasurableSet C ∧
    (∀ z s, processShift z s ∈ C ↔ s ∈ C) ∧
    Measurable (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
      Rminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
      Rplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ s h x, Rminus h x (x + (1, 0)) s = eMinus h x 0 s ∧
      Rminus h x (x + (0, 1)) s = eMinus h x 1 s) ∧
    (∀ s h x, Rplus h x (x + (1, 0)) s = ePlus h x 0 s ∧
      Rplus h x (x + (0, 1)) s = ePlus h x 1 s) ∧
    ∀ s ∈ C, ∀ h,
      (∀ x y z, Rminus h (x + z) (y + z) s =
        Rminus h x y (processShift z s)) ∧
      (∀ x y z, Rplus h (x + z) (y + z) s =
        Rplus h x y (processShift z s)) ∧
      (∀ x y z, Rminus h x y s + Rminus h y z s = Rminus h x z s) ∧
      (∀ x y z, Rplus h x y s + Rplus h y z s = Rplus h x z s) ∧
      recovers_environment s.1 (fun x y => Rminus h x y s) ∧
      recovers_environment s.1 (fun x y => Rplus h x y s)
  obtain ⟨hQMeas, hQShift, hEminusMeas, hEplusMeas, heMinusMeas,
    hePlusMeas, _, _, _, hMinusLimit, hPlusLimit⟩ :=
      countable_unit_envelopes_measurable_finite_and_cofinal g D happrox

  have hRaw (j : ℕ) (x : Lattice) (i : Fin 2) :
      Measurable (X j x i) := by
    exact (measurable_pi_apply i).comp
      ((measurable_pi_apply x).comp ((measurable_pi_apply j).comp measurable_snd))
  have hEnvironment (x : Lattice) :
      Measurable (fun s : ProcessSample => s.1 x) :=
    (measurable_pi_apply x).comp measurable_fst
  have hSquareMeas (j : ℕ) (x : Lattice) :
      MeasurableSet {s : ProcessSample |
        X j x 0 s + X j (x + (1, 0)) 1 s =
          X j x 1 s + X j (x + (0, 1)) 0 s} := by
    exact measurableSet_eq_fun
      ((hRaw j x 0).add (hRaw j (x + (1, 0)) 1))
      ((hRaw j x 1).add (hRaw j (x + (0, 1)) 0))
  have hRecoveryMeas (j : ℕ) (x : Lattice) :
      MeasurableSet {s : ProcessSample |
        min (X j x 0 s) (X j x 1 s) = s.1 x} := by
    exact measurableSet_eq_fun ((hRaw j x 0).min (hRaw j x 1)) (hEnvironment x)
  have hSquareAll : MeasurableSet {s : ProcessSample | ∀ j x,
      X j x 0 s + X j (x + (1, 0)) 1 s =
        X j x 1 s + X j (x + (0, 1)) 0 s} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro x
    exact hSquareMeas j x
  have hRecoveryAll : MeasurableSet {s : ProcessSample | ∀ j x,
      min (X j x 0 s) (X j x 1 s) = s.1 x} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro x
    exact hRecoveryMeas j x
  have hC0Meas : MeasurableSet C0 := by
    change MeasurableSet
      ({s : ProcessSample | ∀ j x,
        X j x 0 s + X j (x + (1, 0)) 1 s =
          X j x 1 s + X j (x + (0, 1)) 0 s} ∩
       {s : ProcessSample | ∀ j x, min (X j x 0 s) (X j x 1 s) = s.1 x})
    exact hSquareAll.inter hRecoveryAll
  have hC0Forward (z : Lattice) (s : ProcessSample) (hs : s ∈ C0) :
      processShift z s ∈ C0 := by
    change (∀ j x, X j x 0 s + X j (x + (1, 0)) 1 s =
        X j x 1 s + X j (x + (0, 1)) 0 s) ∧
      (∀ j x, min (X j x 0 s) (X j x 1 s) = s.1 x) at hs
    change (∀ j x, X j x 0 (processShift z s) +
        X j (x + (1, 0)) 1 (processShift z s) =
          X j x 1 (processShift z s) +
            X j (x + (0, 1)) 0 (processShift z s)) ∧
      (∀ j x, min (X j x 0 (processShift z s))
        (X j x 1 (processShift z s)) = (processShift z s).1 x)
    constructor
    · intro j x
      have hx := hs.1 j (z + x)
      simpa [X, processShift, add_assoc, add_left_comm, add_comm] using hx
    · intro j x
      have hx := hs.2 j (z + x)
      simpa [X, processShift, environmentTranslationEquiv_apply,
        add_assoc, add_left_comm, add_comm] using hx
  have hC0Shift (z : Lattice) (s : ProcessSample) :
      processShift z s ∈ C0 ↔ s ∈ C0 := by
    constructor
    · intro hs
      have h := hC0Forward (-z) (processShift z s) hs
      rwa [processShift_neg_processShift] at h
    · exact hC0Forward z s
  have hCMeas : MeasurableSet C := by
    change MeasurableSet (C0 ∩ Q)
    exact hC0Meas.inter hQMeas
  have hCShift (z : Lattice) (s : ProcessSample) :
      processShift z s ∈ C ↔ s ∈ C := by
    change (processShift z s ∈ C0 ∧ processShift z s ∈ Q) ↔
      (s ∈ C0 ∧ s ∈ Q)
    exact and_congr (hC0Shift z s) (hQShift z s)

  have hRminusMeas : Measurable (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
      Rminus q.1 q.2.1 q.2.2.1 q.2.2.2) :=
    measurable_lattice_coordinate_path_sum eMinus heMinusMeas
  have hRplusMeas : Measurable (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
      Rplus q.1 q.2.1 q.2.2.1 q.2.2.2) :=
    measurable_lattice_coordinate_path_sum ePlus hePlusMeas
  have hRminusUnit := lattice_coordinate_path_sum_unit_values eMinus
  have hRplusUnit := lattice_coordinate_path_sum_unit_values ePlus

  have hCurlMinus (s : ProcessSample) (hs : s ∈ C) (h : SupportTilt g) :
      ∀ x, eMinus h x 0 s + eMinus h (x + (1, 0)) 1 s =
        eMinus h x 1 s + eMinus h (x + (0, 1)) 0 s := by
    change s ∈ C0 ∧ s ∈ Q at hs
    obtain ⟨a, b, hMono, hAnti, hBetween, hLower, hUpper⟩ := happrox h
    have hlim := hMinusLimit s hs.2 h a hMono
      (fun n => (hBetween n).1) hLower
    intro x
    have hLeft : Tendsto
        (fun n => X (a n) x 0 s + X (a n) (x + (1, 0)) 1 s) atTop
        (𝓝 (eMinus h x 0 s + eMinus h (x + (1, 0)) 1 s)) :=
      (hlim x 0).add (hlim (x + (1, 0)) 1)
    have hRight : Tendsto
        (fun n => X (a n) x 1 s + X (a n) (x + (0, 1)) 0 s) atTop
        (𝓝 (eMinus h x 1 s + eMinus h (x + (0, 1)) 0 s)) :=
      (hlim x 1).add (hlim (x + (0, 1)) 0)
    have hSame :
        (fun n => X (a n) x 0 s + X (a n) (x + (1, 0)) 1 s) =
        fun n => X (a n) x 1 s + X (a n) (x + (0, 1)) 0 s := by
      funext n
      exact hs.1.1 (a n) x
    rw [hSame] at hLeft
    exact tendsto_nhds_unique hLeft hRight

  have hCurlPlus (s : ProcessSample) (hs : s ∈ C) (h : SupportTilt g) :
      ∀ x, ePlus h x 0 s + ePlus h (x + (1, 0)) 1 s =
        ePlus h x 1 s + ePlus h (x + (0, 1)) 0 s := by
    change s ∈ C0 ∧ s ∈ Q at hs
    obtain ⟨a, b, hMono, hAnti, hBetween, hLower, hUpper⟩ := happrox h
    have hlim := hPlusLimit s hs.2 h b hAnti
      (fun n => (hBetween n).2) hUpper
    intro x
    have hLeft : Tendsto
        (fun n => X (b n) x 0 s + X (b n) (x + (1, 0)) 1 s) atTop
        (𝓝 (ePlus h x 0 s + ePlus h (x + (1, 0)) 1 s)) :=
      (hlim x 0).add (hlim (x + (1, 0)) 1)
    have hRight : Tendsto
        (fun n => X (b n) x 1 s + X (b n) (x + (0, 1)) 0 s) atTop
        (𝓝 (ePlus h x 1 s + ePlus h (x + (0, 1)) 0 s)) :=
      (hlim x 1).add (hlim (x + (0, 1)) 0)
    have hSame :
        (fun n => X (b n) x 0 s + X (b n) (x + (1, 0)) 1 s) =
        fun n => X (b n) x 1 s + X (b n) (x + (0, 1)) 0 s := by
      funext n
      exact hs.1.1 (b n) x
    rw [hSame] at hLeft
    exact tendsto_nhds_unique hLeft hRight

  have hRecoveryMinus (s : ProcessSample) (hs : s ∈ C) (h : SupportTilt g) :
      ∀ x, min (eMinus h x 0 s) (eMinus h x 1 s) = s.1 x := by
    change s ∈ C0 ∧ s ∈ Q at hs
    obtain ⟨a, b, hMono, hAnti, hBetween, hLower, hUpper⟩ := happrox h
    have hlim := hMinusLimit s hs.2 h a hMono
      (fun n => (hBetween n).1) hLower
    intro x
    have hMin : Tendsto
        (fun n => min (X (a n) x 0 s) (X (a n) x 1 s)) atTop
        (𝓝 (min (eMinus h x 0 s) (eMinus h x 1 s))) :=
      (hlim x 0).min (hlim x 1)
    have hSame :
        (fun n => min (X (a n) x 0 s) (X (a n) x 1 s)) = fun _ => s.1 x := by
      funext n
      exact hs.1.2 (a n) x
    rw [hSame] at hMin
    exact tendsto_nhds_unique hMin tendsto_const_nhds

  have hRecoveryPlus (s : ProcessSample) (hs : s ∈ C) (h : SupportTilt g) :
      ∀ x, min (ePlus h x 0 s) (ePlus h x 1 s) = s.1 x := by
    change s ∈ C0 ∧ s ∈ Q at hs
    obtain ⟨a, b, hMono, hAnti, hBetween, hLower, hUpper⟩ := happrox h
    have hlim := hPlusLimit s hs.2 h b hAnti
      (fun n => (hBetween n).2) hUpper
    intro x
    have hMin : Tendsto
        (fun n => min (X (b n) x 0 s) (X (b n) x 1 s)) atTop
        (𝓝 (min (ePlus h x 0 s) (ePlus h x 1 s))) :=
      (hlim x 0).min (hlim x 1)
    have hSame :
        (fun n => min (X (b n) x 0 s) (X (b n) x 1 s)) = fun _ => s.1 x := by
      funext n
      exact hs.1.2 (b n) x
    rw [hSame] at hMin
    exact tendsto_nhds_unique hMin tendsto_const_nhds

  have hOnC : ∀ s ∈ C, ∀ h : SupportTilt g,
      (∀ x y z, Rminus h (x + z) (y + z) s =
        Rminus h x y (processShift z s)) ∧
      (∀ x y z, Rplus h (x + z) (y + z) s =
        Rplus h x y (processShift z s)) ∧
      (∀ x y z, Rminus h x y s + Rminus h y z s = Rminus h x z s) ∧
      (∀ x y z, Rplus h x y s + Rplus h y z s = Rplus h x z s) ∧
      recovers_environment s.1 (fun x y => Rminus h x y s) ∧
      recovers_environment s.1 (fun x y => Rplus h x y s) := by
    intro s hs h
    have hCurlM := hCurlMinus s hs h
    have hCurlP := hCurlPlus s hs h
    have hRecM := hRecoveryMinus s hs h
    have hRecP := hRecoveryPlus s hs h
    let Em : Lattice → Fin 2 → ℝ := fun x i => eMinus h x i s
    let Ep : Lattice → Fin 2 → ℝ := fun x i => ePlus h x i s
    obtain ⟨hAddM, hTransM⟩ :=
      lattice_edge_extension_sum_additive_translation Em hCurlM
    obtain ⟨hAddP, hTransP⟩ :=
      lattice_edge_extension_sum_additive_translation Ep hCurlP
    have hEshiftM (z : Lattice) (x : Lattice) (i : Fin 2) :
        Em (z + x) i = eMinus h x i (processShift z s) := by
      simp [Em, eMinus, Eminus, X, processShift]
    have hEshiftP (z : Lattice) (x : Lattice) (i : Fin 2) :
        Ep (z + x) i = ePlus h x i (processShift z s) := by
      simp [Ep, ePlus, Eplus, X, processShift]
    have hEshiftMFun (z : Lattice) :
        (fun u i => Em (z + u) i) =
          fun u i => eMinus h u i (processShift z s) := by
      funext u i
      exact hEshiftM z u i
    have hEshiftPFun (z : Lattice) :
        (fun u i => Ep (z + u) i) =
          fun u i => ePlus h u i (processShift z s) := by
      funext u i
      exact hEshiftP z u i
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y z
      have hT := hTransM z x y
      have hT' : Rpath (fun u i => Em (z + u) i) x y =
          Rpath Em (z + x) (z + y) := by
        simpa [Rpath, S, Em] using hT
      calc
        Rminus h (x + z) (y + z) s = Rminus h (z + x) (z + y) s := by
          simp only [add_comm x z, add_comm y z]
        _ = Rminus h x y (processShift z s) := by
          change Rpath Em (z + x) (z + y) =
            Rpath (fun u i => eMinus h u i (processShift z s)) x y
          exact hT'.symm.trans (by rw [hEshiftMFun z])
    · intro x y z
      have hT := hTransP z x y
      have hT' : Rpath (fun u i => Ep (z + u) i) x y =
          Rpath Ep (z + x) (z + y) := by
        simpa [Rpath, S, Ep] using hT
      calc
        Rplus h (x + z) (y + z) s = Rplus h (z + x) (z + y) s := by
          simp only [add_comm x z, add_comm y z]
        _ = Rplus h x y (processShift z s) := by
          change Rpath Ep (z + x) (z + y) =
            Rpath (fun u i => ePlus h u i (processShift z s)) x y
          exact hT'.symm.trans (by rw [hEshiftPFun z])
    · intro x y z
      simpa [Rminus, Rpath, S, Em] using hAddM x y z
    · intro x y z
      simpa [Rplus, Rpath, S, Ep] using hAddP x y z
    · intro x
      change min (Rminus h x (x + (1, 0)) s)
          (Rminus h x (x + (0, 1)) s) = s.1 x
      have hUnitM1 : Rminus h x (x + (1, 0)) s = eMinus h x 0 s := by
        simpa [Rminus, S] using (hRminusUnit h x s).1
      have hUnitM2 : Rminus h x (x + (0, 1)) s = eMinus h x 1 s := by
        simpa [Rminus, S] using (hRminusUnit h x s).2
      rw [hUnitM1, hUnitM2]
      exact hRecM x
    · intro x
      change min (Rplus h x (x + (1, 0)) s)
          (Rplus h x (x + (0, 1)) s) = s.1 x
      have hUnitP1 : Rplus h x (x + (1, 0)) s = ePlus h x 0 s := by
        simpa [Rplus, S] using (hRplusUnit h x s).1
      have hUnitP2 : Rplus h x (x + (0, 1)) s = ePlus h x 1 s := by
        simpa [Rplus, S] using (hRplusUnit h x s).2
      rw [hUnitP1, hUnitP2]
      exact hRecP x
  exact ⟨hCMeas, hCShift, hRminusMeas, hRplusMeas,
    (fun s h x => hRminusUnit h x s), (fun s h x => hRplusUnit h x s), hOnC⟩

end LPP.Busemann
