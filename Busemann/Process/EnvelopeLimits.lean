/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.UnitEnvelopes
import Mathlib.Tactic

/-! Arbitrary one-sided continuity of the actual unit envelopes. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

private theorem tendsto_of_lower_brackets (a b : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (𝓝 l))
    (hbound : ∀ m, ∀ᶠ n in atTop, a m ≤ b n ∧ b n ≤ l) :
    Tendsto b atTop (𝓝 l) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    obtain ⟨m, hm⟩ := (ha.eventually_const_lt hc).exists
    filter_upwards [hbound m] with n hn
    exact lt_of_lt_of_le hm hn.1
  · intro c hc
    filter_upwards [hbound 0] with n hn
    exact lt_of_le_of_lt hn.2 hc

private theorem tendsto_of_upper_brackets (a b : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (𝓝 l))
    (hbound : ∀ m, ∀ᶠ n in atTop, l ≤ b n ∧ b n ≤ a m) :
    Tendsto b atTop (𝓝 l) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    filter_upwards [hbound 0] with n hn
    exact lt_of_lt_of_le hc hn.1
  · intro c hc
    obtain ⟨m, hm⟩ := (ha.eventually_lt_const hc).exists
    filter_upwards [hbound m] with n hn
    exact lt_of_le_of_lt hn.2 hm

/-- Both literal unit-envelope signs converge to the left or right envelope
along every strictly one-sided convergent tilt sequence, as in JR1810.03580v3
after (4.18). -/
theorem unit_envelopes_tendsto_of_one_sided
(g : Quadrant → ℝ) (D : ℕ → SupportTilt g)
(happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
  StrictMono (fun n => (D (a n)).1.1) ∧
  StrictAnti (fun n => (D (b n)).1.1) ∧
  (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
  Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
  Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1)) :
let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
let Q : Set ProcessSample := {s | ∀ j k x,
  (D j).1.1 ≤ (D k).1.1 → X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
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
(∀ s ∈ Q, ∀ h : SupportTilt g, ∀ hs : ℕ → SupportTilt g,
  (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) → ∀ x i,
  Tendsto (fun n => eMinus (hs n) x i s) atTop (𝓝 (eMinus h x i s)) ∧
  Tendsto (fun n => ePlus (hs n) x i s) atTop (𝓝 (eMinus h x i s))) ∧
(∀ s ∈ Q, ∀ h : SupportTilt g, ∀ hs : ℕ → SupportTilt g,
  (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) → ∀ x i,
  Tendsto (fun n => eMinus (hs n) x i s) atTop (𝓝 (ePlus h x i s)) ∧
  Tendsto (fun n => ePlus (hs n) x i s) atTop (𝓝 (ePlus h x i s)))
 := by
  classical
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
    (D j).1.1 ≤ (D k).1.1 → X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
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
  have hknown := countable_unit_envelopes_measurable_finite_and_cofinal g D happrox
  obtain ⟨_, _, _, _, _, _, hfinite, hwithin, hcross, hlower, hupper⟩ := hknown
  change (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ hs : ℕ → SupportTilt g,
    (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) → ∀ x i,
    Tendsto (fun n => eMinus (hs n) x i s) atTop (𝓝 (eMinus h x i s)) ∧
    Tendsto (fun n => ePlus (hs n) x i s) atTop (𝓝 (eMinus h x i s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ hs : ℕ → SupportTilt g,
    (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) → ∀ x i,
    Tendsto (fun n => eMinus (hs n) x i s) atTop (𝓝 (ePlus h x i s)) ∧
    Tendsto (fun n => ePlus (hs n) x i s) atTop (𝓝 (ePlus h x i s)))
  -- Fixed raw indices bracket both finite real envelopes at a neighboring tilt.
  have hbelow (s : ProcessSample) (hs : s ∈ Q) (v : SupportTilt g) (j : ℕ)
      (hj : (D j).1.1 < v.1.1) (x : Lattice) :
      eMinus v x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ eMinus v x 1 s := by
    have he : Eminus v x 0 s ≤ (X j x 0 s : EReal) := by
      change (⨅ k, if (D k).1.1 < v.1.1 then (X k x 0 s : EReal) else ⊤) ≤ _
      exact iInf_le_of_le j (by rw [ite_eq_left hj])
    have hn : (X j x 1 s : EReal) ≤ Eminus v x 1 s := by
      change _ ≤ ⨆ k, if (D k).1.1 < v.1.1 then (X k x 1 s : EReal) else ⊥
      exact le_iSup_of_le j (by rw [ite_eq_left hj])
    exact ⟨by simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal he (hfinite s hs v x 0).2.1 (EReal.coe_ne_top _),
      by simpa only [EReal.toReal_coe] using
        EReal.toReal_le_toReal hn (EReal.coe_ne_bot _) (hfinite s hs v x 1).1⟩
  have habove (s : ProcessSample) (hs : s ∈ Q) (v : SupportTilt g) (j : ℕ)
      (hj : v.1.1 < (D j).1.1) (x : Lattice) :
      X j x 0 s ≤ ePlus v x 0 s ∧ ePlus v x 1 s ≤ X j x 1 s := by
    have he : (X j x 0 s : EReal) ≤ Eplus v x 0 s := by
      change _ ≤ ⨆ k, if v.1.1 < (D k).1.1 then (X k x 0 s : EReal) else ⊥
      exact le_iSup_of_le j (by rw [ite_eq_left hj])
    have hn : Eplus v x 1 s ≤ (X j x 1 s : EReal) := by
      change (⨅ k, if v.1.1 < (D k).1.1 then (X k x 1 s : EReal) else ⊤) ≤ _
      exact iInf_le_of_le j (by rw [ite_eq_left hj])
    exact ⟨by simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal he (EReal.coe_ne_bot _) (hfinite s hs v x 0).2.2.1,
      by simpa only [EReal.toReal_coe] using
        EReal.toReal_le_toReal hn (hfinite s hs v x 1).2.2.2 (EReal.coe_ne_top _)⟩
  constructor
  · intro s hs h v hv hlim x i
    obtain ⟨a, b, hma, hmb, hab, hla, hlb⟩ := happrox h
    have hraw : ∀ i, Tendsto (fun n => X (a n) x i s) atTop (𝓝 (eMinus h x i s)) :=
      hlower s hs h a hma (fun n => (hab n).1) hla x
    have hcoord : Tendsto (fun n => (v n).1.1) atTop (𝓝 h.1.1) :=
      (continuous_fst.tendsto h.1).comp ((continuous_subtype_val.tendsto h).comp hlim)
    have hside (m : ℕ) : ∀ᶠ n in atTop, (D (a m)).1.1 < (v n).1.1 :=
      hcoord.eventually_const_lt ((hab m).1)
    fin_cases i
    · constructor
      · apply tendsto_of_upper_brackets (fun n => X (a n) x 0 s) _ _ (hraw 0)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs (v n) h (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨hc.1.trans hw.1, (hbelow s hs (v n) (a m) hn x).1⟩
      · apply tendsto_of_upper_brackets (fun n => X (a n) x 0 s) _ _ (hraw 0)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs (v n) h (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨hc.1, hw.1.trans (hbelow s hs (v n) (a m) hn x).1⟩
    · constructor
      · apply tendsto_of_lower_brackets (fun n => X (a n) x 1 s) _ _ (hraw 1)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs (v n) h (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨(hbelow s hs (v n) (a m) hn x).2, hw.2.trans hc.2⟩
      · apply tendsto_of_lower_brackets (fun n => X (a n) x 1 s) _ _ (hraw 1)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs (v n) h (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨(hbelow s hs (v n) (a m) hn x).2.trans hw.2, hc.2⟩
  · intro s hs h v hv hlim x i
    obtain ⟨a, b, hma, hmb, hab, hla, hlb⟩ := happrox h
    have hraw : ∀ i, Tendsto (fun n => X (b n) x i s) atTop (𝓝 (ePlus h x i s)) :=
      hupper s hs h b hmb (fun n => (hab n).2) hlb x
    have hcoord : Tendsto (fun n => (v n).1.1) atTop (𝓝 h.1.1) :=
      (continuous_fst.tendsto h.1).comp ((continuous_subtype_val.tendsto h).comp hlim)
    have hside (m : ℕ) : ∀ᶠ n in atTop, (v n).1.1 < (D (b m)).1.1 :=
      hcoord.eventually_lt_const ((hab m).2)
    fin_cases i
    · constructor
      · apply tendsto_of_lower_brackets (fun n => X (b n) x 0 s) _ _ (hraw 0)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs h (v n) (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨(habove s hs (v n) (b m) hn x).1.trans hw.1, hc.1⟩
      · apply tendsto_of_lower_brackets (fun n => X (b n) x 0 s) _ _ (hraw 0)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs h (v n) (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨(habove s hs (v n) (b m) hn x).1, hw.1.trans hc.1⟩
    · constructor
      · apply tendsto_of_upper_brackets (fun n => X (b n) x 1 s) _ _ (hraw 1)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs h (v n) (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨hc.2, hw.2.trans (habove s hs (v n) (b m) hn x).2⟩
      · apply tendsto_of_upper_brackets (fun n => X (b n) x 1 s) _ _ (hraw 1)
        intro m
        filter_upwards [hside m] with n hn
        have hc := hcross s hs h (v n) (hv n) x
        have hw := hwithin s hs (v n) x
        exact ⟨hc.2.trans hw.2, (habove s hs (v n) (b m) hn x).2⟩

end LPP.Busemann
