/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.LastPassage
public import Busemann.Frozen.Definitions.InteriorDirection
public import Busemann.Frozen.Definitions.ApproachesFaceInterval
public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Busemann.Geometry.GeodesicCocycleConfinement
import LPP_Foundations.Model.LastPassage.GradientOrder
import Mathlib.Tactic

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

/-- An eventual real upper increment at neighboring sites rules out a plus
infinite extended limit at the west or south site once the east or north
limit is finite. No extended subtraction is used. -/
theorem ereal_limit_finite_of_eventual_real_upper_increment
    (f g : ℕ → ℝ) (a b : EReal) (K : ℝ)
    (ha : Tendsto (fun n => (f n : EReal)) atTop (𝓝 a))
    (hb : Tendsto (fun n => (g n : EReal)) atTop (𝓝 b))
    (hbbot : (⊥ : EReal) < b) (hbtop : b < (⊤ : EReal))
    (hbound : ∀ᶠ n : ℕ in atTop, f n ≤ K + g n) :
    a < (⊤ : EReal) := by
  have hbtop' : b ≠ (⊤ : EReal) := ne_of_lt hbtop
  have hbbot' : b ≠ (⊥ : EReal) := ne_of_gt hbbot
  have hgr : Tendsto g atTop (𝓝 b.toReal) := by
    have h := (EReal.tendsto_toReal hbtop' hbbot').comp hb
    simpa only [Function.comp_def, EReal.toReal_coe] using h
  have hright : Tendsto (fun n => ((K + g n : ℝ) : EReal)) atTop
      (𝓝 ((K + b.toReal : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp
      ((tendsto_const_nhds (x := K)).add hgr)
  have hle : a ≤ ((K + b.toReal : ℝ) : EReal) :=
    le_of_tendsto_of_tendsto ha hright (hbound.mono fun n hn =>
      EReal.coe_le_coe_iff.mpr hn)
  exact lt_of_le_of_lt hle (EReal.coe_lt_top _)

/-- A property known northeast of one signed root propagates to all signed
sites when each finite west and south step preserves it. The northeast anchor
depends on the requested site; no uniform anchor is assumed. -/
theorem all_lattice_of_northeast_and_west_south
    (u : Lattice) (F : Lattice → Prop)
    (hNE : ∀ x, u ≤ x → F x)
    (hWest : ∀ x, F x → F (x - ((1 : ℤ), (0 : ℤ))))
    (hSouth : ∀ x, F x → F (x - ((0 : ℤ), (1 : ℤ)))) :
    ∀ x : Lattice, F x := by
  have hDown (v : Lattice) (hv : F v) :
      ∀ m n : ℕ, F (v - ((m : ℤ), (n : ℤ))) := by
    intro m
    induction m with
    | zero =>
      intro n
      induction n with
      | zero => simpa [Prod.sub_def] using hv
      | succ n ih =>
        have hs := hSouth (v - ((0 : ℤ), (n : ℤ))) ih
        convert hs using 1; ext <;> simp [Prod.sub_def, Nat.cast_succ]; ring
    | succ m ih =>
      intro n
      have hw := hWest (v - ((m : ℤ), (n : ℤ))) (ih n)
      convert hw using 1; ext <;> simp [Prod.sub_def, Nat.cast_succ]; ring
  intro x
  let v : Lattice := (max u.1 x.1, max u.2 x.2)
  have huv : u ≤ v := ⟨le_max_left _ _, le_max_left _ _⟩
  let m : ℕ := (v.1 - x.1).toNat
  let n : ℕ := (v.2 - x.2).toNat
  have hvm : v - ((m : ℤ), (n : ℤ)) = x := by
    apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub, m, n, v] <;> omega
  rw [← hvm]
  exact hDown v (hNE v huv) m n

/-- A northwest and a southeast calibrated barrier bound the two real
neighboring-start passage increments along the ordinary ray. All three rays
start at the same signed site, so their local-time endpoints have equal level.
The horizontal gradient uses the northwest endpoint; the vertical gradient
uses the southeast endpoint. Strong Existence, g609 and g619, lines 1663–1693. -/
theorem eventually_neighbor_upper_bounds_between_face_barriers
    (ω : Environment)
    (hUniform : ∀ x : Lattice, ∀ ε : ℚ,
      0 < ε → ε < 1 / 2 →
      ∃ C N : ℕ, 0 < N ∧
        ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
          (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
          0 < d.1 ∧ 0 < d.2 ∧
          |lastPassage ω x d -
            lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
          |lastPassage ω x d -
            lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ))
    (u x : Lattice) (γ : ℕ → Lattice)
    (dNW dSE : ℕ → ℕ × ℕ)
    (leftNW rightNW leftSE rightSE : InteriorDirection)
    (hγ0 : γ 0 = u)
    (hγsteps : ∀ n, γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
      γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (hγescape₁ : Tendsto (fun n => (γ n).1) atTop atTop)
    (hγescape₂ : Tendsto (fun n => (γ n).2) atTop atTop)
    (hNWface : approachesFaceInterval dNW leftNW rightNW)
    (hSEface : approachesFaceInterval dSE leftSE rightSE)
    (hNW0 : u + (((dNW 0).1 : ℤ), ((dNW 0).2 : ℤ)) = u)
    (hSE0 : u + (((dSE 0).1 : ℤ), ((dSE 0).2 : ℤ)) = u)
    (hNWsteps : ∀ n,
      u + (((dNW (n + 1)).1 : ℤ), ((dNW (n + 1)).2 : ℤ)) =
        (u + (((dNW n).1 : ℤ), ((dNW n).2 : ℤ))) + ((1 : ℤ), (0 : ℤ)) ∨
      u + (((dNW (n + 1)).1 : ℤ), ((dNW (n + 1)).2 : ℤ)) =
        (u + (((dNW n).1 : ℤ), ((dNW n).2 : ℤ))) + ((0 : ℤ), (1 : ℤ)))
    (hSEsteps : ∀ n,
      u + (((dSE (n + 1)).1 : ℤ), ((dSE (n + 1)).2 : ℤ)) =
        (u + (((dSE n).1 : ℤ), ((dSE n).2 : ℤ))) + ((1 : ℤ), (0 : ℤ)) ∨
      u + (((dSE (n + 1)).1 : ℤ), ((dSE (n + 1)).2 : ℤ)) =
        (u + (((dSE n).1 : ℤ), ((dSE n).2 : ℤ))) + ((0 : ℤ), (1 : ℤ)))
    (hOrderNW : ∀ᶠ n : ℕ in atTop,
      (u + (((dNW n).1 : ℤ), ((dNW n).2 : ℤ))).1 ≤ (γ n).1)
    (hOrderSE : ∀ᶠ n : ℕ in atTop,
      (γ n).1 ≤ (u + (((dSE n).1 : ℤ), ((dSE n).2 : ℤ))).1) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      x ≤ γ n ∧ x + ((1 : ℤ), (0 : ℤ)) ≤ γ n ∧
        x + ((0 : ℤ), (1 : ℤ)) ≤ γ n ∧
        lastPassage ω x (((γ n).1 - x.1).toNat, ((γ n).2 - x.2).toNat) -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
            (((γ n).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
             ((γ n).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤ K ∧
        lastPassage ω x (((γ n).1 - x.1).toNat, ((γ n).2 - x.2).toNat) -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
            (((γ n).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
             ((γ n).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤ K := by
  let ρNW (n : ℕ) : Lattice := u + (((dNW n).1 : ℤ), ((dNW n).2 : ℤ))
  let ρSE (n : ℕ) : Lattice := u + (((dSE n).1 : ℤ), ((dSE n).2 : ℤ))
  obtain ⟨KNW, hNWbound⟩ :=
    eventually_signed_barrier_neighbor_upper_bounds ω hUniform u x
      dNW leftNW rightNW hNWface
  obtain ⟨KSE, hSEbound⟩ :=
    eventually_signed_barrier_neighbor_upper_bounds ω hUniform u x
      dSE leftSE rightSE hSEface
  have hγdomain : ∀ᶠ n : ℕ in atTop,
      x ≤ γ n ∧ x + ((1 : ℤ), (0 : ℤ)) ≤ γ n ∧
        x + ((0 : ℤ), (1 : ℤ)) ≤ γ n := by
    filter_upwards [tendsto_atTop.1 hγescape₁ (x.1 + 1),
      tendsto_atTop.1 hγescape₂ (x.2 + 1)] with n hn₁ hn₂
    constructor
    · exact ⟨by omega, by omega⟩
    constructor
    · exact ⟨by dsimp; omega, by dsimp; omega⟩
    · exact ⟨by dsimp; omega, by dsimp; omega⟩
  have hLevelNW (n : ℕ) : (ρNW n).1 + (ρNW n).2 =
      (γ n).1 + (γ n).2 :=
    (same_level_of_same_root_up_right_steps u γ ρNW hγ0 hNW0
      hγsteps hNWsteps n).symm
  have hLevelSE (n : ℕ) : (γ n).1 + (γ n).2 =
      (ρSE n).1 + (ρSE n).2 :=
    same_level_of_same_root_up_right_steps u γ ρSE hγ0 hSE0
      hγsteps hSEsteps n
  refine ⟨max KNW KSE, ?_⟩
  filter_upwards [hNWbound, hSEbound, hγdomain, hOrderNW, hOrderSE]
    with n hnw hse hγ horderNW horderSE
  have hGradWest :=
    LPP.passage_difference_antidiagonal_order ω x (0 : Fin 2)
      (ρNW n) (γ n) ⟨hnw.1, hnw.2.1⟩ ⟨hγ.1, hγ.2.1⟩
      (hLevelNW n) horderNW
  have hGradSouth :=
    LPP.passage_difference_antidiagonal_order ω x (1 : Fin 2)
      (γ n) (ρSE n) ⟨hγ.1, hγ.2.2⟩ ⟨hse.1, hse.2.2.1⟩
      (hLevelSE n) horderSE
  have hWest :
      lastPassage ω x (((γ n).1 - x.1).toNat, ((γ n).2 - x.2).toNat) -
        lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
          (((γ n).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
           ((γ n).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤ KNW := by
    have hCompare :
        lastPassage ω x (((γ n).1 - x.1).toNat, ((γ n).2 - x.2).toNat) -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
            (((γ n).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
             ((γ n).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤
        lastPassage ω x (((ρNW n).1 - x.1).toNat,
            ((ρNW n).2 - x.2).toNat) -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
            (((ρNW n).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
             ((ρNW n).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) := by
      simpa [orderedPassage, finiteEdgeStep] using hGradWest
    exact hCompare.trans hnw.2.2.2.1
  have hSouth :
      lastPassage ω x (((γ n).1 - x.1).toNat, ((γ n).2 - x.2).toNat) -
        lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
          (((γ n).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
           ((γ n).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤ KSE := by
    have hCompare :
        lastPassage ω x (((γ n).1 - x.1).toNat, ((γ n).2 - x.2).toNat) -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
            (((γ n).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
             ((γ n).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤
        lastPassage ω x (((ρSE n).1 - x.1).toNat,
            ((ρSE n).2 - x.2).toNat) -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
            (((ρSE n).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
             ((ρSE n).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) := by
      simpa [orderedPassage, finiteEdgeStep] using hGradSouth
    exact hCompare.trans hse.2.2.2.2
  exact ⟨hγ.1, hγ.2.1, hγ.2.2,
    hWest.trans (le_max_left _ _), hSouth.trans (le_max_right _ _)⟩

end LPP.Busemann
