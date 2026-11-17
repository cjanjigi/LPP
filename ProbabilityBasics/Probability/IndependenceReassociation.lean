/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Reassociating independent random variables

This file contains the product-law reassociation that turns independence of
`X` from `Y` and of `(X, Y)` from `W` into independence of `X` from
`(Y, W)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics

/--
If `X` is independent of `Y`, and the pair `(X, Y)` is independent of `W`,
then `X` is independent of the pair `(Y, W)`. This is the product-law step
used with the downward finite-energy condition in Georgiou, Rassoul-Agha and Seppäläinen,
arXiv:1510.00860v1, Appendix A, (A.4), lines 1420–1424.
-/
theorem indepFun_prodMk_right_of_indepFun_prodMk_left
    {Ω A S Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → A} {Y : Ω → S} {W : Ω → Z}
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    (hXY_W : IndepFun (fun ω => (X ω, Y ω)) W P)
    (hXY : IndepFun X Y P) :
    IndepFun X (fun ω => (Y ω, W ω)) P := by
  let XY : Ω → A × S := fun ω => (X ω, Y ω)
  let YW : Ω → S × Z := fun ω => (Y ω, W ω)
  let XY_W : Ω → (A × S) × Z := fun ω => (XY ω, W ω)
  let X_YW : Ω → A × (S × Z) := fun ω => (X ω, YW ω)

  have hXY_meas : Measurable XY := hX.prodMk hY
  have hYW_meas : Measurable YW := hY.prodMk hW
  have hXY_W_meas : Measurable XY_W := hXY_meas.prodMk hW

  -- Project the independent block onto its second coordinate.
  have hYW : IndepFun Y W P := by
    simpa [Function.comp_def] using
      hXY_W.comp measurable_snd measurable_id

  -- Express each independence fact as an equality of joint and product laws.
  have hXY_law : P.map XY = (P.map X).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable).mp hXY
  have hYW_law : P.map YW = (P.map Y).prod (P.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hY.aemeasurable hW.aemeasurable).mp hYW
  have hXY_W_law : P.map XY_W = (P.map XY).prod (P.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hXY_meas.aemeasurable hW.aemeasurable).mp hXY_W

  -- Mapping the joint law through prodAssoc changes ((X, Y), W) into (X, (Y, W)).
  have h_assoc_fun : MeasurableEquiv.prodAssoc ∘ XY_W = X_YW := by
    funext ω
    rfl
  have h_assoc_map :
      (P.map XY_W).map MeasurableEquiv.prodAssoc = P.map X_YW := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hXY_W_meas,
      h_assoc_fun]
  have h_assoc_law :
      (P.map XY_W).map MeasurableEquiv.prodAssoc =
        (P.map X).prod ((P.map Y).prod (P.map W)) := by
    rw [hXY_W_law, hXY_law]
    exact Measure.prodAssoc_prod

  -- Reassociate the three marginal laws and replace the law of (Y, W).
  have h_joint_law :
      P.map X_YW = (P.map X).prod (P.map YW) := by
    calc
      P.map X_YW = (P.map XY_W).map MeasurableEquiv.prodAssoc :=
        h_assoc_map.symm
      _ = (P.map X).prod ((P.map Y).prod (P.map W)) := h_assoc_law
      _ = (P.map X).prod (P.map YW) := by rw [hYW_law]

  exact (indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable hYW_meas.aemeasurable).2 h_joint_law

end ProbabilityBasics
