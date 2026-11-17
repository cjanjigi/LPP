/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.RawPairedTrace
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Limits for squeezed states

The finite-state constructor is continuous. When time tends to either
infinity, every finite state tends to the corresponding pole, regardless of
how its real-valued state coordinates vary.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LPP.Busemann

private theorem continuous_compressReal : Continuous compressReal := by
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt (fun y : ℝ => y / (1 + |y|)) x
  exact continuousAt_id.div
    (continuousAt_const.add continuous_abs.continuousAt)
    (ne_of_gt (by linarith [abs_nonneg x]))

private theorem continuous_squeezeScale : Continuous squeezeScale := by
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt (fun y : ℝ => (1 : ℝ) / (1 + |y|)) x
  exact continuousAt_const.div
    (continuousAt_const.add continuous_abs.continuousAt)
    (ne_of_gt (by linarith [abs_nonneg x]))

private theorem abs_compressReal_lt_one (x : ℝ) : |compressReal x| < 1 := by
  have hden : 0 < 1 + |x| := by linarith [abs_nonneg x]
  rw [compressReal, abs_div, abs_of_pos hden]
  rw [div_lt_one hden]
  linarith [abs_nonneg x]

private theorem squeezeScale_nonneg (t : ℝ) : 0 ≤ squeezeScale t := by
  rw [squeezeScale]
  exact div_nonneg zero_le_one (by linarith [abs_nonneg t])

private theorem compressReal_eq_one_sub_squeezeScale {t : ℝ} (ht : 0 ≤ t) :
    compressReal t = 1 - squeezeScale t := by
  rw [compressReal, squeezeScale, abs_of_nonneg ht]
  have hden : 1 + t ≠ 0 := ne_of_gt (by linarith)
  calc
    t / (1 + t) = ((1 + t) - 1) / (1 + t) := by congr 1; ring
    _ = (1 + t) / (1 + t) - 1 / (1 + t) := by rw [sub_div]
    _ = 1 - 1 / (1 + t) := by rw [div_self hden]

private theorem compressReal_eq_neg_one_add_squeezeScale {t : ℝ} (ht : t ≤ 0) :
    compressReal t = -1 + squeezeScale t := by
  rw [compressReal, squeezeScale, abs_of_nonpos ht]
  have hden : 1 - t ≠ 0 := ne_of_gt (by linarith)
  calc
    t / (1 - t) = (1 - (1 - t)) / (1 - t) := by congr 1; ring
    _ = 1 / (1 - t) - (1 - t) / (1 - t) := by rw [sub_div]
    _ = 1 / (1 - t) - 1 := by rw [div_self hden]
    _ = -1 + 1 / (1 - t) := by ring

private theorem tendsto_squeezeScale_of_abs_tendsto_atTop
    {α : Type*} {l : Filter α} {t : α → ℝ}
    (h_abs : Tendsto (fun a => |t a|) l atTop) :
    Tendsto (fun a => squeezeScale (t a)) l (𝓝 0) := by
  have h_den : Tendsto (fun a => 1 + |t a|) l atTop := by
    refine Filter.tendsto_atTop_mono' l ?_ h_abs
    exact Eventually.of_forall fun a => by linarith [abs_nonneg (t a)]
  have h_inv : Tendsto (fun a => (1 + |t a|)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h_den
  simpa [squeezeScale, one_div] using h_inv

private theorem tendsto_squeezeScale_atTop
    {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : Tendsto t l atTop) :
    Tendsto (fun a => squeezeScale (t a)) l (𝓝 0) := by
  apply tendsto_squeezeScale_of_abs_tendsto_atTop
  exact tendsto_abs_atTop_atTop.comp ht

private theorem tendsto_squeezeScale_atBot
    {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : Tendsto t l atBot) :
    Tendsto (fun a => squeezeScale (t a)) l (𝓝 0) := by
  apply tendsto_squeezeScale_of_abs_tendsto_atTop
  exact tendsto_abs_atBot_atTop.comp ht

private theorem tendsto_compressReal_atTop
    {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : Tendsto t l atTop) :
    Tendsto (fun a => compressReal (t a)) l (𝓝 1) := by
  have h_scale := tendsto_squeezeScale_atTop ht
  have h_limit : Tendsto (fun a => 1 - squeezeScale (t a)) l (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub h_scale
  apply Tendsto.congr' ?_ h_limit
  filter_upwards [ht.eventually_ge_atTop 0] with a ha
  exact (compressReal_eq_one_sub_squeezeScale (t := t a) ha).symm

private theorem tendsto_compressReal_atBot
    {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : Tendsto t l atBot) :
    Tendsto (fun a => compressReal (t a)) l (𝓝 (-1 : ℝ)) := by
  have h_scale := tendsto_squeezeScale_atBot ht
  have h_limit : Tendsto (fun a => -1 + squeezeScale (t a)) l (𝓝 (-1 : ℝ)) := by
    simpa using tendsto_const_nhds.add h_scale
  apply Tendsto.congr' ?_ h_limit
  filter_upwards [ht.eventually_le_atBot 0] with a ha
  exact (compressReal_eq_neg_one_add_squeezeScale (t := t a) ha).symm

private theorem tendsto_scaled_compressReal_zero
    {α : Type*} {l : Filter α} {s y : α → ℝ}
    (h_scale : Tendsto s l (𝓝 0))
    (h_nonneg : ∀ a, 0 ≤ s a)
    (h_bound : ∀ a, |compressReal (y a)| ≤ 1) :
    Tendsto (fun a => s a * compressReal (y a)) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h_scale.neg) h_scale ?_ ?_
  · intro a
    have h_lower : -1 ≤ compressReal (y a) := (abs_le.mp (h_bound a)).1
    have h_mul := mul_le_mul_of_nonneg_left h_lower (h_nonneg a)
    simpa using h_mul
  · intro a
    have h_upper : compressReal (y a) ≤ 1 := (abs_le.mp (h_bound a)).2
    have h_mul := mul_le_mul_of_nonneg_left h_upper (h_nonneg a)
    simpa using h_mul

/-- The finite state constructor is continuous in its state and time inputs,
using the embedding formula in
`Busemann/Frozen/StrongExistence/Definitions/SqueezedStateEmbedding.lean:11-14`
and induced topology in
`Busemann/Frozen/StrongExistence/Definitions/SqueezedStateTopology.lean:10-13`. -/
theorem continuous_squeezedState_finite (J : Type*) :
    Continuous (fun p : (J → ℝ) × ℝ =>
      (SqueezedState.finite p.1 p.2 : SqueezedState J)) := by
  -- The topology on squeezed states is induced by the explicit embedding.
  apply continuous_induced_rng.2
  change Continuous (fun p : (J → ℝ) × ℝ =>
    (compressReal p.2, fun i => squeezeScale p.2 * compressReal (p.1 i)))
  have h_time : Continuous (fun p : (J → ℝ) × ℝ => compressReal p.2) :=
    continuous_compressReal.comp continuous_snd
  have h_state : Continuous (fun p : (J → ℝ) × ℝ =>
      fun i => squeezeScale p.2 * compressReal (p.1 i)) := by
    exact continuous_pi fun i =>
      (continuous_squeezeScale.comp continuous_snd).mul
        (continuous_compressReal.comp ((continuous_apply i).comp continuous_fst))
  exact h_time.prodMk h_state

/-- Every finite state tends to the top pole when its time tends to positive
infinity, using the top embedding in
`Busemann/Frozen/StrongExistence/Definitions/SqueezedStateEmbedding.lean:13-16`
and induced topology in
`Busemann/Frozen/StrongExistence/Definitions/SqueezedStateTopology.lean:10-13`. -/
theorem tendsto_squeezedState_finite_atTop
    {α J : Type*} {l : Filter α} (x : α → J → ℝ) (t : α → ℝ)
    (ht : Tendsto t l atTop) :
    Tendsto (fun a => SqueezedState.finite (x a) (t a))
      l (𝓝 (SqueezedState.top : SqueezedState J)) := by
  -- The induced neighborhood is read through the embedding.
  rw [nhds_induced, tendsto_comap_iff]
  change Tendsto (fun a =>
    (compressReal (t a), fun i => squeezeScale (t a) * compressReal (x a i)))
    l (𝓝 (1, fun _ => (0 : ℝ)))
  -- The time coordinate tends to the top embedding coordinate.
  have h_time := tendsto_compressReal_atTop ht
  -- Each state coordinate vanishes by the uniform compression bound.
  have h_state : Tendsto (fun a i => squeezeScale (t a) * compressReal (x a i))
      l (𝓝 (fun _ => (0 : ℝ))) := by
    apply tendsto_pi_nhds.2
    intro i
    exact tendsto_scaled_compressReal_zero (tendsto_squeezeScale_atTop ht)
      (fun a => squeezeScale_nonneg (t a))
      (fun a => (abs_compressReal_lt_one (x a i)).le)
  exact h_time.prodMk_nhds h_state

/-- Every finite state tends to the bottom pole when its time tends to negative
infinity, using the bottom embedding in
`Busemann/Frozen/StrongExistence/Definitions/SqueezedStateEmbedding.lean:13-15`
and induced topology in
`Busemann/Frozen/StrongExistence/Definitions/SqueezedStateTopology.lean:10-13`. -/
theorem tendsto_squeezedState_finite_atBot
    {α J : Type*} {l : Filter α} (x : α → J → ℝ) (t : α → ℝ)
    (ht : Tendsto t l atBot) :
    Tendsto (fun a => SqueezedState.finite (x a) (t a))
      l (𝓝 (SqueezedState.bottom : SqueezedState J)) := by
  -- The induced neighborhood is read through the embedding.
  rw [nhds_induced, tendsto_comap_iff]
  change Tendsto (fun a =>
    (compressReal (t a), fun i => squeezeScale (t a) * compressReal (x a i)))
    l (𝓝 (-1, fun _ => (0 : ℝ)))
  -- The time coordinate tends to the bottom embedding coordinate.
  have h_time := tendsto_compressReal_atBot ht
  -- Each state coordinate vanishes by the uniform compression bound.
  have h_state : Tendsto (fun a i => squeezeScale (t a) * compressReal (x a i))
      l (𝓝 (fun _ => (0 : ℝ))) := by
    apply tendsto_pi_nhds.2
    intro i
    exact tendsto_scaled_compressReal_zero (tendsto_squeezeScale_atBot ht)
      (fun a => squeezeScale_nonneg (t a))
      (fun a => (abs_compressReal_lt_one (x a i)).le)
  exact h_time.prodMk_nhds h_state

end LPP.Busemann
