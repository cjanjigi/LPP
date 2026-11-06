/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.EnvironmentFiniteMaskWeights

/-! # Weights of path families that depend on the whole very-bad mask

The finite-mask weight theorems treat families that are functions of the very-bad
mask on a finite region `Q`. Here the family may depend on the whole mask, subject
to measurability. The only restriction on where paths live is that every collected
site is in a fixed finite region `Q`.

The extra step beyond the finite-mask case is a Fubini transfer: split the
environment into the part on `Q` and the part off `Q`, which are independent, fix
the part off `Q`, apply the finite theorem to the resulting function of the
`Q`-mask, and integrate over the part off `Q`. The measurability hypothesis says
that the family is measurable for the product sigma-algebra on global masks.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- Combine a configuration on `Q` with one off `Q`. -/
private noncomputable def glue {α : Type*} (Q : Finset Lattice) (x : Q → α)
    (y : {z : Lattice // z ∉ Q} → α) (z : Lattice) : α :=
  if h : z ∈ Q then x ⟨z, h⟩ else y ⟨z, h⟩

private theorem glue_of_mem {α : Type*} (Q : Finset Lattice) (x : Q → α)
    (y : {z : Lattice // z ∉ Q} → α) {z : Lattice} (h : z ∈ Q) :
    glue Q x y z = x ⟨z, h⟩ := dite_eq_left h

private theorem glue_of_not_mem {α : Type*} (Q : Finset Lattice) (x : Q → α)
    (y : {z : Lattice // z ∉ Q} → α) {z : Lattice} (h : z ∉ Q) :
    glue Q x y z = y ⟨z, h⟩ := dite_eq_right h

/-- The environment restricted to `Q`. -/
private abbrev regionPart (Q : Finset Lattice) (ω : Environment) : Q → ℝ :=
  fun z => ω z.1

/-- The environment restricted off `Q`. -/
private abbrev outsidePart (Q : Finset Lattice) (ω : Environment) :
    {z : Lattice // z ∉ Q} → ℝ := fun z => ω z.1

private theorem glue_restrict (Q : Finset Lattice) (ω : Environment) :
    glue Q (regionPart Q ω) (outsidePart Q ω) = ω := by
  funext z
  by_cases h : z ∈ Q
  · rw [glue_of_mem Q _ _ h]
  · rw [glue_of_not_mem Q _ _ h]

private theorem measurable_glue {α : Type*} [MeasurableSpace α] (Q : Finset Lattice) :
    Measurable (fun p : (Q → α) × ({z : Lattice // z ∉ Q} → α) => glue Q p.1 p.2) := by
  refine measurable_pi_iff.mpr fun z => ?_
  by_cases h : z ∈ Q
  · have e : (fun p : (Q → α) × ({z : Lattice // z ∉ Q} → α) => glue Q p.1 p.2 z) =
        fun p => p.1 ⟨z, h⟩ := funext fun p => glue_of_mem Q p.1 p.2 h
    change Measurable (fun p : (Q → α) × ({z : Lattice // z ∉ Q} → α) => glue Q p.1 p.2 z)
    rw [e]
    exact (measurable_pi_apply _).comp measurable_fst
  · have e : (fun p : (Q → α) × ({z : Lattice // z ∉ Q} → α) => glue Q p.1 p.2 z) =
        fun p => p.2 ⟨z, h⟩ := funext fun p => glue_of_not_mem Q p.1 p.2 h
    change Measurable (fun p : (Q → α) × ({z : Lattice // z ∉ Q} → α) => glue Q p.1 p.2 z)
    rw [e]
    exact (measurable_pi_apply _).comp measurable_snd

/-- Sites of a finite set inside `Q`, enumerated by `Fin`, are summed over the set. -/
private theorem sum_equivFin_eq_sum_glue (Q : Finset Lattice) (s : Finset Lattice) (hs : s ⊆ Q)
    (x : Q → ℝ) (u : {z : Lattice // z ∉ Q} → ℝ) :
    ∑ k : Fin s.card, x ⟨(s.equivFin.symm k).1, hs (s.equivFin.symm k).2⟩ =
      ∑ z ∈ s, glue Q x u z := by
  calc ∑ k : Fin s.card, x ⟨(s.equivFin.symm k).1, hs (s.equivFin.symm k).2⟩
      = ∑ k : Fin s.card, glue Q x u (s.equivFin.symm k).1 :=
        Finset.sum_congr rfl fun k _ => (glue_of_mem Q x u (hs (s.equivFin.symm k).2)).symm
    _ = ∑ w : s, glue Q x u w.1 :=
        Fintype.sum_equiv s.equivFin.symm _ _ fun k => rfl
    _ = ∑ z ∈ s, glue Q x u z := Finset.sum_coe_sort s (fun z => glue Q x u z)

/-- Fubini transfer: the part of the environment on `Q` is independent of the part off `Q` and
has the product law, so a bound on every section bounds the whole event. -/
private theorem environmentLaw_real_le_of_sections
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : Finset Lattice) (E : Set Environment)
    (hE : MeasurableSet E) (B : ℝ)
    (hsec : ∀ y : {z : Lattice // z ∉ Q} → ℝ,
      (Measure.pi (fun _ : Q => μ)).real {x : Q → ℝ | glue Q x y ∈ E} ≤ B) :
    (environmentLaw μ).real E ≤ B := by
  classical
  have hB : 0 ≤ B := le_trans measureReal_nonneg (hsec fun _ => 0)
  have hXm : Measurable (regionPart Q) := measurable_finite_environment_coordinates Subtype.val
  have hYm : Measurable (outsidePart Q) := measurable_finite_environment_coordinates Subtype.val
  let m : Lattice → MeasurableSpace Environment :=
    fun z => MeasurableSpace.comap (fun ω : Environment => ω z) inferInstance
  have hI : iIndep m (environmentLaw μ) := (iIndepFun_environment_eval μ).iIndep
  have hle : ∀ z, m z ≤ (inferInstance : MeasurableSpace Environment) :=
    fun z => (measurable_environment_eval z).comap_le
  have hsup := indep_iSup_of_disjoint hle hI
    (S := (↑Q : Set Lattice)) (T := (↑Q : Set Lattice)ᶜ) disjoint_compl_right
  have hind : IndepFun (regionPart Q) (outsidePart Q) (environmentLaw μ) := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hsup ?_) ?_
    · rw [MeasurableSpace.comap_le_iff_le_map]
      refine iSup_le fun z => ?_
      rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun (w : Lattice) (_ : w ∈ (↑Q : Set Lattice)) => m w) z.1
        (Finset.mem_coe.mpr z.2)
    · rw [MeasurableSpace.comap_le_iff_le_map]
      refine iSup_le fun z => ?_
      rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun (w : Lattice) (_ : w ∈ (↑Q : Set Lattice)ᶜ) => m w) z.1
        (by simp)
  have hX : (environmentLaw μ).map (regionPart Q) = Measure.pi (fun _ : Q => μ) :=
    environmentLaw_map_finite_coordinates μ Subtype.val Subtype.val_injective
  have hsplit : (environmentLaw μ).map (fun ω => (regionPart Q ω, outsidePart Q ω)) =
      (Measure.pi (fun _ : Q => μ)).prod ((environmentLaw μ).map (outsidePart Q)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).mp hind, hX]
  let E' : Set ((Q → ℝ) × ({z : Lattice // z ∉ Q} → ℝ)) := {p | glue Q p.1 p.2 ∈ E}
  have hE' : MeasurableSet E' := (measurable_glue Q) hE
  have hpre : E = (fun ω => (regionPart Q ω, outsidePart Q ω)) ⁻¹' E' := by
    ext ω
    change ω ∈ E ↔ glue Q (regionPart Q ω) (outsidePart Q ω) ∈ E
    rw [glue_restrict Q ω]
  have hPE : environmentLaw μ E =
      ((Measure.pi (fun _ : Q => μ)).prod ((environmentLaw μ).map (outsidePart Q))) E' := by
    rw [← hsplit, Measure.map_apply (hXm.prodMk hYm) hE', ← hpre]
  have hbound : ((Measure.pi (fun _ : Q => μ)).prod
      ((environmentLaw μ).map (outsidePart Q))) E' ≤ ENNReal.ofReal B := by
    rw [Measure.prod_apply_symm hE']
    calc ∫⁻ y, (Measure.pi (fun _ : Q => μ)) ((fun x => (x, y)) ⁻¹' E')
          ∂((environmentLaw μ).map (outsidePart Q))
        ≤ ∫⁻ _y, ENNReal.ofReal B ∂((environmentLaw μ).map (outsidePart Q)) :=
          lintegral_mono fun y =>
            (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).2 (hsec y)
      _ = ENNReal.ofReal B := by simp
  rw [measureReal_def, hPE]
  exact ENNReal.toReal_le_of_le_ofReal hB hbound

/-- The global-mask form of the weights lemma, for families given by their collected sites.
Every member collects only sites of the finite region `Q`, no very bad site, and at most `n`
sites. The family may depend on the entire mask, subject to measurability for the product
sigma-algebra on masks. The bound is the right-hand side of the finite-mask theorem. -/
theorem global_mask_family_weight_failure_le
    {J : Type*} [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (Q : Finset Lattice) (n N K : ℕ) (hK : 1 ≤ K) (hJ : Fintype.card J ≤ N)
    (active : (Lattice → Bool) → J → Bool)
    (sites : (Lattice → Bool) → J → Finset Lattice)
    (hlen : ∀ a j, active a j = true → (sites a j).card ≤ n)
    (hmem : ∀ a j, active a j = true → sites a j ⊆ Q)
    (hgood : ∀ a j, active a j = true → ∀ z ∈ sites a j, a z = false)
    (hmeas : ∀ (j : J) (s : Finset Lattice),
      MeasurableSet {a : Lattice → Bool | active a j = true ∧ sites a j = s}) :
    let mask := fun ω : Environment => fun z : Lattice => if ω z < -T then true else false
    let E := {ω : Environment | ∃ j : J, active (mask ω) j = true ∧
      ∑ z ∈ sites (mask ω) j, ω z <
        -2 * (∫ y, max (-y) 0 ∂μ) * (sites (mask ω) j).card - (K - 1 : ℕ) * T - t}
    MeasurableSet E ∧ (environmentLaw μ).real E ≤
      N * ((2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3)))) := by
  classical
  intro mask E
  have hmask : Measurable mask :=
    measurable_pi_iff.mpr fun z => Measurable.ite
      (measurableSet_lt (measurable_pi_apply z) measurable_const)
      measurable_const measurable_const
  have hE : E = ⋃ j : J, ⋃ s ∈ Q.powerset,
      (mask ⁻¹' {a : Lattice → Bool | active a j = true ∧ sites a j = s}) ∩
        {ω : Environment | ∑ z ∈ s, ω z <
          -2 * (∫ y, max (-y) 0 ∂μ) * s.card - (K - 1 : ℕ) * T - t} := by
    ext ω
    constructor
    · rintro ⟨j, hact, hlt⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨sites (mask ω) j,
        Finset.mem_powerset.2 (hmem _ _ hact), ⟨⟨hact, rfl⟩, hlt⟩⟩⟩
    · intro h
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
      obtain ⟨s, _, ⟨hact, hs⟩, hlt⟩ := Set.mem_iUnion₂.1 hj
      subst hs
      exact ⟨j, hact, hlt⟩
  have hEm : MeasurableSet E := by
    rw [hE]
    refine MeasurableSet.iUnion fun j => Finset.measurableSet_biUnion _ fun s _ => ?_
    exact (hmask (hmeas j s)).inter
      (measurableSet_lt (Finset.measurable_sum _ fun z _ => measurable_pi_apply z)
        measurable_const)
  refine ⟨hEm, ?_⟩
  refine environmentLaw_real_le_of_sections μ Q E hEm _ fun u => ?_
  obtain ⟨bb, hbb⟩ : ∃ bb : {z : Lattice // z ∉ Q} → Bool,
      ∀ w, bb w = if u w < -T then true else false := ⟨fun w => _, fun w => rfl⟩
  let A : (Q → ℝ) → (Lattice → Bool) := fun x =>
    glue Q (fun z : Q => if x z < -T then true else false) bb
  have hm (x : Q → ℝ) : mask (glue Q x u) = A x := by
    funext z
    by_cases hz : z ∈ Q
    · show (if glue Q x u z < -T then true else false) = glue Q _ bb z
      rw [glue_of_mem Q x u hz, glue_of_mem Q _ bb hz]
    · show (if glue Q x u z < -T then true else false) = glue Q _ bb z
      rw [glue_of_not_mem Q x u hz, glue_of_not_mem Q _ bb hz, hbb]
  have hfinite := finite_mask_family_weight_failure_le μ T p b t hp hT hthreshold hb ht hmoment
    n N K hK hJ (fun a j => active (glue Q a bb) j)
    (fun a j => (sites (glue Q a bb) j).card)
    (fun a j h k => ⟨((sites (glue Q a bb) j).equivFin.symm k).1,
      hmem _ _ h ((sites (glue Q a bb) j).equivFin.symm k).2⟩)
    (fun a j h => hlen _ _ h)
    (fun a j h k k' hkk =>
      (sites (glue Q a bb) j).equivFin.symm.injective (Subtype.ext (by have h2 := congrArg Subtype.val hkk; exact h2)))
    (fun a j h k => by
      have hz := hgood (glue Q a bb) j h _ ((sites (glue Q a bb) j).equivFin.symm k).2
      rwa [glue_of_mem Q a bb (hmem _ _ h ((sites (glue Q a bb) j).equivFin.symm k).2)] at hz)
  have hfin : (Measure.pi fun _ : Q => μ).real {x : Q → ℝ | ∃ j : J,
      if h : active (A x) j = true then
        ∑ k, x ⟨((sites (A x) j).equivFin.symm k).1,
          hmem _ _ h ((sites (A x) j).equivFin.symm k).2⟩ <
          -2 * (∫ y, max (-y) 0 ∂μ) * ((sites (A x) j).card : ℝ) - (K - 1 : ℕ) * T - t
      else False} ≤ _ := hfinite.2
  have hS : {x : Q → ℝ | glue Q x u ∈ E} = {x : Q → ℝ | ∃ j : J,
      if h : active (A x) j = true then
        ∑ k, x ⟨((sites (A x) j).equivFin.symm k).1,
          hmem _ _ h ((sites (A x) j).equivFin.symm k).2⟩ <
          -2 * (∫ y, max (-y) 0 ∂μ) * ((sites (A x) j).card : ℝ) - (K - 1 : ℕ) * T - t
      else False} := by
    ext x
    simp only [E, Set.mem_ofPred_eq]
    rw [hm x]
    refine exists_congr fun j => ?_
    by_cases h : active (A x) j = true
    · rw [dite_eq_left h, and_iff_right h, sum_equivFin_eq_sum_glue Q _ (hmem _ _ h) x u]
    · rw [dite_eq_right h]
      simp [h]
  rw [hS]
  exact hfin

/-- The global-mask form of the weights lemma for path weights. The path family
`q a j` may depend on the entire mask `a`; all collected vertices lie in `Q`, none is very bad,
and the measurability hypothesis is on the finite sets of collected vertices. -/
theorem global_mask_path_weight_failure_le
    {J : Type*} [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (Q : Finset Lattice) (n N K : ℕ) (hK : 1 ≤ K) (hJ : Fintype.card J ≤ N)
    (active : (Lattice → Bool) → J → Bool)
    (starts : (Lattice → Bool) → J → Lattice) (disps : (Lattice → Bool) → J → ℕ × ℕ)
    (q : (a : Lattice → Bool) → (j : J) → Path (starts a j) (disps a j))
    (hlen : ∀ a j, active a j = true → (disps a j).1 + (disps a j).2 ≤ n)
    (hmem : ∀ a j, active a j = true → ∀ i : Fin ((disps a j).1 + (disps a j).2),
      (q a j).vertex i.castSucc ∈ Q)
    (hgood : ∀ a j, active a j = true → ∀ i : Fin ((disps a j).1 + (disps a j).2),
      a ((q a j).vertex i.castSucc) = false)
    (hmeas : ∀ (j : J) (s : Finset Lattice), MeasurableSet {a : Lattice → Bool |
      active a j = true ∧ Finset.univ.image
        (fun i : Fin ((disps a j).1 + (disps a j).2) => (q a j).vertex i.castSucc) = s}) :
    let mask := fun ω : Environment => fun z : Lattice => if ω z < -T then true else false
    let E := {ω : Environment | ∃ j : J, active (mask ω) j = true ∧
      pathWeight ω (q (mask ω) j) <
        -2 * (∫ y, max (-y) 0 ∂μ) * ((disps (mask ω) j).1 + (disps (mask ω) j).2) -
          (K - 1 : ℕ) * T - t}
    MeasurableSet E ∧ (environmentLaw μ).real E ≤
      N * ((2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3)))) := by
  classical
  intro mask E
  have hinj (a : Lattice → Bool) (j : J) : Function.Injective
      (fun i : Fin ((disps a j).1 + (disps a j).2) => (q a j).vertex i.castSucc) :=
    fun i i' h => Fin.castSucc_injective _ ((q a j).vertex_injective h)
  have hcard (a : Lattice → Bool) (j : J) : (Finset.univ.image
      (fun i : Fin ((disps a j).1 + (disps a j).2) => (q a j).vertex i.castSucc)).card =
        (disps a j).1 + (disps a j).2 := by
    rw [Finset.card_image_of_injective _ (hinj a j), Finset.card_univ, Fintype.card_fin]
  have hsum (ω : Environment) (a : Lattice → Bool) (j : J) : pathWeight ω (q a j) =
      ∑ z ∈ Finset.univ.image
        (fun i : Fin ((disps a j).1 + (disps a j).2) => (q a j).vertex i.castSucc), ω z :=
    (Finset.sum_image (hinj a j).injOn).symm
  have hcore := global_mask_family_weight_failure_le μ T p b t hp hT hthreshold hb ht hmoment
    Q n N K hK hJ active
    (fun a j => Finset.univ.image
      (fun i : Fin ((disps a j).1 + (disps a j).2) => (q a j).vertex i.castSucc))
    (fun a j h => (hcard a j).le.trans (hlen a j h))
    (fun a j h z hz => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
      exact hmem a j h i)
    (fun a j h z hz => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
      exact hgood a j h i)
    hmeas
  have heq : E = {ω : Environment | ∃ j : J, active (mask ω) j = true ∧
      ∑ z ∈ Finset.univ.image (fun i : Fin ((disps (mask ω) j).1 + (disps (mask ω) j).2) =>
        (q (mask ω) j).vertex i.castSucc), ω z <
        -2 * (∫ y, max (-y) 0 ∂μ) * (Finset.univ.image
          (fun i : Fin ((disps (mask ω) j).1 + (disps (mask ω) j).2) =>
            (q (mask ω) j).vertex i.castSucc)).card - (K - 1 : ℕ) * T - t} := by
    ext ω
    simp only [E, Set.mem_ofPred_eq]
    refine exists_congr fun j => and_congr_right fun _ => ?_
    rw [hcard, Nat.cast_add, hsum ω (mask ω) j]
  rw [heq]
  exact hcore

end LPPDifferentiability
