/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
public import Busemann.Finite.Locality
public import Busemann.Finite.Measurability
import LPP_Foundations.Probability.EnvironmentLaw

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability

private theorem indep_restrictions {ι : Type*} (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (S : Set ι) :
    IndepFun (fun ω : ι → ℝ => fun x : S => ω x.1)
      (fun ω : ι → ℝ => fun x : (Sᶜ : Set ι) => ω x.1)
      (Measure.infinitePi (fun _ : ι => μ)) := by
  let m : ι → MeasurableSpace (ι → ℝ) :=
    fun i => MeasurableSpace.comap (fun ω => ω i) inferInstance
  have hi : iIndep m (Measure.infinitePi (fun _ : ι => μ)) := by
    apply (iIndepFun_iff_iIndep (fun _ : ι => inferInstance)
      (fun (i : ι) (ω : ι → ℝ) => ω i) _).mp
    exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ι → ℝ)) := by
    intro i
    exact (measurable_pi_apply i).comap_le
  have hg := indep_iSup_of_disjoint hle hi (S := S) (T := Sᶜ) disjoint_compl_right
  have hf : @Measurable (ι → ℝ) (S → ℝ) (⨆ i ∈ S, m i) inferInstance
      (fun ω x => ω x.1) := by
    let : MeasurableSpace (ι → ℝ) := ⨆ i ∈ S, m i
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le x.1 (le_iSup (fun _ : x.1 ∈ S => m x.1) x.2)
  have ht : @Measurable (ι → ℝ) ((Sᶜ : Set ι) → ℝ) (⨆ i ∈ Sᶜ, m i) inferInstance
      (fun ω x => ω x.1) := by
    let : MeasurableSpace (ι → ℝ) := ⨆ i ∈ Sᶜ, m i
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le x.1 (le_iSup (fun _ : x.1 ∈ Sᶜ => m x.1) x.2)
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro a b ha hb
  exact ((Indep_iff _ _ _).mp hg) _ _ (hf ha) (ht hb)

private theorem indep_pair_with_fresh {Ω A B C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) (Q : Measure C) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : Ω → A} {g : Ω → B} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g P) :
    IndepFun (fun p : Ω × C => (f p.1, p.2)) (fun p => g p.1) (P.prod Q) := by
  let a := P.map f
  let b := P.map g
  have hp : MeasurePreserving (fun ω => (f ω, g ω)) P (a.prod b) :=
    ⟨hf.prodMk hg, h.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have hp2 := hp.prod (MeasurePreserving.id Q)
  have hp3 := (measurePreserving_prodAssoc a b Q).comp hp2
  have hp4 := ((MeasurePreserving.id a).prod (Measure.measurePreserving_swap (μ := b) (ν := Q))).comp hp3
  have hp5 := (measurePreserving_prodAssoc a Q b).symm.comp hp4
  have hall : MeasurePreserving (fun p : Ω × C => ((f p.1, p.2), g p.1))
      (P.prod Q) ((a.prod Q).prod b) := by
    exact hp5
  have hfirst : (P.prod Q).map (fun p : Ω × C => (f p.1, p.2)) = a.prod Q := by
    have hh := (measurePreserving_fst (μ := a.prod Q) (ν := b)).comp hall
    simpa only [Function.comp_def] using hh.map_eq
  have hsecond : (P.prod Q).map (fun p : Ω × C => g p.1) = b := by
    have hh := (measurePreserving_snd (μ := a.prod Q) (ν := b)).comp hall
    simpa only [Function.comp_def] using hh.map_eq
  apply (indepFun_iff_map_prod_eq_prod_map_map
    ((hf.comp measurable_fst).prodMk measurable_snd).aemeasurable
    (hg.comp measurable_fst).aemeasurable).mpr
  change (P.prod Q).map (fun p : Ω × C => ((f p.1, p.2), g p.1)) =
    ((P.prod Q).map (fun p : Ω × C => (f p.1, p.2))).prod
      ((P.prod Q).map (fun p : Ω × C => g p.1))
  rw [hfirst, hsecond]
  exact hall.map_eq

namespace LPP.Busemann

/-- The raw future at a shared finite horizon is independent of the strict past; see JR1810.03580v3, Theorem 4.8(b). -/
theorem finiteBusemann_raw_future_indep_past (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℕ → ℝ × ℝ) (n : ℕ) (I : Set Lattice) :
    let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
    let U : Environment × Fin (n + 1) →
        (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
      fun p s => match s with
        | .inl x => p.1 x.1
        | .inr (j, x, i) => finiteBusemannEdge p.1 (h j) x.1 ((p.2.val + 1 : ℕ) : ℤ) i
    let V : Environment × Fin (n + 1) →
        ({x : Lattice // ∀ z ∈ I, ¬ z ≤ x} → ℝ) := fun p x => p.1 x.1
    IndepFun U V (finiteBusemannSharedHorizonLaw μ n) := by
  classical
  let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
  let R : Environment → (J → ℝ) := fun ω x => ω x.1
  let T : Environment → ((Jᶜ : Set Lattice) → ℝ) := fun ω x => ω x.1
  let fill : (J → ℝ) → Environment := fun r x => if hx : x ∈ J then r ⟨x, hx⟩ else 0
  have hR : Measurable R := measurable_pi_iff.mpr fun x => measurable_pi_apply x.1
  have hT : Measurable T := measurable_pi_iff.mpr fun x => measurable_pi_apply x.1
  have hfill : Measurable fill := by
    apply measurable_pi_iff.mpr
    intro x
    by_cases hx : x ∈ J
    · simpa only [fill, dite_eq_left hx] using (measurable_pi_apply (⟨x, hx⟩ : J))
    · simpa only [fill, dite_eq_right hx] using (measurable_const : Measurable (fun _ : J → ℝ => (0 : ℝ)))
  let F : (J → ℝ) × Fin (n + 1) →
      (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
    fun p s => match s with
      | .inl x => fill p.1 x.1
      | .inr (j, x, i) => finiteBusemannEdge (fill p.1) (h j) x.1 ((p.2.val + 1 : ℕ) : ℤ) i
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro s
    cases s with
    | inl x => exact (measurable_pi_apply x.1).comp (hfill.comp measurable_fst)
    | inr q =>
      rcases q with ⟨j, x, i⟩
      apply measurable_from_prod_countable_left
      intro u
      exact (measurable_finiteBusemannEdge (h j) x.1 ((u.val + 1 : ℕ) : ℤ) i).comp hfill
  let G : ((Jᶜ : Set Lattice) → ℝ) → ({x : Lattice // ∀ z ∈ I, ¬ z ≤ x} → ℝ) :=
    fun r x => r ⟨x.1, by simpa [J] using x.2⟩
  have hG : Measurable G := measurable_pi_iff.mpr fun x => measurable_pi_apply _
  have hind := indep_pair_with_fresh (environmentLaw μ) (uniformOriginLaw n) hR hT
    (indep_restrictions μ J)
  have hcomp := hind.comp hF hG
  change IndepFun _ _ ((environmentLaw μ).prod (uniformOriginLaw n))
  convert hcomp using 1
  · funext p s
    cases s with
    | inl x =>
      have hx : x.1 ∈ J := ⟨x.1, x.2, le_rfl⟩
      simp [F, fill, R, hx]
    | inr q =>
      rcases q with ⟨j, x, i⟩
      apply (finiteBusemannEdge_eq_of_eqOn_Ici _ _ _ _ _ _ ?_).symm
      intro y hy
      have hyJ : y ∈ J := by
        obtain ⟨z, hz, hzx⟩ := x.2
        exact ⟨z, hz, le_trans hzx hy⟩
      simp [fill, R, hyJ]
  · rfl

end LPP.Busemann
