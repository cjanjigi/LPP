/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Family
public import Differentiability.FinalDraft.SelectedGridPaths.MeasurableStreams
import LPP_Foundations.Model.Paths.Fintype
import LPP_Foundations.Model.Paths.Translate

/-! # Measurability of the exact selected staircase family -/

public section

open MeasureTheory Set
open scoped Classical

namespace LPPDifferentiability.SelectedGridPaths

open StairGeometry

local notation "Mask" => Lattice → Bool

private theorem measurableSet_mask_exists {ι : Type*} [Countable ι] {p : ι → Mask → Prop}
    (hp : ∀ i, MeasurableSet {b | p i b}) :
    MeasurableSet {b | ∃ i, p i b} := by
  rw [show {b | ∃ i, p i b} = ⋃ i, {b | p i b} by ext b; exact mem_iUnion.symm]
  exact MeasurableSet.iUnion hp

private theorem packedPath_eq_of_stream (y : ℕ → Lattice) (n : ℕ) (q r : PackedPath)
    (hq₀ : q.1 = y 0) (hr₀ : r.1 = y 0)
    (hqn : q.2.1.1 + q.2.1.2 = n) (hrn : r.2.1.1 + r.2.1.2 = n)
    (hq : ∀ i, q.2.2.vertex i = y i.val) (hr : ∀ i, r.2.2.vertex i = y i.val) :
    q = r := by
  rcases q with ⟨u, d, p⟩
  rcases r with ⟨v, e, r⟩
  dsimp only at hq₀ hr₀ hqn hrn hq hr
  subst u
  subst v
  have hp : p.vertex (Fin.last (d.1 + d.2)) = y n := by
    simpa only [Fin.val_last, hqn] using hq (Fin.last (d.1 + d.2))
  have hr' : r.vertex (Fin.last (e.1 + e.2)) = y n := by
    simpa only [Fin.val_last, hrn] using hr (Fin.last (e.1 + e.2))
  have hend : ((d.1 : ℤ), (d.2 : ℤ)) = ((e.1 : ℤ), (e.2 : ℤ)) :=
    add_left_cancel (p.finish.symm.trans (hp.trans (hr'.symm.trans r.finish)))
  have hd₁ : (d.1 : ℤ) = (e.1 : ℤ) := congrArg Prod.fst hend
  have hd₂ : (d.2 : ℤ) = (e.2 : ℤ) := congrArg Prod.snd hend
  have he : d = e := Prod.ext (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
  subst e
  have hp_eq : p = r := Path.ext fun i => (hq i).trans (hr i).symm
  subst r
  rfl

private theorem measurableSet_admissibleIn (Q : Set Lattice)
    (y : Mask → ℕ → Lattice) (hy : ∀ i, Measurable (fun b => y b i)) (n : ℕ) :
    MeasurableSet {b | admissibleIn Q b (y b) n} := by
  have hQ : MeasurableSet Q := (Set.to_countable Q).measurableSet
  have hregion : MeasurableSet {b | ∀ i ≤ n, y b i ∈ Q} :=
    measurableSet_mask_forall fun i => measurableSet_mask_imp (hy i hQ)
  have hgood : MeasurableSet {b : Mask | ∀ i < n, b (y b i) = false} :=
    measurableSet_mask_forall fun i => measurableSet_mask_imp (measurableSet_mask_false_at_site (hy i))
  have hstep (i : ℕ) (v : Lattice) :
      MeasurableSet {b | y b (i + 1) = y b i + v} :=
    measurableSet_eq_fun (hy (i + 1)) ((Measurable.of_discrete (f := fun z : Lattice => z + v)).comp (hy i))
  have hsteps : MeasurableSet {b | ∀ i < n,
      y b (i + 1) = y b i + (1, 0) ∨ y b (i + 1) = y b i + (0, 1)} :=
    measurableSet_mask_forall fun i => measurableSet_mask_imp ((hstep i (1, 0)).union (hstep i (0, 1)))
  exact hsteps.inter (hregion.inter hgood)

private theorem measurableSet_checkedPath_eq_some (Q : Set Lattice)
    (y : Mask → ℕ → Lattice) (hy : ∀ i, Measurable (fun b => y b i)) (n : ℕ) (q : PackedPath) :
    MeasurableSet {b | checkedPath Q b (y b) n = some q} := by
  have hset : {b : Mask | checkedPath Q b (y b) n = some q} =
      {b : Mask | admissibleIn Q b (y b) n ∧ q.1 = y b 0 ∧ q.2.1.1 + q.2.1.2 = n ∧
        ∀ i, q.2.2.vertex i = y b i.val} := by
    ext b
    constructor
    · intro h
      obtain ⟨ha, hz, hn, hv, -⟩ := checkedPath_spec h
      exact ⟨ha, hz, hn, hv⟩
    · rintro ⟨ha, hz, hn, hv⟩
      obtain ⟨r, h⟩ := checkedPath_exists ha
      obtain ⟨-, hrz, hrn, hrv, -⟩ := checkedPath_spec h
      rw [← packedPath_eq_of_stream (y b) n r q hrz hz hrn hn hrv hv]
      exact h
  rw [hset]
  exact (measurableSet_admissibleIn Q y hy n).inter
    ((measurableSet_eq_fun measurable_const (hy 0)).inter
      ((MeasurableSet.const _).inter (measurableSet_mask_forall fun i =>
        measurableSet_eq_fun measurable_const (hy i.val))))

private theorem measurableSet_fineChoice_eq_some (Q : Set Lattice)
    (a : ℝ) (u : Lattice) (I : ℤ) (l : ℕ) (q : PackedPath) :
    MeasurableSet {b : Mask | fineChoice Q b a u I l = some q} := by
  rw [show {b : Mask | fineChoice Q b a u I l = some q} =
      {b : Mask | gammaDefined Q b a u I ∧ gammaDefined Q b a u (I + (l : ℤ))} ∩
        {b : Mask | checkedPath Q b (gammaStream b a u I) l = some q} by
    ext b
    unfold fineChoice
    by_cases hb : gammaDefined Q b a u I ∧ gammaDefined Q b a u (I + (l : ℤ)) <;> simp [hb]]
  exact ((measurableSet_gammaDefined Q a u I).inter
    (measurableSet_gammaDefined Q a u (I + (l : ℤ)))).inter
    (measurableSet_checkedPath_eq_some Q (fun b => gammaStream b a u I)
      (measurable_gammaStream a u I) l q)

private theorem measurableSet_arrivalChoice_eq_some (Q : Set Lattice)
    (a : ℝ) (L : ℕ) (u v : Lattice) (I : ℤ) (q : PackedPath) :
    MeasurableSet {b : Mask | arrivalChoice Q b a L u v I = some q} := by
  let n := (lev v - I).toNat
  let y (b : Mask) := arrivalStream b L (gammaPoint b a u I) v
  have hy (s : ℕ) : Measurable (fun b : Mask => y b s) :=
    measurable_arrivalStream_at (measurable_gammaPoint a u I) L v s
  let ready (b : Mask) := gammaDefined Q b a u I ∧
    gammaPoint b a u I ∉ forwardTrapped (maskEnvironment b) 0 ∧
    boxFree (maskEnvironment b) 0 L v ∧ L ≤ n ∧ y b n = v
  have hstart := measurableSet_not_trapped_at_site (measurable_gammaPoint a u I)
  have hlength : MeasurableSet {b : Mask | L ≤ n} := MeasurableSet.const _
  have hend := measurableSet_eq_fun (hy n) (measurable_const (a := v))
  have hcompletion : MeasurableSet {b : Mask | boxFree (maskEnvironment b) 0 L v ∧
      L ≤ n ∧ y b n = v} :=
    (measurableSet_mask_boxFree L v).inter (hlength.inter hend)
  have hready : MeasurableSet {b : Mask | ready b} :=
    (measurableSet_gammaDefined Q a u I).inter (hstart.inter hcompletion)
  rw [show {b : Mask | arrivalChoice Q b a L u v I = some q} =
      {b : Mask | ready b} ∩ {b : Mask | checkedPath Q b (y b) n = some q} by
    ext b
    change (if ready b then checkedPath Q b (y b) n else none) = some q ↔
      ready b ∧ checkedPath Q b (y b) n = some q
    by_cases hb : ready b <;> simp [hb]]
  exact hready.inter (measurableSet_checkedPath_eq_some Q y hy n q)

private theorem measurableSet_mergeChoices_mem (Q : Set Lattice)
    (a : ℝ) (Δ₀ : ℕ) (u v : Lattice) (I Λ : ℤ) (q : PackedPath) :
    MeasurableSet {b : Mask | q ∈ mergeChoices Q b a Δ₀ u v I Λ} := by
  let ready (b : Mask) := gammaDefined Q b a u I ∧
    gammaPoint b a u I ∉ forwardTrapped (maskEnvironment b) 0 ∧
    v ∉ forwardTrapped (maskEnvironment b) 0
  let mergePrefix (b : Mask) (i : ℕ) := checkedPath Q b (mergeStream b a Δ₀ u v Λ) i
  let suffix (b : Mask) (i : ℕ) :=
    checkedPath Q b (gammaStream b a u (lev v + (i : ℤ))) ((Λ - lev v).toNat - i)
  have hready : MeasurableSet {b | ready b} :=
    (measurableSet_gammaDefined Q a u I).inter
      ((measurableSet_not_trapped_at_site (measurable_gammaPoint a u I)).inter
        (measurableSet_not_trapped_at_site (measurable_const (a := v))))
  have hprefix (i : ℕ) (r : PackedPath) : MeasurableSet {b | mergePrefix b i = some r} :=
    measurableSet_checkedPath_eq_some Q _ (measurable_mergeStream a Δ₀ u v Λ) i r
  have hsuffix (i : ℕ) : MeasurableSet {b | suffix b i = some q} :=
    measurableSet_checkedPath_eq_some Q _ (measurable_gammaStream a u (lev v + (i : ℤ))) _ q
  have heq : {b : Mask | q ∈ mergeChoices Q b a Δ₀ u v I Λ} =
      {b : Mask | ready b ∧ ∃ i, firstMeeting Q b a Δ₀ u v Λ = some i ∧
        ∃ r, mergePrefix b i = some r ∧
          (q = r ∨ gammaDefined Q b a u Λ ∧ suffix b i = some q)} := by
    ext b
    change q ∈ (if ready b then
      match firstMeeting Q b a Δ₀ u v Λ with
      | none => ∅
      | some i => match mergePrefix b i with
        | none => ∅
        | some r => insert r (if gammaDefined Q b a u Λ then (suffix b i).toFinset else ∅)
      else ∅) ↔ _
    by_cases hb : ready b
    · rw [ite_eq_left hb]
      cases hmeet : firstMeeting Q b a Δ₀ u v Λ with
      | none => simp [hb, hmeet]
      | some i =>
        cases hprefix' : mergePrefix b i with
        | none => simp [hb, hmeet, hprefix']
        | some r =>
          simp only [mem_ofPred_eq, hmeet, hprefix']
          change q ∈ insert r (if gammaDefined Q b a u Λ then (suffix b i).toFinset else ∅) ↔
            ready b ∧ ∃ j, some i = some j ∧ ∃ p, mergePrefix b j = some p ∧
              (q = p ∨ gammaDefined Q b a u Λ ∧ suffix b j = some q)
          have hmem : q ∈ insert r (if gammaDefined Q b a u Λ then (suffix b i).toFinset else ∅) ↔
              q = r ∨ gammaDefined Q b a u Λ ∧ suffix b i = some q := by
            by_cases hend : gammaDefined Q b a u Λ <;> simp [hend, Option.mem_toFinset]
          rw [hmem]
          constructor
          · intro h
            exact ⟨hb, i, rfl, r, hprefix', h⟩
          · rintro ⟨-, j, hj, p, hp, h⟩
            have hij : i = j := Option.some.inj hj
            subst j
            rw [hprefix'] at hp
            have hrp : r = p := Option.some.inj hp
            subst p
            exact h
    · rw [ite_eq_right hb]
      simp [hb]
  rw [heq]
  exact hready.inter (measurableSet_mask_exists fun i =>
    (measurableSet_firstMeeting_eq_some Q a Δ₀ u v Λ i).inter
      (measurableSet_mask_exists fun r => (hprefix i r).inter
        ((MeasurableSet.const (q = r)).union ((measurableSet_gammaDefined Q a u Λ).inter (hsuffix i)))))

private theorem measurableSet_mem_biUnion {ι : Type*} (labels : Finset ι)
    {paths : ι → Mask → Finset PackedPath} (q : PackedPath)
    (h : ∀ i ∈ labels, MeasurableSet {b | q ∈ paths i b}) :
    MeasurableSet {b | q ∈ labels.biUnion fun i => paths i b} := by
  rw [show {b | q ∈ labels.biUnion fun i => paths i b} =
      ⋃ i : labels, {b | q ∈ paths i.val b} by
    ext b
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_biUnion, Subtype.exists, exists_prop]]
  exact MeasurableSet.iUnion fun i => h i.val i.property

private theorem measurableSet_mem_path_union {F G : Mask → Finset PackedPath}
    (q : PackedPath) (hF : MeasurableSet {b | q ∈ F b}) (hG : MeasurableSet {b | q ∈ G b}) :
    MeasurableSet {b | q ∈ F b ∪ G b} := by
  rw [show {b | q ∈ F b ∪ G b} = {b | q ∈ F b} ∪ {b | q ∈ G b} by
    ext b
    simp only [mem_ofPred_eq, Finset.mem_union, mem_union]]
  exact hF.union hG

private theorem measurableSet_mem_pathFamily (a cstar A R C₁ : ℝ)
    (m : ℕ → ℕ) (k K₁ K₃ : ℕ) (q : PackedPath) :
    MeasurableSet {b : Mask | q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b} := by
  unfold pathFamily
  dsimp only
  refine measurableSet_mem_biUnion _ q fun u _ => ?_
  refine measurableSet_mem_biUnion _ q fun j _ => ?_
  refine measurableSet_mem_biUnion _ q fun I _ => ?_
  by_cases hf : (mesh (m k) j : ℝ) < 8 * (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ)))
  · simp only [ite_eq_left hf, Option.mem_toFinset, Option.mem_def]
    exact measurableSet_fineChoice_eq_some _ a u I _ q
  · simp only [ite_eq_right hf]
    refine measurableSet_mem_biUnion _ q fun h _ => ?_
    refine measurableSet_mem_biUnion _ q fun ν _ => ?_
    apply measurableSet_mem_path_union
    · refine measurableSet_mem_biUnion _ q fun v _ => ?_
      simpa only [Option.mem_toFinset, Option.mem_def] using
        measurableSet_arrivalChoice_eq_some (workingRegion a A R C₁ m k) a
          (arrivalBoxSize (slopeCutoff a) K₁ K₃) u v I q
    · refine measurableSet_mem_biUnion _ q fun v _ => ?_
      exact measurableSet_mergeChoices_mem _ a (deviationBound K₁ K₃) u v I
        (I + (mesh (m k) j : ℤ)) q

/-- Every fibre of the actual selected staircase family is measurable in the
very-bad mask, at every scale (final draft, Appendix B item `ch:family`). -/
theorem measurableSet_pathFamily_fibre (a cstar A R C₁ : ℝ)
    (m : ℕ → ℕ) (k K₁ K₃ : ℕ) (F : Finset PackedPath) :
    MeasurableSet {b : Lattice → Bool | pathFamily a cstar A R C₁ m k K₁ K₃ b = F} := by
  have heq : {b : Mask | pathFamily a cstar A R C₁ m k K₁ K₃ b = F} =
      {b : Mask | ∀ q : PackedPath, q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b ↔ q ∈ F} := by
    ext b
    exact Finset.ext_iff
  rw [heq]
  apply measurableSet_mask_forall
  intro q
  have hq := measurableSet_mem_pathFamily a cstar A R C₁ m k K₁ K₃ q
  by_cases h : q ∈ F
  · simpa only [h, iff_true] using hq
  · simp only [h, iff_false]
    rw [show {b : Mask | q ∉ pathFamily a cstar A R C₁ m k K₁ K₃ b} =
        {b : Mask | q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b}ᶜ by
      ext b
      simp only [mem_ofPred_eq, mem_compl_iff]]
    exact hq.compl

end LPPDifferentiability.SelectedGridPaths
