/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Coarse.Arrival
public import Differentiability.FinalDraft.SelectedGridPaths.Coarse.Merge
public import Differentiability.Model.Paths.GridConnectionsGeneral
import all Differentiability.FinalDraft.SelectedGridPaths.Fine
import Differentiability.Model.Paths.GridCoarseGeneralAssembly
import Differentiability.Analysis.GridScaleCounts
import Mathlib.Tactic

/-! The source coarse grid connection from a fixed capped crossing and the three
selected staircase paths. This is the coarse case of `rk:grid-general`. -/

public section

namespace LPPDifferentiability.SelectedGridPaths.CoarseBlock
open StairGeometry Set

/-- The coarse connection of the final draft, with the actual window, actual
trial, and the weight bound for the finite family `P_k`. -/
theorem coarse_gridConnection
    {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ : ℕ} {u : Lattice}
    (C : CoarseBlock a cstar A R C₁ m k u) (ω : Environment)
    (T t G dl dr K Cm : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hjk : C.j ≤ k) (ht : 0 ≤ t) (hcs : cstar = 50 / min a (1 - a))
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (hCm : 0 ≤ Cm) (hGC : 0 ≤ G + 2 * Cm)
    (huR : |transverse a u| ≤ R * (2 : ℝ) ^ k)
    (htrial : ω ∈ C.cappedTrial G K)
    (hweight : ∀ q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ (siteMask ω T),
      -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - t / 2 ≤ pathWeight ω q.2.2) :
    let Q := workingRegion a A R C₁ m k
    let θ := slopeCutoff a
    let Δ := deviationBound K₁ K₃
    let L := arrivalBoxSize θ K₁ K₃
    let r := trimLength θ K₁ K₃
    let b := siteMask ω T
    8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (r : ℝ) + 3 * cstar + 1 ≤ C₁ →
    4 * ((Δ : ℝ) + (r : ℝ) + (L : ℝ)) ≤ (C.w : ℝ) →
    2 * (Δ : ℝ) * K + 4 * (r : ℝ) * Cm ≤ (C.w : ℝ) →
    ω ∈ goodEvent θ K₁ K₃ T Q → gammaDefined Q b a u C.I →
    gammaDefined Q b a u C.upperLevel →
    GridConnection ω a G dl dr (C₁ * C.scaleFactor + 2 * t) (C₁ * C.scaleFactor) u
      (gammaPoint b a u C.I) (gammaPoint b a u C.upperLevel) := by
  intro Q θ Δ L r b hC₁ hW4 hWK hE hγ hγend
  let l := C.ell
  let w := C.w
  let P := C.scaleFactor
  let m' := C.inset
  let ρ := transverse a u
  let g := gammaStream b a u C.I
  let B := cstar * P
  change 4 * ((Δ : ℝ) + (r : ℝ) + (L : ℝ)) ≤ (w : ℝ) at hW4
  change 2 * (Δ : ℝ) * K + 4 * (r : ℝ) * Cm ≤ (w : ℝ) at hWK
  have hupper : C.upperLevel = C.I + (l : ℤ) := rfl
  have hj := (Finset.mem_Icc.mp C.scale_mem).1
  obtain ⟨hθ, hθ', _, _, hcθ, hc100⟩ := coarse_direction_facts a cstar θ rfl ha₀ ha₁ hcs
  have hK0 : 0 ≤ K := (abs_nonneg dl).trans hdl
  have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr1 : (1 : ℝ) ≤ r := by
    change (1 : ℝ) ≤ ((K₁ * (2 * L + 1) + componentSize K₁ K₃ : ℕ) : ℝ)
    have hrN := Nat.mul_le_mul hK₁ (show 1 ≤ 2 * L + 1 by omega)
    exact_mod_cast (show 1 ≤ K₁ * (2 * L + 1) + componentSize K₁ K₃ by omega)
  have hwbig : 4 * (Δ : ℝ) + 4 ≤ w := by linarith only [hW4, hr1, hL0]
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hP0 : 0 ≤ P := by dsimp [P, CoarseBlock.scaleFactor]; positivity
  have hPw : (w : ℝ) ≤ P := le_mul_of_one_le_left hw0 (one_le_pow₀ (by exact_mod_cast hj))
  have hcP : 100 * P ≤ cstar * P := mul_le_mul_of_nonneg_right hc100 hP0
  have hlR : 8 * (cstar * P) ≤ (l : ℝ) := C.coarse
  have hm₁ : cstar * P ≤ m' := Nat.le_ceil _
  have hm₂ : (m' : ℝ) < cstar * P + 1 := Nat.ceil_lt_add_one (mul_nonneg (by linarith) hP0)
  have hml : 2 * m' + 2 * r + 2 ≤ l := by
    have h : ((2 * m' + 2 * r + 2 : ℕ) : ℝ) ≤ (l : ℝ) := by
      push_cast
      linarith only [hm₂, hlR, hW4, hwbig, hPw, hcP, hΔ0, hr0, hL0, hP0]
    exact_mod_cast h
  have hLm : L ≤ m' := by
    have h : (L : ℝ) ≤ m' := by linarith only [hW4, hΔ0, hr0, hPw, hcP, hm₁, hP0]
    exact_mod_cast h
  have hmpos : 1 ≤ m' := by
    have h : (1 : ℝ) ≤ m' := by linarith only [hm₁, hcP, hPw, hwbig, hΔ0, hP0]
    exact_mod_cast h
  have hcG : 0 ≤ cstar * (G + 2 * Cm) := mul_nonneg (by linarith) hGC
  have hcC : cstar ≤ C₁ := by linarith only [hC₁, hcG, hK0, hr0, hc100]
  have hPbound : P ≤ 2 * (2 : ℝ) ^ k := coarse_pow_bound C.j k hjk
  have hlbound : (l : ℝ) ≤ (2 : ℝ) ^ m k := by exact_mod_cast grid_mesh_le (m k) C.j
  have h2m : 0 ≤ (2 : ℝ) ^ m k := by positivity
  have h2k : 0 ≤ (2 : ℝ) ^ k := by positivity
  obtain ⟨hI₁, hI₂⟩ := abs_le.mp (mem_gridLevels.mp C.level_mem).2
  obtain ⟨hu₁, hu₂⟩ := abs_le.mp huR
  have hQ (y : Lattice) (hy₁ : C.I ≤ lev y) (hy₂ : lev y ≤ C.upperLevel)
      (hy : |transverse a y - ρ| ≤ B) : y ∈ Q := by
    have hcast₁ : (C.I : ℝ) ≤ (lev y : ℝ) := by exact_mod_cast hy₁
    have hcast₂ : (lev y : ℝ) ≤ (C.I : ℝ) + (l : ℝ) := by
      rw [hupper] at hy₂
      exact_mod_cast hy₂
    have hB := mul_le_mul_of_nonneg_left hPbound (by linarith only [hc100] : 0 ≤ cstar)
    have hC := mul_le_mul_of_nonneg_right hcC h2k
    change |transverse a y - transverse a u| ≤ cstar * P at hy
    obtain ⟨h₁, h₂⟩ := abs_le.mp hy
    change |(lev y : ℝ)| ≤ (A + 5) * 2 ^ m k ∧ |transverse a y| ≤ (R + 2 * C₁ + 10) * 2 ^ k
    exact ⟨abs_le.mpr ⟨by linarith only [hcast₁, hI₁, h2m],
        by linarith only [hcast₂, hI₂, hlbound]⟩,
      abs_le.mpr ⟨by linarith only [h₁, hu₁, hB, hC, h2k],
        by linarith only [h₂, hu₂, hB, hC, h2k]⟩⟩
  have hgs (s : ℕ) : g (s + 1) = g s + (1, 0) ∨ g (s + 1) = g s + (0, 1) := by
    simpa only [g, gammaStream, Nat.cast_add, Nat.cast_one, add_assoc] using
      gammaPoint_step b a u (C.I + (s : ℤ))
  have hgl (s : ℕ) : lev (g s) = C.I + (s : ℤ) := gammaPoint_level _ _ _ _
  have hg (s : ℕ) (hs : s ≤ l) :
      g s ∈ Q ∧ b (g s) = false ∧ |transverse a (g s) - ρ| ≤ (Δ : ℝ) :=
    gammaPoint_bounds b a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ (goodEvent_siteMask hE) u C.site_mem _
      (gammaDefined_between hγ hγend (by omega) (by omega))
  have hg₀ : g 0 = gammaPoint b a u C.I := by simp only [g, gammaStream, Nat.cast_zero, add_zero]
  have hgt : gammaPoint b a u C.I ∉ forwardTrapped ω T := by
    have hΔ : K₃ ^ 2 ≤ Δ := by
      have hlo : K₃ ^ 2 ≤ (2 * K₃ ^ 2 + 1) ^ 2 :=
        le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
      exact hlo.trans (by
        exact le_trans (Nat.le_mul_of_pos_left _ hK₁) (Nat.le_succ _))
    have hlen : K₃ ^ 2 ≤ l + 1 := hΔ.trans (by
      have hi : (Δ : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
        push_cast
        linarith only [hwbig, hPw, hlR, hcP, hP0, hΔ0]
      exact_mod_cast hi)
    have hgQ : g 0 ∈ collar Q (collarRadius θ K₁ K₃) :=
      ⟨g 0, (hg 0 (Nat.zero_le _)).1, by simp [latticeDistance]⟩
    have hnt := not_trapped_of_long_seq ω T K₃ g l (fun s _ => hgs s)
      (fun s hs => (siteMask_eq_false_iff ω T _).mp (hg s hs.le).2.1) hlen (hE.2 _ hgQ).1
    rwa [← hg₀]
  obtain ⟨x₀, d, x, hx0, hd, hxB, hxw, hxW⟩ := C.exists_capped_crossing htrial (by omega)
  have hc := (coarse_crossing_centre_spec a C.h w C.I m' (C.ν.val + 1)).2
  change |transverse a C.centre - ((C.h : ℝ) * w + 30 * ((C.ν.val + 1 : ℕ) : ℝ) * w)| ≤ 1 / 2 at hc
  have hN1 : 1 ≤ (C.ν.val + 1 : ℕ) := by omega
  have hN2 : C.ν.val + 1 ≤ C.j ^ 2 := C.ν.isLt
  have hNw : ((C.ν.val + 1 : ℕ) : ℝ) * w ≤ P :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hN2) hw0
  have hNw1 : (w : ℝ) ≤ ((C.ν.val + 1 : ℕ) : ℝ) * w :=
    le_mul_of_one_le_left hw0 (by exact_mod_cast hN1)
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  obtain ⟨hh₁, hh₂⟩ := C.transverse_mem
  have hxρ (i : Fin (d.1 + d.2 + 1)) : |transverse a (x.vertex i) - ρ| ≤ 39 * P := by
    have hband : |transverse a (x.vertex i) - transverse a C.centre| ≤ 8 * (w : ℝ) := (hxB i).2.2
    obtain ⟨h₁, h₂⟩ := abs_le.mp hband
    exact abs_le.mpr ⟨by linarith only [h₁, h₂, hc₁, hc₂, hh₁, hh₂, hNw, hNw1, hPw, hwbig, hΔ0],
      by linarith only [h₁, h₂, hc₁, hc₂, hh₁, hh₂, hNw, hNw1, hPw, hwbig, hΔ0]⟩
  have hxQ (i : Fin (d.1 + d.2 + 1)) : x.vertex i ∈ Q := by
    have h₁ : C.I + (m' : ℤ) ≤ lev (x.vertex i) := (hxB i).1
    have h₂ : lev (x.vertex i) ≤ C.I + (l : ℤ) - (m' : ℤ) := (hxB i).2.1
    exact hQ _ (by omega) (by omega) ((hxρ i).trans (by linarith only [hcP, hP0]))
  let Wx := G * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ)
  obtain ⟨v, v', α, β, hα, hβ₁, hβ₂, hvl, hv'l, ⟨iv, hiv⟩, ⟨iv', hiv'⟩, hbox, hv'nt,
      e, p₂, hend₂, hw₂, hloc₂⟩ :=
    coarse_trim_piece ω T θ K₃ K₁ Q a ρ B w Wx hθ hθ' hK₃ hK₁ hE hw0 x₀ d x
      (by change 2 * r + 1 ≤ d.1 + d.2; omega)
      hxQ hxw (fun i => (hxρ i).trans (by linarith only [hcP, hP0])) hxW.le
  change α ≤ r at hα
  change d.1 + d.2 ≤ β + r at hβ₁
  have hv : v ∈ C.sites := hiv ▸ hxB iv
  have hv' : v' ∈ C.sites := hiv' ▸ hxB iv'
  have hvρ : |transverse a v - ρ| ≤ 39 * P := hiv ▸ hxρ iv
  have hv'ρ : |transverse a v' - ρ| ≤ 39 * P := hiv' ▸ hxρ iv'
  have hv'Q : v' ∈ Q := hiv' ▸ hxQ iv'
  have hvlev : lev v = C.I + (m' : ℤ) + (α : ℤ) := hvl.trans (by rw [show x₀.1 + x₀.2 = C.I + (m' : ℤ) from hx0])
  have hv'lev : lev v' = C.I + (m' : ℤ) + (β : ℤ) := hv'l.trans (by rw [show x₀.1 + x₀.2 = C.I + (m' : ℤ) from hx0])
  have hθm : 40 * P ≤ 4 * θ * (m' : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm₁ hθ.le
    have hprod : θ * (cstar * P) = 10 * P := by rw [← mul_assoc, hcθ]
    linarith only [h, hprod]
  have hγρ : |transverse a (gammaPoint b a u C.I) - ρ| ≤ (Δ : ℝ) :=
    hg₀ ▸ (hg 0 (Nat.zero_le _)).2.2
  obtain ⟨hγ₁, hγ₂⟩ := abs_le.mp hγρ
  obtain ⟨hv₁, hv₂⟩ := abs_le.mp hvρ
  have hn₁ : (lev v - C.I).toNat = m' + α := by omega
  obtain ⟨s₁, hs₁, hs10, hs1end, hs1len, hs1loc⟩ :=
    C.selected_arrival ω T (40 * P) B ha₀ ha₁ hK₁ hK₃ v hv hE hγ hgt
      (by change lev v ≤ C.I + (m' : ℤ) + (r : ℤ); omega)
      hbox (by change L ≤ (lev v - C.I).toNat; rw [hn₁]; omega)
      (by
        rw [hn₁, Nat.cast_add]
        have hθα := mul_nonneg hθ.le (Nat.cast_nonneg (α := ℝ) α)
        exact abs_le.mpr ⟨by linarith only [hγ₁, hγ₂, hv₁, hv₂, hθm, hθα, hwbig, hPw, hΔ0],
          by linarith only [hγ₁, hγ₂, hv₁, hv₂, hθm, hθα, hwbig, hPw, hΔ0]⟩)
      (hγρ.trans (by linarith only [hwbig, hPw, hP0, hΔ0])) (hvρ.trans (by linarith only [hP0]))
      (by linarith only [hcP, hW4, hPw, hΔ0, hr0, hL0, hP0]) hQ
  have hn₂ : (C.upperLevel - lev v').toNat = l - (m' + β) := by omega
  have hn₂lo : (m' : ℝ) ≤ ((l - (m' + β) : ℕ) : ℝ) := by
    exact_mod_cast (show m' ≤ l - (m' + β) by omega)
  have hθn := mul_le_mul_of_nonneg_left hn₂lo hθ.le
  have hgβ : gammaPoint b a u (lev v') = g (m' + β) := by
    simp only [g, gammaStream, hv'lev, Nat.cast_add, add_assoc]
  have hgβρ := (hg (m' + β) (by omega)).2.2
  obtain ⟨hgβ₁, hgβ₂⟩ := abs_le.mp hgβρ
  obtain ⟨hv'₁, hv'₂⟩ := abs_le.mp hv'ρ
  have hv'band : |transverse a v' - transverse a C.centre| ≤ 8 * (w : ℝ) := hv'.2.2
  obtain ⟨hv'c₁, _⟩ := abs_le.mp hv'band
  obtain ⟨i, _, hin, _, s₃, hs₃, s₄, hs₄, hs30, hs3end, hs40, hs4end, hs3len, hs4len, hs3loc, hs4loc⟩ :=
    C.selected_merge ω T (40 * P) B ha₀ ha₁ hK₁ hK₃ v' hv' hE hγ hγend hgt hv'Q hv'nt
      (by change C.upperLevel - (m' : ℤ) - (r : ℤ) ≤ lev v'; omega) (by omega)
      (by
        change transverse a (gammaPoint b a u (lev v' + ((0 : ℕ) : ℤ))) < _
        rw [Nat.cast_zero, add_zero, hgβ]
        linarith only [hgβ₂, hv'c₁, hc₁, hh₂, hNw1, hwbig, hΔ0])
      (by
        rw [hn₂]
        exact abs_le.mpr ⟨by linarith only [hv'₁, hv'₂, hθm, hθn, hwbig, hPw, hΔ0],
          by linarith only [hv'₁, hv'₂, hθm, hθn, hwbig, hPw, hΔ0]⟩)
      (hv'ρ.trans (by linarith only [hP0]))
      (by linarith only [hwbig, hPw, hP0, hΔ0])
      (by linarith only [hcP, hwbig, hPw, hP0, hΔ0]) hQ
    -- Both merge pieces come from the same fixed first meeting.
  have hw₁ := hweight s₁ hs₁
  have hw₃ := hweight s₃ hs₃
  have hw₄ := hweight s₄ hs₄
  rw [hs1len, hn₁] at hw₁
  rw [hs3len] at hw₃
  rw [hs4len, hn₂] at hw₄
  rw [hn₂] at hin
  let z := gammaPoint b a u C.I
  let z' := gammaPoint b a u C.upperLevel
  let meet := gammaStream b a u (lev v') i
  rcases s₁ with ⟨z₁, d₁, p₁⟩
  rcases s₃ with ⟨z₃, d₃, p₃⟩
  rcases s₄ with ⟨z₄, d₄, p₄⟩
  change z₁ = z at hs10
  change z₃ = v' at hs30
  change z₄ = meet at hs40
  subst z₁ z₃ z₄
  obtain ⟨D34, p34, hD34, hw34, hloc34⟩ := exists_path_join ω (fun y => transverse a y - ρ) B
    _ _ v' meet z' ⟨d₃, p₃, hs3end, hw₃, hs3loc⟩ ⟨d₄, p₄, hs4end, hw₄, hs4loc⟩
  have hw34' : -2 * Cm * ((l - (m' + β) : ℕ) : ℝ) - t ≤ pathWeight ω p34 := by
    rw [Nat.cast_sub hin.le] at hw34
    linarith only [hw34]
  have hw₂' : G * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ) - 2 * (r : ℝ) * (w : ℝ) ≤
      pathWeight ω p₂ := hw₂
  obtain ⟨D12, p12, hD12, hw12, hloc12⟩ := exists_path_join ω (fun y => transverse a y - ρ) B
    _ _ z v v' ⟨d₁, p₁, hs1end, hw₁, hs1loc⟩ ⟨e, p₂, hend₂, hw₂', hloc₂⟩
  obtain ⟨D, y, hD, hyw, hyloc⟩ := exists_path_join ω (fun y => transverse a y - ρ) B
    _ _ z v' z' ⟨D12, p12, hD12, hw12, hloc12⟩ ⟨D34, p34, hD34, hw34', hloc34⟩
  -- The three non-crossing pieces span at most the two insets plus the two trims.
  have hzlev : z.1 + z.2 = C.I := gammaPoint_level _ _ _ _
  have hz'lev : z'.1 + z'.2 = C.I + (l : ℤ) := gammaPoint_level _ _ _ _
  have hD₁ : z.1 + (D.1 : ℤ) = z'.1 := congrArg Prod.fst hD
  have hD₂ : z.2 + (D.2 : ℤ) = z'.2 := congrArg Prod.snd hD
  have hDl : (D.1 : ℝ) + (D.2 : ℝ) = (l : ℝ) := by exact_mod_cast
    (show (D.1 : ℤ) + (D.2 : ℤ) = (l : ℤ) by omega)
  have hDr : (1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ) = transverse a z' - transverse a z := by
    have e₁ : (z.1 : ℝ) + D.1 = z'.1 := by exact_mod_cast hD₁
    have e₂ : (z.2 : ℝ) + D.2 = z'.2 := by exact_mod_cast hD₂
    unfold transverse
    linear_combination (1 - a) * e₁ - a * e₂
  have hz'r : |transverse a z' - ρ| ≤ (Δ : ℝ) := (hg l le_rfl).2.2
  obtain ⟨hl₁, hl₂⟩ := abs_le.mp hz'r
  have hDr' : |(1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)| ≤ 2 * (Δ : ℝ) := by
    rw [hDr, abs_le]
    exact ⟨by linarith only [hγ₁, hγ₂, hl₁, hl₂], by linarith only [hγ₁, hγ₂, hl₁, hl₂]⟩
  have hσ (σ : ℝ) (hσ : |σ| ≤ K) :
      σ * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) ≤ 2 * (Δ : ℝ) * K := by
    calc
      _ ≤ |σ * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ))| := le_abs_self _
      _ ≤ K * (2 * (Δ : ℝ)) := by
        rw [abs_mul]
        exact mul_le_mul hσ hDr' (abs_nonneg _) hK0
      _ = _ := by ring
  have hc₂m : ((l - 2 * m' : ℕ) : ℝ) = (l : ℝ) - 2 * (m' : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_two]
  have hc₃ : ((l - (m' + β) : ℕ) : ℝ) = (l : ℝ) - (m' : ℝ) - (β : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, sub_sub]
  have hβR : (l : ℝ) - 2 * (m' : ℝ) ≤ (β : ℝ) + (r : ℝ) := by
    rw [← hc₂m, ← Nat.cast_add]
    exact_mod_cast (show l - 2 * m' ≤ β + r by omega)
  rw [hc₂m, hc₃, Nat.cast_add] at hyw
  have hαR : (α : ℝ) ≤ r := by exact_mod_cast hα
  have hCmb := mul_le_mul_of_nonneg_left
    (show ((m' : ℝ) + α) + ((l : ℝ) - m' - β) ≤ 2 * (m' : ℝ) + 2 * r by
      linarith only [hβR, hαR])
    (by linarith only [hCm] : 0 ≤ 2 * Cm)
  have hG₂ := mul_le_mul_of_nonneg_right (show 2 * (m' : ℝ) ≤ 4 * cstar * P by
    linarith only [hm₂, hcP, hPw, hwbig, hP0, hΔ0]) hGC
  have hKw := mul_le_mul_of_nonneg_left hPw (by linarith only [hK0, hr0] : 0 ≤ K + 2 * (r : ℝ))
  have hC₁P := mul_le_mul_of_nonneg_right (show 4 * cstar * (G + 2 * Cm) + K + 2 * (r : ℝ) + 1 ≤ C₁ by
    linarith only [hC₁, hcG, hK0, hc100]) hP0
  have hloc (j : Fin (D.1 + D.2 + 1)) : |transverse a (y.vertex j) - ρ| ≤ C₁ * P :=
    (hyloc j).trans (mul_le_mul_of_nonneg_right hcC hP0)
  refine ⟨D, y, hD, ?_, ?_, hloc⟩
  · have h := hσ dl hdl
    rw [hDl]
    linarith only [h, hyw, hCmb, hG₂, hKw, hC₁P, hWK, hPw, ht]
  · have h := hσ dr hdr
    rw [hDl]
    linarith only [h, hyw, hCmb, hG₂, hKw, hC₁P, hWK, hPw, ht]

end LPPDifferentiability.SelectedGridPaths.CoarseBlock
