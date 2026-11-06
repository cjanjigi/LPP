/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.LevelTransverseStaircase
public import Differentiability.Model.Paths.GridCoarseAttachment
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # One-scale connections

Lemma 5.7 (i) of the differentiability preprint, at one grid interval. For one grid interval
`[I, I + l]` at scale `(j, w)` and one transverse coordinate `ρ`, with `c_* = 50 / min a (1 - a)`:

* at a fine scale (`l < 8 c_* j² w`) the staircase at `ρ` joins `ẑ(I, ρ)` to `ẑ(I + l, ρ)`;
  if its weight is at least `l E - t`, both defects are at most
  `8 c_* (G0 - E) j² w + K + t` and every vertex is within `1` of `ρ`;
* at a coarse scale the crossing connection of `GridCoarseAttachment` applies;
* in both cases the defects are at most `C₁ j² w + 2 t` and every vertex is within
  `C₁ j² w` of `ρ`, where `C₁ = 8 c_* (G0 - E) + 2 K + 3 c_*`.
-/

public section

namespace LPPDifferentiability

/-- The defect of a path with displacement `D` of level `l`, transverse part of absolute
value at most `1`, and weight at least `l E - t`. -/
private theorem fine_defect_core (a ρ G0 E s K t cstar P W : ℝ) (l : ℕ) (D : ℕ × ℕ)
    (z₀ z₁ : Lattice) (hD : z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁) (hDl : D.1 + D.2 = l)
    (hz₀a : ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ))
    (hz₀b : (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ)
    (hz₁a : ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ))
    (hz₁b : (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ)
    (hK : |s| ≤ K) (hEG : E ≤ G0) (hl : (l : ℝ) ≤ 8 * cstar * P)
    (hW : (l : ℝ) * E - t ≤ W) :
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + s * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - W ≤
      8 * cstar * (G0 - E) * P + K + t := by
  have e1 := congrArg Prod.fst hD
  have e2 := congrArg Prod.snd hD
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  have r1 : (z₀.1 : ℝ) + D.1 = z₁.1 := by exact_mod_cast e1
  have r2 : (z₀.2 : ℝ) + D.2 = z₁.2 := by exact_mod_cast e2
  have hlR : (D.1 : ℝ) + D.2 = l := by exact_mod_cast hDl
  have hrD : |(1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)| ≤ 1 := by
    have q1 : (D.1 : ℝ) = z₁.1 - z₀.1 := by linarith
    have q2 : (D.2 : ℝ) = z₁.2 - z₀.2 := by linarith
    rw [q1, q2, abs_le]
    constructor <;> linarith
  have hK0 : 0 ≤ K := (abs_nonneg s).trans hK
  have hs : s * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) ≤ K := by
    calc s * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) ≤
        |s * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ))| := le_abs_self _
      _ = |s| * |(1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)| := abs_mul _ _
      _ ≤ K * 1 := mul_le_mul hK hrD (abs_nonneg _) hK0
      _ = K := mul_one K
  have h2 : (G0 - E) * (l : ℝ) ≤ (G0 - E) * (8 * cstar * P) :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  have g1 : G0 * ((D.1 : ℝ) + (D.2 : ℝ)) = G0 * (l : ℝ) := by rw [hlR]
  linarith

/-- **Fine scale of Lemma 5.7 (i), one fixed environment.** At a fine scale
`l < 8 c_* j² w`, the staircase from `ẑ(I, ρ)` to `ẑ(I + l, ρ)` has vertex `k` equal to
`ẑ(I + k, ρ)` and all vertices within `1` of `ρ`; if its weight is at least `l E - t`,
both literal defects are at most `8 c_* (G0 - E) j² w + K + t`. -/
theorem fine_scale_connection
    (a G0 E dl dr K t cstar : ℝ) (ω : Environment) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hEG : E ≤ G0) (hdl : |dl| ≤ K) (hdr : |dr| ≤ K)
    (w j l : ℕ) (hl : (l : ℝ) < 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)))
    (I : ℤ) (ρ : ℝ) (z₀ z₁ : Lattice)
    (hz₀ : z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
      (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ)
    (hz₁ : z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
      (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) :
    ∃ (D : ℕ × ℕ) (q : Path z₀ D),
      z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
      (∀ k : Fin (D.1 + D.2 + 1),
        q.vertex k =
          (⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋,
            (I + (k.val : ℤ)) - ⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋)) ∧
      (∀ k, |(1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) - ρ| < 1) ∧
      ((l : ℝ) * E - t ≤ pathWeight ω q →
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω q ≤
          8 * cstar * (G0 - E) * ((j : ℝ) ^ 2 * (w : ℝ)) + K + t ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω q ≤
          8 * cstar * (G0 - E) * ((j : ℝ) ^ 2 * (w : ℝ)) + K + t) := by
  obtain ⟨i, q, hv, hr, hu⟩ := exists_level_transverse_staircase a ρ ha₀ ha₁ I l
  obtain ⟨hz₀l, hz₀a, hz₀b⟩ := hz₀
  obtain ⟨hz₁l, hz₁a, hz₁b⟩ := hz₁
  have hil : i.val ≤ l := by
    have := i.isLt
    omega
  have hz₀eq : z₀ = q.vertex 0 := hu 0 z₀ (by simpa using hz₀l) hz₀a hz₀b
  rw [q.start] at hz₀eq
  subst hz₀eq
  have hz₁eq : z₁ = q.vertex (Fin.last (i.val + (l - i.val))) :=
    hu (Fin.last (i.val + (l - i.val))) z₁ (by simp only [Fin.val_last]; omega) hz₁a hz₁b
  have hD : (⌊ρ + a * (I : ℝ)⌋, I - ⌊ρ + a * (I : ℝ)⌋) +
      (((i.val, l - i.val).1 : ℤ), ((i.val, l - i.val).2 : ℤ)) = z₁ := by
    rw [hz₁eq, q.finish]
  have hdisp : (i.val, l - i.val).1 + (i.val, l - i.val).2 = l := by
    show i.val + (l - i.val) = l
    omega
  refine ⟨(i.val, l - i.val), q, hD, hv, fun k => ?_, fun hW => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hr k
    rw [abs_lt]
    constructor <;> linarith
  · have hl' : (l : ℝ) ≤ 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) := hl.le
    exact ⟨fine_defect_core a ρ G0 E dl K t cstar _ _ l _ _ _ hD hdisp hz₀a hz₀b hz₁a hz₁b
        hdl hEG hl' hW,
      fine_defect_core a ρ G0 E dr K t cstar _ _ l _ _ _ hD hdisp hz₀a hz₀b hz₁a hz₁b
        hdr hEG hl' hW⟩

/-- **Combined one-scale connection of Lemma 5.7 (i), one fixed environment.**
With `C₁ = 8 c_* (G0 - E) + 2 K + 3 c_*`, at every scale the connection from `ẑ(I, ρ)` to
`ẑ(I + l, ρ)` has both literal defects at most `C₁ j² w + 2 t` and all vertices within
`C₁ j² w` of `ρ`. The first part is the fine case. The second part is the coarse case: it holds
for every family of block centres with the level and rounding properties of
`coarse_scale_connection`, and `exists_grid_coarse_centres` gives one such family. -/
theorem grid_scale_connection
    (a G0 E dl dr K t cstar : ℝ) (ω : Environment) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hcstar : cstar = 50 / min a (1 - a)) (hEG : E ≤ G0)
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (ht : 0 ≤ t)
    (w j l m : ℕ) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hm : m = ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊)
    (I h : ℤ) (ρ : ℝ) (hρ₁ : (h : ℝ) * (w : ℝ) ≤ ρ) (hρ₂ : ρ < ((h : ℝ) + 1) * (w : ℝ))
    (z₀ z₁ : Lattice)
    (hz₀ : z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
      (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ)
    (hz₁ : z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
      (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) :
    ((l : ℝ) < 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) →
      ∃ (D : ℕ × ℕ) (q : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        (∀ k : Fin (D.1 + D.2 + 1),
          q.vertex k =
            (⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋,
              (I + (k.val : ℤ)) - ⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋)) ∧
        ((l : ℝ) * E - t ≤ pathWeight ω q →
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω q ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω q ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          ∀ k, |(1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) - ρ| ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)))) ∧
    (8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) → (l : ℝ) ≤ (w : ℝ) ^ 3 / 2 →
      ∀ c : Fin (j ^ 2) → Lattice,
        (∀ ν, (c ν).1 + (c ν).2 = I + (m : ℤ)) →
        (∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
          ((h : ℝ) * (w : ℝ) + 30 * ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ))| ≤ 1 / 2) →
        ∀ (ν : Fin (j ^ 2)) (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
          u.1 + u.2 = I + (m : ℤ) → d.1 + d.2 = l - 2 * m →
          (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ) -
            ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ)) →
          G0 * ((l - 2 * m : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x →
          ∃ d₁ d₂ : ℕ × ℕ,
            z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) = u ∧
            u + ((d.1 : ℤ), (d.2 : ℤ)) + ((d₂.1 : ℤ), (d₂.2 : ℤ)) = z₁ ∧
            ((m : ℝ) * E - t ≤ pathWeight ω (horizontalFirst z₀ d₁) →
              (m : ℝ) * E - t ≤
                pathWeight ω (horizontalFirst (u + ((d.1 : ℤ), (d.2 : ℤ))) d₂) →
              ∃ (D : ℕ × ℕ) (y : Path z₀ D),
                z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
                G0 * ((D.1 : ℝ) + (D.2 : ℝ)) +
                  dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - pathWeight ω y ≤
                    (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) *
                      ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
                G0 * ((D.1 : ℝ) + (D.2 : ℝ)) +
                  dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - pathWeight ω y ≤
                    (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) *
                      ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
                ∀ k, |(1 - a) * ((y.vertex k).1 : ℝ) - a * ((y.vertex k).2 : ℝ) - ρ| ≤
                  (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) *
                    ((j : ℝ) ^ 2 * (w : ℝ)))) := by
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    linarith
  have hcpos : 0 < cstar := by rw [hcstar]; positivity
  have hcθ : min a (1 - a) * cstar = 50 := by rw [hcstar]; field_simp
  have hc100 : 100 ≤ cstar := by
    have := mul_le_mul_of_nonneg_right hθ2 hcpos.le
    linarith
  have hw2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    rw [sq]
    exact one_le_mul_of_one_le_of_one_le hj1 hj1
  have hP2 : 2 ≤ (j : ℝ) ^ 2 * (w : ℝ) := by
    calc (2 : ℝ) = 1 * 2 := by norm_num
      _ ≤ (j : ℝ) ^ 2 * (w : ℝ) := mul_le_mul hj2 hw2 (by norm_num) (by positivity)
  have hK0 : 0 ≤ K := (abs_nonneg dl).trans hdl
  have hGE : 0 ≤ G0 - E := by linarith
  have hcP : 0 ≤ cstar * ((j : ℝ) ^ 2 * (w : ℝ)) :=
    mul_nonneg hcpos.le (by positivity)
  have hX : 0 ≤ cstar * (G0 - E) * ((j : ℝ) ^ 2 * (w : ℝ)) :=
    mul_nonneg (mul_nonneg hcpos.le hGE) (by positivity)
  have hKP : 0 ≤ K * ((j : ℝ) ^ 2 * (w : ℝ)) :=
    mul_nonneg hK0 (by positivity)
  have hKP1 : K * 1 ≤ K * ((j : ℝ) ^ 2 * (w : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have hcP100 : 100 * 2 ≤ cstar * ((j : ℝ) ^ 2 * (w : ℝ)) :=
    mul_le_mul hc100 hP2 (by norm_num) (by linarith)
  refine ⟨fun hl => ?_, fun hl hell => ?_⟩
  · obtain ⟨D, q, hD, hv, hr, hk⟩ :=
      fine_scale_connection a G0 E dl dr K t cstar ω ha₀ ha₁ hEG hdl hdr w j l hl I ρ z₀ z₁ hz₀ hz₁
    refine ⟨D, q, hD, hv, fun hW => ?_⟩
    obtain ⟨b₁, b₂⟩ := hk hW
    refine ⟨by linarith, by linarith, fun k => ?_⟩
    have := (hr k).le
    linarith
  · intro c hc1 hc2 ν u d x hu hd hx hW
    obtain ⟨d₁, d₂, h1, h2, hk⟩ := coarse_scale_connection a G0 E dl dr K t cstar ω ha₀ ha₁
      hcstar hEG hdl hdr w j l m hw hj hm hl hell I h ρ hρ₁ hρ₂ z₀ z₁ hz₀ hz₁ c hc1 hc2
      ν u d x hu hd hx hW
    refine ⟨d₁, d₂, h1, h2, fun hw₁ hw₂ => ?_⟩
    obtain ⟨D, y, hD, b₁, b₂, b₃⟩ := hk hw₁ hw₂
    refine ⟨D, y, hD, by linarith, by linarith, fun k => (b₃ k).trans ?_⟩
    linarith

/-- **Existence of coarse block centres for Lemma 5.7 (i).** For the parameters of
`grid_scale_connection` with `2 m < l` and `l ≤ w³ / 2`, some family of centres `c ν`, one for
each `ν < j²`, has the level and rounding properties used by `coarse_scale_connection`.
This is `exists_coarse_crossing_blocks` with `N = j²`. -/
theorem exists_grid_coarse_centres (a : ℝ) (I h : ℤ) (w j l m : ℕ) (hw : 2 ≤ w)
    (hml : 2 * m < l) (hell : (l : ℝ) ≤ (w : ℝ) ^ 3 / 2) :
    ∃ c : Fin (j ^ 2) → Lattice,
      (∀ ν, (c ν).1 + (c ν).2 = I + (m : ℤ)) ∧
      (∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
        ((h : ℝ) * (w : ℝ) + 30 * ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ))| ≤ 1 / 2) := by
  have hw1 : (1 : ℝ) ≤ w := by
    have : 1 ≤ w := by omega
    exact_mod_cast this
  obtain ⟨c, -, hlevel, hround, -⟩ :=
    exists_coarse_crossing_blocks a (h : ℝ) (w : ℝ) I l m (j ^ 2) hw1 hml hell
  exact ⟨c, hlevel, hround⟩

end LPPDifferentiability
