/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.AttachmentSegment
public import LPP_Foundations.Model.Paths.Concat
public import LPP_Foundations.Model.Paths.Geometry
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Real `l1` bounds for actual lattice paths and their concatenation. -/

@[expose] public section

namespace LPPDifferentiability

/-- The endpoint displacement of an ordered path has real `l1` length equal to
its number of steps. -/
theorem lattice_attachment_endpoint_l1_eq (u : Lattice) (d : ℕ × ℕ) :
    (|(((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ)) - ((u.1 : ℝ))| + |(((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ)) - ((u.2 : ℝ))|) = (d.1 + d.2 : ℝ) := by
  have h₁ :
      ((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ) - (u.1 : ℝ) = (d.1 : ℝ) := by
    simp only [Prod.fst_add, Int.cast_add, Int.cast_natCast]
    ring
  have h₂ :
      ((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ) - (u.2 : ℝ) = (d.2 : ℝ) := by
    simp only [Prod.snd_add, Int.cast_add, Int.cast_natCast]
    ring
  rw [h₁, h₂, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _)]

namespace Path

/-- Every vertex of an actual ordered path is within its step count of its
initial vertex in real `l1` distance. -/
theorem vertex_l1_from_start_le_length {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (i : Fin (d.1 + d.2 + 1)) :
    (|((p.vertex i).1 : ℝ) - (u.1 : ℝ)| + |((p.vertex i).2 : ℝ) - (u.2 : ℝ)|) ≤
      (d.1 + d.2 : ℝ) := by
  rcases p.vertex_mem_Icc i with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  simp only [Prod.fst_add] at h₃
  simp only [Prod.snd_add] at h₄
  have h₁' : (p.vertex i).1 - u.1 ≤ (d.1 : ℤ) := by omega
  have h₂' : (p.vertex i).2 - u.2 ≤ (d.2 : ℤ) := by omega
  have h₁r₀ : 0 ≤ ((p.vertex i).1 : ℝ) - (u.1 : ℝ) := by
    exact_mod_cast (sub_nonneg.mpr h₁)
  have h₂r₀ : 0 ≤ ((p.vertex i).2 : ℝ) - (u.2 : ℝ) := by
    exact_mod_cast (sub_nonneg.mpr h₂)
  have h₁r : ((p.vertex i).1 : ℝ) - (u.1 : ℝ) ≤ (d.1 : ℝ) := by
    exact_mod_cast h₁'
  have h₂r : ((p.vertex i).2 : ℝ) - (u.2 : ℝ) ≤ (d.2 : ℝ) := by
    exact_mod_cast h₂'
  rw [abs_of_nonneg h₁r₀, abs_of_nonneg h₂r₀]
  calc
    (((p.vertex i).1 : ℝ) - (u.1 : ℝ)) +
        (((p.vertex i).2 : ℝ) - (u.2 : ℝ)) ≤ (d.1 : ℝ) + (d.2 : ℝ) :=
      add_le_add h₁r h₂r
    _ = (d.1 + d.2 : ℝ) := by simp only

/-- Every vertex of an actual ordered path is within its remaining step count
of its terminal vertex in real `l1` distance. -/
theorem vertex_l1_to_finish_le_length {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (i : Fin (d.1 + d.2 + 1)) :
    (|((p.vertex i).1 : ℝ) - ((u + ((d.1 : ℤ), (d.2 : ℤ))).1)| + |((p.vertex i).2 : ℝ) - ((u + ((d.1 : ℤ), (d.2 : ℤ))).2)|) ≤
      (d.1 + d.2 : ℝ) := by
  rcases p.vertex_mem_Icc i with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  simp only [Prod.fst_add] at h₃
  simp only [Prod.snd_add] at h₄
  have h₁' : (p.vertex i).1 - (u.1 + (d.1 : ℤ)) ≤ 0 := by omega
  have h₂' : (p.vertex i).2 - (u.2 + (d.2 : ℤ)) ≤ 0 := by omega
  have h₁r₀ :
      ((p.vertex i).1 : ℝ) - ((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ) ≤ 0 := by
    exact_mod_cast h₁'
  have h₂r₀ :
      ((p.vertex i).2 : ℝ) - ((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ) ≤ 0 := by
    exact_mod_cast h₂'
  have h₁r :
      ((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ) - ((p.vertex i).1 : ℝ) ≤
        (d.1 : ℝ) := by
    have hbound : (u.1 + (d.1 : ℤ)) - (p.vertex i).1 ≤ (d.1 : ℤ) := by omega
    exact_mod_cast hbound
  have h₂r :
      ((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ) - ((p.vertex i).2 : ℝ) ≤
        (d.2 : ℝ) := by
    have hbound : (u.2 + (d.2 : ℤ)) - (p.vertex i).2 ≤ (d.2 : ℤ) := by omega
    exact_mod_cast hbound
  rw [abs_of_nonpos h₁r₀, abs_of_nonpos h₂r₀]
  calc
    -(((p.vertex i).1 : ℝ) - ((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ)) +
        -(((p.vertex i).2 : ℝ) - ((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ)) =
        (((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ) - ((p.vertex i).1 : ℝ)) +
          (((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ) - ((p.vertex i).2 : ℝ)) := by ring
    _ ≤ (d.1 : ℝ) + (d.2 : ℝ) := add_le_add h₁r h₂r
    _ = (d.1 + d.2 : ℝ) := by simp only

private theorem transport_vertex {a b : Lattice} {d : ℕ × ℕ}
    (h : a = b) (p : Path a d) (i : Fin (d.1 + d.2 + 1)) :
    (h ▸ p : Path b d).vertex i = p.vertex i := by
  cases h
  rfl

private theorem concat_vertex_in_piece {u : Lattice} {d e : ℕ × ℕ}
    (p : Path u d) (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (i : Fin ((d + e).1 + (d + e).2 + 1)) :
    (∃ j : Fin (d.1 + d.2 + 1), (p.concat q).vertex i = p.vertex j) ∨
    (∃ j : Fin (e.1 + e.2 + 1), (p.concat q).vertex i = q.vertex j) := by
  by_cases h : i.val ≤ d.1 + d.2
  · let j : Fin (d.1 + d.2 + 1) := ⟨i.val, by omega⟩
    refine Or.inl ⟨j, ?_⟩
    have hi : i = ⟨j.val, by
        have hlen := i.isLt
        simp only [Prod.fst_add, Prod.snd_add] at hlen
        omega⟩ := Fin.ext rfl
    rw [hi]
    exact p.concat_vertex_left q j
  · let j : Fin (e.1 + e.2 + 1) := ⟨i.val - (d.1 + d.2), by
      have hlen := i.isLt
      simp only [Prod.fst_add, Prod.snd_add] at hlen
      omega⟩
    refine Or.inr ⟨j, ?_⟩
    have hjval : j.val = i.val - (d.1 + d.2) := rfl
    have hi : i = ⟨d.1 + d.2 + j.val, by
        have hlen := i.isLt
        simp only [Prod.fst_add, Prod.snd_add] at hlen
        rw [hjval]
        omega⟩ := by
      apply Fin.ext
      change i.val = d.1 + d.2 + j.val
      omega
    rw [hi]
    exact p.concat_vertex_right q j

end Path

/-- The actual nested concatenation of the prefix, middle, and suffix has the
claimed terminal vertex and every one of its vertices lies in the original
segment tube. The middle-path tube premise is the source travel estimate. -/
theorem concat_three_attachments_within_tube
    (u uHat vHat v : Lattice) (d₁ d₂ d₃ : ℕ × ℕ) (m : ℕ)
    (p : Path u d₁) (q : Path uHat d₂) (r : Path vHat d₃)
    (hUHat : uHat = u + ((d₁.1 : ℤ), (d₁.2 : ℤ)))
    (hVHat : vHat = uHat + ((d₂.1 : ℤ), (d₂.2 : ℤ)))
    (hV : v = vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ)))
    (hPrefixLength : d₁.1 + d₁.2 = m)
    (hSuffixLength : d₃.1 + d₃.2 = m)
    (δ s : ℝ) (hScale : (m : ℝ) ≤ δ * s / 2)
    (hMiddle : ∀ i : Fin (d₂.1 + d₂.2 + 1),
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        (|((q.vertex i).1 : ℝ) - ((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ))| + |((q.vertex i).2 : ℝ) - ((1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ))|) ≤ δ * s / 2) :
    (let joined : Path u (d₁ + (d₂ + d₃)) :=
      p.concat ((hUHat ▸ q).concat
        ((hVHat.trans (congrArg (fun z : Lattice =>
          z + ((d₂.1 : ℤ), (d₂.2 : ℤ))) hUHat)) ▸ r));
      (∀ i : Fin ((d₁ + (d₂ + d₃)).1 + (d₁ + (d₂ + d₃)).2 + 1),
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
          (|((joined.vertex i).1 : ℝ) - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |((joined.vertex i).2 : ℝ) - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) ≤ δ * s) ∧
        joined.vertex (Fin.last ((d₁ + (d₂ + d₃)).1 +
          (d₁ + (d₂ + d₃)).2)) = v) := by
  dsimp only
  let qAligned : Path (u + ((d₁.1 : ℤ), (d₁.2 : ℤ))) d₂ := hUHat ▸ q
  have hQEnd : vHat = (u + ((d₁.1 : ℤ), (d₁.2 : ℤ))) +
      ((d₂.1 : ℤ), (d₂.2 : ℤ)) :=
    hVHat.trans (congrArg (fun z : Lattice => z + ((d₂.1 : ℤ), (d₂.2 : ℤ))) hUHat)
  let rAligned : Path ((u + ((d₁.1 : ℤ), (d₁.2 : ℤ))) +
      ((d₂.1 : ℤ), (d₂.2 : ℤ))) d₃ := hQEnd ▸ r
  let joined : Path u (d₁ + (d₂ + d₃)) := p.concat (qAligned.concat rAligned)
  change (∀ i : Fin ((d₁ + (d₂ + d₃)).1 + (d₁ + (d₂ + d₃)).2 + 1),
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        (|((joined.vertex i).1 : ℝ) - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |((joined.vertex i).2 : ℝ) - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) ≤ δ * s) ∧
      joined.vertex (Fin.last ((d₁ + (d₂ + d₃)).1 +
        (d₁ + (d₂ + d₃)).2)) = v
  have hqVertex (i : Fin (d₂.1 + d₂.2 + 1)) : qAligned.vertex i = q.vertex i :=
    Path.transport_vertex hUHat q i
  have hrVertex (i : Fin (d₃.1 + d₃.2 + 1)) : rAligned.vertex i = r.vertex i :=
    Path.transport_vertex hQEnd r i
  have hAttachmentStart :
      (|(uHat.1 : ℝ) - (u.1 : ℝ)| + |(uHat.2 : ℝ) - (u.2 : ℝ)|) = (m : ℝ) := by
    calc
      (|(uHat.1 : ℝ) - (u.1 : ℝ)| + |(uHat.2 : ℝ) - (u.2 : ℝ)|) =
          (|(((u + ((d₁.1 : ℤ), (d₁.2 : ℤ))).1)) - (u.1 : ℝ)| + |(((u + ((d₁.1 : ℤ), (d₁.2 : ℤ))).2)) - (u.2 : ℝ)|) := by rw [hUHat]
      _ = (d₁.1 + d₁.2 : ℝ) := lattice_attachment_endpoint_l1_eq u d₁
      _ = (m : ℝ) := by exact_mod_cast hPrefixLength
  have hAttachmentFinish :
      (|(vHat.1 : ℝ) - (v.1 : ℝ)| + |(vHat.2 : ℝ) - (v.2 : ℝ)|) = (m : ℝ) := by
    calc
      (|(vHat.1 : ℝ) - (v.1 : ℝ)| + |(vHat.2 : ℝ) - (v.2 : ℝ)|) =
          (|(vHat.1 : ℝ) - (((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).1))| + |(vHat.2 : ℝ) - (((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).2))|) := by rw [hV]
      _ = (|(((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).1)) - (vHat.1 : ℝ)| + |(((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).2)) - (vHat.2 : ℝ)|) := realL1Distance_comm
        ((vHat.1 : ℝ), (vHat.2 : ℝ))
        (((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).1 : ℝ),
          ((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).2 : ℝ))
      _ = (d₃.1 + d₃.2 : ℝ) := lattice_attachment_endpoint_l1_eq vHat d₃
      _ = (m : ℝ) := by exact_mod_cast hSuffixLength
  have hRadius : (δ * s / 2) + (m : ℝ) ≤ δ * s := by linarith
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hAttachmentRadius : (m : ℝ) ≤ δ * s := by linarith [hScale, hm0]
  constructor
  · intro i
    rcases Path.concat_vertex_in_piece p (qAligned.concat rAligned) i with hp | htail
    · rcases hp with ⟨j, hji⟩
      have hprefix :
          (|((p.vertex j).1 : ℝ) - (u.1 : ℝ)| + |((p.vertex j).2 : ℝ) - (u.2 : ℝ)|) ≤ (m : ℝ) := by
        calc
          (|((p.vertex j).1 : ℝ) - (u.1 : ℝ)| + |((p.vertex j).2 : ℝ) - (u.2 : ℝ)|) ≤
              (d₁.1 + d₁.2 : ℝ) := p.vertex_l1_from_start_le_length j
          _ = (m : ℝ) := by exact_mod_cast hPrefixLength
      refine ⟨0, by norm_num, by norm_num, ?_⟩
      rw [hji]
      simpa [] using le_trans hprefix hAttachmentRadius
    · rcases htail with ⟨j, hji⟩
      rcases Path.concat_vertex_in_piece qAligned rAligned j with hq | hr
      · rcases hq with ⟨k, hjk⟩
        obtain ⟨t, ht0, ht1, hnear⟩ := hMiddle k
        have htrans := realPoint_attachment_segment_transfer
          ((q.vertex k).1, (q.vertex k).2) u uHat vHat v (δ * s / 2) m t
          ht0 ht1 hnear (le_of_eq hAttachmentStart) (le_of_eq hAttachmentFinish)
        refine ⟨t, ht0, ht1, ?_⟩
        rw [hji, hjk, hqVertex k]
        exact le_trans htrans hRadius
      · rcases hr with ⟨k, hjk⟩
        have hsuffix :
            (|((r.vertex k).1 : ℝ) - (v.1 : ℝ)| + |((r.vertex k).2 : ℝ) - (v.2 : ℝ)|) ≤
              (m : ℝ) := by
          calc
            (|((r.vertex k).1 : ℝ) - (v.1 : ℝ)| + |((r.vertex k).2 : ℝ) - (v.2 : ℝ)|) ≤
                (|((r.vertex k).1 : ℝ) - (((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).1))| + |((r.vertex k).2 : ℝ) - (((vHat + ((d₃.1 : ℤ), (d₃.2 : ℤ))).2))|) := by rw [hV]
            _ ≤ (d₃.1 + d₃.2 : ℝ) := r.vertex_l1_to_finish_le_length k
            _ = (m : ℝ) := by exact_mod_cast hSuffixLength
        refine ⟨1, by norm_num, by norm_num, ?_⟩
        rw [hji, hjk, hrVertex k]
        simpa [] using le_trans hsuffix hAttachmentRadius
  · have hTotal :
        u + (((d₁ + (d₂ + d₃)).1 : ℤ), ((d₁ + (d₂ + d₃)).2 : ℤ)) =
          ((u + ((d₁.1 : ℤ), (d₁.2 : ℤ))) + ((d₂.1 : ℤ), (d₂.2 : ℤ))) +
            ((d₃.1 : ℤ), (d₃.2 : ℤ)) := by
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> ring
    calc
      joined.vertex (Fin.last ((d₁ + (d₂ + d₃)).1 + (d₁ + (d₂ + d₃)).2)) =
          u + (((d₁ + (d₂ + d₃)).1 : ℤ), ((d₁ + (d₂ + d₃)).2 : ℤ)) := joined.finish
      _ = ((u + ((d₁.1 : ℤ), (d₁.2 : ℤ))) + ((d₂.1 : ℤ), (d₂.2 : ℤ))) +
          ((d₃.1 : ℤ), (d₃.2 : ℤ)) := hTotal
      _ = v := by rw [← hQEnd, hV]

end LPPDifferentiability

end
