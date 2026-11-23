import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.Search

theorem L_meta_489_clause_len (c : Clause) :
    c.length + 1 ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [encodeClause]
  | cons l c ih =>
    simp [encodeClause, encodeLiteral] at ih ⊢
    omega

theorem L_meta_489_len (φ : CNF) :
    (φ.flatMap (fun c => c.map some ++ [none])).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    simp only [encodeCNF, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, List.length_nil] at ih ⊢
    have := L_meta_489_clause_len c
    omega

theorem L_meta_489_mem (φ : CNF) (z : ℕ)
    (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
    ∃ o ∈ φ.flatMap (fun c => c.map some ++ [none]), o.any (fun l => l.1 == z) = true := by
  simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap,
    List.mem_map] at hz
  obtain ⟨c, hc, l, hl, rfl⟩ := hz
  refine ⟨some l, ?_, by simp⟩
  simp only [List.mem_flatMap, List.mem_append, List.mem_map]
  exact ⟨c, hc, Or.inl ⟨l, hl, rfl⟩⟩

theorem L_meta_489 : ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < (PEqualNP.Search.encodeCNF φ).length) ∧ ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z' := by
  intro φ e he
  have hlt : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      e z < (φ.flatMap (fun c => c.map some ++ [none])).length := by
    intro z hz
    obtain ⟨o, ho, hp⟩ := L_meta_489_mem φ z hz
    rw [he z]
    exact List.findIdx_lt_length_of_exists ⟨o, ho, hp⟩
  refine ⟨fun z hz => lt_of_lt_of_le (hlt z hz) (L_meta_489_len φ), ?_⟩
  intro z hz z' hz' heq
  have h1 := hlt z hz
  have h2 := hlt z' hz'
  rw [he z] at h1
  rw [he z'] at h2
  have p1 := List.findIdx_getElem (w := h1)
  have p2 := List.findIdx_getElem (w := h2)
  have hidx := heq
  rw [he z, he z'] at hidx
  simp only [hidx] at p1
  generalize (φ.flatMap (fun c => c.map some ++ [none]))[
    (φ.flatMap (fun c => c.map some ++ [none])).findIdx
      (fun o => o.any (fun l => l.1 == z'))] = o at p1 p2
  cases o with
  | none => simp at p1
  | some l =>
    simp only [Option.any_some, beq_iff_eq] at p1 p2
    rw [← p1, ← p2]

end PEqualNP.Outside
