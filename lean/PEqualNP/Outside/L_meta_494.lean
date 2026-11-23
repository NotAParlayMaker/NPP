import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_494 : ∀ φ : PEqualNP.Search.CNF, 4 * (φ.map List.length).sum + 2 * φ.length ≤ (PEqualNP.Search.encodeCNF φ).length ∧ 2 * (φ.map (fun c => c.length + 1)).sum ≤ (PEqualNP.Search.encodeCNF φ).length := by
  have hl : ∀ l : PEqualNP.Search.Literal, 4 ≤ (PEqualNP.Search.encodeLiteral l).length := by
    intro l
    simp only [PEqualNP.Search.encodeLiteral, List.length_append, List.length_cons, List.length_nil]
    omega
  have hc : ∀ c : PEqualNP.Search.Clause, 4 * c.length + 2 ≤ (PEqualNP.Search.encodeClause c).length := by
    intro c
    induction c with
    | nil => simp [PEqualNP.Search.encodeClause]
    | cons l c ih =>
      have h := hl l
      simp only [PEqualNP.Search.encodeClause, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
      omega
  intro φ
  induction φ with
  | nil => simp [PEqualNP.Search.encodeCNF]
  | cons c φ ih =>
    have h := hc c
    simp only [PEqualNP.Search.encodeCNF, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega
