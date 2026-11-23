import Mathlib
import PEqualNP.Defs

theorem L_meta_494_lit_len_ge (l : PEqualNP.Search.Literal) : 4 ≤ (PEqualNP.Search.encodeLiteral l).length := by
  simp [PEqualNP.Search.encodeLiteral]

theorem L_meta_494_clause_len_ge (c : PEqualNP.Search.Clause) :
    4 * c.length + 2 ≤ (PEqualNP.Search.encodeClause c).length := by
  induction c with
  | nil => simp [PEqualNP.Search.encodeClause]
  | cons l t ih =>
    have h := L_meta_494_lit_len_ge l
    simp only [PEqualNP.Search.encodeClause, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    omega

theorem L_meta_494_cnf_len_ge (φ : PEqualNP.Search.CNF) :
    4 * (φ.map List.length).sum + 2 * φ.length ≤ (PEqualNP.Search.encodeCNF φ).length := by
  induction φ with
  | nil => simp [PEqualNP.Search.encodeCNF]
  | cons c t ih =>
    have h := L_meta_494_clause_len_ge c
    simp only [PEqualNP.Search.encodeCNF, List.flatMap_cons, List.length_append,
      List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem L_meta_494_sum_succ_eq (φ : PEqualNP.Search.CNF) :
    (φ.map (fun c => c.length + 1)).sum = (φ.map List.length).sum + φ.length := by
  induction φ with
  | nil => simp
  | cons c t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem PEqualNP.Outside.L_meta_494 : ∀ φ : PEqualNP.Search.CNF, 4 * (φ.map List.length).sum + 2 * φ.length ≤ (PEqualNP.Search.encodeCNF φ).length ∧ 2 * (φ.map (fun c => c.length + 1)).sum ≤ (PEqualNP.Search.encodeCNF φ).length := by
  intro φ
  have h1 := L_meta_494_cnf_len_ge φ
  have h2 := L_meta_494_sum_succ_eq φ
  constructor
  · exact h1
  · rw [h2]
    omega
