import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Aux489

private theorem lit_len (c : PEqualNP.Search.Clause) :
    c.length ≤ (c.flatMap PEqualNP.Search.encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      PEqualNP.Search.encodeLiteral] at ih ⊢
    omega

private theorem items_len (φ : PEqualNP.Search.CNF) :
    (φ.flatMap (fun c => c.map some ++ [none])).length ≤
      (PEqualNP.Search.encodeCNF φ).length := by
  induction φ with
  | nil => simp [PEqualNP.Search.encodeCNF]
  | cons c φ ih =>
    have hc := lit_len c
    simp only [PEqualNP.Search.encodeCNF, PEqualNP.Search.encodeClause, List.flatMap_cons,
      List.length_append, List.length_cons, List.length_map, List.length_nil] at ih ⊢
    omega

private theorem items_ex (φ : PEqualNP.Search.CNF) (z : ℕ)
    (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
    ∃ o ∈ φ.flatMap (fun c => c.map some ++ [none]),
      (fun o : Option PEqualNP.Search.Literal => o.any (fun l => l.1 == z)) o = true := by
  simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap,
    List.mem_map] at hz
  obtain ⟨c, hc, l, hl, rfl⟩ := hz
  refine ⟨some l, ?_, by simp⟩
  simp only [List.mem_flatMap]
  exact ⟨c, hc, by simp [hl]⟩

private theorem same_item (I : List (Option PEqualNP.Search.Literal)) (z z' : ℕ) (i j : ℕ)
    (hi : i < I.length) (hj : j < I.length) (hij : i = j)
    (a : (I[i]).any (fun l => l.1 == z) = true)
    (b : (I[j]).any (fun l => l.1 == z') = true) : z = z' := by
  subst hij
  cases hI : I[i] with
  | none => simp [hI] at a
  | some l =>
    simp only [hI, Option.any_some, beq_iff_eq] at a b
    exact a.symm.trans b

end PEqualNP.Outside.Aux489

theorem PEqualNP.Outside.L_meta_489 : ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < (PEqualNP.Search.encodeCNF φ).length) ∧ ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z' := by
  intro φ e he
  constructor
  · intro z hz
    rw [he z]
    exact lt_of_lt_of_le
      (List.findIdx_lt_length_of_exists (PEqualNP.Outside.Aux489.items_ex φ z hz))
      (PEqualNP.Outside.Aux489.items_len φ)
  · intro z hz z' hz' h
    rw [he z, he z'] at h
    have hlt := List.findIdx_lt_length_of_exists (PEqualNP.Outside.Aux489.items_ex φ z hz)
    have hlt' := List.findIdx_lt_length_of_exists (PEqualNP.Outside.Aux489.items_ex φ z' hz')
    exact PEqualNP.Outside.Aux489.same_item _ z z' _ _ hlt hlt' h
      (List.findIdx_getElem (w := hlt)) (List.findIdx_getElem (w := hlt'))
