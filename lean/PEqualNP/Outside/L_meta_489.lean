import Mathlib
import PEqualNP.Defs

namespace Meta489

open PEqualNP.Search

private def tokens (φ : CNF) : List (Option Literal) :=
  φ.flatMap (fun c => c.map some ++ [none])

private theorem clause_length_bound (c : Clause) : c.length+1 ≤ (encodeClause c).length := by
  induction c with
  | nil => decide
  | cons x xs ih =>
    simp [encodeClause,encodeLiteral,List.length_flatMap] at *
    omega

private theorem tokens_bounded (φ : CNF) : (tokens φ).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    change ((c.map some ++ [none]) ++ tokens cs).length ≤ (encodeClause c ++ encodeCNF cs).length
    simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]
    have := clause_length_bound c
    omega

end Meta489

theorem PEqualNP.Outside.L_meta_489 : ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < (PEqualNP.Search.encodeCNF φ).length) ∧ ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z' := by
  intro φ e he
  let xs := Meta489.tokens φ
  let matchVar (z : ℕ) (o : Option PEqualNP.Search.Literal) := o.any (fun l => l.1 == z)
  have found (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
      ∃ o ∈ xs, matchVar z o = true := by
    simp only [PEqualNP.MetaComplexity.CoverPromise.vars,List.mem_toFinset,
      List.mem_flatMap,List.mem_map] at hz
    obtain ⟨cl,hcl,l,hl,heq⟩ := hz
    refine ⟨some l,List.mem_flatMap.mpr ⟨cl,hcl,List.mem_append_left _ (List.mem_map_of_mem hl)⟩,?_⟩
    simp [matchVar,heq]
  have idx (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
      e z < xs.length := by
    rw [he]
    exact List.findIdx_lt_length_of_exists (found z hz)
  have varAt (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
      (xs[e z]?.join.map Prod.fst) = some z := by
    have h := idx z hz
    have p : matchVar z xs[e z] = true := by
      have hit := @List.findIdx_getElem _ (matchVar z) xs (List.findIdx_lt_length_of_exists (found z hz))
      have hidx : e z = xs.findIdx (matchVar z) := he z
      simpa only [hidx] using hit
    rw [List.getElem?_eq_getElem h]
    cases ht : xs[e z] with
    | none => simp [ht,matchVar] at p
    | some l => simpa [ht,matchVar] using p
  constructor
  · exact fun z hz => (idx z hz).trans_le (Meta489.tokens_bounded φ)
  · intro z hz z' hz' eq
    have h := varAt z hz
    rw [eq,varAt z' hz'] at h
    exact (Option.some.inj h).symm
