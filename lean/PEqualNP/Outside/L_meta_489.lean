import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L489

def items (φ : PEqualNP.Search.CNF) : List (Option PEqualNP.Search.Literal) :=
  φ.flatMap (fun c => c.map some ++ [none])

def pz (z : ℕ) : Option PEqualNP.Search.Literal → Bool :=
  fun o => o.any (fun l => l.1 == z)

theorem len_enc (l : PEqualNP.Search.Literal) : 1 ≤ (PEqualNP.Search.encodeLiteral l).length := by
  simp only [PEqualNP.Search.encodeLiteral, List.length_append, List.length_cons, List.length_nil]
  omega

theorem len_flat (c : PEqualNP.Search.Clause) :
    c.length ≤ (c.flatMap PEqualNP.Search.encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := len_enc l
    omega

theorem len_clause (c : PEqualNP.Search.Clause) :
    c.length + 1 ≤ (PEqualNP.Search.encodeClause c).length := by
  unfold PEqualNP.Search.encodeClause
  have := len_flat c
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem len_items (φ : PEqualNP.Search.CNF) :
    (items φ).length ≤ (PEqualNP.Search.encodeCNF φ).length := by
  unfold items PEqualNP.Search.encodeCNF
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_singleton]
    have := len_clause c
    omega

theorem mem_items (φ : PEqualNP.Search.CNF) (z : ℕ)
    (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) : ∃ o ∈ items φ, pz z o = true := by
  rw [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap] at hz
  obtain ⟨c, hc, hzc⟩ := hz
  rw [List.mem_map] at hzc
  obtain ⟨l, hl, hlz⟩ := hzc
  unfold items
  refine ⟨some l, List.mem_flatMap.2 ⟨c, hc, List.mem_append_left _ (List.mem_map.2 ⟨l, hl, rfl⟩)⟩, ?_⟩
  simp [pz, hlz]

theorem pz_some (z : ℕ) (o : Option PEqualNP.Search.Literal) (h : pz z o = true) :
    ∃ l, o = some l ∧ l.1 = z := by
  cases o with
  | none => simp [pz] at h
  | some l => exact ⟨l, rfl, by simpa [pz] using h⟩

end PEqualNP.Outside.L489

theorem PEqualNP.Outside.L_meta_489 :
    ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < (PEqualNP.Search.encodeCNF φ).length) ∧ ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z' := by
  intro φ e he
  have he' : ∀ z, e z = (PEqualNP.Outside.L489.items φ).findIdx (PEqualNP.Outside.L489.pz z) := he
  have key : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      e z < (PEqualNP.Outside.L489.items φ).length ∧
        ∃ o, (PEqualNP.Outside.L489.items φ)[e z]? = some o ∧ PEqualNP.Outside.L489.pz z o = true := by
    intro z hz
    have hex := PEqualNP.Outside.L489.mem_items φ z hz
    have hw := List.findIdx_lt_length_of_exists hex
    rw [he' z]
    exact ⟨hw, _, List.findIdx_getElem?_eq_getElem_of_exists hex, List.findIdx_getElem (w := hw)⟩
  refine ⟨fun z hz => lt_of_lt_of_le (key z hz).1 (PEqualNP.Outside.L489.len_items φ), ?_⟩
  intro z hz z' hz' hzz
  obtain ⟨o, ho, hpo⟩ := (key z hz).2
  obtain ⟨o', ho', hpo'⟩ := (key z' hz').2
  rw [hzz, ho'] at ho
  obtain ⟨l, hol, hl⟩ := PEqualNP.Outside.L489.pz_some z o hpo
  obtain ⟨l', hol', hl'⟩ := PEqualNP.Outside.L489.pz_some z' o' hpo'
  rw [hol, hol'] at ho
  have hll : l' = l := Option.some.inj (Option.some.inj ho)
  rw [← hl, ← hl', hll]
