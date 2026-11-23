import PEqualNP.Defs

namespace PEqualNP.Outside

theorem L_meta_495 :
    ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ),
      (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) →
      ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
        (∃ l : PEqualNP.Search.Literal,
          (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) ∧
        ∀ g < e z, ∀ l : PEqualNP.Search.Literal,
          (φ.flatMap (fun c => c.map some ++ [none]))[g]? = some (some l) → l.1 ≠ z := by
  intro φ e he z hz
  let L : List (Option PEqualNP.Search.Literal) := φ.flatMap (fun c => c.map some ++ [none])
  let p : Option PEqualNP.Search.Literal → Bool := fun o => o.any (fun l => l.1 == z)
  have hex : ∃ x ∈ L, p x = true := by
    simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap,
      List.mem_map] at hz
    rcases hz with ⟨c, hc, l, hl, rfl⟩
    refine ⟨some l, ?_, by simp [p]⟩
    rw [List.mem_flatMap]
    exact ⟨c, hc, List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)⟩
  have hlt : L.findIdx p < L.length := List.findIdx_lt_length_of_exists hex
  have hget : p L[L.findIdx p] = true := List.findIdx_getElem (w := hlt)
  constructor
  · change ∃ l : PEqualNP.Search.Literal, L[e z]? = some (some l) ∧ l.1 = z
    rw [he z, List.getElem?_eq_getElem hlt]
    cases hval : L[L.findIdx p] with
    | none => simp [p, hval] at hget
    | some l' =>
      refine ⟨l', rfl, ?_⟩
      simpa [p, hval] using hget
  · intro g hg l' hgl
    change L[g]? = some (some l') at hgl
    rw [he z] at hg
    have hglt : g < L.length := lt_trans hg hlt
    rw [List.getElem?_eq_getElem hglt] at hgl
    have hfalse : p L[g] = false := List.not_of_lt_findIdx hg
    injection hgl with hval
    rw [hval] at hfalse
    simpa [p] using hfalse

end PEqualNP.Outside
