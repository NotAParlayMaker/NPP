import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_495 : ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, (∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) ∧ ∀ g < e z, ∀ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[g]? = some (some l) → l.1 ≠ z := by
  intro φ e he z hz
  set L := φ.flatMap (fun c => c.map some ++ [none]) with hL
  simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset,
    List.mem_flatMap, List.mem_map] at hz
  obtain ⟨c, hc, l, hl, hzl⟩ := hz
  have hmem : some l ∈ L := by
    rw [hL]
    exact List.mem_flatMap.mpr ⟨c, hc,
      List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)⟩
  have hp : (some l).any (fun m => m.1 == z) := beq_iff_eq.mpr hzl
  have hex : ∃ o ∈ L, (fun o => o.any (fun m => m.1 == z)) o := ⟨some l, hmem, hp⟩
  have hlt : e z < L.length := by
    rw [he z]
    exact List.findIdx_lt_length.mpr hex
  have hget : L[e z]? = some (L[e z]'hlt) := List.getElem?_eq_getElem hlt
  have hval : Option.any (fun m => m.1 == z) (L[e z]'hlt) := by
    have hget' : L[L.findIdx (fun o => o.any (fun m => m.1 == z))]? =
        some (L[e z]'hlt) := by
      rw [← he z]
      exact hget
    exact List.findIdx_of_getElem?_eq_some hget'
  obtain ⟨l', hl', hpl'⟩ := (Option.any_eq_true _ _).mp hval
  refine ⟨⟨l', ?_, beq_iff_eq.mp hpl'⟩, ?_⟩
  · exact hget.trans (congrArg some hl')
  · intro g hg l' hgL
    rw [he z] at hg
    have hpf := List.not_of_lt_findIdx hg
    obtain ⟨hglt, hge⟩ := List.getElem?_eq_some_iff.mp hgL
    have hff : (l'.1 == z) = false := (Option.any_eq_false _ _).mp hpf l' hge
    intro hcontra
    simp [hcontra] at hff
