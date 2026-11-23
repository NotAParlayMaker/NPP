import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_495 : ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, (∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) ∧ ∀ g < e z, ∀ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[g]? = some (some l) → l.1 ≠ z := by
  classical
  intro φ e he z hz
  have hzList : z ∈ φ.flatMap (List.map Prod.fst) := by
    simpa only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset] using hz
  let xs : List (Option PEqualNP.Search.Literal) := φ.flatMap (fun c => c.map some ++ [none])
  let p : Option PEqualNP.Search.Literal → Bool := fun o => o.any (fun l => l.1 == z)
  have hidx : e z = xs.findIdx p := by
    simpa [xs, p] using he z
  have hzsome : ∃ l : PEqualNP.Search.Literal, some l ∈ xs ∧ l.1 = z := by
    rcases List.mem_flatMap.mp hzList with ⟨c, hc, hzc⟩
    rcases List.mem_map.mp hzc with ⟨l, hl, hzl⟩
    refine ⟨l, ?_, ?_⟩
    · exact List.mem_flatMap.mpr
        ⟨c, hc, List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨l, hl, rfl⟩))⟩
    · exact hzl
  have hpExists : ∃ o ∈ xs, p o := by
    rcases hzsome with ⟨l, hmem, hvar⟩
    refine ⟨some l, hmem, ?_⟩
    simp [p, hvar]
  have hi : xs.findIdx p < xs.length :=
    List.findIdx_lt_length_of_exists hpExists
  have hseen : p xs[xs.findIdx p] :=
    List.findIdx_getElem (w := hi)
  have hf : ∃ l : PEqualNP.Search.Literal,
      xs[xs.findIdx p]? = some (some l) ∧ l.1 = z := by
    cases hv : xs[xs.findIdx p] with
    | none =>
      simp [p, hv] at hseen
    | some l =>
      refine ⟨l, ?_, ?_⟩
      · simpa [hv] using (List.getElem?_eq_getElem hi : xs[xs.findIdx p]? =
          some xs[xs.findIdx p])
      · simpa [p, hv] using hseen
  constructor
  · simpa [xs, hidx] using hf
  · intro g hg l hget hbad
    have hg' : g < xs.findIdx p := by simpa [hidx] using hg
    have hgLen : g < xs.length := Nat.lt_trans hg' hi
    have hnot : p xs[g] = false :=
      List.not_of_lt_findIdx hg'
    have helem : xs[g] = some l := by
      have hget' : xs[g]? = some (some l) := by simpa [xs] using hget
      simpa [List.getElem?_eq_getElem hgLen] using hget'
    have hfalse : p (some l) = false := by simpa [helem] using hnot
    simp [p, hbad] at hfalse
