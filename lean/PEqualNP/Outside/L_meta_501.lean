import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_501 : ∀ φ : PEqualNP.Search.CNF, ((fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map List.length = φ.map List.length ∧ ∀ c ∈ (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ, ∀ l ∈ c, l.1 < (((fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
  intro φ
  constructor
  · simp only [List.map_map, Function.comp_def, List.length_map]
  · intro c hc l hl
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    have hmem : some l₀ ∈ φ.flatMap
        (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none]) :=
      List.mem_flatMap.mpr ⟨c₀, hc₀,
        List.mem_append_left _ (List.mem_map.mpr ⟨l₀, hl₀, rfl⟩)⟩
    have hidx := List.findIdx_lt_length_of_exists
      (p := fun o : Option PEqualNP.Search.Literal =>
        o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l₀.1))
      ⟨some l₀, hmem, by simp⟩
    simpa only [List.map_map, Function.comp_def, List.length_map, List.length_flatMap,
      List.length_append, List.length_singleton] using hidx
