import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_501 :
    ∀ φ : PEqualNP.Search.CNF,
      ((fun φ : PEqualNP.Search.CNF =>
          φ.map (fun c : PEqualNP.Search.Clause =>
            c.map (fun l : PEqualNP.Search.Literal =>
              ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx
                (fun o : Option PEqualNP.Search.Literal =>
                  o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map List.length =
        φ.map List.length ∧
      ∀ c ∈ (fun φ : PEqualNP.Search.CNF =>
          φ.map (fun c : PEqualNP.Search.Clause =>
            c.map (fun l : PEqualNP.Search.Literal =>
              ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx
                (fun o : Option PEqualNP.Search.Literal =>
                  o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ,
        ∀ l ∈ c,
          l.1 < (((fun φ : PEqualNP.Search.CNF =>
              φ.map (fun c : PEqualNP.Search.Clause =>
                c.map (fun l : PEqualNP.Search.Literal =>
                  ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx
                    (fun o : Option PEqualNP.Search.Literal =>
                      o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map
            (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
  intro φ
  constructor
  · simp [List.map_map, Function.comp_def]
  · intro c hc l hl
    rcases List.mem_map.mp hc with ⟨c₀, hc₀, rfl⟩
    rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
    dsimp only
    let items : List (Option PEqualNP.Search.Literal) :=
      φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])
    have hmem : some l₀ ∈ items := by
      refine List.mem_flatMap.mpr ⟨c₀, hc₀, ?_⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨l₀, hl₀, rfl⟩)
    have hlt :
        items.findIdx
            (fun o : Option PEqualNP.Search.Literal =>
              o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l₀.1)) <
          items.length :=
      List.findIdx_lt_length_of_exists ⟨some l₀, hmem, by simp⟩
    have hlen :
        items.length =
          ((φ.map (fun c : PEqualNP.Search.Clause =>
              c.map (fun l : PEqualNP.Search.Literal =>
                (items.findIdx (fun o : Option PEqualNP.Search.Literal =>
                  o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))).map
            (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
      simp [items, List.length_flatMap, List.map_map, Function.comp_def]
    exact hlen ▸ hlt
