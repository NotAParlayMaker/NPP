import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2706_2 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.MetaComplexity.Monotone2 x1 →
        x2 < (14 : ℕ) + x1.size →
          x3 < (14 : ℕ) + x1.size →
            (14 : ℕ) ≤ x2 →
              (14 : ℕ) ≤ x3 →
                x2 < x3 →
                  (x1.gates[x2 - (14 : ℕ)]?.map PEqualNP.CircuitLowerBounds.Gate.op) =
                    some PEqualNP.CircuitLowerBounds.GateOp.or →
                  (x1.gates[x3 - (14 : ℕ)]?.map PEqualNP.CircuitLowerBounds.Gate.op) =
                    some PEqualNP.CircuitLowerBounds.GateOp.or →
                  have x7 : List (ℕ × ℕ) :=
                    [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)),
                     ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)),
                     ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)),
                     ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)),
                     ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)),
                     ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)),
                     ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
                  have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) =>
                    ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)),
                      (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;
                  have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool :=
                    fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) =>
                      (x1.wires (List.ofFn x10)).getD x9 Bool.false;
                  (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) →
                    (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) →
                      (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) →
                        (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) →
                          (26 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.MetaComplexity.Monotone2 x1 →
        x2 < (14 : ℕ) + x1.size →
          x3 < (14 : ℕ) + x1.size →
            (14 : ℕ) ≤ x2 →
              (14 : ℕ) ≤ x3 →
                x2 ≠ x3 →
                  (x1.gates[x2 - (14 : ℕ)]?.map PEqualNP.CircuitLowerBounds.Gate.op) =
                    some PEqualNP.CircuitLowerBounds.GateOp.and →
                  have x7 : List (ℕ × ℕ) :=
                    [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)),
                     ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)),
                     ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)),
                     ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)),
                     ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)),
                     ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)),
                     ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
                  have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) =>
                    ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)),
                      (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;
                  have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool :=
                    fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) =>
                      (x1.wires (List.ofFn x10)).getD x9 Bool.false;
                  (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) →
                    (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) →
                      (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) →
                        (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) →
                          (26 : ℕ) ≤ x1.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.MetaComplexity.Monotone2 x1 →
        x2 < (14 : ℕ) + x1.size →
          x3 < (14 : ℕ) + x1.size →
            have x7 : List (ℕ × ℕ) :=
              [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)),
               ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)),
               ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)),
               ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)),
               ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)),
               ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)),
               ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
            have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) =>
              ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)),
                (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;
            have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool :=
              fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) =>
                (x1.wires (List.ofFn x10)).getD x9 Bool.false;
            (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) →
              (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) →
                (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) →
                  (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) →
                    (26 : ℕ) ≤ x1.size := by
  intro hBothOr hFirstAnd x1 x2 x3 hmono hx2 hx3 x7 x8 x9 hcover hfalse h2only h3only
  let edges : List (ℕ × ℕ) :=
    [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)),
     ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)),
     ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)),
     ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)),
     ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)),
     ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)),
     ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]
  have hwireIn :
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
        i < w.length →
          (gs.foldl (fun acc g =>
            acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w).getD i false =
            w.getD i false := by
    intro gs
    induction gs with
    | nil =>
        intro w i _
        rfl
    | cons g gs ih =>
        intro w i hi
        have hlen : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
          simp [List.length_append]
          omega
        rw [List.foldl_cons, ih _ i hlen]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hEdgeNe : ∀ p ∈ edges, p.1 ≠ p.2 := by decide
  have hge14 :
      ∀ k : ℕ,
        (∀ x : Fin 14 → Bool,
          ¬(∃ a b : Fin 14, (↑a, ↑b) ∈ edges ∧ x a = true ∧ x b = true) →
            (x1.wires (List.ofFn x)).getD k false = false) →
        14 ≤ k := by
    intro k hkfalse
    by_contra hlt
    push Not at hlt
    let s : Fin 14 → Bool := fun i => decide (i.val = k)
    have hns : ¬(∃ a b : Fin 14, (↑a, ↑b) ∈ edges ∧ s a = true ∧ s b = true) := by
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a.val = k := by simpa [s] using ha
      have hb' : b.val = k := by simpa [s] using hb
      exact hEdgeNe (a.val, b.val) hab (ha'.trans hb'.symm)
    have hf : (x1.wires (List.ofFn s)).getD k false = false := hkfalse s hns
    change (x1.gates.foldl (fun acc g =>
      acc ++ [g.op.eval (g.inputs.map fun m => acc.getD m false)]) (List.ofFn s)).getD k false = false at hf
    have hlen : k < (List.ofFn s).length := by
      simp [hlt]
    rw [hwireIn x1.gates (List.ofFn s) k hlen] at hf
    have hof : (List.ofFn s).getD k false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn]
      simp [s]
    rw [hof] at hf
    exact Bool.noConfusion hf
  have h14_2 : 14 ≤ x2 := hge14 x2 (fun x hx => (hfalse x hx).1)
  have h14_3 : 14 ≤ x3 := hge14 x3 (fun x hx => (hfalse x hx).2)
  have hne23 : x2 ≠ x3 := by
    rintro rfl
    rcases h2only with ⟨x, _, ht, hf⟩
    rw [ht] at hf
    exact Bool.noConfusion hf
  have hlt2 : x2 - 14 < x1.gates.length := by
    change x2 < 14 + x1.gates.length at hx2
    omega
  have hlt3 : x3 - 14 < x1.gates.length := by
    change x3 < 14 + x1.gates.length at hx3
    omega
  have hm :
      ∀ g ∈ x1.gates,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := hmono
  have hop2 :
      x1.gates[x2 - 14].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        x1.gates[x2 - 14].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm _ (List.getElem_mem hlt2)).1
  have hop3 :
      x1.gates[x3 - 14].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        x1.gates[x3 - 14].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm _ (List.getElem_mem hlt3)).1
  have hget2 : x1.gates[x2 - 14]? = some x1.gates[x2 - 14] := List.getElem?_eq_getElem hlt2
  have hget3 : x1.gates[x3 - 14]? = some x1.gates[x3 - 14] := List.getElem?_eq_getElem hlt3
  rcases hop2 with h2and | h2or
  · exact hFirstAnd x1 x2 x3 hmono hx2 hx3 h14_2 h14_3 hne23
      (by rw [hget2, Option.map_some, h2and]) hcover hfalse h2only h3only
  · rcases hop3 with h3and | h3or
    · exact hFirstAnd x1 x3 x2 hmono hx3 hx2 h14_3 h14_2 (Ne.symm hne23)
        (by rw [hget3, Option.map_some, h3and])
        (fun x hx => (hcover x hx).symm)
        (fun x hx => ⟨(hfalse x hx).2, (hfalse x hx).1⟩)
        h3only h2only
    · rcases lt_or_gt_of_ne hne23 with hlt | hgt
      · exact hBothOr x1 x2 x3 hmono hx2 hx3 h14_2 h14_3 hlt
          (by rw [hget2, Option.map_some, h2or])
          (by rw [hget3, Option.map_some, h3or])
          hcover hfalse h2only h3only
      · exact hBothOr x1 x3 x2 hmono hx3 hx2 h14_3 h14_2 hgt
          (by rw [hget3, Option.map_some, h3or])
          (by rw [hget2, Option.map_some, h2or])
          (fun x hx => (hcover x hx).symm)
          (fun x hx => ⟨(hfalse x hx).2, (hfalse x hx).1⟩)
          h3only h2only
