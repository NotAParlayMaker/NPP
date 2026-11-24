import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3172_2
    (base : ∀ (a b : Fin 9) (i : Fin 11), ∃ x : Fin 9 → Bool, (List.ofFn x ++ [!x 0, x a || x b]).getD i.val false ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (last_and : ∀ a ∈ ({2,3,8} : Finset (Fin 9)), ∀ b ∈ ({2,3,8} : Finset (Fin 9)), ∀ (gs : List Gate),
      FanInTwo ⟨gs, 0⟩ → gs.length ≤ 12 → ∀ ins : List ℕ, ins.length ≤ 2 →
      ∃ x : Fin 9 → Bool, GateOp.and.eval
        (ins.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x ++ [!x 0, x a || x b])).getD i false)) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (last_or : ∀ a ∈ ({2,3,8} : Finset (Fin 9)), ∀ b ∈ ({2,3,8} : Finset (Fin 9)), ∀ (gs : List Gate),
      FanInTwo ⟨gs, 0⟩ → gs.length ≤ 12 → ∀ ins : List ℕ, ins.length ≤ 2 →
      ∃ x : Fin 9 → Bool, GateOp.or.eval
        (ins.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x ++ [!x 0, x a || x b])).getD i false)) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (last_not : ∀ a ∈ ({2,3,8} : Finset (Fin 9)), ∀ b ∈ ({2,3,8} : Finset (Fin 9)), ∀ (gs : List Gate),
      FanInTwo ⟨gs, 0⟩ → gs.length ≤ 12 → ∀ ins : List ℕ, ins.length ≤ 2 →
      ∃ x : Fin 9 → Bool, GateOp.not.eval
        (ins.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x ++ [!x 0, x a || x b])).getD i false)) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  classical
  intro ls hl _ allowed
  obtain ⟨u,v,rfl⟩ : ∃ u v : ℕ, ls = [u,v] := by
    cases ls with
    | nil => simp at hl
    | cons u tail =>
      cases tail with
      | nil => simp at hl
      | cons v rest =>
        have : rest = [] := by simpa using hl
        subst rest
        exact ⟨_,_,rfl⟩
  have hu := allowed u (by simp)
  have hv := allowed v (by simp)
  let a : Fin 9 := ⟨u, by omega⟩
  let b : Fin 9 := ⟨v, by omega⟩
  have ha : a ∈ ({2,3,8} : Finset (Fin 9)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; exact hu
  have hb : b ∈ ({2,3,8} : Finset (Fin 9)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; exact hv
  let inp (x : Fin 9 → Bool) := (List.ofFn x ++ [!x 0, x a || x b])
  let target (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  have sz (gs : List Gate) (x : Fin 9 → Bool) :
      ((Circuit.mk gs 0).wires (inp x)).length = 11+gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [Circuit.wires, inp]
    | append_singleton gs g ih =>
      simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.length_append, List.length_cons, List.length_nil] at ih ⊢
      omega
  have main (gs : List Gate) (ok : FanInTwo ⟨gs,0⟩) (bound : gs.length ≤ 13) (o : ℕ) :
      ∃ x, (Circuit.mk gs o).eval (inp x) ≠ target x := by
    induction gs using List.reverseRecOn generalizing o with
    | nil =>
      by_cases ho : o < 11
      · exact base a b ⟨o,ho⟩
      · refine ⟨fun _ => true, ?_⟩
        change (inp _).getD o false ≠ _
        rw [List.getD_eq_default _ _ (by simp [inp]; omega)]
        decide
    | append_singleton gs g ih =>
      have short : gs.length ≤ 12 := by simp only [List.length_append, List.length_cons, List.length_nil] at bound; omega
      have old : FanInTwo ⟨gs,0⟩ := fun z hz => ok z (List.mem_append_left _ hz)
      have hg := ok g (List.mem_append_right _ (by simp))
      have eval (x : Fin 9 → Bool) : (Circuit.mk (gs++[g]) o).eval (inp x) =
          (((Circuit.mk gs 0).wires (inp x)) ++ [g.op.eval (g.inputs.map
            (fun i => ((Circuit.mk gs 0).wires (inp x)).getD i false))]).getD o false := by
        simp [Circuit.eval, Circuit.wires, List.foldl_append]
      by_cases hlt : o < 11+gs.length
      · obtain ⟨x,hx⟩ := ih old (by omega) o
        exact ⟨x, by rw [eval, List.getD_append _ _ _ _ (by simpa [sz] using hlt)]; exact hx⟩
      by_cases he : o = 11+gs.length
      · have splitOp : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using hg.1
        have bad : ∃ x, g.op.eval (g.inputs.map (fun i => ((Circuit.mk gs 0).wires (inp x)).getD i false)) ≠ target x := by
          rcases splitOp with hh | hh | hh
          · rw [hh]; exact last_and a ha b hb gs old short g.inputs hg.2
          · rw [hh]; exact last_or a ha b hb gs old short g.inputs hg.2
          · rw [hh]; exact last_not a ha b hb gs old short g.inputs hg.2
        obtain ⟨x,hx⟩ := bad
        refine ⟨x, ?_⟩
        rw [eval, List.getD_append_right _ _ _ _ (by rw [sz]; omega), sz, he, Nat.sub_self]
        exact hx
      · refine ⟨fun _ => true, ?_⟩
        rw [eval, List.getD_eq_default _ _ (by simp [sz]; omega)]
        decide
  intro C ok bound
  obtain ⟨x,hx⟩ := main C.gates ok bound C.output
  refine ⟨x, ?_⟩
  have rd (i : Fin 9) : (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_ofFn]
  change C.eval ((List.ofFn x ++ [!x 0]) ++ [((List.ofFn x ++ [!x 0]).getD a.val false || ((List.ofFn x ++ [!x 0]).getD b.val false || false))]) ≠ target x
  rw [rd a, rd b, Bool.or_false]
  exact hx
