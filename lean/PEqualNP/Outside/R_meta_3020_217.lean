import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3020_217
    (no_monotone_15 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ (15 : ℕ) →
        ∃ (x : Fin (9 : ℕ) → Bool),
          C.eval (List.ofFn x) ≠
            (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (with_not_base :
      ∀ (x1 : List (Fin (11 : ℕ))),
        (x1 ∈ ([[], [(10 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ))]] : List (List (Fin (11 : ℕ)))) ∨
          (x1.length = (2 : ℕ) ∧ ∃ a ∈ x1, a = (0 : Fin (11 : ℕ)) ∨ a = (4 : Fin (11 : ℕ)) ∨ a = (6 : Fin (11 : ℕ)))) →
        ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
          (∃ g ∈ x3.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
          ∃ (x6 : Fin (9 : ℕ) → Bool),
            have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];
            x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (with_not_mid :
      ∀ (x1 : List (Fin (11 : ℕ))),
        x1 ∈ ([[(1 : Fin (11 : ℕ)), (3 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))]] : List (List (Fin (11 : ℕ)))) →
        ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
          (∃ g ∈ x3.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
          ∃ (x6 : Fin (9 : ℕ) → Bool),
            have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];
            x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (with_not_hard :
      ∀ (x1 : List (Fin (11 : ℕ))),
        x1 ∈ ([[(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))]] : List (List (Fin (11 : ℕ)))) →
        ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
          (∃ g ∈ x3.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
          ∃ (x6 : Fin (9 : ℕ) → Bool),
            have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];
            x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen C hfan hsize
  let F : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let W : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 2]
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have hmap_wires : ∀ (f : ℕ → ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
        w1.length = w2.length → 11 ≤ w1.length →
        (∀ i, w2.getD (f i) false = w1.getD i false) →
        (∀ i, 11 ≤ i → f i = i) →
        (∀ i, i < 11 → f i < 11) →
        ∀ u, ((gs.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step w2).getD (f u) false =
          (gs.foldl step w1).getD u false := by
      intro f gs
      induction gs with
      | nil =>
        intro w1 w2 _ _ hag _ _ u
        exact hag u
      | cons g rest ih =>
        intro w1 w2 hleq h11 hag hge hlt u
        change ((rest.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step (step w2 ⟨g.op, g.inputs.map f⟩)).getD (f u) false =
          (rest.foldl step (step w1 g)).getD u false
        have hval : (g.inputs.map f).map (fun i => w2.getD i false) = g.inputs.map (fun i => w1.getD i false) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact hag i
        have hveq : g.op.eval ((g.inputs.map f).map fun i => w2.getD i false) =
            g.op.eval (g.inputs.map fun i => w1.getD i false) := congrArg g.op.eval hval
        apply ih (step w1 g) (step w2 ⟨g.op, g.inputs.map f⟩)
        · simp [step, hleq]
        · simp [step]; omega
        · intro i
          by_cases hi11 : i < 11
          · have hfi : f i < w2.length := by have := hlt i hi11; omega
            have hi : i < w1.length := by omega
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hfi, List.getElem?_append_left hi]
            exact hag i
          · have hfi : f i = i := hge i (by omega)
            rw [hfi]
            by_cases him : i < w1.length
            · have him2 : i < w2.length := by omega
              simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left him2, List.getElem?_append_left him]
              have := hag i
              rwa [hfi] at this
            · by_cases hieq : i = w1.length
              · have hieq2 : i = w2.length := by omega
                simp only [step, List.getD_eq_getElem?_getD]
                rw [hieq2, List.getElem?_append_right le_rfl, Nat.sub_self]
                rw [← hieq2, hieq, List.getElem?_append_right le_rfl, Nat.sub_self]
                exact congrArg (fun b => (some b).getD false) hveq
              · have hgt1 : (step w1 g).length ≤ i := by simp [step]; omega
                have hgt2 : (step w2 ⟨g.op, g.inputs.map f⟩).length ≤ i := by simp [step]; omega
                rw [List.getD_eq_default _ _ hgt2, List.getD_eq_default _ _ hgt1]
        · exact hge
        · exact hlt
    have hmap_fan : ∀ (f : ℕ → ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨C.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C.output⟩ := by
      intro f g hg
      rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
      exact ⟨(hfan g0 hg0).1, by simp [(hfan g0 hg0).2]⟩
    have hmap_size : ∀ (f : ℕ → ℕ),
        (⟨C.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size ≤ 13 := by
      intro f
      change (C.gates.map _).length ≤ 13
      rw [List.length_map]
      exact hsize
    have hmap_not : ∀ (f : ℕ → ℕ),
        ∃ g ∈ (C.gates.map fun g => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map f)), g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro f
      rcases hnot with ⟨g0, hg0, hop⟩
      exact ⟨⟨g0.op, g0.inputs.map f⟩, List.mem_map.mpr ⟨g0, hg0, rfl⟩, hop⟩
    have hrewire_same : ∀ (a : Fin 10),
        (∀ x : Fin 9 → Bool,
          PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1) =
            (W x).getD a.val false) →
        ∃ x : Fin 9 → Bool,
          C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1)]) ≠ F x := by
      intro a ha
      let f : ℕ → ℕ := fun i => if i = 10 then a.val else i
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C.output⟩
      have hsub := with_not_base [(0 : Fin 11)] (Or.inl (by simp)) C' (hmap_fan f) (hmap_size f) (hmap_not f)
      rcases hsub with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hsnoc_lt : ∀ (l : List Bool) (v : Bool) (k : ℕ), k < l.length →
          (l ++ [v]).getD k false = l.getD k false := by
        intro l v k hk
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      have hsnoc_eq : ∀ (l : List Bool) (v : Bool), (l ++ [v]).getD l.length false = v := by
        intro l v
        simp
      have heq : C'.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [(0 : Fin 11)])]) =
          C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1)]) := by
        apply hmap_wires f C.gates
        · simp [W]
        · simp [W]
        · intro i
          by_cases hi10 : i = 10
          · subst hi10
            have hfa : f 10 = a.val := rfl
            rw [hfa]
            have ha10 : a.val < (W x).length := by simp [W]
            rw [hsnoc_lt _ _ _ ha10]
            have h10 : (W x).length = 10 := by simp [W]
            conv_rhs => rw [← h10]
            rw [hsnoc_eq]
            exact (ha x).symm
          · have hfi : f i = i := if_neg hi10
            rw [hfi]
            by_cases hi10' : i < 10
            · have hiw : i < (W x).length := by simp [W]; exact hi10'
              rw [hsnoc_lt _ _ _ hiw, hsnoc_lt _ _ _ hiw]
            · have hge1 : (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [(0 : Fin 11)])]).length ≤ i := by
                simp [W]; omega
              have hge2 : (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1)]).length ≤ i := by
                simp [W]; omega
              rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
        · intro i hi; dsimp only [f]; exact if_neg (by omega)
        · intro i hi
          dsimp only [f]
          by_cases h10 : i = 10
          · subst h10; show a.val < 11; omega
          · rw [if_neg h10]; exact hi
      have hx' : C'.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [(0 : Fin 11)])]) ≠ F x := hx
      rwa [heq] at hx'
    have hgetW : ∀ (x : Fin 9 → Bool) (i : Fin 9), (W x).getD i.val false = x i := by
      intro x i
      have hi : i.val < (List.ofFn x).length := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      rw [List.getElem?_ofFn]
      simp
    have hgetW9 : ∀ (x : Fin 9 → Bool), (W x).getD 9 false = (x 0 || x 2) := by
      intro x
      simp [W]
    have hgetW10 : ∀ (x : Fin 9 → Bool), (W x).getD 10 false = false := by
      intro x
      exact List.getD_eq_default _ _ (by simp [W])
    have hand1 : ∀ b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [b] = b := by
      intro b; cases b <;> rfl
    have hand2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
      intro a b; cases a <;> cases b <;> rfl
    let sig9 : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
    let sig11 : Fin 11 → Fin 11 := ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]
    have hsig9_inv : ∀ i : Fin 9, sig9 (sig9 i) = i := by decide
    have hsigF : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
        (a2 && a1 || a1 && a0 || a0 && a5 || a5 && a7 || a7 && a2 || a2 && a3 || a1 && a6 || a0 && a4 || a5 && a8 || a3 && a4 || a6 && a8 || a8 && a3) =
        (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) := by
      decide
    have hF_sig : ∀ x : Fin 9 → Bool, F (fun i => x (sig9 i)) = F x := by
      intro x
      exact hsigF (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    have hW_sig : ∀ (x : Fin 9 → Bool) (k : Fin 11),
        (W (fun i => x (sig9 i))).getD (sig11 k).val false = (W x).getD k.val false := by
      intro x k
      fin_cases k
      · exact hgetW _ 2
      · exact hgetW _ 1
      · exact hgetW _ 0
      · exact hgetW _ 5
      · exact hgetW _ 7
      · exact hgetW _ 3
      · exact hgetW _ 6
      · exact hgetW _ 4
      · exact hgetW _ 8
      · change (W (fun i => x (sig9 i))).getD 9 false = (W x).getD 9 false
        rw [hgetW9, hgetW9]
        exact Bool.or_comm (x 2) (x 0)
      · change (W (fun i => x (sig9 i))).getD 10 false = (W x).getD 10 false
        rw [hgetW10, hgetW10]
    have hsym_pair : ∀ (a b : Fin 11),
        (∃ x : Fin 9 → Bool,
          let C' : PEqualNP.CircuitLowerBounds.Circuit :=
            ⟨C.gates.map fun g => ⟨g.op, g.inputs.map fun i => if h : i < 11 then (sig11 ⟨i, h⟩).val else i⟩,
             if h : C.output < 11 then (sig11 ⟨C.output, h⟩).val else C.output⟩
          C'.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 a, sig11 b])]) ≠ F x) →
        ∃ x : Fin 9 → Bool,
          C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b])]) ≠ F x := by
      intro a b hsub
      let f : ℕ → ℕ := fun i => if h : i < 11 then (sig11 ⟨i, h⟩).val else i
      rcases hsub with ⟨y, hy⟩
      let x : Fin 9 → Bool := fun i => y (sig9 i)
      refine ⟨x, ?_⟩
      have hxy : (fun i => x (sig9 i)) = y := by
        funext i; exact congrArg y (hsig9_inv i)
      have hFx : F x = F y := hF_sig y
      have h10 : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W y).getD (↑x8) false) [sig11 a, sig11 b]) =
          PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b]) := by
        simp only [List.map_cons, List.map_nil]
        have ha' : (W y).getD (sig11 a).val false = (W x).getD a.val false := by
          have := hW_sig x a; rwa [hxy] at this
        have hb' : (W y).getD (sig11 b).val false = (W x).getD b.val false := by
          have := hW_sig x b; rwa [hxy] at this
        rw [ha', hb']
      have hev : (⟨C.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval
            (W y ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W y).getD (↑x8) false) [sig11 a, sig11 b])]) =
          C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b])]) := by
        apply hmap_wires f C.gates
        · simp [W]
        · simp [W]
        · intro i
          by_cases hi10 : i < 10
          · have hi11 : i < 11 := by omega
            have hfi : f i = (sig11 ⟨i, hi11⟩).val := by dsimp only [f]; exact dif_pos hi11
            have hfi10 : (sig11 ⟨i, hi11⟩).val < 10 := by
              have hlt10 : ∀ k : Fin 11, k.val < 10 → (sig11 k).val < 10 := by decide
              exact hlt10 ⟨i, hi11⟩ hi10
            rw [hfi]
            have hleny : (sig11 ⟨i, hi11⟩).val < (W y).length := by simp [W]; exact hfi10
            have hlenx : i < (W x).length := by simp [W]; exact hi10
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hleny]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlenx]
            change (W y).getD (sig11 ⟨i, hi11⟩).val false = (W x).getD i false
            have hws := hW_sig x ⟨i, hi11⟩
            rw [hxy] at hws
            exact hws
          · by_cases hi_eq : i = 10
            · subst hi_eq
              have hfi : f 10 = 10 := by decide
              rw [hfi]
              have hleny : (W y).length = 10 := by simp [W]
              have hlenx : (W x).length = 10 := by simp [W]
              conv_lhs => rw [← hleny]
              conv_rhs => rw [← hlenx]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              exact h10
            · have hfi : f i = i := by dsimp only [f]; exact dif_neg (by omega)
              rw [hfi]
              have hge1 : (W y ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W y).getD (↑x8) false) [sig11 a, sig11 b])]).length ≤ i := by
                simp [W]; omega
              have hge2 : (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b])]).length ≤ i := by
                simp [W]; omega
              rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
        · intro i hi; dsimp only [f]; exact dif_neg (by omega)
        · intro i hi; dsimp only [f]; rw [dif_pos hi]; exact (sig11 ⟨i, hi⟩).isLt
      rw [← hev, hFx]
      exact hy
    have hcomm : ∀ (a b : Fin 11),
        (∃ x : Fin 9 → Bool,
          C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [b, a])]) ≠ F x) →
        ∃ x : Fin 9 → Bool,
          C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b])]) ≠ F x := by
      intro a b h
      rcases h with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hba : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [b, a]) =
          PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b]) := by
        simp only [List.map_cons, List.map_nil, hand2]
        exact Bool.and_comm _ _
      rwa [← hba]
    rcases x1 with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · exact with_not_base [] (Or.inl (by simp)) C hfan hsize hnot
    · by_cases ha10 : a = (10 : Fin 11)
      · subst ha10
        exact with_not_base [(10 : Fin 11)] (Or.inl (by simp)) C hfan hsize hnot
      · have halt : a.val < 10 := by omega
        exact hrewire_same ⟨a.val, halt⟩ (fun x => by simp only [List.map_cons, List.map_nil, hand1])
    · by_cases h10 : a = (10 : Fin 11) ∨ b = (10 : Fin 11)
      · have hsub := with_not_base [(10 : Fin 11)] (Or.inl (by simp)) C hfan hsize hnot
        rcases hsub with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        have hval : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b]) =
            PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [(10 : Fin 11)]) := by
          simp only [List.map_cons, List.map_nil, hand1, hand2]
          rcases h10 with rfl | rfl
          · change ((W x).getD 10 false && (W x).getD b.val false) = (W x).getD 10 false
            rw [hgetW10]; rfl
          · change ((W x).getD a.val false && (W x).getD 10 false) = (W x).getD 10 false
            rw [hgetW10, Bool.and_false]
        show C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [a, b])]) ≠ F x
        rw [hval]
        exact hx
      · by_cases heq : a = b
        · subst heq
          have halt : a.val < 10 := by omega
          exact hrewire_same ⟨a.val, halt⟩ (fun x => by simp only [List.map_cons, List.map_nil, hand2, Bool.and_self])
        · by_cases habs : (a = 0 ∧ b = 9) ∨ (a = 9 ∧ b = 0) ∨ (a = 2 ∧ b = 9) ∨ (a = 9 ∧ b = 2)
          · rcases habs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hrewire_same ⟨0, by decide⟩ (fun x => by
                simp only [List.map_cons, List.map_nil, hand2]
                change ((W x).getD (0 : Fin 9).val false && (W x).getD 9 false) = (W x).getD (0 : Fin 9).val false
                rw [hgetW x 0, hgetW9 x]; cases x 0 <;> rfl)
            · exact hrewire_same ⟨0, by decide⟩ (fun x => by
                simp only [List.map_cons, List.map_nil, hand2]
                change ((W x).getD 9 false && (W x).getD (0 : Fin 9).val false) = (W x).getD (0 : Fin 9).val false
                rw [hgetW x 0, hgetW9 x]; cases x 0 <;> cases x 2 <;> rfl)
            · exact hrewire_same ⟨2, by decide⟩ (fun x => by
                simp only [List.map_cons, List.map_nil, hand2]
                change ((W x).getD (2 : Fin 9).val false && (W x).getD 9 false) = (W x).getD (2 : Fin 9).val false
                rw [hgetW x 2, hgetW9 x]; cases x 0 <;> cases x 2 <;> rfl)
            · exact hrewire_same ⟨2, by decide⟩ (fun x => by
                simp only [List.map_cons, List.map_nil, hand2]
                change ((W x).getD 9 false && (W x).getD (2 : Fin 9).val false) = (W x).getD (2 : Fin 9).val false
                rw [hgetW x 2, hgetW9 x]; cases x 0 <;> cases x 2 <;> rfl)
          · let f : ℕ → ℕ := fun i => if h : i < 11 then (sig11 ⟨i, h⟩).val else i
            let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C.output⟩
            have hcl :
                (a = 0 ∨ a = 4 ∨ a = 6 ∨ b = 0 ∨ b = 4 ∨ b = 6) ∨
                (sig11 a = 0 ∨ sig11 a = 4 ∨ sig11 a = 6 ∨ sig11 b = 0 ∨ sig11 b = 4 ∨ sig11 b = 6) ∨
                [a, b] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                [b, a] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                [sig11 a, sig11 b] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                [sig11 b, sig11 a] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                [a, b] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) ∨
                [b, a] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) ∨
                [sig11 a, sig11 b] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) ∨
                [sig11 b, sig11 a] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) := by
              have hcl_all : ∀ (u v : Fin 11),
                  u = 10 ∨ v = 10 ∨ u = v ∨
                  (u = 0 ∧ v = 9) ∨ (u = 9 ∧ v = 0) ∨ (u = 2 ∧ v = 9) ∨ (u = 9 ∧ v = 2) ∨
                  (u = 0 ∨ u = 4 ∨ u = 6 ∨ v = 0 ∨ v = 4 ∨ v = 6) ∨
                  (sig11 u = 0 ∨ sig11 u = 4 ∨ sig11 u = 6 ∨ sig11 v = 0 ∨ sig11 v = 4 ∨ sig11 v = 6) ∨
                  [u, v] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                  [v, u] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                  [sig11 u, sig11 v] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                  [sig11 v, sig11 u] ∈ ([[(1 : Fin 11), 3], [1, 8], [3, 5], [8, 9]] : List (List (Fin 11))) ∨
                  [u, v] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) ∨
                  [v, u] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) ∨
                  [sig11 u, sig11 v] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) ∨
                  [sig11 v, sig11 u] ∈ ([[(1 : Fin 11), 9], [3, 8], [3, 9]] : List (List (Fin 11))) := by
                intro u v
                fin_cases u <;> fin_cases v <;> simp [sig11]
              rcases hcl_all a b with h | h | h | h | h | h | h | h
              · exact absurd (Or.inl h) h10
              · exact absurd (Or.inr h) h10
              · exact absurd h heq
              · exact absurd (Or.inl h) habs
              · exact absurd (Or.inr (Or.inl h)) habs
              · exact absurd (Or.inr (Or.inr (Or.inl h))) habs
              · exact absurd (Or.inr (Or.inr (Or.inr h))) habs
              · exact h
            rcases hcl with h | h | h | h | h | h | h | h | h | h
            · apply with_not_base [a, b] _ C hfan hsize hnot
              right; refine ⟨rfl, ?_⟩
              rcases h with h | h | h | h | h | h
              · exact ⟨a, by simp, Or.inl h⟩
              · exact ⟨a, by simp, Or.inr (Or.inl h)⟩
              · exact ⟨a, by simp, Or.inr (Or.inr h)⟩
              · exact ⟨b, by simp, Or.inl h⟩
              · exact ⟨b, by simp, Or.inr (Or.inl h)⟩
              · exact ⟨b, by simp, Or.inr (Or.inr h)⟩
            · apply hsym_pair a b
              apply with_not_base [sig11 a, sig11 b] _ C' (hmap_fan f) (hmap_size f) (hmap_not f)
              right; refine ⟨rfl, ?_⟩
              rcases h with h | h | h | h | h | h
              · exact ⟨sig11 a, by simp, Or.inl h⟩
              · exact ⟨sig11 a, by simp, Or.inr (Or.inl h)⟩
              · exact ⟨sig11 a, by simp, Or.inr (Or.inr h)⟩
              · exact ⟨sig11 b, by simp, Or.inl h⟩
              · exact ⟨sig11 b, by simp, Or.inr (Or.inl h)⟩
              · exact ⟨sig11 b, by simp, Or.inr (Or.inr h)⟩
            · exact with_not_mid [a, b] h C hfan hsize hnot
            · exact hcomm a b (with_not_mid [b, a] h C hfan hsize hnot)
            · exact hsym_pair a b (with_not_mid [sig11 a, sig11 b] h C' (hmap_fan f) (hmap_size f) (hmap_not f))
            · apply hsym_pair a b
              rcases with_not_mid [sig11 b, sig11 a] h C' (hmap_fan f) (hmap_size f) (hmap_not f) with ⟨x, hx⟩
              refine ⟨x, ?_⟩
              have hba : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 b, sig11 a]) =
                  PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 a, sig11 b]) := by
                simp only [List.map_cons, List.map_nil, hand2]; exact Bool.and_comm _ _
              show C'.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 a, sig11 b])]) ≠ F x
              rw [← hba]
              exact hx
            · exact with_not_hard [a, b] h C hfan hsize hnot
            · exact hcomm a b (with_not_hard [b, a] h C hfan hsize hnot)
            · exact hsym_pair a b (with_not_hard [sig11 a, sig11 b] h C' (hmap_fan f) (hmap_size f) (hmap_not f))
            · apply hsym_pair a b
              rcases with_not_hard [sig11 b, sig11 a] h C' (hmap_fan f) (hmap_size f) (hmap_not f) with ⟨x, hx⟩
              refine ⟨x, ?_⟩
              have hba : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 b, sig11 a]) =
                  PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 a, sig11 b]) := by
                simp only [List.map_cons, List.map_nil, hand2]; exact Bool.and_comm _ _
              show C'.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) [sig11 a, sig11 b])]) ≠ F x
              rw [← hba]
              exact hx
    · simp at hlen
  · let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩
    let g1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, x1.map Fin.val⟩
    let Cfull : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: g1 :: C.gates, C.output⟩
    have hmono : PEqualNP.MetaComplexity.Monotone2 Cfull := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr rfl, by decide⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨Or.inl rfl, by simp [g1]; exact hlen⟩
        · have hfg := hfan g hg
          have hne : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := fun h => hnot ⟨g, hg, h⟩
          have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
            rcases hfg.1 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hne
          exact ⟨hop, hfg.2⟩
    have hfull_size : Cfull.size ≤ 15 := by
      have hsz : C.gates.length ≤ 13 := hsize
      change C.gates.length + 2 ≤ 15
      omega
    rcases no_monotone_15 Cfull hmono hfull_size with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hstep0 : step (List.ofFn x) g0 = W x := by
      have h0 : (List.ofFn x).getD 0 false = x 0 := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      have h2 : (List.ofFn x).getD 2 false = x 2 := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      have hor2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
        intro a b; cases a <;> cases b <;> rfl
      show List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval ([0, 2].map fun i => (List.ofFn x).getD i false)] = W x
      simp only [List.map_cons, List.map_nil, h0, h2, hor2]
      rfl
    have hstep1 : step (W x) g1 =
        W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1)] := by
      show W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval ((x1.map Fin.val).map fun i => (W x).getD i false)] = _
      rw [List.map_map]
      rfl
    have heval : Cfull.eval (List.ofFn x) =
        C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1)]) := by
      change (C.gates.foldl step (step (step (List.ofFn x) g0) g1)).getD C.output false = _
      rw [hstep0, hstep1]
      rfl
    show C.eval (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin 11) => (W x).getD (↑x8) false) x1)]) ≠ F x
    rwa [← heval]
