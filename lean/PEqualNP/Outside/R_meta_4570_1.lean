import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_4570_1
    (oneReader : ∀ x1 ∈ ([(1 : Fin 9), 2, 3, 5, 7, 8] : List (Fin 9)), ∀ C : Circuit, FanInTwo C →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      C.size ≤ 13 →
      (C.gates.filter fun g => ([0, 9] : List ℕ).any fun i => g.inputs.contains i).length = 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x x1]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (monoTwo : ∀ x1 ∈ ([(1 : Fin 9), 2, 3, 5, 7, 8] : List (Fin 9)), ∀ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      C.size ≤ 13 →
      (C.gates.filter fun g => ([0, 9] : List ℕ).any fun i => g.inputs.contains i).length = 2 →
      (∃ g ∈ C.gates, 0 ∈ g.inputs) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x x1]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (oneNotAdj : ∀ x1 ∈ ([(1 : Fin 9), 8] : List (Fin 9)), ∀ C : Circuit, FanInTwo C →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      C.size = 13 →
      (C.gates.filter fun g => g.op.eval [false]).length = 1 →
      (C.gates.filter fun g => ([0, 9] : List ℕ).any fun i => g.inputs.contains i).length = 2 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x x1]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (oneNotNonAdj : ∀ x1 ∈ ([(2 : Fin 9), 3, 5, 7] : List (Fin 9)), ∀ C : Circuit, FanInTwo C →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      C.size = 13 →
      (C.gates.filter fun g => g.op.eval [false]).length = 1 →
      (C.gates.filter fun g => ([0, 9] : List ℕ).any fun i => g.inputs.contains i).length = 2 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x x1]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (12 : ℕ) ≤ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => !x6.op.eval [Bool.false]) x3.gates).length → (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x8 : ℕ) => x7.inputs.contains x8) (List.map (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => { op := x7.op, inputs := if x7.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x7.inputs else x7.inputs : PEqualNP.CircuitLowerBounds.Gate }) x3.gates)).length ≤ (2 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))] ++ [x8 (6 : Fin (9 : ℕ)) || x8 x1]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 C hfan hsz hnonNot hread09
  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
      x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let normGate (g : Gate) : Gate :=
    { op := g.op, inputs := if g.op.eval [false] = true then g.inputs.take 1 else g.inputs }
  let reads09 (g : Gate) : Bool := ([0, 9] : List ℕ).any fun i => g.inputs.contains i
  let C' : Circuit := ⟨C.gates.map normGate, C.output⟩
  have snoc_eq (L : List Bool) (v : Bool) : (L ++ [v]).getD L.length false = v := by simp
  have snoc_ne (L : List Bool) (v : Bool) (j : ℕ) (hj : j ≠ L.length) :
      (L ++ [v]).getD j false = L.getD j false := by
    by_cases hlt : j < L.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have norm_eval (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (F : ℕ → Bool) : (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    rcases g with ⟨op, ins⟩
    rcases hg with h | h | h
    · change op = GateOp.and at h; subst h; simp [normGate, GateOp.eval]
    · change op = GateOp.or at h; subst h; simp [normGate, GateOp.eval]
    · change op = GateOp.not at h; subst h; cases ins <;> simp [normGate, GateOp.eval]
  have norm_wires (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (w : List Bool) : (gs.map normGate).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have h1 : step w (normGate g) = step w g := by
        simp only [step]
        rw [norm_eval g (hg g List.mem_cons_self)]
      rw [h1]
      exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (step w g)
  have heval_eq (w : List Bool) : C'.eval w = C.eval w := by
    change ((C.gates.map normGate).foldl step w).getD C.output false = (C.gates.foldl step w).getD C.output false
    rw [norm_wires C.gates (fun g hg => (hfan g hg).1) w]
  have hfan' : FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    refine ⟨(hfan g0 hg0).1, ?_⟩
    simp only [normGate]
    split
    · simp
    · exact (hfan g0 hg0).2
  have hnot1 : ∀ g ∈ C'.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop
    obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
    change g0.op = GateOp.not at hop
    simp [normGate, hop, GateOp.eval]
  have hsz' : C'.size ≤ 13 := by
    change (C.gates.map normGate).length ≤ 13
    rw [List.length_map]
    exact hsz
  have filter_map_op (p : GateOp → Bool) (gs : List Gate) :
      ((gs.map normGate).filter fun g => p g.op).length = (gs.filter fun g => p g.op).length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.filter_cons]
      have hop : (normGate g).op = g.op := rfl
      rw [hop]
      cases p g.op <;> simp [ih]
  have hnonNot' : 12 ≤ (C'.gates.filter fun g => !g.op.eval [false]).length := by
    simpa only [C'] using (filter_map_op (fun op => !op.eval [false]) C.gates).symm ▸ hnonNot
  have filter_part (p : Gate → Bool) (gs : List Gate) :
      (gs.filter p).length + (gs.filter fun g => !p g).length = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.filter_cons]
      cases p g <;> simp <;> omega
  have hpart := filter_part (fun g => g.op.eval [false]) C'.gates
  have hread09' : (C'.gates.filter reads09).length ≤ 2 := hread09
  have hrc : (C'.gates.filter reads09).length = 0 ∨
      (C'.gates.filter reads09).length = 1 ∨
      (C'.gates.filter reads09).length = 2 := by omega
  let inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [!x 0] ++ [x 6 || x x1]
  have hinp_len (x : Fin 9 → Bool) : (inp x).length = 11 := by simp [inp]
  have hinp_lt9 (x : Fin 9 → Bool) (i : Fin 9) : (inp x).getD i.val false = x i := by
    simp only [inp, List.append_assoc]
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hinp_9 (x : Fin 9 → Bool) : (inp x).getD 9 false = !x 0 := by
    simp only [inp]
    rw [List.getD_append _ _ _ _ (by simp)]
    have h9 : (List.ofFn x ++ [!x 0]).getD (List.ofFn x).length false = !x 0 := snoc_eq _ _
    simpa only [List.length_ofFn] using h9
  have hinp_10 (x : Fin 9 → Bool) : (inp x).getD 10 false = (x 6 || x x1) := by
    simp only [inp]
    have h10 : ((List.ofFn x ++ [!x 0]) ++ [x 6 || x x1]).getD (List.ofFn x ++ [!x 0]).length false =
        (x 6 || x x1) := snoc_eq _ _
    simpa only [List.length_append, List.length_ofFn, List.length_singleton] using h10
  have hx1_ne0 : x1 ≠ (0 : Fin 9) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
    rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  let xa : Fin 9 → Bool := fun i => i == 1
  let xb : Fin 9 → Bool := fun i => i == 0 || i == 1
  have hxa_xb_eq (i : Fin 9) (hi : i ≠ 0) : xa i = xb i := by
    have h0 : (i == 0) = false := by simp [hi]
    simp [xa, xb, h0]
  have hxa_xb_inp (j : ℕ) (hj0 : j ≠ 0) (hj9 : j ≠ 9) :
      (inp xa).getD j false = (inp xb).getD j false := by
    by_cases hlt : j < 9
    · let i : Fin 9 := ⟨j, hlt⟩
      have hi0 : i ≠ 0 := fun h => hj0 (congrArg Fin.val h)
      rw [show j = i.val from rfl, hinp_lt9, hinp_lt9, hxa_xb_eq i hi0]
    · by_cases h10 : j = 10
      · subst h10
        rw [hinp_10, hinp_10, hxa_xb_eq 6 (by decide), hxa_xb_eq x1 hx1_ne0]
      · rw [List.getD_eq_default _ _ (by rw [hinp_len]; omega),
          List.getD_eq_default _ _ (by rw [hinp_len]; omega)]
  have hdone (h : ∃ x : Fin 9 → Bool, C'.eval (inp x) ≠ edge x) :
      ∃ x : Fin 9 → Bool, C.eval (inp x) ≠ edge x := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, by rwa [← heval_eq]⟩
  rcases hrc with hr0 | hr1 | hr2
  · apply hdone
    have hnil : C'.gates.filter reads09 = [] := List.eq_nil_of_length_eq_zero hr0
    have hnoread : ∀ g ∈ C'.gates, 0 ∉ g.inputs ∧ 9 ∉ g.inputs := by
      intro g hg
      have hf : reads09 g = false := by
        have := List.filter_eq_nil_iff.mp hnil g hg
        cases h : reads09 g
        · rfl
        · exact False.elim (this h)
      simp only [reads09, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
        List.contains_eq_mem, decide_eq_false_iff_not] at hf
      exact hf
    by_cases ho0 : C'.output = 0
    · let x0 : Fin 9 → Bool := fun i => i == 0
      refine ⟨x0, ?_⟩
      change (C'.gates.foldl step (inp x0)).getD C'.output false ≠ edge x0
      rw [ho0, fold_keep _ _ _ (by rw [hinp_len]; decide), show (0 : ℕ) = (0 : Fin 9).val from rfl, hinp_lt9 x0 0]
      decide
    · by_cases ho9 : C'.output = 9
      · let xf : Fin 9 → Bool := fun _ => false
        refine ⟨xf, ?_⟩
        change (C'.gates.foldl step (inp xf)).getD C'.output false ≠ edge xf
        rw [ho9, fold_keep _ _ _ (by rw [hinp_len]; decide), hinp_9 xf]
        decide
      · have hagree : ∀ (gs : List Gate) (w w' : List Bool),
            w.length = w'.length → 10 ≤ w.length →
            (∀ j, j ≠ 0 → j ≠ 9 → w.getD j false = w'.getD j false) →
            (∀ g ∈ gs, 0 ∉ g.inputs ∧ 9 ∉ g.inputs) →
            ∀ j, j ≠ 0 → j ≠ 9 → (gs.foldl step w).getD j false = (gs.foldl step w').getD j false := by
          intro gs
          induction gs with
          | nil => intro w w' _ _ hag _ j hj0 hj9; exact hag j hj0 hj9
          | cons g gs ih =>
            intro w w' hl h10 hag hgs
            have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
                g.op.eval (g.inputs.map fun i => w'.getD i false) := by
              congr 1
              apply List.map_congr_left
              intro a ha
              obtain ⟨h0, h9⟩ := hgs g List.mem_cons_self
              exact hag a (fun h => h0 (h ▸ ha)) (fun h => h9 (h ▸ ha))
            apply ih (step w g) (step w' g) (by simp [step, hl]) (by simp [step]; omega) _
              (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
            intro j hj0 hj9
            simp only [step, hv]
            by_cases hjl : j = w.length
            · rw [hjl, snoc_eq, hl, snoc_eq]
            · rw [snoc_ne _ _ _ hjl, snoc_ne _ _ _ (by omega)]
              exact hag j hj0 hj9
        have heq : C'.eval (inp xa) = C'.eval (inp xb) :=
          hagree C'.gates (inp xa) (inp xb) (by rw [hinp_len, hinp_len]) (by rw [hinp_len]; omega)
            hxa_xb_inp hnoread C'.output ho0 ho9
        by_cases h : C'.eval (inp xa) = edge xa
        · refine ⟨xb, ?_⟩
          rw [← heq, h]
          decide
        · exact ⟨xa, h⟩
  · exact hdone (oneReader x1 hx1 C' hfan' hnot1 hsz' hr1)
  · apply hdone
    have hnot_le : (C'.gates.filter fun g => g.op.eval [false]).length ≤ 1 := by
      change C'.gates.length ≤ 13 at hsz'
      omega
    have hnot_cases : (C'.gates.filter fun g => g.op.eval [false]).length = 0 ∨
        (C'.gates.filter fun g => g.op.eval [false]).length = 1 := by omega
    rcases hnot_cases with hnot0 | hnot1c
    · have hnil : C'.gates.filter (fun g => g.op.eval [false]) = [] := List.eq_nil_of_length_eq_zero hnot0
      have hmono : ∀ g ∈ C'.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        obtain ⟨hop, hlen⟩ := hfan' g hg
        refine ⟨?_, hlen⟩
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          have hnotg : g.op = GateOp.not := h
          have hf := List.filter_eq_nil_iff.mp hnil g hg
          exact hf (by simp [hnotg, GateOp.eval])
      by_cases hhas0 : ∃ g ∈ C'.gates, 0 ∈ g.inputs
      · exact monoTwo x1 hx1 C' hmono hsz' hr2 hhas0
      · by_cases ho0 : C'.output = 0
        · let x0 : Fin 9 → Bool := fun i => i == 0
          refine ⟨x0, ?_⟩
          change (C'.gates.foldl step (inp x0)).getD C'.output false ≠ edge x0
          rw [ho0, fold_keep _ _ _ (by rw [hinp_len]; decide), show (0 : ℕ) = (0 : Fin 9).val from rfl, hinp_lt9 x0 0]
          decide
        · have hno0 : ∀ g ∈ C'.gates, 0 ∉ g.inputs := fun g hg h0 => hhas0 ⟨g, hg, h0⟩
          have hmono_run : ∀ (gs : List Gate) (w w' : List Bool),
              w.length = w'.length → 1 ≤ w.length →
              (∀ j, j ≠ 0 → w.getD j false = true → w'.getD j false = true) →
              (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ 0 ∉ g.inputs) →
              ∀ j, j ≠ 0 → (gs.foldl step w).getD j false = true → (gs.foldl step w').getD j false = true := by
            intro gs
            induction gs with
            | nil => intro w w' _ _ hle _ j hj h; exact hle j hj h
            | cons g gs ih =>
              intro w w' hl h1 hle hgs
              obtain ⟨hop, hg0⟩ := hgs g List.mem_cons_self
              have hgmono : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
                  g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
                rcases hop with hand | hor
                · rw [hand]
                  change (g.inputs.map fun i => w.getD i false).all id = true →
                    (g.inputs.map fun i => w'.getD i false).all id = true
                  simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
                  exact fun h a ha => hle a (fun he => hg0 (he ▸ ha)) (h a ha)
                · rw [hor]
                  change (g.inputs.map fun i => w.getD i false).any id = true →
                    (g.inputs.map fun i => w'.getD i false).any id = true
                  simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
                  rintro ⟨a, ha, h⟩
                  exact ⟨a, ha, hle a (fun he => hg0 (he ▸ ha)) h⟩
              apply ih (step w g) (step w' g) (by simp [step, hl]) (by simp [step]) _
                (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
              intro j hj
              simp only [step]
              by_cases hjl : j = w.length
              · rw [hjl, snoc_eq, hl, snoc_eq]
                exact hgmono
              · rw [snoc_ne _ _ _ hjl, snoc_ne _ _ _ (by omega)]
                exact hle j hj
          have hinit_le (j : ℕ) (hj0 : j ≠ 0) :
              (inp xb).getD j false = true → (inp xa).getD j false = true := by
            by_cases hj9 : j = 9
            · subst hj9
              rw [hinp_9 xb]
              intro h
              cases h
            · rw [hxa_xb_inp j hj0 hj9]
              exact id
          have hba : C'.eval (inp xb) = true → C'.eval (inp xa) = true :=
            hmono_run C'.gates (inp xb) (inp xa) (by rw [hinp_len, hinp_len]) (by rw [hinp_len]; omega)
              hinit_le (fun g hg => ⟨(hmono g hg).1, hno0 g hg⟩) C'.output ho0
          by_cases h : C'.eval (inp xb) = true
          · refine ⟨xa, ?_⟩
            rw [hba h]
            decide
          · refine ⟨xb, ?_⟩
            intro he
            exact h (he.trans (by decide))
    · have hsz13 : C'.size = 13 := by
        change C'.gates.length = 13
        change C'.gates.length ≤ 13 at hsz'
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
      rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact oneNotAdj 1 (by decide) C' hfan' hnot1 hsz13 hnot1c hr2
      · exact oneNotNonAdj 2 (by decide) C' hfan' hnot1 hsz13 hnot1c hr2
      · exact oneNotNonAdj 3 (by decide) C' hfan' hnot1 hsz13 hnot1c hr2
      · exact oneNotNonAdj 5 (by decide) C' hfan' hnot1 hsz13 hnot1c hr2
      · exact oneNotNonAdj 7 (by decide) C' hfan' hnot1 hsz13 hnot1c hr2
      · exact oneNotAdj 8 (by decide) C' hfan' hnot1 hsz13 hnot1c hr2
