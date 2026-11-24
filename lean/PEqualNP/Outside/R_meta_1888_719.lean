import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1888_719
    (subAnd :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) C →
        (11 : ℕ) ≤ C.output → C.output < (11 : ℕ) + C.gates.length →
        C.size ≤ (18 : ℕ) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ (x5 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5)
    (subOr :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) C →
        (11 : ℕ) ≤ C.output → C.output < (11 : ℕ) + C.gates.length →
        C.size ≤ (18 : ℕ) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ∃ (x5 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5)
    (subNot :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) C →
        (11 : ℕ) ≤ C.output → C.output < (11 : ℕ) + C.gates.length →
        C.size ≤ (18 : ℕ) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        ∃ (x5 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  classical
  intro C σ hfan hsize
  let fPet : (Fin 10 → Bool) → Bool := fun x6 =>
    x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
      x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 4 && x6 9 ||
      x6 5 && x6 7 || x6 7 && x6 9 || x6 9 && x6 6 || x6 6 && x6 8 || x6 8 && x6 5
  by_contra hno
  have hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) = fPet x := by
    intro x
    by_contra hne
    exact hno ⟨x, hne⟩
  let remapIdx (k : ℕ) : ℕ := if h : k < 10 then (σ ⟨k, h⟩).val else k
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate =>
      (⟨g.op, g.inputs.map remapIdx⟩ : PEqualNP.CircuitLowerBounds.Gate)), remapIdx C.output⟩
  have hD_fan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    rcases hfan g' hg' with ⟨hop, hlen⟩
    exact ⟨hop, by simp [hlen]⟩
  have hD_size : D.size ≤ 18 := by
    change (C.gates.map _).length ≤ 18
    rw [List.length_map]
    exact hsize
  have foldl_remapIdx : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wC wD : List Bool),
      wC.length = wD.length → 11 ≤ wC.length →
      (∀ k, k < wC.length → wD.getD (remapIdx k) false = wC.getD k false) →
      let wC' := gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wC
      let wD' := (gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
        (⟨g.op, g.inputs.map remapIdx⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
        (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wD
      wC'.length = wD'.length ∧
        ∀ k, k < wC'.length → wD'.getD (remapIdx k) false = wC'.getD k false := by
    intro gs
    induction gs with
    | nil => intro wC wD hlen _ hinv; exact ⟨hlen, hinv⟩
    | cons g gs ih =>
      intro wC wD hlen h11 hinv
      simp only [List.map_cons, List.foldl_cons]
      have hinv_all : ∀ k, wD.getD (remapIdx k) false = wC.getD k false := by
        intro k
        by_cases hk : k < wC.length
        · exact hinv k hk
        · have hk_ge : wC.length ≤ k := Nat.le_of_not_lt hk
          have hk_d : wD.length ≤ remapIdx k := by
            dsimp only [remapIdx]
            split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hk_ge, List.getElem?_eq_none hk_d]
      have hbit : g.op.eval ((g.inputs.map remapIdx).map fun i => wD.getD i false) =
          g.op.eval (g.inputs.map fun i => wC.getD i false) := by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro u _
        exact hinv_all u
      let wC1 := wC ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)]
      let wD1 := wD ++ [g.op.eval ((g.inputs.map remapIdx).map fun i => wD.getD i false)]
      apply ih wC1 wD1 (by simp [wC1, wD1, hlen]) (by simp [wC1]; omega)
      intro k hk
      have hk' : k < wC.length + 1 := by simpa [wC1] using hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk') with hlt | rfl
      · have hlt_d : remapIdx k < wD.length := by
          dsimp only [remapIdx]
          split_ifs <;> omega
        dsimp only [wC1, wD1]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlt_d, List.getElem?_append_left hlt]
        exact hinv k hlt
      · have hrem : remapIdx wC.length = wD.length := by
          dsimp only [remapIdx]
          split_ifs <;> omega
        dsimp only [wC1, wD1]
        rw [hrem, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl, hlen, Nat.sub_self]
        simpa using hbit
  have foldl_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp [List.length_append]
      omega
  have hD_eval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = fPet x := by
    intro x
    let wC0 := List.ofFn (x ∘ σ) ++ [x 0 || x 2]
    let wD0 := List.ofFn x ++ [x 0 || x 2]
    have hinv0 : ∀ k < wC0.length, wD0.getD (remapIdx k) false = wC0.getD k false := by
      intro k hk
      dsimp only [remapIdx]
      split_ifs with hlt
      · have hlt_d : (σ ⟨k, hlt⟩).val < 10 := (σ ⟨k, hlt⟩).isLt
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        dsimp only [wC0, wD0]
        rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp; exact hlt),
          List.getElem?_eq_getElem (by simp), List.getElem?_eq_getElem (by simp; exact hlt),
          List.getElem_ofFn, List.getElem_ofFn]
        simp only [Fin.eta, Function.comp_apply]
      · have hk10 : k = 10 := by
          have hlen : wC0.length = 11 := by simp [wC0]
          omega
        subst hk10
        simp [wC0, wD0, List.getD_eq_getElem?_getD]
    have hstep := foldl_remapIdx C.gates wC0 wD0 (by simp [wC0, wD0]) (by simp [wC0]) hinv0
    have hC_out : D.eval wD0 = C.eval wC0 := by
      change (D.wires wD0).getD (remapIdx C.output) false = (C.wires wC0).getD C.output false
      by_cases hlt : C.output < (C.wires wC0).length
      · exact hstep.2 C.output hlt
      · have hgeC : (C.wires wC0).length ≤ C.output := Nat.le_of_not_lt hlt
        have hlenC : (C.wires wC0).length = 11 + C.gates.length := by
          change (C.gates.foldl _ wC0).length = 11 + C.gates.length
          rw [foldl_len]
          simp [wC0]
        have hlenD : (D.wires wD0).length = 11 + C.gates.length := by
          change (D.gates.foldl _ wD0).length = 11 + C.gates.length
          rw [foldl_len]
          simp [wD0, D]
        have hgeD : (D.wires wD0).length ≤ remapIdx C.output := by
          rw [hlenD]
          dsimp only [remapIdx]
          split_ifs <;> omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none hgeC, List.getElem?_eq_none hgeD]
    rw [hC_out]
    exact hC x
  let cleanGate (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    PEqualNP.CircuitLowerBounds.GateOp.recOn (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate) g.op
      (if g.inputs.all (fun u => decide (u < 11 + j)) then g else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, g.inputs.filter (fun u => decide (u < 11 + j))⟩
      (List.recOn (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate) g.inputs
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩
        (fun u _ _ => if u < 11 + j then ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [u]⟩
                      else ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩))
      (fun _ => g)
      g
  let cleanAux : ℕ → List PEqualNP.CircuitLowerBounds.Gate → List PEqualNP.CircuitLowerBounds.Gate :=
    fun j gs => List.recOn gs (fun _ => []) (fun g _ ih j' => cleanGate j' g :: ih (j' + 1)) j
  have cleanAux_len : ∀ gs j, (cleanAux j gs).length = gs.length := by
    intro gs
    induction gs with
    | nil => intro j; rfl
    | cons g gs ih => intro j; simp [cleanAux, ih (j + 1)]
  let E : PEqualNP.CircuitLowerBounds.Circuit := ⟨cleanAux 0 D.gates, D.output⟩
  have hE_fan : PEqualNP.MetaComplexity.FanInTwo E := by
    have haux : ∀ gs j, (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ g ∈ cleanAux j gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
      intro gs
      induction gs with
      | nil => intro j _ g hg; simp [cleanAux] at hg
      | cons g' gs ih =>
        intro j hgs g hg
        simp only [cleanAux, List.mem_cons] at hg
        rcases hg with rfl | hg'
        · rcases hgs g' (by simp) with ⟨hop, hlen⟩
          rcases hop with h | h | h
          · dsimp only [cleanGate]; rw [h]; dsimp only
            split_ifs
            · exact ⟨Or.inl h, hlen⟩
            · exact ⟨Or.inr (Or.inl rfl), by simp⟩
          · dsimp only [cleanGate]; rw [h]; dsimp only
            exact ⟨Or.inr (Or.inl rfl), le_trans (List.length_filter_le _ _) hlen⟩
          · rcases hgin : g'.inputs with _ | ⟨u, _⟩
            · dsimp only [cleanGate]; rw [h, hgin]; exact ⟨Or.inl rfl, by simp⟩
            · dsimp only [cleanGate]; rw [h, hgin]; dsimp only
              split_ifs
              · exact ⟨Or.inr (Or.inr rfl), by simp⟩
              · exact ⟨Or.inl rfl, by simp⟩
        · exact ih (j + 1) (fun g'' hg'' => hgs g'' (by simp [hg''])) g hg'
    exact haux D.gates 0 hD_fan
  have hE_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 E := by
    have haux : ∀ gs j,
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ k < (cleanAux j gs).length,
        ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨cleanAux j gs, D.output⟩ k).inputs, u < 11 + (j + k) := by
      intro gs
      induction gs with
      | nil => intro j _ k hk; simp [cleanAux] at hk
      | cons g' gs ih =>
        intro j hgs k hk u hu
        cases k with
        | zero =>
          have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨cleanAux j (g' :: gs), D.output⟩ 0 = cleanGate j g' := rfl
          rw [hgate] at hu
          rcases (hgs g' (by simp)).1 with h | h | h
          · dsimp only [cleanGate] at hu
            rw [h] at hu
            dsimp only at hu
            split_ifs at hu with hall
            · simp only [List.all_eq_true, decide_eq_true_eq] at hall
              have := hall u hu
              omega
            · simp at hu
          · dsimp only [cleanGate] at hu
            rw [h] at hu
            dsimp only at hu
            obtain ⟨_, hdec⟩ := List.mem_filter.mp hu
            simp only [decide_eq_true_eq] at hdec
            omega
          · dsimp only [cleanGate] at hu
            rw [h] at hu
            dsimp only at hu
            rcases hgin : g'.inputs with _ | ⟨v, _⟩
            · simp [hgin] at hu
            · simp only [hgin] at hu
              split_ifs at hu with hv
              · simp only [List.mem_singleton] at hu; subst hu; omega
              · simp at hu
        | succ k =>
          have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨cleanAux j (g' :: gs), D.output⟩ (k + 1) =
              PEqualNP.MetaComplexity.NestedCover.gateAt ⟨cleanAux (j + 1) gs, D.output⟩ k := rfl
          rw [hgate] at hu
          have hk' : k < (cleanAux (j + 1) gs).length := by
            rw [cleanAux_len gs (j + 1)]
            rw [cleanAux_len (g' :: gs) j] at hk
            simp only [List.length_cons] at hk
            omega
          have := ih (j + 1) (fun g'' hg'' => hgs g'' (by simp [hg''])) k hk' u hu
          omega
    intro k hk u hu
    simpa using haux D.gates 0 hD_fan k (by simpa [E] using hk) u hu
  have hE_size : E.size ≤ 18 := by
    change (cleanAux 0 D.gates).length ≤ 18
    rw [cleanAux_len]
    change (C.gates.map _).length ≤ 18
    rw [List.length_map]
    exact hsize
  have hclean_gate_eval : ∀ (j : ℕ) (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      w.length = 11 + j →
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
      (cleanGate j g).op.eval ((cleanGate j g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro j w g hw hgop
    rcases hgop with h | h | h
    · dsimp only [cleanGate]; rw [h]; dsimp only
      split_ifs with hall
      · rw [h]
      · change false = (g.inputs.map fun i => w.getD i false).all id
        by_cases ha : (g.inputs.map fun i => w.getD i false).all id
        · exfalso
          simp only [List.all_eq_true, decide_eq_true_eq, not_forall, not_lt] at hall
          rcases hall with ⟨u, hu, hge⟩
          simp only [List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂] at ha
          have htrue := ha u hu
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at htrue
          cases htrue
        · have hfal : (g.inputs.map fun i => w.getD i false).all id = false := by
            cases hb : (g.inputs.map fun i => w.getD i false).all id
            · rfl
            · exact False.elim (ha hb)
          exact hfal.symm
    · dsimp only [cleanGate]; rw [h]; dsimp only
      change ((g.inputs.filter (fun u => decide (u < 11 + j))).map fun i => w.getD i false).any id =
        (g.inputs.map fun i => w.getD i false).any id
      simp only [List.any_map, List.any_filter]
      symm
      congr 1
      ext u
      by_cases hlt : u < 11 + j
      · simp [hlt]
      · have hge : w.length ≤ u := by omega
        simp [hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    · rcases hgin : g.inputs with _ | ⟨u, us⟩
      · dsimp only [cleanGate]; rw [h, hgin]; rfl
      · dsimp only [cleanGate]; rw [h, hgin]; dsimp only
        split_ifs with hlt
        · rfl
        · have hge : w.length ≤ u := by omega
          change true = !(w.getD u false)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
          rfl
  have hclean_wires : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ) (w : List Bool),
      w.length = 11 + j →
      (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      (cleanAux j gs).foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w =
        gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w := by
    intro gs
    induction gs with
    | nil => intro j w _ _; rfl
    | cons g gs ih =>
      intro j w hw hgs
      simp only [cleanAux, List.foldl_cons]
      have hg0 := hgs g (by simp)
      rw [hclean_gate_eval j w g hw hg0.1]
      apply ih (j + 1)
      · simp [hw]; omega
      · exact fun g' hg' => hgs g' (by simp [hg'])
  have hE_eval : ∀ x : Fin 10 → Bool, E.eval (List.ofFn x ++ [x 0 || x 2]) = fPet x := by
    intro x
    let w0 := List.ofFn x ++ [x 0 || x 2]
    have hw0 : w0.length = 11 + 0 := by simp [w0]
    have hcw := hclean_wires D.gates 0 w0 hw0 hD_fan
    have hEw : E.wires w0 = D.wires w0 := hcw
    change (E.wires w0).getD D.output false = fPet x
    rw [hEw]
    exact hD_eval x
  have hpref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ), k < w.length →
      (gs.foldl (fun w' (g : PEqualNP.CircuitLowerBounds.Gate) => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w).getD k false = w.getD k false := by
    intro gs
    induction gs with
    | nil => intro w k _; rfl
    | cons g gs ih =>
      intro w k hk
      simp only [List.foldl_cons]
      rw [ih (w ++ _) k (by simp; omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hk]
  have hE_out_ge : 11 ≤ E.output := by
    by_contra hlt
    have hlt11 : E.output < 11 := Nat.lt_of_not_le hlt
    by_cases h10 : E.output < 10
    · let x0 : Fin 10 → Bool := fun i => decide (i.val = E.output)
      have hev := hE_eval x0
      have hLHS : E.eval (List.ofFn x0 ++ [x0 0 || x0 2]) = true := by
        change (E.gates.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) (List.ofFn x0 ++ [x0 0 || x0 2])).getD E.output false = true
        rw [hpref E.gates _ E.output (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact h10),
          List.getElem?_eq_getElem (by simp; exact h10), List.getElem_ofFn]
        simp [x0]
      have hRHS : fPet x0 = false := by
        dsimp only [fPet, x0]
        revert h10
        generalize E.output = k
        intro hk
        interval_cases k <;> decide
      rw [hLHS, hRHS] at hev
      cases hev
    · have hk10 : E.output = 10 := by omega
      let x0 : Fin 10 → Bool := fun i => decide (i.val = 0)
      have hev := hE_eval x0
      have hLHS : E.eval (List.ofFn x0 ++ [x0 0 || x0 2]) = true := by
        change (E.gates.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) (List.ofFn x0 ++ [x0 0 || x0 2])).getD E.output false = true
        rw [hpref E.gates _ E.output (by simp; omega), hk10,
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp [x0]
      have hRHS : fPet x0 = false := by decide
      rw [hLHS, hRHS] at hev
      cases hev
  have hE_out_lt : E.output < 11 + E.gates.length := by
    by_contra hge
    have hge' : 11 + E.gates.length ≤ E.output := Nat.le_of_not_lt hge
    let x1 : Fin 10 → Bool := fun _ => true
    have hev := hE_eval x1
    have hlen : (E.wires (List.ofFn x1 ++ [x1 0 || x1 2])).length = 11 + E.gates.length := by
      change (E.gates.foldl _ (List.ofFn x1 ++ [x1 0 || x1 2])).length = 11 + E.gates.length
      rw [foldl_len]
      simp
    have hLHS : E.eval (List.ofFn x1 ++ [x1 0 || x1 2]) = false := by
      change (E.wires (List.ofFn x1 ++ [x1 0 || x1 2])).getD E.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have hRHS : fPet x1 = true := by decide
    rw [hLHS, hRHS] at hev
    cases hev
  have hE_nonempty : 0 < E.gates.length := by omega
  have hgate0_mem : PEqualNP.MetaComplexity.NestedCover.gateAt E 0 ∈ E.gates := by
    cases hgs : E.gates with
    | nil => simp [hgs] at hE_nonempty
    | cons g gs =>
      have hg0 : PEqualNP.MetaComplexity.NestedCover.gateAt E 0 = g := by
        change List.getD E.gates 0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g
        rw [hgs]
        rfl
      rw [hg0]
      simp
  have hgate0_op := (hE_fan (PEqualNP.MetaComplexity.NestedCover.gateAt E 0) hgate0_mem).1
  rcases hgate0_op with hop | hop | hop
  · obtain ⟨x, hx⟩ := subAnd E hE_fan hE_rb hE_out_ge hE_out_lt hE_size hop
    exact hx (hE_eval x)
  · obtain ⟨x, hx⟩ := subOr E hE_fan hE_rb hE_out_ge hE_out_lt hE_size hop
    exact hx (hE_eval x)
  · obtain ⟨x, hx⟩ := subNot E hE_fan hE_rb hE_out_ge hE_out_lt hE_size hop
    exact hx (hE_eval x)
