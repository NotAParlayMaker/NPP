import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2163_7
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∃ a b : Fin C.gates.length, a ≠ b ∧
        (C.gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ c : Fin C.gates.length,
          (C.gates.get c).op = PEqualNP.CircuitLowerBounds.GateOp.not → c = a ∨ c = b) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && (x 1 || x 4 || x 5) || x 2 && (x 1 || x 3 || x 7) || x 8 && (x 3 || x 5 || x 6) ||
        x 1 && x 6 || x 3 && x 4 || x 5 && x 7) →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      g.inputs ≤ g.inputs.map (fun k => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] k k) →
      16 ≤ C.size)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∃ a b : Fin C.gates.length, a ≠ b ∧
        (C.gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ c : Fin C.gates.length,
          (C.gates.get c).op = PEqualNP.CircuitLowerBounds.GateOp.not → c = a ∨ c = b) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && (x 1 || x 4 || x 5) || x 2 && (x 1 || x 3 || x 7) || x 8 && (x 3 || x 5 || x 6) ||
        x 1 && x 6 || x 3 && x 4 || x 5 && x 7) →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      g.inputs ≤ g.inputs.map (fun k => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] k k) →
      16 ≤ C.size)
    (h3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∃ a b : Fin C.gates.length, a ≠ b ∧
        (C.gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ c : Fin C.gates.length,
          (C.gates.get c).op = PEqualNP.CircuitLowerBounds.GateOp.not → c = a ∨ c = b) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && (x 1 || x 4 || x 5) || x 2 && (x 1 || x 3 || x 7) || x 8 && (x 3 || x 5 || x 6) ||
        x 1 && x 6 || x 3 && x 4 || x 5 && x 7) →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      g.inputs ≤ g.inputs.map (fun k => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] k k) →
      16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 ≠ x4 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hfan hN h9 hfun
  have hwi : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (l : List Bool), D.wires l =
      D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l :=
    fun _ _ => rfl
  have hcf : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool),
      PEqualNP.MetaComplexity.circuitFun 9 D x =
        (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD D.output false := fun _ _ => rfl
  have hsz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  have hE : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) =
      (b0 && (b1 || b4 || b5) || b2 && (b1 || b3 || b7) || b8 && (b3 || b5 || b6) ||
        b1 && b6 || b3 && b4 || b5 && b7) := by
    decide
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
      x 0 && (x 1 || x 4 || x 5) || x 2 && (x 1 || x 3 || x 7) || x 8 && (x 3 || x 5 || x 6) ||
        x 1 && x 6 || x 3 && x 4 || x 5 && x 7 := by
    rw [hfun]
    funext x
    exact hE (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  have hlen : 1 < C.gates.length := by
    obtain ⟨a, b, hab, _, _, _⟩ := hN
    have ha := a.2
    have hb := b.2
    have hv : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
    omega
  have hg : C.gates[1]? = some C.gates[1] := List.getElem?_eq_getElem hlen
  generalize C.gates[1] = g at hg
  -- the symmetry (0 2)(3 5)(4 7) of the graph, which fixes the first gate x0 OR x2
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b2 && (b1 || b7 || b3) || b0 && (b1 || b5 || b4) || b8 && (b5 || b3 || b6) ||
        b1 && b6 || b5 && b7 || b3 && b4) =
      (b0 && (b1 || b4 || b5) || b2 && (b1 || b3 || b7) || b8 && (b3 || b5 || b6) ||
        b1 && b6 || b3 && b4 || b5 && b7) := by
    decide
  have hlt : ∀ j : ℕ, j < 9 → List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j < 9 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 9 ≤ j → List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hinv : ∀ j : ℕ, List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8]
      (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j) (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j) = j := by
    intro j
    by_cases hj : j < 9
    · interval_cases j <;> decide
    · rw [hge j (by omega), hge j (by omega)]
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
            (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          j false := by
    intro gs
    induction gs with
    | nil =>
      intro W W' _ _ hW j
      exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp
        omega
      · have hv : g.op.eval ((g.inputs.map fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        by_cases hj : j < W.length
        · have hj' : List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j < W'.length := by
            by_cases h : j < 9
            · have := hlt j h
              omega
            · rw [hge j (by omega)]
              omega
          have hWj := hW j
          generalize List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j = r at hj' hWj ⊢
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hj', List.getElem?_append_left hj]
          simpa only [List.getD_eq_getElem?_getD] using hWj
        · rw [hge j (by omega)]
          by_cases hj2 : j = W.length
          · subst hj2
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
              List.getElem?_append_right (le_refl _), ← hl,
              List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hin : ∀ y : Fin 9 → Bool, ∀ j : ℕ,
      (List.ofFn y).getD (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j) false =
        (List.ofFn fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)).getD j false := by
    intro y j
    by_cases hj : j < 9
    · interval_cases j <;> rfl
    · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hop := (hfan g (List.mem_of_getElem? hg)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hcase : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      (∃ a b : Fin D.gates.length, a ≠ b ∧
        (D.gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (D.gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ c : Fin D.gates.length,
          (D.gates.get c).op = PEqualNP.CircuitLowerBounds.GateOp.not → c = a ∨ c = b) →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (PEqualNP.MetaComplexity.circuitFun 9 D = fun x : Fin 9 → Bool =>
        x 0 && (x 1 || x 4 || x 5) || x 2 && (x 1 || x 3 || x 7) || x 8 && (x 3 || x 5 || x 6) ||
        x 1 && x 6 || x 3 && x 4 || x 5 && x 7) →
      ∀ d : PEqualNP.CircuitLowerBounds.Gate, D.gates[1]? = some d → d.op = g.op →
      d.inputs ≤ d.inputs.map (fun k => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] k k) →
      16 ≤ D.size := by
    intro D hD hDN hD9 hDf d hd hdo hdc
    rcases hop with hop | hop | hop
    · exact h1 D hD hDN hD9 hDf d hd (hdo.trans hop) hdc
    · exact h2 D hD hDN hD9 hDf d hd (hdo.trans hop) hdc
    · exact h3 D hD hDN hD9 hDf d hd (hdo.trans hop) hdc
  rcases le_total g.inputs (g.inputs.map fun k => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] k k)
    with hc | hc
  · exact hcase C hfan hN h9 hfun' g hg rfl hc
  · have hW : ∀ y : Fin 9 → Bool, ∀ j : ℕ,
        ((C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y)).getD
            (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] j j) false =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i))).getD j false := by
      intro y j
      apply hpre
      · simp
      · simp
      · exact hin y
    have hl : (C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
        PEqualNP.CircuitLowerBounds.Gate.mk g.op
          (g.inputs.map fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i)).length =
        C.gates.length := List.length_map _
    have hsize := hcase
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
          PEqualNP.CircuitLowerBounds.Gate.mk g.op
            (g.inputs.map fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i))
        (List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] C.output C.output))
      ?_ ?_ ?_ ?_
      (PEqualNP.CircuitLowerBounds.Gate.mk g.op
        (g.inputs.map fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i))
      ?_ rfl ?_
    · rw [hsz] at hsize
      rw [hsz]
      simpa using hsize
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      refine ⟨(hfan d0 hd0).1, ?_⟩
      simpa using (hfan d0 hd0).2
    · obtain ⟨a, b, hab, ha, hb, hall⟩ := hN
      refine ⟨Fin.cast hl.symm a, Fin.cast hl.symm b, ?_, ?_, ?_, ?_⟩
      · intro h
        apply hab
        ext
        have h' := congrArg Fin.val h
        simpa using h'
      · simpa [List.get_eq_getElem] using ha
      · simpa [List.get_eq_getElem] using hb
      · intro c hc
        have hc' : (C.gates.get (Fin.cast hl c)).op =
            PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa [List.get_eq_getElem] using hc
        rcases hall _ hc' with h | h
        · left
          ext
          have h' := congrArg Fin.val h
          simpa using h'
        · right
          ext
          have h' := congrArg Fin.val h
          simpa using h'
    · intro y
      have e := hW y 9
      rw [hge 9 (le_refl _)] at e
      rw [hwi]
      dsimp only
      rw [e]
      refine (h9 _).trans ?_
      show (y 2 || y 0) = (y 0 || y 2)
      exact Bool.or_comm _ _
    · funext y
      have e := hW y C.output
      have hf := congrFun hfun' (fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i))
      rw [hcf] at hf
      rw [hcf]
      dsimp only at hf ⊢
      rw [e]
      rw [hf]
      exact hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    · simp [hg]
    · rw [List.map_map]
      have : ((fun k => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] k k) ∘
          fun i => List.getD [2, 1, 0, 5, 7, 3, 6, 4, 8] i i) = id := by
        funext k
        exact hinv k
      rw [this, List.map_id]
      exact hc
