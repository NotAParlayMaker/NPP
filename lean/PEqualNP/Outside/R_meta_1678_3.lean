import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1678_3
    (h46 : ∀ C : Circuit, FanInTwo C →
      C.gates.head? = some ⟨GateOp.or, [4, 6]⟩ →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (h64 : ∀ C : Circuit, FanInTwo C →
      C.gates.head? = some ⟨GateOp.or, [6, 4]⟩ →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) ||
        (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
        (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) ||
        (x 8 && x 5)) →
      16 ≤ C.size := by
  intro C hFan hWire hFun
  cases hgates : C.gates with
  | nil =>
      let y : Fin 9 → Bool := fun i => decide (i.val = 4)
      have hy := hWire y
      have hfold : C.wires (List.ofFn y) = List.ofFn y := by
        simp [Circuit.wires, hgates]
      rw [hfold] at hy
      rw [List.getD_eq_default (List.ofFn y) false (by simp)] at hy
      simp [y] at hy
  | cons g gs =>
      have hgmem : g ∈ C.gates := by simp [hgates]
      have hlen : g.inputs.length ≤ 2 := (hFan g hgmem).2
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        have hmem := (hFan g hgmem).1
        rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        exact hmem
      have hpres : ∀ (rest : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) w).getD i
              false = w.getD i false := by
        intro rest
        induction rest with
        | nil => intro w i hi; rfl
        | cons g' rest ih =>
            intro w i hi
            simp only [List.foldl_cons]
            have hlt : i < (w ++ [g'.op.eval (g'.inputs.map fun t => w.getD t false)]).length := by
              simp
              omega
            have hstep := ih (w ++ [g'.op.eval (g'.inputs.map fun t => w.getD t false)]) i hlt
            rwa [List.getD_append w [g'.op.eval (g'.inputs.map fun t => w.getD t false)] false i hi] at hstep
      have hgate : ∀ z : Fin 9 → Bool,
          g.op.eval (g.inputs.map fun t => (List.ofFn z).getD t false) = (z 4 || z 6) := by
        intro z
        let v := g.op.eval (g.inputs.map fun t => (List.ofFn z).getD t false)
        have hlen9 : (List.ofFn z).length = 9 := by simp
        have hfirst : ((List.ofFn z) ++ [v]).getD 9 false = v := by
          rw [List.getD_append_right (List.ofFn z) [v] false 9 (by simp [hlen9])]
          simp
        have hwires : C.wires (List.ofFn z) =
            gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)])
              ((List.ofFn z) ++ [v]) := by
          simp [Circuit.wires, hgates, List.foldl_cons, v]
        have hkeep := hpres gs ((List.ofFn z) ++ [v]) 9 (by simp [hlen9])
        have := hWire z
        rw [hwires, hkeep, hfirst] at this
        exact this
      let z0 : Fin 9 → Bool := fun _ => false
      let bit : ℕ → Fin 9 → Bool := fun k i => decide (i.val = k)
      have read0 : ∀ t, (List.ofFn z0).getD t false = false := by
        intro t
        by_cases ht : t < 9
        · have hlt : t < (List.ofFn z0).length := by simp [ht]
          rw [List.getD_eq_getElem (List.ofFn z0) false hlt, List.getElem_ofFn]
        · exact List.getD_eq_default (List.ofFn z0) false (by simp; omega)
      have readBit : ∀ k t, k < 9 → (List.ofFn (bit k)).getD t false = decide (t = k) := by
        intro k t hk
        by_cases ht : t < 9
        · have hlt : t < (List.ofFn (bit k)).length := by simp [ht]
          rw [List.getD_eq_getElem (List.ofFn (bit k)) false hlt, List.getElem_ofFn]
        · rw [List.getD_eq_default (List.ofFn (bit k)) false (by simp; omega)]
          exact (decide_eq_false (by omega : ¬ t = k)).symm
      have hz0 : g.op.eval (g.inputs.map fun t => (List.ofFn z0).getD t false) = false := by
        simpa [z0] using hgate z0
      have hpos : ∀ k, k < 9 → k = 4 ∨ k = 6 →
          g.op.eval (g.inputs.map fun t => (List.ofFn (bit k)).getD t false) = true := by
        intro k hk hk46
        rcases hk46 with rfl | rfl
        · simpa [bit] using hgate (bit 4)
        · simpa [bit] using hgate (bit 6)
      have hneg : ∀ k, k < 9 → k ≠ 4 → k ≠ 6 →
          g.op.eval (g.inputs.map fun t => (List.ofFn (bit k)).getD t false) = false := by
        intro k hk hk4 hk6
        have hdec : (bit k) 4 = false ∧ (bit k) 6 = false := by
          constructor
          · change decide (4 = k) = false
            exact decide_eq_false (fun h => hk4 h.symm)
          · change decide (6 = k) = false
            exact decide_eq_false (fun h => hk6 h.symm)
        have := hgate (bit k)
        rw [hdec.1, hdec.2] at this
        simpa using this
      have hshape : g = ⟨GateOp.or, [4, 6]⟩ ∨ g = ⟨GateOp.or, [6, 4]⟩ := by
        cases hinputs : g.inputs with
        | nil =>
            rcases hop with hand | hor | hnot
            · rw [hand, hinputs] at hz0
              simp [GateOp.eval, List.map_nil, List.all_nil] at hz0
            · have h4 := hpos 4 (by decide) (by decide)
              rw [hor, hinputs] at h4
              simp [GateOp.eval, List.map_nil] at h4
            · rw [hnot, hinputs] at hz0
              simp [GateOp.eval, List.map_nil, List.headD] at hz0
        | cons a as =>
            cases has : as with
            | nil =>
                rcases hop with hand | hor | hnot
                · have h4 := hpos 4 (by decide) (by decide)
                  have h6 := hpos 6 (by decide) (by decide)
                  rw [hand, hinputs, has] at h4 h6
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                    Bool.and_true] at h4 h6
                  rw [readBit 4 a (by decide)] at h4
                  rw [readBit 6 a (by decide)] at h6
                  have ha4 : a = 4 := of_decide_eq_true h4
                  have ha6 : a = 6 := of_decide_eq_true h6
                  omega
                · have h4 := hpos 4 (by decide) (by decide)
                  have h6 := hpos 6 (by decide) (by decide)
                  rw [hor, hinputs, has] at h4 h6
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                    Bool.or_false] at h4 h6
                  rw [readBit 4 a (by decide)] at h4
                  rw [readBit 6 a (by decide)] at h6
                  have ha4 : a = 4 := of_decide_eq_true h4
                  have ha6 : a = 6 := of_decide_eq_true h6
                  omega
                · rw [hnot, hinputs, has] at hz0
                  simp only [GateOp.eval, List.map_cons, List.headD_cons] at hz0
                  rw [read0 a] at hz0
                  cases hz0
            | cons b bs =>
                cases hbs : bs with
                | cons c cs =>
                    simp [hinputs, has, hbs, List.length_cons] at hlen
                | nil =>
                    rcases hop with hand | hor | hnot
                    · have h4 := hpos 4 (by decide) (by decide)
                      have h6 := hpos 6 (by decide) (by decide)
                      rw [hand, hinputs, has, hbs] at h4 h6
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        Bool.and_true] at h4 h6
                      rw [readBit 4 a (by decide), readBit 4 b (by decide)] at h4
                      rw [readBit 6 a (by decide), readBit 6 b (by decide)] at h6
                      simp only [Bool.and_eq_true] at h4 h6
                      rcases h4 with ⟨h4a, h4b⟩
                      rcases h6 with ⟨h6a, h6b⟩
                      have ha4 : a = 4 := of_decide_eq_true h4a
                      have hb4 : b = 4 := of_decide_eq_true h4b
                      have ha6 : a = 6 := of_decide_eq_true h6a
                      omega
                    · have h4 := hpos 4 (by decide) (by decide)
                      have h6 := hpos 6 (by decide) (by decide)
                      rw [hor, hinputs, has, hbs] at h4 h6
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        Bool.or_false] at h4 h6
                      rw [readBit 4 a (by decide), readBit 4 b (by decide)] at h4
                      rw [readBit 6 a (by decide), readBit 6 b (by decide)] at h6
                      simp only [Bool.or_eq_true] at h4 h6
                      have h4p : a = 4 ∨ b = 4 := by
                        rcases h4 with h | h
                        · exact Or.inl (of_decide_eq_true h)
                        · exact Or.inr (of_decide_eq_true h)
                      have h6p : a = 6 ∨ b = 6 := by
                        rcases h6 with h | h
                        · exact Or.inl (of_decide_eq_true h)
                        · exact Or.inr (of_decide_eq_true h)
                      rcases h4p with ha | hb <;> rcases h6p with ha6 | hb6
                      · have : (4 : ℕ) = 6 := by rw [← ha, ha6]
                        omega
                      · left
                        cases g
                        congr
                        · exact hinputs.trans (by rw [ha, has, hbs, hb6])
                      · right
                        cases g
                        congr
                        · exact hinputs.trans (by rw [ha6, has, hbs, hb])
                      · have : (4 : ℕ) = 6 := by rw [← hb, hb6]
                        omega
                    · rw [hnot, hinputs, has, hbs] at hz0
                      simp only [GateOp.eval, List.map_cons, List.headD_cons] at hz0
                      rw [read0 a] at hz0
                      cases hz0
      rcases hshape with h | h
      · exact h46 C hFan (by simp [hgates, h]) hFun
      · exact h64 C hFan (by simp [hgates, h]) hFun
