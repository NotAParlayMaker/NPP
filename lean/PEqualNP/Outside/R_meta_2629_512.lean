import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_2629_512
    (hasAndReader : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length = 2 ∧
        ∃ i1 i2 j1, ∃ (h1 : i1 < C.gates.length) (h2 : i2 < C.gates.length) (h3 : j1 < C.gates.length),
          i1 < j1 ∧ i1 ≠ i2 ∧ i2 ≠ j1 ∧
          C.gates[i1].op = .not ∧ C.gates[i2].op = .or ∧ C.gates[j1].op = .and ∧
          (C.gates[i1].inputs.take 1).contains v.val ∧ (C.gates[i2].inputs.take 2).contains v.val ∧
          (C.gates[j1].inputs.take 2).contains (n + i1) ∧
          (∀ (j : ℕ) (hj : j < C.gates.length),
            (C.gates[j].inputs.take (bif C.gates[j].op.eval [false] then 1 else 2)).contains (n + i1) → j = j1)) →
      (∃ v' ∉ A, ∃ g ∈ readers v', g.op = .and) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (noAndReader : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length = 2 ∧
        ∃ i1 i2 j1, ∃ (h1 : i1 < C.gates.length) (h2 : i2 < C.gates.length) (h3 : j1 < C.gates.length),
          i1 < j1 ∧ i1 ≠ i2 ∧ i2 ≠ j1 ∧
          C.gates[i1].op = .not ∧ C.gates[i2].op = .or ∧ C.gates[j1].op = .and ∧
          (C.gates[i1].inputs.take 1).contains v.val ∧ (C.gates[i2].inputs.take 2).contains v.val ∧
          (C.gates[j1].inputs.take 2).contains (n + i1) ∧
          (∀ (j : ℕ) (hj : j < C.gates.length),
            (C.gates[j].inputs.take (bif C.gates[j].op.eval [false] then 1 else 2)).contains (n + i1) → j = j1)) →
      (∀ v' ∉ A, ∀ g ∈ readers v', g.op ≠ .and) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G _ A C f readers hdeg hcycle hend hedge hfan hfun hminSz hread hhasNot
  have hmin : IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro E hE hEq
    exact hminSz E.size ⟨E, hE, le_rfl, fun x => congrFun (hEq.trans hfun) x⟩
  let effInputs : Gate → List ℕ := fun g =>
    g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have effInputs_not : ∀ g : Gate, g.op = .not → effInputs g = g.inputs.take 1 := by
    intro g h; simp [effInputs, h, GateOp.eval]
  have effInputs_and : ∀ g : Gate, g.op = .and → g.inputs.length ≤ 2 → effInputs g = g.inputs := by
    intro g h hlen; simp [effInputs, h, GateOp.eval, List.take_of_length_le hlen]
  have effInputs_or : ∀ g : Gate, g.op = .or → g.inputs.length ≤ 2 → effInputs g = g.inputs := by
    intro g h hlen; simp [effInputs, h, GateOp.eval, List.take_of_length_le hlen]
  obtain ⟨v, hvA, hvLen2, gnot, hgnotMem, hgnotOp⟩ := hhasNot
  have circuitWires_len : ∀ (gs : List Gate) (acc : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g r ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  have circuitWires_prefix : ∀ (gs : List Gate) (acc : List Bool) (w : ℕ), w < acc.length →
      (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).getD w false =
        acc.getD w false := by
    intro gs
    induction gs with
    | nil => intro acc w _; rfl
    | cons g r ih =>
      intro acc w hw
      simp only [List.foldl_cons]
      have hlen : w < (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]).length := by
        simp; omega
      rw [ih _ w hlen]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have circuitWires_gate : ∀ (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length),
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD (n + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i =>
          if i < n + j then (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false
          else false) := by
    intro gs x j hj
    let step : List Bool → Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
      have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
      have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
      calc gs = gs.take j ++ gs.drop j := h1.symm
        _ = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by rw [h2]
        _ = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by simp
    set acc := (gs.take j).foldl step (List.ofFn x)
    have haccLen : acc.length = n + j := by
      dsimp only [acc]
      rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have haccAt : ∀ u < n + j,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD u false = acc.getD u false := by
      intro u hu
      unfold Circuit.wires
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hu2 : u < (step acc gs[j]).length := by simp [step]; omega
      rw [circuitWires_prefix (gs.drop (j + 1)) _ u hu2]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
    have hmain : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD (n + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => acc.getD i false) := by
      unfold Circuit.wires
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hjlt : n + j < (step acc gs[j]).length := by simp [step, haccLen]
      rw [circuitWires_prefix (gs.drop (j + 1)) _ (n + j) hjlt]
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rw [hmain]
    congr 1
    apply List.map_congr_left
    intro i _
    split_ifs with hlt
    · exact (haccAt i hlt).symm
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : acc.length ≤ i)]
  let redirWire : ℕ → ℕ → ℕ → ℕ := fun cut rep u =>
    if u = cut then rep else if u > cut then u - 1 else u
  let redirGate : ℕ → ℕ → Gate → Gate := fun cut rep g =>
    ⟨g.op, g.inputs.map (redirWire cut rep)⟩
  let deleteRedirectCircuit : ℕ → ℕ → Circuit := fun i rep =>
    let oob := n + C.gates.length
    let pre := (C.gates.take i).map fun g =>
      ⟨g.op, g.inputs.map (fun u => if u ≥ n + i then oob else u)⟩
    let post := (C.gates.drop (i + 1)).map (redirGate (n + i) rep)
    ⟨pre ++ post, redirWire (n + i) rep C.output⟩
  have deleteRedirectCircuit_size : ∀ (i : ℕ), i < C.gates.length → ∀ (rep : ℕ),
      (deleteRedirectCircuit i rep).size = C.size - 1 := by
    intro i hi rep
    dsimp only [deleteRedirectCircuit, Circuit.size]
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  have deleteRedirectCircuit_fanInTwo : ∀ (i rep : ℕ), FanInTwo (deleteRedirectCircuit i rep) := by
    intro i rep g hg
    dsimp only [deleteRedirectCircuit] at hg
    rcases List.mem_append.mp hg with h1 | h2
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
      simpa [List.length_map] using hmin.1 g0 (List.mem_of_mem_take hg0)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
      simpa [redirGate, List.length_map] using hmin.1 g0 (List.mem_of_mem_drop hg0)
  have gate_eval_eq_of_eff : ∀ (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (f1 f2 : ℕ → Bool), (∀ u ∈ effInputs g, f1 u = f2 u) →
      g.op.eval (g.inputs.map f1) = g.op.eval (g.inputs.map f2) := by
    intro g hfan f1 f2 h
    rcases hfan.1 with hop | hop | hop
    · rw [effInputs_and g hop hfan.2] at h; rw [List.map_congr_left h]
    · rw [effInputs_or g hop hfan.2] at h; rw [List.map_congr_left h]
    · rw [Set.mem_singleton_iff] at hop
      rw [effInputs_not g hop] at h
      cases hgin : g.inputs with
      | nil => rfl
      | cons u tl =>
        simp only [hop, GateOp.eval, List.map_cons, List.headD_cons]
        have hu : u ∈ (u :: tl).take 1 := by simp
        rw [hgin] at h
        rw [h u hu]
  have deleteRedirectCircuit_eval : ∀ (i : ℕ) (hi : i < C.gates.length) (rep : ℕ),
      (rep < n + i ∨ rep = n + C.gates.length) →
      (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i) false =
        if rep < n + i then (C.wires (List.ofFn x)).getD rep false else false) →
      circuitFun n (deleteRedirectCircuit i rep) = circuitFun n C := by
    intro i hi rep hrep hrep_eq
    funext x
    let C' := deleteRedirectCircuit i rep
    have hlenC' : C'.gates.length = C.gates.length - 1 := deleteRedirectCircuit_size i hi rep
    have hwire : ∀ w < n + C'.gates.length,
        (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD w false =
          (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (if w ≥ n + i then w + 1 else w) false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hlt : w < n
        · rw [if_neg (by omega : ¬ w ≥ n + i)]
          unfold Circuit.wires
          rw [circuitWires_prefix C'.gates (List.ofFn x) w (by simp [hlt]),
              circuitWires_prefix C.gates (List.ofFn x) w (by simp [hlt])]
        · let j := w - n
          have hj : j < C'.gates.length := by omega
          have hwj : w = n + j := by omega
          rw [hwj]
          by_cases hji : j < i
          · rw [if_neg (by omega : ¬ n + j ≥ n + i)]
            have hget : C'.gates[j] = ⟨C.gates[j].op, C.gates[j].inputs.map (fun u => if u ≥ n + i then n + C.gates.length else u)⟩ := by
              have htl : ((C.gates.take i).map fun g => Gate.mk g.op (g.inputs.map fun u => if u ≥ n + i then n + C.gates.length else u)).length = i := by
                rw [List.length_map, List.length_take]; omega
              simp only [C', deleteRedirectCircuit] at hj ⊢
              rw [List.getElem_append_left (by omega)]
              simp only [List.getElem_map, List.getElem_take]
            rw [circuitWires_gate C'.gates x j hj, circuitWires_gate C.gates x j (by omega), hget]
            simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u _
            dsimp only [Function.comp_apply]
            by_cases hu : u < n + j
            · have hnotgeU : ¬ u ≥ n + i := by omega
              simp only [hnotgeU, hu, ↓reduceIte]
              have := ih u (by omega) (by omega)
              rw [if_neg hnotgeU] at this
              exact this
            · simp only [hu, ↓reduceIte]
              split_ifs <;> first | rfl | omega
          · rw [if_pos (by omega : n + j ≥ n + i), show n + j + 1 = n + (j + 1) by omega]
            have hj1 : j + 1 < C.gates.length := by omega
            have hget : C'.gates[j] = redirGate (n + i) rep C.gates[j + 1] := by
              have htl : ((C.gates.take i).map fun g => Gate.mk g.op (g.inputs.map fun u => if u ≥ n + i then n + C.gates.length else u)).length = i := by
                rw [List.length_map, List.length_take]; omega
              simp only [C', deleteRedirectCircuit] at hj ⊢
              rw [List.getElem_append_right (by omega)]
              simp only [List.getElem_map, List.getElem_drop, htl]
              congr 2; omega
            rw [circuitWires_gate C'.gates x j hj, circuitWires_gate C.gates x (j + 1) hj1, hget]
            simp only [redirGate, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u _
            dsimp only [Function.comp_apply, redirWire]
            by_cases huEq : u = n + i
            · subst huEq
              simp only [↓reduceIte, show n + i < n + (j + 1) by omega]
              rcases hrep with hrepLt | hrepOob
              · simp only [show rep < n + j by omega, ↓reduceIte]
                have := ih rep (by omega) (by omega)
                rw [if_neg (by omega : ¬ rep ≥ n + i)] at this
                have hre : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i) false =
                    (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD rep false := by
                  have h := hrep_eq x; rw [if_pos hrepLt] at h; exact h
                rw [this, hre]
              · simp only [hrepOob, show ¬ n + C.gates.length < n + j by omega, ↓reduceIte]
                have hre : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i) false = false := by
                  have h := hrep_eq x; rw [if_neg (by omega)] at h; exact h
                rw [hre]
            · simp only [huEq, ↓reduceIte]
              by_cases huGt : u > n + i
              · simp only [huGt, ↓reduceIte]
                by_cases huLt : u < n + (j + 1)
                · simp only [show u - 1 < n + j by omega, huLt, ↓reduceIte]
                  have := ih (u - 1) (by omega) (by omega)
                  rw [if_pos (by omega : u - 1 ≥ n + i), show u - 1 + 1 = u by omega] at this
                  exact this
                · simp only [show ¬ u - 1 < n + j by omega, huLt, ↓reduceIte]
              · simp only [huGt, show u < n + j by omega, show u < n + (j + 1) by omega, ↓reduceIte]
                have := ih u (by omega) (by omega)
                rw [if_neg (by omega : ¬ u ≥ n + i)] at this
                exact this
    change (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD (redirWire (n + i) rep C.output) false =
      (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD C.output false
    dsimp only [redirWire]
    by_cases houtEq : C.output = n + i
    · simp only [houtEq, ↓reduceIte]
      rcases hrep with hrepLt | hrepOob
      · have := hwire rep (by omega)
        rw [if_neg (by omega : ¬ rep ≥ n + i)] at this
        have hre : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i) false =
            (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD rep false := by
          have h := hrep_eq x; rw [if_pos hrepLt] at h; exact h
        rw [this, hre]
      · have hre : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i) false = false := by
          have h := hrep_eq x; rw [if_neg (by omega)] at h; exact h
        rw [hrepOob, hre]
        have hlenW : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).length = n + C'.gates.length := by
          unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).length ≤ n + C.gates.length)]
        rfl
    · simp only [houtEq, ↓reduceIte]
      by_cases houtGt : C.output > n + i
      · simp only [houtGt, ↓reduceIte]
        by_cases houtLt : C.output < n + C.gates.length
        · have := hwire (C.output - 1) (by omega)
          rw [if_pos (by omega : C.output - 1 ≥ n + i), show C.output - 1 + 1 = C.output by omega] at this
          exact this
        · have hlenW1 : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).length = n + C'.gates.length := by
            unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
          have hlenW2 : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).length = n + C.gates.length := by
            unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).length ≤ C.output - 1),
            List.getElem?_eq_none (by omega : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).length ≤ C.output)]
      · simp only [houtGt, ↓reduceIte]
        have := hwire C.output (by omega)
        rw [if_neg (by omega : ¬ C.output ≥ n + i)] at this
        exact this
  have minimal_no_const_false : ∀ (i : ℕ) (hi : i < C.gates.length),
      ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i) false = true := by
    intro i hi
    by_contra h
    push Not at h
    have hfalse : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i) false = false := by
      intro x; cases hv : (C.wires (List.ofFn x)).getD (n + i) false
      · rfl
      · exact False.elim (h x hv)
    have hle := hmin.2 (deleteRedirectCircuit i (n + C.gates.length))
      (deleteRedirectCircuit_fanInTwo i (n + C.gates.length))
      (deleteRedirectCircuit_eval i hi (n + C.gates.length) (Or.inr rfl) (fun x => by rw [if_neg (by omega), hfalse x]))
    have hsz := deleteRedirectCircuit_size i hi (n + C.gates.length)
    unfold Circuit.size at hsz hle
    omega
  have minimal_no_dup_wire : ∀ (i : ℕ) (hi : i < C.gates.length) (rep : ℕ), rep < n + i →
      ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i) false ≠ (C.wires (List.ofFn x)).getD rep false := by
    intro i hi rep hrep
    by_contra h
    push Not at h
    have hle := hmin.2 (deleteRedirectCircuit i rep)
      (deleteRedirectCircuit_fanInTwo i rep)
      (deleteRedirectCircuit_eval i hi rep (Or.inl hrep) (fun x => by rw [if_pos hrep]; exact h x))
    have hsz := deleteRedirectCircuit_size i hi rep
    unfold Circuit.size at hsz hle
    omega
  have minimal_gate_has_reader : ∀ (i : ℕ) (hi : i < C.gates.length), n + i ≠ C.output →
      ∃ j, ∃ hj : j < C.gates.length, i < j ∧ (n + i) ∈ effInputs C.gates[j] := by
    intro i hi hne_out
    by_contra h
    push Not at h
    let C' := deleteRedirectCircuit i (n + C.gates.length)
    have heval' : circuitFun n C' = circuitFun n C := by
      funext x
      have hlenC' : C'.gates.length = C.gates.length - 1 := deleteRedirectCircuit_size i hi (n + C.gates.length)
      have hwire : ∀ w < n + C'.gates.length,
          (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD w false =
            (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (if w ≥ n + i then w + 1 else w) false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hlt : w < n
          · rw [if_neg (by omega : ¬ w ≥ n + i)]
            unfold Circuit.wires
            rw [circuitWires_prefix C'.gates (List.ofFn x) w (by simp [hlt]),
                circuitWires_prefix C.gates (List.ofFn x) w (by simp [hlt])]
          · let j := w - n
            have hj : j < C'.gates.length := by omega
            have hwj : w = n + j := by omega
            rw [hwj]
            by_cases hji : j < i
            · rw [if_neg (by omega : ¬ n + j ≥ n + i)]
              have hget : C'.gates[j] = ⟨C.gates[j].op, C.gates[j].inputs.map (fun u => if u ≥ n + i then n + C.gates.length else u)⟩ := by
                have htl : ((C.gates.take i).map fun g => Gate.mk g.op (g.inputs.map fun u => if u ≥ n + i then n + C.gates.length else u)).length = i := by
                  rw [List.length_map, List.length_take]; omega
                simp only [C', deleteRedirectCircuit] at hj ⊢
                rw [List.getElem_append_left (by omega)]
                simp only [List.getElem_map, List.getElem_take]
              rw [circuitWires_gate C'.gates x j hj, circuitWires_gate C.gates x j (by omega), hget]
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro u _
              dsimp only [Function.comp_apply]
              by_cases hu : u < n + j
              · have hnotgeU : ¬ u ≥ n + i := by omega
                simp only [hnotgeU, hu, ↓reduceIte]
                have := ih u (by omega) (by omega)
                rw [if_neg hnotgeU] at this
                exact this
              · simp only [hu, ↓reduceIte]
                split_ifs <;> first | rfl | omega
            · rw [if_pos (by omega : n + j ≥ n + i), show n + j + 1 = n + (j + 1) by omega]
              have hj1 : j + 1 < C.gates.length := by omega
              have hget : C'.gates[j] = redirGate (n + i) (n + C.gates.length) C.gates[j + 1] := by
                have htl : ((C.gates.take i).map fun g => Gate.mk g.op (g.inputs.map fun u => if u ≥ n + i then n + C.gates.length else u)).length = i := by
                  rw [List.length_map, List.length_take]; omega
                simp only [C', deleteRedirectCircuit] at hj ⊢
                rw [List.getElem_append_right (by omega)]
                simp only [List.getElem_map, List.getElem_drop, htl]
                congr 2; omega
              rw [circuitWires_gate C'.gates x j hj, circuitWires_gate C.gates x (j + 1) hj1, hget]
              simp only [redirGate, List.map_map]
              apply gate_eval_eq_of_eff C.gates[j + 1] (hmin.1 C.gates[j + 1] (List.getElem_mem hj1))
              intro u huEff
              dsimp only [Function.comp_apply, redirWire]
              have hneI : u ≠ n + i := fun heq => h (j + 1) hj1 (by omega) (heq ▸ huEff)
              simp only [hneI, ↓reduceIte]
              by_cases huGt : u > n + i
              · simp only [huGt, ↓reduceIte]
                by_cases huLt : u < n + (j + 1)
                · simp only [show u - 1 < n + j by omega, huLt, ↓reduceIte]
                  have := ih (u - 1) (by omega) (by omega)
                  rw [if_pos (by omega : u - 1 ≥ n + i), show u - 1 + 1 = u by omega] at this
                  exact this
                · simp only [show ¬ u - 1 < n + j by omega, huLt, ↓reduceIte]
              · simp only [huGt, show u < n + j by omega, show u < n + (j + 1) by omega, ↓reduceIte]
                have := ih u (by omega) (by omega)
                rw [if_neg (by omega : ¬ u ≥ n + i)] at this
                exact this
      change (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD (redirWire (n + i) (n + C.gates.length) C.output) false =
        (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD C.output false
      dsimp only [redirWire]
      simp only [hne_out.symm, ↓reduceIte]
      by_cases houtGt : C.output > n + i
      · simp only [houtGt, ↓reduceIte]
        by_cases houtLt : C.output < n + C.gates.length
        · have := hwire (C.output - 1) (by omega)
          rw [if_pos (by omega : C.output - 1 ≥ n + i), show C.output - 1 + 1 = C.output by omega] at this
          exact this
        · have hlenW1 : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).length = n + C'.gates.length := by
            unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
          have hlenW2 : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).length = n + C.gates.length := by
            unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).length ≤ C.output - 1),
            List.getElem?_eq_none (by omega : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).length ≤ C.output)]
      · simp only [houtGt, ↓reduceIte]
        have := hwire C.output (by omega)
        rw [if_neg (by omega : ¬ C.output ≥ n + i)] at this
        exact this
    have hle := hmin.2 C' (deleteRedirectCircuit_fanInTwo i (n + C.gates.length)) heval'
    have hsz := deleteRedirectCircuit_size i hi (n + C.gates.length)
    dsimp only [C'] at hle
    unfold Circuit.size at hsz hle
    omega
  let evalSym : List Bool → (Bool ⊕ ℕ) → Bool := fun ws s =>
    match s with
    | Sum.inl b => b
    | Sum.inr u => ws.getD u false
  let simplifyOne : ℕ → List (Bool ⊕ ℕ) → Gate → Option Gate × (Bool ⊕ ℕ) := fun k env g =>
    match g.op with
    | .not =>
      match g.inputs with
      | [] => (none, Sum.inl true)
      | u :: _ =>
        match env.getD u (Sum.inl false) with
        | Sum.inl b => (none, Sum.inl (!b))
        | Sum.inr u' => (some ⟨.not, [u']⟩, Sum.inr (n + k))
    | .and =>
      match g.inputs with
      | [] => (none, Sum.inl true)
      | [u] => (none, env.getD u (Sum.inl false))
      | [u1, u2] =>
        match env.getD u1 (Sum.inl false) with
        | Sum.inl false => (none, Sum.inl false)
        | Sum.inl true => (none, env.getD u2 (Sum.inl false))
        | Sum.inr a =>
          match env.getD u2 (Sum.inl false) with
          | Sum.inl false => (none, Sum.inl false)
          | Sum.inl true => (none, Sum.inr a)
          | Sum.inr b => (some ⟨.and, [a, b]⟩, Sum.inr (n + k))
      | _ => (none, Sum.inl false)
    | .or =>
      match g.inputs with
      | [] => (none, Sum.inl false)
      | [u] => (none, env.getD u (Sum.inl false))
      | [u1, u2] =>
        match env.getD u1 (Sum.inl false) with
        | Sum.inl true => (none, Sum.inl true)
        | Sum.inl false => (none, env.getD u2 (Sum.inl false))
        | Sum.inr a =>
          match env.getD u2 (Sum.inl false) with
          | Sum.inl true => (none, Sum.inl true)
          | Sum.inl false => (none, Sum.inr a)
          | Sum.inr b => (some ⟨.or, [a, b]⟩, Sum.inr (n + k))
      | _ => (none, Sum.inl false)
    | _ => (none, Sum.inl false)
  let simplifyGate : (List Gate × List (Bool ⊕ ℕ)) → Gate → (List Gate × List (Bool ⊕ ℕ)) := fun st g =>
    let r := simplifyOne st.1.length st.2 g
    (match r.1 with | none => st.1 | some ng => st.1 ++ [ng], st.2 ++ [r.2])
  let initEnv : List (Bool ⊕ ℕ) :=
    (List.range n).map fun i => if i = v.val then Sum.inl false else Sum.inr i
  have simplifyGate_env_len : ∀ st g, (simplifyGate st g).2.length = st.2.length + 1 := by
    intro st g; simp [simplifyGate]
  have simplifyGate_gs_le : ∀ st g, (simplifyGate st g).1.length ≤ st.1.length + 1 := by
    intro st g; dsimp only [simplifyGate]; cases (simplifyOne st.1.length st.2 g).1 <;> simp
  have simplifyGate_env_prefix : ∀ st g w, w < st.2.length →
      (simplifyGate st g).2.getD w (Sum.inl false) = st.2.getD w (Sum.inl false) := by
    intro st g w hw
    simp only [simplifyGate, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have simplifyFold_env_len : ∀ (gs : List Gate) st,
      (gs.foldl simplifyGate st).2.length = st.2.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro st; simp
    | cons g r ih => intro st; simp only [List.foldl_cons, ih, simplifyGate_env_len, List.length_cons]; omega
  have simplifyFold_env_prefix : ∀ (gs : List Gate) st w, w < st.2.length →
      (gs.foldl simplifyGate st).2.getD w (Sum.inl false) = st.2.getD w (Sum.inl false) := by
    intro gs
    induction gs with
    | nil => intro st w _; rfl
    | cons g r ih =>
      intro st w hw
      simp only [List.foldl_cons]
      have hlt : w < (simplifyGate st g).2.length := by rw [simplifyGate_env_len]; omega
      rw [ih _ w hlt, simplifyGate_env_prefix st g w hw]
  have simplifyGate_elim_of_const_input : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ u ∈ effInputs g, ∀ b : Bool, st.2.getD u (Sum.inl false) = Sum.inl b →
      (simplifyGate st g).1.length = st.1.length := by
    intro st g hfan u hu b hconst
    dsimp only [simplifyGate, simplifyOne]
    rcases hfan.1 with hop | hop | hop
    · rw [effInputs_and g hop hfan.2] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        cases tl with
        | nil => simp [hop, hgin]
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · rw [hop]; dsimp only []; rw [hconst]; cases b <;> (cases st.2.getD u2 (Sum.inl false) with | inl b2 => cases b2 <;> rfl | inr _ => rfl)
            · rw [hop]; dsimp only []; rw [hconst]; cases st.2.getD u1 (Sum.inl false) with | inl b1 => cases b1 <;> (cases b <;> rfl) | inr _ => cases b <;> rfl
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [effInputs_or g hop hfan.2] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        cases tl with
        | nil => simp [hop]
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · rw [hop]; dsimp only []; rw [hconst]; cases b <;> (cases st.2.getD u2 (Sum.inl false) with | inl b2 => cases b2 <;> rfl | inr _ => rfl)
            · rw [hop]; dsimp only []; rw [hconst]; cases st.2.getD u1 (Sum.inl false) with | inl b1 => cases b1 <;> (cases b <;> rfl) | inr _ => cases b <;> rfl
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [Set.mem_singleton_iff] at hop
      rw [effInputs_not g hop] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        rw [hgin] at hu
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        subst hu
        rw [hop]; dsimp only []; rw [hconst]
  have simplifyGate_const_of_nonOr_false : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      g.op ≠ .or → ∀ u ∈ effInputs g, st.2.getD u (Sum.inl false) = Sum.inl false →
      ∃ c : Bool, (simplifyGate st g).2.getD st.2.length (Sum.inl false) = Sum.inl c := by
    intro st g hfan hnonOr u hu hconst
    have hlast : ∀ a : Bool ⊕ ℕ, (st.2 ++ [a]).getD st.2.length (Sum.inl false) = a := by
      intro a; simp [List.getD_eq_getElem?_getD]
    dsimp only [simplifyGate, simplifyOne]
    rcases hfan.1 with hop | hop | hop
    · rw [effInputs_and g hop hfan.2] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        cases tl with
        | nil =>
          rw [hgin] at hu; simp at hu; subst hu
          exact ⟨false, by rw [hop]; dsimp only []; rw [hlast, hconst]⟩
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · rw [hop]; dsimp only []; rw [hconst]; exact ⟨false, hlast _⟩
            · rw [hop]; dsimp only []; rw [hconst]; cases st.2.getD u1 (Sum.inl false) with
              | inl b1 => cases b1 <;> exact ⟨false, hlast _⟩
              | inr _ => exact ⟨false, hlast _⟩
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · exact False.elim (hnonOr hop)
    · rw [Set.mem_singleton_iff] at hop
      rw [effInputs_not g hop] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        rw [hgin] at hu
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        subst hu
        rw [hop]; dsimp only []; rw [hconst]
        exact ⟨true, hlast _⟩
  have simplifyGate_const_of_two_const : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ u1 u2, u1 ≠ u2 → u1 ∈ effInputs g → u2 ∈ effInputs g →
      ∀ b1 b2 : Bool, st.2.getD u1 (Sum.inl false) = Sum.inl b1 →
      st.2.getD u2 (Sum.inl false) = Sum.inl b2 →
      ∃ c : Bool, (simplifyGate st g).2.getD st.2.length (Sum.inl false) = Sum.inl c := by
    intro st g hfan u1 u2 hne hu1 hu2 b1 b2 hc1 hc2
    have hlast : ∀ a : Bool ⊕ ℕ, (st.2 ++ [a]).getD st.2.length (Sum.inl false) = a := by
      intro a; simp [List.getD_eq_getElem?_getD]
    dsimp only [simplifyGate, simplifyOne]
    rcases hfan.1 with hop | hop | hop
    · rw [effInputs_and g hop hfan.2] at hu1 hu2
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu1
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hgin] at hu1 hu2; simp at hu1 hu2; exact False.elim (hne (hu1.trans hu2.symm))
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu1 hu2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu1 hu2
            rcases hu1 with h1 | h1 <;> rcases hu2 with h2 | h2
            · exact False.elim (hne (h1.trans h2.symm))
            · subst h1; subst h2; rw [hop]; dsimp only []; rw [hc1, hc2]; cases b1 <;> cases b2 <;> exact ⟨_, hlast _⟩
            · subst h1; subst h2; rw [hop]; dsimp only []; rw [hc1, hc2]; cases b1 <;> cases b2 <;> exact ⟨_, hlast _⟩
            · exact False.elim (hne (h1.trans h2.symm))
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [effInputs_or g hop hfan.2] at hu1 hu2
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu1
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hgin] at hu1 hu2; simp at hu1 hu2; exact False.elim (hne (hu1.trans hu2.symm))
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu1 hu2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu1 hu2
            rcases hu1 with h1 | h1 <;> rcases hu2 with h2 | h2
            · exact False.elim (hne (h1.trans h2.symm))
            · subst h1; subst h2; rw [hop]; dsimp only []; rw [hc1, hc2]; cases b1 <;> cases b2 <;> exact ⟨_, hlast _⟩
            · subst h1; subst h2; rw [hop]; dsimp only []; rw [hc1, hc2]; cases b1 <;> cases b2 <;> exact ⟨_, hlast _⟩
            · exact False.elim (hne (h1.trans h2.symm))
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [Set.mem_singleton_iff] at hop
      rw [effInputs_not g hop] at hu1 hu2
      cases hgin : g.inputs with
      | nil => rw [hgin] at hu1; simp at hu1
      | cons a tl =>
        rw [hgin] at hu1 hu2
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hu1 hu2
        exact False.elim (hne (hu1.trans hu2.symm))
  have simplifyGate_sound : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ t ∈ st.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) →
      (∀ s ∈ st.2, ∀ u, s = Sum.inr u → u < n + st.1.length) →
      ∀ (x : Fin n → Bool) (ws : List Bool), ws.length = st.2.length →
      (∀ w < st.2.length, ws.getD w false = evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD w (Sum.inl false))) →
      (∀ t ∈ (simplifyGate st g).1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
      (∀ s ∈ (simplifyGate st g).2, ∀ u, s = Sum.inr u → u < n + (simplifyGate st g).1.length) ∧
      ∀ w < st.2.length + 1,
        (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false =
          evalSym (Circuit.wires ⟨(simplifyGate st g).1, 0⟩ (List.ofFn x)) ((simplifyGate st g).2.getD w (Sum.inl false)) := by
    intro st g hfan hfanSt hbound x ws hwsLen heq
    have hread : ∀ u, ws.getD u false = evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD u (Sum.inl false)) := by
      intro u
      by_cases hu : u < st.2.length
      · exact heq u hu
      · have h1 : ws.getD u false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ u)]
        have h2 : st.2.getD u (Sum.inl false) = Sum.inl false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : st.2.length ≤ u)]
        rw [h1, h2]
    have hgetBound : ∀ u k, st.2.getD u (Sum.inl false) = Sum.inr k → k < n + st.1.length := by
      intro u k hk
      by_cases hu : u < st.2.length
      · have hmem : st.2.getD u (Sum.inl false) ∈ st.2 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]
          exact List.getElem_mem hu
        exact hbound _ hmem k hk
      · have h2 : st.2.getD u (Sum.inl false) = Sum.inl false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : st.2.length ≤ u)]
        rw [h2] at hk; cases hk
    have hnoEmit : ∀ (a : Bool ⊕ ℕ),
        (∀ u, a = Sum.inr u → u < n + st.1.length) →
        g.op.eval (g.inputs.map fun i => ws.getD i false) =
          evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) a →
        (∀ t ∈ st.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
        (∀ s ∈ st.2 ++ [a], ∀ u, s = Sum.inr u → u < n + st.1.length) ∧
        ∀ w < st.2.length + 1,
          (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false =
            evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) ((st.2 ++ [a]).getD w (Sum.inl false)) := by
      intro a haB haE
      refine ⟨hfanSt, ?_, ?_⟩
      · intro s hs u hu
        rcases List.mem_append.mp hs with h1 | h2
        · exact hbound s h1 u hu
        · rw [List.mem_singleton.mp h2] at hu; exact haB u hu
      · intro w hw
        by_cases hlt : w < st.2.length
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < ws.length),
            List.getElem?_append_left hlt]
          simpa only [List.getD_eq_getElem?_getD] using heq w hlt
        · have hweq : w = st.2.length := by omega
          subst hweq
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega : ws.length ≤ st.2.length),
              List.getElem?_append_right le_rfl]
          simp only [hwsLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact haE
    have hEmit : ∀ (ng : Gate),
        (ng.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ ng.inputs.length ≤ 2) →
        g.op.eval (g.inputs.map fun i => ws.getD i false) =
          ng.op.eval (ng.inputs.map fun i => (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).getD i false) →
        (∀ t ∈ st.1 ++ [ng], t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
        (∀ s ∈ st.2 ++ [Sum.inr (n + st.1.length)], ∀ u, s = Sum.inr u → u < n + (st.1 ++ [ng]).length) ∧
        ∀ w < st.2.length + 1,
          (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false =
            evalSym (Circuit.wires ⟨st.1 ++ [ng], 0⟩ (List.ofFn x)) ((st.2 ++ [Sum.inr (n + st.1.length)]).getD w (Sum.inl false)) := by
      intro ng hngF hngE
      have hlenW : (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).length = n + st.1.length := by
        unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
      have hWapp : Circuit.wires ⟨st.1 ++ [ng], 0⟩ (List.ofFn x) =
          Circuit.wires ⟨st.1, 0⟩ (List.ofFn x) ++
            [ng.op.eval (ng.inputs.map fun i => (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).getD i false)] := by
        unfold Circuit.wires; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        rcases List.mem_append.mp ht with h1 | h2
        · exact hfanSt t h1
        · rw [List.mem_singleton.mp h2]; exact hngF
      · intro s hs u hu
        rw [List.length_append, List.length_singleton]
        rcases List.mem_append.mp hs with h1 | h2
        · have := hbound s h1 u hu; omega
        · rw [List.mem_singleton.mp h2] at hu; injection hu with hEq; omega
      · intro w hw
        by_cases hlt : w < st.2.length
        · have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = ws.getD w false := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < ws.length)]
          have h2 : (st.2 ++ [Sum.inr (n + st.1.length)]).getD w (Sum.inl false) = st.2.getD w (Sum.inl false) := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [h1, h2, heq w hlt, hWapp]
          cases hsw : st.2.getD w (Sum.inl false) with
          | inl b => rfl
          | inr u =>
            have hu : u < n + st.1.length := hgetBound w u hsw
            simp only [evalSym, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).length)]
        · have hweq : w = st.2.length := by omega
          subst hweq
          have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD st.2.length false =
              g.op.eval (g.inputs.map fun i => ws.getD i false) := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega : ws.length ≤ st.2.length)]
            simp [hwsLen]
          have h2 : (st.2 ++ [Sum.inr (n + st.1.length)]).getD st.2.length (Sum.inl false) = Sum.inr (n + st.1.length) := by
            simp [List.getD_eq_getElem?_getD]
          rw [h1, h2, hWapp]
          simp only [evalSym, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega : (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).length ≤ n + st.1.length)]
          simp only [hlenW, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact hngE
    rcases hfan.1 with hop | hop | hop
    · cases hgin : g.inputs with
      | nil =>
        have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
          dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
        rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by simp [hop, hgin, GateOp.eval, evalSym])
      | cons u1 tl =>
        cases tl with
        | nil =>
          have hres : simplifyGate st g = (st.1, st.2 ++ [st.2.getD u1 (Sum.inl false)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
          rw [hres, ← hgin]; exact hnoEmit (st.2.getD u1 (Sum.inl false)) (hgetBound u1) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hread u1)
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            cases h1 : st.2.getD u1 (Sum.inl false) with
            | inl b1 =>
              cases b1
              · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
                rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1, h1]; rfl)
              · cases h2 : st.2.getD u2 (Sum.inl false) with
                | inl b2 =>
                  cases b2
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                | inr b =>
                  have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr b]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr b) (fun _ h => hgetBound u2 _ (h2.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1, hread u2, h1, h2]; rfl)
            | inr a =>
              cases h2 : st.2.getD u2 (Sum.inl false) with
              | inl b2 =>
                cases b2
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr a]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr a) (fun _ h => hgetBound u1 _ (h1.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
              | inr b =>
                have hres : simplifyGate st g = (st.1 ++ [⟨.and, [a, b]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                rw [hres, ← hgin]; exact hEmit ⟨.and, [a, b]⟩ (by simp) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1, hread u2, h1, h2])
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · cases hgin : g.inputs with
      | nil =>
        have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
          dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
        rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by simp [hop, hgin, GateOp.eval, evalSym])
      | cons u1 tl =>
        cases tl with
        | nil =>
          have hres : simplifyGate st g = (st.1, st.2 ++ [st.2.getD u1 (Sum.inl false)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
          rw [hres, ← hgin]; exact hnoEmit (st.2.getD u1 (Sum.inl false)) (hgetBound u1) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hread u1)
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            cases h1 : st.2.getD u1 (Sum.inl false) with
            | inl b1 =>
              cases b1
              · cases h2 : st.2.getD u2 (Sum.inl false) with
                | inl b2 =>
                  cases b2
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                | inr b =>
                  have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr b]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr b) (fun _ h => hgetBound u2 _ (h2.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1, hread u2, h1, h2]; rfl)
              · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
                rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1, h1]; rfl)
            | inr a =>
              cases h2 : st.2.getD u2 (Sum.inl false) with
              | inl b2 =>
                cases b2
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr a]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr a) (fun _ h => hgetBound u1 _ (h1.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
              | inr b =>
                have hres : simplifyGate st g = (st.1 ++ [⟨.or, [a, b]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                rw [hres, ← hgin]; exact hEmit ⟨.or, [a, b]⟩ (by simp) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1, hread u2, h1, h2])
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [Set.mem_singleton_iff] at hop
      cases hgin : g.inputs with
      | nil =>
        have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
          dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
        rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by simp [hop, hgin, GateOp.eval, evalSym])
      | cons u1 tl =>
        cases h1 : st.2.getD u1 (Sum.inl false) with
        | inl b1 =>
          have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl (!b1)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
          rw [hres, ← hgin]; exact hnoEmit (Sum.inl (!b1)) (fun _ h => by cases h) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.headD_cons]
            rw [hread u1, h1])
        | inr a =>
          have hres : simplifyGate st g = (st.1 ++ [⟨.not, [a]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
          rw [hres, ← hgin]; exact hEmit ⟨.not, [a]⟩ (by simp) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.headD_cons]
            rw [hread u1, h1])
  have simplifyFold_sound : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      let st := gs.foldl simplifyGate ([], initEnv)
      (∀ t ∈ st.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
      (∀ s ∈ st.2, ∀ u, s = Sum.inr u → u < n + st.1.length) ∧
      ∀ (x : Fin n → Bool) (w : ℕ), w < n + gs.length →
        (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x v false))).getD w false =
          evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD w (Sum.inl false)) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨by simp, ?_, ?_⟩
      · intro s hs u hu
        simp only [List.foldl_nil, initEnv, List.mem_map, List.mem_range, List.length_nil] at hs ⊢
        obtain ⟨i, hi, rfl⟩ := hs
        by_cases hEq : i = v.val
        · rw [if_pos hEq] at hu; cases hu
        · rw [if_neg hEq] at hu; injection hu with hU; omega
      · intro x w hw
        have hwn : w < n := by simp at hw; omega
        simp only [List.foldl_nil, initEnv, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range hwn, Option.map_some, Option.getD_some]
        rw [List.getElem?_ofFn, dif_pos hwn, Option.getD_some]
        split_ifs with heq
        · have hfv : (⟨w, hwn⟩ : Fin n) = v := Fin.ext heq
          rw [hfv, Function.update_self]
        · have hne : (⟨w, hwn⟩ : Fin n) ≠ v := fun h => heq (congrArg Fin.val h)
          rw [Function.update_of_ne hne]
          simp only [evalSym, Circuit.wires, List.foldl_nil,
            List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hwn, Option.getD_some]
    | append_singleton gs g ih =>
      intro hfan
      have hfan1 : ∀ t ∈ gs, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2 :=
        fun t ht => hfan t (List.mem_append_left _ ht)
      have hfanG := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
      obtain ⟨hfanSt, hboundSt, heqSt⟩ := ih hfan1
      set st := gs.foldl simplifyGate ([], initEnv)
      have hstLen : st.2.length = n + gs.length := by
        dsimp only [st]; rw [simplifyFold_env_len]; simp [initEnv]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hstep : ∀ x : Fin n → Bool,
          (∀ t ∈ (simplifyGate st g).1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
          (∀ s ∈ (simplifyGate st g).2, ∀ u, s = Sum.inr u → u < n + (simplifyGate st g).1.length) ∧
          ∀ w < st.2.length + 1,
            ((gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x v false))) ++
              [g.op.eval (g.inputs.map fun i => (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x v false))).getD i false)]).getD w false =
              evalSym (Circuit.wires ⟨(simplifyGate st g).1, 0⟩ (List.ofFn x)) ((simplifyGate st g).2.getD w (Sum.inl false)) := by
        intro x
        have hwsLen : (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x v false))).length = st.2.length := by
          rw [circuitWires_len, List.length_ofFn, hstLen]
        exact simplifyGate_sound st g hfanG hfanSt hboundSt x _ hwsLen (fun w hw => heqSt x w (by omega))
      have h0 := hstep (fun _ => false)
      refine ⟨h0.1, h0.2.1, fun x w hw => ?_⟩
      rw [List.length_append, List.length_singleton] at hw
      exact (hstep x).2.2 w (by omega)
  have simplifyFold_size_bound : ∀ (gs : List Gate) (S : Finset ℕ),
      (∀ k ∈ S, ∃ hk : k < gs.length,
        (simplifyGate ((gs.take k).foldl simplifyGate ([], initEnv)) gs[k]).1.length =
          ((gs.take k).foldl simplifyGate ([], initEnv)).1.length) →
      (gs.foldl simplifyGate ([], initEnv)).1.length + S.card ≤ gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro S hS
      have hSe : S = ∅ := by
        ext k; simp only [Finset.notMem_empty, iff_false]
        intro hk; obtain ⟨hklt, _⟩ := hS k hk; simp at hklt
      simp [hSe]
    | append_singleton gs g ih =>
      intro S hS
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton]
      set S' := S.erase gs.length
      have hS' : ∀ k ∈ S', ∃ hk : k < gs.length,
          (simplifyGate ((gs.take k).foldl simplifyGate ([], initEnv)) gs[k]).1.length =
            ((gs.take k).foldl simplifyGate ([], initEnv)).1.length := by
        intro k hk
        have hkS := Finset.mem_of_mem_erase hk
        have hkne := Finset.ne_of_mem_erase hk
        obtain ⟨hk1, hk2⟩ := hS k hkS
        rw [List.length_append, List.length_singleton] at hk1
        have hklt : k < gs.length := by omega
        refine ⟨hklt, ?_⟩
        have htake : (gs ++ [g]).take k = gs.take k := List.take_append_of_le_length (Nat.le_of_lt hklt)
        have hget : (gs ++ [g])[k]'(by rw [List.length_append, List.length_singleton]; omega) = gs[k] :=
          List.getElem_append_left hklt
        simp only [htake, hget] at hk2
        exact hk2
      have hih := ih S' hS'
      by_cases hmem : gs.length ∈ S
      · have hcard : S.card = S'.card + 1 := by
          have h := Finset.card_erase_add_one hmem
          change S'.card + 1 = S.card at h; omega
        obtain ⟨_, h1⟩ := hS gs.length hmem
        have htake : (gs ++ [g]).take gs.length = gs := by simp
        have hget : (gs ++ [g])[gs.length]'(by simp) = g := by simp
        simp only [htake, hget] at h1
        omega
      · have hcard : S'.card = S.card := by simp [S', Finset.erase_eq_of_notMem hmem]
        have hle := simplifyGate_gs_le (gs.foldl simplifyGate ([], initEnv)) g
        omega
  have hnonconst : ∃ x1 x2 : Fin n → Bool,
      circuitFun n C (Function.update x1 v false) ≠ circuitFun n C (Function.update x2 v false) := by
    obtain ⟨u, w, huw⟩ := hedge
    have hkeep : ∃ a b : Fin n, G.Adj a b ∧ a ≠ v ∧ b ≠ v := by
      by_cases huv : u = v
      · subst huv
        have hdegW : (G.neighborSet w).ncard = 3 := hdeg w (hend w u huw.symm)
        have hne : ∃ j, G.Adj w j ∧ j ≠ u := by
          by_contra! hall
          have hsub : G.neighborSet w ⊆ {u} := fun j hj => Set.mem_singleton_iff.mpr (hall j hj)
          have hle := Set.ncard_le_ncard hsub
          rw [hdegW, Set.ncard_singleton] at hle; omega
        obtain ⟨j, hwj, hju⟩ := hne
        exact ⟨w, j, hwj, huw.ne.symm, hju⟩
      · by_cases hwv : w = v
        · subst hwv
          have hdegU : (G.neighborSet u).ncard = 3 := hdeg u (hend u w huw)
          have hne : ∃ j, G.Adj u j ∧ j ≠ w := by
            by_contra! hall
            have hsub : G.neighborSet u ⊆ {w} := fun j hj => Set.mem_singleton_iff.mpr (hall j hj)
            have hle := Set.ncard_le_ncard hsub
            rw [hdegU, Set.ncard_singleton] at hle; omega
          obtain ⟨j, huj, hjw⟩ := hne
          exact ⟨u, j, huj, huv, hjw⟩
        · exact ⟨u, w, huw, huv, hwv⟩
    obtain ⟨a, b, hab, hav, hbv⟩ := hkeep
    refine ⟨fun _ => false, fun z => decide (z = a ∨ z = b), ?_⟩
    rw [hfun]
    dsimp only [f]
    unfold graphFun
    have h0 : (decide (∃ x ∈ A, Function.update (fun _ : Fin n => false) v false x = true) ||
        decide (∃ i j, G.Adj i j ∧ Function.update (fun _ : Fin n => false) v false i = true ∧
          Function.update (fun _ : Fin n => false) v false j = true)) = false := by
      simp [Function.update]
    have h1 : (decide (∃ x ∈ A, Function.update (fun z : Fin n => decide (z = a ∨ z = b)) v false x = true) ||
        decide (∃ i j, G.Adj i j ∧ Function.update (fun z : Fin n => decide (z = a ∨ z = b)) v false i = true ∧
          Function.update (fun z : Fin n => decide (z = a ∨ z = b)) v false j = true)) = true := by
      rw [Bool.or_eq_true]; right; rw [decide_eq_true_eq]
      refine ⟨a, b, hab, ?_, ?_⟩
      · simp [Function.update_of_ne hav]
      · simp [Function.update_of_ne hbv]
    rw [h0, h1]; decide
  have simplifyFold_sound_gen : ∀ (gs : List Gate) (st0 : List Gate × List (Bool ⊕ ℕ)),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ t ∈ st0.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) →
      (∀ s ∈ st0.2, ∀ u, s = Sum.inr u → u < n + st0.1.length) →
      ∀ (x : Fin n → Bool) (ws : List Bool), ws.length = st0.2.length →
      (∀ w < st0.2.length, ws.getD w false = evalSym (Circuit.wires ⟨st0.1, 0⟩ (List.ofFn x)) (st0.2.getD w (Sum.inl false))) →
      let st1 := gs.foldl simplifyGate st0
      (∀ t ∈ st1.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
      (∀ s ∈ st1.2, ∀ u, s = Sum.inr u → u < n + st1.1.length) ∧
      ∀ w < st0.2.length + gs.length,
        (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) ws).getD w false =
          evalSym (Circuit.wires ⟨st1.1, 0⟩ (List.ofFn x)) (st1.2.getD w (Sum.inl false)) := by
    intro gs
    induction gs with
    | nil =>
      intro st0 _ hfan0 hbound0 x ws _ heq0
      exact ⟨hfan0, hbound0, fun w hw => heq0 w (by simpa using hw)⟩
    | cons g r ih =>
      intro st0 hfanG hfan0 hbound0 x ws hwsLen heq0
      have hstep := simplifyGate_sound st0 g (hfanG g (by simp)) hfan0 hbound0 x ws hwsLen heq0
      have hlen1 : (ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]).length = (simplifyGate st0 g).2.length := by
        rw [List.length_append, List.length_singleton, hwsLen, simplifyGate_env_len]
      have hrec := ih (simplifyGate st0 g) (fun t ht => hfanG t (by simp [ht])) hstep.1 hstep.2.1 x
        (ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) hlen1
        (fun w hw => hstep.2.2 w (by rw [simplifyGate_env_len] at hw; exact hw))
      refine ⟨hrec.1, hrec.2.1, fun w hw => ?_⟩
      simp only [List.foldl_cons]
      exact hrec.2.2 w (by rw [simplifyGate_env_len]; simp at hw; omega)
  have minimal_no_const_true : ∀ (i : ℕ) (hi : i < C.gates.length),
      ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i) false = false := by
    intro i hi
    by_contra! htrue
    have htrue' : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i) false = true :=
      fun x => by cases h : (C.wires (List.ofFn x)).getD (n + i) false with | false => exact False.elim (htrue x h) | true => rfl
    let st0 : List Gate × List (Bool ⊕ ℕ) :=
      (C.gates.take i, (List.range (n + i)).map Sum.inr ++ [Sum.inl true])
    have hst0_fan : ∀ t ∈ st0.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2 :=
      fun t ht => hmin.1 t (List.mem_of_mem_take ht)
    have hst0_len1 : st0.1.length = i := by simp [st0, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hst0_len2 : st0.2.length = n + i + 1 := by simp [st0]
    have hst0_bound : ∀ s ∈ st0.2, ∀ u, s = Sum.inr u → u < n + st0.1.length := by
      intro s hs u hu
      dsimp only [st0] at hs
      rcases List.mem_append.mp hs with h1 | h2
      · obtain ⟨k, hk, hkeq⟩ := List.mem_map.mp h1
        rw [List.mem_range] at hk
        rw [← hkeq] at hu; cases hu; omega
      · rw [List.mem_singleton.mp h2] at hu; cases hu
    have hst0_eq : ∀ x : Fin n → Bool, ∀ w < st0.2.length,
        ((C.gates.take (i + 1)).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).getD w false =
          evalSym (Circuit.wires ⟨st0.1, 0⟩ (List.ofFn x)) (st0.2.getD w (Sum.inl false)) := by
      intro x w hw
      have hlenPre : ((C.gates.take i).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).length = n + i := by
        rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
      have hsplitC : C.gates = C.gates.take (i + 1) ++ C.gates.drop (i + 1) := (List.take_append_drop (i + 1) C.gates).symm
      have hlenTake1 : ((C.gates.take (i + 1)).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).length = n + i + 1 := by
        rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega : i + 1 ≤ C.gates.length)]; omega
      by_cases hlt : w < n + i
      · have hL : ((C.gates.take (i + 1)).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).getD w false =
            ((C.gates.take i).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).getD w false := by
          rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
          exact circuitWires_prefix [C.gates[i]] _ w (by rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]; omega)
        have hR : st0.2.getD w (Sum.inl false) = Sum.inr w := by
          dsimp only [st0]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map,
            List.getElem?_range hlt]; rfl
        rw [hL, hR]; rfl
      · have hweq : w = n + i := by omega
        subst hweq
        have hL : ((C.gates.take (i + 1)).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).getD (n + i) false =
            (C.wires (List.ofFn x)).getD (n + i) false := by
          unfold Circuit.wires
          conv_rhs => rw [hsplitC, List.foldl_append]
          exact (circuitWires_prefix (C.gates.drop (i + 1)) _ (n + i) (by omega)).symm
        have hR : st0.2.getD (n + i) (Sum.inl false) = Sum.inl true := by
          dsimp only [st0]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp
        rw [hL, hR, htrue' x]
    have hfoldLen : ∀ (gs : List Gate) (s : List Gate × List (Bool ⊕ ℕ)),
        (gs.foldl simplifyGate s).1.length ≤ s.1.length + gs.length := by
      intro gs; induction gs with
      | nil => intro s; simp
      | cons g r ih => intro s; simp only [List.foldl_cons]; have := ih (simplifyGate s g); have := simplifyGate_gs_le s g; simp; omega
    let stEnd := (C.gates.drop (i + 1)).foldl simplifyGate st0
    have hEndLen : stEnd.1.length ≤ C.gates.length - 1 := by
      have := hfoldLen (C.gates.drop (i + 1)) st0
      rw [hst0_len1, List.length_drop] at this
      dsimp only [stEnd]; omega
    have hEndSound := simplifyFold_sound_gen (C.gates.drop (i + 1)) st0
      (fun g hg => hmin.1 g (List.mem_of_mem_drop hg)) hst0_fan hst0_bound
    have hEndFan : FanInTwo ⟨stEnd.1, 0⟩ := by
      intro g hg
      exact (hEndSound (fun _ => false)
        ((C.gates.take (i + 1)).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn (fun _ => false)))
        (by rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega : i + 1 ≤ C.gates.length), hst0_len2]; omega)
        (hst0_eq (fun _ => false))).1 g hg
    have hEndEq : ∀ x : Fin n → Bool, ∀ w < n + C.gates.length,
        (C.wires (List.ofFn x)).getD w false =
          evalSym (Circuit.wires ⟨stEnd.1, 0⟩ (List.ofFn x)) (stEnd.2.getD w (Sum.inl false)) := by
      intro x w hw
      have hwsLen : ((C.gates.take (i + 1)).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).length = st0.2.length := by
        rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega : i + 1 ≤ C.gates.length), hst0_len2]; omega
      have h := (hEndSound x _ hwsLen (hst0_eq x)).2.2 w (by rw [hst0_len2, List.length_drop]; omega)
      have hsplitC : C.gates = C.gates.take (i + 1) ++ C.gates.drop (i + 1) := (List.take_append_drop (i + 1) C.gates).symm
      unfold Circuit.wires
      conv_lhs => rw [hsplitC, List.foldl_append]
      exact h
    have houtLt : C.output < n + C.gates.length := by
      by_contra hge
      obtain ⟨x1, x2, hne⟩ := hnonconst
      apply hne
      unfold circuitFun Circuit.eval Circuit.wires
      have hlen1 : (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn (Function.update x1 v false))).length = n + C.gates.length := by
        rw [circuitWires_len, List.length_ofFn]
      have hlen2 : (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn (Function.update x2 v false))).length = n + C.gates.length := by
        rw [circuitWires_len, List.length_ofFn]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [hlen1]; omega),
        List.getElem?_eq_none (by rw [hlen2]; omega)]
    cases houtSym : stEnd.2.getD C.output (Sum.inl false) with
    | inl b =>
      obtain ⟨x1, x2, hne⟩ := hnonconst
      apply hne
      unfold circuitFun Circuit.eval
      rw [hEndEq _ C.output houtLt, hEndEq _ C.output houtLt, houtSym]
    | inr out' =>
      have hle := hmin.2 ⟨stEnd.1, out'⟩ hEndFan (by
        funext x; unfold circuitFun Circuit.eval
        rw [hEndEq x C.output houtLt, houtSym]; rfl)
      unfold Circuit.size at hle; dsimp only at hle; omega
  have simplifyGate_const_of_or_true : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      g.op = .or → ∀ u ∈ effInputs g, st.2.getD u (Sum.inl false) = Sum.inl true →
      (simplifyGate st g).2.getD st.2.length (Sum.inl false) = Sum.inl true := by
    intro st g hfg hop u hu hconst
    have hlast : ∀ a : Bool ⊕ ℕ, (st.2 ++ [a]).getD st.2.length (Sum.inl false) = a := by
      intro a; simp [List.getD_eq_getElem?_getD]
    dsimp only [simplifyGate, simplifyOne]
    rw [effInputs_or g hop hfg.2] at hu
    cases hgin : g.inputs with
    | nil => simp [hgin] at hu
    | cons u1 tl =>
      cases tl with
      | nil =>
        rw [hgin] at hu; simp at hu; subst hu
        rw [hop]; dsimp only []; rw [hlast, hconst]
      | cons u2 tl2 =>
        cases tl2 with
        | nil =>
          rw [hgin] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · rw [hop]; dsimp only []; rw [hconst, hlast]
          · rw [hop]; dsimp only []; rw [hconst]
            cases st.2.getD u1 (Sum.inl false) with
            | inl b1 => cases b1 <;> exact hlast _
            | inr _ => exact hlast _
        | cons _ _ => rw [hgin] at hfg; simp at hfg
  let st := C.gates.foldl simplifyGate ([], initEnv)
  have hstSound := simplifyFold_sound C.gates hmin.1
  have hfanSt : FanInTwo ⟨st.1, 0⟩ := hstSound.1
  have heqSt : ∀ (x : Fin n → Bool) (w : ℕ), w < n + C.gates.length →
      (C.wires (List.ofFn (Function.update x v false))).getD w false =
        evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD w (Sum.inl false)) := hstSound.2.2
  have hstAt : ∀ (k : ℕ) (hk : k ≤ C.gates.length) (w : ℕ), w < n + k →
      ((C.gates.take k).foldl simplifyGate ([], initEnv)).2.getD w (Sum.inl false) =
        st.2.getD w (Sum.inl false) := by
    intro k hk w hw
    have hsplit : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    have htkLen : ((C.gates.take k).foldl simplifyGate ([], initEnv)).2.length = n + k := by
      rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left hk]; simp [initEnv]
    dsimp only [st]
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (simplifyFold_env_prefix (C.gates.drop k) _ w (by omega)).symm
  have hvConst : st.2.getD v.val (Sum.inl false) = Sum.inl false := by
    have h0 := hstAt 0 (Nat.zero_le _) v.val (by omega)
    rw [← h0]
    simp [initEnv, List.getD_eq_getElem?_getD, List.getElem?_range v.isLt]
  have hconst_ne_out : ∀ (k : ℕ) (hk : k < C.gates.length) (b : Bool),
      st.2.getD (n + k) (Sum.inl false) = Sum.inl b → n + k ≠ C.output := by
    intro k hk b hkb heqOut
    obtain ⟨x1, x2, hne⟩ := hnonconst
    apply hne
    unfold circuitFun Circuit.eval
    rw [← heqOut, heqSt x1 (n + k) (by omega), heqSt x2 (n + k) (by omega), hkb]
  have houtLt : C.output < n + C.gates.length := by
    by_contra hge
    obtain ⟨x1, x2, hne⟩ := hnonconst
    apply hne
    unfold circuitFun Circuit.eval Circuit.wires
    have hlen1 : (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn (Function.update x1 v false))).length = n + C.gates.length := by
      rw [circuitWires_len, List.length_ofFn]
    have hlen2 : (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn (Function.update x2 v false))).length = n + C.gates.length := by
      rw [circuitWires_len, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [hlen1]; omega),
      List.getElem?_eq_none (by rw [hlen2]; omega)]
  have finish4 : st.1.length + 4 ≤ C.gates.length →
      ∃ v0 ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v0 false)) s := by
    intro h4
    cases houtSym : st.2.getD C.output (Sum.inl false) with
    | inl b =>
      exfalso
      obtain ⟨x1, x2, hne⟩ := hnonconst
      apply hne
      unfold circuitFun Circuit.eval
      rw [heqSt x1 C.output houtLt, heqSt x2 C.output houtLt, houtSym]
    | inr out' =>
      refine ⟨v, hvA, st.1.length, h4, ⟨st.1, out'⟩, hfanSt, le_rfl, fun x => ?_⟩
      rw [← hfun]; symm
      change (C.wires (List.ofFn (Function.update x v false))).getD C.output false =
        (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).getD out' false
      rw [heqSt x C.output houtLt, houtSym]
  have hexTwo : ∃ i1 i2, ∃ (h1 : i1 < C.gates.length) (h2 : i2 < C.gates.length),
      i1 ≠ i2 ∧ C.gates[i1].op = .not ∧ v.val ∈ effInputs C.gates[i1] ∧ v.val ∈ effInputs C.gates[i2] := by
    let Pv : Gate → Bool := fun g => (effInputs g).contains v.val
    have hPvLen : (C.gates.filter Pv).length = 2 := hvLen2
    have hmemNot : gnot ∈ C.gates.filter Pv := hgnotMem
    have hrec : ∀ (l : List Gate), (l.filter Pv).length = 2 → (∃ g ∈ l.filter Pv, g.op = .not) →
        ∃ a b, ∃ (ha : a < l.length) (hb : b < l.length), a ≠ b ∧ l[a].op = .not ∧ Pv l[a] = true ∧ Pv l[b] = true := by
      intro l; induction l with
      | nil => intro h; simp at h
      | cons g r ih =>
        intro hlen hnot
        rw [List.filter_cons] at hlen hnot
        cases hpg : Pv g
        · simp only [hpg, Bool.false_eq_true, ↓reduceIte] at hlen hnot
          obtain ⟨a, b, ha, hb, hab, hop, hpa, hpb⟩ := ih hlen hnot
          exact ⟨a + 1, b + 1, by simp; omega, by simp; omega, by omega, hop, hpa, hpb⟩
        · simp only [hpg, ↓reduceIte, List.length_cons] at hlen
          have hr1 : (r.filter Pv).length = 1 := by omega
          have hmemR : ∃ x ∈ r.filter Pv, True := by
            cases hrf : r.filter Pv with
            | nil => rw [hrf] at hr1; simp at hr1
            | cons x _ => exact ⟨x, by simp, trivial⟩
          obtain ⟨x, hx, _⟩ := hmemR
          obtain ⟨hxR, hpx⟩ := List.mem_filter.mp hx
          obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hxR
          simp only [hpg, ↓reduceIte, List.mem_cons] at hnot
          obtain ⟨gn, hgn | hgn, hgnOp⟩ := hnot
          · subst hgn
            exact ⟨0, idx + 1, by simp, by simp; omega, by omega, hgnOp, hpg, by simpa [hget] using hpx⟩
          · obtain ⟨hgnR, hpgn⟩ := List.mem_filter.mp hgn
            obtain ⟨idx2, hidx2, hget2⟩ := List.getElem_of_mem hgnR
            exact ⟨idx2 + 1, 0, by simp; omega, by simp, by omega, by simpa [hget2] using hgnOp,
              by simpa [hget2] using hpgn, hpg⟩
    obtain ⟨a, b, ha, hb, hab, hop, hpa, hpb⟩ := hrec C.gates hPvLen ⟨gnot, hmemNot, hgnotOp⟩
    exact ⟨a, b, ha, hb, hab, hop, List.contains_iff_mem.mp hpa, List.contains_iff_mem.mp hpb⟩
  obtain ⟨i1, i2, hi1, hi2, hi12, hop1, hmem1, hmem2⟩ := hexTwo
  have hnot1_val : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i1) false = !x v := by
    intro x
    change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i1) false = !x v
    rw [circuitWires_gate C.gates x i1 hi1, hop1]
    rw [effInputs_not C.gates[i1] hop1] at hmem1
    cases hgin1 : C.gates[i1].inputs with
    | nil => rw [hgin1] at hmem1; simp at hmem1
    | cons u tl =>
      rw [hgin1] at hmem1
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem1
      subst hmem1
      simp only [GateOp.eval, List.map_cons, List.headD_cons, if_pos (by omega : v.val < n + i1)]
      unfold Circuit.wires
      rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
  have hi1_elim : (simplifyGate ((C.gates.take i1).foldl simplifyGate ([], initEnv)) C.gates[i1]).1.length =
      ((C.gates.take i1).foldl simplifyGate ([], initEnv)).1.length :=
    simplifyGate_elim_of_const_input _ C.gates[i1] (hmin.1 _ (List.getElem_mem hi1)) v.val hmem1 false
      (by rw [hstAt i1 (Nat.le_of_lt hi1) v.val (by omega), hvConst])
  have hi2_elim : (simplifyGate ((C.gates.take i2).foldl simplifyGate ([], initEnv)) C.gates[i2]).1.length =
      ((C.gates.take i2).foldl simplifyGate ([], initEnv)).1.length :=
    simplifyGate_elim_of_const_input _ C.gates[i2] (hmin.1 _ (List.getElem_mem hi2)) v.val hmem2 false
      (by rw [hstAt i2 (Nat.le_of_lt hi2) v.val (by omega), hvConst])
  have hi1_true : st.2.getD (n + i1) (Sum.inl false) = Sum.inl true := by
    have hstepEq : (C.gates.take (i1 + 1)).foldl simplifyGate ([], initEnv) =
        simplifyGate ((C.gates.take i1).foldl simplifyGate ([], initEnv)) C.gates[i1] := by
      rw [List.take_succ_eq_append_getElem hi1, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have htkLen : ((C.gates.take i1).foldl simplifyGate ([], initEnv)).2.length = n + i1 := by
      rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi1)]; simp [initEnv]
    rw [← hstAt (i1 + 1) (by omega) (n + i1) (by omega), hstepEq]
    have hlast : ∀ a : Bool ⊕ ℕ, (((C.gates.take i1).foldl simplifyGate ([], initEnv)).2 ++ [a]).getD (n + i1) (Sum.inl false) = a := by
      intro a; rw [← htkLen]; simp [List.getD_eq_getElem?_getD]
    dsimp only [simplifyGate, simplifyOne]
    have hm1 := hmem1; rw [effInputs_not C.gates[i1] hop1] at hm1
    cases hgin1 : C.gates[i1].inputs with
    | nil => rw [hgin1] at hm1; simp at hm1
    | cons u tl =>
      rw [hgin1] at hm1
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hm1
      subst hm1
      rw [hop1]; dsimp only []
      rw [hstAt i1 (Nat.le_of_lt hi1) v.val (by omega), hvConst]
      exact hlast _
  have hreader_ne_i2 : ∀ j (hj : j < C.gates.length), i1 < j → n + i1 ∈ effInputs C.gates[j] → j ≠ i2 := by
    intro j hj hlt hread heq; subst j
    have hf2 := hmin.1 C.gates[i2] (List.getElem_mem hi2)
    rcases hf2.1 with hop2 | hop2 | hop2
    · rw [effInputs_and C.gates[i2] hop2 hf2.2] at hmem2 hread
      have hpair : C.gates[i2].inputs = [v.val, n + i1] ∨ C.gates[i2].inputs = [n + i1, v.val] := by
        cases hgin2 : C.gates[i2].inputs with
        | nil => rw [hgin2] at hmem2; simp at hmem2
        | cons a tl =>
          cases tl with
          | nil => rw [hgin2] at hmem2 hread; simp at hmem2 hread; omega
          | cons b tl2 =>
            cases tl2 with
            | nil =>
              rw [hgin2] at hmem2 hread; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread
              rcases hmem2 with rfl | rfl <;> rcases hread with h | h <;> first | omega | (left; simp [h]; done) | (right; simp [h]; done)
            | cons _ _ => rw [hgin2] at hf2; simp at hf2
      obtain ⟨x, hx⟩ := minimal_no_const_false i2 hi2
      have hf : (C.wires (List.ofFn x)).getD (n + i2) false = false := by
        change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i2) false = false
        rw [circuitWires_gate C.gates x i2 hi2, hop2]
        have hvW : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
          unfold Circuit.wires; rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
          simp [List.getD_eq_getElem?_getD, v.isLt]
        rcases hpair with h | h <;> rw [h] <;>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            show v.val < n + i2 by omega, show n + i1 < n + i2 by omega, ↓reduceIte, hvW]
        · change (x v && (C.wires (List.ofFn x)).getD (n + i1) false) = false; rw [hnot1_val x]; cases x v <;> rfl
        · change ((C.wires (List.ofFn x)).getD (n + i1) false && x v) = false; rw [hnot1_val x]; cases x v <;> rfl
      rw [hf] at hx; cases hx
    · rw [effInputs_or C.gates[i2] hop2 hf2.2] at hmem2 hread
      have hpair : C.gates[i2].inputs = [v.val, n + i1] ∨ C.gates[i2].inputs = [n + i1, v.val] := by
        cases hgin2 : C.gates[i2].inputs with
        | nil => rw [hgin2] at hmem2; simp at hmem2
        | cons a tl =>
          cases tl with
          | nil => rw [hgin2] at hmem2 hread; simp at hmem2 hread; omega
          | cons b tl2 =>
            cases tl2 with
            | nil =>
              rw [hgin2] at hmem2 hread; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread
              rcases hmem2 with rfl | rfl <;> rcases hread with h | h <;> first | omega | (left; simp [h]; done) | (right; simp [h]; done)
            | cons _ _ => rw [hgin2] at hf2; simp at hf2
      obtain ⟨x, hx⟩ := minimal_no_const_true i2 hi2
      have ht : (C.wires (List.ofFn x)).getD (n + i2) false = true := by
        change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i2) false = true
        rw [circuitWires_gate C.gates x i2 hi2, hop2]
        have hvW : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
          unfold Circuit.wires; rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
        rcases hpair with h | h <;> rw [h] <;>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            show v.val < n + i2 by omega, show n + i1 < n + i2 by omega, ↓reduceIte, hvW]
        · change (x v || (C.wires (List.ofFn x)).getD (n + i1) false) = true; rw [hnot1_val x]; cases x v <;> rfl
        · change ((C.wires (List.ofFn x)).getD (n + i1) false || x v) = true; rw [hnot1_val x]; cases x v <;> rfl
      rw [ht] at hx; cases hx
    · rw [Set.mem_singleton_iff] at hop2
      rw [effInputs_not C.gates[i2] hop2] at hmem2 hread
      cases hgin2 : C.gates[i2].inputs with
      | nil => rw [hgin2] at hmem2; simp at hmem2
      | cons u tl =>
        rw [hgin2] at hmem2 hread
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread
        omega
  obtain ⟨j1, hj1, hlt_i1_j1, hread1⟩ := minimal_gate_has_reader i1 hi1 (hconst_ne_out i1 hi1 true hi1_true)
  have hj1_ne_i2 : j1 ≠ i2 := hreader_ne_i2 j1 hj1 hlt_i1_j1 hread1
  have hj1_elim : (simplifyGate ((C.gates.take j1).foldl simplifyGate ([], initEnv)) C.gates[j1]).1.length =
      ((C.gates.take j1).foldl simplifyGate ([], initEnv)).1.length :=
    simplifyGate_elim_of_const_input _ C.gates[j1] (hmin.1 _ (List.getElem_mem hj1)) (n + i1) hread1 true
      (by rw [hstAt j1 (Nat.le_of_lt hj1) (n + i1) (by omega), hi1_true])
  by_cases hsecond : ∃ j2, ∃ (hj2 : j2 < C.gates.length), i1 < j2 ∧ j2 ≠ j1 ∧ n + i1 ∈ effInputs C.gates[j2]
  · obtain ⟨j2, hj2, hlt_i1_j2, hj2_ne_j1, hread2⟩ := hsecond
    have hj2_ne_i2 : j2 ≠ i2 := hreader_ne_i2 j2 hj2 hlt_i1_j2 hread2
    have hj2_elim : (simplifyGate ((C.gates.take j2).foldl simplifyGate ([], initEnv)) C.gates[j2]).1.length =
        ((C.gates.take j2).foldl simplifyGate ([], initEnv)).1.length :=
      simplifyGate_elim_of_const_input _ C.gates[j2] (hmin.1 _ (List.getElem_mem hj2)) (n + i1) hread2 true
        (by rw [hstAt j2 (Nat.le_of_lt hj2) (n + i1) (by omega), hi1_true])
    let S : Finset ℕ := {i1, i2, j1, j2}
    have hScard : S.card = 4 := by
      dsimp only [S]
      rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_singleton]
    have h4 := simplifyFold_size_bound C.gates S (fun k hk => by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact ⟨hi1, hi1_elim⟩
      · exact ⟨hi2, hi2_elim⟩
      · exact ⟨hj1, hj1_elim⟩
      · exact ⟨hj2, hj2_elim⟩)
    rw [hScard] at h4
    exact finish4 h4
  · push Not at hsecond
    have hj1_unique : ∀ (j : ℕ) (hj : j < C.gates.length), i1 < j → n + i1 ∈ effInputs C.gates[j] → j = j1 := by
      intro j hj hlt hmem
      by_contra hne
      exact hsecond j hj hlt hne hmem
    have hfj1 := hmin.1 C.gates[j1] (List.getElem_mem hj1)
    rcases hfj1.1 with hopj1 | hopj1 | hopj1
    · -- j1.op = .and
      have hfi2 := hmin.1 C.gates[i2] (List.getElem_mem hi2)
      rcases hfi2.1 with hopi2 | hopi2 | hopi2
      · -- i2.op = .and -> i2 becomes false -> has reader k != j1 -> 4 gates
        have hi2_false : ∃ c2 : Bool, st.2.getD (n + i2) (Sum.inl false) = Sum.inl c2 := by
          obtain ⟨c2, hc2⟩ := simplifyGate_const_of_nonOr_false ((C.gates.take i2).foldl simplifyGate ([], initEnv))
            C.gates[i2] hfi2 (by rw [hopi2]; intro h; cases h) v.val hmem2
            (by rw [hstAt i2 (Nat.le_of_lt hi2) v.val (by omega), hvConst])
          have htkLen : ((C.gates.take i2).foldl simplifyGate ([], initEnv)).2.length = n + i2 := by
            rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi2)]; simp [initEnv]
          rw [htkLen] at hc2
          have hstepEq : (C.gates.take (i2 + 1)).foldl simplifyGate ([], initEnv) =
              simplifyGate ((C.gates.take i2).foldl simplifyGate ([], initEnv)) C.gates[i2] := by
            rw [List.take_succ_eq_append_getElem hi2, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [← hstepEq, hstAt (i2 + 1) (by omega) (n + i2) (by omega)] at hc2
          exact ⟨c2, hc2⟩
        obtain ⟨c2, hc2⟩ := hi2_false
        obtain ⟨k, hk, hlt_i2_k, hreadk⟩ := minimal_gate_has_reader i2 hi2 (hconst_ne_out i2 hi2 c2 hc2)
        have hk_ne_j1 : k ≠ j1 := by
          intro heq; subst k
          rw [effInputs_and C.gates[j1] hopj1 hfj1.2] at hread1 hreadk
          have hpair : C.gates[j1].inputs = [n + i1, n + i2] ∨ C.gates[j1].inputs = [n + i2, n + i1] := by
            cases hgin : C.gates[j1].inputs with
            | nil => rw [hgin] at hread1; simp at hread1
            | cons a tl =>
              cases tl with
              | nil => rw [hgin] at hread1 hreadk; simp at hread1 hreadk; omega
              | cons b tl2 =>
                cases tl2 with
                | nil =>
                  rw [hgin] at hread1 hreadk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hread1 hreadk
                  rcases hread1 with rfl | rfl <;> rcases hreadk with h | h <;> first | omega | (left; simp [h]; done) | (right; simp [h]; done)
                | cons _ _ => rw [hgin] at hfj1; simp at hfj1
          obtain ⟨x, hx⟩ := minimal_no_const_false j1 hj1
          have hf : (C.wires (List.ofFn x)).getD (n + j1) false = false := by
            change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false = false
            rw [circuitWires_gate C.gates x j1 hj1, hopj1]
            have hi2f : x v = false → (C.wires (List.ofFn x)).getD (n + i2) false = false := by
              intro hxvf
              change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i2) false = false
              rw [circuitWires_gate C.gates x i2 hi2, hopi2]
              rw [effInputs_and C.gates[i2] hopi2 hfi2.2] at hmem2
              simp only [GateOp.eval, List.all_eq_false]
              refine ⟨false, ?_, by decide⟩
              rw [List.mem_map]; refine ⟨v.val, hmem2, ?_⟩
              rw [if_pos (by omega : v.val < n + i2)]
              unfold Circuit.wires; rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
              simp [List.getD_eq_getElem?_getD, v.isLt, hxvf]
            rcases hpair with h | h <;> rw [h] <;>
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true,
                show n + i1 < n + j1 by omega, show n + i2 < n + j1 by omega, ↓reduceIte]
            · change ((C.wires (List.ofFn x)).getD (n + i1) false && (C.wires (List.ofFn x)).getD (n + i2) false) = false
              rw [hnot1_val x]; cases hxv : x v
              · rw [hi2f hxv]; rfl
              · rfl
            · change ((C.wires (List.ofFn x)).getD (n + i2) false && (C.wires (List.ofFn x)).getD (n + i1) false) = false
              rw [hnot1_val x]; cases hxv : x v
              · rw [hi2f hxv]; rfl
              · simp
          rw [hf] at hx; cases hx
        have hk_ne_i1 : k ≠ i1 := by
          intro heq; subst k
          rw [effInputs_not C.gates[i1] hop1] at hmem1 hreadk
          cases h : C.gates[i1].inputs with
          | nil => rw [h] at hmem1; simp at hmem1
          | cons u tl =>
            rw [h] at hmem1 hreadk
            simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem1 hreadk
            omega
        have hk_elim : (simplifyGate ((C.gates.take k).foldl simplifyGate ([], initEnv)) C.gates[k]).1.length =
            ((C.gates.take k).foldl simplifyGate ([], initEnv)).1.length :=
          simplifyGate_elim_of_const_input _ C.gates[k] (hmin.1 _ (List.getElem_mem hk)) (n + i2) hreadk c2
            (by rw [hstAt k (Nat.le_of_lt hk) (n + i2) (by omega), hc2])
        let S : Finset ℕ := {i1, i2, j1, k}
        have hScard : S.card = 4 := by
          dsimp only [S]
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_singleton]
        have h4 := simplifyFold_size_bound C.gates S (fun m hm => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl
          · exact ⟨hi1, hi1_elim⟩
          · exact ⟨hi2, hi2_elim⟩
          · exact ⟨hj1, hj1_elim⟩
          · exact ⟨hk, hk_elim⟩)
        rw [hScard] at h4
        exact finish4 h4
      · -- i2.op = .or and j1.op = .and (Subcase B3c): split hasAndReader vs noAndReader
        have hsub3c : ∃ v0 ∉ A, (readers v0).length = 2 ∧
            ∃ a1 a2 b1, ∃ (ha1 : a1 < C.gates.length) (ha2 : a2 < C.gates.length) (hb1 : b1 < C.gates.length),
              a1 < b1 ∧ a1 ≠ a2 ∧ a2 ≠ b1 ∧
              C.gates[a1].op = .not ∧ C.gates[a2].op = .or ∧ C.gates[b1].op = .and ∧
              (C.gates[a1].inputs.take 1).contains v0.val ∧ (C.gates[a2].inputs.take 2).contains v0.val ∧
              (C.gates[b1].inputs.take 2).contains (n + a1) ∧
              (∀ (j : ℕ) (hj : j < C.gates.length),
                (C.gates[j].inputs.take (bif C.gates[j].op.eval [false] then 1 else 2)).contains (n + a1) → j = b1) := by
          refine ⟨v, hvA, hvLen2, i1, i2, j1, hi1, hi2, hj1, hlt_i1_j1, hi12, hj1_ne_i2.symm, hop1, hopi2, hopj1, ?_, ?_, ?_, ?_⟩
          · rw [List.contains_iff_mem]; rwa [effInputs_not C.gates[i1] hop1] at hmem1
          · rw [List.contains_iff_mem]; rwa [effInputs_or C.gates[i2] hopi2 hfi2.2, ← List.take_of_length_le hfi2.2] at hmem2
          · rw [List.contains_iff_mem]; rwa [effInputs_and C.gates[j1] hopj1 hfj1.2, ← List.take_of_length_le hfj1.2] at hread1
          · intro j hj hcon
            have hmem := List.contains_iff_mem.mp hcon
            by_cases hlt : i1 < j
            · exact hj1_unique j hj hlt hmem
            · -- If j <= i1, wire n + i1 is out-of-bounds at step j, so C.gates[j] reading n + i1 always gets false -> wait!
              -- Can a gate j <= i1 have n + i1 in effInputs? If so, replacing n + i1 by out-of-bounds? Wait: n + i1 >= n + j!
              -- If C.gates[j] has an input u >= n + j, then u evaluates to false at step j -> C.gates[j] simplifies!
              exfalso
              have hge : n + j ≤ n + i1 := by omega
              -- Use simplifyFold starting from take j with C.gates[j] reading u >= n + j -> u maps to Sum.inl false?
              -- Better: prove directly that minimal circuit has no gate j with input >= n + j!
              let stJ0 : List Gate × List (Bool ⊕ ℕ) :=
                (C.gates.take j, (List.range (n + j)).map Sum.inr)
              have hstJ0_len1 : stJ0.1.length = j := by simp [stJ0, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
              have hstJ0_len2 : stJ0.2.length = n + j := by simp [stJ0]
              have hstJ0_fan : ∀ t ∈ stJ0.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2 :=
                fun t ht => hmin.1 t (List.mem_of_mem_take ht)
              have hstJ0_bound : ∀ s ∈ stJ0.2, ∀ u, s = Sum.inr u → u < n + stJ0.1.length := by
                intro s hs u hu; dsimp only [stJ0] at hs
                obtain ⟨k, hk, hkeq⟩ := List.mem_map.mp hs; rw [List.mem_range] at hk
                rw [← hkeq] at hu; cases hu; omega
              have hstJ0_eq : ∀ x : Fin n → Bool, ∀ w < stJ0.2.length,
                  ((C.gates.take j).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).getD w false =
                    evalSym (Circuit.wires ⟨stJ0.1, 0⟩ (List.ofFn x)) (stJ0.2.getD w (Sum.inl false)) := by
                intro x w hw
                rw [hstJ0_len2] at hw
                have hR : stJ0.2.getD w (Sum.inl false) = Sum.inr w := by
                  dsimp only [stJ0]; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]; rfl
                rw [hR]; rfl
              have hj_elim_oob : (simplifyGate stJ0 C.gates[j]).1.length = stJ0.1.length :=
                simplifyGate_elim_of_const_input stJ0 C.gates[j] (hmin.1 _ (List.getElem_mem hj)) (n + i1) hmem false
                  (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hstJ0_len2]; omega)]; rfl)
              have hfoldLen : ∀ (gs : List Gate) (s : List Gate × List (Bool ⊕ ℕ)),
                  (gs.foldl simplifyGate s).1.length ≤ s.1.length + gs.length := by
                intro gs; induction gs with
                | nil => intro s; simp
                | cons g r ih => intro s; simp only [List.foldl_cons]; have := ih (simplifyGate s g); have := simplifyGate_gs_le s g; simp; omega
              let stJEnd := (C.gates.drop j).foldl simplifyGate stJ0
              have hJEndLen : stJEnd.1.length ≤ C.gates.length - 1 := by
                have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
                have h1 : stJEnd = (C.gates.drop (j + 1)).foldl simplifyGate (simplifyGate stJ0 C.gates[j]) := by
                  dsimp only [stJEnd]; rw [hdrop, List.foldl_cons]
                rw [h1]
                have := hfoldLen (C.gates.drop (j + 1)) (simplifyGate stJ0 C.gates[j])
                rw [hj_elim_oob, hstJ0_len1, List.length_drop] at this; omega
              have hJEndSound := simplifyFold_sound_gen (C.gates.drop j) stJ0
                (fun g hg => hmin.1 g (List.mem_of_mem_drop hg)) hstJ0_fan hstJ0_bound
              have hJEndFan : FanInTwo ⟨stJEnd.1, 0⟩ := by
                intro g hg
                exact (hJEndSound (fun _ => false)
                  ((C.gates.take j).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn (fun _ => false)))
                  (by rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), hstJ0_len2])
                  (hstJ0_eq (fun _ => false))).1 g hg
              have hJEndEq : ∀ x : Fin n → Bool, ∀ w < n + C.gates.length,
                  (C.wires (List.ofFn x)).getD w false =
                    evalSym (Circuit.wires ⟨stJEnd.1, 0⟩ (List.ofFn x)) (stJEnd.2.getD w (Sum.inl false)) := by
                intro x w hw
                have hwsLen : ((C.gates.take j).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) (List.ofFn x)).length = stJ0.2.length := by
                  rw [circuitWires_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), hstJ0_len2]
                have h := (hJEndSound x _ hwsLen (hstJ0_eq x)).2.2 w (by rw [hstJ0_len2, List.length_drop]; omega)
                have hsplitC : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
                unfold Circuit.wires
                conv_lhs => rw [hsplitC, List.foldl_append]
                exact h
              cases houtSym : stJEnd.2.getD C.output (Sum.inl false) with
              | inl b =>
                obtain ⟨x1, x2, hne⟩ := hnonconst
                apply hne; unfold circuitFun Circuit.eval
                rw [hJEndEq _ C.output houtLt, hJEndEq _ C.output houtLt, houtSym]
              | inr out' =>
                have hle := hmin.2 ⟨stJEnd.1, out'⟩ hJEndFan (by
                  funext x; unfold circuitFun Circuit.eval
                  rw [hJEndEq x C.output houtLt, houtSym]; rfl)
                unfold Circuit.size at hle; dsimp only at hle; omega
        by_cases hAnd : ∃ v' ∉ A, ∃ g ∈ readers v', g.op = .and
        · exact hasAndReader n G A C hdeg hcycle hend hedge hfan hfun hminSz hread hsub3c hAnd
        · push Not at hAnd
          exact noAndReader n G A C hdeg hcycle hend hedge hfan hfun hminSz hread hsub3c hAnd
      · -- i2.op = .not -> duplicate of i1!
        rw [Set.mem_singleton_iff] at hopi2
        have hnot2_val : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + i2) false = !x v := by
          intro x
          change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i2) false = !x v
          rw [circuitWires_gate C.gates x i2 hi2, hopi2]
          rw [effInputs_not C.gates[i2] hopi2] at hmem2
          cases hgin2 : C.gates[i2].inputs with
          | nil => rw [hgin2] at hmem2; simp at hmem2
          | cons u tl =>
            rw [hgin2] at hmem2
            simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem2
            subst hmem2
            simp only [GateOp.eval, List.map_cons, List.headD_cons, if_pos (by omega : v.val < n + i2)]
            unfold Circuit.wires
            rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
            simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
        by_cases hlt12 : i1 < i2
        · obtain ⟨x, hx⟩ := minimal_no_dup_wire i2 hi2 (n + i1) (by omega)
          exact False.elim (hx (by rw [hnot2_val x, hnot1_val x]))
        · obtain ⟨x, hx⟩ := minimal_no_dup_wire i1 hi1 (n + i2) (by omega)
          exact False.elim (hx (by rw [hnot1_val x, hnot2_val x]))
    · -- j1.op = .or -> j1 becomes true -> has reader j2 > j1
      have hj1_true : st.2.getD (n + j1) (Sum.inl false) = Sum.inl true := by
        have h1 := simplifyGate_const_of_or_true ((C.gates.take j1).foldl simplifyGate ([], initEnv))
          C.gates[j1] hfj1 hopj1 (n + i1) hread1
          (by rw [hstAt j1 (Nat.le_of_lt hj1) (n + i1) (by omega), hi1_true])
        have htkLen : ((C.gates.take j1).foldl simplifyGate ([], initEnv)).2.length = n + j1 := by
          rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj1)]; simp [initEnv]
        rw [htkLen] at h1
        have hstepEq : (C.gates.take (j1 + 1)).foldl simplifyGate ([], initEnv) =
            simplifyGate ((C.gates.take j1).foldl simplifyGate ([], initEnv)) C.gates[j1] := by
          rw [List.take_succ_eq_append_getElem hj1, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [← hstepEq, hstAt (j1 + 1) (by omega) (n + j1) (by omega)] at h1
        exact h1
      by_cases hother : ∃ j2, ∃ (hj2 : j2 < C.gates.length), j1 < j2 ∧ j2 ≠ i2 ∧ n + j1 ∈ effInputs C.gates[j2]
      · obtain ⟨j2, hj2, hlt_j1_j2, hj2_ne_i2, hread2⟩ := hother
        have hj2_elim : (simplifyGate ((C.gates.take j2).foldl simplifyGate ([], initEnv)) C.gates[j2]).1.length =
            ((C.gates.take j2).foldl simplifyGate ([], initEnv)).1.length :=
          simplifyGate_elim_of_const_input _ C.gates[j2] (hmin.1 _ (List.getElem_mem hj2)) (n + j1) hread2 true
            (by rw [hstAt j2 (Nat.le_of_lt hj2) (n + j1) (by omega), hj1_true])
        let S : Finset ℕ := {i1, i2, j1, j2}
        have hScard : S.card = 4 := by
          dsimp only [S]
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_singleton]
        have h4 := simplifyFold_size_bound C.gates S (fun m hm => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl
          · exact ⟨hi1, hi1_elim⟩
          · exact ⟨hi2, hi2_elim⟩
          · exact ⟨hj1, hj1_elim⟩
          · exact ⟨hj2, hj2_elim⟩)
        rw [hScard] at h4
        exact finish4 h4
      · push Not at hother
        obtain ⟨j2, hj2, hlt_j1_j2, hread2⟩ := minimal_gate_has_reader j1 hj1 (hconst_ne_out j1 hj1 true hj1_true)
        have hj2_eq_i2 : j2 = i2 := by by_contra hne; exact hother j2 hj2 hlt_j1_j2 hne hread2
        subst j2
        -- Now j1 < i2, i2 is the ONLY reader of n + j1, and i2 reads both v.val and n + j1!
        have hfi2 := hmin.1 C.gates[i2] (List.getElem_mem hi2)
        -- Extract the other input w of j1 (which is .or reading n + i1)
        have hj1_other : ∃ w < n + j1, ∀ x : Fin n → Bool,
            (C.wires (List.ofFn x)).getD (n + j1) false = (!x v || (C.wires (List.ofFn x)).getD w false) := by
          rw [effInputs_or C.gates[j1] hopj1 hfj1.2] at hread1
          cases hgin1 : C.gates[j1].inputs with
          | nil => rw [hgin1] at hread1; simp at hread1
          | cons a tl =>
            cases tl with
            | nil =>
              exfalso
              rw [hgin1] at hread1; simp at hread1; subst hread1
              obtain ⟨x, hx⟩ := minimal_no_dup_wire j1 hj1 (n + i1) (by omega)
              apply hx
              change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false = _
              rw [circuitWires_gate C.gates x j1 hj1, hopj1, hgin1]
              simp [GateOp.eval, show n + i1 < n + j1 by omega]; rfl
            | cons b tl2 =>
              cases tl2 with
              | nil =>
                rw [hgin1] at hread1; simp only [List.mem_cons, List.not_mem_nil, or_false] at hread1
                rcases hread1 with rfl | rfl
                · by_cases hblt : b < n + j1
                  · refine ⟨b, hblt, fun x => ?_⟩
                    change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false = _
                    rw [circuitWires_gate C.gates x j1 hj1, hopj1, hgin1]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                      show n + i1 < n + j1 by omega, hblt, ↓reduceIte]
                    change ((C.wires (List.ofFn x)).getD (n + i1) false || (C.wires (List.ofFn x)).getD b false) = _
                    rw [hnot1_val x]
                  · exfalso
                    obtain ⟨x, hx⟩ := minimal_no_dup_wire j1 hj1 (n + i1) (by omega)
                    apply hx
                    change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false = _
                    rw [circuitWires_gate C.gates x j1 hj1, hopj1, hgin1]
                    simp [GateOp.eval, show n + i1 < n + j1 by omega, hblt]; rfl
                · by_cases halt : a < n + j1
                  · refine ⟨a, halt, fun x => ?_⟩
                    change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false = _
                    rw [circuitWires_gate C.gates x j1 hj1, hopj1, hgin1]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                      show n + i1 < n + j1 by omega, halt, ↓reduceIte]
                    change ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD (n + i1) false) = _
                    rw [hnot1_val x, Bool.or_comm]
                  · exfalso
                    obtain ⟨x, hx⟩ := minimal_no_dup_wire j1 hj1 (n + i1) (by omega)
                    apply hx
                    change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false = _
                    rw [circuitWires_gate C.gates x j1 hj1, hopj1, hgin1]
                    simp [GateOp.eval, show n + i1 < n + j1 by omega, halt]; rfl
              | cons _ _ => rw [hgin1] at hfj1; simp at hfj1
        obtain ⟨w, hwLt, hj1_val⟩ := hj1_other
        rcases hfi2.1 with hopi2 | hopi2 | hopi2
        · -- i2.op = .and: i2 computes x v && (!x v || w) = x v && w -> deleteRedirectCircuit j1 w!
          exfalso
          rw [effInputs_and C.gates[i2] hopi2 hfi2.2] at hmem2 hread2
          have hpair : C.gates[i2].inputs = [v.val, n + j1] ∨ C.gates[i2].inputs = [n + j1, v.val] := by
            cases hgin2 : C.gates[i2].inputs with
            | nil => rw [hgin2] at hmem2; simp at hmem2
            | cons a tl =>
              cases tl with
              | nil => rw [hgin2] at hmem2 hread2; simp at hmem2 hread2; omega
              | cons b tl2 =>
                cases tl2 with
                | nil =>
                  rw [hgin2] at hmem2 hread2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread2
                  rcases hmem2 with rfl | rfl <;> rcases hread2 with h | h <;> first | omega | (left; simp [h]; done) | (right; simp [h]; done)
                | cons _ _ => rw [hgin2] at hfi2; simp at hfi2
          let C' := deleteRedirectCircuit j1 w
          have hlenC' : C'.gates.length = C.gates.length - 1 := deleteRedirectCircuit_size j1 hj1 w
          have hevalC' : circuitFun n C' = circuitFun n C := by
            funext x
            have hwire : ∀ u < n + C'.gates.length,
                (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD u false =
                  if u < n + j1 then (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD u false
                  else (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (u + 1) false := by
              intro u
              induction u using Nat.strongRecOn with
              | ind u ih =>
                intro hu
                by_cases hltN : u < n
                · have hltJ : u < n + j1 := by omega
                  rw [if_pos hltJ]
                  unfold Circuit.wires
                  rw [circuitWires_prefix C'.gates (List.ofFn x) u (by simp; omega),
                      circuitWires_prefix C.gates (List.ofFn x) u (by simp; omega)]
                · let j := u - n
                  have hj : j < C'.gates.length := by omega
                  have huj : u = n + j := by omega
                  by_cases hltJ : j < j1
                  · rw [if_pos (by omega)]
                    have hget : C'.gates[j] = ⟨C.gates[j].op, C.gates[j].inputs.map (fun z => if z ≥ n + j1 then n + C.gates.length else z)⟩ := by
                      dsimp only [C', deleteRedirectCircuit]
                      have htl : ((C.gates.take j1).map fun g => Gate.mk g.op (g.inputs.map fun z => if z ≥ n + j1 then n + C.gates.length else z)).length = j1 := by
                        rw [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj1)]
                      rw [List.getElem_append_left (by omega), List.getElem_map, List.getElem_take]
                    rw [huj, circuitWires_gate C'.gates x j hj, circuitWires_gate C.gates x j (by omega), hget]
                    dsimp only []
                    rw [List.map_map]
                    congr 1; apply List.map_congr_left; intro z _; dsimp only [Function.comp]
                    by_cases hz : z < n + j
                    · have hnotge : ¬ z ≥ n + j1 := by omega
                      simp only [hnotge, hz, ↓reduceIte]
                      rw [ih z (by omega) (by omega), if_pos (by omega)]
                    · by_cases hge : z ≥ n + j1
                      · simp only [hge, hz, ↓reduceIte, show ¬ n + C.gates.length < n + j by omega]
                      · simp only [hge, hz, ↓reduceIte]
                  · rw [if_neg (by omega)]
                    have hj1' : j + 1 < C.gates.length := by omega
                    have hget : C'.gates[j] = redirGate (n + j1) w C.gates[j + 1] := by
                      dsimp only [C', deleteRedirectCircuit]
                      have htl : ((C.gates.take j1).map fun g => Gate.mk g.op (g.inputs.map fun z => if z ≥ n + j1 then n + C.gates.length else z)).length = j1 := by
                        rw [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj1)]
                      rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_drop]
                      congr 2; omega
                    rw [huj, show n + j + 1 = n + (j + 1) by omega,
                        circuitWires_gate C'.gates x j hj, circuitWires_gate C.gates x (j + 1) hj1', hget]
                    dsimp only [redirGate]
                    by_cases hji2 : j + 1 = i2
                    · -- At gate i2, x v && w = x v && (!x v || w)!
                      have hgi2 : C.gates[j + 1] = C.gates[i2] := by congr 1
                      rw [hgi2, hopi2]
                      have hvW : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
                        unfold Circuit.wires; rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
                        simp [List.getD_eq_getElem?_getD, v.isLt]
                      have hvRedir : redirWire (n + j1) w v.val = v.val := by
                        dsimp only [redirWire]; rw [if_neg (by omega), if_neg (by omega)]
                      have hj1Redir : redirWire (n + j1) w (n + j1) = w := by
                        dsimp only [redirWire]; rw [if_pos rfl]
                      have hvIH : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
                        rw [ih v.val (by omega) (by omega), if_pos (by omega), hvW]
                      have hwIH : (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD w false =
                          (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD w false := by
                        rw [ih w (by omega) (by omega), if_pos hwLt]
                      rcases hpair with h | h <;> rw [h] <;>
                        simp only [List.map_cons, List.map_nil, hvRedir, hj1Redir, GateOp.eval, List.all_cons, List.all_nil,
                          id_eq, Bool.and_true, show v.val < n + j by omega, show w < n + j by omega,
                          show v.val < n + (j + 1) by omega, show n + j1 < n + (j + 1) by omega, ↓reduceIte, hvIH, hwIH, hvW]
                      · change (x v && (C.wires (List.ofFn x)).getD w false) =
                          (x v && (C.wires (List.ofFn x)).getD (n + j1) false)
                        rw [hj1_val x]; cases x v <;> simp
                      · change ((C.wires (List.ofFn x)).getD w false && x v) =
                          ((C.wires (List.ofFn x)).getD (n + j1) false && x v)
                        rw [hj1_val x]; cases x v <;> simp
                    · -- At gate j + 1 ≠ i2, n + j1 ∉ effInputs C.gates[j + 1]!
                      have hnotMem : n + j1 ∉ effInputs C.gates[j + 1] := hother (j + 1) hj1' (by omega) hji2
                      have heff := gate_eval_eq_of_eff C.gates[j + 1] (hmin.1 _ (List.getElem_mem hj1'))
                        (fun z => if redirWire (n + j1) w z < n + j then
                          (Circuit.wires ⟨C'.gates, 0⟩ (List.ofFn x)).getD (redirWire (n + j1) w z) false else false)
                        (fun z => if z < n + (j + 1) then
                          (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD z false else false)
                      rw [List.map_map]
                      apply heff
                      intro z hz
                      have hzne : z ≠ n + j1 := fun h => hnotMem (h ▸ hz)
                      dsimp only [redirWire]
                      simp only [hzne, ↓reduceIte]
                      by_cases hgt : z > n + j1
                      · simp only [hgt, ↓reduceIte]
                        by_cases hzlt : z < n + (j + 1)
                        · rw [if_pos (by omega), if_pos hzlt, ih (z - 1) (by omega) (by omega), if_neg (by omega),
                            show z - 1 + 1 = z by omega]
                        · rw [if_neg (by omega), if_neg hzlt]
                      · simp only [hgt, ↓reduceIte]
                        have hzlt1 : z < n + j := by omega
                        have hzlt2 : z < n + (j + 1) := by omega
                        rw [if_pos hzlt1, if_pos hzlt2, ih z (by omega) (by omega), if_pos (by omega)]
            unfold circuitFun Circuit.eval
            dsimp only [C', deleteRedirectCircuit, redirWire]
            have hneOut : C.output ≠ n + j1 := (hconst_ne_out j1 hj1 true hj1_true).symm
            rw [if_neg hneOut]
            by_cases hgt : C.output > n + j1
            · rw [if_pos hgt]
              have h1 := hwire (C.output - 1) (by omega)
              rw [if_neg (by omega), show C.output - 1 + 1 = C.output by omega] at h1
              exact h1
            · rw [if_neg hgt]
              have h1 := hwire C.output (by omega)
              rw [if_pos (by omega)] at h1
              exact h1
          have hle := hmin.2 C' (deleteRedirectCircuit_fanInTwo j1 w) hevalC'
          unfold Circuit.size at hle; omega
        · -- i2.op = .or: i2 computes x v || (!x v || w) = true -> contradicts minimal_no_const_true!
          exfalso
          rw [effInputs_or C.gates[i2] hopi2 hfi2.2] at hmem2 hread2
          have hpair : C.gates[i2].inputs = [v.val, n + j1] ∨ C.gates[i2].inputs = [n + j1, v.val] := by
            cases hgin2 : C.gates[i2].inputs with
            | nil => rw [hgin2] at hmem2; simp at hmem2
            | cons a tl =>
              cases tl with
              | nil => rw [hgin2] at hmem2 hread2; simp at hmem2 hread2; omega
              | cons b tl2 =>
                cases tl2 with
                | nil =>
                  rw [hgin2] at hmem2 hread2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread2
                  rcases hmem2 with rfl | rfl <;> rcases hread2 with h | h <;> first | omega | (left; simp [h]; done) | (right; simp [h]; done)
                | cons _ _ => rw [hgin2] at hfi2; simp at hfi2
          obtain ⟨x, hx⟩ := minimal_no_const_true i2 hi2
          have ht : (C.wires (List.ofFn x)).getD (n + i2) false = true := by
            change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i2) false = true
            rw [circuitWires_gate C.gates x i2 hi2, hopi2]
            have hvW : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
              unfold Circuit.wires; rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
              simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
            rcases hpair with h | h <;> rw [h] <;>
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                show v.val < n + i2 by omega, show n + j1 < n + i2 by omega, ↓reduceIte, hvW]
            · change (x v || (C.wires (List.ofFn x)).getD (n + j1) false) = true
              rw [hj1_val x]; cases x v <;> simp
            · change ((C.wires (List.ofFn x)).getD (n + j1) false || x v) = true
              rw [hj1_val x]; cases x v <;> simp
          rw [ht] at hx; cases hx
        · -- i2.op = .not: effInputs has length 1, can't contain both v.val and n + j1
          rw [Set.mem_singleton_iff] at hopi2
          rw [effInputs_not C.gates[i2] hopi2] at hmem2 hread2
          cases hgin2 : C.gates[i2].inputs with
          | nil => rw [hgin2] at hmem2; simp at hmem2
          | cons u tl =>
            rw [hgin2] at hmem2 hread2
            simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread2
            omega
    · -- j1.op = .not -> j1 computes !(!x v) = x v -> contradicts minimal_no_dup_wire!
      rw [Set.mem_singleton_iff] at hopj1
      obtain ⟨x, hx⟩ := minimal_no_dup_wire j1 hj1 v.val (by omega)
      exfalso; apply hx
      change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + j1) false =
        (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false
      rw [circuitWires_gate C.gates x j1 hj1, hopj1]
      rw [effInputs_not C.gates[j1] hopj1] at hread1
      cases hgin1 : C.gates[j1].inputs with
      | nil => rw [hgin1] at hread1; simp at hread1
      | cons u tl =>
        rw [hgin1] at hread1
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hread1
        subst hread1
        simp only [GateOp.eval, List.map_cons, List.headD_cons, if_pos (by omega : n + i1 < n + j1)]
        have hvW : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
          unfold Circuit.wires; rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
        rw [hvW]
        change (!((C.wires (List.ofFn x)).getD (n + i1) false)) = x v
        rw [hnot1_val x, Bool.not_not]
