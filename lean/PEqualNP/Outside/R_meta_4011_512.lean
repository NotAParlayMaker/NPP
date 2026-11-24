import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_4011_512 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      IsMinimalCircuit n C →
      circuitFun n C = graphFun G A →
      (∀ v ∉ A, let rs := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val;
        rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = .or)) →
      (∀ v ∉ A, (C.gates.filter fun g => (match g.op with | .or => false | _ => true) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
      (∀ g ∈ C.gates, g.op ≠ .not) →
      (∀ T : Finset (Fin n), Disjoint A T → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < A.card + G.edgeFinset.card + T.card) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      IsMinimalCircuit n C →
      circuitFun n C = graphFun G A →
      (∀ v ∉ A, let rs := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val;
        rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = .or)) →
      (∀ v ∉ A, (C.gates.filter fun g => (match g.op with | .or => false | _ => true) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
      (∃ g ∈ C.gates, g.op = .not) →
      (∀ T : Finset (Fin n), Disjoint A T → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < A.card + G.edgeFinset.card + T.card) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →             PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →               (∀ x12 ∉ x4,                   have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;                   x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                 (∀ (x13 : Finset (Fin x1)), Disjoint x4 x13 → (∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → x15 ∈ x13 ∨ x16 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + x13.card) → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15 := by
  intro hMono hHasNot n G _ A C hdeg hcycle hend hedge hmin hfun hread hsmall
  let effInputs : Gate → List ℕ := fun g =>
    g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have effInputs_not : ∀ g : Gate, g.op = .not → effInputs g = g.inputs.take 1 := by
    intro g h; simp [effInputs, h, GateOp.eval]
  have effInputs_and : ∀ g : Gate, g.op = .and → g.inputs.length ≤ 2 → effInputs g = g.inputs := by
    intro g h hlen; simp [effInputs, h, GateOp.eval, List.take_of_length_le hlen]
  have effInputs_or : ∀ g : Gate, g.op = .or → g.inputs.length ≤ 2 → effInputs g = g.inputs := by
    intro g h hlen; simp [effInputs, h, GateOp.eval, List.take_of_length_le hlen]
  by_cases htwo : ∃ v ∉ A, 2 ≤ (C.gates.filter fun g => (match g.op with | .or => false | _ => true) && (effInputs g).contains v.val).length
  · obtain ⟨v, hvA, hv2⟩ := htwo
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
    let P : Gate → Bool := fun g => (match g.op with | .or => false | _ => true) && (effInputs g).contains v.val
    have hexPair : ∃ i1 i2, ∃ (h1 : i1 < C.gates.length) (h2 : i2 < C.gates.length),
        i1 < i2 ∧ C.gates[i1].op ≠ .or ∧ v.val ∈ effInputs C.gates[i1] ∧
        C.gates[i2].op ≠ .or ∧ v.val ∈ effInputs C.gates[i2] := by
      have hrec : ∀ (l : List Gate), 2 ≤ (l.filter P).length →
          ∃ i1 i2, ∃ (h1 : i1 < l.length) (h2 : i2 < l.length),
            i1 < i2 ∧ P l[i1] = true ∧ P l[i2] = true := by
        intro l
        induction l with
        | nil => intro h; simp at h
        | cons g r ih =>
          intro h
          rw [List.filter_cons] at h
          split_ifs at h with hPg
          · have hpos : 0 < (r.filter P).length := by simp at h; omega
            have hne : r.filter P ≠ [] := List.ne_nil_of_length_pos hpos
            obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
            have ht' := List.mem_filter.mp ht
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht'.1
            exact ⟨0, j + 1, by simp, by simp [hj], by omega, hPg, ht'.2⟩
          · obtain ⟨i1, i2, h1, h2, hlt, hp1, hp2⟩ := ih h
            exact ⟨i1 + 1, i2 + 1, by simp [h1], by simp [h2], by omega, hp1, hp2⟩
      obtain ⟨i1, i2, h1, h2, hlt, hp1, hp2⟩ := hrec C.gates hv2
      simp only [P, Bool.and_eq_true, List.contains_iff_mem] at hp1 hp2
      have hne1 : C.gates[i1].op ≠ .or := by intro h; rw [h] at hp1; simp at hp1
      have hne2 : C.gates[i2].op ≠ .or := by intro h; rw [h] at hp2; simp at hp2
      exact ⟨i1, i2, h1, h2, hlt, hne1, hp1.2, hne2, hp2.2⟩
    obtain ⟨i1, i2, hi1, hi2, hlt12, hnon1, hmem1, hnon2, hmem2⟩ := hexPair
    let st := C.gates.foldl simplifyGate ([], initEnv)
    obtain ⟨hfanSt, hboundSt, heqSt⟩ := simplifyFold_sound C.gates hmin.1
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
      unfold circuitFun Circuit.eval Circuit.wires
      rw [← heqOut, heqSt x1 (n + k) (by omega), heqSt x2 (n + k) (by omega), hkb]
    have hi1_elim : (simplifyGate ((C.gates.take i1).foldl simplifyGate ([], initEnv)) C.gates[i1]).1.length =
        ((C.gates.take i1).foldl simplifyGate ([], initEnv)).1.length :=
      simplifyGate_elim_of_const_input _ C.gates[i1] (hmin.1 _ (List.getElem_mem hi1)) v.val hmem1 false
        (by rw [hstAt i1 (Nat.le_of_lt hi1) v.val (by omega), hvConst])
    have hi2_elim : (simplifyGate ((C.gates.take i2).foldl simplifyGate ([], initEnv)) C.gates[i2]).1.length =
        ((C.gates.take i2).foldl simplifyGate ([], initEnv)).1.length :=
      simplifyGate_elim_of_const_input _ C.gates[i2] (hmin.1 _ (List.getElem_mem hi2)) v.val hmem2 false
        (by rw [hstAt i2 (Nat.le_of_lt hi2) v.val (by omega), hvConst])
    have hi1_const : ∃ c1 : Bool, st.2.getD (n + i1) (Sum.inl false) = Sum.inl c1 := by
      obtain ⟨c1, hc1⟩ := simplifyGate_const_of_nonOr_false ((C.gates.take i1).foldl simplifyGate ([], initEnv))
        C.gates[i1] (hmin.1 _ (List.getElem_mem hi1)) hnon1 v.val hmem1
        (by rw [hstAt i1 (Nat.le_of_lt hi1) v.val (by omega), hvConst])
      have htkLen : ((C.gates.take i1).foldl simplifyGate ([], initEnv)).2.length = n + i1 := by
        rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi1)]; simp [initEnv]
      rw [htkLen] at hc1
      have hstepEq : (C.gates.take (i1 + 1)).foldl simplifyGate ([], initEnv) =
          simplifyGate ((C.gates.take i1).foldl simplifyGate ([], initEnv)) C.gates[i1] := by
        rw [List.take_succ_eq_append_getElem hi1, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [← hstepEq, hstAt (i1 + 1) (by omega) (n + i1) (by omega)] at hc1
      exact ⟨c1, hc1⟩
    have hi2_const : ∃ c2 : Bool, st.2.getD (n + i2) (Sum.inl false) = Sum.inl c2 := by
      obtain ⟨c2, hc2⟩ := simplifyGate_const_of_nonOr_false ((C.gates.take i2).foldl simplifyGate ([], initEnv))
        C.gates[i2] (hmin.1 _ (List.getElem_mem hi2)) hnon2 v.val hmem2
        (by rw [hstAt i2 (Nat.le_of_lt hi2) v.val (by omega), hvConst])
      have htkLen : ((C.gates.take i2).foldl simplifyGate ([], initEnv)).2.length = n + i2 := by
        rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi2)]; simp [initEnv]
      rw [htkLen] at hc2
      have hstepEq : (C.gates.take (i2 + 1)).foldl simplifyGate ([], initEnv) =
          simplifyGate ((C.gates.take i2).foldl simplifyGate ([], initEnv)) C.gates[i2] := by
        rw [List.take_succ_eq_append_getElem hi2, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [← hstepEq, hstAt (i2 + 1) (by omega) (n + i2) (by omega)] at hc2
      exact ⟨c2, hc2⟩
    obtain ⟨c1, hc1⟩ := hi1_const
    obtain ⟨c2, hc2⟩ := hi2_const
    obtain ⟨j1, hj1, hlt_i1_j1, hread1⟩ := minimal_gate_has_reader i1 hi1 (hconst_ne_out i1 hi1 c1 hc1)
    obtain ⟨j2, hj2, hlt_i2_j2, hread2⟩ := minimal_gate_has_reader i2 hi2 (hconst_ne_out i2 hi2 c2 hc2)
    have hj1_ne_i2 : j1 ≠ i2 := by
      intro heq; subst j1
      have hf1 := hmin.1 C.gates[i1] (List.getElem_mem hi1)
      have hf2 := hmin.1 C.gates[i2] (List.getElem_mem hi2)
      rcases hf2.1 with hop2 | hop2 | hop2
      · rw [effInputs_and C.gates[i2] hop2 hf2.2] at hmem2 hread1
        have hpair : C.gates[i2].inputs = [v.val, n + i1] ∨ C.gates[i2].inputs = [n + i1, v.val] := by
          cases hgin2 : C.gates[i2].inputs with
          | nil => rw [hgin2] at hmem2; simp at hmem2
          | cons a tl =>
            cases tl with
            | nil => rw [hgin2] at hmem2 hread1; simp at hmem2 hread1; omega
            | cons b tl2 =>
              cases tl2 with
              | nil =>
                rw [hgin2] at hmem2 hread1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread1
                rcases hmem2 with rfl | rfl <;> rcases hread1 with h | h
                · omega
                · left; rw [h]
                · right; rw [h]
                · omega
              | cons _ _ => rw [hgin2] at hf2; simp at hf2
        have hev2 : ∀ x : Fin n → Bool,
            (C.wires (List.ofFn x)).getD (n + i2) false =
              (x v && (C.wires (List.ofFn x)).getD (n + i1) false) := by
          intro x
          change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i2) false = _
          rw [circuitWires_gate C.gates x i2 hi2]
          have hvW : (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD v.val false = x v := by
            unfold Circuit.wires
            rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
            simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
          rcases hpair with h | h <;> rw [h, hop2]
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true,
              show v.val < n + i2 by omega, show n + i1 < n + i2 by omega, ↓reduceIte, hvW]; rfl
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true,
              show v.val < n + i2 by omega, show n + i1 < n + i2 by omega, ↓reduceIte, hvW, Bool.and_comm]; rfl
        rcases hf1.1 with hop1 | hop1 | hop1
        · obtain ⟨x, hx⟩ := minimal_no_dup_wire i2 hi2 (n + i1) (by omega)
          apply hx; rw [hev2 x]
          by_cases hxv : x v = true
          · simp [hxv]
          · have hxvf : x v = false := by
              cases h : x v
              · rfl
              · exact False.elim (hxv h)
            simp only [hxvf, Bool.false_and]; symm
            change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + i1) false = false
            rw [circuitWires_gate C.gates x i1 hi1, hop1]
            rw [effInputs_and C.gates[i1] hop1 hf1.2] at hmem1
            simp only [GateOp.eval, List.all_eq_false]
            refine ⟨false, ?_, by decide⟩
            rw [List.mem_map]
            refine ⟨v.val, hmem1, ?_⟩
            rw [if_pos (by omega : v.val < n + i1)]
            unfold Circuit.wires
            rw [circuitWires_prefix C.gates (List.ofFn x) v.val (by simp)]
            simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, hxvf]
        · exact False.elim (hnon1 hop1)
        · rw [Set.mem_singleton_iff] at hop1
          obtain ⟨x, hx⟩ := minimal_no_const_false i2 hi2
          rw [hev2 x] at hx
          have hnot1 : (C.wires (List.ofFn x)).getD (n + i1) false = !x v := by
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
          rw [hnot1] at hx; cases x v <;> simp at hx
      · exact False.elim (hnon2 hop2)
      · rw [Set.mem_singleton_iff] at hop2
        rw [effInputs_not C.gates[i2] hop2] at hmem2 hread1
        cases hgin2 : C.gates[i2].inputs with
        | nil => rw [hgin2] at hmem2; simp at hmem2
        | cons u tl =>
          rw [hgin2] at hmem2 hread1
          simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem2 hread1
          omega
    have hj1_elim : (simplifyGate ((C.gates.take j1).foldl simplifyGate ([], initEnv)) C.gates[j1]).1.length =
        ((C.gates.take j1).foldl simplifyGate ([], initEnv)).1.length :=
      simplifyGate_elim_of_const_input _ C.gates[j1] (hmin.1 _ (List.getElem_mem hj1)) (n + i1) hread1 c1
        (by rw [hstAt j1 (Nat.le_of_lt hj1) (n + i1) (by omega), hc1])
    have hj2_elim : (simplifyGate ((C.gates.take j2).foldl simplifyGate ([], initEnv)) C.gates[j2]).1.length =
        ((C.gates.take j2).foldl simplifyGate ([], initEnv)).1.length :=
      simplifyGate_elim_of_const_input _ C.gates[j2] (hmin.1 _ (List.getElem_mem hj2)) (n + i2) hread2 c2
        (by rw [hstAt j2 (Nat.le_of_lt hj2) (n + i2) (by omega), hc2])
    have h4 : st.1.length + 4 ≤ C.gates.length := by
      by_cases hjeq : j1 = j2
      · subst hjeq
        have hj_const : ∃ c3 : Bool, st.2.getD (n + j1) (Sum.inl false) = Sum.inl c3 := by
          obtain ⟨c3, hc3⟩ := simplifyGate_const_of_two_const ((C.gates.take j1).foldl simplifyGate ([], initEnv))
            C.gates[j1] (hmin.1 _ (List.getElem_mem hj1)) (n + i1) (n + i2) (by omega) hread1 hread2 c1 c2
            (by rw [hstAt j1 (Nat.le_of_lt hj1) (n + i1) (by omega), hc1])
            (by rw [hstAt j1 (Nat.le_of_lt hj1) (n + i2) (by omega), hc2])
          have htkLen : ((C.gates.take j1).foldl simplifyGate ([], initEnv)).2.length = n + j1 := by
            rw [simplifyFold_env_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj1)]; simp [initEnv]
          rw [htkLen] at hc3
          have hstepEq : (C.gates.take (j1 + 1)).foldl simplifyGate ([], initEnv) =
              simplifyGate ((C.gates.take j1).foldl simplifyGate ([], initEnv)) C.gates[j1] := by
            rw [List.take_succ_eq_append_getElem hj1, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [← hstepEq, hstAt (j1 + 1) (by omega) (n + j1) (by omega)] at hc3
          exact ⟨c3, hc3⟩
        obtain ⟨c3, hc3⟩ := hj_const
        obtain ⟨j3, hj3, hlt_j1_j3, hread3⟩ := minimal_gate_has_reader j1 hj1 (hconst_ne_out j1 hj1 c3 hc3)
        have hj3_elim : (simplifyGate ((C.gates.take j3).foldl simplifyGate ([], initEnv)) C.gates[j3]).1.length =
            ((C.gates.take j3).foldl simplifyGate ([], initEnv)).1.length :=
          simplifyGate_elim_of_const_input _ C.gates[j3] (hmin.1 _ (List.getElem_mem hj3)) (n + j1) hread3 c3
            (by rw [hstAt j3 (Nat.le_of_lt hj3) (n + j1) (by omega), hc3])
        let S : Finset ℕ := {i1, i2, j1, j3}
        have hScard : S.card = 4 := by
          dsimp only [S]
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_singleton]
        have hSbound := simplifyFold_size_bound C.gates S (fun k hk => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl | rfl
          · exact ⟨hi1, hi1_elim⟩
          · exact ⟨hi2, hi2_elim⟩
          · exact ⟨hj1, hj1_elim⟩
          · exact ⟨hj3, hj3_elim⟩)
        rw [hScard] at hSbound
        exact hSbound
      · let S : Finset ℕ := {i1, i2, j1, j2}
        have hScard : S.card = 4 := by
          dsimp only [S]
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_singleton]
        have hSbound := simplifyFold_size_bound C.gates S (fun k hk => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl | rfl
          · exact ⟨hi1, hi1_elim⟩
          · exact ⟨hi2, hi2_elim⟩
          · exact ⟨hj1, hj1_elim⟩
          · exact ⟨hj2, hj2_elim⟩)
        rw [hScard] at hSbound
        exact hSbound
    have houtLt : C.output < n + C.gates.length := by
      by_contra hge
      obtain ⟨x1, x2, hne⟩ := hnonconst
      apply hne
      unfold circuitFun Circuit.eval Circuit.wires
      have hlen1 : (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x1 v false))).length = n + C.gates.length := by
        rw [circuitWires_len, List.length_ofFn]
      have hlen2 : (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x2 v false))).length = n + C.gates.length := by
        rw [circuitWires_len, List.length_ofFn]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [hlen1]; omega),
        List.getElem?_eq_none (by rw [hlen2]; omega)]
    cases houtSym : st.2.getD C.output (Sum.inl false) with
    | inl b =>
      exfalso
      obtain ⟨x1, x2, hne⟩ := hnonconst
      apply hne
      unfold circuitFun Circuit.eval Circuit.wires
      rw [heqSt x1 C.output houtLt, heqSt x2 C.output houtLt, houtSym]
    | inr out' =>
      refine ⟨v, hvA, st.1.length, h4, ⟨st.1, out'⟩, hfanSt, le_rfl, fun x => ?_⟩
      symm
      change (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn (Function.update x v false))).getD C.output false =
        (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).getD out' false
      rw [heqSt x C.output houtLt, houtSym]
  · push Not at htwo
    have hle1 : ∀ v ∉ A, (C.gates.filter fun g => (match g.op with | .or => false | _ => true) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1 := by
      intro v hvA
      have := htwo v hvA
      change (C.gates.filter fun g => (match g.op with | .or => false | _ => true) && (effInputs g).contains v.val).length ≤ 1
      omega
    by_cases hnot : ∃ g ∈ C.gates, g.op = .not
    · exact hHasNot n G A C hdeg hcycle hend hedge hmin hfun hread hle1 hnot hsmall
    · push Not at hnot
      exact hMono n G A C hdeg hcycle hend hedge hmin hfun hread hle1 hnot hsmall
