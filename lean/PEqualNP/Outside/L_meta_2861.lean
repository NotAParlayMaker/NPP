import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside

private lemma fold_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp
    omega

private lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih _)

private lemma getD_prefix {w l : List Bool} (h : w <+: l) {i : ℕ} (hi : i < w.length) :
    l.getD i false = w.getD i false := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_len C.gates x

private lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = (C.gates[j]).op.eval
      ((C.gates[j]).inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hpl : ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + j := by
    rw [fold_len, List.length_take, min_eq_left hj.le]
  have hfull : C.wires x = (C.gates.drop (j + 1)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)]) := by
    conv_lhs => rw [Circuit.wires, hsplit, List.foldl_append, List.foldl_cons]
  have hp1 := fold_prefix (C.gates.drop (j + 1)) (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)])
  rw [← hfull] at hp1
  have hp0 := (List.prefix_append _ _).trans hp1
  rw [getD_prefix hp1 (by rw [List.length_append, hpl]; simp)]
  rw [← hpl, List.getD_append_right _ _ _ _ le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · rw [hpl, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    exact (getD_prefix hp0 (by rw [hpl]; exact hi)).symm
  · rw [hpl, ite_eq_right_of_eq_false _ _ (eq_false hi)]
    exact List.getD_eq_default _ _ (by rw [hpl]; omega)

private lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_prefix (fold_prefix C.gates x) hi

theorem L_meta_2861 : ∀ (n : ℕ) (C : Circuit) (i j a b c : ℕ),
    ReadsBack n C → j < C.gates.length → i < j →
    (gateAt C i).op = GateOp.and → (gateAt C i).inputs = [a, b] →
    (gateAt C j).op = GateOp.and → (gateAt C j).inputs = [n + i, c] →
    c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (gateAt C k).inputs) →
    C.output ≠ n + i →
    ReadsBack n (⟨(C.gates.set i ⟨GateOp.and, [a, c]⟩).set j
      ⟨GateOp.and, [n + i, b]⟩, C.output⟩ : Circuit) ∧
    (⟨(C.gates.set i ⟨GateOp.and, [a, c]⟩).set j
      ⟨GateOp.and, [n + i, b]⟩, C.output⟩ : Circuit).size = C.size ∧
    ∀ x : Fin n → Bool,
      (⟨(C.gates.set i ⟨GateOp.and, [a, c]⟩).set j
        ⟨GateOp.and, [n + i, b]⟩, C.output⟩ : Circuit).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
  intro n C i j a b c hreads hj hij hiop hiinputs hjop hjinputs hc hunique hout
  have hi : i < C.gates.length := hij.trans hj
  have ha : a < n + i := hreads i hi a (by simp [hiinputs])
  have hb : b < n + i := hreads i hi b (by simp [hiinputs])
  let D : Circuit :=
    ⟨(C.gates.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩, C.output⟩
  have hDlen : D.gates.length = C.gates.length := by simp [D]
  have hDi : gateAt D i = ⟨GateOp.and, [a, c]⟩ := by
    simp [gateAt, D, List.getD_eq_getElem?_getD, List.getElem?_set, hij.ne', hi]
  have hDj : gateAt D j = ⟨GateOp.and, [n + i, b]⟩ := by
    simp [gateAt, D, List.getD_eq_getElem?_getD, List.getElem?_set, hj]
  have hDsame (k : ℕ) (hki : k ≠ i) (hkj : k ≠ j) : gateAt D k = gateAt C k := by
    simp [gateAt, D, List.getD_eq_getElem?_getD, List.getElem?_set,
      Ne.symm hki, Ne.symm hkj]
  have hCi : C.gates[i] = ⟨GateOp.and, [a, b]⟩ := by
    have h : gateAt C i = ⟨GateOp.and, [a, b]⟩ := by
      generalize hgate : gateAt C i = g at hiop hiinputs ⊢
      cases g with
      | mk op inputs =>
        dsimp at hiop hiinputs ⊢
        cases hiop
        cases hiinputs
        rfl
    simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h
  have hCj : C.gates[j] = ⟨GateOp.and, [n + i, c]⟩ := by
    have h : gateAt C j = ⟨GateOp.and, [n + i, c]⟩ := by
      generalize hgate : gateAt C j = g at hjop hjinputs ⊢
      cases g with
      | mk op inputs =>
        dsimp at hjop hjinputs ⊢
        cases hjop
        cases hjinputs
        rfl
    simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h
  have hDreads : ReadsBack n D := by
    intro k hk q hq
    have hkC : k < C.gates.length := by omega
    by_cases hki : k = i
    · subst k
      rw [hDi] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ha
      · exact hc
    · by_cases hkj : k = j
      · subst k
        rw [hDj] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · omega
        · omega
      · rw [hDsame k hki hkj] at hq
        exact hreads k hkC q hq
  refine ⟨hDreads, by simp [D, Circuit.size], ?_⟩
  intro x
  change (D.wires (List.ofFn x)).getD C.output false =
    (C.wires (List.ofFn x)).getD C.output false
  have hw : ∀ w : ℕ, w ≠ n + i →
      (D.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwi
      by_cases hwtotal : n + C.gates.length ≤ w
      · have hDtotal : n + D.gates.length ≤ w := by omega
        rw [List.getD_eq_default _ _ (by rw [wires_len]; simpa using hDtotal),
          List.getD_eq_default _ _ (by rw [wires_len]; simpa using hwtotal)]
      · by_cases hwn : w < n
        · rw [wires_input D _ _ (by simp; omega), wires_input C _ _ (by simp; omega)]
        · let k := w - n
          have hwk : w = n + k := by dsimp [k]; omega
          have hk : k < C.gates.length := by omega
          rw [hwk] at hwi ⊢
          have hDk : k < D.gates.length := by omega
          by_cases hki : k = i
          · exact (hwi (by omega)).elim
          · by_cases hkj : k = j
            · rw [hkj] at hDk ⊢
              have hDiEval : (D.wires (List.ofFn x)).getD (n + i) false =
                  ((D.wires (List.ofFn x)).getD a false &&
                    (D.wires (List.ofFn x)).getD c false) := by
                have h := wires_gate D (List.ofFn x) i (by omega)
                have hDi' : D.gates[i] = ⟨GateOp.and, [a, c]⟩ := by
                  simpa [gateAt, List.getD_eq_getElem?_getD,
                    List.getElem?_eq_getElem (show i < D.gates.length by omega)] using hDi
                simp only [List.length_ofFn, hDi', List.map_cons, List.map_nil,
                  if_pos ha, if_pos hc] at h
                simpa [GateOp.eval] using h
              have hCiEval : (C.wires (List.ofFn x)).getD (n + i) false =
                  ((C.wires (List.ofFn x)).getD a false &&
                    (C.wires (List.ofFn x)).getD b false) := by
                have h := wires_gate C (List.ofFn x) i hi
                simp only [List.length_ofFn, hCi, List.map_cons, List.map_nil,
                  if_pos ha, if_pos hb] at h
                simpa [GateOp.eval] using h
              rw [show n + j = (List.ofFn x).length + j by simp]
              rw [wires_gate D _ _ hDk, wires_gate C _ _ hj]
              have hDj' : D.gates[j] = ⟨GateOp.and, [n + i, b]⟩ := by
                simpa [gateAt, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem hDk] using hDj
              simp only [List.length_ofFn, hDj', hCj, List.map_cons, List.map_nil,
                if_pos (by omega : n + i < n + j), if_pos (by omega : b < n + j),
                if_pos (by omega : c < n + j)]
              rw [hDiEval, hCiEval, ih a (by omega) (by omega), ih b (by omega) (by omega),
                ih c (by omega) (by omega)]
              cases (C.wires (List.ofFn x)).getD a false <;>
                cases (C.wires (List.ofFn x)).getD b false <;>
                cases (C.wires (List.ofFn x)).getD c false <;> rfl
            · have hDsame' : D.gates[k] = C.gates[k] := by
                have h := hDsame k hki hkj
                simpa [gateAt, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem hDk, List.getElem?_eq_getElem hk] using h
              rw [show n + k = (List.ofFn x).length + k by simp]
              rw [wires_gate D _ _ hDk, wires_gate C _ _ hk]
              simp only [List.length_ofFn, hDsame']
              congr 1
              apply List.map_congr_left
              intro q hqmem
              by_cases hq : q < n + k
              · have hqmem' : q ∈ (gateAt C k).inputs := by
                  simpa [gateAt, List.getD_eq_getElem?_getD,
                    List.getElem?_eq_getElem hk] using hqmem
                have hqi : q ≠ n + i := by
                  intro hqi
                  subst q
                  exact hunique k hk hkj hqmem'
                rw [ih q (by omega) hqi]
              · simp only [if_neg hq]
  exact hw C.output hout

end PEqualNP.Outside
