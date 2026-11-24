import Mathlib
import PEqualNP.Defs

-- A lift keeps the function: where h is false, gate m = OR(p, h) equals p, so erasing it with
-- its readers sent to p changes no later wire; where h is true, h below the output makes both
-- outputs true. The gate count is unchanged and every gate still reads two earlier wires.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

namespace PEqualNP.Outside.L_meta_4293

-- The wire list of a gate list started on the list w.
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_app (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => by simp [run]
  | g :: gs, w => by rw [run_cons, run_len gs]; simp; omega

theorem run_pre : ∀ (gs : List Gate) (w : List Bool) (r : ℕ), r < w.length →
    (run gs w).getD r false = w.getD r false
  | [], _, _, _ => rfl
  | g :: gs, w, r, hr => by
    rw [run_cons, run_pre gs _ r (by simp; omega), List.getD_append _ _ _ _ hr]

theorem run_high (gs : List Gate) (w : List Bool) (r : ℕ) (hr : w.length + gs.length ≤ r) :
    (run gs w).getD r false = false :=
  List.getD_eq_default _ _ (by rw [run_len]; omega)

theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs w).getD (w.length + j) false = gs[j].op.eval (gs[j].inputs.map fun r =>
      if r < w.length + j then (run gs w).getD r false else false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hul : (run (gs.take j) w).length = w.length + j := by
    rw [run_len, List.length_take]; omega
  have hall : run gs w = run (gs.drop (j + 1)) (run (gs.take j) w ++
      [gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) w).getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [run_app, run_cons]
  have key : ∀ r, (if r < w.length + j then (run gs w).getD r false else false) =
      (run (gs.take j) w).getD r false := by
    intro r
    split_ifs with h
    · rw [hall, run_pre _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    · exact (List.getD_eq_default _ _ (by omega)).symm
  simp only [key]
  rw [hall, run_pre _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hul, Nat.sub_self, List.getD_cons_zero]

def substWire (k a i : ℕ) : ℕ := if i < k then i else if i = k then a else i - 1

def delete (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map
      (fun g => ⟨g.op, g.inputs.map (substWire (m + j) a)⟩), substWire (m + j) a C.output⟩

theorem delete_inv (k a : ℕ) (ha : a < k) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length + 1 → k < w1.length →
    (∀ i < w1.length, w2.getD (substWire k a i) false = w1.getD i false) →
    ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map (substWire k a)⟩) w2).getD
      (substWire k a i) false = (run gs w1).getD i false
  | [], w1, w2, hl, hk, h => by
    intro i
    by_cases hi : i < w1.length
    · exact h i hi
    · have : substWire k a i = i - 1 := by unfold substWire; split_ifs <;> omega
      rw [this]
      simp only [run, List.map_nil, List.foldl_nil]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | g :: gs, w1, w2, hl, hk, h => by
    simp only [List.map_cons, run_cons]
    have hval : ((g.inputs.map (substWire k a)).map fun r => w2.getD r false) =
        g.inputs.map (fun r => w1.getD r false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      by_cases hr : r < w1.length
      · exact h r hr
      · have : substWire k a r = r - 1 := by unfold substWire; split_ifs <;> omega
        simp only [Function.comp_apply, this]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    apply delete_inv k a ha gs _ _ (by simp; omega) (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rw [hval]
    by_cases hi' : i < w1.length
    · have hs : substWire k a i < w2.length := by unfold substWire; split_ifs <;> omega
      rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hi']
      exact h i hi'
    · have he : i = w1.length := by omega
      have hs : substWire k a i = w2.length := by unfold substWire; split_ifs <;> omega
      rw [hs, he]
      simp [List.getD_append_right]

theorem delete_run (m : ℕ) (C : Circuit) (j a : ℕ) (v : List Bool) (hv : v.length = m)
    (hj : j < C.gates.length) (ha : a < m + j)
    (heq : (run C.gates v).getD (m + j) false = (run C.gates v).getD a false) :
    ∀ i, (run (delete m C j a).gates v).getD (substWire (m + j) a i) false =
      (run C.gates v).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  set w2 := run (C.gates.take j) v with hw2
  have hl2 : w2.length = m + j := by rw [hw2, run_len, List.length_take]; omega
  set w1 := w2 ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w2.getD i false)] with hw1
  have hall : run C.gates v = run (C.gates.drop (j + 1)) w1 := by
    conv_lhs => rw [hsplit]
    rw [run_app, run_cons]
  have hnew : run (delete m C j a).gates v =
      run ((C.gates.drop (j + 1)).map fun g => ⟨g.op, g.inputs.map (substWire (m + j) a)⟩) w2 := by
    simp only [delete]; rw [run_app]
  rw [hnew, hall]
  apply delete_inv (m + j) a ha _ w1 w2 (by simp [hw1]) (by simp [hw1, hl2])
  intro i hi
  by_cases hlt : i < m + j
  · have : substWire (m + j) a i = i := by unfold substWire; simp [hlt]
    rw [this, hw1, List.getD_append _ _ _ _ (by omega)]
  · have hie : i = m + j := by simp [hw1, hl2] at hi; omega
    have : substWire (m + j) a i = a := by unfold substWire; simp [hie]
    rw [this]
    have e1 : (run C.gates v).getD (m + j) false = w1.getD (m + j) false := by
      rw [hall, run_pre _ _ _ (by simp [hw1, hl2])]
    have e2 : (run C.gates v).getD a false = w1.getD a false := by
      rw [hall, run_pre _ _ _ (by simp [hw1, hl2]; omega)]
    rw [hie, ← e1, heq, e2, hw1, List.getD_append _ _ _ _ (by omega)]


theorem redirect_eq (n m p i : ℕ) : eraseRedirect n m p i = substWire (n + m) p i := by
  unfold eraseRedirect substWire; split_ifs <;> omega

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p = delete n C m p := by
  unfold eraseGate delete
  rw [if_pos hm]
  have hf : (fun g : Gate => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate)) =
      fun g => ⟨g.op, g.inputs.map (substWire (n + m) p)⟩ := by
    funext g; congr 1; apply List.map_congr_left; intro i _; exact redirect_eq n m p i
  rw [hf, redirect_eq]

theorem wires_run (C : Circuit) (w : List Bool) : C.wires w = run C.gates w := rfl

theorem sw_lt (k a i b : ℕ) (ha : a < k) (hk : k ≤ b) (hi : i < b + 1) : substWire k a i < b := by
  unfold substWire; split_ifs <;> omega

theorem main (n : ℕ) (C C' : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (ho : C.output < n + C.gates.length) (hL : Lift n C C') :
    PEqualNP.TopForm.IsAO2 n C' ∧ C'.output < n + C'.gates.length ∧ C'.size = C.size ∧
      circuitFun n C' = circuitFun n C := by
  obtain ⟨m, hm, p, hp, h, hh, hnh, hg, hbelow, rfl⟩ := hL
  obtain ⟨hand, hback, htwo⟩ := hC
  have hE := erase_eq n C m p hm
  have hEg : (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map
      (fun g => ⟨g.op, g.inputs.map (substWire (n + m) p)⟩) := by rw [hE]; rfl
  have hEo : (eraseGate n C m p).output = substWire (n + m) p C.output := by rw [hE]; rfl
  have hElen : (eraseGate n C m p).gates.length = C.gates.length - 1 := by
    rw [hEg]; simp; omega
  have hgm : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hg with e | e
    · left; rw [List.getElem?_eq_getElem hm] at e; exact Option.some.inj e
    · right; rw [List.getElem?_eq_getElem hm] at e; exact Option.some.inj e
  -- the gates of the lifted circuit
  have hgates : (liftAt n C m p h).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map
      (fun g => ⟨g.op, g.inputs.map (substWire (n + m) p)⟩) ++
      [⟨GateOp.or, [substWire (n + m) p C.output, h]⟩] := by
    simp only [liftAt, hEg, hEo]
  have hlen : (liftAt n C m p h).gates.length = C.gates.length := by
    rw [hgates]; simp; omega
  have hout : (liftAt n C m p h).output = n + (C.gates.length - 1) := by
    simp only [liftAt, hElen]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- AND and OR gates only
    intro g hg'
    rw [hgates] at hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact hand g (List.mem_of_mem_take h2)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h2
        exact hand g0 (List.mem_of_mem_drop hg0)
    · simp at h1; subst h1; right; rfl
  · -- every gate reads earlier wires
    intro j hj i hi
    rw [hlen] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)] at hi
    have hN : 1 ≤ C.gates.length := by omega
    by_cases hjm : j < m
    · have e : (liftAt n C m p h).gates[j]'(by rw [hlen]; exact hj) = C.gates[j] := by
        simp only [hgates]
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
          List.getElem_take]
      rw [e] at hi
      have := hback j hj i (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hj]; exact hi)
      exact this
    · by_cases hjl : j < C.gates.length - 1
      · have e : (liftAt n C m p h).gates[j]'(by rw [hlen]; exact hj) =
            ⟨C.gates[j + 1].op, C.gates[j + 1].inputs.map (substWire (n + m) p)⟩ := by
          simp only [hgates]
          rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
          simp only [List.getElem_map, List.getElem_drop, List.length_take]
          simp only [show m + 1 + (j - min m C.gates.length) = j + 1 by omega]
        rw [e] at hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
        have := hback (j + 1) (by omega) i0 (by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          rw [List.getD_eq_getElem _ _ (by omega)]; exact hi0)
        exact sw_lt _ _ _ _ hp (by omega) (by omega)
      · have hje : j = C.gates.length - 1 := by omega
        have e : (liftAt n C m p h).gates[j]'(by rw [hlen]; exact hj) =
            ⟨GateOp.or, [substWire (n + m) p C.output, h]⟩ := by
          simp only [hgates]
          rw [List.getElem_append_right (by simp; omega)]
          simp
        rw [e] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact sw_lt _ _ _ _ hp (by omega) (by omega)
        · omega
  · -- exactly two inputs each
    intro g hg'
    rw [hgates] at hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact htwo g (List.mem_of_mem_take h2)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h2
        simpa using htwo g0 (List.mem_of_mem_drop hg0)
    · simp at h1; subst h1; rfl
  · rw [hout, hlen]; omega
  · unfold Circuit.size; rw [hlen]
  · funext x
    let v := List.ofFn x
    have hv : v.length = n := List.length_ofFn
    set W := run C.gates v with hW
    set WE := run (eraseGate n C m p).gates v with hWE
    have hWElen : WE.length = n + (C.gates.length - 1) := by rw [hWE, run_len, hv, hElen]
    -- the prefix of the first m gates is shared
    have pre : ∀ i < n + m, WE.getD i false = W.getD i false := by
      intro i hi
      have hs : C.gates = C.gates.take m ++ C.gates.drop m := (List.take_append_drop m _).symm
      have e1 : W = run (C.gates.drop m) (run (C.gates.take m) v) := by
        rw [hW]; conv_lhs => rw [hs]
        rw [run_app]
      have e2 : WE = run ((C.gates.drop (m + 1)).map
          (fun g => ⟨g.op, g.inputs.map (substWire (n + m) p)⟩)) (run (C.gates.take m) v) := by
        rw [hWE, hEg, run_app]
      have hl : (run (C.gates.take m) v).length = n + m := by
        rw [run_len, hv, List.length_take]; omega
      rw [e1, e2, run_pre (C.gates.drop m) _ i (by rw [hl]; exact hi),
        run_pre ((C.gates.drop (m + 1)).map
          (fun g => ⟨g.op, g.inputs.map (substWire (n + m) p)⟩)) _ i (by rw [hl]; exact hi)]
    -- the value of gate m
    have hgv : W.getD (n + m) false = (W.getD p false || W.getD h false) := by
      have := run_gate C.gates v m hm
      rw [hv] at this
      rw [hW, this]
      rcases hgm with e | e <;> rw [e] <;> simp [GateOp.eval, hp, hh] <;> ac_rfl
    -- the lifted output
    have hC' : circuitFun n (liftAt n C m p h) x =
        (WE.getD (substWire (n + m) p C.output) false || WE.getD h false) := by
      show (run (liftAt n C m p h).gates v).getD (liftAt n C m p h).output false = _
      have e : (liftAt n C m p h).gates = (eraseGate n C m p).gates ++
          [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩] := rfl
      rw [e, run_app, hEo, hout, ← hWE, run_cons]
      show (WE ++ [GateOp.or.eval ([substWire (n + m) p C.output, h].map
        fun i => WE.getD i false)]).getD (n + (C.gates.length - 1)) false = _
      rw [show n + (C.gates.length - 1) = WE.length from hWElen.symm,
        List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp [GateOp.eval]
    have hCx : circuitFun n C x = W.getD C.output false := rfl
    rw [hC', hCx]
    cases hhv : W.getD h false
    · -- h false: gate m equals p
      have heq : W.getD (n + m) false = W.getD p false := by rw [hgv, hhv, Bool.or_false]
      have key := delete_run n C m p v hv hm hp (by rw [← hW]; exact heq)
      rw [← hE] at key
      rw [key C.output, pre h hh, hhv, Bool.or_false]
    · -- h true: both outputs true
      have hb := hbelow x hhv
      have : W.getD C.output false = true := hb
      rw [this, pre h hh, hhv, Bool.or_true]

end PEqualNP.Outside.L_meta_4293

theorem PEqualNP.Outside.L_meta_4293 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C C' hC ho hL
  exact PEqualNP.Outside.L_meta_4293.main n C C' hC ho hL
