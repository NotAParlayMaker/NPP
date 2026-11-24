import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma foldl_getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma take_succ_foldl (gs : List Gate) (w : List Bool) (m : ℕ) (hm : m < gs.length) :
    (gs.take (m + 1)).foldl step w = step ((gs.take m).foldl step w) gs[m] := by
  rw [List.take_succ_eq_append_getElem hm, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma getD_take_eq (gs : List Gate) (x0 : List Bool) (m k : ℕ) (hk : k < x0.length + m) (hm : m ≤ gs.length) :
    ((gs.take m).foldl step x0).getD k false = (gs.foldl step x0).getD k false := by
  have hsplit := congrArg (fun l => (l.foldl step x0).getD k false) (List.take_append_drop m gs).symm
  rw [hsplit, List.foldl_append]
  symm
  exact foldl_getD_prefix (gs.drop m) ((gs.take m).foldl step x0) k
    (by rw [foldl_length, List.length_take, Nat.min_eq_left hm]; exact hk)

lemma step_getD_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun r => w.getD r false) := by
  simp [step]

lemma gate_eval_at (gs : List Gate) (x0 : List Bool) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) :
    (gs.foldl step x0).getD (x0.length + k) false =
      g.op.eval (g.inputs.map fun r => ((gs.take k).foldl step x0).getD r false) := by
  have hk : k < gs.length := (List.getElem?_eq_some_iff.mp hg).1
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  rw [← getD_take_eq gs x0 (k + 1) (x0.length + k) (by omega) (by omega)]
  rw [take_succ_foldl gs x0 k hk, hgk]
  have hlen : ((gs.take k).foldl step x0).length = x0.length + k := by
    rw [foldl_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [← hlen]
  exact step_getD_new _ _

lemma bool_rebracket (op1 op2 : GateOp)
    (hop : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (va vb vc vz : Bool) :
    op1.eval [op2.eval [va, op1.eval [vb, vc]], vz] =
      op1.eval [op2.eval [va, vb], op1.eval [op2.eval [va, vc], vz]] ∧
    op1.eval [op2.eval [va, op1.eval [vb, vc]], vz] =
      op1.eval [op1.eval [op2.eval [va, vc], vz], op2.eval [va, vb]] := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases va <;> cases vb <;> cases vc <;> cases vz <;> decide

lemma core (n : ℕ) (C : Circuit) (j is iv iw a b c z : ℕ) (op1 op2 : GateOp)
    (hop : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (his : C.gates[is]? = some { op := op2, inputs := [a, b] })
    (hiv : C.gates[iv]? = some { op := op2, inputs := [a, c] })
    (hiw : C.gates[iw]? = some { op := op1, inputs := [n + iv, z] })
    (hj : C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
          C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] })
    (his_j : is < j) (hiv_iw : iv < iw) (hiw_j : iw < j)
    (ha_is : a < n + is) (hb_is : b < n + is) (ha_iv : a < n + iv) (hb_iv : b < n + iv) (hc_iv : c < n + iv)
    (hz_iw : z < n + iw) (hz_iv : z ≠ n + iv)
    (hno_iv : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs)
    (hno_iw : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs)
    (hout_iv : C.output ≠ n + iv) (hout_iw : C.output ≠ n + iw) :
    let gs' := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
        { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }
    circuitFun n { gates := gs', output := C.output } = circuitFun n C ∧
    gs'.length = C.gates.length := by
  set g_iv' : Gate := { op := op1, inputs := [b, c] }
  set g_iw' : Gate := { op := op2, inputs := [a, n + iv] }
  set g_j' : Gate := { op := op1, inputs := [n + iw, z] }
  set gs := C.gates
  set gs' := ((gs.set iv g_iv').set iw g_iw').set j g_j'
  have hlen' : gs'.length = gs.length := by simp [gs']
  refine ⟨?_, hlen'⟩
  have hj_lt : j < gs.length := by
    rcases hj with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  have hiv_lt : iv < gs.length := by omega
  have hiw_lt : iw < gs.length := by omega
  have his_lt : is < gs.length := by omega
  have hgs'_iv : gs'[iv]? = some g_iv' := by
    simp only [gs']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have hgs'_iw : gs'[iw]? = some g_iw' := by
    simp only [gs']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hgs'_j : gs'[j]? = some g_j' := by
    simp only [gs']
    rw [List.getElem?_set_self (by simp; omega)]
  have hgs'_other : ∀ k, k ≠ iv → k ≠ iw → k ≠ j → gs'[k]? = gs[k]? := by
    intro k h1 h2 h3
    simp only [gs']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  funext x
  set x0 : List Bool := List.ofFn x
  have hx0 : x0.length = n := by simp [x0]
  set W := gs.foldl step x0
  have hmain : ∀ m ≤ gs.length,
      (∀ r < n + m, r ≠ n + iv → r ≠ n + iw →
        ((gs'.take m).foldl step x0).getD r false = ((gs.take m).foldl step x0).getD r false) ∧
      (iv < m → ((gs'.take m).foldl step x0).getD (n + iv) false =
        op1.eval [W.getD b false, W.getD c false]) ∧
      (iw < m → ((gs'.take m).foldl step x0).getD (n + iw) false =
        op2.eval [W.getD a false, op1.eval [W.getD b false, W.getD c false]]) := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨fun r _ _ _ => rfl, fun h => by omega, fun h => by omega⟩
    | succ m ih =>
      obtain ⟨hag, hiv_eq, hiw_eq⟩ := ih (by omega)
      have hm_lt : m < gs.length := by omega
      have hm_lt' : m < gs'.length := by omega
      rw [take_succ_foldl gs' x0 m hm_lt', take_succ_foldl gs x0 m hm_lt]
      set L := (gs.take m).foldl step x0
      set L' := (gs'.take m).foldl step x0
      have hL : L.length = n + m := by
        dsimp only [L]; rw [foldl_length, hx0, List.length_take, Nat.min_eq_left (by omega)]
      have hL' : L'.length = n + m := by
        dsimp only [L']; rw [foldl_length, hx0, List.length_take, Nat.min_eq_left (by omega)]
      have hL_W : ∀ r < n + m, L.getD r false = W.getD r false := by
        intro r hr
        exact getD_take_eq gs x0 m r (by omega) (by omega)
      have hstep_old : ∀ r < n + m,
          (step L' gs'[m]).getD r false = L'.getD r false ∧
          (step L gs[m]).getD r false = L.getD r false := by
        intro r hr
        exact ⟨List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)⟩
      have hstep_new :
          (step L' gs'[m]).getD (n + m) false =
            gs'[m].op.eval (gs'[m].inputs.map fun r => L'.getD r false) ∧
          (step L gs[m]).getD (n + m) false =
            gs[m].op.eval (gs[m].inputs.map fun r => L.getD r false) := by
        constructor
        · unfold step; rw [List.getD_append_right _ _ _ _ (by omega), hL', Nat.sub_self, List.getD_cons_zero]
        · unfold step; rw [List.getD_append_right _ _ _ _ (by omega), hL, Nat.sub_self, List.getD_cons_zero]
      refine ⟨?_, ?_, ?_⟩
      · intro r hr hne1 hne2
        by_cases hrm : r < n + m
        · rw [(hstep_old r hrm).1, (hstep_old r hrm).2]
          exact hag r hrm hne1 hne2
        · have heq : r = n + m := by omega
          subst heq
          rw [hstep_new.1, hstep_new.2]
          have hm_ne_iv : m ≠ iv := by omega
          have hm_ne_iw : m ≠ iw := by omega
          by_cases hm_j : m = j
          · subst hm_j
            have hgj' : gs'[m] = g_j' := (List.getElem?_eq_some_iff.mp hgs'_j).2
            rw [hgj']
            simp only [g_j', List.map_cons, List.map_nil]
            have h1 : L'.getD (n + iw) false = op2.eval [W.getD a false, op1.eval [W.getD b false, W.getD c false]] :=
              hiw_eq hiw_j
            have h2 : L'.getD z false = W.getD z false := by
              rw [hag z (by omega) hz_iv (by omega), hL_W z (by omega)]
            rw [h1, h2]
            have his_val : W.getD (n + is) false = op2.eval [W.getD a false, W.getD b false] := by
              have := gate_eval_at gs x0 is _ his
              rw [hx0] at this
              rw [this]
              simp only [List.map_cons, List.map_nil]
              congr 1; congr 1
              · exact getD_take_eq gs x0 is a (by omega) (by omega)
              · congr 1; exact getD_take_eq gs x0 is b (by omega) (by omega)
            have hiv_val : W.getD (n + iv) false = op2.eval [W.getD a false, W.getD c false] := by
              have := gate_eval_at gs x0 iv _ hiv
              rw [hx0] at this
              rw [this]
              simp only [List.map_cons, List.map_nil]
              congr 1; congr 1
              · exact getD_take_eq gs x0 iv a (by omega) (by omega)
              · congr 1; exact getD_take_eq gs x0 iv c (by omega) (by omega)
            have hiw_val : W.getD (n + iw) false = op1.eval [op2.eval [W.getD a false, W.getD c false], W.getD z false] := by
              have := gate_eval_at gs x0 iw _ hiw
              rw [hx0] at this
              rw [this]
              simp only [List.map_cons, List.map_nil]
              rw [getD_take_eq gs x0 iw (n + iv) (by omega) (by omega),
                  getD_take_eq gs x0 iw z (by omega) (by omega), hiv_val]
            have hrb := bool_rebracket op1 op2 hop (W.getD a false) (W.getD b false) (W.getD c false) (W.getD z false)
            rcases hj with hj1 | hj2
            · have hgj : gs[m] = { op := op1, inputs := [n + is, n + iw] } := (List.getElem?_eq_some_iff.mp hj1).2
              rw [hgj]; simp only [List.map_cons, List.map_nil]
              rw [hL_W (n + is) (by omega), hL_W (n + iw) (by omega), his_val, hiw_val]
              exact hrb.1
            · have hgj : gs[m] = { op := op1, inputs := [n + iw, n + is] } := (List.getElem?_eq_some_iff.mp hj2).2
              rw [hgj]; simp only [List.map_cons, List.map_nil]
              rw [hL_W (n + iw) (by omega), hL_W (n + is) (by omega), his_val, hiw_val]
              exact hrb.2
          · have hsame : gs'[m] = gs[m] := by
              have h1 := hgs'_other m hm_ne_iv hm_ne_iw hm_j
              rw [List.getElem?_eq_getElem hm_lt', List.getElem?_eq_getElem hm_lt] at h1
              exact Option.some.inj h1
            rw [hsame]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hgm : gs[m]? = some gs[m] := List.getElem?_eq_getElem hm_lt
            have hu1 : u ≠ n + iv := fun h => hno_iv m gs[m] hgm hm_ne_iw (h ▸ hu)
            have hu2 : u ≠ n + iw := fun h => hno_iw m gs[m] hgm hm_j (h ▸ hu)
            by_cases hum : u < n + m
            · exact hag u hum hu1 hu2
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · intro hiv_s
        by_cases h1 : iv < m
        · rw [(hstep_old (n + iv) (by omega)).1]
          exact hiv_eq h1
        · have heq : m = iv := by omega
          subst heq
          rw [hstep_new.1]
          have hgiv' : gs'[m] = g_iv' := (List.getElem?_eq_some_iff.mp hgs'_iv).2
          rw [hgiv']
          simp only [g_iv', List.map_cons, List.map_nil]
          rw [hag b hb_iv (by omega) (by omega), hL_W b hb_iv,
              hag c hc_iv (by omega) (by omega), hL_W c hc_iv]
      · intro hiw_s
        by_cases h1 : iw < m
        · rw [(hstep_old (n + iw) (by omega)).1]
          exact hiw_eq h1
        · have heq : m = iw := by omega
          subst heq
          rw [hstep_new.1]
          have hgiw' : gs'[m] = g_iw' := (List.getElem?_eq_some_iff.mp hgs'_iw).2
          rw [hgiw']
          simp only [g_iw', List.map_cons, List.map_nil]
          rw [hag a (by omega) (by omega) (by omega), hL_W a (by omega), hiv_eq hiv_iw]
  obtain ⟨hag_all, _, _⟩ := hmain gs.length (le_refl _)
  have ht1 : gs'.take gs.length = gs' := by rw [← hlen']; exact List.take_length
  have ht2 : gs.take gs.length = gs := List.take_length
  rw [ht1, ht2] at hag_all
  change (gs'.foldl step x0).getD C.output false = (gs.foldl step x0).getD C.output false
  by_cases ho : C.output < n + gs.length
  · exact hag_all C.output ho hout_iv hout_iw
  · rw [List.getD_eq_default _ _ (by rw [foldl_length, hx0, hlen']; omega),
        List.getD_eq_default _ _ (by rw [foldl_length, hx0]; omega)]

end PEqualNP.Outside.L_meta_2920

theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length :=
  PEqualNP.Outside.L_meta_2920.core
