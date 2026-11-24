import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := ext gs w
  rw [hs]; exact List.getD_append _ _ _ _ h

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := ext gs w
  rw [hs]; simp [hl]

theorem at_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) ∧
    ∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  obtain ⟨q, hq, hql⟩ := ext (gs.take j) w
  have hQ : ((gs.take j).foldl step w).length = w.length + j := by
    rw [hq]; simp [hql]; omega
  obtain ⟨t, ht, _⟩ := ext (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have hf : gs.foldl step w = step ((gs.take j).foldl step w) gs[j] ++ t := by
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons, ht]
  rw [hf]
  constructor
  · rw [← hQ]
    simp [step, List.getD_eq_getElem?_getD]
  · intro i hi
    rw [← hQ] at hi
    have hi2 : i < (step ((gs.take j).foldl step w) gs[j]).length := by simp [step]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi2]
    simp only [step]
    rw [List.getElem?_append_left hi]

theorem loc (n : ℕ) (gs : List Gate) (w : List Bool) (hw : w.length = n) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < n + j) :
    (gs.foldl step w).getD (n + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl step w).getD i false) := by
  obtain ⟨h1, h2⟩ := at_gate gs w j hj
  rw [hw] at h1 h2
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (h2 i (hrb i hi)).symm


theorem loc2 (n : ℕ) (gs : List Gate) (w : List Bool) (hw : w.length = n) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (n + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then (gs.foldl step w).getD i false else false) := by
  obtain ⟨h1, h2⟩ := at_gate gs w j hj
  rw [hw] at h1 h2
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases h : i < n + j
  · rw [if_pos h]; exact (h2 i h).symm
  · rw [if_neg h]
    apply List.getD_eq_default
    rw [fold_len, hw, List.length_take]
    omega

theorem b1 (p q r s : Bool) : ((p || (q && r)) && s) = ((p || q) && ((p || r) && s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem b2 (p q r s : Bool) : ((p || (q && r)) && s) = (((p || r) && s) && (p || q)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem b3 (p q r s : Bool) : ((p && (q || r)) || s) = ((p && q) || ((p && r) || s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem b4 (p q r s : Bool) : ((p && (q || r)) || s) = (((p && r) || s) || (p && q)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

end PEqualNP.Outside.L_meta_2920_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2920_aux in
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
    C.gates.length := by
  rintro n ⟨gs, out⟩ j is iv iw a b c z op1 op2 hops his hiv hiw hj hisj hvw hwj ha1 hb1 ha2 hb2 hc2 hz hzv hnv hnw ho1 ho2
  simp only at his hiv hiw hj hnv hnw ho1 ho2
  refine ⟨?_, by simp⟩
  obtain ⟨hisl, his⟩ := List.getElem?_eq_some_iff.mp his
  obtain ⟨hivl, hiv⟩ := List.getElem?_eq_some_iff.mp hiv
  obtain ⟨hiwl, hiw⟩ := List.getElem?_eq_some_iff.mp hiw
  have hjl : j < gs.length := by
    rcases hj with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  have hj2 : gs[j] = { op := op1, inputs := [n + is, n + iw] } ∨ gs[j] = { op := op1, inputs := [n + iw, n + is] } := by
    rcases hj with h | h
    · exact Or.inl (List.getElem?_eq_some_iff.mp h).2
    · exact Or.inr (List.getElem?_eq_some_iff.mp h).2
  obtain ⟨G, hG⟩ : ∃ G, G = ((gs.set iv { op := op1, inputs := [b, c] }).set iw { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] } := ⟨_, rfl⟩
  simp only
  rw [← hG]
  have hlen : G.length = gs.length := by rw [hG]; simp
  have hGj : ∀ (h : j < G.length), G[j] = { op := op1, inputs := [n + iw, z] } := by
    intro h; subst hG; simp
  have hGw : ∀ (h : iw < G.length), G[iw] = { op := op2, inputs := [a, n + iv] } := by
    intro h; subst hG
    rw [List.getElem_set_of_ne (by omega)]
    simp
  have hGv : ∀ (h : iv < G.length), G[iv] = { op := op1, inputs := [b, c] } := by
    intro h; subst hG
    rw [List.getElem_set_of_ne (by omega), List.getElem_set_of_ne (by omega)]
    simp
  have hGo : ∀ k (h : k < G.length) (h2 : k < gs.length), k ≠ j → k ≠ iw → k ≠ iv → G[k] = gs[k] := by
    intro k h h2 h3 h4 h5; subst hG
    rw [List.getElem_set_of_ne (Ne.symm h3), List.getElem_set_of_ne (Ne.symm h4), List.getElem_set_of_ne (Ne.symm h5)]
  funext x
  show (G.foldl step (List.ofFn x)).getD out false = (gs.foldl step (List.ofFn x)).getD out false
  have hx : (List.ofFn x).length = n := by simp
  have hL := fun k hk => loc2 n gs (List.ofFn x) hx k hk
  have hM := fun k hk => loc2 n G (List.ofFn x) hx k hk
  have hl1 := fold_len gs (List.ofFn x)
  have hl2 := fold_len G (List.ofFn x)
  have hf1 := fold_get gs (List.ofFn x)
  have hf2 := fold_get G (List.ofFn x)
  rw [hx] at hl1 hl2 hf1 hf2
  generalize gs.foldl step (List.ofFn x) = W at hL hl1 hf1 ⊢
  generalize G.foldl step (List.ofFn x) = V at hM hl2 hf2 ⊢
  have key : ∀ i, i ≠ n + iv → i ≠ n + iw → V.getD i false = W.getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hne1 hne2
      rcases lt_or_ge i n with hin | hin
      · rw [hf1 i hin, hf2 i hin]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin
        by_cases hkl : k < gs.length
        · by_cases hkj : k = j
          · subst hkj
            have es := hL is hisl
            have ev := hL iv hivl
            have ew := hL iw hiwl
            have ej := hL k hkl
            have fv := hM iv (by omega)
            have fw := hM iw (by omega)
            have fj := hM k (by omega)
            rw [his] at es
            rw [hiv] at ev
            rw [hiw] at ew
            rw [hGv (by omega)] at fv
            rw [hGw (by omega)] at fw
            rw [hGj (by omega)] at fj
            have ia := ih a (by omega) (by omega) (by omega)
            have ib := ih b (by omega) (by omega) (by omega)
            have ic := ih c (by omega) (by omega) (by omega)
            have iz := ih z (by omega) hzv (by omega)
            have t1 : n + iv < n + iw := by omega
            have t2 : n + iw < n + k := by omega
            have t3 : n + is < n + k := by omega
            have t4 : z < n + k := by omega
            have t5 : a < n + iw := by omega
            rcases hops with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rcases hj2 with h | h
              · rw [h] at ej
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false, if_true, ha1, hb1, ha2, hb2, hc2, hz, t1, t2, t3, t4, t5] at es ev ew ej fv fw fj
                rw [fj, fw, fv, ej, es, ew, ev, ia, ib, ic, iz]
                exact b1 _ _ _ _
              · rw [h] at ej
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false, if_true, ha1, hb1, ha2, hb2, hc2, hz, t1, t2, t3, t4, t5] at es ev ew ej fv fw fj
                rw [fj, fw, fv, ej, es, ew, ev, ia, ib, ic, iz]
                exact b2 _ _ _ _
            · rcases hj2 with h | h
              · rw [h] at ej
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false, if_true, ha1, hb1, ha2, hb2, hc2, hz, t1, t2, t3, t4, t5] at es ev ew ej fv fw fj
                rw [fj, fw, fv, ej, es, ew, ev, ia, ib, ic, iz]
                exact b3 _ _ _ _
              · rw [h] at ej
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false, if_true, ha1, hb1, ha2, hb2, hc2, hz, t1, t2, t3, t4, t5] at es ev ew ej fv fw fj
                rw [fj, fw, fv, ej, es, ew, ev, ia, ib, ic, iz]
                exact b4 _ _ _ _
          · have hk1 : k ≠ iw := by omega
            have hk2 : k ≠ iv := by omega
            rw [hM k (by omega), hL k hkl, hGo k (by omega) hkl hkj hk1 hk2]
            congr 1
            apply List.map_congr_left
            intro i hi
            by_cases hik : i < n + k
            · rw [if_pos hik, if_pos hik]
              apply ih i hik
              · intro h
                subst h
                exact hnv k gs[k] (List.getElem?_eq_getElem hkl) hk1 hi
              · intro h
                subst h
                exact hnw k gs[k] (List.getElem?_eq_getElem hkl) hkj hi
            · rw [if_neg hik, if_neg hik]
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  exact key out ho1 ho2
