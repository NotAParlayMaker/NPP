import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7630

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7630

theorem PEqualNP.Outside.L_meta_7630 : ∀ (x1 : ℕ) (x2 : Finset ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 ∈ x2, x4 < x1) → PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.any fun (x8 : ℕ) => Decidable.decide (x8 ∈ x2)) x3.gates).length = x3.size ∧ ∀ (x7 : List Bool), x7.length = x1 → (∀ x9 ∈ x2, x7.getD x9 Bool.false = Bool.false) → x6.eval x7 = x3.eval x7 := by
  intro n S C hS hC
  classical
  let P : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g => g.inputs.any fun i => decide (i ∈ S)
  let BIG := n + C.gates.length + 1
  let Good : List Bool → Prop := fun x => x.length = n ∧ ∀ i ∈ S, x.getD i false = false
  let ov : List Bool → Option ℕ → Bool := fun w o => match o with
    | none => false
    | some t => w.getD t false
  have hC2 : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have key : ∀ k ≤ C.gates.length, ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Option ℕ),
      (∀ g ∈ hs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      hs.length + ((C.gates.take k).filter P).length = k ∧ (∀ w t, w < n + k → m w = some t → t < n + hs.length) ∧
      ∀ x, Good x → ∀ w < n + k, (PEqualNP.Outside.L_meta_7630.run C.gates x).getD w false = ov (PEqualNP.Outside.L_meta_7630.run hs x) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => some w, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        cases ht
        simpa using hw
      · intro x hx w hw
        rw [PEqualNP.Outside.L_meta_7630.run_input _ _ _ (by rw [hx.1]; omega)]
        rfl
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      obtain ⟨hop, hlen⟩ := hC2 _ (List.getElem_mem hk')
      have rg : ∀ x, Good x → (PEqualNP.Outside.L_meta_7630.run C.gates x).getD (n + k) false = C.gates[k].op.eval (C.gates[k].inputs.map fun i => if i < n + k then (PEqualNP.Outside.L_meta_7630.run C.gates x).getD i false else false) := by
        intro x hx
        have := PEqualNP.Outside.L_meta_7630.run_gate C.gates x k hk'
        rw [hx.1] at this
        exact this
      have hfil : ((C.gates.take (k + 1)).filter P).length = ((C.gates.take k).filter P).length + if P C.gates[k] = true then 1 else 0 := by
        rw [List.take_succ_eq_append_getElem hk', List.filter_append, List.length_append]
        congr 1
        split_ifs with h <;> simp [h]
      -- reads
      let rd : ℕ → Option ℕ := fun i => if i < n + k then m i else none
      have rd1 : ∀ i t, rd i = some t → t < n + hs.length := by
        intro i t ht
        simp only [rd] at ht
        split_ifs at ht with h
        exact h3 i t h ht
      have rd2 : ∀ x, Good x → ∀ i, (if i < n + k then (PEqualNP.Outside.L_meta_7630.run C.gates x).getD i false else false) = ov (PEqualNP.Outside.L_meta_7630.run hs x) (rd i) := by
        intro x hx i
        simp only [rd]
        split_ifs with h
        · exact h4 x hx i h
        · rfl
      have hszero : ∀ x, Good x → ∀ i ∈ S, (if i < n + k then (PEqualNP.Outside.L_meta_7630.run C.gates x).getD i false else false) = false := by
        intro x hx i hi
        split_ifs with h
        · rw [PEqualNP.Outside.L_meta_7630.run_input _ _ _ (by rw [hx.1]; exact hS i hi)]
          exact hx.2 i hi
        · rfl
      by_cases hP : P C.gates[k] = true
      · -- the gate is deleted
        have fin : ∀ r : Option ℕ, (∀ t, r = some t → t < n + hs.length) → (∀ x, Good x → (PEqualNP.Outside.L_meta_7630.run C.gates x).getD (n + k) false = ov (PEqualNP.Outside.L_meta_7630.run hs x) r) →
            ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Option ℕ),
      (∀ g ∈ hs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      hs.length + ((C.gates.take (k + 1)).filter P).length = k + 1 ∧ (∀ w t, w < n + (k + 1) → m w = some t → t < n + hs.length) ∧
      ∀ x, Good x → ∀ w < n + (k + 1), (PEqualNP.Outside.L_meta_7630.run C.gates x).getD w false = ov (PEqualNP.Outside.L_meta_7630.run hs x) (m w) := by
          intro r hr hval
          refine ⟨hs, Function.update m (n + k) r, h1, by rw [hfil, if_pos hP]; omega, ?_, ?_⟩
          · intro w t hw ht
            by_cases hwe : w = n + k
            · subst hwe; rw [Function.update_self] at ht; exact hr t ht
            · rw [Function.update_of_ne hwe] at ht; exact h3 w t (by omega) ht
          · intro x hx w hw
            by_cases hwe : w = n + k
            · subst hwe; rw [Function.update_self]; exact hval x hx
            · rw [Function.update_of_ne hwe]; exact h4 x hx w (by omega)
        have hex : ∃ i ∈ C.gates[k].inputs, i ∈ S := by simpa [P] using hP
        obtain ⟨i, hi, hiS⟩ := hex
        rcases hop with ho | ho
        · refine fin none (by simp) fun x hx => ?_
          rw [rg x hx, ho]
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, ov, List.all_eq_false, Function.comp, id]
          exact ⟨i, hi, by rw [hszero x hx i hiS]; simp⟩
        · generalize hl : C.gates[k].inputs = l at hlen hi
          rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · cases hi
          · refine fin (rd a) (rd1 a) fun x hx => ?_
            rw [rg x hx, ho, hl, ← rd2 x hx a]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · refine fin (rd b) (rd1 b) fun x hx => ?_
              rw [rg x hx, ho, hl, ← rd2 x hx b]
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, hszero x hx i hiS, Bool.false_or, Bool.or_false]
            · refine fin (rd a) (rd1 a) fun x hx => ?_
              rw [rg x hx, ho, hl, ← rd2 x hx a]
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, hszero x hx i hiS, Bool.or_false]
          · simp at hlen
      · -- the gate is kept
        let f : ℕ → ℕ := fun i => (rd i).getD BIG
        have hhs : hs.length ≤ k := by omega
        refine ⟨hs ++ [⟨C.gates[k].op, C.gates[k].inputs.map f⟩], Function.update m (n + k) (some (n + hs.length)), ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · have : g = ⟨C.gates[k].op, C.gates[k].inputs.map f⟩ := by simpa using hg
            subst this
            exact ⟨hop, by simpa using hlen⟩
        · rw [hfil, if_neg hP, List.length_append]
          simp only [List.length_singleton]
          omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht; cases ht; simp
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht
            omega
        · intro x hx w hw
          by_cases hwe : w = n + k
          · subst hwe
            rw [Function.update_self]
            have hl : n + hs.length = (PEqualNP.Outside.L_meta_7630.run hs x).length := by rw [PEqualNP.Outside.L_meta_7630.run_length, hx.1]
            simp only [ov]
            rw [PEqualNP.Outside.L_meta_7630.run_snoc, hl, PEqualNP.Outside.L_meta_7630.getD_at, rg x hx, List.map_map]
            congr 1
            refine List.map_congr_left fun i _ => ?_
            rw [rd2 x hx i]
            simp only [Function.comp, f]
            cases hr : rd i with
            | none =>
              simp only [Option.getD_none, ov]
              exact (List.getD_eq_default _ _ (by rw [← hl]; simp only [BIG]; omega)).symm
            | some t => simp only [Option.getD_some, ov]
          · rw [Function.update_of_ne hwe, h4 x hx w (by omega)]
            cases hm : m w with
            | none => rfl
            | some t =>
              have := h3 w t (by omega) hm
              simp only [ov]
              rw [PEqualNP.Outside.L_meta_7630.run_prefix _ _ _ _ (by rw [hx.1]; exact this)]
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  rw [List.take_length] at h2
  refine ⟨⟨hs, if C.output < n + C.gates.length then (m C.output).getD BIG else BIG⟩, ?_, h2, fun x hx hxS => ?_⟩
  · intro g hg
    exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
  · have hG : Good x := ⟨hx, hxS⟩
    have hbig : (PEqualNP.Outside.L_meta_7630.run hs x).getD BIG false = false := by
      refine List.getD_eq_default _ _ ?_
      rw [PEqualNP.Outside.L_meta_7630.run_length, hx]
      simp only [BIG]; omega
    change (PEqualNP.Outside.L_meta_7630.run hs x).getD (if C.output < n + C.gates.length then (m C.output).getD BIG else BIG) false = (PEqualNP.Outside.L_meta_7630.run C.gates x).getD C.output false
    by_cases ho : C.output < n + C.gates.length
    · rw [if_pos ho, h4 x hG _ ho]
      cases hm : m C.output with
      | none => exact hbig
      | some t => rfl
    · rw [if_neg ho, hbig, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_7630.run_length, hx]; omega)]
