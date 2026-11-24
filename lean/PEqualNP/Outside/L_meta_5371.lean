import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5371

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

private def evalGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α)
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private theorem getD_append_snoc_self {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

private theorem getD_eq_default_of_le {α : Type} (l : List α) (i : ℕ) (d : α)
    (hi : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

private theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD, hi]

private theorem evalGates_length (gs : List Gate) (x : List Bool) :
    (evalGates gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem evalGates_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    evalGates (gs₁ ++ gs₂) x = evalGates gs₂ (evalGates gs₁ x) := by
  simp [evalGates, List.foldl_append]

private theorem evalGates_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    evalGates (gs ++ [g]) x =
      evalGates gs x ++ [g.op.eval (g.inputs.map fun i => (evalGates gs x).getD i false)] := by
  rw [evalGates_append]
  rfl

private theorem evalGates_getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (evalGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hi', getD_append_left _ _ _ _ hi]

private theorem gateAt_append_self (pre : List Gate) (g : Gate) (rest : List Gate) :
    gateAt ⟨pre ++ g :: rest, 0⟩ pre.length = g := by
  simp [gateAt, List.getD]

private theorem gateAt_append_left (acc : List Gate) (g : Gate) (j : ℕ)
    (hj : j < acc.length) :
    gateAt ⟨acc ++ [g], 0⟩ j = gateAt ⟨acc, 0⟩ j := by
  unfold gateAt
  exact getD_append_left acc [g] j ⟨GateOp.or, []⟩ hj

private theorem gateAt_snoc_self (acc : List Gate) (g : Gate) :
    gateAt ⟨acc ++ [g], 0⟩ acc.length = g := by
  unfold gateAt
  exact getD_append_snoc_self acc g ⟨GateOp.or, []⟩

private theorem inputs_eq_pair (l : List ℕ) (hl : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all [List.getD]

private def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

private def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

private theorem branch1_vars (op : GateOp) (za zb : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (h1 : ((isAndOp op && (za || zb)) || (isOrOp op && za && zb)) = true) :
    (op = GateOp.and ∧ (za = true ∨ zb = true)) ∨ (op = GateOp.or ∧ za = true ∧ zb = true) := by
  rcases hop with rfl | rfl <;> cases za <;> cases zb <;> simp_all [isAndOp, isOrOp]

private theorem branch2_vars (op : GateOp) (za zb : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (h2 : (isOrOp op && za && !zb) = true) :
    op = GateOp.or ∧ za = true ∧ zb = false := by
  rcases hop with rfl | rfl <;> cases za <;> cases zb <;> simp_all [isOrOp]

private theorem branch3_vars (op : GateOp) (za zb : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (h3 : (isOrOp op && !za && zb) = true) :
    op = GateOp.or ∧ za = false ∧ zb = true := by
  rcases hop with rfl | rfl <;> cases za <;> cases zb <;> simp_all [isOrOp]

private theorem else_branch_false (op : GateOp) (za zb : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (h1 : ¬((isAndOp op && (za || zb)) || (isOrOp op && za && zb)) = true)
    (h2 : ¬(isOrOp op && za && !zb) = true)
    (h3 : ¬(isOrOp op && !za && zb) = true) :
    za = false ∧ zb = false := by
  rcases hop with rfl | rfl <;> cases za <;> cases zb <;> simp_all [isAndOp, isOrOp]

private def compactAux (n idx : ℕ) (Z : ℕ → Bool) (R : ℕ → ℕ) (acc : List Gate) :
    List Gate → List Gate × (ℕ → Bool) × (ℕ → ℕ)
  | [] => (acc, Z, R)
  | g :: rest =>
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if (isAndOp g.op && (Z a || Z b)) || (isOrOp g.op && Z a && Z b) then
      compactAux n (idx + 1) (fun w => if w = n + idx then true else Z w) R acc rest
    else if isOrOp g.op && Z a && !Z b then
      compactAux n (idx + 1) (fun w => if w = n + idx then false else Z w)
        (fun w => if w = n + idx then R b else R w) acc rest
    else if isOrOp g.op && !Z a && Z b then
      compactAux n (idx + 1) (fun w => if w = n + idx then false else Z w)
        (fun w => if w = n + idx then R a else R w) acc rest
    else
      let g' : Gate := ⟨g.op, [R a, R b]⟩
      compactAux n (idx + 1) (fun w => if w = n + idx then false else Z w)
        (fun w => if w = n + idx then n + acc.length else R w) (acc ++ [g']) rest

private theorem compactAux_len_le (n idx : ℕ) (Z : ℕ → Bool) (R : ℕ → ℕ) (acc rest : List Gate) :
    (compactAux n idx Z R acc rest).1.length ≤ acc.length + rest.length := by
  induction rest generalizing idx Z R acc with
  | nil => simp [compactAux]
  | cons g rest ih =>
    simp only [compactAux]
    split_ifs <;>
      exact le_trans (ih _ _ _ _)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

private theorem compactAux_inv (n : ℕ) (x2 : Fin n) (pre rest acc : List Gate)
    (Z : ℕ → Bool) (R : ℕ → ℕ)
    (hao2 : IsAO2 n ⟨pre ++ rest, 0⟩)
    (hacc_ao2 : IsAO2 n ⟨acc, 0⟩)
    (hzx2 : Z x2.val = true)
    (hinv : ∀ (x9 : Fin n → Bool) (w : ℕ), w < n + pre.length →
      (Z w = true →
        (evalGates pre (List.ofFn (Function.update x9 x2 false))).getD w false = false) ∧
      (Z w = false →
        R w < n + acc.length ∧
        (evalGates acc (List.ofFn x9)).getD (R w) false =
          (evalGates pre (List.ofFn (Function.update x9 x2 false))).getD w false)) :
    let res := compactAux n pre.length Z R acc rest
    IsAO2 n ⟨res.1, 0⟩ ∧
    res.2.1 x2.val = true ∧
    ∀ (x9 : Fin n → Bool) (w : ℕ), w < n + (pre ++ rest).length →
      (res.2.1 w = true →
        (evalGates (pre ++ rest) (List.ofFn (Function.update x9 x2 false))).getD w false = false) ∧
      (res.2.1 w = false →
        res.2.2 w < n + res.1.length ∧
        (evalGates res.1 (List.ofFn x9)).getD (res.2.2 w) false =
          (evalGates (pre ++ rest) (List.ofFn (Function.update x9 x2 false))).getD w false) := by
  induction rest generalizing pre acc Z R with
  | nil =>
    simp only [compactAux, List.append_nil]
    exact ⟨hacc_ao2, hzx2, hinv⟩
  | cons g rest ih =>
    have hao2' : IsAO2 n ⟨(pre ++ [g]) ++ rest, 0⟩ := by
      simpa [List.append_assoc] using hao2
    have hg_mem : g ∈ (⟨pre ++ g :: rest, 0⟩ : Circuit).gates := by simp
    have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := hao2.1 g hg_mem
    have hg_len : g.inputs.length = 2 := hao2.2.2 g hg_mem
    have hg_rb : ∀ w ∈ g.inputs, w < n + pre.length := by
      intro w hw
      have hrb := hao2.2.1 pre.length (by simp) w
      rw [gateAt_append_self] at hrb
      exact hrb hw
    set a := g.inputs.getD 0 0
    set b := g.inputs.getD 1 0
    have hg_inputs : g.inputs = [a, b] := inputs_eq_pair g.inputs hg_len
    have ha_lt : a < n + pre.length := hg_rb a (by rw [hg_inputs]; simp)
    have hb_lt : b < n + pre.length := hg_rb b (by rw [hg_inputs]; simp)
    have hx2_ne : x2.val ≠ n + pre.length := by have := x2.isLt; omega
    have eval_orig_step : ∀ (x9 : Fin n → Bool),
        (evalGates (pre ++ [g]) (List.ofFn (Function.update x9 x2 false))).getD
          (n + pre.length) false =
        g.op.eval [(evalGates pre (List.ofFn (Function.update x9 x2 false))).getD a false,
                   (evalGates pre (List.ofFn (Function.update x9 x2 false))).getD b false] := by
      intro x9
      have hlen_pre : (evalGates pre (List.ofFn (Function.update x9 x2 false))).length =
          n + pre.length := by
        rw [evalGates_length, List.length_ofFn]
      rw [evalGates_snoc, ← hlen_pre, getD_append_snoc_self]
      congr 1
      conv_lhs => rw [hg_inputs]
      simp [a, b]
    have eval_orig_old : ∀ (x9 : Fin n → Bool) (w : ℕ), w < n + pre.length →
        (evalGates (pre ++ [g]) (List.ofFn (Function.update x9 x2 false))).getD w false =
        (evalGates pre (List.ofFn (Function.update x9 x2 false))).getD w false := by
      intro x9 w hw
      rw [evalGates_append]
      apply evalGates_getD_prefix
      rw [evalGates_length, List.length_ofFn]
      exact hw
    dsimp only [compactAux]
    split_ifs with h1 h2 h3
    · have h1v := branch1_vars g.op (Z a) (Z b) hg_op h1
      have hval_f : ∀ x9, (evalGates (pre ++ [g]) (List.ofFn (Function.update x9 x2 false))).getD
          (n + pre.length) false = false := by
        intro x9
        rw [eval_orig_step]
        rcases h1v with ⟨hop, hZa | hZb⟩ | ⟨hop, hZa, hZb⟩
        · have ha_f := (hinv x9 a ha_lt).1 hZa
          rw [hop, ha_f]
          simp [GateOp.eval]
        · have hb_f := (hinv x9 b hb_lt).1 hZb
          rw [hop, hb_f]
          simp [GateOp.eval]
        · have ha_f := (hinv x9 a ha_lt).1 hZa
          have hb_f := (hinv x9 b hb_lt).1 hZb
          rw [hop, ha_f, hb_f]
          simp [GateOp.eval]
      have hz' : (if x2.val = n + pre.length then true else Z x2.val) = true := by
        simp [hx2_ne, hzx2]
      have hres := ih (pre ++ [g]) acc (fun w => if w = n + pre.length then true else Z w) R
        hao2' hacc_ao2 hz' (by
          intro x9 w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hw
          by_cases hweq : w = n + pre.length
          · subst hweq
            exact ⟨fun _ => hval_f x9, fun h => by simp at h⟩
          · have hwlt : w < n + pre.length := by omega
            rw [eval_orig_old x9 w hwlt]
            simp only [hweq, ↓reduceIte]
            exact hinv x9 w hwlt)
      simpa [List.append_assoc, List.length_append, List.length_cons, List.length_nil] using hres
    · rcases branch2_vars g.op (Z a) (Z b) hg_op h2 with ⟨hop, hZa, hZb⟩
      have ha_f : ∀ x9, (evalGates pre (List.ofFn (Function.update x9 x2 false))).getD a false =
          false := fun x9 => (hinv x9 a ha_lt).1 hZa
      have hb_inv := fun x9 => (hinv x9 b hb_lt).2 hZb
      have hz' : (if x2.val = n + pre.length then false else Z x2.val) = true := by
        simp [hx2_ne, hzx2]
      have hres := ih (pre ++ [g]) acc (fun w => if w = n + pre.length then false else Z w)
        (fun w => if w = n + pre.length then R b else R w) hao2' hacc_ao2 hz' (by
          intro x9 w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hw
          by_cases hweq : w = n + pre.length
          · subst hweq
            refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [↓reduceIte]
            refine ⟨(hb_inv x9).1, ?_⟩
            rw [eval_orig_step, hop, ha_f]
            simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.false_or,
              Bool.or_false]
            exact (hb_inv x9).2
          · have hwlt : w < n + pre.length := by omega
            rw [eval_orig_old x9 w hwlt]
            simp only [hweq, ↓reduceIte]
            exact hinv x9 w hwlt)
      simpa [List.append_assoc, List.length_append, List.length_cons, List.length_nil, a, b] using
        hres
    · rcases branch3_vars g.op (Z a) (Z b) hg_op h3 with ⟨hop, hZa, hZb⟩
      have ha_inv := fun x9 => (hinv x9 a ha_lt).2 hZa
      have hb_f : ∀ x9, (evalGates pre (List.ofFn (Function.update x9 x2 false))).getD b false =
          false := fun x9 => (hinv x9 b hb_lt).1 hZb
      have hz' : (if x2.val = n + pre.length then false else Z x2.val) = true := by
        simp [hx2_ne, hzx2]
      have hres := ih (pre ++ [g]) acc (fun w => if w = n + pre.length then false else Z w)
        (fun w => if w = n + pre.length then R a else R w) hao2' hacc_ao2 hz' (by
          intro x9 w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hw
          by_cases hweq : w = n + pre.length
          · subst hweq
            refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [↓reduceIte]
            refine ⟨(ha_inv x9).1, ?_⟩
            rw [eval_orig_step, hop, hb_f]
            simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact (ha_inv x9).2
          · have hwlt : w < n + pre.length := by omega
            rw [eval_orig_old x9 w hwlt]
            simp only [hweq, ↓reduceIte]
            exact hinv x9 w hwlt)
      simpa [List.append_assoc, List.length_append, List.length_cons, List.length_nil, a, b] using
        hres
    · rcases else_branch_false g.op (Z a) (Z b) hg_op h1 h2 h3 with ⟨hZa, hZb⟩
      let g' : Gate := ⟨g.op, [R a, R b]⟩
      have ha_inv := fun x9 => (hinv x9 a ha_lt).2 hZa
      have hb_inv := fun x9 => (hinv x9 b hb_lt).2 hZb
      have ha_Rlt : R a < n + acc.length := (ha_inv (fun _ => false)).1
      have hb_Rlt : R b < n + acc.length := (hb_inv (fun _ => false)).1
      have hacc_ao2' : IsAO2 n ⟨acc ++ [g'], 0⟩ := by
        refine ⟨?_, ?_, ?_⟩
        · intro g1 hg1
          simp only [List.mem_append, List.mem_singleton] at hg1
          rcases hg1 with hg1 | rfl
          · exact hacc_ao2.1 g1 hg1
          · exact hg_op
        · intro j hj w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hjlt : j < acc.length
          · rw [gateAt_append_left _ _ _ hjlt] at hw
            exact hacc_ao2.2.1 j hjlt w hw
          · have hjeq : j = acc.length := by omega
            subst hjeq
            rw [gateAt_snoc_self] at hw
            simp only [g', List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl <;> assumption
        · intro g1 hg1
          simp only [List.mem_append, List.mem_singleton] at hg1
          rcases hg1 with hg1 | rfl
          · exact hacc_ao2.2.2 g1 hg1
          · simp [g']
      have hz' : (if x2.val = n + pre.length then false else Z x2.val) = true := by
        simp [hx2_ne, hzx2]
      have hres := ih (pre ++ [g]) (acc ++ [g'])
        (fun w => if w = n + pre.length then false else Z w)
        (fun w => if w = n + pre.length then n + acc.length else R w)
        hao2' hacc_ao2' hz' (by
          intro x9 w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hw
          have eval_new_old : ∀ u, u < n + acc.length →
              (evalGates (acc ++ [g']) (List.ofFn x9)).getD u false =
              (evalGates acc (List.ofFn x9)).getD u false := by
            intro u hu
            rw [evalGates_append]
            apply evalGates_getD_prefix
            rw [evalGates_length, List.length_ofFn]
            exact hu
          have eval_new_self :
              (evalGates (acc ++ [g']) (List.ofFn x9)).getD (n + acc.length) false =
              g.op.eval [(evalGates acc (List.ofFn x9)).getD (R a) false,
                         (evalGates acc (List.ofFn x9)).getD (R b) false] := by
            have hlen_acc : (evalGates acc (List.ofFn x9)).length = n + acc.length := by
              rw [evalGates_length, List.length_ofFn]
            rw [evalGates_snoc, ← hlen_acc, getD_append_snoc_self]
            simp [g']
          by_cases hweq : w = n + pre.length
          · subst hweq
            refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil]
            refine ⟨by omega, ?_⟩
            rw [eval_new_self, eval_orig_step, (ha_inv x9).2, (hb_inv x9).2]
          · have hwlt : w < n + pre.length := by omega
            rw [eval_orig_old x9 w hwlt]
            simp only [hweq, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
            refine ⟨(hinv x9 w hwlt).1, fun hzw => ?_⟩
            have hsub := (hinv x9 w hwlt).2 hzw
            refine ⟨by omega, ?_⟩
            rw [eval_new_old (R w) hsub.1, hsub.2])
      simpa [List.append_assoc, List.length_append, List.length_cons, List.length_nil, g', a, b] using
        hres

private theorem compactAux_full_no_x2 (n : ℕ) (x2 : Fin n) (idx : ℕ)
    (Z : ℕ → Bool) (R : ℕ → ℕ) (acc rest : List Gate)
    (hao : ∀ g ∈ rest, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hzx2 : Z x2.val = true)
    (hfull : (compactAux n idx Z R acc rest).1.length = acc.length + rest.length) :
    ∀ g ∈ rest, x2.val ∉ g.inputs := by
  induction rest generalizing idx Z R acc with
  | nil => simp
  | cons g rest ih =>
    have hg := hao g (by simp)
    have hrest : ∀ g' ∈ rest, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
      fun g' hg' => hao g' (by simp [hg'])
    have hx2_ne : x2.val ≠ n + idx := by have := x2.isLt; omega
    dsimp only [compactAux] at hfull
    split_ifs at hfull with h1 h2 h3
    · have hle := compactAux_len_le n (idx + 1)
          (fun w => if w = n + idx then true else Z w) R acc rest
      simp only [List.length_cons] at hfull
      omega
    · have hle := compactAux_len_le n (idx + 1)
          (fun w => if w = n + idx then false else Z w)
          (fun w => if w = n + idx then R (g.inputs.getD 1 0) else R w) acc rest
      simp only [List.length_cons] at hfull
      omega
    · have hle := compactAux_len_le n (idx + 1)
          (fun w => if w = n + idx then false else Z w)
          (fun w => if w = n + idx then R (g.inputs.getD 0 0) else R w) acc rest
      simp only [List.length_cons] at hfull
      omega
    · have hZab := else_branch_false g.op (Z (g.inputs.getD 0 0)) (Z (g.inputs.getD 1 0))
          hg.1 h1 h2 h3
      have hz' : (if x2.val = n + idx then false else Z x2.val) = true := by
        simp [hx2_ne, hzx2]
      let g' : Gate := ⟨g.op, [R (g.inputs.getD 0 0), R (g.inputs.getD 1 0)]⟩
      have hfull' : (compactAux n (idx + 1) (fun w => if w = n + idx then false else Z w)
          (fun w => if w = n + idx then n + acc.length else R w)
          (acc ++ [g']) rest).1.length = (acc ++ [g']).length + rest.length := by
        dsimp only [g']
        exact Eq.trans hfull (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have ih_res := ih (idx + 1) _ _ _ hrest hz' hfull'
      intro g1 hg1
      simp only [List.mem_cons] at hg1
      rcases hg1 with rfl | hg1
      · have hg_inputs := inputs_eq_pair g1.inputs hg.2
        rw [hg_inputs]
        intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with haeq | hbeq
        · rw [← haeq, hzx2] at hZab
          cases hZab.1
        · rw [← hbeq, hzx2] at hZab
          cases hZab.2
      · exact ih_res g1 hg1

private theorem evalGates_eq_of_not_mem (gs : List Gate) (k : ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hw : ∀ u, u ≠ k → w₁.getD u false = w₂.getD u false)
    (hgs : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ u, u ≠ k → (evalGates gs w₁).getD u false = (evalGates gs w₂).getD u false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hw
  | cons g gs ih =>
    have hg_not : k ∉ g.inputs := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, k ∉ g'.inputs := fun g' hg' => hgs g' (by simp [hg'])
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hw
      intro hik
      subst hik
      exact hg_not hi
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro u huk
      by_cases hu : u < w₁.length
      · have hu2 : u < w₂.length := hlen ▸ hu
        rw [getD_append_left _ _ _ _ hu, getD_append_left _ _ _ _ hu2]
        exact hw u huk
      · by_cases hueq : u = w₁.length
        · subst hueq
          rw [getD_append_snoc_self, hlen, getD_append_snoc_self]
        · have hu1 : (w₁ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)]).length ≤ u := by
            simp; omega
          have hu2 : (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)]).length ≤ u := by
            simp; omega
          rw [getD_eq_default_of_le _ _ _ hu1, getD_eq_default_of_le _ _ _ hu2]
    · exact hgs'

private theorem main_proof :
    ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : Circuit),
      x4.size = x3 → IsAO2 x1 x4 →
      (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool),
        x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠
        x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) →
      ∃ (x8 : Circuit), IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧
        ((∃ (x9 : Fin x1 → Bool),
          x4.eval (List.ofFn x9) ≠
          x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧
        ∀ (x9 : Fin x1 → Bool),
          x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) := by
  intro x1 x2 x3 x4 _ hAO2 hnonconst
  let Z0 : ℕ → Bool := fun w => decide (w = x2.val)
  let R0 : ℕ → ℕ := id
  let res := compactAux x1 0 Z0 R0 [] x4.gates
  let x8 : Circuit := { gates := res.1, output := res.2.2 x4.output }
  have hAO2_pre : IsAO2 x1 ⟨[] ++ x4.gates, 0⟩ := by
    refine ⟨hAO2.1, hAO2.2.1, hAO2.2.2⟩
  have hacc0 : IsAO2 x1 ⟨[], 0⟩ := by
    refine ⟨by simp [AndOrOnly], by simp [ReadsBack], by simp⟩
  have hzx2_0 : Z0 x2.val = true := by simp [Z0]
  have hinv0 : ∀ (x9 : Fin x1 → Bool) (w : ℕ), w < x1 + ([] : List Gate).length →
      (Z0 w = true →
        (evalGates [] (List.ofFn (Function.update x9 x2 false))).getD w false = false) ∧
      (Z0 w = false →
        R0 w < x1 + ([] : List Gate).length ∧
        (evalGates [] (List.ofFn x9)).getD (R0 w) false =
          (evalGates [] (List.ofFn (Function.update x9 x2 false))).getD w false) := by
    intro x9 w hw
    simp only [List.length_nil, add_zero] at hw
    refine ⟨fun hzw => ?_, fun hzw => ?_⟩
    · have hweq : w = x2.val := of_decide_eq_true hzw
      subst hweq
      simp [evalGates]
    · have hwne : w ≠ x2.val := of_decide_eq_false hzw
      refine ⟨hw, ?_⟩
      simp only [evalGates, List.foldl_nil, R0, id_eq]
      rw [getD_ofFn x9 w hw, getD_ofFn (Function.update x9 x2 false) w hw]
      have hfin : (⟨w, hw⟩ : Fin x1) ≠ x2 := fun h => hwne (congrArg Fin.val h)
      simp [Function.update_of_ne hfin]
  have hmain := compactAux_inv x1 x2 [] x4.gates [] Z0 R0 hAO2_pre hacc0 hzx2_0 hinv0
  simp only [List.length_nil, List.nil_append] at hmain
  rcases hmain with ⟨hres_ao2, hres_zx2, hres_inv⟩
  have hx8_ao2 : IsAO2 x1 x8 := ⟨hres_ao2.1, hres_ao2.2.1, hres_ao2.2.2⟩
  have hx8_le : x8.size ≤ x4.size := by
    have hle := compactAux_len_le x1 0 Z0 R0 [] x4.gates
    simpa [x8, Circuit.size] using hle
  rcases hnonconst with ⟨y1, y2, hy⟩
  have hout_lt : x4.output < x1 + x4.gates.length := by
    by_contra hge
    have hle : x1 + x4.gates.length ≤ x4.output := Nat.le_of_not_lt hge
    have h1 : x4.eval (List.ofFn (Function.update y1 x2 false)) = false := by
      simp only [Circuit.eval]
      apply getD_eq_default_of_le
      change (evalGates x4.gates (List.ofFn (Function.update y1 x2 false))).length ≤ x4.output
      rw [evalGates_length, List.length_ofFn]
      exact hle
    have h2 : x4.eval (List.ofFn (Function.update y2 x2 false)) = false := by
      simp only [Circuit.eval]
      apply getD_eq_default_of_le
      change (evalGates x4.gates (List.ofFn (Function.update y2 x2 false))).length ≤ x4.output
      rw [evalGates_length, List.length_ofFn]
      exact hle
    exact hy (h1.trans h2.symm)
  have hout_z : res.2.1 x4.output = false := by
    by_cases hzt : res.2.1 x4.output = true
    · have h1 : x4.eval (List.ofFn (Function.update y1 x2 false)) = false :=
        (hres_inv y1 x4.output hout_lt).1 hzt
      have h2 : x4.eval (List.ofFn (Function.update y2 x2 false)) = false :=
        (hres_inv y2 x4.output hout_lt).1 hzt
      exact False.elim (hy (h1.trans h2.symm))
    · cases hzb : res.2.1 x4.output
      · rfl
      · exact False.elim (hzt hzb)
  refine ⟨x8, hx8_ao2, hx8_le, ?_, ?_⟩
  · intro hdiff
    rcases hdiff with ⟨x9, hx9⟩
    by_contra hnotlt
    have heq : x8.size = x4.size := Nat.le_antisymm hx8_le (Nat.le_of_not_lt hnotlt)
    have hfull : res.1.length = ([] : List Gate).length + x4.gates.length := by
      simpa [x8, Circuit.size] using heq
    have hno_x2 : ∀ g ∈ x4.gates, x2.val ∉ g.inputs :=
      compactAux_full_no_x2 x1 x2 0 Z0 R0 [] x4.gates
        (fun g hg => ⟨hAO2.1 g hg, hAO2.2.2 g hg⟩) hzx2_0 hfull
    have hout_ne : x4.output ≠ x2.val := by
      intro heqo
      rw [heqo, hres_zx2] at hout_z
      cases hout_z
    have hsame : x4.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 false)) := by
      simp only [Circuit.eval]
      apply evalGates_eq_of_not_mem x4.gates x2.val
      · simp
      · intro u huk
        by_cases hu : u < x1
        · rw [getD_ofFn x9 u hu, getD_ofFn (Function.update x9 x2 false) u hu]
          have hfin : (⟨u, hu⟩ : Fin x1) ≠ x2 := fun h => huk (congrArg Fin.val h)
          simp [Function.update_of_ne hfin]
        · have hu1 : (List.ofFn x9).length ≤ u := by simp; omega
          have hu2 : (List.ofFn (Function.update x9 x2 false)).length ≤ u := by simp; omega
          rw [getD_eq_default_of_le _ _ _ hu1, getD_eq_default_of_le _ _ _ hu2]
      · exact hno_x2
      · exact hout_ne
    exact hx9 hsame
  · intro x9
    exact (hres_inv x9 x4.output hout_lt).2 hout_z |>.2

end PEqualNP.Outside.L_meta_5371

theorem PEqualNP.Outside.L_meta_5371 : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) := by
  exact PEqualNP.Outside.L_meta_5371.main_proof
