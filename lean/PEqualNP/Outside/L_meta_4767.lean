import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4767

open PEqualNP.CircuitLowerBounds

section BasicEval

private def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private def runWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl wireStep w

private lemma wires_eq_runWires (gs : List Gate) (out : ℕ) (w : List Bool) :
    Circuit.wires ⟨gs, out⟩ w = runWires gs w := rfl

private lemma runWires_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runWires (g :: gs) w = runWires gs (wireStep w g) := rfl

private lemma runWires_append (gs hs : List Gate) (w : List Bool) :
    runWires (gs ++ hs) w = runWires hs (runWires gs w) := by
  simp [runWires, List.foldl_append]

private lemma runWires_length (gs : List Gate) (w : List Bool) :
    (runWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runWires]
  | cons g gs ih =>
    rw [runWires_cons, ih]
    simp [wireStep]
    omega

private lemma runWires_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (runWires gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [runWires_cons, ih _ (by simp [wireStep]; omega)]
    exact List.getD_append _ _ false i hi

private lemma runWires_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (runWires gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map (fun i => (runWires (gs.take j) w).getD i false)) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  conv_lhs => rw [hsplit, runWires_append, runWires_cons]
  set pre := runWires (gs.take j) w
  have hpre : pre.length = w.length + j := by
    rw [runWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [runWires_getD_lt _ _ _ (by simp [wireStep, hpre])]
  rw [wireStep, ← hpre, List.getD_append_right _ _ false pre.length (le_refl _)]
  simp

private def wval {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (runWires gs (List.ofFn x)).getD i false

private lemma wval_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval gs x i = x ⟨i, hi⟩ := by
  unfold wval
  rw [runWires_getD_lt _ _ _ (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

private lemma wval_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    wval gs x i = false := by
  unfold wval
  apply List.getD_eq_default
  rw [runWires_length, List.length_ofFn]
  exact hi

private def MonoGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private def Wf (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, MonoGate g) ∧
  (∀ (j : ℕ) (hj : j < gs.length), ∀ a ∈ gs[j].inputs, a < n + j)

private lemma wval_gate_wf {n : ℕ} {gs : List Gate} (hwf : Wf n gs)
    (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    wval gs x (n + j) = gs[j].op.eval (gs[j].inputs.map (wval gs x)) := by
  unfold wval
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h1 := runWires_getD_gate gs (List.ofFn x) j hj
  rw [hlen] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < n + j := hwf.2 j hj a ha
  have hpre : (runWires (gs.take j) (List.ofFn x)).length = n + j := by
    rw [runWires_length, hlen, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  have h2 := runWires_getD_lt (gs.drop j) (runWires (gs.take j) (List.ofFn x)) a (by rw [hpre]; exact halt)
  conv_rhs => rw [hsplit, runWires_append, h2]

private lemma eval_mono_op {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ {l1 l2 : List Bool}, List.Forall₂ (fun a b => a ≤ b) l1 l2 → op.eval l1 ≤ op.eval l2 := by
  intro l1 l2 h
  rcases hop with rfl | rfl
  · induction h with
    | nil => exact le_refl _
    | @cons a b _ _ h1 _ ih =>
      simp only [GateOp.eval, List.all_cons] at ih ⊢
      cases a <;> cases b
      · simp
      · simp
      · exact absurd (h1 rfl) (by decide)
      · simpa using ih
  · induction h with
    | nil => exact le_refl _
    | @cons a b _ _ h1 _ ih =>
      simp only [GateOp.eval, List.any_cons] at ih ⊢
      cases a <;> cases b
      · simpa using ih
      · simp
      · exact absurd (h1 rfl) (by decide)
      · simp

private lemma map_forall₂_le {α : Type*} {f g : α → Bool} {l : List α}
    (h : ∀ a ∈ l, f a ≤ g a) : List.Forall₂ (fun a b => a ≤ b) (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private lemma wval_mono {n : ℕ} {gs : List Gate} (hwf : Wf n gs)
    {x y : Fin n → Bool} (hxy : ∀ k, x k ≤ y k) :
    ∀ w, wval gs x w ≤ wval gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [wval_input gs x w hlt, wval_input gs y w hlt]
      exact hxy ⟨w, hlt⟩
    · by_cases hge : n + gs.length ≤ w
      · rw [wval_ge gs x w hge, wval_ge gs y w hge]
      · have hj : w - n < gs.length := by omega
        have hw : w = n + (w - n) := by omega
        rw [hw, wval_gate_wf hwf x (w - n) hj, wval_gate_wf hwf y (w - n) hj]
        apply eval_mono_op (hwf.1 _ (List.getElem_mem hj)).1
        apply map_forall₂_le
        intro a ha
        exact ih a (by have := hwf.2 (w - n) hj a ha; omega)

private lemma wval_mono_true {n : ℕ} {gs : List Gate} (hwf : Wf n gs)
    {x y : Fin n → Bool} (hxy : ∀ k, x k = true → y k = true) {w : ℕ}
    (hx : wval gs x w = true) : wval gs y w = true := by
  have hle : ∀ k, x k ≤ y k := fun k => by
    cases h : x k
    · exact Bool.false_le _
    · rw [hxy k h]
  have := wval_mono hwf hle w
  rw [hx] at this
  exact Bool.eq_true_of_true_le this

end BasicEval

section Phase0Clamp

private def clampGate (bound : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | .and, [] => ⟨.and, []⟩
  | .and, [a] => if a < bound then ⟨.and, [a]⟩ else ⟨.or, []⟩
  | .and, [a, b] => if a < bound ∧ b < bound then ⟨.and, [a, b]⟩ else ⟨.or, []⟩
  | .or, [] => ⟨.or, []⟩
  | .or, [a] => if a < bound then ⟨.or, [a]⟩ else ⟨.or, []⟩
  | .or, [a, b] =>
    if a < bound ∧ b < bound then ⟨.or, [a, b]⟩
    else if a < bound then ⟨.or, [a]⟩
    else if b < bound then ⟨.or, [b]⟩
    else ⟨.or, []⟩
  | _, _ => ⟨.or, []⟩

private def clampList (bound : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => clampGate bound g :: clampList (bound + 1) gs

private lemma clampList_length (bound : ℕ) (gs : List Gate) :
    (clampList bound gs).length = gs.length := by
  induction gs generalizing bound with
  | nil => rfl
  | cons g gs ih => simp [clampList, ih]

private lemma clampList_getElem (bound : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (clampList bound gs)[j]'(by rw [clampList_length]; exact hj) = clampGate (bound + j) gs[j] := by
  induction gs generalizing bound j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [clampList]
    | succ j =>
      simp only [clampList, List.getElem_cons_succ]
      have h := ih (bound + 1) j (Nat.lt_of_succ_lt_succ hj)
      have heq : bound + 1 + j = bound + (j + 1) := by omega
      rwa [heq] at h

private lemma clampGate_mono (bound : ℕ) (g : Gate) : MonoGate (clampGate bound g) := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp only [clampGate] <;> (try split_ifs) <;> simp [MonoGate]

private lemma clampGate_lt (bound : ℕ) (g : Gate) :
    ∀ a ∈ (clampGate bound g).inputs, a < bound := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp only [clampGate] <;> (try split_ifs) <;> simp_all

private lemma clampGate_eval (w : List Bool) (g : Gate) (hg : MonoGate g) :
    (clampGate w.length g).op.eval ((clampGate w.length g).inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · rfl
    · simp only [clampGate]
      split_ifs with h
      · rfl
      · have hd : w.getD a false = false := List.getD_eq_default _ _ (by omega)
        simp [GateOp.eval, hd, -List.getD_eq_getElem?_getD]
    · simp only [clampGate]
      split_ifs with h
      · rfl
      · by_cases ha : a < w.length
        · have hb : w.length ≤ b := by omega
          have hd : w.getD b false = false := List.getD_eq_default _ _ hb
          simp [GateOp.eval, hd, -List.getD_eq_getElem?_getD]
        · have hd : w.getD a false = false := List.getD_eq_default _ _ (by omega)
          simp [GateOp.eval, hd, -List.getD_eq_getElem?_getD]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · rfl
    · simp only [clampGate]
      split_ifs with h
      · rfl
      · have hd : w.getD a false = false := List.getD_eq_default _ _ (by omega)
        simp [GateOp.eval, hd, -List.getD_eq_getElem?_getD]
    · simp only [clampGate]
      split_ifs with h1 h2 h3
      · rfl
      · have hb : w.getD b false = false := List.getD_eq_default _ _ (by omega)
        simp [GateOp.eval, hb, -List.getD_eq_getElem?_getD]
      · have ha : w.getD a false = false := List.getD_eq_default _ _ (by omega)
        simp [GateOp.eval, ha, -List.getD_eq_getElem?_getD]
      · have ha : w.getD a false = false := List.getD_eq_default _ _ (by omega)
        have hb : w.getD b false = false := List.getD_eq_default _ _ (by omega)
        simp [GateOp.eval, ha, hb, -List.getD_eq_getElem?_getD]
    · simp at hlen

private lemma clampList_runWires (gs : List Gate) (hg : ∀ g ∈ gs, MonoGate g) (w : List Bool) :
    runWires (clampList w.length gs) w = runWires gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [clampList, runWires_cons, runWires_cons]
    have hev := clampGate_eval w g (hg g List.mem_cons_self)
    have hstep : wireStep w (clampGate w.length g) = wireStep w g := by
      unfold wireStep
      rw [hev]
    rw [hstep]
    have hlen : (wireStep w g).length = w.length + 1 := by simp [wireStep]
    rw [← hlen]
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) (wireStep w g)

private lemma clampGate_op_and {bound : ℕ} {g : Gate} (h : (clampGate bound g).op = GateOp.and) :
    g.op = GateOp.and := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp only [clampGate] at h <;> (try split_ifs at h) <;> cases h <;> rfl

private lemma clampList_wf (n : ℕ) (gs : List Gate) : Wf n (clampList n gs) := by
  constructor
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < gs.length := by rwa [clampList_length] at hj
    rw [clampList_getElem n gs j hj']
    exact clampGate_mono _ _
  · intro j hj a ha
    have hj' : j < gs.length := by rwa [clampList_length] at hj
    rw [clampList_getElem n gs j hj'] at ha
    exact clampGate_lt _ _ a ha

end Phase0Clamp

section GraphHelpers

private def edgeFun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : Bool :=
  decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

private def singleVec {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun k => decide (k = u)

private def edgeVec {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun k => decide (k = u ∨ k = v)

private lemma edgeFun_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    edgeFun G (singleVec u) = false := by
  rw [edgeFun, decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [singleVec, decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.ne_of_adj hab rfl

private lemma edgeFun_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (huv : G.Adj u v) :
    edgeFun G (edgeVec u v) = true := by
  rw [edgeFun, decide_eq_true_iff]
  exact ⟨u, v, huv, by simp [edgeVec], by simp [edgeVec]⟩

private lemma edgeFun_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    edgeFun G x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [edgeFun]

private def BelowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval gs x w = true → edgeFun G x = true

private def AtMostOneEdge {n : ℕ} (G : SimpleGraph (Fin n))
    (gs : List Gate) (w : ℕ) : Prop :=
  ∀ a b c d : Fin n, G.Adj a b → G.Adj c d →
    wval gs (edgeVec a b) w = true → wval gs (edgeVec c d) w = true →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

private def AllAndBelow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and → BelowF G gs (n + j)

end GraphHelpers

section Phase1Replace

open Classical in
private noncomputable def fixGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (j : ℕ) (g : Gate) : Gate :=
  if g.op = GateOp.and ∧ ¬ BelowF G gs (n + j) then
    if h : ∃ u v : Fin n, G.Adj u v ∧ wval gs (edgeVec u v) (n + j) = true then
      let u := Classical.choose h
      let v := Classical.choose (Classical.choose_spec h)
      ⟨GateOp.and, [u.val, v.val]⟩
    else
      ⟨GateOp.or, []⟩
  else g

private noncomputable def fixGates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) : List Gate :=
  (List.finRange gs.length).map (fun i => fixGate G gs i.val (gs[i.val]))

private lemma fixGates_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) : (fixGates G gs).length = gs.length := by
  simp [fixGates]

private lemma fixGates_getElem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (fixGates G gs)[j]'(by rw [fixGates_length]; exact hj) = fixGate G gs j gs[j] := by
  simp [fixGates]

private lemma fixGates_wf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} (hwf : Wf n gs) : Wf n (fixGates G gs) := by
  classical
  constructor
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < gs.length := by rwa [fixGates_length] at hj
    rw [fixGates_getElem G gs j hj']
    unfold fixGate
    split_ifs
    · simp [MonoGate]
    · simp [MonoGate]
    · exact hwf.1 _ (List.getElem_mem hj')
  · intro j hj a ha
    have hj' : j < gs.length := by rwa [fixGates_length] at hj
    rw [fixGates_getElem G gs j hj'] at ha
    unfold fixGate at ha
    split_ifs at ha with h1 h2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact Nat.lt_of_lt_of_le (Classical.choose h2).isLt (Nat.le_add_right _ _)
      · exact Nat.lt_of_lt_of_le (Classical.choose (Classical.choose_spec h2)).isLt
          (Nat.le_add_right _ _)
    · simp at ha
    · exact hwf.2 j hj' a ha

private lemma fixGates_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} (hwf : Wf n gs) (x : Fin n → Bool) :
    ∀ w, wval (fixGates G gs) x w ≤ wval gs x w := by
  classical
  have hwf' := fixGates_wf G hwf
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [wval_input _ x w hlt, wval_input _ x w hlt]
    · by_cases hge : n + gs.length ≤ w
      · rw [wval_ge _ x w (by rw [fixGates_length]; exact hge), wval_ge _ x w hge]
      · have hj : w - n < gs.length := by omega
        have hj' : w - n < (fixGates G gs).length := by rw [fixGates_length]; exact hj
        have hw : w = n + (w - n) := by omega
        rw [hw, wval_gate_wf hwf' x (w - n) hj', fixGates_getElem G gs (w - n) hj]
        unfold fixGate
        split_ifs with h1 h2
        · set u := Classical.choose h2
          set v := Classical.choose (Classical.choose_spec h2)
          have hspec : G.Adj u v ∧ wval gs (edgeVec u v) (n + (w - n)) = true :=
            Classical.choose_spec (Classical.choose_spec h2)
          change GateOp.and.eval ([u.val, v.val].map (wval (fixGates G gs) x)) ≤ _
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
            id, Bool.and_true, wval_input _ x u.val u.isLt, wval_input _ x v.val v.isLt]
          cases hxu : x u <;> cases hxv : x v
          · exact Bool.false_le _
          · exact Bool.false_le _
          · exact Bool.false_le _
          · simp only [Bool.and_self]
            have htrue := wval_mono_true hwf (x := edgeVec u v) (y := x) (fun k hk => by
              simp only [edgeVec, decide_eq_true_eq] at hk
              rcases hk with rfl | rfl <;> assumption) hspec.2
            rw [htrue]
        · simp [GateOp.eval]
        · rw [wval_gate_wf hwf x (w - n) hj]
          apply eval_mono_op (hwf.1 _ (List.getElem_mem hj)).1
          apply map_forall₂_le
          intro a ha
          exact ih a (by have := hwf.2 (w - n) hj a ha; omega)

private lemma fixGates_eq_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} (hwf : Wf n gs)
    (hstar : ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and →
      BelowF G gs (n + j) ∨ AtMostOneEdge G gs (n + j))
    {a b : Fin n} (hab : G.Adj a b) :
    ∀ w, wval (fixGates G gs) (edgeVec a b) w = wval gs (edgeVec a b) w := by
  classical
  have hwf' := fixGates_wf G hwf
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [wval_input _ _ w hlt, wval_input _ _ w hlt]
    · by_cases hge : n + gs.length ≤ w
      · rw [wval_ge _ _ w (by rw [fixGates_length]; exact hge), wval_ge _ _ w hge]
      · have hj : w - n < gs.length := by omega
        have hj' : w - n < (fixGates G gs).length := by rw [fixGates_length]; exact hj
        have hw : w = n + (w - n) := by omega
        rw [hw, wval_gate_wf hwf' _ (w - n) hj', fixGates_getElem G gs (w - n) hj]
        unfold fixGate
        split_ifs with h1 h2
        · set u := Classical.choose h2
          set v := Classical.choose (Classical.choose_spec h2)
          have hspec : G.Adj u v ∧ wval gs (edgeVec u v) (n + (w - n)) = true :=
            Classical.choose_spec (Classical.choose_spec h2)
          have hamo : AtMostOneEdge G gs (n + (w - n)) :=
            (hstar (w - n) hj h1.1).resolve_left h1.2
          change GateOp.and.eval ([u.val, v.val].map (wval (fixGates G gs) (edgeVec a b))) = _
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
            id, Bool.and_true, wval_input _ _ u.val u.isLt, wval_input _ _ v.val v.isLt,
            Fin.eta]
          by_cases hmatch : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
          · rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simp [edgeVec, hspec.2]
            · have hev : edgeVec v u = edgeVec u v := by
                funext k; simp [edgeVec, or_comm]
              rw [hev, hspec.2]; simp [edgeVec]
          · have hne : u ≠ v := G.ne_of_adj hspec.1
            have hlhs : (edgeVec a b u && edgeVec a b v) = false := by
              rw [Bool.and_eq_false_iff]
              by_contra hnot
              push Not at hnot
              simp only [Bool.not_eq_false, edgeVec, decide_eq_true_eq] at hnot
              rcases hnot.1 with hu | hu <;> rcases hnot.2 with hv | hv
              · exact hne (hu.trans hv.symm)
              · exact hmatch (Or.inl ⟨hu.symm, hv.symm⟩)
              · exact hmatch (Or.inr ⟨hv.symm, hu.symm⟩)
              · exact hne (hu.trans hv.symm)
            have hrhs : wval gs (edgeVec a b) (n + (w - n)) = false := by
              cases hval : wval gs (edgeVec a b) (n + (w - n))
              · rfl
              · exfalso
                exact hmatch (hamo a b u v hab hspec.1 hval hspec.2)
            rw [hlhs, hrhs]
        · simp only [GateOp.eval, List.map_nil, List.any_nil]
          cases hval : wval gs (edgeVec a b) (n + (w - n))
          · rfl
          · exfalso; exact h2 ⟨a, b, hab, hval⟩
        · rw [wval_gate_wf hwf _ (w - n) hj]
          congr 1
          apply List.map_congr_left
          intro c hc
          exact ih c (by have := hwf.2 (w - n) hj c hc; omega)

private lemma phase1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} {out : ℕ} (hwf : Wf n gs)
    (hcomp : ∀ x, wval gs x out = edgeFun G x)
    (hstar : ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and →
      BelowF G gs (n + j) ∨ AtMostOneEdge G gs (n + j)) :
    ∃ gs' : List Gate, gs'.length = gs.length ∧ Wf n gs' ∧
      (∀ x, wval gs' x out = edgeFun G x) ∧ AllAndBelow G gs' := by
  classical
  refine ⟨fixGates G gs, fixGates_length G gs, fixGates_wf G hwf, ?_, ?_⟩
  · intro x
    have hle : wval (fixGates G gs) x out ≤ edgeFun G x := by
      rw [← hcomp x]; exact fixGates_le G hwf x out
    cases hfx : edgeFun G x
    · rw [hfx] at hle
      cases hval : wval (fixGates G gs) x out
      · rfl
      · rw [hval] at hle; exact absurd (hle rfl) (by decide)
    · rw [edgeFun_true_iff] at hfx
      obtain ⟨a, b, hab, hxa, hxb⟩ := hfx
      have he : wval (fixGates G gs) (edgeVec a b) out = true := by
        rw [fixGates_eq_edge G hwf hstar hab out, hcomp, edgeFun_edge G hab]
      exact wval_mono_true (fixGates_wf G hwf) (x := edgeVec a b) (y := x) (fun k hk => by
        simp only [edgeVec, decide_eq_true_eq] at hk
        rcases hk with rfl | rfl <;> assumption) he
  · intro j hj hop x hx
    have hj' : j < gs.length := by rwa [fixGates_length] at hj
    rw [fixGates_getElem G gs j hj'] at hop
    unfold fixGate at hop
    split_ifs at hop with h1 h2
    · rw [wval_gate_wf (fixGates_wf G hwf) x j hj, fixGates_getElem G gs j hj'] at hx
      unfold fixGate at hx
      rw [ite_eq_left h1, dite_eq_left h2] at hx
      set u := Classical.choose h2
      set v := Classical.choose (Classical.choose_spec h2)
      have hspec : G.Adj u v ∧ wval gs (edgeVec u v) (n + j) = true :=
        Classical.choose_spec (Classical.choose_spec h2)
      change GateOp.and.eval ([u.val, v.val].map (wval (fixGates G gs) x)) = true at hx
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id, Bool.and_true, wval_input _ x u.val u.isLt, wval_input _ x v.val v.isLt,
        Fin.eta, Bool.and_eq_true] at hx
      rw [edgeFun_true_iff]
      exact ⟨u, v, hspec.1, hx.1, hx.2⟩
    · have hbel : BelowF G gs (n + j) := by
        by_contra hn
        exact h1 ⟨hop, hn⟩
      have hle := fixGates_le G hwf x (n + j)
      rw [hx] at hle
      exact hbel x (Bool.eq_true_of_true_le hle)

end Phase1Replace

section Phase2Unmix

private def singleSet (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v : Fin n => wval gs (singleVec v) w = true)

private lemma mem_singleSet {n : ℕ} (gs : List Gate) (w : ℕ) (v : Fin n) :
    v ∈ singleSet n gs w ↔ wval gs (singleVec v) w = true := by
  simp [singleSet]

private lemma singleSet_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) :
    singleSet n gs i = {⟨i, hi⟩} := by
  ext v
  simp [singleSet, wval_input gs _ i hi, singleVec, Fin.ext_iff, eq_comm]

private lemma singleSet_belowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} {w : ℕ} (hb : BelowF G gs w) :
    singleSet n gs w = ∅ := by
  ext v
  simp only [mem_singleSet, Finset.notMem_empty, iff_false]
  intro h
  have := hb (singleVec v) h
  rw [edgeFun_single G v] at this
  exact Bool.noConfusion this

private lemma belowF_of_singleSet_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} (hwf : Wf n gs) (hab : AllAndBelow G gs) :
    ∀ w, singleSet n gs w = ∅ → BelowF G gs w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hempty x hx
    by_cases hlt : w < n
    · exfalso
      have : (⟨w, hlt⟩ : Fin n) ∈ singleSet n gs w := by
        rw [singleSet_input gs w hlt]; simp
      rw [hempty] at this; exact Finset.notMem_empty _ this
    · by_cases hge : n + gs.length ≤ w
      · rw [wval_ge gs x w hge] at hx; exact Bool.noConfusion hx
      · have hj : w - n < gs.length := by omega
        have hw : w = n + (w - n) := by omega
        rw [hw] at hempty hx
        rcases (hwf.1 _ (List.getElem_mem hj)).1 with hand | hor
        · exact hab (w - n) hj hand x hx
        · have hlen := (hwf.1 _ (List.getElem_mem hj)).2
          rw [wval_gate_wf hwf x (w - n) hj, hor] at hx
          rcases h_ins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · rw [h_ins] at hx; simp [GateOp.eval] at hx
          · rw [h_ins] at hx
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              Bool.or_false] at hx
            have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [h_ins]; simp)
            have hsa : singleSet n gs a = ∅ := by
              ext v
              simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv
              have hmem : v ∈ singleSet n gs (n + (w - n)) := by
                rw [mem_singleSet, wval_gate_wf hwf _ (w - n) hj, hor, h_ins]
                simp [GateOp.eval, hv]
              rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
            exact ih a (by omega) hsa x hx
          · rw [h_ins] at hx
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              Bool.or_false, Bool.or_eq_true] at hx
            have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [h_ins]; simp)
            have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [h_ins]; simp)
            have hsa : singleSet n gs a = ∅ := by
              ext v
              simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv
              have hmem : v ∈ singleSet n gs (n + (w - n)) := by
                rw [mem_singleSet, wval_gate_wf hwf _ (w - n) hj, hor, h_ins]
                simp [GateOp.eval, hv]
              rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
            have hsb : singleSet n gs b = ∅ := by
              ext v
              simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv
              have hmem : v ∈ singleSet n gs (n + (w - n)) := by
                rw [mem_singleSet, wval_gate_wf hwf _ (w - n) hj, hor, h_ins]
                simp [GateOp.eval, hv]
              rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
            rcases hx with hxa | hxb
            · exact ih a (by omega) hsa x hxa
            · exact ih b (by omega) hsb x hxb
          · rw [h_ins] at hlen; simp at hlen

private def remapIdx (n k v : ℕ) (i : ℕ) : ℕ :=
  if i < n + k then i
  else if i = n + k then v
  else i - 1

private def remapGate (n k v : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapIdx n k v)⟩

private def unmixGates (n k u v out : ℕ) (gs : List Gate) : List Gate :=
  gs.take k ++ (gs.drop (k + 1)).map (remapGate n k v) ++ [⟨GateOp.or, [remapIdx n k v out, u]⟩]

private lemma unmixGates_length {n k u v out : ℕ} {gs : List Gate} (hk : k < gs.length) :
    (unmixGates n k u v out gs).length = gs.length := by
  simp only [unmixGates, List.length_append, List.length_take, List.length_map, List.length_drop,
    List.length_singleton]
  omega

private lemma unmixGates_getElem_lt {n k u v out : ℕ} {gs : List Gate} {j : ℕ}
    (hj : j < k) (hk : k < gs.length) :
    (unmixGates n k u v out gs)[j]'(by rw [unmixGates_length hk]; omega) = gs[j] := by
  unfold unmixGates
  have h1 : j < (gs.take k).length := by simp [Nat.min_eq_left (Nat.le_of_lt hk)]; exact hj
  rw [List.getElem_append_left (by simp [List.length_append]; omega)]
  rw [List.getElem_append_left h1, List.getElem_take]

private lemma unmixGates_getElem_mid {n k u v out : ℕ} {gs : List Gate} {j : ℕ}
    (hjk : k ≤ j) (hj : j + 1 < gs.length) :
    (unmixGates n k u v out gs)[j]'(by rw [unmixGates_length (by omega)]; omega) =
      remapGate n k v gs[j + 1] := by
  unfold unmixGates
  have hk : k < gs.length := by omega
  have htake : (gs.take k).length = k := by simp [Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [List.getElem_append_left (by simp [htake]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [List.getElem_map, List.getElem_drop, htake]
  congr 1
  have heq : k + 1 + (j - k) = j + 1 := by omega
  simp [heq]

private lemma unmixGates_getElem_last {n k u v out : ℕ} {gs : List Gate} (hk : k < gs.length) :
    (unmixGates n k u v out gs)[gs.length - 1]'(by rw [unmixGates_length hk]; omega) =
      ⟨GateOp.or, [remapIdx n k v out, u]⟩ := by
  unfold unmixGates
  have htake : (gs.take k).length = k := by simp [Nat.min_eq_left (Nat.le_of_lt hk)]
  have hlen : (gs.take k ++ (gs.drop (k + 1)).map (remapGate n k v)).length = gs.length - 1 := by
    simp [htake]; omega
  rw [List.getElem_append_right (by omega)]
  simp

private lemma remapIdx_lt {n k v i bound : ℕ} (hv : v < n + k) (hi : i < bound)
    (hb : n + k < bound) : remapIdx n k v i < bound - 1 := by
  unfold remapIdx
  split_ifs <;> omega

private lemma unmixGates_wf {n k u v out : ℕ} {gs : List Gate}
    (hwf : Wf n gs) (hk : k < gs.length) (hu : u < n + k) (hv : v < n + k)
    (hout : out < n + gs.length) :
    Wf n (unmixGates n k u v out gs) := by
  have hlen := unmixGates_length (n := n) (u := u) (v := v) (out := out) hk
  constructor
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [hlen] at hj
    by_cases h1 : j < k
    · rw [unmixGates_getElem_lt h1 hk]
      exact hwf.1 _ (List.getElem_mem (by omega))
    · by_cases h2 : j + 1 < gs.length
      · rw [unmixGates_getElem_mid (by omega) h2]
        have hm := hwf.1 _ (List.getElem_mem h2)
        exact ⟨hm.1, by simp [remapGate, hm.2]⟩
      · have hjlast : j = gs.length - 1 := by omega
        subst hjlast
        rw [unmixGates_getElem_last hk]
        simp [MonoGate]
  · intro j hj a ha
    rw [hlen] at hj
    by_cases h1 : j < k
    · rw [unmixGates_getElem_lt h1 hk] at ha
      exact hwf.2 j (by omega) a ha
    · by_cases h2 : j + 1 < gs.length
      · rw [unmixGates_getElem_mid (by omega) h2] at ha
        simp only [remapGate, List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        have hblt := hwf.2 (j + 1) h2 b hb
        have := remapIdx_lt hv hblt (by omega)
        omega
      · have hjlast : j = gs.length - 1 := by omega
        subst hjlast
        rw [unmixGates_getElem_last hk] at ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have := remapIdx_lt hv hout (by omega)
          omega
        · omega

private lemma unmixGates_eq_lt {n k u v out : ℕ} {gs : List Gate}
    (hwf : Wf n gs) (hk : k < gs.length) (hu : u < n + k) (hv : v < n + k)
    (hout : out < n + gs.length) (x : Fin n → Bool) :
    ∀ i, i < n + k → wval (unmixGates n k u v out gs) x i = wval gs x i := by
  have hwf' := unmixGates_wf hwf hk hu hv hout
  have hlen := unmixGates_length (n := n) (u := u) (v := v) (out := out) hk
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hlt : i < n
    · rw [wval_input _ x i hlt, wval_input _ x i hlt]
    · have hj : i - n < k := by omega
      have hj' : i - n < gs.length := by omega
      have hi_eq : i = n + (i - n) := by omega
      rw [hi_eq, wval_gate_wf hwf' x (i - n) (by omega),
        unmixGates_getElem_lt hj hk, wval_gate_wf hwf x (i - n) hj']
      congr 1
      apply List.map_congr_left
      intro a ha
      have halt := hwf.2 (i - n) hj' a ha
      exact ih a (by omega) (by omega)

private lemma unmixGates_le_and_eq {n k u v out : ℕ} {gs : List Gate}
    (hwf : Wf n gs) (hk : k < gs.length) (hu : u < n + k) (hv : v < n + k)
    (hout : out < n + gs.length)
    (hgk : ∀ x : Fin n → Bool, wval gs x (n + k) = (wval gs x u || wval gs x v))
    (x : Fin n → Bool) :
    ∀ i, i < n + gs.length →
      wval (unmixGates n k u v out gs) x (remapIdx n k v i) ≤ wval gs x i ∧
      (wval gs x u = false → wval (unmixGates n k u v out gs) x (remapIdx n k v i) = wval gs x i) := by
  have hwf' := unmixGates_wf hwf hk hu hv hout
  have hlen := unmixGates_length (n := n) (u := u) (v := v) (out := out) hk
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases h1 : i < n + k
    · have hr : remapIdx n k v i = i := by unfold remapIdx; simp [h1]
      rw [hr, unmixGates_eq_lt hwf hk hu hv hout x i h1]
      exact ⟨le_refl _, fun _ => rfl⟩
    · by_cases h2 : i = n + k
      · subst h2
        have hr : remapIdx n k v (n + k) = v := by unfold remapIdx; simp
        rw [hr, unmixGates_eq_lt hwf hk hu hv hout x v hv, hgk x]
        constructor
        · cases wval gs x u <;> cases wval gs x v <;> decide
        · intro huf; rw [huf]; simp
      · have hgt : n + k < i := by omega
        have hr : remapIdx n k v i = n + (i - n - 1) := by
          unfold remapIdx
          rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
          omega
        have hj : i - n - 1 + 1 < gs.length := by omega
        have hjk : k ≤ i - n - 1 := by omega
        have hi_eq : i = n + (i - n - 1 + 1) := by omega
        have hgi : wval gs x i = gs[i - n - 1 + 1].op.eval (gs[i - n - 1 + 1].inputs.map (wval gs x)) := by
          conv_lhs => rw [hi_eq]
          exact wval_gate_wf hwf x (i - n - 1 + 1) hj
        rw [hr, wval_gate_wf hwf' x (i - n - 1) (by omega), unmixGates_getElem_mid hjk hj, hgi]
        simp only [remapGate, List.map_map]
        constructor
        · apply eval_mono_op (hwf.1 _ (List.getElem_mem hj)).1
          apply map_forall₂_le
          intro a ha
          have halt := hwf.2 (i - n - 1 + 1) hj a ha
          exact (ih a (by omega) (by omega)).1
        · intro huf
          congr 1
          apply List.map_congr_left
          intro a ha
          have halt := hwf.2 (i - n - 1 + 1) hj a ha
          exact (ih a (by omega) (by omega)).2 huf

private def countNonemptyS (n : ℕ) (gs : List Gate) : ℕ :=
  (Finset.univ.filter (fun j : Fin gs.length => (singleSet n gs (n + j.val)).Nonempty)).card

private lemma phase2_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} {out k u v : ℕ} (hwf : Wf n gs) (hab : AllAndBelow G gs)
    (hcomp : ∀ x, wval gs x out = edgeFun G x)
    (hout : out < n + gs.length)
    (hk : k < gs.length) (hu : u < n + k) (hv : v < n + k)
    (hgk : ∀ x : Fin n → Bool, wval gs x (n + k) = (wval gs x u || wval gs x v))
    (hsu : singleSet n gs u = ∅) (hsv : (singleSet n gs v).Nonempty) :
    let gs' := unmixGates n k u v out gs
    let out' := n + (gs.length - 1)
    gs'.length = gs.length ∧ out' < n + gs'.length ∧ Wf n gs' ∧ AllAndBelow G gs' ∧
      (∀ x, wval gs' x out' = edgeFun G x) ∧ countNonemptyS n gs' < countNonemptyS n gs := by
  dsimp only
  set gs' := unmixGates n k u v out gs
  set out' := n + (gs.length - 1)
  have hlen : gs'.length = gs.length := unmixGates_length hk
  have hwf' : Wf n gs' := unmixGates_wf hwf hk hu hv hout
  have hbu : BelowF G gs u := belowF_of_singleSet_empty G hwf hab u hsu
  have hcomp' : ∀ x, wval gs' x out' = edgeFun G x := by
    intro x
    have hlast : wval gs' x out' = (wval gs' x (remapIdx n k v out) || wval gs' x u) := by
      rw [wval_gate_wf hwf' x (gs.length - 1) (by omega), unmixGates_getElem_last hk]
      simp [GateOp.eval]
    rw [hlast, unmixGates_eq_lt hwf hk hu hv hout x u hu]
    obtain ⟨hle, heq⟩ := unmixGates_le_and_eq hwf hk hu hv hout hgk x out hout
    cases hux : wval gs x u
    · rw [heq hux, hcomp x]; simp
    · rw [hbu x hux]; simp
  have hab' : AllAndBelow G gs' := by
    intro j hj hop x hx
    rw [hlen] at hj
    by_cases h1 : j < k
    · rw [unmixGates_getElem_lt h1 hk] at hop
      rw [unmixGates_eq_lt hwf hk hu hv hout x (n + j) (by omega)] at hx
      exact hab j (by omega) hop x hx
    · by_cases h2 : j + 1 < gs.length
      · rw [unmixGates_getElem_mid (by omega) h2] at hop
        have hop' : gs[j + 1].op = GateOp.and := hop
        have hr : remapIdx n k v (n + (j + 1)) = n + j := by
          unfold remapIdx
          rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
          omega
        have hle := (unmixGates_le_and_eq hwf hk hu hv hout hgk x (n + (j + 1)) (by omega)).1
        rw [hr, hx] at hle
        exact hab (j + 1) h2 hop' x (Bool.eq_true_of_true_le hle)
      · have hjlast : j = gs.length - 1 := by omega
        subst hjlast
        rw [unmixGates_getElem_last hk] at hop
        cases hop
  have hcnt : countNonemptyS n gs' < countNonemptyS n gs := by
    let A := Finset.univ.filter (fun j : Fin gs'.length => (singleSet n gs' (n + j.val)).Nonempty)
    let B := Finset.univ.filter (fun j : Fin gs.length => (singleSet n gs (n + j.val)).Nonempty)
    change A.card < B.card
    have hA_eq : A.card = ((Finset.range gs.length).filter (fun j => (singleSet n gs' (n + j)).Nonempty)).card := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢
        exact ⟨by omega, hj⟩
      · intro j1 _ j2 _ h; exact Fin.ext h
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        exact ⟨⟨j, by omega⟩, by simp [A, hj.2], rfl⟩
    have hB_eq : B.card = ((Finset.range gs.length).filter (fun j => (singleSet n gs (n + j)).Nonempty)).card := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢
        exact ⟨j.isLt, hj⟩
      · intro j1 _ j2 _ h; exact Fin.ext h
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        exact ⟨⟨j, hj.1⟩, by simp [B, hj.2], rfl⟩
    rw [hA_eq, hB_eq]
    set S1 := (Finset.range gs.length).filter (fun j => (singleSet n gs' (n + j)).Nonempty)
    set S2 := (Finset.range gs.length).filter (fun j => (singleSet n gs (n + j)).Nonempty)
    have hlast_not : gs.length - 1 ∉ S1 := by
      simp only [S1, Finset.mem_filter, Finset.mem_range, not_and]
      intro _
      have hempty : singleSet n gs' out' = ∅ := by
        apply singleSet_belowF G
        intro x hx; rw [hcomp' x] at hx; exact hx
      rw [hempty]; exact Finset.not_nonempty_empty
    have hk_in : k ∈ S2 := by
      simp only [S2, Finset.mem_filter, Finset.mem_range]
      refine ⟨hk, ?_⟩
      obtain ⟨w, hw⟩ := hsv
      refine ⟨w, ?_⟩
      rw [mem_singleSet, hgk, (mem_singleSet _ _ _).mp hw]
      simp
    let emb : ℕ → ℕ := fun j => if j < k then j else j + 1
    have himg : S1.image emb ⊆ S2.erase k := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      have hjne : j ≠ gs.length - 1 := fun heq => hlast_not (heq ▸ hj)
      simp only [S1, Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_erase]
      simp only [S2, Finset.mem_filter, Finset.mem_range, emb]
      split_ifs with hjk
      · refine ⟨by omega, by omega, ?_⟩
        obtain ⟨w, hw⟩ := hj.2
        refine ⟨w, ?_⟩
        rw [mem_singleSet] at hw ⊢
        rwa [unmixGates_eq_lt hwf hk hu hv hout _ (n + j) (by omega)] at hw
      · refine ⟨by omega, by omega, ?_⟩
        obtain ⟨w, hw⟩ := hj.2
        refine ⟨w, ?_⟩
        rw [mem_singleSet] at hw ⊢
        have hr : remapIdx n k v (n + (j + 1)) = n + j := by
          unfold remapIdx
          rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
          omega
        have hle := (unmixGates_le_and_eq hwf hk hu hv hout hgk (singleVec w) (n + (j + 1)) (by omega)).1
        rw [hr, hw] at hle
        exact Bool.eq_true_of_true_le hle
    have hinj : ∀ j1 ∈ S1, ∀ j2 ∈ S1, emb j1 = emb j2 → j1 = j2 := by
      intro j1 _ j2 _ h
      simp only [emb] at h
      split_ifs at h <;> omega
    have hcard1 : S1.card = (S1.image emb).card := (Finset.card_image_of_injOn hinj).symm
    have hcard2 : (S1.image emb).card ≤ (S2.erase k).card := Finset.card_le_card himg
    have hcard3 : (S2.erase k).card + 1 = S2.card := Finset.card_erase_add_one hk_in
    omega
  exact ⟨hlen, by omega, hwf', hab', hcomp', hcnt⟩

private def NoMixedOr {n : ℕ} (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.or →
    ∀ a b, gs[j].inputs = [a, b] → (singleSet n gs a = ∅ ↔ singleSet n gs b = ∅)

private lemma phase2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} {out : ℕ} (hwf : Wf n gs) (hab : AllAndBelow G gs)
    (hcomp : ∀ x, wval gs x out = edgeFun G x) (hout : out < n + gs.length) :
    ∃ (gs' : List Gate) (out' : ℕ), gs'.length = gs.length ∧ out' < n + gs'.length ∧
      Wf n gs' ∧ AllAndBelow G gs' ∧ (∀ x, wval gs' x out' = edgeFun G x) ∧ NoMixedOr (n := n) gs' := by
  classical
  have hmain : ∀ m : ℕ, ∀ (gs : List Gate) (out : ℕ),
      countNonemptyS n gs = m → Wf n gs → AllAndBelow G gs →
      (∀ x, wval gs x out = edgeFun G x) → out < n + gs.length →
      ∃ (gs' : List Gate) (out' : ℕ), gs'.length = gs.length ∧ out' < n + gs'.length ∧
        Wf n gs' ∧ AllAndBelow G gs' ∧ (∀ x, wval gs' x out' = edgeFun G x) ∧ NoMixedOr (n := n) gs' := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro gs out hm hwf hab hcomp hout
      by_cases hnm : NoMixedOr (n := n) gs
      · exact ⟨gs, out, rfl, hout, hwf, hab, hcomp, hnm⟩
      · unfold NoMixedOr at hnm
        push Not at hnm
        obtain ⟨k, hk, hor, a, b, hins, hneq⟩ := hnm
        have ha : a < n + k := hwf.2 k hk a (by rw [hins]; simp)
        have hb : b < n + k := hwf.2 k hk b (by rw [hins]; simp)
        have hgk_ab : ∀ x : Fin n → Bool, wval gs x (n + k) = (wval gs x a || wval gs x b) := by
          intro x
          rw [wval_gate_wf hwf x k hk, hor, hins]
          simp [GateOp.eval]
        rcases hneq with ⟨hsa, hsb⟩ | ⟨hsa_ne, hsb⟩
        · obtain ⟨hlen, hout', hwf', hab', hcomp', hlt⟩ :=
            phase2_step G hwf hab hcomp hout hk ha hb hgk_ab hsa hsb
          obtain ⟨gs'', out'', hlen'', hout'', hwf'', hab'', hcomp'', hnm''⟩ :=
            ih _ (hm ▸ hlt) _ _ rfl hwf' hab' hcomp' hout'
          exact ⟨gs'', out'', hlen''.trans hlen, hout'', hwf'', hab'', hcomp'', hnm''⟩
        · have hgk_ba : ∀ x : Fin n → Bool, wval gs x (n + k) = (wval gs x b || wval gs x a) := fun x => by
            rw [hgk_ab x, Bool.or_comm]
          obtain ⟨hlen, hout', hwf', hab', hcomp', hlt⟩ :=
            phase2_step G hwf hab hcomp hout hk hb ha hgk_ba hsb hsa_ne
          obtain ⟨gs'', out'', hlen'', hout'', hwf'', hab'', hcomp'', hnm''⟩ :=
            ih _ (hm ▸ hlt) _ _ rfl hwf' hab' hcomp' hout'
          exact ⟨gs'', out'', hlen''.trans hlen, hout'', hwf'', hab'', hcomp'', hnm''⟩
  exact hmain (countNonemptyS n gs) gs out rfl hwf hab hcomp hout

end Phase2Unmix

section GraphReachCount

private def Reach {α : Type*} (E : List (α × α)) : α → α → Prop :=
  Relation.ReflTransGen (fun x y => (x, y) ∈ E ∨ (y, x) ∈ E)

private lemma reach_refl {α : Type*} (E : List (α × α)) (a : α) : Reach E a a :=
  Relation.ReflTransGen.refl

private lemma reach_trans {α : Type*} {E : List (α × α)} {a b c : α}
    (h1 : Reach E a b) (h2 : Reach E b c) : Reach E a c :=
  Relation.ReflTransGen.trans h1 h2

private lemma reach_symm {α : Type*} {E : List (α × α)} {a b : α} (h : Reach E a b) :
    Reach E b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep.symm) ih

private lemma reach_of_mem {α : Type*} {E : List (α × α)} {a b : α} (h : (a, b) ∈ E) :
    Reach E a b :=
  Relation.ReflTransGen.single (Or.inl h)

private lemma reach_mono {α : Type*} {E1 E2 : List (α × α)} (hsub : ∀ p ∈ E1, p ∈ E2)
    {a b : α} (h : Reach E1 a b) : Reach E2 a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    apply Relation.ReflTransGen.tail ih
    rcases hstep with h1 | h1
    · exact Or.inl (hsub _ h1)
    · exact Or.inr (hsub _ h1)

private lemma reach_cons_cases {α : Type*} {u v : α} {E : List (α × α)} {a b : α}
    (h : Reach ((u, v) :: E) a b) :
    Reach E a b ∨ (Reach E a u ∧ Reach E v b) ∨ (Reach E a v ∧ Reach E u b) := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail y z _ hstep ih =>
    simp only [List.mem_cons, Prod.mk.injEq] at hstep
    rcases hstep with (⟨rfl, rfl⟩ | hE) | (⟨rfl, rfl⟩ | hE)
    · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.refl⟩)
      · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.refl⟩)
      · exact Or.inl h1
    · have hyz : Reach E y z := Relation.ReflTransGen.single (Or.inl hE)
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (reach_trans h1 hyz)
      · exact Or.inr (Or.inl ⟨h1, reach_trans h2 hyz⟩)
      · exact Or.inr (Or.inr ⟨h1, reach_trans h2 hyz⟩)
    · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.refl⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.refl⟩)
    · have hyz : Reach E y z := Relation.ReflTransGen.single (Or.inr hE)
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (reach_trans h1 hyz)
      · exact Or.inr (Or.inl ⟨h1, reach_trans h2 hyz⟩)
      · exact Or.inr (Or.inr ⟨h1, reach_trans h2 hyz⟩)

open Classical in
private noncomputable def compOf {α : Type*} (V : Finset α) (E : List (α × α)) (x : α) : Finset α :=
  V.filter (fun y => Reach E x y)

open Classical in
private noncomputable def comps {α : Type*} (V : Finset α) (E : List (α × α)) : Finset (Finset α) :=
  V.image (compOf V E)

private lemma compOf_eq_iff {α : Type*} {V : Finset α} {E : List (α × α)}
    {x y : α} (_hx : x ∈ V) (hy : y ∈ V) :
    compOf V E x = compOf V E y ↔ Reach E x y := by
  classical
  constructor
  · intro h
    have hmem : y ∈ compOf V E y := by simp [compOf, hy, reach_refl]
    rw [← h] at hmem
    simp only [compOf, Finset.mem_filter] at hmem
    exact hmem.2
  · intro hxy
    ext z
    simp only [compOf, Finset.mem_filter]
    exact ⟨fun ⟨hz, hxz⟩ => ⟨hz, reach_trans (reach_symm hxy) hxz⟩,
      fun ⟨hz, hyz⟩ => ⟨hz, reach_trans hxy hyz⟩⟩

private lemma comps_nil {α : Type*} (V : Finset α) : (comps V []).card = V.card := by
  classical
  unfold comps
  rw [Finset.card_image_of_injOn]
  intro x hx y hy h
  have hr := (compOf_eq_iff hx hy).mp h
  cases hr with
  | refl => rfl
  | tail _ hstep => simp at hstep

private lemma comps_cons_le {α : Type*} (V : Finset α) (u v : α) (E : List (α × α)) :
    (comps V E).card ≤ (comps V ((u, v) :: E)).card + 1 := by
  classical
  -- Map each component C ∈ comps V E (picking a rep x ∈ C) to compOf V ((u,v)::E) x.
  -- Show on (comps V E).erase (compOf V E v) this map is injective!
  let S := (comps V E).erase (compOf V E v)
  have hS : (comps V E).card ≤ S.card + 1 := by
    dsimp only [S]
    by_cases hv : compOf V E v ∈ comps V E
    · have := Finset.card_erase_add_one hv
      omega
    · rw [Finset.erase_eq_of_notMem hv]; omega
  suffices hle : S.card ≤ (comps V ((u, v) :: E)).card by omega
  let lift : Finset α → Finset α := fun C =>
    if h : C.Nonempty then compOf V ((u, v) :: E) (Classical.choose h) else ∅
  have himg : S.image lift ⊆ comps V ((u, v) :: E) := by
    intro D hD
    rw [Finset.mem_image] at hD
    obtain ⟨C, hC, rfl⟩ := hD
    have hCm : C ∈ comps V E := Finset.mem_of_mem_erase hC
    rw [comps, Finset.mem_image] at hCm
    obtain ⟨x, hx, rfl⟩ := hCm
    have hne : (compOf V E x).Nonempty := ⟨x, by simp [compOf, hx, reach_refl]⟩
    have hch : Classical.choose hne ∈ V := by
      have hm := Classical.choose_spec hne
      simp only [compOf, Finset.mem_filter] at hm
      exact hm.1
    simp only [lift, hne, ↓reduceDIte]
    exact Finset.mem_image_of_mem (compOf V ((u, v) :: E)) hch
  have hinj : ∀ C1 ∈ S, ∀ C2 ∈ S, lift C1 = lift C2 → C1 = C2 := by
    intro C1 hC1 C2 hC2 heq
    have hC1ne : C1 ≠ compOf V E v := (Finset.mem_erase.mp hC1).1
    have hC2ne : C2 ≠ compOf V E v := (Finset.mem_erase.mp hC2).1
    have hC1m := Finset.mem_of_mem_erase hC1
    have hC2m := Finset.mem_of_mem_erase hC2
    rw [comps, Finset.mem_image] at hC1m hC2m
    obtain ⟨x1, hx1, rfl⟩ := hC1m
    obtain ⟨x2, hx2, rfl⟩ := hC2m
    have hne1 : (compOf V E x1).Nonempty := ⟨x1, by simp [compOf, hx1, reach_refl]⟩
    have hne2 : (compOf V E x2).Nonempty := ⟨x2, by simp [compOf, hx2, reach_refl]⟩
    set y1 := Classical.choose hne1
    set y2 := Classical.choose hne2
    have hy1m : y1 ∈ compOf V E x1 := Classical.choose_spec hne1
    have hy2m : y2 ∈ compOf V E x2 := Classical.choose_spec hne2
    simp only [compOf, Finset.mem_filter] at hy1m hy2m
    have he1 : compOf V E x1 = compOf V E y1 := (compOf_eq_iff hx1 hy1m.1).mpr hy1m.2
    have he2 : compOf V E x2 = compOf V E y2 := (compOf_eq_iff hx2 hy2m.1).mpr hy2m.2
    simp only [lift, hne1, hne2, ↓reduceDIte] at heq
    have hr : Reach ((u, v) :: E) y1 y2 := (compOf_eq_iff hy1m.1 hy2m.1).mp heq
    rcases reach_cons_cases hr with hE | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [he1, he2]; exact (compOf_eq_iff hy1m.1 hy2m.1).mpr hE
    · exfalso
      apply hC2ne
      rw [he2]
      ext z
      simp only [compOf, Finset.mem_filter]
      exact ⟨fun ⟨hz, hyz⟩ => ⟨hz, reach_trans h2 hyz⟩,
        fun ⟨hz, hvz⟩ => ⟨hz, reach_trans (reach_symm h2) hvz⟩⟩
    · exfalso
      apply hC1ne
      rw [he1]
      ext z
      simp only [compOf, Finset.mem_filter]
      exact ⟨fun ⟨hz, hyz⟩ => ⟨hz, reach_trans (reach_symm h1) hyz⟩,
        fun ⟨hz, hvz⟩ => ⟨hz, reach_trans h1 hvz⟩⟩
  calc S.card = (S.image lift).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (comps V ((u, v) :: E)).card := Finset.card_le_card himg

private lemma card_le_edges_add_one {α : Type*} (V : Finset α) (E : List (α × α))
    (hV : V.Nonempty) (hconn : ∀ a ∈ V, ∀ b ∈ V, Reach E a b) :
    V.card ≤ E.length + 1 := by
  classical
  have hstep : ∀ L : List (α × α), V.card ≤ (comps V L).card + L.length := by
    intro L
    induction L with
    | nil => simp [comps_nil]
    | cons p L ih =>
      rcases p with ⟨u, v⟩
      have h1 := comps_cons_le V u v L
      simp only [List.length_cons]
      omega
  have h1 : (comps V E).card = 1 := by
    obtain ⟨x0, hx0⟩ := hV
    have heq : comps V E = {V} := by
      ext C
      simp only [comps, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, rfl⟩
        ext y
        simp only [compOf, Finset.mem_filter, and_iff_left_iff_imp]
        intro hy; exact hconn x hx y hy
      · rintro rfl
        refine ⟨x0, hx0, ?_⟩
        ext y
        simp only [compOf, Finset.mem_filter, and_iff_left_iff_imp]
        intro hy; exact hconn x0 hx0 y hy
    rw [heq, Finset.card_singleton]
  have := hstep E
  omega

end GraphReachCount

section Phase3Ledger

private def edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (w : ℕ) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter (fun e =>
    Sym2.lift ⟨fun u v => wval gs (edgeVec u v) w,
      fun u v => by
        dsimp only
        have h : edgeVec u v = edgeVec v u := by funext k; simp [edgeVec, or_comm]
        rw [h]⟩ e = true)

private lemma mem_edgeSet_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (w : ℕ) (u v : Fin n) :
    s(u, v) ∈ edgeSet G gs w ↔ G.Adj u v ∧ wval gs (edgeVec u v) w = true := by
  simp [edgeSet, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

private lemma val_imp_mem_singleSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {gs : List Gate} (hwf : Wf n gs) (hab : AllAndBelow G gs) (hnm : NoMixedOr (n := n) gs) :
    ∀ w, (singleSet n gs w).Nonempty →
      ∀ x : Fin n → Bool, wval gs x w = true → ∃ v ∈ singleSet n gs w, x v = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hne x hx
    by_cases hlt : w < n
    · rw [wval_input gs x w hlt] at hx
      exact ⟨⟨w, hlt⟩, by rw [singleSet_input gs w hlt]; simp, hx⟩
    · by_cases hge : n + gs.length ≤ w
      · rw [wval_ge gs x w hge] at hx; exact Bool.noConfusion hx
      · have hj : w - n < gs.length := by omega
        have hw : w = n + (w - n) := by omega
        rw [hw] at hne hx ⊢
        rcases (hwf.1 _ (List.getElem_mem hj)).1 with hand | hor
        · exfalso
          have hempty := singleSet_belowF G (hab (w - n) hj hand)
          rw [hempty] at hne
          exact Finset.not_nonempty_empty hne
        · have hlen := (hwf.1 _ (List.getElem_mem hj)).2
          rw [wval_gate_wf hwf x (w - n) hj, hor] at hx
          rcases hins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · rw [hins] at hx; simp [GateOp.eval] at hx
          · rw [hins] at hx
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              Bool.or_false] at hx
            have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hseq : singleSet n gs (n + (w - n)) = singleSet n gs a := by
              ext v
              simp only [mem_singleSet]
              rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]
              simp [GateOp.eval]
            rw [hseq] at hne ⊢
            exact ih a (by omega) hne x hx
          · rw [hins] at hx
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              Bool.or_false, Bool.or_eq_true] at hx
            have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [hins]; simp)
            have hsunion : singleSet n gs (n + (w - n)) = singleSet n gs a ∪ singleSet n gs b := by
              ext v
              simp only [Finset.mem_union, mem_singleSet]
              rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]
              simp [GateOp.eval]
            have hiff := hnm (w - n) hj hor a b hins
            have hnea : (singleSet n gs a).Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              intro hea
              have heb : singleSet n gs b = ∅ := hiff.mp hea
              rw [hsunion, hea, heb, Finset.empty_union] at hne
              exact Finset.not_nonempty_empty hne
            have hneb : (singleSet n gs b).Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              intro heb
              have hea : singleSet n gs a = ∅ := hiff.mpr heb
              rw [hsunion, hea, heb, Finset.empty_union] at hne
              exact Finset.not_nonempty_empty hne
            rw [hsunion]
            rcases hx with hxa | hxb
            · obtain ⟨v, hv, hxv⟩ := ih a (by omega) hnea x hxa
              exact ⟨v, Finset.mem_union_left _ hv, hxv⟩
            · obtain ⟨v, hv, hxv⟩ := ih b (by omega) hneb x hxb
              exact ⟨v, Finset.mem_union_right _ hv, hxv⟩
          · rw [hins] at hlen; simp at hlen

private lemma c4_unique_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {S : Finset (Fin n)} (hS : 2 ≤ S.card) {c1 c2 : Fin n}
    (hc1 : ∀ v ∈ S, G.Adj c1 v) (hc2 : ∀ v ∈ S, G.Adj c2 v) : c1 = c2 := by
  by_contra hne
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  exact hc4 c1 b c2 d hne hbd ⟨hc1 b hb, (hc2 b hb).symm, hc2 d hd, (hc1 d hd).symm⟩

private lemma and_star_structure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {gs : List Gate} (hwf : Wf n gs) (hab : AllAndBelow G gs) (hnm : NoMixedOr (n := n) gs)
    {j a b : ℕ} (hj : j < gs.length) (hop : gs[j].op = GateOp.and) (hins : gs[j].inputs = [a, b])
    (hnea : (singleSet n gs a).Nonempty) (hneb : (singleSet n gs b).Nonempty) :
    (∀ u ∈ singleSet n gs a, ∀ v ∈ singleSet n gs b, G.Adj u v) ∧
    ((∃ c : Fin n, singleSet n gs a = {c} ∧
      ∀ e : Sym2 (Fin n), e ∈ edgeSet G gs (n + j) ↔ ∃ v ∈ singleSet n gs b, e = s(c, v)) ∨
     (∃ c : Fin n, singleSet n gs b = {c} ∧
      ∀ e : Sym2 (Fin n), e ∈ edgeSet G gs (n + j) ↔ ∃ v ∈ singleSet n gs a, e = s(c, v))) := by
  have hval : ∀ x : Fin n → Bool, wval gs x (n + j) = (wval gs x a && wval gs x b) := by
    intro x
    rw [wval_gate_wf hwf x j hj, hop, hins]
    simp [GateOp.eval]
  have hadj : ∀ u ∈ singleSet n gs a, ∀ v ∈ singleSet n gs b, G.Adj u v := by
    intro u hu v hv
    have ha1 : wval gs (edgeVec u v) a = true :=
      wval_mono_true hwf (x := singleVec u) (y := edgeVec u v)
        (fun k hk => by simp only [singleVec, edgeVec, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
        (mem_singleSet gs a u |>.mp hu)
    have hb1 : wval gs (edgeVec u v) b = true :=
      wval_mono_true hwf (x := singleVec v) (y := edgeVec u v)
        (fun k hk => by simp only [singleVec, edgeVec, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
        (mem_singleSet gs b v |>.mp hv)
    have hboth : wval gs (edgeVec u v) (n + j) = true := by rw [hval, ha1, hb1]; rfl
    have hf := hab j hj hop (edgeVec u v) hboth
    rw [edgeFun_true_iff] at hf
    obtain ⟨p, q, hpq, hp, hq⟩ := hf
    simp only [edgeVec, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd hpq ((fun h => G.ne_of_adj h rfl))
    · exact hpq
    · exact hpq.symm
    · exact absurd hpq ((fun h => G.ne_of_adj h rfl))
  have hdisj : Disjoint (singleSet n gs a) (singleSet n gs b) := by
    rw [Finset.disjoint_left]
    intro u hua hub
    exact G.ne_of_adj (hadj u hua u hub) rfl
  have hedge_iff : ∀ u v : Fin n, s(u, v) ∈ edgeSet G gs (n + j) ↔
      (u ∈ singleSet n gs a ∧ v ∈ singleSet n gs b) ∨ (v ∈ singleSet n gs a ∧ u ∈ singleSet n gs b) := by
    intro u v
    rw [mem_edgeSet_iff, hval, Bool.and_eq_true]
    constructor
    · rintro ⟨_, hwa, hwb⟩
      obtain ⟨p, hp, hpu⟩ := val_imp_mem_singleSet G hwf hab hnm a hnea (edgeVec u v) hwa
      obtain ⟨q, hq, hqv⟩ := val_imp_mem_singleSet G hwf hab hnm b hneb (edgeVec u v) hwb
      simp only [edgeVec, decide_eq_true_eq] at hpu hqv
      rcases hpu with rfl | rfl <;> rcases hqv with rfl | rfl
      · exact absurd hp (Finset.disjoint_right.mp hdisj hq)
      · exact Or.inl ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hq⟩
      · exact absurd hp (Finset.disjoint_right.mp hdisj hq)
    · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
      · refine ⟨hadj u hu v hv, ?_, ?_⟩
        · exact wval_mono_true hwf (x := singleVec u) (y := edgeVec u v)
            (fun k hk => by simp only [singleVec, edgeVec, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
            ((mem_singleSet gs a u).mp hu)
        · exact wval_mono_true hwf (x := singleVec v) (y := edgeVec u v)
            (fun k hk => by simp only [singleVec, edgeVec, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
            ((mem_singleSet gs b v).mp hv)
      · refine ⟨(hadj v hv u hu).symm, ?_, ?_⟩
        · exact wval_mono_true hwf (x := singleVec v) (y := edgeVec u v)
            (fun k hk => by simp only [singleVec, edgeVec, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
            ((mem_singleSet gs a v).mp hv)
        · exact wval_mono_true hwf (x := singleVec u) (y := edgeVec u v)
            (fun k hk => by simp only [singleVec, edgeVec, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
            ((mem_singleSet gs b u).mp hu)
  have hcard : (singleSet n gs a).card = 1 ∨ (singleSet n gs b).card = 1 := by
    by_contra hnot
    push Not at hnot
    have hca : 1 < (singleSet n gs a).card := by
      have := Finset.card_pos.mpr hnea; omega
    have hcb : 1 < (singleSet n gs b).card := by
      have := Finset.card_pos.mpr hneb; omega
    obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hca
    obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp hcb
    exact hc4 u1 v1 u2 v2 hu12 hv12
      ⟨hadj u1 hu1 v1 hv1, (hadj u2 hu2 v1 hv1).symm, hadj u2 hu2 v2 hv2, (hadj u1 hu1 v2 hv2).symm⟩
  refine ⟨hadj, ?_⟩
  rcases hcard with hca | hcb
  · left
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hca
    refine ⟨c, hc, fun e => ?_⟩
    induction e using Sym2.ind with
    | _ u v =>
      rw [hedge_iff, hc]
      simp only [Finset.mem_singleton]
      constructor
      · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
        · exact ⟨v, hv, rfl⟩
        · exact ⟨u, hu, Sym2.eq_swap⟩
      · rintro ⟨w, hw, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, hw⟩
        · exact Or.inr ⟨rfl, hw⟩
  · right
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcb
    refine ⟨c, hc, fun e => ?_⟩
    induction e using Sym2.ind with
    | _ u v =>
      rw [hedge_iff, hc]
      simp only [Finset.mem_singleton]
      constructor
      · rintro (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
        · exact ⟨u, hu, Sym2.eq_swap⟩
        · exact ⟨v, hv, rfl⟩
      · rintro ⟨w, hw, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨hw, rfl⟩
        · exact Or.inl ⟨hw, rfl⟩

private lemma phase3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {gs : List Gate} {out : ℕ} (hwf : Wf n gs) (hab : AllAndBelow G gs) (hnm : NoMixedOr (n := n) gs)
    (hcomp : ∀ x, wval gs x out = edgeFun G x) (hout : out < n + gs.length)
    (hEne : G.edgeFinset.Nonempty) :
    ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ gs.length + 1 := by
  classical
  -- Step 1: Partition gate indices into AND gates and OR gates
  let andIdx : Finset (Fin gs.length) := Finset.univ.filter (fun j => gs[j.val].op = GateOp.and)
  let orIdx : Finset (Fin gs.length) := Finset.univ.filter (fun j => gs[j.val].op = GateOp.or)
  have hpart : andIdx.card + orIdx.card = gs.length := by
    have hdisj : Disjoint andIdx orIdx := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [andIdx, orIdx, Finset.mem_filter] at hj1 hj2
      rw [hj1.2] at hj2; cases hj2.2
    have hunion : andIdx ∪ orIdx = Finset.univ := by
      ext j
      simp only [andIdx, orIdx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      exact (hwf.1 _ (List.getElem_mem j.isLt)).1
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  -- Step 2: Build vertex cover T of size ≤ andIdx.card from productive star AND gates
  let centerOpt (j : Fin gs.length) : Option (Fin n) :=
    match h : gs[j.val] with
    | ⟨GateOp.and, [a, b]⟩ =>
      if hne : (singleSet n gs a).Nonempty ∧ (singleSet n gs b).Nonempty then
        if h1 : ∃ c : Fin n, singleSet n gs a = {c} ∧
            ∀ e : Sym2 (Fin n), e ∈ edgeSet G gs (n + j.val) ↔ ∃ v ∈ singleSet n gs b, e = s(c, v) then
          some (Classical.choose h1)
        else
          let hst := (and_star_structure G hc4 hwf hab hnm j.isLt (by rw [h]) (by rw [h]) hne.1 hne.2).2
          some (Classical.choose (hst.resolve_left h1))
      else none
    | _ => none
  let T : Finset (Fin n) := andIdx.biUnion (fun j => (centerOpt j).toFinset)
  have hT_card : T.card ≤ andIdx.card := by
    have h1 : T.card ≤ ∑ j ∈ andIdx, ((centerOpt j).toFinset).card := Finset.card_biUnion_le
    have h2 : ∑ j ∈ andIdx, ((centerOpt j).toFinset).card ≤ ∑ _j ∈ andIdx, 1 := by
      apply Finset.sum_le_sum
      intro j _
      cases centerOpt j <;> simp
    have h3 : ∑ _j ∈ andIdx, 1 = andIdx.card := by simp
    omega
  have hstar_cover : ∀ (j : Fin gs.length) (a b : ℕ), gs[j.val].op = GateOp.and →
      gs[j.val].inputs = [a, b] → (singleSet n gs a).Nonempty → (singleSet n gs b).Nonempty →
      ∀ e ∈ edgeSet G gs (n + j.val), ∃ t ∈ T, t ∈ e := by
    intro j a b hop hins hnea hneb e he
    have hjA : j ∈ andIdx := by simp [andIdx, hop]
    have hgate : gs[j.val] = ⟨GateOp.and, [a, b]⟩ := by
      cases h : gs[j.val]
      simp_all
    have hne : (singleSet n gs a).Nonempty ∧ (singleSet n gs b).Nonempty := ⟨hnea, hneb⟩
    have hst := (and_star_structure G hc4 hwf hab hnm j.isLt hop hins hnea hneb).2
    by_cases h1 : ∃ c : Fin n, singleSet n gs a = {c} ∧
        ∀ e : Sym2 (Fin n), e ∈ edgeSet G gs (n + j.val) ↔ ∃ v ∈ singleSet n gs b, e = s(c, v)
    · set c := Classical.choose h1
      have hc := Classical.choose_spec h1
      obtain ⟨v, _, rfl⟩ := (hc.2 e).mp he
      have hcOpt : centerOpt j = some c := by
        dsimp only [centerOpt]
        split
        · rename_i a' b' hmatch
          rw [hgate] at hmatch
          cases hmatch
          rw [dite_eq_left hne, dite_eq_left h1]
        · rename_i hnot
          exact absurd hgate (hnot a b)
      have hcT : c ∈ T := by
        rw [Finset.mem_biUnion]
        exact ⟨j, hjA, by rw [hcOpt]; simp⟩
      exact ⟨c, hcT, Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · have h2 := hst.resolve_left h1
      set c := Classical.choose h2
      have hc := Classical.choose_spec h2
      obtain ⟨v, _, rfl⟩ := (hc.2 e).mp he
      have hcOpt : centerOpt j = some c := by
        dsimp only [centerOpt]
        split
        · rename_i a' b' hmatch
          rw [hgate] at hmatch
          cases hmatch
          rw [dite_eq_left hne, dite_eq_right h1]
        · rename_i hnot
          exact absurd hgate (hnot a b)
      have hcT : c ∈ T := by
        rw [Finset.mem_biUnion]
        exact ⟨j, hjA, by rw [hcOpt]; simp⟩
      exact ⟨c, hcT, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  have hcover_wire : ∀ w, w < n + gs.length → singleSet n gs w = ∅ →
      ∀ e ∈ edgeSet G gs w, ∃ t ∈ T, t ∈ e := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hempty e he
      by_cases hlt : w < n
      · exfalso
        have : (⟨w, hlt⟩ : Fin n) ∈ singleSet n gs w := by rw [singleSet_input gs w hlt]; simp
        rw [hempty] at this; exact Finset.notMem_empty _ this
      · have hj : w - n < gs.length := by omega
        have hweq : w = n + (w - n) := by omega
        rw [hweq] at hempty he
        have hlen := (hwf.1 _ (List.getElem_mem hj)).2
        rcases (hwf.1 _ (List.getElem_mem hj)).1 with hand | hor
        · rcases hins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · exfalso
            have h0 : wval gs (fun _ : Fin n => false) (n + (w - n)) = true := by
              rw [wval_gate_wf hwf _ (w - n) hj, hand, hins]; simp [GateOp.eval]
            have hf := hab (w - n) hj hand (fun _ => false) h0
            rw [edgeFun_true_iff] at hf
            obtain ⟨_, _, _, hfalse, _⟩ := hf; exact Bool.noConfusion hfalse
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hveq : ∀ x : Fin n → Bool, wval gs x (n + (w - n)) = wval gs x a := fun x => by
              rw [wval_gate_wf hwf x (w - n) hj, hand, hins]; simp [GateOp.eval]
            have hsa : singleSet n gs a = ∅ := by
              ext v; simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv; rw [← hveq] at hv
              have : v ∈ singleSet n gs (n + (w - n)) := (mem_singleSet _ _ _).mpr hv
              rw [hempty] at this; exact Finset.notMem_empty _ this
            have hea : e ∈ edgeSet G gs a := by
              induction e using Sym2.ind with
              | _ u v =>
                rw [mem_edgeSet_iff] at he ⊢
                exact ⟨he.1, (hveq _).symm.trans he.2⟩
            exact ih a (by omega) (by omega) hsa e hea
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [hins]; simp)
            by_cases hsa : singleSet n gs a = ∅
            · have hea : e ∈ edgeSet G gs a := by
                induction e using Sym2.ind with
                | _ u v =>
                  rw [mem_edgeSet_iff] at he ⊢
                  have hval := he.2
                  rw [wval_gate_wf hwf _ (w - n) hj, hand, hins] at hval
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                    Bool.and_true, Bool.and_eq_true] at hval
                  exact ⟨he.1, hval.1⟩
              exact ih a (by omega) (by omega) hsa e hea
            · by_cases hsb : singleSet n gs b = ∅
              · have heb : e ∈ edgeSet G gs b := by
                  induction e using Sym2.ind with
                  | _ u v =>
                    rw [mem_edgeSet_iff] at he ⊢
                    have hval := he.2
                    rw [wval_gate_wf hwf _ (w - n) hj, hand, hins] at hval
                    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                      Bool.and_true, Bool.and_eq_true] at hval
                    exact ⟨he.1, hval.2⟩
                exact ih b (by omega) (by omega) hsb e heb
              · exact hstar_cover ⟨w - n, hj⟩ a b hand hins
                  (Finset.nonempty_iff_ne_empty.mpr hsa)
                  (Finset.nonempty_iff_ne_empty.mpr hsb) e he
          · rw [hins] at hlen; simp at hlen
        · rcases hins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · exfalso
            induction e using Sym2.ind with
            | _ u v =>
              rw [mem_edgeSet_iff, wval_gate_wf hwf _ (w - n) hj, hor, hins] at he
              simp [GateOp.eval] at he
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hveq : ∀ x : Fin n → Bool, wval gs x (n + (w - n)) = wval gs x a := fun x => by
              rw [wval_gate_wf hwf x (w - n) hj, hor, hins]; simp [GateOp.eval]
            have hsa : singleSet n gs a = ∅ := by
              ext v; simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv; rw [← hveq] at hv
              have : v ∈ singleSet n gs (n + (w - n)) := (mem_singleSet _ _ _).mpr hv
              rw [hempty] at this; exact Finset.notMem_empty _ this
            have hea : e ∈ edgeSet G gs a := by
              induction e using Sym2.ind with
              | _ u v =>
                rw [mem_edgeSet_iff] at he ⊢
                exact ⟨he.1, (hveq _).symm.trans he.2⟩
            exact ih a (by omega) (by omega) hsa e hea
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [hins]; simp)
            have hsunion : singleSet n gs (n + (w - n)) = singleSet n gs a ∪ singleSet n gs b := by
              ext v; simp only [Finset.mem_union, mem_singleSet]
              rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]; simp [GateOp.eval]
            rw [hsunion, Finset.union_eq_empty] at hempty
            have hmem : e ∈ edgeSet G gs a ∨ e ∈ edgeSet G gs b := by
              induction e using Sym2.ind with
              | _ u v =>
                rw [mem_edgeSet_iff] at he
                rw [mem_edgeSet_iff, mem_edgeSet_iff]
                have hval := he.2
                rw [wval_gate_wf hwf _ (w - n) hj, hor, hins] at hval
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  Bool.or_false, Bool.or_eq_true] at hval
                rcases hval with h1 | h2
                · exact Or.inl ⟨he.1, h1⟩
                · exact Or.inr ⟨he.1, h2⟩
            rcases hmem with hea | heb
            · exact ih a (by omega) (by omega) hempty.1 e hea
            · exact ih b (by omega) (by omega) hempty.2 e heb
          · rw [hins] at hlen; simp at hlen
  have hT_cover : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    have hout_empty : singleSet n gs out = ∅ := by
      apply singleSet_belowF G; intro x hx; rw [hcomp x] at hx; exact hx
    have he : s(u, v) ∈ edgeSet G gs out := by
      rw [mem_edgeSet_iff]; exact ⟨huv, (hcomp _).trans (edgeFun_edge G huv)⟩
    obtain ⟨t, htT, hte⟩ := hcover_wire out hout hout_empty s(u, v) he
    simp only [Sym2.mem_iff] at hte
    rcases hte with rfl | rfl
    · exact Or.inl htT
    · exact Or.inr htT
  -- Step 3: Build edge-merging graph H with ≤ orIdx.card edges
  let orEdge (j : Fin gs.length) : Option (Sym2 (Fin n) × Sym2 (Fin n)) :=
    match gs[j.val] with
    | ⟨GateOp.or, [a, b]⟩ =>
      if hL : (singleSet n gs a).Nonempty ∧ (singleSet n gs b).Nonempty ∧
          ∃ c : Fin n, ∀ v ∈ singleSet n gs (n + j.val), G.Adj c v then
        some (s(Classical.choose hL.2.2, Classical.choose hL.1),
              s(Classical.choose hL.2.2, Classical.choose hL.2.1))
      else if hB : (edgeSet G gs a).Nonempty ∧ (edgeSet G gs b).Nonempty then
        some (Classical.choose hB.1, Classical.choose hB.2)
      else none
    | _ => none
  let orList : List (Fin gs.length) := (List.finRange gs.length).filter (fun j => decide (gs[j.val].op = GateOp.or))
  let H_edges : List (Sym2 (Fin n) × Sym2 (Fin n)) := orList.filterMap orEdge
  have hH_len : H_edges.length ≤ orIdx.card := by
    have h1 : H_edges.length ≤ orList.length := List.length_filterMap_le _ _
    have h2 : orList.length = orIdx.card := by
      have hnd : orList.Nodup := (List.nodup_finRange gs.length).filter _
      rw [← List.toFinset_card_of_nodup hnd]
      congr 1
      ext j
      simp [orList, orIdx]
    omega
  have hmem_H : ∀ (j : Fin gs.length) (p : Sym2 (Fin n) × Sym2 (Fin n)),
      gs[j.val].op = GateOp.or → orEdge j = some p → p ∈ H_edges := by
    intro j p hor heq
    rw [List.mem_filterMap]
    refine ⟨j, ?_, heq⟩
    simp [orList, hor]
  -- InvL: For every Type-L wire w and common neighbor c of singleSet n gs w, Star(c, singleSet n gs w) is connected in H
  have hInvL : ∀ w, w < n + gs.length → (singleSet n gs w).Nonempty →
      ∀ c : Fin n, (∀ v ∈ singleSet n gs w, G.Adj c v) →
      ∀ x ∈ singleSet n gs w, ∀ y ∈ singleSet n gs w, Reach H_edges s(c, x) s(c, y) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hne c hc x hx y hy
      by_cases hlt : w < n
      · rw [singleSet_input gs w hlt] at hx hy
        simp only [Finset.mem_singleton] at hx hy
        rw [hx, hy]; exact reach_refl _ _
      · have hj : w - n < gs.length := by omega
        have hweq : w = n + (w - n) := by omega
        rw [hweq] at hne hc hx hy
        rcases (hwf.1 _ (List.getElem_mem hj)).1 with hand | hor
        · exfalso
          have hempty := singleSet_belowF G (hab (w - n) hj hand)
          rw [hempty] at hne; exact Finset.not_nonempty_empty hne
        · have hlen := (hwf.1 _ (List.getElem_mem hj)).2
          rcases hins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
          · exfalso
            have hempty : singleSet n gs (n + (w - n)) = ∅ := by
              ext v; simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]; simp [GateOp.eval]
            rw [hempty] at hne; exact Finset.not_nonempty_empty hne
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hseq : singleSet n gs (n + (w - n)) = singleSet n gs a := by
              ext v; simp only [mem_singleSet]
              rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]; simp [GateOp.eval]
            rw [hseq] at hne hc hx hy
            exact ih a (by omega) (by omega) hne c hc x hx y hy
          · by_cases hxy : x = y
            · subst hxy; exact reach_refl _ _
            · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
              have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [hins]; simp)
              have hsunion : singleSet n gs (n + (w - n)) = singleSet n gs a ∪ singleSet n gs b := by
                ext v; simp only [Finset.mem_union, mem_singleSet]
                rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]; simp [GateOp.eval]
              have hiff := hnm (w - n) hj hor a b hins
              have hnea : (singleSet n gs a).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hea
                have heb := hiff.mp hea
                rw [hsunion, hea, heb, Finset.empty_union] at hne
                exact Finset.not_nonempty_empty hne
              have hneb : (singleSet n gs b).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro heb
                have hea := hiff.mpr heb
                rw [hsunion, hea, heb, Finset.empty_union] at hne
                exact Finset.not_nonempty_empty hne
              have hca : ∀ v ∈ singleSet n gs a, G.Adj c v := fun v hv =>
                hc v (by rw [hsunion]; exact Finset.mem_union_left _ hv)
              have hcb : ∀ v ∈ singleSet n gs b, G.Adj c v := fun v hv =>
                hc v (by rw [hsunion]; exact Finset.mem_union_right _ hv)
              have hcard2 : 2 ≤ (singleSet n gs (n + (w - n))).card := by
                have hlt1 : 1 < (singleSet n gs (n + (w - n))).card :=
                  Finset.one_lt_card.mpr ⟨x, hx, y, hy, hxy⟩
                omega
              -- Extract the edge added by orEdge ⟨w - n, hj⟩
              let jf : Fin gs.length := ⟨w - n, hj⟩
              have hgate : gs[jf.val] = ⟨GateOp.or, [a, b]⟩ := by
                change gs[w - n] = ⟨GateOp.or, [a, b]⟩
                cases hg : gs[w - n] with
                | mk op ins =>
                  rw [hg] at hor hins
                  dsimp only at hor hins
                  rw [hor, hins]
              have hLcond : (singleSet n gs a).Nonempty ∧ (singleSet n gs b).Nonempty ∧
                  ∃ c' : Fin n, ∀ v ∈ singleSet n gs (n + jf.val), G.Adj c' v :=
                ⟨hnea, hneb, c, hc⟩
              set u0 := Classical.choose hLcond.1
              set v0 := Classical.choose hLcond.2.1
              set c0 := Classical.choose hLcond.2.2
              have hu0 : u0 ∈ singleSet n gs a := Classical.choose_spec hLcond.1
              have hv0 : v0 ∈ singleSet n gs b := Classical.choose_spec hLcond.2.1
              have hc0 : ∀ v ∈ singleSet n gs (n + (w - n)), G.Adj c0 v :=
                Classical.choose_spec hLcond.2.2
              have hc0_eq : c0 = c := c4_unique_common_neighbor G hc4 hcard2 hc0 hc
              have hedge_mem : (s(c0, u0), s(c0, v0)) ∈ H_edges := by
                apply hmem_H jf _ hor
                dsimp only [orEdge]
                rw [hgate]
                dsimp only
                rw [dite_eq_left hLcond]
              rw [hc0_eq] at hedge_mem
              have huv_reach : Reach H_edges s(c, u0) s(c, v0) := reach_of_mem hedge_mem
              rw [hsunion] at hx hy
              rcases Finset.mem_union.mp hx with hxa | hxb <;>
              rcases Finset.mem_union.mp hy with hya | hyb
              · exact ih a (by omega) (by omega) hnea c hca x hxa y hya
              · exact reach_trans
                  (ih a (by omega) (by omega) hnea c hca x hxa u0 hu0)
                  (reach_trans huv_reach
                    (ih b (by omega) (by omega) hneb c hcb v0 hv0 y hyb))
              · exact reach_trans
                  (ih b (by omega) (by omega) hneb c hcb x hxb v0 hv0)
                  (reach_trans (reach_symm huv_reach)
                    (ih a (by omega) (by omega) hnea c hca u0 hu0 y hya))
              · exact ih b (by omega) (by omega) hneb c hcb x hxb y hyb
          · rw [hins] at hlen; simp at hlen
  -- InvB: For every Type-B wire w, edgeSet G gs w is connected in H
  have hInvB : ∀ w, w < n + gs.length → singleSet n gs w = ∅ →
      ∀ e1 ∈ edgeSet G gs w, ∀ e2 ∈ edgeSet G gs w, Reach H_edges e1 e2 := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hempty e1 he1 e2 he2
      by_cases hlt : w < n
      · exfalso
        have : (⟨w, hlt⟩ : Fin n) ∈ singleSet n gs w := by rw [singleSet_input gs w hlt]; simp
        rw [hempty] at this; exact Finset.notMem_empty _ this
      · have hj : w - n < gs.length := by omega
        have hweq : w = n + (w - n) := by omega
        rw [hweq] at hempty he1 he2
        have hlen := (hwf.1 _ (List.getElem_mem hj)).2
        rcases (hwf.1 _ (List.getElem_mem hj)).1 with hand | hor
        · rcases hins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
          · exfalso
            have h0 : wval gs (fun _ : Fin n => false) (n + (w - n)) = true := by
              rw [wval_gate_wf hwf _ (w - n) hj, hand, hins]; simp [GateOp.eval]
            have hf := hab (w - n) hj hand (fun _ => false) h0
            rw [edgeFun_true_iff] at hf
            obtain ⟨_, _, _, hfalse, _⟩ := hf; exact Bool.noConfusion hfalse
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hveq : ∀ x : Fin n → Bool, wval gs x (n + (w - n)) = wval gs x a := fun x => by
              rw [wval_gate_wf hwf x (w - n) hj, hand, hins]; simp [GateOp.eval]
            have hsa : singleSet n gs a = ∅ := by
              ext v; simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv; rw [← hveq] at hv
              have : v ∈ singleSet n gs (n + (w - n)) := (mem_singleSet _ _ _).mpr hv
              rw [hempty] at this; exact Finset.notMem_empty _ this
            have hesub : ∀ e, e ∈ edgeSet G gs (n + (w - n)) → e ∈ edgeSet G gs a := fun e he => by
              induction e using Sym2.ind with
              | _ u v =>
                rw [mem_edgeSet_iff] at he ⊢; exact ⟨he.1, (hveq _).symm.trans he.2⟩
            exact ih a (by omega) (by omega) hsa e1 (hesub e1 he1) e2 (hesub e2 he2)
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [hins]; simp)
            by_cases hsa : singleSet n gs a = ∅
            · have hesub : ∀ e, e ∈ edgeSet G gs (n + (w - n)) → e ∈ edgeSet G gs a := fun e he => by
                induction e using Sym2.ind with
                | _ u v =>
                  rw [mem_edgeSet_iff] at he ⊢
                  have hval := he.2
                  rw [wval_gate_wf hwf _ (w - n) hj, hand, hins] at hval
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                    Bool.and_true, Bool.and_eq_true] at hval
                  exact ⟨he.1, hval.1⟩
              exact ih a (by omega) (by omega) hsa e1 (hesub e1 he1) e2 (hesub e2 he2)
            · by_cases hsb : singleSet n gs b = ∅
              · have hesub : ∀ e, e ∈ edgeSet G gs (n + (w - n)) → e ∈ edgeSet G gs b := fun e he => by
                  induction e using Sym2.ind with
                  | _ u v =>
                    rw [mem_edgeSet_iff] at he ⊢
                    have hval := he.2
                    rw [wval_gate_wf hwf _ (w - n) hj, hand, hins] at hval
                    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                      Bool.and_true, Bool.and_eq_true] at hval
                    exact ⟨he.1, hval.2⟩
                exact ih b (by omega) (by omega) hsb e1 (hesub e1 he1) e2 (hesub e2 he2)
              · have hnea := Finset.nonempty_iff_ne_empty.mpr hsa
                have hneb := Finset.nonempty_iff_ne_empty.mpr hsb
                obtain ⟨hadj, hst⟩ := and_star_structure G hc4 hwf hab hnm hj hand hins hnea hneb
                rcases hst with ⟨c, hca, hiff⟩ | ⟨c, hcb, hiff⟩
                · obtain ⟨v1, hv1, rfl⟩ := (hiff e1).mp he1
                  obtain ⟨v2, hv2, rfl⟩ := (hiff e2).mp he2
                  have hcb_adj : ∀ v ∈ singleSet n gs b, G.Adj c v := fun v hv =>
                    hadj c (by rw [hca]; simp) v hv
                  exact hInvL b (by omega) hneb c hcb_adj v1 hv1 v2 hv2
                · obtain ⟨v1, hv1, rfl⟩ := (hiff e1).mp he1
                  obtain ⟨v2, hv2, rfl⟩ := (hiff e2).mp he2
                  have hca_adj : ∀ v ∈ singleSet n gs a, G.Adj c v := fun v hv =>
                    (hadj v hv c (by rw [hcb]; simp)).symm
                  exact hInvL a (by omega) hnea c hca_adj v1 hv1 v2 hv2
          · rw [hins] at hlen; simp at hlen
        · rcases hins : gs[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
          · exfalso
            induction e1 using Sym2.ind with
            | _ u v =>
              rw [mem_edgeSet_iff, wval_gate_wf hwf _ (w - n) hj, hor, hins] at he1
              simp [GateOp.eval] at he1
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hveq : ∀ x : Fin n → Bool, wval gs x (n + (w - n)) = wval gs x a := fun x => by
              rw [wval_gate_wf hwf x (w - n) hj, hor, hins]; simp [GateOp.eval]
            have hsa : singleSet n gs a = ∅ := by
              ext v; simp only [mem_singleSet, Finset.notMem_empty, iff_false]
              intro hv; rw [← hveq] at hv
              have : v ∈ singleSet n gs (n + (w - n)) := (mem_singleSet _ _ _).mpr hv
              rw [hempty] at this; exact Finset.notMem_empty _ this
            have hesub : ∀ e, e ∈ edgeSet G gs (n + (w - n)) → e ∈ edgeSet G gs a := fun e he => by
              induction e using Sym2.ind with
              | _ u v =>
                rw [mem_edgeSet_iff] at he ⊢; exact ⟨he.1, (hveq _).symm.trans he.2⟩
            exact ih a (by omega) (by omega) hsa e1 (hesub e1 he1) e2 (hesub e2 he2)
          · have ha : a < n + (w - n) := hwf.2 (w - n) hj a (by rw [hins]; simp)
            have hb : b < n + (w - n) := hwf.2 (w - n) hj b (by rw [hins]; simp)
            have hsunion : singleSet n gs (n + (w - n)) = singleSet n gs a ∪ singleSet n gs b := by
              ext v; simp only [Finset.mem_union, mem_singleSet]
              rw [wval_gate_wf hwf _ (w - n) hj, hor, hins]; simp [GateOp.eval]
            rw [hsunion, Finset.union_eq_empty] at hempty
            have hmem : ∀ e, e ∈ edgeSet G gs (n + (w - n)) → e ∈ edgeSet G gs a ∨ e ∈ edgeSet G gs b := by
              intro e he
              induction e using Sym2.ind with
              | _ u v =>
                rw [mem_edgeSet_iff] at he
                rw [mem_edgeSet_iff, mem_edgeSet_iff]
                have hval := he.2
                rw [wval_gate_wf hwf _ (w - n) hj, hor, hins] at hval
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  Bool.or_false, Bool.or_eq_true] at hval
                rcases hval with h1 | h2
                · exact Or.inl ⟨he.1, h1⟩
                · exact Or.inr ⟨he.1, h2⟩
            rcases hmem e1 he1 with h1a | h1b <;> rcases hmem e2 he2 with h2a | h2b
            · exact ih a (by omega) (by omega) hempty.1 e1 h1a e2 h2a
            · -- Connect edgeSet a and edgeSet b via orEdge ⟨w - n, hj⟩!
              let jf : Fin gs.length := ⟨w - n, hj⟩
              have hgate : gs[jf.val] = ⟨GateOp.or, [a, b]⟩ := by
                change gs[w - n] = ⟨GateOp.or, [a, b]⟩
                cases hg : gs[w - n] with
                | mk op ins =>
                  rw [hg] at hor hins
                  dsimp only at hor hins
                  rw [hor, hins]
              have hnL : ¬ ((singleSet n gs a).Nonempty ∧ (singleSet n gs b).Nonempty ∧
                  ∃ c : Fin n, ∀ v ∈ singleSet n gs (n + jf.val), G.Adj c v) := by
                rw [hempty.1]; simp
              have hBcond : (edgeSet G gs a).Nonempty ∧ (edgeSet G gs b).Nonempty :=
                ⟨⟨e1, h1a⟩, ⟨e2, h2b⟩⟩
              set ea0 := Classical.choose hBcond.1
              set eb0 := Classical.choose hBcond.2
              have hea0 : ea0 ∈ edgeSet G gs a := Classical.choose_spec hBcond.1
              have heb0 : eb0 ∈ edgeSet G gs b := Classical.choose_spec hBcond.2
              have hedge_mem : (ea0, eb0) ∈ H_edges := by
                apply hmem_H jf _ hor
                dsimp only [orEdge]
                rw [hgate]
                dsimp only
                rw [dite_eq_right hnL, dite_eq_left hBcond]
              exact reach_trans
                (ih a (by omega) (by omega) hempty.1 e1 h1a ea0 hea0)
                (reach_trans (reach_of_mem hedge_mem)
                  (ih b (by omega) (by omega) hempty.2 eb0 heb0 e2 h2b))
            · let jf : Fin gs.length := ⟨w - n, hj⟩
              have hgate : gs[jf.val] = ⟨GateOp.or, [a, b]⟩ := by
                change gs[w - n] = ⟨GateOp.or, [a, b]⟩
                cases hg : gs[w - n] with
                | mk op ins =>
                  rw [hg] at hor hins
                  dsimp only at hor hins
                  rw [hor, hins]
              have hnL : ¬ ((singleSet n gs a).Nonempty ∧ (singleSet n gs b).Nonempty ∧
                  ∃ c : Fin n, ∀ v ∈ singleSet n gs (n + jf.val), G.Adj c v) := by
                rw [hempty.1]; simp
              have hBcond : (edgeSet G gs a).Nonempty ∧ (edgeSet G gs b).Nonempty :=
                ⟨⟨e2, h2a⟩, ⟨e1, h1b⟩⟩
              set ea0 := Classical.choose hBcond.1
              set eb0 := Classical.choose hBcond.2
              have hea0 : ea0 ∈ edgeSet G gs a := Classical.choose_spec hBcond.1
              have heb0 : eb0 ∈ edgeSet G gs b := Classical.choose_spec hBcond.2
              have hedge_mem : (ea0, eb0) ∈ H_edges := by
                apply hmem_H jf _ hor
                dsimp only [orEdge]
                rw [hgate]
                dsimp only
                rw [dite_eq_right hnL, dite_eq_left hBcond]
              exact reach_trans
                (ih b (by omega) (by omega) hempty.2 e1 h1b eb0 heb0)
                (reach_trans (reach_symm (reach_of_mem hedge_mem))
                  (ih a (by omega) (by omega) hempty.1 ea0 hea0 e2 h2a))
            · exact ih b (by omega) (by omega) hempty.2 e1 h1b e2 h2b
          · rw [hins] at hlen; simp at hlen
  -- Apply hInvB to out
  have hout_empty : singleSet n gs out = ∅ := by
    apply singleSet_belowF G; intro x hx; rw [hcomp x] at hx; exact hx
  have hout_edges : edgeSet G gs out = G.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet_iff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        and_iff_left_iff_imp]
      intro huv; rw [hcomp, edgeFun_edge G huv]
  have hconn : ∀ e1 ∈ G.edgeFinset, ∀ e2 ∈ G.edgeFinset, Reach H_edges e1 e2 := by
    intro e1 he1 e2 he2
    rw [← hout_edges] at he1 he2
    exact hInvB out hout hout_empty e1 he1 e2 he2
  have hE_le : G.edgeFinset.card ≤ H_edges.length + 1 :=
    card_le_edges_add_one G.edgeFinset H_edges hEne hconn
  refine ⟨T, hT_cover, ?_⟩
  omega

end Phase3Ledger

end PEqualNP.Outside.L_meta_4767

theorem PEqualNP.Outside.L_meta_4767 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
        (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true →
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨
          (∀ a b c d : Fin n, G.Adj a b → G.Adj c d →
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true →
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true →
            (a = c ∧ b = d) ∨ (a = d ∧ b = c))) →
        ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G _ hc4 gates out hmono hcomp hstar
  by_cases hEne : G.edgeFinset.Nonempty
  · -- Phase 0: clamp out-of-bounds inputs
    let gs0 := PEqualNP.Outside.L_meta_4767.clampList n gates
    have hlen0 : gs0.length = gates.length := PEqualNP.Outside.L_meta_4767.clampList_length n gates
    have hwf0 : PEqualNP.Outside.L_meta_4767.Wf n gs0 := PEqualNP.Outside.L_meta_4767.clampList_wf n gates
    have hval0 : ∀ (x : Fin n → Bool) (w : ℕ), PEqualNP.Outside.L_meta_4767.wval gs0 x w =
        PEqualNP.Outside.L_meta_4767.wval gates x w := by
      intro x w
      unfold PEqualNP.Outside.L_meta_4767.wval
      have hlen : (List.ofFn x).length = n := List.length_ofFn
      have h := PEqualNP.Outside.L_meta_4767.clampList_runWires gates hmono (List.ofFn x)
      rw [hlen] at h
      rw [h]
    have hcomp0 : ∀ x, PEqualNP.Outside.L_meta_4767.wval gs0 x out =
        PEqualNP.Outside.L_meta_4767.edgeFun G x := by
      intro x
      rw [hval0]
      exact hcomp x
    have hstar0 : ∀ (j : ℕ) (hj : j < gs0.length), gs0[j].op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.Outside.L_meta_4767.BelowF G gs0 (n + j) ∨
        PEqualNP.Outside.L_meta_4767.AtMostOneEdge G gs0 (n + j) := by
      intro j hj hop
      have hj' : j < gates.length := by rwa [hlen0] at hj
      rw [PEqualNP.Outside.L_meta_4767.clampList_getElem n gates j hj'] at hop
      have hop' : gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and :=
        PEqualNP.Outside.L_meta_4767.clampGate_op_and hop
      have hst := hstar ⟨j, hj'⟩ hop'
      rcases hst with hbel | hamo
      · left
        intro x hx
        rw [hval0] at hx
        rw [PEqualNP.Outside.L_meta_4767.edgeFun_true_iff]
        exact hbel x hx
      · right
        intro a b c d hab hcd h1 h2
        rw [hval0] at h1 h2
        exact hamo a b c d hab hcd h1 h2
    -- Phase 1: replace non-below-f AND gates
    obtain ⟨gs1, hlen1, hwf1, hcomp1, hab1⟩ :=
      PEqualNP.Outside.L_meta_4767.phase1 G hwf0 hcomp0 hstar0
    have hout1 : out < n + gs1.length := by
      by_contra hge
      obtain ⟨e, he⟩ := hEne
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        have hfalse := PEqualNP.Outside.L_meta_4767.wval_ge gs1
          (PEqualNP.Outside.L_meta_4767.edgeVec u v) out (by omega)
        rw [hcomp1, PEqualNP.Outside.L_meta_4767.edgeFun_edge G huv] at hfalse
        exact Bool.noConfusion hfalse
    -- Phase 2: eliminate mixed OR gates
    obtain ⟨gs2, out2, hlen2, hout2, hwf2, hab2, hcomp2, hnm2⟩ :=
      PEqualNP.Outside.L_meta_4767.phase2 G hwf1 hab1 hcomp1 hout1
    -- Phase 3: ledger
    obtain ⟨T, hTcov, hTbound⟩ :=
      PEqualNP.Outside.L_meta_4767.phase3 G hc4 hwf2 hab2 hnm2 hcomp2 hout2 hEne
    refine ⟨T, hTcov, ?_⟩
    omega
  · -- Empty graph case
    refine ⟨∅, ?_, ?_⟩
    · intro u v huv
      exfalso
      exact hEne ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv⟩
    · have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEne
      simp [hempty]
