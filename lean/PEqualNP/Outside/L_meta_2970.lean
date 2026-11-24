import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2970

def run {α : Type} (F : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) init

lemma run_cons {α : Type} (F : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    run F (g :: gs) init = run F gs (init ++ [F init g]) := rfl

lemma run_append {α : Type} (F : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    run F (gs ++ hs) init = run F hs (run F gs init) := by
  unfold run; rw [List.foldl_append]

lemma run_length {α : Type} (F : List α → Gate → α) (gs : List Gate) :
    ∀ init : List α, (run F gs init).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; simp [run]
  | cons g gs ih => intro init; rw [run_cons, ih]; simp; omega

lemma run_getD_lt {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (i : ℕ), i < init.length → (run F gs init).getD i d = init.getD i d := by
  induction gs with
  | nil => intro init i _; rfl
  | cons g gs ih =>
    intro init i hi
    rw [run_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_getD_gate {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (j : ℕ) (g : Gate), gs[j]? = some g →
      (run F gs init).getD (init.length + j) d = F (run F (gs.take j) init) g := by
  induction gs with
  | nil => intro init j g h; simp at h
  | cons g0 gs ih =>
    intro init j g h
    cases j with
    | zero =>
      simp at h
      subst h
      rw [run_cons, run_getD_lt F d gs _ _ (by simp)]
      simp [run]
    | succ j =>
      simp at h
      rw [run_cons]
      have h1 := ih (init ++ [F init g0]) j g h
      simp only [List.length_append, List.length_singleton] at h1
      rw [show init.length + (j + 1) = init.length + 1 + j by omega, h1]
      simp [run_cons]

lemma run_take_getD {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) (init : List α)
    (j i : ℕ) (hj : j ≤ gs.length) (hi : i < init.length + j) :
    (run F (gs.take j) init).getD i d = (run F gs init).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  rw [run_getD_lt F d (gs.drop j) (run F (gs.take j) init) i
    (by rw [run_length, List.length_take, Nat.min_eq_left hj]; exact hi)]

def lpF (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  match g.op with
  | GateOp.or => ((g.inputs.map fun i => w.getD i (false, false)).any (·.1),
      (g.inputs.map fun i => w.getD i (false, false)).any (·.2))
  | GateOp.and => (g.inputs.map fun i => w.getD i (false, false)).foldl
      (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def lpInit (N : ℕ) (x : List Bool) : List (Bool × Bool) :=
  (x.zipIdx).map fun (b, i) => if (decide (N ≤ i)) then (false, b) else (b, false)

lemma linearParts_eq (C : Circuit) (N : ℕ) (x : List Bool) :
    PEqualNP.ReadK.linearParts C (fun i => decide (N ≤ i)) x = run lpF C.gates (lpInit N x) := rfl

def wvF (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = run wvF C.gates x := rfl

def xs (N : ℕ) (x : ℕ → Bool) : List Bool := (List.range (N + N)).map x

def pP (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.ReadK.linearParts C (fun i => decide (N ≤ i)) (xs N x)).getD w (false, false)

def pA (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (pP C N x w).1

def pB (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (pP C N x w).2

def pV (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (C.wires (xs N x)).getD w false

lemma lpInit_length (N : ℕ) (x : List Bool) : (lpInit N x).length = x.length := by
  simp [lpInit]

lemma xs_length (N : ℕ) (x : ℕ → Bool) : (xs N x).length = N + N := by simp [xs]

lemma pP_input (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N + N) :
    pP C N x w = if N ≤ w then (false, x w) else (x w, false) := by
  unfold pP
  rw [linearParts_eq, run_getD_lt _ _ _ _ _ (by rw [lpInit_length, xs_length]; exact hw)]
  simp [lpInit, xs, List.getD_eq_getElem?_getD, hw]

lemma pV_input (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N + N) :
    pV C N x w = x w := by
  unfold pV
  rw [wires_eq, run_getD_lt _ _ _ _ _ (by rw [xs_length]; exact hw)]
  simp [xs, List.getD_eq_getElem?_getD, hw]

lemma pP_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pP C N x w = (false, false) := by
  unfold pP
  rw [linearParts_eq]
  apply List.getD_eq_default
  rw [run_length, lpInit_length, xs_length]; exact hw

lemma pV_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pV C N x w = false := by
  unfold pV
  rw [wires_eq]
  apply List.getD_eq_default
  rw [run_length, xs_length]; exact hw

lemma pP_gate (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pP C N x (N + N + j) = lpF [pP C N x a, pP C N x b] ⟨op, [0, 1]⟩ := by
  have hj : j ≤ C.gates.length := by
    have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have hl : (lpInit N (xs N x)).length = N + N := by rw [lpInit_length, xs_length]
  unfold pP
  rw [linearParts_eq]
  have h1 := run_getD_gate lpF (false, false) C.gates (lpInit N (xs N x)) j _ hg
  rw [hl] at h1
  rw [h1]
  have ea := run_take_getD lpF (false, false) C.gates (lpInit N (xs N x)) j a hj (by rw [hl]; exact ha)
  have eb := run_take_getD lpF (false, false) C.gates (lpInit N (xs N x)) j b hj (by rw [hl]; exact hb)
  simp only [List.getD_eq_getElem?_getD] at ea eb
  cases op <;> simp [lpF, ea, eb]

lemma pV_gate (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pV C N x (N + N + j) = op.eval [pV C N x a, pV C N x b] := by
  have hj : j ≤ C.gates.length := by
    have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have hl : (xs N x).length = N + N := xs_length N x
  unfold pV
  rw [wires_eq]
  have h1 := run_getD_gate wvF false C.gates (xs N x) j _ hg
  rw [hl] at h1
  rw [h1]
  have ea := run_take_getD wvF false C.gates (xs N x) j a hj (by rw [hl]; exact ha)
  have eb := run_take_getD wvF false C.gates (xs N x) j b hj (by rw [hl]; exact hb)
  simp only [List.getD_eq_getElem?_getD] at ea eb
  simp [wvF, ea, eb]

def Good (C : Circuit) (N : ℕ) : Prop :=
  (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
  (∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j) ∧
  ∀ g ∈ C.gates, g.inputs.length = 2

lemma gate_view (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < N + N + j ∧ b < N + N + j ∧
      (C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∨ C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) := by
  obtain ⟨h1, h2, h3⟩ := hG
  have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have e1 := h1 _ hm
  have e2 := h2 j hj
  have e3 := h3 _ hm
  rw [List.getD_eq_getElem _ _ hj] at e2
  rcases hgj : C.gates[j] with ⟨op, ins⟩
  rw [hgj] at e1 e2 e3
  simp only at e1 e2 e3
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp e3
  refine ⟨a, b, e2 a (by simp), e2 b (by simp), ?_⟩
  rw [List.getElem?_eq_getElem hj, hgj]
  rcases e1 with e1 | e1
  · right; rw [e1]
  · left; rw [e1]

lemma wire_kind (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) :
    w < N ∨ (N ≤ w ∧ w < N + N) ∨
    (∃ j a b, w = N + N + j ∧ a < N + N + j ∧ b < N + N + j ∧
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) ∨
    (∃ j a b, w = N + N + j ∧ a < N + N + j ∧ b < N + N + j ∧
      C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) ∨
    N + N + C.gates.length ≤ w := by
  by_cases h1 : w < N
  · exact Or.inl h1
  by_cases h2 : w < N + N
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)
  by_cases h3 : N + N + C.gates.length ≤ w
  · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  obtain ⟨a, b, ha, hb, h⟩ := gate_view C N hG (w - (N + N)) (by omega)
  have e : w = N + N + (w - (N + N)) := by omega
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl ⟨_, a, b, e, ha, hb, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, a, b, e, ha, hb, h⟩)))

lemma ev_pt (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N) :
    pA C N x w = x w ∧ pB C N x w = false ∧ pV C N x w = x w := by
  have h1 : ¬ N ≤ w := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_input C N x w (by omega), h1]
  · simp [pB, pP_input C N x w (by omega), h1]
  · exact pV_input C N x w (by omega)

lemma ev_ln (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    pA C N x w = false ∧ pB C N x w = x w ∧ pV C N x w = x w := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_input C N x w h2, h1]
  · simp [pB, pP_input C N x w h2, h1]
  · exact pV_input C N x w h2

lemma ev_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pA C N x w = false ∧ pB C N x w = false ∧ pV C N x w = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_out C N x w hw]
  · simp [pB, pP_out C N x w hw]
  · exact pV_out C N x w hw

lemma ev_or (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pA C N x (N + N + j) = (pA C N x a || pA C N x b) ∧
    pB C N x (N + N + j) = (pB C N x a || pB C N x b) ∧
    pV C N x (N + N + j) = (pV C N x a || pV C N x b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pB, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pV_gate C N x j a b _ hg ha hb, GateOp.eval]

lemma ev_and (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pA C N x (N + N + j) = (pA C N x a && pA C N x b) ∧
    pB C N x (N + N + j) = ((pA C N x a && pB C N x b) || (pB C N x a && pA C N x b)) ∧
    pV C N x (N + N + j) = (pV C N x a && pV C N x b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pA, pB, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pV_gate C N x j a b _ hg ha hb, GateOp.eval]

lemma pA_mono (C : Circuit) (N : ℕ) (hG : Good C N) (x x' : ℕ → Bool)
    (hx : ∀ i, i < N → x i = true → x' i = true) :
    ∀ w, pA C N x w = true → pA C N x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb, hg⟩ |
      ⟨j, a, b, rfl, ha, hb, hg⟩ | h
    · rw [(ev_pt C N x w h).1, (ev_pt C N x' w h).1]; exact hx w h
    · rw [(ev_ln C N x w h1 h2).1]; simp
    · rw [(ev_or C N x j a b hg ha hb).1, (ev_or C N x' j a b hg ha hb).1]
      simp only [Bool.or_eq_true]
      rintro (h | h)
      · exact Or.inl (ih a ha h)
      · exact Or.inr (ih b hb h)
    · rw [(ev_and C N x j a b hg ha hb).1, (ev_and C N x' j a b hg ha hb).1]
      simp only [Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      exact ⟨ih a ha h1, ih b hb h2⟩
    · rw [(ev_out C N x w h).1]; simp

lemma parts_le_val (C : Circuit) (N : ℕ) (hG : Good C N) (x : ℕ → Bool) :
    ∀ w, (pA C N x w = true ∨ pB C N x w = true) → pV C N x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb, hg⟩ |
      ⟨j, a, b, rfl, ha, hb, hg⟩ | h
    · obtain ⟨e1, e2, e3⟩ := ev_pt C N x w h
      rw [e1, e2, e3]; simp
    · obtain ⟨e1, e2, e3⟩ := ev_ln C N x w h1 h2
      rw [e1, e2, e3]; simp
    · obtain ⟨e1, e2, e3⟩ := ev_or C N x j a b hg ha hb
      rw [e1, e2, e3]; simp only [Bool.or_eq_true]
      have iha := ih a ha
      have ihb := ih b hb
      tauto
    · obtain ⟨e1, e2, e3⟩ := ev_and C N x j a b hg ha hb
      rw [e1, e2, e3]; simp only [Bool.or_eq_true, Bool.and_eq_true]
      have iha := ih a ha
      have ihb := ih b hb
      tauto
    · obtain ⟨e1, e2, e3⟩ := ev_out C N x w h
      rw [e1, e2, e3]; simp

def inp (C : Circuit) (j : ℕ) (s : Bool) : ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (if s then 1 else 0) 0

def sib (C : Circuit) (j : ℕ) (s : Bool) : ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (if s then 0 else 1) 0

def isAnd (C : Circuit) (j : ℕ) : Prop := ∃ a b, C.gates[j]? = some ⟨GateOp.and, [a, b]⟩

def side (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool) : Prop :=
  isAnd C j → pA C N P (sib C j s) = true

def ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) : ℕ → ℕ → Prop
  | 0, w => w = C.output
  | k + 1, w => ∃ j s, j < C.gates.length ∧ w = inp C j s ∧ ctx C N P k (N + N + j) ∧
      side C N P j s

def Ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) (w : ℕ) : Prop := ∃ k, ctx C N P k w

def term (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool) : Prop :=
  j < C.gates.length ∧ Ctx C N P (N + N + j) ∧ side C N P j s

lemma inp_sib (C : Circuit) (j : ℕ) (op : GateOp) (a b : ℕ)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) :
    inp C j false = a ∧ inp C j true = b ∧ sib C j false = b ∧ sib C j true = a := by
  simp [inp, sib, List.getD_eq_getElem?_getD, hg]

lemma inp_lt (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (s : Bool) (hj : j < C.gates.length) :
    inp C j s < N + N + j := by
  obtain ⟨a, b, ha, hb, hg⟩ := gate_view C N hG j hj
  rcases hg with hg | hg
  · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
    cases s
    · rw [e1]; exact ha
    · rw [e2]; exact hb
  · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
    cases s
    · rw [e1]; exact ha
    · rw [e2]; exact hb

lemma not_isAnd_of_or (C : Circuit) (j a b : ℕ) (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) :
    ¬ isAnd C j := by
  rintro ⟨a', b', h'⟩
  rw [hg] at h'
  simp at h'

lemma Ctx_out (C : Circuit) (N : ℕ) (P : ℕ → Bool) : Ctx C N P C.output := ⟨0, by simp [ctx]⟩

lemma Ctx_cases (C : Circuit) (N : ℕ) (P : ℕ → Bool) (w : ℕ) (h : Ctx C N P w) :
    w = C.output ∨ ∃ j s, w = inp C j s ∧ term C N P j s := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => left; simpa [ctx] using hk
  | succ k =>
    simp only [ctx] at hk
    obtain ⟨j, s, hj, hw, hc, hs⟩ := hk
    exact Or.inr ⟨j, s, hw, hj, ⟨k, hc⟩, hs⟩

lemma term_to_Ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool)
    (h : term C N P j s) : Ctx C N P (inp C j s) := by
  obtain ⟨hj, ⟨k, hk⟩, hs⟩ := h
  refine ⟨k + 1, ?_⟩
  simp only [ctx]
  exact ⟨j, s, hj, rfl, hk, hs⟩

lemma ctx_mono (C : Circuit) (N : ℕ) (hG : Good C N) (P P' : ℕ → Bool)
    (h : ∀ i, i < N → P i = true → P' i = true) :
    ∀ k w, ctx C N P k w → ctx C N P' k w := by
  intro k
  induction k with
  | zero => intro w hw; simpa [ctx] using hw
  | succ k ih =>
    intro w hw
    simp only [ctx] at hw ⊢
    obtain ⟨j, s, hj, e, hc, hs⟩ := hw
    exact ⟨j, s, hj, e, ih _ hc, fun ha => pA_mono C N hG P P' h _ (hs ha)⟩

def xin (P : ℕ → Bool) (l : ℕ) : ℕ → Bool := fun i => P i || i == l

def pt (p : ℕ) : ℕ → Bool := fun i => i == p

lemma ctx_B (C : Circuit) (N : ℕ) (hG : Good C N) (P : ℕ → Bool) (l : ℕ) :
    ∀ k w, ctx C N P k w → pB C N (xin P l) w = true → pB C N (xin P l) C.output = true := by
  intro k
  induction k with
  | zero =>
    intro w h hb
    simp only [ctx] at h
    rw [← h]; exact hb
  | succ k ih =>
    intro w h hb
    simp only [ctx] at h
    obtain ⟨j, s, hj, hw, hc, hs⟩ := h
    apply ih _ hc
    obtain ⟨a, b, ha, hb', hg⟩ := gate_view C N hG j hj
    rcases hg with hg | hg
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      rw [(ev_or C N (xin P l) j a b hg ha hb').2.1]
      cases s
      · rw [hw, e1] at hb; simp [hb]
      · rw [hw, e2] at hb; simp [hb]
    · obtain ⟨e1, e2, e3, e4⟩ := inp_sib C j _ a b hg
      have hs' := pA_mono C N hG P (xin P l) (by intro i _ h; simp [xin, h]) _ (hs ⟨a, b, hg⟩)
      rw [(ev_and C N (xin P l) j a b hg ha hb').2.1]
      cases s
      · rw [hw, e1] at hb; rw [e3] at hs'; simp [hb, hs']
      · rw [hw, e2] at hb; rw [e4] at hs'; simp [hb, hs']

lemma B_ctx (C : Circuit) (N : ℕ) (hG : Good C N) (P : ℕ → Bool)
    (hP : ∀ i, P i = true → i < N) (l : ℕ) (hl : N ≤ l) :
    ∀ w, Ctx C N P w → pB C N (xin P l) w = true → Ctx C N P l := by
  have hmono : ∀ c, pA C N (xin P l) c = true → pA C N P c = true := by
    intro c
    apply pA_mono C N hG (xin P l) P
    intro i hi h
    simp only [xin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact h
    · omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hc hb
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb', hg⟩ |
      ⟨j, a, b, rfl, ha, hb', hg⟩ | h
    · rw [(ev_pt C N _ w h).2.1] at hb; simp at hb
    · rw [(ev_ln C N _ w h1 h2).2.1] at hb
      simp only [xin, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with hb | hb
      · exact absurd (hP w hb) (by omega)
      · rw [← hb]; exact hc
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hns := not_isAnd_of_or C j a b hg
      rw [(ev_or C N _ j a b hg ha hb').2.1] at hb
      simp only [Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · apply ih a ha _ hb
        rw [← e1]; exact term_to_Ctx C N P j false ⟨hj, hc, fun h => absurd h hns⟩
      · apply ih b hb' _ hb
        rw [← e2]; exact term_to_Ctx C N P j true ⟨hj, hc, fun h => absurd h hns⟩
    · obtain ⟨e1, e2, e3, e4⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      rw [(ev_and C N _ j a b hg ha hb').2.1] at hb
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hb
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply ih b hb' _ h2
        rw [← e2]
        exact term_to_Ctx C N P j true ⟨hj, hc, fun _ => by rw [e4]; exact hmono a h1⟩
      · apply ih a ha _ h1
        rw [← e1]
        exact term_to_Ctx C N P j false ⟨hj, hc, fun _ => by rw [e3]; exact hmono b h2⟩
    · rw [(ev_out C N _ w h).2.1] at hb; simp at hb

lemma ofFn_xs (N : ℕ) (x : ℕ → Bool) : List.ofFn (fun i : Fin (N + N) => x i) = xs N x := by
  apply List.ext_getElem <;> simp [xs]

lemma ctx_sound (C : Circuit) (N : ℕ) (hG : Good C N) (x2 : Fin N → Fin N → Prop)
    (hS : ∀ (x7 : Fin (N + N) → Bool),
      Fintype.card { x8 : Fin N // x7 (Fin.natAdd N x8) = Bool.true } ≤ (1 : ℕ) →
      (¬∃ (x9 : Fin N) (x10 : Fin N), x2 x9 x10 ∧ x7 (Fin.castAdd N x9) = Bool.true ∧
        x7 (Fin.natAdd N x10) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x7 = Bool.false)
    (l : Fin N) (P : ℕ → Bool) (hP : ∀ i, P i = true → i < N) (h : Ctx C N P (N + l)) :
    ∃ p : Fin N, x2 p l ∧ P p = true := by
  have hB : pB C N (xin P (N + l)) C.output = true := by
    obtain ⟨k, hk⟩ := h
    apply ctx_B C N hG P (N + l) k (N + l) hk
    rw [(ev_ln C N _ (N + l) (by omega) (by omega)).2.1]
    simp [xin]
  have hV := parts_le_val C N hG _ C.output (Or.inr hB)
  by_contra hne
  have hline : ∀ a : Fin N, xin P (N + l) (N + a) = true → a = l := by
    intro a ha
    simp only [xin, Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with ha | ha
    · exact absurd (hP _ ha) (by omega)
    · apply Fin.ext; omega
  have h0 := hS (fun i => xin P (N + l) i) (by
      rw [Fintype.card_le_one_iff_subsingleton]
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      apply Subtype.ext
      simp only [Fin.val_natAdd] at ha hb
      exact (hline a ha).trans (hline b hb).symm) (by
      rintro ⟨p, l', hinc, hp, hl'⟩
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hp hl'
      have e := hline l' hl'
      rw [e] at hinc
      apply hne
      refine ⟨p, hinc, ?_⟩
      simp only [xin, Bool.or_eq_true, beq_iff_eq] at hp
      rcases hp with hp | hp
      · exact hp
      · have := p.isLt; omega)
  have h1 : pV C N (xin P (N + l)) C.output = false := by
    unfold pV
    rw [← ofFn_xs]
    exact h0
  rw [h1] at hV
  simp at hV

def Below (N : ℕ) (x2 : Fin N → Fin N → Prop) (φ : (ℕ → Bool) → Prop) (l : Fin N) : Prop :=
  ∀ P : ℕ → Bool, (∀ i, P i = true → i < N) → φ P → ∃ p : Fin N, x2 p l ∧ P p = true

def Mono (N : ℕ) (φ : (ℕ → Bool) → Prop) : Prop :=
  ∀ P P' : ℕ → Bool, (∀ i, i < N → P i = true → P' i = true) → φ P → φ P'

lemma below_split (N : ℕ) (x2 : Fin N → Fin N → Prop) (φ ψ : (ℕ → Bool) → Prop) (l : Fin N)
    (hφ : Mono N φ) (hψ : Mono N ψ) (h : Below N x2 (fun P => φ P ∧ ψ P) l) :
    Below N x2 φ l ∨ Below N x2 ψ l := by
  by_contra hc
  have h1 : ¬ Below N x2 φ l := fun h' => hc (Or.inl h')
  have h2 : ¬ Below N x2 ψ l := fun h' => hc (Or.inr h')
  unfold Below at h1 h2
  rw [not_forall] at h1 h2
  obtain ⟨P1, h1⟩ := h1
  obtain ⟨P2, h2⟩ := h2
  rw [Classical.not_imp] at h1 h2
  obtain ⟨s1, h1⟩ := h1
  obtain ⟨s2, h2⟩ := h2
  rw [Classical.not_imp] at h1 h2
  obtain ⟨f1, n1⟩ := h1
  obtain ⟨f2, n2⟩ := h2
  obtain ⟨p, hp, hpp⟩ := h (fun i => P1 i || P2 i)
    (by
      intro i hi
      simp only [Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact s1 i hi
      · exact s2 i hi)
    ⟨hφ P1 _ (by intro i _ hi; simp [hi]) f1, hψ P2 _ (by intro i _ hi; simp [hi]) f2⟩
  simp only [Bool.or_eq_true] at hpp
  rcases hpp with hpp | hpp
  · exact n1 ⟨p, hp, hpp⟩
  · exact n2 ⟨p, hp, hpp⟩

lemma pt_supp (N : ℕ) (p : Fin N) : ∀ i, pt p i = true → i < N := by
  intro i hi
  simp only [pt, beq_iff_eq] at hi
  have := p.isLt
  omega

lemma below_pt (N : ℕ) (x2 : Fin N → Fin N → Prop) (φ : (ℕ → Bool) → Prop) (l : Fin N)
    (h : Below N x2 φ l) (p : Fin N) (hp : φ (pt p)) : x2 p l := by
  obtain ⟨p', h1, h2⟩ := h _ (pt_supp N p) hp
  simp only [pt, beq_iff_eq] at h2
  have e : p' = p := Fin.ext h2
  rw [← e]; exact h1

lemma below_unique (N : ℕ) (x2 : Fin N → Fin N → Prop)
    (hK : ∀ (x5 x6 x7 x8 : Fin N), x5 ≠ x6 → x7 ≠ x8 →
      ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8))
    (φ : (ℕ → Bool) → Prop) (l l' : Fin N) (h : Below N x2 φ l) (h' : Below N x2 φ l')
    (p1 p2 : Fin N) (hne : p1 ≠ p2) (h1 : φ (pt p1)) (h2 : φ (pt p2)) : l = l' := by
  by_contra hl
  exact hK p1 p2 l l' hne hl ⟨below_pt N x2 φ l h p1 h1, below_pt N x2 φ l h p2 h2,
    below_pt N x2 φ l' h' p1 h1, below_pt N x2 φ l' h' p2 h2⟩

def Charge (N : ℕ) (x2 : Fin N → Fin N → Prop) (Par Chi : (ℕ → Bool) → Prop)
    (p l : Fin N) : Prop :=
  Below N x2 Par l ∧ (∃ p1 p2 : Fin N, p1 ≠ p2 ∧ Par (pt p1) ∧ Par (pt p2)) ∧
    Chi (pt p) ∧ ∀ p' : Fin N, Chi (pt p') → p' = p

lemma charge_unique (N : ℕ) (x2 : Fin N → Fin N → Prop)
    (hK : ∀ (x5 x6 x7 x8 : Fin N), x5 ≠ x6 → x7 ≠ x8 →
      ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8))
    (Par Chi : (ℕ → Bool) → Prop) (p l p' l' : Fin N)
    (h : Charge N x2 Par Chi p l) (h' : Charge N x2 Par Chi p' l') : p = p' ∧ l = l' := by
  obtain ⟨b, ⟨p1, p2, hne, e1, e2⟩, c, u⟩ := h
  obtain ⟨b', _, c', u'⟩ := h'
  exact ⟨u' p c, below_unique N x2 hK Par l l' b b' p1 p2 hne e1 e2⟩

def ParA (C : Circuit) (N : ℕ) (j : ℕ) : (ℕ → Bool) → Prop :=
  fun P => pA C N P (N + N + j) = true

def ChiA (C : Circuit) (N : ℕ) (j : ℕ) (s : Bool) : (ℕ → Bool) → Prop :=
  fun P => pA C N P (inp C j s) = true

def ParC (C : Circuit) (N : ℕ) (j : ℕ) (s : Bool) : (ℕ → Bool) → Prop :=
  fun P => Ctx C N P (inp C j s)

def ChiC (C : Circuit) (N : ℕ) (j : ℕ) (s : Bool) : (ℕ → Bool) → Prop :=
  fun P => term C N P j s

lemma mono_pA (C : Circuit) (N : ℕ) (hG : Good C N) (c : ℕ) :
    Mono N (fun P => pA C N P c = true) :=
  fun P P' h hf => pA_mono C N hG P P' h c hf

lemma mono_Ctx (C : Circuit) (N : ℕ) (hG : Good C N) (c : ℕ) :
    Mono N (fun P => Ctx C N P c) :=
  fun P P' h hf => by
    obtain ⟨k, hk⟩ := hf
    exact ⟨k, ctx_mono C N hG P P' h k c hk⟩

lemma mono_side (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (s : Bool) :
    Mono N (fun P => side C N P j s) :=
  fun P P' h hf ha => pA_mono C N hG P P' h _ (hf ha)

lemma walkA (C : Circuit) (N : ℕ) (hG : Good C N) (x2 : Fin N → Fin N → Prop) (l : Fin N) :
    ∀ w (p p1 : Fin N), Below N x2 (fun P => pA C N P w = true) l →
      pA C N (pt p) w = true → pA C N (pt p1) w = true → p1 ≠ p →
      ∃ j s, j < C.gates.length ∧ Charge N x2 (ParA C N j) (ChiA C N j s) p l := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro p p1 hb hp hp1 hne
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb', hg⟩ |
      ⟨j, a, b, rfl, ha, hb', hg⟩ | h
    · rw [(ev_pt C N _ w h).1] at hp hp1
      simp only [pt, beq_iff_eq] at hp hp1
      exact absurd (Fin.ext (hp1.symm.trans hp)) hne
    · rw [(ev_ln C N _ w h1 h2).1] at hp; simp at hp
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have key : ∀ (s : Bool) (c : ℕ), inp C j s = c → c < N + N + j →
          (∀ P, pA C N P c = true → pA C N P (N + N + j) = true) →
          pA C N (pt p) c = true →
          ∃ j s, j < C.gates.length ∧ Charge N x2 (ParA C N j) (ChiA C N j s) p l := by
        intro s c hc hlt hle hpc
        by_cases hu : ∀ p' : Fin N, pA C N (pt p') c = true → p' = p
        · refine ⟨j, s, hj, hb, ⟨p, p1, hne.symm, hp, hp1⟩, ?_, ?_⟩
          · show pA C N (pt p) (inp C j s) = true
            rw [hc]; exact hpc
          · intro p' hp'
            apply hu p'
            rw [← hc]; exact hp'
        · rw [not_forall] at hu
          obtain ⟨p', hu⟩ := hu
          rw [Classical.not_imp] at hu
          exact ih c hlt p p' (fun P hs hf => hb P hs (hle P hf)) hpc hu.1 hu.2
      have hp' := hp
      rw [(ev_or C N _ j a b hg ha hb').1] at hp'
      simp only [Bool.or_eq_true] at hp'
      rcases hp' with hpa | hpb
      · exact key false a e1 ha
          (fun P h => by rw [(ev_or C N P j a b hg ha hb').1, h]; simp) hpa
      · exact key true b e2 hb'
          (fun P h => by rw [(ev_or C N P j a b hg ha hb').1, h]; simp) hpb
    · have hsplit := below_split N x2 (fun P => pA C N P a = true) (fun P => pA C N P b = true) l
        (mono_pA C N hG a) (mono_pA C N hG b)
        (fun P hs hf => hb P hs (by
          show pA C N P (N + N + j) = true
          rw [(ev_and C N P j a b hg ha hb').1, hf.1, hf.2]; simp))
      rw [(ev_and C N _ j a b hg ha hb').1] at hp hp1
      simp only [Bool.and_eq_true] at hp hp1
      rcases hsplit with h | h
      · exact ih a ha p p1 h hp.1 hp1.1 hne
      · exact ih b hb' p p1 h hp.2 hp1.2 hne
    · rw [(ev_out C N _ w h).1] at hp; simp at hp

lemma walkC_step (C : Circuit) (N : ℕ) (hG : Good C N) (x2 : Fin N → Fin N → Prop) (l : Fin N)
    (w : ℕ)
    (ih : ∀ j, j < C.gates.length → w < N + N + j → ∀ p p1 : Fin N,
      Below N x2 (fun P => Ctx C N P (N + N + j)) l →
      Ctx C N (pt p) (N + N + j) → Ctx C N (pt p1) (N + N + j) → p1 ≠ p →
      ∃ j s, j < C.gates.length ∧ (Charge N x2 (ParC C N j s) (ChiC C N j s) p l ∨
        Charge N x2 (ParA C N j) (ChiA C N j s) p l)) :
    ∀ p p1 : Fin N, Below N x2 (fun P => Ctx C N P w) l →
      Ctx C N (pt p) w → Ctx C N (pt p1) w → p1 ≠ p →
      ∃ j s, j < C.gates.length ∧ (Charge N x2 (ParC C N j s) (ChiC C N j s) p l ∨
        Charge N x2 (ParA C N j) (ChiA C N j s) p l) := by
  intro p p1 hb hp hp1 hne
  rcases Ctx_cases C N _ w hp with ho | ⟨j, s, hw, ht⟩
  · exfalso
    obtain ⟨q, _, hq⟩ := hb (fun _ => false) (by intro i hi; simp at hi)
      (by rw [ho]; exact Ctx_out C N _)
    simp at hq
  · have hj := ht.1
    have hlt : inp C j s < N + N + j := inp_lt C N hG j s hj
    by_cases hu : ∀ p' : Fin N, term C N (pt p') j s → p' = p
    · refine ⟨j, s, hj, Or.inl ⟨?_, ⟨p, p1, hne.symm, ?_, ?_⟩, ht, hu⟩⟩
      · show Below N x2 (fun P => Ctx C N P (inp C j s)) l
        rw [← hw]; exact hb
      · show Ctx C N (pt p) (inp C j s)
        rw [← hw]; exact hp
      · show Ctx C N (pt p1) (inp C j s)
        rw [← hw]; exact hp1
    · rw [not_forall] at hu
      obtain ⟨p2, hu⟩ := hu
      rw [Classical.not_imp] at hu
      obtain ⟨ht2, hne2⟩ := hu
      have hbt : Below N x2 (fun P => Ctx C N P (N + N + j) ∧ side C N P j s) l :=
        fun P hs hf => hb P hs (by rw [hw]; exact term_to_Ctx C N P j s ⟨hj, hf.1, hf.2⟩)
      rcases below_split N x2 _ _ l (mono_Ctx C N hG (N + N + j)) (mono_side C N hG j s) hbt
        with h | h
      · exact ih j hj (by omega) p p2 h ht.2.1 ht2.2.1 hne2
      · by_cases hand : isAnd C j
        · have h' : Below N x2 (fun P => pA C N P (sib C j s) = true) l :=
            fun P hs hf => h P hs (fun _ => hf)
          obtain ⟨j', s', hj', hc⟩ := walkA C N hG x2 l (sib C j s) p p2 h'
            (ht.2.2 hand) (ht2.2.2 hand) hne2
          exact ⟨j', s', hj', Or.inr hc⟩
        · exfalso
          obtain ⟨q, _, hq⟩ := h (fun _ => false) (by intro i hi; simp at hi)
            (fun ha => absurd ha hand)
          simp at hq

lemma walkC (C : Circuit) (N : ℕ) (hG : Good C N) (x2 : Fin N → Fin N → Prop) (l : Fin N) :
    ∀ m w, N + N + C.gates.length ≤ w + m → ∀ p p1 : Fin N,
      Below N x2 (fun P => Ctx C N P w) l →
      Ctx C N (pt p) w → Ctx C N (pt p1) w → p1 ≠ p →
      ∃ j s, j < C.gates.length ∧ (Charge N x2 (ParC C N j s) (ChiC C N j s) p l ∨
        Charge N x2 (ParA C N j) (ChiA C N j s) p l) := by
  intro m
  induction m with
  | zero =>
    intro w hw
    apply walkC_step C N hG x2 l w
    intro j hj hlt
    omega
  | succ m ih =>
    intro w hw
    apply walkC_step C N hG x2 l w
    intro j hj hlt
    exact ih (N + N + j) (by omega)

def Rel (C : Circuit) (N : ℕ) (x2 : Fin N → Fin N → Prop) (p l : Fin N) :
    (Fin C.gates.length × Bool) ⊕ ((Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool)) →
      Prop
  | Sum.inl (j, s) => inp C j s = N + l ∧ Ctx C N (pt p) (N + l) ∧
      ∀ p' : Fin N, Ctx C N (pt p') (N + l) → p' = p
  | Sum.inr (Sum.inl (j, s)) => Charge N x2 (ParC C N j s) (ChiC C N j s) p l
  | Sum.inr (Sum.inr (j, s)) => Charge N x2 (ParA C N j) (ChiA C N j s) p l

lemma rel_unique (C : Circuit) (N : ℕ) (x2 : Fin N → Fin N → Prop)
    (hK : ∀ (x5 x6 x7 x8 : Fin N), x5 ≠ x6 → x7 ≠ x8 →
      ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8))
    (p l p' l' : Fin N)
    (σ : (Fin C.gates.length × Bool) ⊕ ((Fin C.gates.length × Bool) ⊕
      (Fin C.gates.length × Bool)))
    (h : Rel C N x2 p l σ) (h' : Rel C N x2 p' l' σ) : p = p' ∧ l = l' := by
  rcases σ with ⟨j, s⟩ | ⟨j, s⟩ | ⟨j, s⟩
  · simp only [Rel] at h h'
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨h1', h2', h3'⟩ := h'
    have e : l = l' := by apply Fin.ext; omega
    subst e
    exact ⟨h3' p h2, rfl⟩
  · simp only [Rel] at h h'
    exact charge_unique N x2 hK _ _ p l p' l' h h'
  · simp only [Rel] at h h'
    exact charge_unique N x2 hK _ _ p l p' l' h h'

lemma rel_exists (C : Circuit) (N : ℕ) (hG : Good C N) (x2 : Fin N → Fin N → Prop)
    (hS : ∀ (x7 : Fin (N + N) → Bool),
      Fintype.card { x8 : Fin N // x7 (Fin.natAdd N x8) = Bool.true } ≤ (1 : ℕ) →
      (¬∃ (x9 : Fin N) (x10 : Fin N), x2 x9 x10 ∧ x7 (Fin.castAdd N x9) = Bool.true ∧
        x7 (Fin.natAdd N x10) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x7 = Bool.false)
    (p l : Fin N)
    (hLS : PEqualNP.ReadK.lineSingle C (N + N) (fun x9 => decide (N ≤ x9)) p (N + l) = true) :
    ∃ σ, Rel C N x2 p l σ := by
  have hB : pB C N (xin (pt p) (N + l)) C.output = true := hLS
  have hC : Ctx C N (pt p) (N + l) :=
    B_ctx C N hG (pt p) (pt_supp N p) (N + l) (by omega) C.output (Ctx_out C N _) hB
  have hbelow : Below N x2 (fun P => Ctx C N P (N + l)) l :=
    fun P hs hf => ctx_sound C N hG x2 hS l P hs hf
  by_cases hu : ∀ p' : Fin N, Ctx C N (pt p') (N + l) → p' = p
  · rcases Ctx_cases C N _ _ hC with ho | ⟨j, s, hw, ht⟩
    · exfalso
      obtain ⟨q, _, hq⟩ := hbelow (fun _ => false) (by intro i hi; simp at hi)
        (by rw [ho]; exact Ctx_out C N _)
      simp at hq
    · exact ⟨Sum.inl (⟨j, ht.1⟩, s), hw.symm, hC, hu⟩
  · rw [not_forall] at hu
    obtain ⟨p1, hu⟩ := hu
    rw [Classical.not_imp] at hu
    obtain ⟨j, s, hj, hc⟩ := walkC C N hG x2 l (N + N + C.gates.length) (N + l) (by omega)
      p p1 hbelow hC hu.1 hu.2
    rcases hc with hc | hc
    · exact ⟨Sum.inr (Sum.inl (⟨j, hj⟩, s)), hc⟩
    · exact ⟨Sum.inr (Sum.inr (⟨j, hj⟩, s)), hc⟩

end PEqualNP.Outside.L_meta_2970

theorem PEqualNP.Outside.L_meta_2970 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size := by
  intro N x2 inst C hK hAO hS
  have hG : PEqualNP.Outside.L_meta_2970.Good C N := ⟨hAO.1, hAO.2.1, hAO.2.2⟩
  have hex : ∀ q : { x8 : Fin N × Fin N // x2 x8.1 x8.2 ∧
      PEqualNP.ReadK.lineSingle C (N + N) (fun (x9 : ℕ) => Decidable.decide (N ≤ x9))
        (↑x8.1) (N + ↑x8.2) = Bool.true },
      ∃ σ, PEqualNP.Outside.L_meta_2970.Rel C N x2 q.1.1 q.1.2 σ :=
    fun q => PEqualNP.Outside.L_meta_2970.rel_exists C N hG x2 hS q.1.1 q.1.2 q.2.2
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro q q' e
    have h := PEqualNP.Outside.L_meta_2970.rel_unique C N x2 hK _ _ _ _ (f q) (hf q)
      (by rw [e]; exact hf q')
    exact Subtype.ext (Prod.ext h.1 h.2)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hcard
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  omega
