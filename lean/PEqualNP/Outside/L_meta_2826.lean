import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

namespace PEqualNP.Outside.L_meta_2826_aux

def rep (m : List (ℕ × Bool)) (i : ℕ) : ℕ × Bool := m.getD i (10, false)

def step (s : List (ℕ × Bool) × List BinaryGate) (g : Gate) :
    List (ℕ × Bool) × List BinaryGate :=
  match g.op, g.inputs with
  | GateOp.not, [] => (s.1 ++ [(10, true)], s.2)
  | GateOp.not, i :: _ => (s.1 ++ [((rep s.1 i).1, !(rep s.1 i).2)], s.2)
  | GateOp.and, [] => (s.1 ++ [(10, true)], s.2)
  | GateOp.and, [i] => (s.1 ++ [rep s.1 i], s.2)
  | GateOp.and, [i, j] => (s.1 ++ [(11 + s.2.length, false)],
      s.2 ++ [⟨fun a b => (a == !(rep s.1 i).2) && (b == !(rep s.1 j).2),
        (rep s.1 i).1, (rep s.1 j).1⟩])
  | GateOp.or, [] => (s.1 ++ [(10, false)], s.2)
  | GateOp.or, [i] => (s.1 ++ [rep s.1 i], s.2)
  | GateOp.or, [i, j] => (s.1 ++ [(11 + s.2.length, true)],
      s.2 ++ [⟨fun a b => (a == (rep s.1 i).2) && (b == (rep s.1 j).2),
        (rep s.1 i).1, (rep s.1 j).1⟩])
  | _, _ => (s.1 ++ [(10, false)], s.2)

def cstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bw (x : List Bool) (bg : List BinaryGate) : List Bool :=
  BinaryCircuit.wires ⟨bg, 0⟩ (x ++ [false])

def Inv (w : List Bool) (m : List (ℕ × Bool)) (W : List Bool) : Prop :=
  w.length = m.length ∧ ∀ i, (rep m i).1 < W.length ∧
    w.getD i false = (W.getD (rep m i).1 false != (rep m i).2)

def Form (b : BinaryGate) : Prop := ∃ c d : Bool, b.op = fun a e => a == c && e == d

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem bw_nil (x : List Bool) : bw x [] = x ++ [false] := rfl

theorem bw_append (x : List Bool) (bg : List BinaryGate) (b : BinaryGate) :
    bw x (bg ++ [b]) = bw x bg ++ [b.op ((bw x bg).getD b.left false)
      ((bw x bg).getD b.right false)] := by
  unfold bw BinaryCircuit.wires
  rw [List.foldl_append]
  rfl

theorem bw_length (x : List Bool) : ∀ bg : List BinaryGate,
    (bw x bg).length = x.length + 1 + bg.length := by
  intro bg
  induction bg using List.reverseRecOn with
  | nil => simp [bw_nil]
  | append_singleton bg b ih => rw [bw_append]; simp [ih]; omega

theorem ext {w : List Bool} {m : List (ℕ × Bool)} {W W' : List Bool} {v : Bool}
    {r : ℕ × Bool} (h : Inv w m W) (pre : ∀ k < W.length, W'.getD k false = W.getD k false)
    (len : W.length ≤ W'.length) (rlt : r.1 < W'.length)
    (hv : v = (W'.getD r.1 false != r.2)) : Inv (w ++ [v]) (m ++ [r]) W' := by
  obtain ⟨hl, h⟩ := h
  refine ⟨by simp [hl], fun i => ?_⟩
  rcases lt_trichotomy i m.length with hi | hi | hi
  · have e1 : rep (m ++ [r]) i = rep m i := List.getD_append _ _ _ _ hi
    have e2 : (w ++ [v]).getD i false = w.getD i false := List.getD_append _ _ _ _ (by omega)
    rw [e1, e2]
    obtain ⟨b1, b2⟩ := h i
    exact ⟨by omega, by rw [b2, pre _ b1]⟩
  · subst hi
    have e1 : rep (m ++ [r]) m.length = r := by
      unfold rep; rw [List.getD_append_right _ _ _ _ le_rfl]; simp
    have e2 : (w ++ [v]).getD m.length false = v := by
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hl]
    rw [e1, e2]
    exact ⟨rlt, hv⟩
  · have e1 : rep (m ++ [r]) i = (10, false) :=
      List.getD_eq_default _ _ (by simp; omega)
    have e2 : (w ++ [v]).getD i false = false := List.getD_eq_default _ _ (by simp; omega)
    have e3 : rep m m.length = (10, false) := List.getD_eq_default _ _ le_rfl
    have e4 : w.getD m.length false = false := List.getD_eq_default _ _ (by omega)
    obtain ⟨b1, b2⟩ := h m.length
    rw [e3] at b1 b2
    rw [e4] at b2
    rw [e1, e2]
    refine ⟨by simp; omega, ?_⟩
    simp only at b1 b2 ⊢
    rw [pre _ b1]
    exact b2

theorem pre_same (W : List Bool) : ∀ k < W.length, W.getD k false = W.getD k false :=
  fun _ _ => rfl

theorem pre_app (W : List Bool) (z : Bool) :
    ∀ k < W.length, (W ++ [z]).getD k false = W.getD k false :=
  fun k hk => List.getD_append _ _ _ _ hk

theorem step_inv (x : List Bool) (hx : x.length = 10) (g : Gate) (hg : Ok g)
    (w : List Bool) (m : List (ℕ × Bool)) (bg : List BinaryGate)
    (h : Inv w m (bw x bg)) :
    Inv (cstep w g) (step (m, bg) g).1 (bw x (step (m, bg) g).2) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have hL := bw_length x bg
  rw [hx] at hL
  have h' := h
  obtain ⟨hwl, hh⟩ := h'
  have z10 : (bw x bg).getD 10 false = false := by
    have b2 := (hh m.length).2
    have e3 : rep m m.length = (10, false) := List.getD_eq_default _ _ le_rfl
    have e4 : w.getD m.length false = false := List.getD_eq_default _ _ (by omega)
    rw [e3, e4] at b2
    simp only at b2
    revert b2
    cases (bw x bg).getD 10 false <;> simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ =>
      dsimp only [step]
      exact ext h (pre_same _) le_rfl (by simp only; omega) (by rw [z10]; simp [cstep, GateOp.eval])
    | [i], _ =>
      dsimp only [step]
      exact ext h (pre_same _) le_rfl (hh i).1 (by rw [← (hh i).2]; simp [cstep, GateOp.eval])
    | [i, j], _ =>
      show Inv (cstep w _) _ (bw x (bg ++ _))
      rw [bw_append]
      refine ext h (pre_app _ _) (by simp) (by simp only; simp; omega) ?_
      simp only [cstep, GateOp.eval, List.map_cons, List.map_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [(hh i).2, (hh j).2]
      rw [show 11 + bg.length - (bw x bg).length = 0 by omega]
      generalize (bw x bg).getD (rep m i).1 false = a
      generalize (bw x bg).getD (rep m j).1 false = b
      cases a <;> cases b <;> cases (rep m i).2 <;> cases (rep m j).2 <;> rfl
  · match ins, hlen with
    | [], _ =>
      dsimp only [step]
      exact ext h (pre_same _) le_rfl (by simp only; omega) (by rw [z10]; simp [cstep, GateOp.eval])
    | [i], _ =>
      dsimp only [step]
      exact ext h (pre_same _) le_rfl (hh i).1 (by rw [← (hh i).2]; simp [cstep, GateOp.eval])
    | [i, j], _ =>
      show Inv (cstep w _) _ (bw x (bg ++ _))
      rw [bw_append]
      refine ext h (pre_app _ _) (by simp) (by simp only; simp; omega) ?_
      simp only [cstep, GateOp.eval, List.map_cons, List.map_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [(hh i).2, (hh j).2]
      rw [show 11 + bg.length - (bw x bg).length = 0 by omega]
      generalize (bw x bg).getD (rep m i).1 false = a
      generalize (bw x bg).getD (rep m j).1 false = b
      cases a <;> cases b <;> cases (rep m i).2 <;> cases (rep m j).2 <;> rfl
  · match ins, hlen with
    | [], _ =>
      dsimp only [step]
      exact ext h (pre_same _) le_rfl (by simp only; omega) (by rw [z10]; simp [cstep, GateOp.eval])
    | i :: t, _ =>
      dsimp only [step]
      refine ext h (pre_same _) le_rfl (hh i).1 ?_
      simp only [cstep, GateOp.eval, List.map_cons, List.headD_cons]
      rw [(hh i).2]
      cases (bw x bg).getD (rep m i).1 false <;> cases (rep m i).2 <;> rfl

theorem run_inv (x : List Bool) (hx : x.length = 10) : ∀ (gs : List Gate) (w : List Bool)
    (m : List (ℕ × Bool)) (bg : List BinaryGate), (∀ g ∈ gs, Ok g) → Inv w m (bw x bg) →
    Inv (gs.foldl cstep w) (gs.foldl step (m, bg)).1 (bw x (gs.foldl step (m, bg)).2) := by
  intro gs
  induction gs with
  | nil => intro w m bg _ h; exact h
  | cons g gs ih =>
    intro w m bg hg h
    simp only [List.foldl_cons]
    have := step_inv x hx g (hg g (by simp)) w m bg h
    exact ih _ _ _ (fun g' hg' => hg g' (by simp [hg'])) this

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem notDec (op : GateOp) :
    @decide (op = GateOp.not) (lineDegreeGateOpDecEq op GateOp.not) = isNot op := by
  cases op <;> rfl

theorem step_size (s : List (ℕ × Bool) × List BinaryGate) (g : Gate) :
    (step s g).2.length + (if isNot g.op then 1 else 0) ≤ s.2.length + 1 := by
  obtain ⟨op, ins⟩ := g
  rcases s with ⟨m, bg⟩
  cases op <;> rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩ <;> simp [step, isNot]

theorem run_size : ∀ (gs : List Gate) (s : List (ℕ × Bool) × List BinaryGate),
    (gs.foldl step s).2.length + (gs.filter fun g => isNot g.op).length ≤
      s.2.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    have h1 := ih (step s g)
    have h2 := step_size s g
    simp only [List.foldl_cons, List.filter_cons, List.length_cons]
    cases hg : isNot g.op
    · simp only [hg, Bool.false_eq_true, ite_false] at h1 h2 ⊢
      omega
    · simp only [hg, ite_true, List.length_cons] at h1 h2 ⊢
      omega

theorem step_form (s : List (ℕ × Bool) × List BinaryGate) (g : Gate)
    (h : ∀ b ∈ s.2, Form b) : ∀ b ∈ (step s g).2, Form b := by
  obtain ⟨op, ins⟩ := g
  rcases s with ⟨m, bg⟩
  cases op <;> rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩ <;> simp only [step] <;>
    first
    | exact h
    | (intro b hb
       simp only [List.mem_append, List.mem_singleton] at hb
       rcases hb with hb | rfl
       · exact h b hb
       · exact ⟨_, _, rfl⟩)

theorem run_form : ∀ (gs : List Gate) (s : List (ℕ × Bool) × List BinaryGate),
    (∀ b ∈ s.2, Form b) → ∀ b ∈ (gs.foldl step s).2, Form b := by
  intro gs
  induction gs with
  | nil => intro s h; exact h
  | cons g gs ih => intro s h; exact ih _ (step_form s g h)

def init : List (ℕ × Bool) := (List.range 10).map fun i => (i, false)

theorem inv_init (x : List Bool) (hx : x.length = 10) : Inv x init (bw x []) := by
  refine ⟨by simp [init, hx], fun i => ?_⟩
  rw [bw_nil]
  by_cases hi : i < 10
  · have e : rep init i = (i, false) := by
      simp [rep, init, List.getD_eq_getElem?_getD, hi]
    rw [e]
    refine ⟨by simp; omega, ?_⟩
    simp only
    rw [List.getD_append _ _ _ _ (by omega)]
    simp
  · have e : rep init i = (10, false) := List.getD_eq_default _ _ (by simp [init]; omega)
    rw [e]
    refine ⟨by simp; omega, ?_⟩
    simp only
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    simp [hx]

end PEqualNP.Outside.L_meta_2826_aux

open PEqualNP.Outside.L_meta_2826_aux

theorem PEqualNP.Outside.L_meta_2826 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 := by
  intro C hC
  refine ⟨⟨(C.gates.foldl step (init, [])).2, (rep (C.gates.foldl step (init, [])).1 C.output).1⟩,
    (rep (C.gates.foldl step (init, [])).1 C.output).2, ?_, ?_, ?_⟩
  · exact run_form C.gates (init, []) (by simp)
  · have := run_size C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    simp only [BinaryCircuit.size, notCount, Circuit.size, notDec]
    exact this
  · intro x hx
    obtain ⟨_, hh⟩ := run_inv x hx C.gates x init [] (fun g hg => hC g hg) (inv_init x hx)
    have e : C.eval x = (C.gates.foldl cstep x).getD C.output false := rfl
    rw [e, (hh C.output).2]
    rfl
