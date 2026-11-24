import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4127

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)


def stL2 (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def stL (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  stL2 g.op (g.inputs.map fun i => w.getD i (false, false))

def ini (isL : ℕ → Bool) (xs : List Bool) : List (Bool × Bool) :=
  (xs.zipIdx).map fun (b, i) => if isL i then (false, b) else (b, false)

def lpv (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ) : Bool × Bool :=
  (fd stL gs (ini isL xs)).getD w (false, false)

theorem lp_eq (C : Circuit) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ) :
    (linearParts C isL xs).getD w (false, false) = lpv C.gates isL xs w := rfl

theorem ini_len (isL : ℕ → Bool) (xs : List Bool) : (ini isL xs).length = xs.length := by
  simp [ini]

theorem lp_input (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ)
    (hw : w < xs.length) :
    lpv gs isL xs w = if isL w then (false, xs.getD w false) else (xs.getD w false, false) := by
  rw [lpv, fd_keep stL (false, false) gs _ w (by rw [ini_len]; exact hw)]
  simp [ini, List.getD_eq_getElem?_getD, hw]

theorem lp_big (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ)
    (hw : xs.length + gs.length ≤ w) : lpv gs isL xs w = (false, false) := by
  rw [lpv, List.getD_eq_default _ _ (by rw [fd_len, ini_len]; exact hw)]

theorem lp_gate (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (k : ℕ)
    (hk : k < gs.length) (hin : ∀ i ∈ gs[k].inputs, i < xs.length + k) :
    lpv gs isL xs (xs.length + k) = stL2 gs[k].op (gs[k].inputs.map (lpv gs isL xs)) := by
  have h := fd_gate stL (false, false) gs (ini isL xs) k hk
  rw [ini_len] at h
  rw [lpv, h]
  show stL2 gs[k].op _ = _
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [lpv]
  exact (fd_take stL (false, false) gs (ini isL xs) k i (by rw [ini_len]; exact hin i hi)
    (Nat.le_of_lt hk)).symm


theorem wb_gate (gs : List Gate) (X : List Bool) (k : ℕ) (hk : k < gs.length)
    (hin : ∀ i ∈ gs[k].inputs, i < X.length + k) :
    (fd stB gs X).getD (X.length + k) false
      = gs[k].op.eval (gs[k].inputs.map fun i => (fd stB gs X).getD i false) := by
  rw [fd_gate stB false gs X k hk]
  show gs[k].op.eval _ = _
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (fd_take stB false gs X k i (hin i hi) (Nat.le_of_lt hk)).symm

end PEqualNP.Outside.L_meta_4127

theorem PEqualNP.Outside.L_meta_4127 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) →     ∀ (x3 : Bool),       ((PEqualNP.ReadK.linearParts x1 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x1.output (Bool.false, Bool.false)).2 = Bool.false →         ∃ (x5 : ℕ → Bool),           (∀ (x6 : Fin (7 : ℕ)), (x5 ↑x6 = if x3 = Bool.true then Bool.false else Decidable.decide (x6 = (0 : Fin (7 : ℕ)))) ∧ x5 ((7 : ℕ) + ↑x6) = if x3 = Bool.true then Decidable.decide (x6 = (0 : Fin (7 : ℕ))) else Bool.false) ∧             (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                 x1.gates[x6]? = Option.some x7 →                   x7.inputs = [x8, x9] →                     have x12 : List Bool := x1.wires (List.ofFn fun (x12 : Fin (14 : ℕ)) => Decidable.decide (x12 = if x3 = Bool.true then Fin.castAdd (7 : ℕ) (0 : Fin (7 : ℕ)) else Fin.natAdd (7 : ℕ) (0 : Fin (7 : ℕ))));                     (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((14 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((14 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧               x5 x1.output = Bool.false := by
  intro C hC b hlp
  let isL : ℕ → Bool := fun x4 => decide (x4 = if b = true then 7 else 0)
  let xs : List Bool := List.ofFn fun x4 : Fin 14 => decide (x4.val = 0 ∨ x4.val = 7)
  let e : Fin 14 → Bool := fun x12 => decide (x12 = if b = true then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7))
  let V : ℕ → Bool × Bool := fun w => PEqualNP.Outside.L_meta_4127.lpv C.gates isL xs w
  have hxs : xs.length = 14 := by simp [xs]
  have hW : C.wires (List.ofFn e) = PEqualNP.Outside.L_meta_4127.fd PEqualNP.Outside.L_meta_4127.stB C.gates (List.ofFn e) := rfl
  have hgate : ∀ (k : ℕ) (hk : k < C.gates.length), ∃ a c : ℕ, (C.gates[k]'hk).inputs = [a, c] ∧ a < 14 + k ∧ c < 14 + k ∧
      ((C.gates[k]'hk).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (C.gates[k]'hk).op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
    intro k hk
    obtain ⟨hop, a, c, hin, _, ha, hc⟩ := hC k C.gates[k] (List.getElem?_eq_getElem hk)
    exact ⟨a, c, hin, ha, hc, hop⟩
  have claimA : ∀ w, (V w).1 = (C.wires (List.ofFn e)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases h1 : w < 14
      · show (PEqualNP.Outside.L_meta_4127.lpv C.gates isL xs w).1 = _
        rw [PEqualNP.Outside.L_meta_4127.lp_input C.gates isL xs w (by rw [hxs]; exact h1), hW,
          PEqualNP.Outside.L_meta_4127.fd_keep PEqualNP.Outside.L_meta_4127.stB false C.gates _ w (by simpa using h1)]
        interval_cases w <;> cases b <;> rfl
      · by_cases h2 : 14 + C.gates.length ≤ w
        · show (PEqualNP.Outside.L_meta_4127.lpv C.gates isL xs w).1 = _
          rw [PEqualNP.Outside.L_meta_4127.lp_big C.gates isL xs w (by rw [hxs]; exact h2), hW,
            List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_4127.fd_len]; simpa using h2)]
        · obtain ⟨k, rfl⟩ : ∃ k, w = 14 + k := ⟨w - 14, by omega⟩
          have hk : k < C.gates.length := by omega
          obtain ⟨a, c, hin, ha, hc, hop⟩ := hgate k hk
          have e1 : V (14 + k) = PEqualNP.Outside.L_meta_4127.stL2 C.gates[k].op (C.gates[k].inputs.map V) := by
            have := PEqualNP.Outside.L_meta_4127.lp_gate C.gates isL xs k hk (by rw [hxs, hin]; intro i hi; simp at hi; omega)
            rw [hxs] at this
            exact this
          have e2 := PEqualNP.Outside.L_meta_4127.wb_gate C.gates (List.ofFn e) k hk (by rw [hin]; intro i hi; simp at hi; simp; omega)
          rw [List.length_ofFn] at e2
          rw [e1, hW, e2, hin]
          have iA := ih a (by omega)
          have iC := ih c (by omega)
          rw [hW] at iA iC
          rcases hop with hop | hop <;> rw [hop] <;>
            simp [PEqualNP.Outside.L_meta_4127.stL2, PEqualNP.CircuitLowerBounds.GateOp.eval, iA, iC]
  refine ⟨fun w => (V w).2, ?_, ?_, ?_⟩
  · intro x6
    have h1 := PEqualNP.Outside.L_meta_4127.lp_input C.gates isL xs x6.val (by rw [hxs]; omega)
    have h2 := PEqualNP.Outside.L_meta_4127.lp_input C.gates isL xs (7 + x6.val) (by rw [hxs]; omega)
    show (PEqualNP.Outside.L_meta_4127.lpv C.gates isL xs x6.val).2 = _ ∧ (PEqualNP.Outside.L_meta_4127.lpv C.gates isL xs (7 + x6.val)).2 = _
    rw [h1, h2]
    fin_cases x6 <;> cases b <;> simp [isL, xs, List.getD_eq_getElem?_getD]
  · intro x6 x7 x8 x9 hg hin
    have hk : x6 < C.gates.length := (List.getElem?_eq_some_iff.1 hg).1
    have hx7 : C.gates[x6] = x7 := (List.getElem?_eq_some_iff.1 hg).2
    obtain ⟨a, c, hin', ha, hc, _⟩ := hgate x6 hk
    rw [hx7, hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have e1 : V (14 + x6) = PEqualNP.Outside.L_meta_4127.stL2 x7.op [V x8, V x9] := by
      have := PEqualNP.Outside.L_meta_4127.lp_gate C.gates isL xs x6 hk (by rw [hxs, hx7, hin]; intro i hi; simp at hi; omega)
      rw [hxs, hx7, hin] at this
      exact this
    intro x12
    refine ⟨fun hop => ?_, fun hop => ?_⟩
    · show (V (14 + x6)).2 = _
      rw [e1, hop, ← claimA x8, ← claimA x9]
      simp [PEqualNP.Outside.L_meta_4127.stL2]
    · show (V (14 + x6)).2 = _
      rw [e1, hop]
      simp [PEqualNP.Outside.L_meta_4127.stL2]
  · exact hlp
