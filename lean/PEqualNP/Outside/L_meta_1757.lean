import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1757_aux

open PEqualNP.CircuitLowerBounds


open PEqualNP.CircuitLowerBounds

def chk (n : ℕ) : List Gate → Bool
  | [] => true
  | g :: gs => g.inputs.all (fun i => decide (i < n)) && chk (n + 1) gs

theorem chk_spec : ∀ (gs : List Gate) (n : ℕ), chk n gs = true →
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | g :: gs, n, h, 0, _, i, hi => by
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simpa using h.1 i (by simpa using hi)
  | g :: gs, n, h, j + 1, hj, i, hi => by
    simp only [chk, Bool.and_eq_true] at h
    have := chk_spec gs (n + 1) h.2 j (by simpa using hj) i (by simpa using hi)
    omega

def Inv (w : List Bool) (m : ℕ) : Prop :=
  (∀ i, w.getD i false = m.testBit i) ∧ (∀ i, w.length ≤ i → m.testBit i = false)

theorem step_inv (w : List Bool) (m : ℕ) (b : Bool) (h : Inv w m) :
    Inv (w ++ [b]) (if b then m ||| 2 ^ w.length else m) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro i
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, h1]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow] <;> omega
    · rw [List.getD_append_right _ _ _ _ le_rfl]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow, h2]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      cases b <;> simp [Nat.testBit_or, h2 i hi.le, Nat.testBit_two_pow] <;> omega
  · intro i hi
    simp at hi
    cases b <;> simp [Nat.testBit_or, h2 i (by omega), Nat.testBit_two_pow] <;> omega

def mk : ℕ → ℕ → List Bool → ℕ
  | _, m, [] => m
  | k, m, b :: bs => mk (k + 1) (if b then m ||| 2 ^ k else m) bs

theorem mk_spec : ∀ (bs w : List Bool) (m : ℕ), Inv w m → Inv (w ++ bs) (mk w.length m bs)
  | [], w, m, h => by simpa [mk] using h
  | b :: bs, w, m, h => by
    have := mk_spec bs (w ++ [b]) _ (step_inv w m b h)
    simpa [mk] using this

def run : ℕ → ℕ → List Gate → ℕ
  | _, m, [] => m
  | k, m, g :: gs => run (k + 1) (if g.op.eval (g.inputs.map fun i => m.testBit i) then m ||| 2 ^ k else m) gs

theorem run_spec : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), Inv w m →
    Inv (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) (run w.length m gs)
  | [], w, m, h => by simpa [run] using h
  | g :: gs, w, m, h => by
    have hmap : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => m.testBit i) :=
      List.map_congr_left (fun i _ => h.1 i)
    have := run_spec gs _ _ (step_inv w m (g.op.eval (g.inputs.map fun i => w.getD i false)) h)
    simp only [List.foldl_cons, run]
    rw [hmap] at this ⊢
    simpa using this

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run x.length (mk 0 0 x) C.gates).testBit C.output := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 C.output


theorem wires_eq (C : Circuit) (x : List Bool) (i : ℕ) :
    (C.wires x).getD i false = (run x.length (mk 0 0 x) C.gates).testBit i := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 i

end PEqualNP.Outside.L_meta_1757_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1757 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 29]⟩], 40⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 27 ∧ C.output = 40 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 14 + p.2) ∧ ∀ p l : Fin 7, (p.val = (l.val) % 7 ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) → (C.eval (List.ofFn fun i : Fin 14 => decide (i.val = p.val ∨ i.val = 7 + l.val)) = false ↔ ((p.val = 2 ∧ l.val = 2) ∨ (p.val = 5 ∧ l.val = 2))) := by
  intro C
  refine ⟨rfl, rfl, ?_, ?_⟩
  · decide +kernel
  · simp only [C, PEqualNP.Outside.L_meta_1757_aux.eval_eq]
    set_option maxRecDepth 100000 in decide +kernel
