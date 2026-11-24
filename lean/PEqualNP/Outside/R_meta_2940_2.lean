import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Compress aliases and constant reads, then trim the program at its output.
-- The final gate reads two computed wires. In a shortest program each earlier gate is used.
theorem PEqualNP.Outside.R_meta_2940_2
    (rooted :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
       (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4,false]
    let signed (g : BinaryGate) := ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
    let valid (n : ℕ) (g : BinaryGate) :=
      signed g ∧ g.left < n ∧ g.right < n ∧ g.left ≠ 10 ∧ g.right ≠ 10 ∧ g.left ≠ g.right
    ∀ (C : BinaryCircuit) (p : Bool), C.size ≤ 13 →
      (∀ g ∈ C.gates, signed g) → (∀ x, (C.eval (seed x) != p) = f x) →
      ∃ (gs : List BinaryGate) (g : BinaryGate) (q : Bool), 7 ≤ gs.length ∧ gs.length ≤ 12 ∧
      (∀ (j : ℕ) (h : j < gs.length), valid (11+j) gs[j]) ∧
      valid (11+gs.length) g ∧ 11 ≤ g.left ∧ 11 ≤ g.right ∧
      (∀ i < gs.length, ∃ t ∈ (gs++[g]).drop (i+1), t.left = 11+i ∨ t.right = 11+i) ∧
      (∀ i : Fin 9, ∃ t ∈ gs++[g], t.left = i.val ∨ t.right = i.val) ∧
      ∀ x, ((BinaryCircuit.eval ⟨gs++[g],11+gs.length⟩ (seed x)) != q) = f x)
    (exclude :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
       (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4,false]
    let signed (g : BinaryGate) := ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
    let valid (n : ℕ) (g : BinaryGate) :=
      signed g ∧ g.left < n ∧ g.right < n ∧ g.left ≠ 10 ∧ g.right ≠ 10 ∧ g.left ≠ g.right
    ¬ ∃ (gs : List BinaryGate) (g : BinaryGate) (q : Bool), 7 ≤ gs.length ∧ gs.length ≤ 12 ∧
      (∀ (j : ℕ) (h : j < gs.length), valid (11+j) gs[j]) ∧
      valid (11+gs.length) g ∧ 11 ≤ g.left ∧ 11 ≤ g.right ∧
      (∀ i < gs.length, ∃ t ∈ (gs++[g]).drop (i+1), t.left = 11+i ∨ t.right = 11+i) ∧
      (∀ i : Fin 9, ∃ t ∈ gs++[g], t.left = i.val ∨ t.right = i.val) ∧
      ∀ x, ((BinaryCircuit.eval ⟨gs++[g],11+gs.length⟩ (seed x)) != q) = f x) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro B p signed correct
  by_contra! short
  have graph_eq (x : Fin 9 → Bool) : (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
       (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] <;> rfl
  exact exclude (rooted B p (by omega) signed
    (fun x => (correct x).trans (graph_eq x).symm))
