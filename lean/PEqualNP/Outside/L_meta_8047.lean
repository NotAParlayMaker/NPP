import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8047_aux

open PEqualNP.CircuitLowerBounds

theorem hget (acc : List ℕ) (k i : ℕ) :
    (acc.map (fun x => x.testBit k)).getD i false = (acc.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases acc[i]? <;> simp

theorem tb_or (k : ℕ) (l : List ℕ) :
    (List.foldr (fun (a b : ℕ) => a ||| b) 0 l).testBit k = (l.map (fun x => x.testBit k)).any id := by
  induction l with
  | nil => simp
  | cons a t ih => simp [Nat.testBit_or, ih]

theorem tb_and (n k : ℕ) (hk : k < n) (l : List ℕ) :
    (List.foldr (fun (a b : ℕ) => a &&& b) (2 ^ n - 1) l).testBit k = (l.map (fun x => x.testBit k)).all id := by
  induction l with
  | nil => simp [Nat.testBit_two_pow_sub_one, hk]
  | cons a t ih => simp [Nat.testBit_and, ih]

theorem main (n k : ℕ) (hk : k < n) (gs : List Gate) :
    ∀ (acc : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    List.map (fun (x : ℕ) => x.testBit k)
      (List.foldl (fun (x5 : List ℕ) (x6 : Gate) => x5 ++ [if x6.op.eval [Bool.true, Bool.false] = Bool.true then List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs) else List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) ((2 : ℕ) ^ n - (1 : ℕ)) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs)]) acc gs)
    = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.map (fun (x : ℕ) => x.testBit k) acc) gs := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g t ih =>
    intro acc h
    have hg := h g (by simp)
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun g' hg' => h g' (by simp [hg']))]
    congr 1
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, _⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_append, List.map_cons, List.map_nil]
      simp [tb_and n k hk, List.map_map, Function.comp_def]
      congr 1
      funext x
      cases acc[x]? <;> simp
    · simp only [GateOp.eval, List.map_append, List.map_cons, List.map_nil]
      simp [tb_or, List.map_map, Function.comp_def]
      congr 1
      funext x
      cases acc[x]? <;> simp

end PEqualNP.Outside.L_meta_8047_aux

theorem PEqualNP.Outside.L_meta_8047 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x5 : List ℕ := List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [if x6.op.eval [Bool.true, Bool.false] = Bool.true then List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs) else List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) ((2 : ℕ) ^ x1 - (1 : ℕ)) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs)]) x3 x2.gates;     ∀ x6 < x1, (x5.getD x2.output (0 : ℕ)).testBit x6 = x2.eval (List.map (fun (x8 : ℕ) => x8.testBit x6) x3) := by
  intro x1 x2 x3 h x5 x6 hk
  have hm := PEqualNP.Outside.L_meta_8047_aux.main x1 x6 hk x2.gates x3 h
  rw [← PEqualNP.Outside.L_meta_8047_aux.hget]
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  exact congrArg (fun l => l.getD x2.output false) hm
