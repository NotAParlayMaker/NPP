import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2101_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [18, 17]⟩,
    ⟨GateOp.or, [26, 15]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.and, [28, 5]⟩,
    ⟨GateOp.or, [19, 18]⟩,
    ⟨GateOp.or, [30, 16]⟩,
    ⟨GateOp.or, [31, 23]⟩,
    ⟨GateOp.and, [32, 6]⟩,
    ⟨GateOp.or, [20, 19]⟩,
    ⟨GateOp.or, [34, 17]⟩,
    ⟨GateOp.or, [35, 24]⟩,
    ⟨GateOp.and, [36, 7]⟩,
    ⟨GateOp.or, [21, 20]⟩,
    ⟨GateOp.or, [38, 18]⟩,
    ⟨GateOp.or, [39, 25]⟩,
    ⟨GateOp.and, [40, 8]⟩,
    ⟨GateOp.or, [22, 21]⟩,
    ⟨GateOp.or, [42, 19]⟩,
    ⟨GateOp.or, [43, 13]⟩,
    ⟨GateOp.and, [44, 9]⟩,
    ⟨GateOp.or, [23, 22]⟩,
    ⟨GateOp.or, [46, 20]⟩,
    ⟨GateOp.or, [47, 14]⟩,
    ⟨GateOp.and, [48, 10]⟩,
    ⟨GateOp.or, [24, 23]⟩,
    ⟨GateOp.or, [50, 21]⟩,
    ⟨GateOp.or, [51, 15]⟩,
    ⟨GateOp.and, [52, 11]⟩,
    ⟨GateOp.or, [25, 24]⟩,
    ⟨GateOp.or, [54, 22]⟩,
    ⟨GateOp.or, [55, 16]⟩,
    ⟨GateOp.and, [56, 12]⟩,
    ⟨GateOp.or, [29, 33]⟩,
    ⟨GateOp.or, [58, 37]⟩,
    ⟨GateOp.or, [59, 41]⟩,
    ⟨GateOp.or, [60, 45]⟩,
    ⟨GateOp.or, [61, 49]⟩,
    ⟨GateOp.or, [62, 53]⟩,
    ⟨GateOp.or, [63, 57]⟩], 64⟩

def o (a b : Bool) : Bool := [a, b].any id
def n (a b : Bool) : Bool := [a, b].all id

theorem o_eq (a b : Bool) : o a b = (a || b) := by simp [o]
theorem n_eq (a b : Bool) : n a b = (a && b) := by simp [n]

def A (y z : Fin 13 → Bool) (p a b c d : Fin 13) : Bool :=
  n (o (o (o (z a) (z b)) (z c)) (z d)) (y p)

def F (y z : Fin 13 → Bool) : Bool :=
  o (o (o (o (o (o (o (A y z 5 5 4 2 9) (A y z 6 6 5 3 10)) (A y z 7 7 6 4 11))
    (A y z 8 8 7 5 12)) (A y z 9 9 8 6 0)) (A y z 10 10 9 7 1)) (A y z 11 11 10 8 2))
    (A y z 12 12 11 9 3)

theorem mk (y z : Fin 13 → Bool) (p l : Fin 13) (h1 : y p = true) (h2 : z l = true)
    (hc : 5 ≤ (p : ℕ) ∧ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d := by decide) :
    ∃ p l : Fin 13, 5 ≤ (p : ℕ) ∧ (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d) ∧
      y p = true ∧ z l = true :=
  ⟨p, l, hc.1, hc.2, h1, h2⟩

theorem key (y z : Fin 13 → Bool) : F y z = decide (∃ p l : Fin 13, 5 ≤ (p : ℕ) ∧
    (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d) ∧ y p = true ∧ z l = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    simp only [F, A, o_eq, n_eq, Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
    rcases h with h|h|h|h|h|h|h|h <;> obtain ⟨h2, h1⟩ := h <;>
      rcases h2 with h2|h2|h2|h2 <;> exact mk y z _ _ h1 h2
  · rintro ⟨p, l, hp, ⟨d, hd, hpl⟩, h1, h2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl <;> subst hpl <;> fin_cases l <;>
      simp_all [F, A, o_eq, n_eq]

theorem fun_eq (x : Fin 26 → Bool) : circuitFun 26 C x =
    F (fun p => x (Fin.castAdd 13 p)) (fun l => x (Fin.natAdd 13 l)) := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, C, List.ofFn_succ, List.ofFn_zero,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.getD_cons_succ, List.getD_cons_zero, GateOp.eval]
  rfl

end PEqualNP.Outside.L_meta_2101_aux

open PEqualNP.Outside.L_meta_2101_aux in
theorem PEqualNP.Outside.L_meta_2101 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 ∧       x1.size ≤ (39 : ℕ) ∧         have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => ∃ x5 ∈ x2, x3 = x4 + x5;         ∀ (x4 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x5 ∧ x3 x5 x6 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by
  refine ⟨C, ?_, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h <;>
      simp_all
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide
  · intro x2 x3 x
    exact (fun_eq x).trans (key _ _)
