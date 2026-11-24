import PEqualNP.Defs

/-! L-meta-3937: the hypotheses are contradictory. A circuit with no gate at index 1 has at most
one gate, and wire 9 is pinned to x0 or x1, so that gate exists and every wire is an input or
x0 or x1. No such wire computes the edge function: an input wire or wire 9 is true on an input
with a single true bit, where the function is false, and a missing wire is false on the all-true
input, where the function is true. -/

namespace PEqualNP.Outside.L_meta_3937

open PEqualNP.CircuitLowerBounds

theorem wires_one (C : Circuit) (g : Gate) (hg : C.gates = [g])
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1))
    (x : Fin 9 → Bool) : C.wires (List.ofFn x) = List.ofFn x ++ [x 0 || x 1] := by
  have h := h9 x
  simp only [Circuit.wires, hg, List.foldl_cons, List.foldl_nil] at h ⊢
  rw [List.getD_append_right _ _ _ _ (by simp)] at h
  simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero] at h
  rw [h]

end PEqualNP.Outside.L_meta_3937

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3937 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size := by
  intro C _ h9 hf _ hnone
  exfalso
  cases hgs : C.gates with
  | nil =>
    have h := h9 (fun _ => true)
    simp [Circuit.wires, hgs] at h
  | cons g t =>
    cases t with
    | cons g2 t2 => rw [hgs] at hnone; simp at hnone
    | nil =>
      have hw := PEqualNP.Outside.L_meta_3937.wires_one C g hgs h9
      have hv : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [x 0 || x 1]).getD C.output false =
          ([((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (5, 7), (6, 8), (8, 5)].any fun e => x e.1 && x e.2) := by
        intro x
        have h := congrFun hf x
        simpa only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, hw] using h
      generalize C.output = o at hv
      have ho : o < 10 := by
        by_contra hc
        have h := hv (fun _ => true)
        rw [List.getD_eq_default _ _ (by simp; omega)] at h
        revert h
        decide
      interval_cases o
      · exact absurd (hv fun i => decide (i.val = 0)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 1)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 2)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 3)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 4)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 5)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 6)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 7)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 8)) (by decide)
      · exact absurd (hv fun i => decide (i.val = 0)) (by decide)
