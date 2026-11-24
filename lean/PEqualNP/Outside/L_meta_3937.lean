import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3937

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma edge_single (k : Fin 9) :
    ([((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun p =>
      decide (p.1 = k) && decide (p.2 = k)) = false := by
  revert k
  decide

end PEqualNP.Outside.L_meta_3937

theorem PEqualNP.Outside.L_meta_3937 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size := by
  intro x1 _ hfirst hcomp _ hnone
  exfalso
  cases hgs : x1.gates with
  | nil =>
    have h1 := hfirst (fun _ => true)
    simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, hgs, List.foldl_nil] at h1
    exact absurd h1 (by decide)
  | cons g0 gs =>
    cases gs with
    | cons g1 gs1 =>
      simp [hgs] at hnone
    | nil =>
      have hlen : ∀ (x : Fin 9 → Bool), (x1.wires (List.ofFn x)).length = 10 := by
        intro x
        simp [PEqualNP.CircuitLowerBounds.Circuit.wires, hgs]
      have hlt9 : ∀ (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9),
          (x1.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
        intro x i hi
        simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, hgs, List.foldl_cons, List.foldl_nil]
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega
      have hev : ∀ (x : Fin 9 → Bool),
          (x1.wires (List.ofFn x)).getD x1.output false =
          ([((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun x5 => x x5.1 && x x5.2) := by
        intro x
        exact congrFun hcomp x
      by_cases h10 : 10 ≤ x1.output
      · have h0 := hev (fun _ => true)
        have hdef : (x1.wires (List.ofFn (fun _ : Fin 9 => true))).getD x1.output false = false :=
          List.getD_eq_default _ _ (by rw [hlen]; exact h10)
        rw [hdef] at h0
        exact absurd h0 (by decide)
      · by_cases h9 : x1.output = 9
        · have h0 := hev (fun i => decide (i = 0))
          rw [h9, hfirst] at h0
          exact absurd h0 (by decide)
        · have hk : x1.output < 9 := by omega
          have h0 := hev (fun i => decide (i = ⟨x1.output, hk⟩))
          rw [hlt9 _ x1.output hk] at h0
          have htrue : decide ((⟨x1.output, hk⟩ : Fin 9) = ⟨x1.output, hk⟩) = true := decide_eq_true rfl
          rw [htrue] at h0
          have hed := PEqualNP.Outside.L_meta_3937.edge_single ⟨x1.output, hk⟩
          rw [hed] at h0
          exact Bool.noConfusion h0
