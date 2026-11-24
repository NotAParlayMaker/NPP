import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4449_1
    (hnot : ∀ (x2 : Fin 9) (C : Circuit), x2 ≠ 0 → x2 ≠ 4 → x2 ≠ 6 → x2 ≠ 7 → FanInTwo C → C.size ≤ 13 → (∃ g rest, C.gates = g :: rest ∧ g.op = GateOp.not) → ∃ x10 : Fin 9 → Bool, C.eval ((List.ofFn x10 ++ [x10 0 || x10 6]).set ↑x2 !x10 x2) ≠ [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun e => x10 e.1 && x10 e.2)
    (hand : ∀ (x2 : Fin 9) (C : Circuit), x2 ≠ 0 → x2 ≠ 4 → x2 ≠ 6 → x2 ≠ 7 → FanInTwo C → C.size ≤ 13 → (∃ g rest, C.gates = g :: rest ∧ g.op = GateOp.and) → ∃ x10 : Fin 9 → Bool, C.eval ((List.ofFn x10 ++ [x10 0 || x10 6]).set ↑x2 !x10 x2) ≠ [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun e => x10 e.1 && x10 e.2)
    (hor : ∀ (x2 : Fin 9) (C : Circuit), x2 ≠ 0 → x2 ≠ 4 → x2 ≠ 6 → x2 ≠ 7 → FanInTwo C → C.size ≤ 13 → (∃ g rest, C.gates = g :: rest ∧ g.op = GateOp.or) → ∃ x10 : Fin 9 → Bool, C.eval ((List.ofFn x10 ++ [x10 0 || x10 6]).set ↑x2 !x10 x2) ≠ [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun e => x10 e.1 && x10 e.2) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → x2 ≠ (7 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]).set ↑x2 !x10 x2) ≠ x1 x10 := by
  dsimp only
  intro x2 C h0 h4 h6 h7 fan budget
  cases hg : C.gates with
  | nil =>
    have hev : ∀ w : List Bool, C.eval w = w.getD C.output false := by
      intro w
      have hw : C.wires w = w := by simp [Circuit.wires, hg]
      simp [Circuit.eval, hw]
    simp only [hev]
    by_cases hout : C.output < 10
    · have key : ∀ (o : Fin 10) (j : Fin 9), j ≠ 0 → j ≠ 4 → j ≠ 6 → j ≠ 7 →
          ∃ x10 ∈ ((fun _ : Fin 9 => false) :: (fun _ : Fin 9 => true) :: List.ofFn (fun k : Fin 9 => fun i : Fin 9 => decide (i = k))),
            ((List.ofFn x10 ++ [x10 0 || x10 6]).set ↑j !x10 j).getD o false ≠
            [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun e => x10 e.1 && x10 e.2 := by
        decide +kernel
      obtain ⟨x10, -, hx10⟩ := key ⟨C.output, hout⟩ x2 h0 h4 h6 h7
      exact ⟨x10, hx10⟩
    · have hout10 : 10 ≤ C.output := Nat.not_lt.mp hout
      refine ⟨fun _ => true, ?_⟩
      rw [List.getD_eq_default _ _ (by
        simp only [List.length_set, List.length_append, List.length_ofFn, List.length_singleton]
        exact hout10)]
      decide +kernel
  | cons g rest =>
    have hmem : g ∈ C.gates := by rw [hg]; exact List.mem_cons_self
    obtain ⟨hop, _hlen⟩ := fan g hmem
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
    rcases hop with hop | hop | hop
    · exact hand x2 C h0 h4 h6 h7 fan budget ⟨g, rest, hg, hop⟩
    · exact hor x2 C h0 h4 h6 h7 fan budget ⟨g, rest, hg, hop⟩
    · exact hnot x2 C h0 h4 h6 h7 fan budget ⟨g, rest, hg, hop⟩
