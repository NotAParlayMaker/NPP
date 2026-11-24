import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2551_1
    (h1 :
      let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 4]
      let edge := fun (x : Fin 9 → Bool) =>
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)),
          ((2 : Fin 9), (3 : Fin 9)), ((0 : Fin 9), (4 : Fin 9)),
          ((3 : Fin 9), (4 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
          ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)),
          ((5 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
          ((5 : Fin 9), (8 : Fin 9)), ((6 : Fin 9), (8 : Fin 9))].any
          (fun e : Fin 9 × Fin 9 => x e.1 && x e.2)
      let all : List ℕ := [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116,
        132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]
      let good : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
          (∀ x : Fin 9 → Bool, C.eval (row x) = edge x) →
            ∀ n ∈ all,
              C.eval (List.ofFn (fun i : Fin 9 => n.testBit i) ++
                [n.testBit 0 || n.testBit 4]) = decide (n ∈ good))
    (h2 :
      let all : List ℕ := [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116,
        132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]
      let good : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
          (∀ n ∈ all,
            C.eval (List.ofFn (fun i : Fin 9 => n.testBit i) ++
              [n.testBit 0 || n.testBit 4]) = decide (n ∈ good)) →
            15 ≤ C.size) :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [x 0 || x 4]) =
            [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)),
              ((2 : Fin 9), (3 : Fin 9)), ((0 : Fin 9), (4 : Fin 9)),
              ((3 : Fin 9), (4 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
              ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)),
              ((5 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
              ((5 : Fin 9), (8 : Fin 9)), ((6 : Fin 9), (8 : Fin 9))].any
              (fun e : Fin 9 × Fin 9 => x e.1 && x e.2)) →
          15 ≤ C.size := by
  intro C hC hEval
  exact h2 C hC (h1 C hC hEval)
