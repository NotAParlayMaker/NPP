import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing any of four symmetric vertices leaves the nine-vertex graph and preserves the first gate.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4936_723
    (project : ∀ (C : Circuit) (v : Fin 10) (p : Fin 10 → Fin 9),
      let read := fun (C : Circuit) (v : ℕ) => C.gates.countP fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
      let lift := fun (y : Fin 9 → Bool) (b : Bool) =>
        (List.ofFn fun i : Fin 10 => if i = v then false else y (p i)) ++ [b]
      FanInTwo C →
      (∃ y z : Fin 9 → Bool, ∃ b d : Bool, C.eval (lift y b) ≠ C.eval (lift z d)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + read C v.val ≤ C.size ∧
        ∀ (y : Fin 9 → Bool) (b : Bool), D.eval (List.ofFn y ++ [b]) = C.eval (lift y b))
    (nine : ∀ (D : Circuit) (b : Bool), FanInTwo D →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 15 ≤ D.size)
    (few : ∀ (C : Circuit) (b : Bool), let read := fun (C : Circuit) (v : ℕ) => C.gates.countP fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
      FanInTwo C → C.size ≤ 18 → C.output ≤ 29 →
      (∀ g ∈ C.gates, ∀ w ∈ g.inputs, w ≤ 29) →
      (∀ v ∈ ([3,7,8,9] : List ℕ), 15 + read C v ≤ C.size) →
      ∃ x : Fin 10 → Bool,
        C.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  classical
  let read := fun (C : Circuit) (v : ℕ) => C.gates.countP fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
  let target₉ := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let target₁₀ := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let p := fun (v : Fin 10) (i : Fin 10) => Fin.ofNat 9
    ((if v = 3 then [0,1,6,9,4,5,2,8,7,3] else
      if v = 7 then [0,1,6,8,5,4,2,9,3,7] else
      if v = 8 then [0,1,2,7,5,4,6,3,9,8] else
      [0,1,2,3,4,5,6,7,8,9] : List ℕ).getD i.val 0)
  let lift := fun (v : Fin 10) (x : Fin 9 → Bool) (i : Fin 10) =>
    if i = v then false else x (p v i)
  let pick := fun (b : Bool) (a c : Bool) => if b then a && c else a || c
  have iso : ∀ v ∈ ([3,7,8,9] : List (Fin 10)), ∀ y : Fin 9 → Bool,
      target₁₀ (lift v y) = target₉ y ∧ lift v y 0 = y 0 ∧ lift v y 1 = y 1 := by
    decide +kernel
  intro C b fan cap out pins
  by_contra! equal
  change ∀ x, C.eval (List.ofFn x ++ [pick b (x 0) (x 1)]) = target₁₀ x at equal
  have limited (i : ℕ) (hi : i ∈ ([3,7,8,9] : List ℕ)) : 15 + read C i ≤ C.size := by
    have within : i < 10 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    let v : Fin 10 := ⟨i, within⟩
    have member : v ∈ ([3,7,8,9] : List (Fin 10)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    have co (y : Fin 9 → Bool) :
        C.eval (List.ofFn (lift v y) ++ [pick b (y 0) (y 1)]) = target₉ y := by
      obtain ⟨graph, a, c⟩ := iso v member y
      rw [← graph, ← a, ← c, equal]
    have nz : ∃ y z : Fin 9 → Bool, ∃ s t : Bool,
        C.eval (List.ofFn (lift v y) ++ [s]) ≠ C.eval (List.ofFn (lift v z) ++ [t]) := by
      refine ⟨fun _ => false, fun _ => true, pick b false false, pick b true true, ?_⟩
      rw [co (fun _ => false), co (fun _ => true)]
      decide
    obtain ⟨D, smallFan, count, sim⟩ := project C v (p v) fan nz
    have correct (y : Fin 9 → Bool) :
        D.eval (List.ofFn y ++ [pick b (y 0) (y 1)]) = target₉ y :=
      (sim y _).trans (co y)
    have minimum := nine D b smallFan correct
    change D.size + read C i ≤ C.size at count
    omega
  obtain ⟨x, different⟩ := few C b fan cap out pins limited
  exact different (equal x)
