import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3074_317
    (normal : ∀ C : Circuit, FanInTwo C →
    let r := fun (i : ℕ) (g : Gate) =>
      (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i
    let n := fun (f : Gate→Bool) => (C.gates.filter f).length
    (∀ m∈([2,3,4,6,10,12,160] : List ℕ), C.eval
      (List.ofFn (fun j : Fin 9 => m.testBit j.val) ++ [false]) =
      ([3,6,12,160] : List ℕ).contains m) → (∃ x : Fin 9→Bool, C.eval (List.ofFn x++[x 0 && x 3]) ≠ C.eval (List.ofFn x++[false])) →
    (∀ i∈([0,3] : List ℕ), n (fun g => r i g || r 9 g) ≤ 2) →
    n (fun g => !(r 0 g || r 3 g || r 9 g)) + 3 = C.size ∧ n (r 9)=1 ∧ (∀ i∈([0,3] : List ℕ), n (fun g => r i g && !r 9 g)=1) ∧
      ∀ g∈C.gates, r 0 g=true → r 3 g=false)
    (residual : ∀ C : Circuit, FanInTwo C →
    let r := fun (i : ℕ) (g : Gate) =>
      (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i
    let n := fun (f : Gate→Bool) => (C.gates.filter f).length
    let v := fun (x : Fin 9→Bool) (b : Bool) => C.eval (List.ofFn x++[b])
    let h := fun x : Fin 9→Bool => x 0 && x 3
    n (fun g => !(r 0 g || r 3 g || r 9 g)) ≤ 11 →
    (n (r 9)=1 ∧ (∀ i∈([0,3] : List ℕ), n (fun g => r i g && !r 9 g)=1) ∧
      ∀ g∈C.gates, r 0 g=true → r 3 g=false) →
    (∀ x, v x (h x) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/9)) && x (Fin.ofNat 9 e))) →
    (∃ x, v x (h x) ≠ v x (x 4 && x 6)) →
    (∃ x, v x (h x) ≠ v x false) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) → (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) → (15 : ℕ) ≤ x1.size := by
  intro C legal switched pinned correct bounded
  by_contra! small
  have probes : (∀ m∈([2,3,4,6,10,12,160] : List ℕ), C.eval
      (List.ofFn (fun j : Fin 9 => m.testBit j.val) ++ [false]) =
      ([3,6,12,160] : List ℕ).contains m) := by
    intro m hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact correct (fun i => (2:ℕ).testBit i.val)
    · exact correct (fun i => (3:ℕ).testBit i.val)
    · exact correct (fun i => (4:ℕ).testBit i.val)
    · exact correct (fun i => (6:ℕ).testBit i.val)
    · exact correct (fun i => (10:ℕ).testBit i.val)
    · exact correct (fun i => (12:ℕ).testBit i.val)
    · exact correct (fun i => (160:ℕ).testBit i.val)
  obtain ⟨cnt,roles⟩ := normal C legal probes pinned
    (fun i hi => by simpa only [List.any_cons,List.any_nil,Bool.or_false] using bounded i hi)
  apply residual C legal (by omega) roles _ switched pinned
  intro x
  apply (correct x).trans
  change _ = (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 ||
    (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 ||
    (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false))))))))))))
  simp only [Bool.or_false,Bool.or_assoc]
