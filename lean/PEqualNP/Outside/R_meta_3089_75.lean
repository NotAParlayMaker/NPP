import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_3089_75
    (guarded : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    ∀ C : Circuit, FanInTwo C → C.size = 14 →
      (∃ p : Fin 9, (∀ g ∈ C.gates, 9 ∈ g.inputs → g.op = .and ∧ p.val ∈ g.inputs) ∧
        (p = 4 ∨ Monotone2 C)) →
      (∀ i : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    (negCase : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    ∀ C : Circuit, FanInTwo C → C.size = 14 →
      let reads := C.output :: C.gates.flatMap Gate.inputs;
      (C.output ≤ 24 ∧ ∀ g ∈ C.gates, ∀ a ∈ g.inputs, a ≤ 24) →
      (∀ a < 24, a ∈ reads) →
      9 + (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
        ∑ a ∈ Finset.range 24, (reads.count a - 1) ≤ 14 →
      reads.count 9 = 1 → (∃ g ∈ C.gates, g.op = .not) →
      (∃ g ∈ C.gates, 9 ∈ g.inputs ∧ ¬(g.op = .and ∧ 4 ∈ g.inputs)) →
      (∀ i : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    (monoCase : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    ∀ C : Circuit, Monotone2 C → C.size = 14 →
      let reads := C.output :: C.gates.flatMap Gate.inputs;
      (C.output ≤ 24 ∧ ∀ g ∈ C.gates, ∀ a ∈ g.inputs, a ≤ 24) →
      (∀ a < 24, a ∈ reads) →
      9 + (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
        ∑ a ∈ Finset.range 24, (reads.count a - 1) ≤ 14 →
      reads.count 9 = 1 → (∀ p : Fin 9, ∃ g ∈ C.gates, 9 ∈ g.inputs ∧ ¬(g.op = .and ∧ p.val ∈ g.inputs)) →
      (∀ i : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) = (1 : ℕ) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  intro rawTarget C hf sz bounded used budget once miss
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have eqf : f = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by decide +kernel
  have different : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x i]) ≠ f x := by
    simpa only [eqf] using miss
  suffices result : ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x by
    simpa only [eqf] using result
  have bnd : C.output ≤ 24 ∧ ∀ g ∈ C.gates, ∀ a ∈ g.inputs, a ≤ 24 := by simpa only [sz] using bounded
  have uses : ∀ a < 24, a ∈ C.output :: C.gates.flatMap Gate.inputs := by simpa only [sz] using used
  let reads := C.output :: C.gates.flatMap Gate.inputs
  have cost : 9 + (C.gates.filter (fun (g : Gate) => g.op.eval [false] && !g.op.eval [true])).length +
      ∑ a ∈ Finset.range 24, (reads.count a - 1) ≤ 14 := by simpa only [sz] using budget
  let cond := fun p : Fin 9 => ∀ g ∈ C.gates, 9 ∈ g.inputs → g.op = .and ∧ p.val ∈ g.inputs
  have bad (p : Fin 9) (no : ¬cond p) : ∃ g ∈ C.gates, 9 ∈ g.inputs ∧ ¬(g.op = .and ∧ p.val ∈ g.inputs) := by
    by_contra! h
    exact no h
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · by_cases ok : cond 4
    · exact guarded C hf sz ⟨4,ok,Or.inl rfl⟩ different
    exact negCase C hf sz bnd uses cost once neg (bad 4 ok) different
  · have hm : Monotone2 C := by
      intro g mem
      obtain ⟨hop,arity⟩ := hf g mem
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
      exact ⟨hop.imp_right (fun h => h.resolve_right (fun e => neg ⟨g,mem,e⟩)),arity⟩
    by_cases ok : ∃ p : Fin 9, cond p
    · obtain ⟨p,hp⟩ := ok
      exact guarded C hf sz ⟨p,hp,Or.inr hm⟩ different
    exact monoCase C hm sz bnd uses cost once (fun p => bad p (fun hp => ok ⟨p,hp⟩)) different
