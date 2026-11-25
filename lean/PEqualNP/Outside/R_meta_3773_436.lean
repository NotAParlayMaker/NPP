import PEqualNP.Defs

-- A flag and five independent configurations suffice for an invariant output.
-- The circuit may use a different internal computation on each configuration.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3773_436
    (flags : let D : Finset (Fin 13) := {0,1,3,9}
      let iso := fun (p l : Fin 13 → Fin 13) => ∀ i j, (i+j ∈ D ↔ p i+l j ∈ D)
      ∀ i j : Fin 13, i+j ∈ D → ∃ p l, iso p l ∧ p 0 = i ∧ l 0 = j)
    (boundaries : let D : Finset (Fin 13) := {0,1,3,9}
      let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, i+j ∉ D
      let reps : List (Finset (Fin 13)) := [∅,{0},{0,1},{0,1,2},{0,1,3}]
      let iso := fun (p l : Fin 13 → Fin 13) => ∀ i j, (i+j ∈ D ↔ p i+l j ∈ D)
      ∀ s : Finset (Fin 13), s.card ≤ 3 → ∃ t ∈ reps, ∃ p l, iso p l ∧
        t.image p = s ∧ (off t).image l = off s)
    (synthesis : let D : Finset (Fin 13) := {0,1,3,9}
      let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, i+j ∉ D
      let reps : List (Finset (Fin 13)) := [∅,{0},{0,1},{0,1,2},{0,1,3}]
      let iso := fun (p l : Fin 13 → Fin 13) => ∀ i j, (i+j ∈ D ↔ p i+l j ∈ D)
      ∃ (C : Circuit) (g : Gate), Monotone2 C ∧ C.size ≤ 63 ∧ C.gates.head? = some g ∧
        (g.op = .and ∧ g.inputs = [0,13] ∨ g.op = .or ∧ g.inputs ∈ [[0,1],[0,13],[2,13]]) ∧
        let f := fun (s t : Finset (Fin 13)) => C.eval (incidenceInput s t)
        f {0} {0} = true ∧ (∀ s ∈ reps, f s (off s) = false) ∧
        (∀ s t, f t s = f s t) ∧
        ∀ p l, iso p l → ∀ s t, f (s.image p) (t.image l) = f s t) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  let D : Finset (Fin 13) := {0,1,3,9}
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, i+j ∉ D
  obtain ⟨C,g,mono,budget,head,first,yes,no,swap,invariant⟩ := synthesis
  refine ⟨C,mono,budget,⟨g,head,first⟩,?_,?_⟩
  · intro i j edge
    obtain ⟨p,l,rel,hp,hl⟩ := flags i j edge
    have transfer := invariant p l rel {0} {0}
    simp only [Finset.image_singleton,hp,hl] at transfer
    have inputEq : ∀ i j : Fin 13, List.ofFn (PEqualNP.EdgeOwnership.pairInput
        (Fin.castAdd 13 i) (Fin.natAdd 13 j)) = incidenceInput {i} {j} := by
      intro i j
      change List.ofFn _ = List.ofFn _ ++ List.ofFn _
      rw [List.ofFn_add]
      congr 1 <;> congr 1 <;> funext k
      · change decide (Fin.castAdd 13 k = Fin.castAdd 13 i ∨ Fin.castAdd 13 k = Fin.natAdd 13 j) =
            decide (k ∈ ({i} : Finset (Fin 13)))
        simp [Fin.ext_iff] <;> omega
      · change decide (Fin.natAdd 13 k = Fin.castAdd 13 i ∨ Fin.natAdd 13 k = Fin.natAdd 13 j) =
            decide (k ∈ ({j} : Finset (Fin 13)))
        simp [Fin.ext_iff] <;> omega
    rw [inputEq]
    exact transfer.trans yes
  · intro s small
    obtain ⟨t,ht,p,l,rel,hp,hl⟩ := boundaries s small
    have transfer := invariant p l rel t (off t)
    change (off t).image l = off s at hl
    rw [hp,hl] at transfer
    have quiet : C.eval (incidenceInput s (off s)) = false := transfer.trans (no t ht)
    have quietDual := (swap s (off s)).trans quiet
    have split (a b : Fin 13 → Bool) : List.ofFn (fun i : Fin (13+13) =>
        Fin.addCases a b i) = List.ofFn a ++ List.ofFn b := by
      rw [List.ofFn_add]
      congr 1 <;> congr 1 <;> funext i <;> first | exact Fin.addCases_left i | exact Fin.addCases_right i
    have expandInput (u v : Finset (Fin 13)) : incidenceInput u v =
        List.ofFn (fun i : Fin 13 => decide (i ∈ u)) ++ List.ofFn (fun j : Fin 13 => decide (j ∈ v)) := rfl
    rw [split,split]
    constructor
    · simpa only [expandInput,off,D,Finset.mem_filter,Finset.mem_univ,true_and] using quiet
    · simpa only [expandInput,off,D,Finset.mem_filter,Finset.mem_univ,true_and,add_comm] using quietDual
