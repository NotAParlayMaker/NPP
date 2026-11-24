import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2379_522
    (collapse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ),
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) →
      ∃ D : AndCountCircuit n, D.size ≤ A.card ∧ D.WellFormed ∧ D.Computes G)
    (bound : ∀ D : AndCountCircuit 42, D.WellFormed →
      D.Computes (edgeGraph 42 ((List.range 21).flatMap (fun i : ℕ =>
        [(i,21+(i+20) % 21),(i,21+i),(i,21+(i+5) % 21),(i,21+(i+7) % 21),(i,21+(i+17) % 21)]))) → 21 ≤ D.size) :∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro C mono computes
  let es : List (ℕ × ℕ) := ((List.range 21).flatMap (fun i : ℕ =>
        [(i,21+(i+20) % 21),(i,21+i),(i,21+(i+5) % 21),(i,21+(i+7) % 21),(i,21+(i+17) % 21)]))
  let G := edgeGraph 42 es
  have noLoops (u v : Fin 42) (e : (u.val,v.val) ∈ es) : u ≠ v := by
    intro eq
    subst v
    change (u.val,u.val) ∈ (List.range 21).flatMap _ at e
    obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp e
    have ilt := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with h | h | h | h | h <;> omega
  have sem (x : Fin 42 → Bool) :
      C.eval (List.ofFn x) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [computes]
    constructor
    · rintro ⟨u,v,e,hu,hv⟩
      exact ⟨u,v,⟨noLoops u v e,Or.inl e⟩,hu,hv⟩
    · rintro ⟨u,v,⟨_,e⟩,hu,hv⟩
      rcases e with e | e
      · exact ⟨u,v,e,hu,hv⟩
      · exact ⟨v,u,e,hv,hu⟩
  let T : Finset (Fin C.gates.length) :=
    Finset.univ.filter fun i => (C.gates.get i).op = GateOp.and
  let A := T.map Fin.valEmbedding
  have contains (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) (hop : g.op = GateOp.and) :
      j ∈ A := by
    obtain ⟨h,e⟩ := List.getElem?_eq_some_iff.mp hj
    apply Finset.mem_map.mpr
    exact ⟨⟨j,h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [List.get_eq_getElem,e] using hop⟩, rfl⟩
  obtain ⟨D,sz,wf,hcomp⟩ := collapse 42 G C A mono sem contains
  have lower : 21 ≤ D.size := bound D wf hcomp
  have hT : (↑T : Set (Fin C.gates.length)) = {i | (C.gates.get i).op = GateOp.and} := by
    ext i
    simp [T]
  rw [← hT,Set.ncard_coe_finset]
  exact (lower.trans sz).trans_eq (Finset.card_map Fin.valEmbedding)
