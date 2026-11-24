import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3456_1
 (tree : ∀ (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I],
  let price := fun T : Finset (Fin (N+N)) => Fintype.card {e : Fin N × Fin N // I e.1 e.2} + T.card - 1
  let cover := fun T : Finset (Fin (N+N)) => ∀ p l, I p l → Fin.castAdd N p∈T ∨ Fin.natAdd N l∈T
  let exact := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ z, PEqualNP.MetaComplexity.circuitFun (N+N) C z=true ↔ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true
  let cost := fun C : PEqualNP.CircuitLowerBounds.Circuit => (C.gates.foldl (fun (w : List Nat) g => w ++ [(g.inputs.map (fun i => w.getD i 0)).sum+1]) (List.replicate (N+N) 0)).getD C.output 0
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ p q l k,p≠q → l≠k → ¬(I p l ∧ I p k ∧ I q l ∧ I q k)) → PEqualNP.MetaComplexity.Monotone2 C → exact C → ∃ T,cover T ∧ price T ≤ cost C)
 (stars : ∀ (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I],
  let price := fun T : Finset (Fin (N+N)) => Fintype.card {e : Fin N × Fin N // I e.1 e.2} + T.card - 1
  let cover := fun T : Finset (Fin (N+N)) => ∀ p l, I p l → Fin.castAdd N p∈T ∨ Fin.natAdd N l∈T
  let exact := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ z, PEqualNP.MetaComplexity.circuitFun (N+N) C z=true ↔ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true
  let clean := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ j<D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op=.and → ∀ t : Fin (N+N), (D.wires (List.ofFn fun k => decide (k=t))).getD (N+N+j) false=false
  ∀ T,cover T → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) D ∧ D.size≤price T ∧ exact D ∧ clean D)
 (shared : ∀ (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I],
  let price := fun T : Finset (Fin (N+N)) => Fintype.card {e : Fin N × Fin N // I e.1 e.2} + T.card - 1
  let cover := fun T : Finset (Fin (N+N)) => ∀ p l, I p l → Fin.castAdd N p∈T ∨ Fin.natAdd N l∈T
  let exact := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ z, PEqualNP.MetaComplexity.circuitFun (N+N) C z=true ↔ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true
  let cost := fun C : PEqualNP.CircuitLowerBounds.Circuit => (C.gates.foldl (fun (w : List Nat) g => w ++ [(g.inputs.map (fun i => w.getD i 0)).sum+1]) (List.replicate (N+N) 0)).getD C.output 0
  let clean := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ j<D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op=.and → ∀ t : Fin (N+N), (D.wires (List.ofFn fun k => decide (k=t))).getD (N+N+j) false=false
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ p q l k,p≠q → l≠k → ¬(I p l ∧ I p k ∧ I q l ∧ I q k)) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C → exact C → C.size<cost C → (∀ T,cover T → C.size<price T) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) D ∧ D.size≤C.size ∧ exact D ∧ clean D) :
 ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  intro N I inst C free mono back exact
  obtain ⟨T,cov,lower⟩ := tree N I C free mono exact
  let price := fun U : Finset (Fin (N+N)) => Fintype.card {e : Fin N × Fin N // I e.1 e.2} + U.card - 1
  let covers := fun U : Finset (Fin (N+N)) => ∀ p l,I p l → Fin.castAdd N p∈U ∨ Fin.natAdd N l∈U
  by_cases cheap : ∃ U,covers U ∧ price U ≤ C.size
  · obtain ⟨U,cu,sz⟩ := cheap
    obtain ⟨D,dm,db,ds,de,dc⟩ := stars N I U cu
    exact ⟨D,dm,db,ds.trans sz,de,fun j hj op => ⟨fun p => dc j hj op (Fin.castAdd N p),fun l => dc j hj op (Fin.natAdd N l)⟩⟩
  · push Not at cheap
    obtain ⟨D,dm,db,ds,de,dc⟩ := shared N I C free mono back exact (lt_of_lt_of_le (cheap T cov) lower) cheap
    exact ⟨D,dm,db,ds,de,fun j hj op => ⟨fun p => dc j hj op (Fin.castAdd N p),fun l => dc j hj op (Fin.natAdd N l)⟩⟩
