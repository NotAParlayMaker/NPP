import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- A minimum vertex cover gives enough stars. Each AND gate can put its point operand first.
theorem PEqualNP.Outside.R_meta_2976_317
    (charge : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) → (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      E.card + M.card ≤ C.size + 1)
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ (D : Circuit) (S : Bool → Finset ℕ),
        IsAO2 (n+m) D ∧ D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        let g := NestedCover.gateAt D
        (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
          ∃ i < D.size, w = n+m+i ∧ (g i).op = GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < D.size, (g i).op = GateOp.and →
          ∃ a b t, (g i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  classical
  have saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (r : α → β → Prop) (A : Finset α) (B : Finset β)
      (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
      (minimal : ∀ (X : Finset α) (Y : Finset β),
        (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
      ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
    classical
    let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
    have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
      let X : Finset α := s.map (Function.Embedding.subtype _)
      let Y := s.biUnion adj
      have Xsub : X ⊆ A := by
        intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
        exact i.property
      have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
        intro a b h
        by_cases hb : b ∈ B
        · exact Or.inr (Finset.mem_union_left _ hb)
        have ha := (cov a b h).resolve_right hb
        by_cases hx : a ∈ X
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
          exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
      have bound := minimal _ _ replacement
      have card := Finset.card_sdiff_add_card_eq_card Xsub
      have union := Finset.card_union_le B Y
      have sizeX : X.card = s.card := Finset.card_map _
      change s.card ≤ Y.card
      omega
    obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

  have matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
    classical
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
      ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
    have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
      ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
    have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
      rw [least]
      exact Nat.find_min' has ⟨X,Y,h,rfl⟩
    obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
    obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
      (fun b a h => (cov a b h).symm) (fun Y X h => by
        simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
    let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
    have first : Function.Injective (Prod.fst ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
        | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
        | inr b' => exact congrArg Sum.inr (gi eq)
    have second : Function.Injective (Prod.snd ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (fi eq)
        | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
        | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
    let M := Finset.univ.image pair
    refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
    · intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      cases i with
      | inl a => exact (hf a).1
      | inr b => exact (hg b).1
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (first eq)
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (second eq)
    · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

  intro n m I _ C square ao correct
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  obtain ⟨M,A,B,sub,points,lines,cover,dual⟩ := matchingCover n m E
  have budget := charge n m E M C (by simpa only [mem] using square) ao
    (by simpa only [mem] using correct) sub
    (fun _ he _ hf h => points he hf h) (fun _ he _ hf h => lines he hf h)
  obtain ⟨D,S,strict,size,eval,closed,ands⟩ := stars n m E A B cover
  let ordered (g : Gate) := ∃ a b : ℕ, g.inputs = [a,b] ∧ a ∈ S false ∧ b ∈ S true
  let flip (g : Gate) := g.op = GateOp.and ∧ ¬ ordered g
  let orient (g : Gate) : Gate := if flip g then {g with inputs := g.inputs.reverse} else g
  let D' : Circuit := ⟨D.gates.map orient, D.output⟩
  have count : D'.gates.length = D.gates.length := List.length_map orient
  have op (g : Gate) : (orient g).op = g.op := by
    dsimp only [orient]
    split <;> rfl
  have operands (g : Gate) : (orient g).inputs.Perm g.inputs := by
    dsimp only [orient]
    split
    · exact List.reverse_perm _
    · exact List.Perm.refl _
  have atGate (i : ℕ) (hi : i < D.gates.length) :
      NestedCover.gateAt D' i = orient (NestedCover.gateAt D i) := by
    change (D.gates.map orient).getD i _ = orient (D.gates.getD i _)
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  have strict' : IsAO2 (n+m) D' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hg
      simpa only [op] using strict.1 src hsrc
    · intro i hi w hw
      rw [count] at hi
      rw [atGate i hi] at hw
      exact strict.2.1 i hi w ((operands _).mem_iff.mp hw)
    · intro g hg
      obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hg
      exact (operands src).length_eq.trans (strict.2.2 src hsrc)
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have next (ws : List Bool) (g : Gate) : step ws (orient g) = step ws g := by
    by_cases f : flip g
    · have andGate := f.1
      simp [step, orient, f, andGate, evalAnd]
    · simp [orient, f]
  have wires (gs : List Gate) (ws : List Bool) :
      (gs.map orient).foldl step ws = gs.foldl step ws := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons, List.foldl_cons, next, ih]
  have sameFun (z : Fin (n+m) → Bool) : circuitFun (n+m) D' z = circuitFun (n+m) D z :=
    congrArg (fun ws : List Bool => ws.getD D.output false) (wires D.gates (List.ofFn z))
  have side (t : Bool) (w : ℕ) (hw : w ∈ S t) :
      (w < n+m ∧ decide (n ≤ w) = t) ∨ ∃ i < D'.gates.length,
        w = n+m+i ∧ (NestedCover.gateAt D' i).op = GateOp.or ∧
          ∀ u ∈ (NestedCover.gateAt D' i).inputs, u ∈ S t := by
    rcases closed t w hw with h | ⟨i, hi, wi, orGate, rest⟩
    · exact Or.inl h
    · right
      refine ⟨i, count ▸ hi, wi, ?_, ?_⟩
      · rwa [atGate i hi, op]
      · rw [atGate i hi]
        exact fun u hu => rest u ((operands _).mem_iff.mp hu)
  have size' : D'.size = D.size := count
  refine ⟨D', S false, S true, strict', ?_, by omega, ?_, ?_, ?_⟩
  · intro z
    simpa only [mem] using (sameFun z).trans (eval z)
  · intro w hw
    rcases side false w hw with ⟨_, h⟩ | gate
    · exact Or.inl (by simpa using h)
    · exact Or.inr gate
  · intro w hw
    rcases side true w hw with ⟨bound, h⟩ | gate
    · exact Or.inl ⟨by simpa using h, bound⟩
    · exact Or.inr gate
  · intro i hi andGate
    rw [count] at hi
    rw [atGate i hi, op] at andGate
    change ordered (NestedCover.gateAt D' i)
    rw [atGate i hi]
    let g := NestedCover.gateAt D i
    change ordered (orient g)
    by_cases good : ordered g
    · have keep : ¬ flip g := fun f => f.2 good
      simpa only [orient, ite_eq_right keep] using good
    · have rev : flip g := ⟨andGate, good⟩
      obtain ⟨a,b,t,inputs,ha,hb⟩ := ands i hi andGate
      change g.inputs = [a,b] at inputs
      cases t with
      | false => exact (good ⟨a,b,inputs,ha,hb⟩).elim
      | true =>
        refine ⟨b, a, ?_, hb, ha⟩
        simp [orient, rev, inputs]
