import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2056_401
    (core :
      let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ e p l
      let v := fun r : Finset (Fin 13) × Finset (Fin 13) => List.ofFn fun i : Fin 26 =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ r.1) else decide (Fin.ofNat 13 i.val ∈ r.2)
      ∃ (D : Circuit) (a b : ℕ) (q : Bool) (X Y : Finset (Fin 13) × Finset (Fin 13)),
        Monotone2 D ∧ D.size ≤ 62 ∧ 26 ≤ a ∧ a < b ∧ b < 26 + D.size ∧
        let read := fun w r => (D.wires (v r)).getD w false
        let f := fun r => (if q then GateOp.and else GateOp.or).eval [read a r, read b r]
        let pos := fun r => ∃ p l, e p l ∧ r = ({p},{l})
        let neg := fun r => ∃ s : Finset (Fin 13), s.card ≤ 3 ∧ (r = (s,off s) ∨ r = (off s,s))
        (if q then neg X ∧ neg Y else pos X ∧ pos Y) ∧
        read a X ≠ read b X ∧ read a X = read b Y ∧ read b X = read a Y ∧
        (∀ r, pos r → (q = false ∧ (r = X ∨ r = Y)) ∨ f r = true) ∧
        ∀ r, neg r → (q = true ∧ (r = X ∨ r = Y)) ∨ f r = false)
    (finish : ∀ (n : ℕ) (D : Circuit), Monotone2 D → ∀ (q : Bool) (a b : ℕ),
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 1 ∧
        ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          (if q then GateOp.and else GateOp.or).eval
            [(D.wires (List.ofFn x)).getD a false, (D.wires (List.ofFn x)).getD b false]) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false
  := by
  let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ e p l
  let vec := fun r : Finset (Fin 13) × Finset (Fin 13) => fun i : Fin 26 =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ r.1) else decide (Fin.ofNat 13 i.val ∈ r.2)
  obtain ⟨D,a,b,q,X,Y,hD,sz,_,_,_,_,hne,h1,h2,yes,no⟩ := core
  obtain ⟨C,hC,hsize,heval⟩ := finish 26 D hD q a b
  let read := fun w r => (D.wires (List.ofFn (vec r))).getD w false
  let f := fun r => (if q then GateOp.and else GateOp.or).eval [read a r, read b r]
  have hneX : read a X ≠ read b X := hne
  have h1' : read a X = read b Y := h1
  have h2' : read b X = read a Y := h2
  have hneY : read a Y ≠ read b Y := by rw [← h1', ← h2']; exact Ne.symm hneX
  have mixBool (u v : Bool) (h : u ≠ v) :
      (if q then GateOp.and else GateOp.or).eval [u,v] = !q := by
    cases q <;> cases u <;> cases v <;> first | rfl | exact False.elim (h rfl)
  have mix (r : Finset (Fin 13) × Finset (Fin 13))
      (hr : read a r ≠ read b r) : f r = !q := mixBool _ _ hr
  have edgeRow (p l : Fin 13) (he : e p l) : f ({p},{l}) = true := by
    rcases yes ({p},{l}) ⟨p,l,he,rfl⟩ with ⟨hq, hp | hp⟩ | h
    · rw [hp, mix X hneX, hq] <;> rfl
    · rw [hp, mix Y hneY, hq] <;> rfl
    · exact h
  have blankRow (r : Finset (Fin 13) × Finset (Fin 13))
      (hr : ∃ s : Finset (Fin 13), s.card ≤ 3 ∧ (r = (s,off s) ∨ r = (off s,s))) :
      f r = false := by
    rcases no r hr with ⟨hq, hp | hp⟩ | h
    · rw [hp, mix X hneX, hq] <;> rfl
    · rw [hp, mix Y hneY, hq] <;> rfl
    · exact h
  refine ⟨C,hC,by omega,?_⟩
  change (∀ p l, e p l → C.eval (List.ofFn (vec ({p},{l}))) = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 →
      C.eval (List.ofFn (vec (s,off s))) = false ∧ C.eval (List.ofFn (vec (off s,s))) = false
  constructor
  · intro p l h
    rw [heval]
    exact edgeRow p l h
  · intro s hs
    constructor
    · rw [heval]
      exact blankRow (s,off s) ⟨s,hs,Or.inl rfl⟩
    · rw [heval]
      exact blankRow (off s,s) ⟨s,hs,Or.inr rfl⟩
