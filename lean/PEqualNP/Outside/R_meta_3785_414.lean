import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_3785_414
    (cover : ∀ (R : Fin 13 → Fin 13 → Prop) [DecidableRel R]
        (f : Finset (Fin 13) → Finset (Fin 13) → Bool),
      (∀ A B A' B', A ⊆ A' → B ⊆ B' → f A B = true → f A' B' = true) →
      (∀ p l, R p l → f {p} {l} = true) →
      (∀ (S : Finset (Fin 13)), let T := Finset.univ.filter fun l => ∀ p ∈ S, ¬R p l
        f (Finset.univ.filter fun p => ∀ l ∈ T, ¬R p l) T = false) →
      ∀ S T, f S T = true ↔ ∃ p ∈ S, ∃ l ∈ T, R p l)
    (witness : let R := fun p l : Fin 13 => p.val ∉ ([0,1,3,9] : List ℕ) ∧
          (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
        let ix := ([2,4,5,6,7,8,10,11,12] : List ℕ) ++ List.range' 14 12
        let row := fun (S T : Finset (Fin 13)) => ix.map fun k =>
          if k < 13 then decide (Fin.ofNat 13 k ∈ S) else decide (Fin.ofNat 13 k ∈ T)
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 43 ∧ C.output < 21 + C.size ∧
          (∀ p l, R p l → C.eval (row {p} {l}) = true) ∧
          (∀ S : Finset (Fin 13), let T := Finset.univ.filter fun l => ∀ p ∈ S, ¬R p l
            C.eval (row (Finset.univ.filter fun p => ∀ l ∈ T, ¬R p l) T) = false)) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (43 : ℕ) ∧       x1.output < (21 : ℕ) + x1.size ∧         have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];         have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.map (x3 x5 x6) x2) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x4 x7 x8 := by
  have step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      g.op.eval (g.inputs.map fun i => u.getD i false) = true →
        g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
    have hand (z : List Bool) : GateOp.and.eval z = z.all id := rfl
    have hor (z : List Bool) : GateOp.or.eval z = z.any id := rfl
    rcases hop with hop | hop
    · simp only [hop, hand, List.all_eq_true, List.mem_map, id_eq]
      intro hu b hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h i (hu _ ⟨i, hi, rfl⟩)
    · simp only [hop, hor, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨v.getD i false, ⟨i, hi, rfl⟩, h i hb⟩

  have wires_mono (gs : List Gate)
      (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (Circuit.wires ⟨gs, 0⟩ u).getD i false = true →
        (Circuit.wires ⟨gs, 0⟩ v).getD i false = true := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      let a := g.op.eval (g.inputs.map fun i => u.getD i false)
      let b := g.op.eval (g.inputs.map fun i => v.getD i false)
      change ∀ i, (Circuit.wires ⟨gs, 0⟩ (u ++ [a])).getD i false = true →
        (Circuit.wires ⟨gs, 0⟩ (v ++ [b])).getD i false = true
      apply ih (fun k hk => hgs k (List.mem_cons_of_mem g hk)) _ _ (by simp [hlen])
      intro i hi
      rcases lt_trichotomy i u.length with hlt | rfl | hgt
      · have hlt' : i < v.length := by omega
        simpa only [List.getD_append _ _ _ _ hlt'] using h i
          (by simpa only [List.getD_append _ _ _ _ hlt] using hi)
      · have ha : a = true := by simpa [List.getD_eq_getElem?_getD] using hi
        have hb : b = true := step_mono g (hgs g List.mem_cons_self) u v h ha
        simpa [hlen, List.getD_eq_getElem?_getD] using hb
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact Bool.noConfusion hi

  let R := fun p l : Fin 13 => p.val ∉ ([0,1,3,9] : List ℕ) ∧
          (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let ix := ([2,4,5,6,7,8,10,11,12] : List ℕ) ++ List.range' 14 12
  let row := fun (S T : Finset (Fin 13)) => ix.map fun k =>
          if k < 13 then decide (Fin.ofNat 13 k ∈ S) else decide (Fin.ofNat 13 k ∈ T)
  obtain ⟨C,hC,hs,ho,hp,hn⟩ := witness
  refine ⟨C,hC,hs,ho,?_⟩
  have ordered : ∀ A B A' B' : Finset (Fin 13), A ⊆ A' → B ⊆ B' →
      C.eval (row A B) = true → C.eval (row A' B') = true := by
    intro A B A' B' hA hB
    apply wires_mono C.gates (fun g hg => (hC g hg).1) _ _ (by simp [row]) _ C.output
    intro i hi
    by_cases hh : i < ix.length
    · simp [row,List.getD_eq_getElem?_getD, hh] at hi ⊢
      split at hi
      · rename_i hsmall
        simpa [hsmall] using hA (by simpa using hi)
      · rename_i hlarge
        simpa [hlarge] using hB (by simpa using hi)
    · simp [row,List.getD_eq_getElem?_getD, hh] at hi
  have hf := cover R (fun s t => C.eval (row s t)) ordered hp hn
  intro _ _ _ S T
  change C.eval (row S T) = true ↔ _
  rw [hf]
  constructor
  · rintro ⟨p,hp,l,hl,hp',hr⟩
    exact ⟨p,hp,hp',l,hl,hr⟩
  · rintro ⟨p,hp,hp',l,hl,hr⟩
    exact ⟨p,hp,l,hl,hp',hr⟩
