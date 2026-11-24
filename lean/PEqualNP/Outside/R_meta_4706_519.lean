import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

-- The leaves give a distinguishing input coordinate for an incident flag and a generic negative.
-- Each of the 62 internal rectangles must be covered by two earlier rectangles.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4706_519
    (synthesize : ∀ (n m o : ℕ) (R : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))), o < n+m →
      (∀ w, ∃ A B : Set (Fin n → Bool), R w = A ×ˢ B) →
      (∀ w : Fin n, ∀ z ∈ R w.val, z.1 w = true ∧ z.2 w = false) →
      (∀ j < m, ∃ a < n+j, ∃ b < n+j, R (n+j) ⊆ R a ∪ R b) →
      ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack n C ∧ C.size = m ∧
        ∀ z ∈ R o, circuitFun n C z.1 = true ∧ circuitFun n C z.2 = false)
    (geometry : let seeds : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (d : Bool) =>
        let f := fun (a b : ℕ) (i : Fin 13) => if d = true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
        Fin.append (f z.1 z.2) (f z.2 z.1)
      ∀ z ∈ seeds, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ (t : Fin 13) (d : Bool),
        ∃ X Y : Finset (Fin 13), IsMaximalFalse singerLines3 X Y ∧ IsGeneric singerLines3 3 X Y ∧
          List.ofFn (row z m t d) = incidenceInput X Y)
    (search : let Flag : Type := Fin 13 × Fin 13
      let Negative : Type := Finset (Fin 13) × Finset (Fin 13)
      ∃ q : Fin 4,
        let k : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
        let liftRow : List Bool → Fin 27 → Bool := fun x (w : Fin (26+1)) =>
          Fin.lastCases (if q.val = 0 then x.getD 0 false && x.getD k.val false
            else x.getD 0 false || x.getD k.val false) (fun i : Fin 26 => x.getD i.val false) w
        ∃ R : ℕ → Set (Flag × Negative),
          (∀ w : ℕ, ∃ (A : Set (Fin 13 × Fin 13)) (B : Set (Finset (Fin 13) × Finset (Fin 13))),
            R w = A ×ˢ B) ∧
          (∀ w : Fin 27, ∀ z ∈ R w.val,
            liftRow (incidenceInput {z.1.1} {z.1.2}) w = true ∧
            liftRow (incidenceInput z.2.1 z.2.2) w = false) ∧
          (∀ j < 62, ∃ a < 27+j, ∃ b < 27+j, R (27+j) ⊆ R a ∪ R b) ∧
          ∀ u ∈ incidences singerLines3, ∀ v : Negative, IsMaximalFalse singerLines3 v.1 v.2 →
            IsGeneric singerLines3 3 v.1 v.2 → (u,v) ∈ R 88) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (4 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x5 ∧       x5.size ≤ (62 : ℕ) ∧         have x6 : Fin (26 : ℕ) := if ↑x4 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x4 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x7 : Bool := Decidable.decide (↑x4 = (0 : ℕ));         have x8 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x8 : Fin (26 : ℕ) → Bool) (x9 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x7 = Bool.true then x8 (0 : Fin (26 : ℕ)) && x8 x6 else x8 (0 : Fin (26 : ℕ)) || x8 x6) x8 x9;         (∀ (x9 x10 : Fin (13 : ℕ)), (∃ x11 ∈ x1, x9 = x10 + x11) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) ∧ ∀ x9 ∈ x2, ∀ x11 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x13 : Fin (13 : ℕ)) (x14 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 (x3 x9 x11 x13 x14)) = Bool.false := by
  classical
  let seeds : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
  let row := fun (z : ℕ × ℕ) (m t : Fin 13) (d : Bool) =>
        let f := fun (a b : ℕ) (i : Fin 13) => if d = true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
        Fin.append (f z.1 z.2) (f z.2 z.1)
  obtain ⟨q,R,rect,raw,grow,root⟩ := search
  let k : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
  let L : List Bool → Fin 27 → Bool := fun (x : List Bool) => Fin.lastCases (if q.val = 0 then x.getD 0 false && x.getD k.val false
        else x.getD 0 false || x.getD k.val false) (fun i : Fin 26 => x.getD i.val false)
  let P := fun e : Fin 13 × Fin 13 => L (incidenceInput {e.1} {e.2})
  let N := fun v : Finset (Fin 13) × Finset (Fin 13) => L (incidenceInput v.1 v.2)
  let S := fun w => Prod.map P N '' R w
  have rectS : ∀ w, ∃ A B : Set (Fin 27 → Bool), S w = A ×ˢ B := by
    intro w
    obtain ⟨A,B,h⟩ := rect w
    exact ⟨P '' A,N '' B,by dsimp [S]; rw [h,Set.prodMap_image_prod]⟩
  obtain ⟨C,hm,hback,hs,hout⟩ := synthesize 27 62 88 S (by decide) rectS (by
    intro i z hz
    obtain ⟨e,he,rfl⟩ := hz
    exact raw i e he) (by
    intro j hj
    obtain ⟨a,ha,b,hb,cover⟩ := grow j hj
    refine ⟨a,ha,b,hb,?_⟩
    rintro _ ⟨e,he,rfl⟩
    exact (cover he).elim (fun ha => Or.inl ⟨e,ha,rfl⟩) (fun hb => Or.inr ⟨e,hb,rfl⟩))
  have compare (u : Fin 13 × Fin 13) (hu : u ∈ incidences singerLines3) (v : Finset (Fin 13) × Finset (Fin 13)) (hv : IsMaximalFalse singerLines3 v.1 v.2) (hg : IsGeneric singerLines3 3 v.1 v.2) :
      circuitFun 27 C (P u) = true ∧ circuitFun 27 C (N v) = false :=
    hout (Prod.map P N (u,v)) ⟨(u,v),root u hu v hv hg,rfl⟩
  let D : Finset (Fin 13) := {0,1,3,9}
  have flag : ∀ p l : Fin 13, (p,l) ∈ incidences singerLines3 ↔ ∃ d ∈ D, p = l+d := by decide +kernel
  have flagRow : ∀ p l : Fin 13, List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) =
      incidenceInput {p} {l} := by decide +kernel
  let aug : (Fin 26 → Bool) → Fin 27 → Bool := fun (x : Fin 26 → Bool) => Fin.lastCases
      (if (decide (q.val = 0)) = true then x 0 && x k else x 0 || x k) x
  have lift_eq (x : Fin 26 → Bool) : L (List.ofFn x) = aug x := by
    have rd (t : Fin 26) : (List.ofFn x).getD t.val false = x t := by
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have rz : (List.ofFn x).getD 0 false = x 0 := rd 0
    have rf : (fun i : Fin 26 => (List.ofFn x).getD i.val false) = x := funext rd
    dsimp only [L,aug]
    rw [rz,rd k,rf]
    by_cases eqzero : q.val = 0 <;> simp [eqzero]
  obtain ⟨X0,Y0,hmax,hgen,_⟩ := geometry (7,904) (by decide) 1 (by decide) 0 false
  refine ⟨q,C,hm,hback,hs.le,?_,?_⟩
  · intro p l hit
    have ev := (compare (p,l) ((flag p l).mpr hit) (X0,Y0) hmax hgen).1
    change circuitFun 27 C (aug _) = true
    rw [←lift_eq (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)),flagRow]
    exact ev
  · intro z hz m hm t d
    obtain ⟨X,Y,hmax,hgen,eqn⟩ := geometry z hz m hm t d
    have ev := (compare (0,0) (by decide) (X,Y) hmax hgen).2
    change circuitFun 27 C (aug (row z m t d)) = false
    rw [← lift_eq,show List.ofFn (row z m t d) = incidenceInput X Y from eqn]
    exact ev
