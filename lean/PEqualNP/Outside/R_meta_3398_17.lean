import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Attach a private eight-cycle to each original vertex by two opposite spokes.
-- Ten new edges and four new matched edges allow fourteen more gates per vertex.
-- The augmented graph has no leaves or four-cycles. The star upper bound is already checked.
set_option synthInstance.maxSize 1024 in
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_3398_17
    (leafless : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         x4 ⊆ x3 →           (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →             (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →               have x12 : Fin x1 × Fin x2 → Prop := fun (x12 : Fin x1 × Fin x2) => (∀ x13 ∈ x3, x13.1 = x12.1 → x13 = x12) ∨ ∀ x13 ∈ x3, x13.2 = x12.2 → x13 = x12;               (∀ x13 ∈ x3, ¬x12 x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ))
    (stars : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         x4 ⊆ x3 →           (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →             (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →               have x12 : Fin x1 × Fin x2 → Prop := fun (x12 : Fin x1 × Fin x2) => (∀ x13 ∈ x3, x13.1 = x12.1 → x13 = x12) ∨ ∀ x13 ∈ x3, x13.2 = x12.2 → x13 = x12;               (∀ x13 ∈ x3, x12 x13 → x13 ∈ x4) → (∃ x14 ∈ x4, x12 x14) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E M C hsq hao eval hsub mr mc _ _ matched
  obtain ⟨e, em, _⟩ := matched
  have nonempty : E.Nonempty := ⟨e, hsub em⟩
  let U := Fin n ⊕ Fin m
  let L := Fin n ⊕ (U × Fin 4)
  let R := Fin m ⊕ (U × Fin 4)
  let Tag := (Fin 4 × Bool) ⊕ Bool
  let step (i : Fin 4) (b : Bool) : Fin 4 := if b then i+1 else i
  let port (b : Bool) : Fin 4 := if b then 2 else 0
  let ring (i j : Fin 4) : Prop := j = i ∨ j = i+1
  let spoke (i : Fin 4) : Prop := i = 0 ∨ i = 2

  let fresh (w : U × Tag) : L × R := Sum.elim
    (fun z => (.inr (w.1,z.1), .inr (w.1,step z.1 z.2)))
    (fun b => Sum.elim (fun p => (.inl p, .inr (.inl p,port b)))
      (fun l => (.inr (.inr l,port b), .inl l)) w.1) w.2

  let adj (E : Finset (Fin n × Fin m)) (x : L) (y : R) : Prop := Sum.elim
    (fun p => Sum.elim (fun l => (p,l) ∈ E) (fun z => z.1 = .inl p ∧ spoke z.2) y)
    (fun w => Sum.elim (fun l => w.1 = .inr l ∧ spoke w.2)
      (fun z => w.1=z.1 ∧ ring w.2 z.2) y) x

  have fresh_adj (E : Finset (Fin n × Fin m)) (t : U × Tag) :
      adj E (fresh t).1 (fresh t).2 := by
    rcases t with ⟨u,t⟩
    rcases t with ⟨i,b⟩ | b <;> cases u <;> cases b <;> simp [fresh, adj, spoke, ring, step, port]

  have square (E : Finset (Fin n × Fin m))
      (free : ∀ a b c d, (a,c) ∈ E → (a,d) ∈ E → (b,c) ∈ E → (b,d) ∈ E → a=b ∨ c=d) :
      ∀ a b c d, adj E a c → adj E a d → adj E b c → adj E b d → a=b ∨ c=d := by
    have sq : ∀ i k j l, ring i j → ring i l → ring k j → ring k l → i=k ∨ j=l := by
      unfold ring; decide
    have sl : ∀ i j k, spoke i → spoke j → ring k i → ring k j → i=j := by
      unfold spoke ring; decide
    have sr : ∀ i j k, spoke i → spoke j → ring i k → ring j k → i=j := by
      unfold spoke ring; decide
    rintro (a | ⟨s,i⟩) (b | ⟨t,k⟩) (c | ⟨u,j⟩) (d | ⟨v,l⟩) ac ad bc bd <;>
      simp [adj] at ac ad bc bd ⊢ <;> grind

  have noLeaf (F : Finset (L × R)) (all : ∀ t, fresh t ∈ F) :
      (∀ a : L, ∃ b c : R, b ≠ c ∧ (a,b) ∈ F ∧ (a,c) ∈ F) ∧
      ∀ b : R, ∃ a c : L, a ≠ c ∧ (a,b) ∈ F ∧ (c,b) ∈ F := by
    have distinct : (0 : Fin 4) ≠ 2 := by decide
    have diff : ∀ i : Fin 4, i ≠ i+1 := by decide
    have back : ∀ j : Fin 4, ∃ i, i ≠ j ∧ step i true = j := by decide
    constructor
    · rintro (a | ⟨u,i⟩)
      · exact ⟨.inr (.inl a,0), .inr (.inl a,2), fun h => distinct (congrArg Prod.snd (Sum.inr.inj h)),
               all (.inl a,.inr false), all (.inl a,.inr true)⟩
      · exact ⟨.inr (u,i), .inr (u,i+1), fun h => diff i (congrArg Prod.snd (Sum.inr.inj h)),
               all (u,.inl (i,false)), all (u,.inl (i,true))⟩
    · rintro (b | ⟨u,j⟩)
      · exact ⟨.inr (.inr b,0), .inr (.inr b,2), fun h => distinct (congrArg Prod.snd (Sum.inr.inj h)),
               all (.inr b,.inr false), all (.inr b,.inr true)⟩
      · obtain ⟨i, ne, h⟩ := back j
        refine ⟨.inr (u,i), .inr (u,j), fun h => ne (congrArg Prod.snd (Sum.inr.inj h)), ?_, all (u,.inl (j,false))⟩
        exact h ▸ all (u,.inl (i,true))

  have decorate (E M : Finset (Fin n × Fin m)) (edge : E.Nonempty)
      (sq : ∀ a b c d, a≠b → c≠d → ¬((a,c)∈E ∧ (a,d)∈E ∧ (b,c)∈E ∧ (b,d)∈E))
      (sub : M ⊆ E) (mr : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e=f)
      (mc : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e=f) :
      ∃ (N K : ℕ) (l : Fin n ↪ Fin N) (r : Fin m ↪ Fin K)
        (B Q : Finset (Fin N × Fin K)) (X : Finset (Fin N)) (Y : Finset (Fin K)),
        let F := E.image (fun e => (l e.1, r e.2)) ∪ B
        (∀ a b c d, a≠b → c≠d → ¬((a,c)∈F ∧ (a,d)∈F ∧ (b,c)∈F ∧ (b,d)∈F)) ∧
        Q ⊆ F ∧ (∀ e ∈ Q, ∀ f ∈ Q, e.1=f.1 → e=f) ∧ (∀ e ∈ Q, ∀ f ∈ Q, e.2=f.2 → e=f) ∧
        (∀ e ∈ F, ¬((∀ d ∈ F, d.1=e.1 → d=e) ∨ ∀ d ∈ F, d.2=e.2 → d=e)) ∧
        B.Nonempty ∧ (∀ e ∈ B, e.1 ∈ X ∨ e.2 ∈ Y) ∧ E.card + M.card + (B.card+X.card+Y.card) ≤ F.card+Q.card := by
    classical
    let N := Fintype.card (L)
    let K := Fintype.card (R)
    let el : L ≃ Fin N := Fintype.equivFin _
    let er : R ≃ Fin K := Fintype.equivFin _
    let l : Fin n ↪ Fin N := ⟨fun p => el (.inl p), fun _ _ h => Sum.inl.inj (el.injective h)⟩
    let r : Fin m ↪ Fin K := ⟨fun p => er (.inl p), fun _ _ h => Sum.inl.inj (er.injective h)⟩
    let old (e : Fin n × Fin m) := (l e.1, r e.2)
    let enc (e : L × R) := (el e.1, er e.2)
    let ex (t : U × Tag) := enc (fresh t)
    let diag (w : U × Fin 4) := enc (.inr w, .inr w)
    let oldE := E.image old
    let B := Finset.univ.image ex
    let F := oldE ∪ B
    let dm := Finset.univ.image diag
    let Q := M.image old ∪ dm
    let xl (s : Fin m × Fin 4) := el (.inr (.inr s.1,s.2))
    let yr (s : Fin n × Fin 4) := er (.inr (.inl s.1,s.2))
    let X := Finset.univ.image xl
    let Y := Finset.univ.image yr
    have oi : Function.Injective old := fun _ _ h => Prod.ext
      (l.injective (congrArg Prod.fst h)) (r.injective (congrArg Prod.snd h))
    have di : Function.Injective diag := fun _ _ h =>
      Sum.inr.inj (el.injective (congrArg Prod.fst h))
    have apart (e : Fin n × Fin m) (t : U × Tag) : old e ≠ ex t := by
      intro h
      rcases t with ⟨u,t⟩
      rcases t with ⟨i,b⟩ | b <;> cases u <;> first
        | exact Sum.inl_ne_inr (el.injective (congrArg Prod.fst h))
        | exact Sum.inl_ne_inr (er.injective (congrArg Prod.snd h))
    have edis : Disjoint oldE B := by
      apply Finset.disjoint_left.mpr
      intro e h1 h2
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨v,_,h⟩ := Finset.mem_image.mp h2
      exact apart u v h.symm
    have mdis : Disjoint (M.image old) dm := by
      apply Finset.disjoint_left.mpr
      intro e h1 h2
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨v,_,h⟩ := Finset.mem_image.mp h2
      exact Sum.inr_ne_inl (el.injective (congrArg Prod.fst h))
    have sound (w : Fin N × Fin K) (hw : w ∈ F) : adj E (el.symm w.1) (er.symm w.2) := by
      rcases Finset.mem_union.mp hw with ho | hf
      · obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp ho
        change adj E (el.symm (el (.inl a))) (er.symm (er (.inl b)))
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hab
      · obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hf
        simpa [ex,enc] using fresh_adj E t
    have squareE : ∀ a b c d, (a,c)∈E → (a,d)∈E → (b,c)∈E → (b,d)∈E → a=b ∨ c=d := by
      intro a b c d ac ad bc bd
      by_contra! h
      exact sq a b c d h.1 h.2 ⟨ac,ad,bc,bd⟩
    have freshMem (t : U × Tag) : ex t ∈ F :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
    let raw := Finset.univ.image (fresh)
    have witnesses := noLeaf raw (fun t => Finset.mem_image_of_mem _ (Finset.mem_univ t))
    have transfer {a : L} {b : R} (h : (a,b)∈raw) : (el a,er b)∈F := by
      obtain ⟨t,_,ht⟩ := Finset.mem_image.mp h
      change enc (a,b) ∈ F
      rw [← ht]
      exact freshMem t
    refine ⟨N,K,l,r,B,Q,X,Y,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro a b c d ab cd h
      exact (square E squareE (el.symm a) (el.symm b) (er.symm c) (er.symm d)
        (sound (a,c) h.1) (sound (a,d) h.2.1) (sound (b,c) h.2.2.1) (sound (b,d) h.2.2.2)).elim
          (fun e => ab (el.symm.injective e)) (fun e => cd (er.symm.injective e))
    · intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (sub hu))
      · obtain ⟨⟨u,i⟩,_,rfl⟩ := Finset.mem_image.mp h
        exact freshMem (u,.inl (i,false))
    · intro e he f hf h
      rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf <;>
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he <;> obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hf
      · exact congrArg old (mr u hu v hv (l.injective h))
      · exact (Sum.inl_ne_inr (el.injective h)).elim
      · exact (Sum.inr_ne_inl (el.injective h)).elim
      · exact congrArg diag (Sum.inr.inj (el.injective h))
    · intro e he f hf h
      rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf <;>
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he <;> obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hf
      · exact congrArg old (mc u hu v hv (r.injective h))
      · exact (Sum.inl_ne_inr (er.injective h)).elim
      · exact (Sum.inr_ne_inl (er.injective h)).elim
      · exact congrArg diag (Sum.inr.inj (er.injective h))
    · rintro ⟨a,b⟩ _ (h | h)
      · obtain ⟨c,d,ne,hc,hd⟩ := witnesses.1 (el.symm a)
        have h1 := h (a,er c) (by simpa only [Equiv.apply_symm_apply] using transfer hc) rfl
        have h2 := h (a,er d) (by simpa only [Equiv.apply_symm_apply] using transfer hd) rfl
        exact ne (er.injective (congrArg Prod.snd (h1.trans h2.symm)))
      · obtain ⟨c,d,ne,hc,hd⟩ := witnesses.2 (er.symm b)
        have h1 := h (el c,b) (by simpa only [Equiv.apply_symm_apply] using transfer hc) rfl
        have h2 := h (el d,b) (by simpa only [Equiv.apply_symm_apply] using transfer hd) rfl
        exact ne (el.injective (congrArg Prod.fst (h1.trans h2.symm)))
    · obtain ⟨⟨a,_⟩,_⟩ := edge
      exact ⟨_, Finset.mem_image_of_mem ex (Finset.mem_univ (.inl a,.inr false))⟩
    · intro e he
      obtain ⟨⟨u,t⟩,_,rfl⟩ := Finset.mem_image.mp he
      rcases u with p | j
      · right
        rcases t with ⟨i,b⟩ | b
        · exact Finset.mem_image_of_mem yr (Finset.mem_univ (p, step i b))
        · exact Finset.mem_image_of_mem yr (Finset.mem_univ (p, port b))
      · left
        rcases t with ⟨i,b⟩ | b
        · exact Finset.mem_image_of_mem xl (Finset.mem_univ (j,i))
        · exact Finset.mem_image_of_mem xl (Finset.mem_univ (j,port b))
    · have cardE : oldE.card = E.card := Finset.card_image_of_injective _ oi
      have cardM := Finset.card_image_of_injective M oi
      have cardF := Finset.card_union_of_disjoint edis
      have cardQ := Finset.card_union_of_disjoint mdis
      have dsize : dm.card = (n+m)*4 := by
        simp [dm, Finset.card_image_of_injective _ di, U]
      have xsize : X.card ≤ m*4 := (Finset.card_image_le).trans_eq (by simp)
      have ysize : Y.card ≤ n*4 := (Finset.card_image_le).trans_eq (by simp)
      change E.card + M.card + (B.card+X.card+Y.card) ≤ (oldE∪B).card+(M.image old∪dm).card
      omega

  have sizeEq (T : Circuit) : T.size = T.gates.length := rfl
  let push (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

  have foldLen (gs : List Gate) (w : List Bool) : (gs.foldl push w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [push]; omega

  have oldWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl push w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (push w g) (by simp [push]; omega)]
      simp [push, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  let liftGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map ρ⟩

  have simulate (ρ : ℕ → ℕ) (gs : List Gate) (s t : List Bool)
      (agree : ∀ i, t.getD (ρ i) false = s.getD i false)
      (before : ∀ i, i < s.length → ρ i < t.length)
      (after : ∀ i, s.length ≤ i → ρ i = t.length + (i-s.length)) :
      ∀ i, ((gs.map (liftGate ρ)).foldl push t).getD (ρ i) false = (gs.foldl push s).getD i false := by
    induction gs generalizing s t with
    | nil => exact agree
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      let z := g.op.eval (g.inputs.map fun i => s.getD i false)
      have hz : push t (liftGate ρ g) = t ++ [z] := by
        have bits : (g.inputs.map ρ).map (fun i => t.getD i false) = g.inputs.map (fun i => s.getD i false) := by
          rw [List.map_map]
          exact List.map_congr_left (fun i _ => agree i)
        change t ++ [g.op.eval ((g.inputs.map ρ).map _)] = _
        rw [bits]
      rw [hz]
      change ∀ i, ((gs.map (liftGate ρ)).foldl push (t++[z])).getD (ρ i) false =
        (gs.foldl push (s++[z])).getD i false
      apply ih
      · intro i
        rcases Nat.lt_trichotomy i s.length with hi | rfl | hi
        · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
            List.getElem?_append_left (before i hi)] using agree i
        · simp [after s.length le_rfl, List.getD_eq_getElem?_getD]
        · have ht := after i (by omega)
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none
            (show (s++[z]).length ≤ i by simp; omega), List.getElem?_eq_none
            (show (t++[z]).length ≤ ρ i by simp; omega)]
      · intro i hi
        simp at hi ⊢
        by_cases h : i < s.length
        · have := before i h; omega
        · have := after i (by omega); omega
      · intro i hi
        simp at hi ⊢
        have := after i (by omega)
        omega

  let good (n : ℕ) (gs : List Gate) := ∀ j (hj : j < gs.length),
    ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) ∧ (gs[j]).inputs.length = 2 ∧
      ∀ i ∈ (gs[j]).inputs, i < n+j

  have goodModel (n : ℕ) (C : Circuit) : good n C.gates ↔ IsAO2 n C := by
    have ga (j) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
      change C.gates.getD j _ = _
      simp [List.getD_eq_getElem?_getD, hj]
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
        exact (h j hj).1
      · intro j hj
        rw [ga j hj]
        exact (h j hj).2.2
      · intro g hg
        obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
        exact (h j hj).2.1
    · intro h j hj
      refine ⟨h.1 _ (List.getElem_mem hj), h.2.2 _ (List.getElem_mem hj), ?_⟩
      rw [← ga j hj]
      exact h.2.1 j hj

  have goodAppend (n : ℕ) (ls rs : List Gate) (h : good n ls) (k : good (n+ls.length) rs) :
      good n (ls++rs) := by
    intro i hi
    by_cases pre : i < ls.length
    · rw [List.getElem_append_left pre]
      exact h i pre
    · have sub : i-ls.length < rs.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega)]
      simpa only [show n+ls.length+(i-ls.length) = n+i by omega] using k _ sub

  let ren {n N : ℕ} (f : Fin n → Fin N) (offset w : ℕ) : ℕ :=
    if h : w < n then (f ⟨w,h⟩).val else offset + (w-n)

  have goodLift {n N : ℕ} (f : Fin n → Fin N) (k : ℕ) (gs : List Gate) (h : good n gs) :
      good (N+k) (gs.map (liftGate (ren f (N+k)))) := by
    intro i hi
    have hl : i < gs.length := by simpa using hi
    simp only [List.getElem_map, liftGate, List.length_map]
    refine ⟨(h i hl).1,(h i hl).2.1,?_⟩
    intro j hj
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hj
    have := (h i hl).2.2 v hv
    unfold ren
    split
    · rename_i hlt
      have := (f ⟨v,hlt⟩).isLt
      omega
    · omega

  let liftC {n N : ℕ} (f : Fin n → Fin N) (p : List Gate) (C : Circuit) : Circuit :=
    let ρ := ren f (N+p.length)
    ⟨p ++ C.gates.map (liftGate ρ), ρ C.output⟩

  have liftEval {n N : ℕ} (f : Fin n → Fin N) (p : List Gate) (C : Circuit) (x : Fin N → Bool) :
      circuitFun N (liftC f p C) x = circuitFun n C (x ∘ f) := by
    let t := p.foldl push (List.ofFn x)
    let s := List.ofFn (x ∘ f)
    have ht : t.length = N+p.length := by simp [t,foldLen]
    have hs : s.length = n := by simp [s]
    let ρ := ren f (N+p.length)
    have before (i : ℕ) (hi : i < s.length) : ρ i < t.length := by
      have hn : i < n := hs ▸ hi
      simpa [ρ,ren,hn,ht] using (show (f ⟨i,hn⟩).val < N+p.length by have := (f ⟨i,hn⟩).isLt; omega)
    have after (i : ℕ) (hi : s.length ≤ i) : ρ i = t.length + (i-s.length) := by
      have hn : ¬i < n := by omega
      simp [ρ,ren,hn,ht,hs]
    have agrees (i : ℕ) : t.getD (ρ i) false = s.getD i false := by
      by_cases hi : i < n
      · change (p.foldl push (List.ofFn x)).getD (ren f (N+p.length) i) false = _
        rw [show ren f (N+p.length) i = (f ⟨i,hi⟩).val by simp [ren,hi],
          oldWire _ _ _ (by simp)]
        simp [s,List.getD_eq_getElem?_getD,hi]
      · have hρ := after i (by omega)
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show t.length ≤ ρ i by omega),
          List.getElem?_eq_none (show s.length ≤ i by omega)]
    change ((p ++ C.gates.map (liftGate ρ)).foldl push (List.ofFn x)).getD (ρ C.output) false =
      (C.gates.foldl push s).getD C.output false
    rw [List.foldl_append]
    exact simulate ρ C.gates s t agrees before after C.output

  have join {n N : ℕ} (f : Fin n → Fin N) (C S : Circuit)
      (hc : IsAO2 n C) (hs : IsAO2 N S) (co : C.output < n+C.size) (so : S.output < N+S.size) :
      ∃ D : Circuit, IsAO2 N D ∧ D.size = C.size+S.size+1 ∧
        ∀ x, circuitFun N D x = (circuitFun n C (x ∘ f) || circuitFun N S x) := by
    let A := liftC f [] C
    let B := liftC (id : Fin N → Fin N) A.gates S
    have aLen : A.gates.length = C.size := by simp [A,liftC,sizeEq]
    have bLen : B.gates.length = C.size+S.size := by simp [B,liftC,aLen,sizeEq]
    have liftBound {v w} (g : Fin v → Fin N) (k i : ℕ) (hi : i < v+w) :
        ren g (N+k) i < N+k+w := by
      unfold ren
      split
      · rename_i h
        have := (g ⟨i,h⟩).isLt
        omega
      · omega
    have ao : A.output < N+A.gates.length := by
      simpa [A,liftC,sizeEq] using liftBound f 0 C.output co
    have bo : B.output < N+B.gates.length := by
      simpa [B,liftC,sizeEq,Nat.add_assoc] using liftBound (id : Fin N → Fin N) A.gates.length S.output so
    have ga : good N A.gates := by
      simpa [A,liftC] using goodLift f 0 C.gates ((goodModel n C).2 hc)
    have gb : good N B.gates := goodAppend _ _ _ ga
      (goodLift (id : Fin N → Fin N) A.gates.length S.gates ((goodModel N S).2 hs))
    let g : Gate := ⟨GateOp.or,[A.output,B.output]⟩
    let D : Circuit := ⟨B.gates++[g],N+B.gates.length⟩
    have last : good (N+B.gates.length) [g] := by
      intro j hj
      have : j = 0 := by simp at hj; omega
      subst j
      have ab : A.output < N+B.gates.length := by omega
      simpa [g] using And.intro ab bo
    refine ⟨D,(goodModel N D).1 (goodAppend _ _ _ gb last),?_,?_⟩
    · change (B.gates++[g]).length = _
      simp [bLen]
    · intro x
      let t := A.gates.foldl push (List.ofFn x)
      let w := B.gates.foldl push (List.ofFn x)
      have wl : w.length = N+B.gates.length := by simp [w,foldLen]
      have hA : w.getD A.output false = circuitFun n C (x ∘ f) := by
        change ((A.gates ++ S.gates.map _).foldl push (List.ofFn x)).getD A.output false = _
        rw [List.foldl_append, oldWire _ _ _ (by simpa [foldLen] using ao)]
        exact liftEval f [] C x
      have hB : w.getD B.output false = circuitFun N S x := liftEval (id : Fin N → Fin N) A.gates S x
      change ((B.gates++[g]).foldl push (List.ofFn x)).getD (N+B.gates.length) false = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have binary (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
      change (w ++ [GateOp.or.eval [w.getD A.output false, w.getD B.output false]]).getD (N+B.gates.length) false = _
      rw [binary]
      rw [← wl,hA,hB]
      simp [List.getD_eq_getElem?_getD]

  obtain ⟨N,K,l,r,B,Q,X,Y,hSquare,hSub,hRow,hCol,hNoLeaf,Bne,hCover,budget⟩ :=
    decorate E M nonempty hsq hsub mr mc
  let old (e : Fin n × Fin m) := (l e.1,r e.2)
  let F := E.image old ∪ B
  let ι : Fin (n+m) → Fin (N+K) := Fin.addCases (fun p => Fin.castAdd K (l p)) (fun b => Fin.natAdd N (r b))
  have il (p : Fin n) : ι (Fin.castAdd m p) = Fin.castAdd K (l p) := by simp [ι]
  have ir (q : Fin m) : ι (Fin.natAdd n q) = Fin.natAdd N (r q) := by simp [ι]
  obtain ⟨S,_,sao,ssize,seval,_⟩ := stars N K B X Y hCover
  have valid {k : ℕ} (T : Circuit) (h : circuitFun k T (fun _ => true) = true) : T.output < k+T.size := by
    by_contra! hn
    change (T.gates.foldl push (List.ofFn (fun _ : Fin k => true))).getD T.output false = true at h
    have len : (T.gates.foldl push (List.ofFn (fun _ : Fin k => true))).length = k+T.size := by
      simp only [foldLen, List.length_ofFn, sizeEq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (len.trans_le hn)] at h
    contradiction
  obtain ⟨⟨p,q⟩,pq⟩ := nonempty
  have co := valid C (by rw [eval]; exact decide_eq_true ⟨p,q,pq,rfl,rfl⟩)
  obtain ⟨⟨u,v⟩,uv⟩ := Bne
  have so := valid S (by rw [seval]; exact decide_eq_true ⟨u,v,uv,rfl,rfl⟩)
  obtain ⟨D,dao,dsize,deval⟩ := join ι C S hao sao co so
  have model (x : Fin (N+K) → Bool) : circuitFun (N+K) D x =
      decide (∃ i j, (i,j)∈F ∧ x (Fin.castAdd K i)=true ∧ x (Fin.natAdd N j)=true) := by
    rw [deval,eval,seval]
    have iffB (s t : Bool) : s=t ↔ (s=true ↔ t=true) := by cases s <;> cases t <;> decide
    apply (iffB _ _).2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Function.comp_apply, il, ir]
    constructor
    · rintro (⟨i,j,hij,hi,hj⟩ | ⟨i,j,hij,hi,hj⟩)
      · exact ⟨l i,r j,Finset.mem_union_left _ (Finset.mem_image_of_mem old hij),hi,hj⟩
      · exact ⟨i,j,Finset.mem_union_right _ hij,hi,hj⟩
    · rintro ⟨i,j,hij,hi,hj⟩
      rcases Finset.mem_union.mp hij with ho | hb
      · obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_image.mp ho
        have h1 : l a = i := congrArg Prod.fst heq
        have h2 : r b = j := congrArg Prod.snd heq
        exact Or.inl ⟨a,b,hab,h1 ▸ hi,h2 ▸ hj⟩
      · exact Or.inr ⟨i,j,hb,hi,hj⟩
  have bound := leafless N K F Q D hSquare dao model hSub hRow hCol hNoLeaf
  have positive := Finset.card_pos.mpr (show B.Nonempty from ⟨(u,v),uv⟩)
  change E.card + M.card + (B.card+X.card+Y.card) ≤ F.card+Q.card at budget
  omega
