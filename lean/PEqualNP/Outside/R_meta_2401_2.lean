import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection

-- The negative tests become point quadrangles and line quadrangles.
set_option maxRecDepth 40000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2401_2
    (shape : ∀ Q : Finset (Fin 13),
      IsFalseInput singerLines3 Q (missLines singerLines3 Q) →
      InNoLine singerLines3 Q → InNoPencil singerLines3 (missLines singerLines3 Q) →
      IsQuadrangle singerLines3 Q ∨ IsQuadrangle
        (fun p : Fin 13 => Finset.univ.filter (fun l : Fin 13 => p ∈ singerLines3 l))
        (missLines singerLines3 Q))
    (build :
      let S := singerLines3
      let D (p : Fin 13) := Finset.univ.filter (fun l : Fin 13 => p ∈ S l)
      ∃ (k : Fin 4) (C : Circuit), Monotone2 C ∧ ReadsBack 27 C ∧ C.size ≤ 62 ∧
        let j : ℕ := if k.val = 1 then 1 else if k.val = 3 then 14 else 13
        let run (x : List Bool) := C.eval (x ++
          [if k.val = 0 then x.getD 0 false && x.getD j false else x.getD 0 false || x.getD j false])
        (∀ l : Fin 13, ∀ p ∈ S l, run (incidenceInput {p} {l}) = true) ∧
          (∀ Q ∈ quadrangles S, run (incidenceInput Q (missLines S Q)) = false) ∧
          ∀ L ∈ quadrangles D, run (incidenceInput (missLines D L) L) = false) :
∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false
 := by
  obtain ⟨k,C,hmon,hback,hsize,hpos,hquad,hdual⟩ := build
  refine ⟨k,C,hmon,hback,hsize,?_⟩
  let S := singerLines3
  let D (p : Fin 13) := Finset.univ.filter (fun l : Fin 13 => p ∈ S l)
  let offsets : Finset (Fin 13) := {0,1,3,9}
  let inc (p l : Fin 13) := ∃ d ∈ offsets, p=l+d
  let j : Fin 26 := if k.val=1 then 1 else if k.val=3 then 14 else 13
  let extend (x : Fin 26 → Bool) (i : Fin 27) : Bool :=
    Fin.lastCases (if decide (k.val=0) = true then x 0 && x j else x 0 || x j) x i
  let run (x : List Bool) :=
    C.eval (x ++ [if k.val=0 then x.getD 0 false && x.getD j.val false
      else x.getD 0 false || x.getD j.val false])
  have idx : j.val = if k.val=1 then 1 else if k.val=3 then 14 else 13 := by
    dsimp [j]
    split_ifs <;> rfl
  have hit (p l : Fin 13) : inc p l ↔ p ∈ S l := by
    have all : ∀ p l : Fin 13, inc p l ↔ p ∈ S l := by
      dsimp only [inc,offsets,S]
      decide +kernel
    exact all p l
  have val (x : Fin 26 → Bool) (i : Fin 26) :
      (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have last (x : Fin 26 → Bool) (v : Bool) :
      List.ofFn (fun i : Fin 27 => Fin.lastCases v x i) = List.ofFn x ++ [v] := by
    rw [List.ofFn_succ']
    simp only [Fin.lastCases_castSucc,List.concat_eq_append]
    congr 2
  have eval (x : Fin 26 → Bool) :
      circuitFun 27 C (extend x) = run (List.ofFn x) := by
    change C.eval (List.ofFn (fun i : Fin 27 => Fin.lastCases _ x i)) = _
    rw [last]
    unfold run
    rw [show (List.ofFn x).getD 0 false = x 0 from val x 0, val x j]
    simp only [decide_eq_true_eq]
  have support (Q L : Finset (Fin 13)) (x : Fin 26 → Bool)
      (h : ∀ i, x i = true ↔ (∃ p ∈ Q, i = Fin.castAdd 13 p) ∨
        ∃ l ∈ L, i = Fin.natAdd 13 l) :
      List.ofFn x = incidenceInput Q L := by
    let y : Fin 26 → Bool := Fin.append
      (fun p : Fin 13 => decide (p ∈ Q)) (fun l : Fin 13 => decide (l ∈ L))
    have same : x = y := by
      funext i
      refine Fin.addCases (m := 13) (n := 13)
        (motive := fun i => x i = y i) (fun p => ?_) (fun l => ?_) i
      · change x (Fin.castAdd 13 p) = Fin.append _ _ (Fin.castAdd 13 p)
        rw [Fin.append_left,Bool.eq_iff_iff,h,decide_eq_true_eq]
        constructor
        · rintro (⟨q,hq,eq⟩ | ⟨l,_,eq⟩)
          · have same := (Fin.castAdd_injective 13 13) eq
            exact same.symm ▸ hq
          · have e := congrArg Fin.val eq
            change p.val = 13+l.val at e
            omega
        · intro hp
          exact Or.inl ⟨p,hp,rfl⟩
      · change x (Fin.natAdd 13 l) = Fin.append _ _ (Fin.natAdd 13 l)
        rw [Fin.append_right,Bool.eq_iff_iff,h,decide_eq_true_eq]
        constructor
        · rintro (⟨p,_,eq⟩ | ⟨q,hq,eq⟩)
          · have e := congrArg Fin.val eq
            change 13+l.val = p.val at e
            omega
          · have same := (Fin.natAdd_injective 13 13) eq
            exact same.symm ▸ hq
        · intro hl
          exact Or.inr ⟨l,hl,rfl⟩
    rw [same]
    exact List.ofFn_fin_append _ _
  change (∀ p l : Fin 13, inc p l → circuitFun 27 C
      (extend (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) ∧ _
  constructor
  · intro p l hp
    let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    have hx : List.ofFn x = incidenceInput {p} {l} := by
      apply support {p} {l} x
      intro i
      simp [x]
    change circuitFun 27 C (extend x) = true
    rw [eval,hx]
    simpa only [run,idx] using hpos l p ((hit p l).mp hp)
  · intro Q
    dsimp only
    intro closure hGen x hx
    let L := missLines S Q
    have memL (l : Fin 13) : l ∈ L ↔ ∀ p ∈ Q, ¬ inc p l := by
      change (l ∈ Finset.univ.filter (fun t : Fin 13 => Disjoint (S t) Q)) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
      constructor
      · intro h p hp hi
        exact h ((hit p l).mp hi) hp
      · intro h p hi hp
        exact h p hp ((hit p l).mpr hi)
    have noLine : InNoLine S Q := by
      intro l h
      exact hGen.1 ⟨l,fun p hp => (hit p l).mpr (h hp)⟩
    have noPencil : InNoPencil S L := by
      intro p h
      exact hGen.2 ⟨p,fun l hl => (hit p l).mpr (h l ((memL l).mpr hl))⟩
    have falseRows : IsFalseInput S Q L := by
      intro l hl
      exact (Finset.mem_filter.mp hl).2
    have link : missLines D L = Q := by
      ext p
      change (p ∈ Finset.univ.filter (fun u : Fin 13 => Disjoint (D u) L)) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,D]
      constructor
      · intro h
        by_contra outside
        obtain ⟨l,hl,hi⟩ := closure p outside
        exact h ((hit p l).mp hi) ((memL l).mpr hl)
      · intro hp l had hl
        exact (memL l).mp hl p hp ((hit p l).mpr had)
    have supported : List.ofFn x = incidenceInput Q L := by
      apply support Q L x
      intro i
      constructor
      · intro h
        rcases (hx i).mp h with hp | ⟨l,e,hl⟩
        · exact Or.inl hp
        · exact Or.inr ⟨l,(memL l).mpr hl,e⟩
      · intro h
        apply (hx i).mpr
        rcases h with hp | ⟨l,hl,e⟩
        · exact Or.inl hp
        · exact Or.inr ⟨l,e,(memL l).mp hl⟩
    change circuitFun 27 C (extend x) = false
    rw [eval,supported]
    have quad (E : Fin 13 → Finset (Fin 13)) (U : Finset (Fin 13))
        (h : IsQuadrangle E U) : U ∈ quadrangles E := by
      change U ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
        (fun V => ∀ l : Fin 13, (V ∩ E l).card ≤ 2)
      change U.card = 4 ∧ ∀ l : Fin 13, (U ∩ E l).card ≤ 2 at h
      simpa only [Finset.mem_filter,Finset.mem_powersetCard,
        Finset.subset_univ,true_and] using h
    rcases shape Q falseRows noLine noPencil with q | d
    · simpa only [run,idx] using hquad Q (quad S Q q)
    · rw [← link]
      simpa only [run,idx] using hdual L (quad D L d)
