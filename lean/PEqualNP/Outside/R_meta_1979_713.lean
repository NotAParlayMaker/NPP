import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1979_713
    (geometry : let rel := fun (d : Bool) (p l : Fin 13) => (if d then l-p else p-l) ∈ ([0,1,3,9] : List (Fin 13))
      let cap := fun d (a : Finset (Fin 13)) => ∀ l, (a.filter (fun p => rel d p l)).card ≤ 2
      let ext := fun d (a : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ a, ¬rel d p l)
      ∀ a b, cap false a → cap true b → b ⊆ ext false a →
        ∃ (d : Bool) (t : Finset (Fin 13)), t.card=3 ∧ cap d t ∧
          (if d then b ⊆ t ∧ a ⊆ ext d t else a ⊆ t ∧ b ⊆ ext d t))
    (synthesis : let rel := fun (d : Bool) (p l : Fin 13) => (if d then l-p else p-l) ∈ ([0,1,3,9] : List (Fin 13))
      let cap := fun d (a : Finset (Fin 13)) => ∀ l, (a.filter (fun p => rel d p l)).card ≤ 2
      let ext := fun d (a : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ a, ¬rel d p l)
      let row := fun (a b : Finset (Fin 13)) (i : Fin 26) =>
        decide ((∃ p ∈ a, i = Fin.castAdd 13 p) ∨ ∃ l ∈ b, i = Fin.natAdd 13 l)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ p l, rel false p l → circuitFun 26 C (row {p} {l}) = true) ∧
        ∀ d t, t.card=3 → cap d t →
          circuitFun 26 C (if d then row (ext d t) t else row t (ext d t)) = false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  have order : ∀ (n : ℕ) (C : Circuit), Monotone2 C → Monotone (circuitFun n C) := by
    let le := fun (a b : List Bool) => ∀ i, a.getD i false = true → b.getD i false = true
    let step := fun (xs : List Bool) (g : Gate) => xs ++ [g.op.eval (g.inputs.map (fun i => xs.getD i false))]
    have wires : ∀ (gs : List Gate) (a b : List Bool),
        (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        a.length = b.length → le a b → le (gs.foldl step a) (gs.foldl step b) := by
      intro gs
      induction gs with
      | nil => exact fun _ _ _ _ ab => ab
      | cons g gs ih =>
        intro a b good len ab
        apply ih _ _ (fun v hv => good v (List.mem_cons_of_mem _ hv))
        · simp [step,len]
        · have gate : g.op.eval (g.inputs.map (fun i => a.getD i false)) = true →
              g.op.eval (g.inputs.map (fun i => b.getD i false)) = true := by
            rcases good g List.mem_cons_self with h|h <;> rw [h]
            · change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
              simp only [List.all_eq_true,List.mem_map,id_eq,forall_exists_index,and_imp]
              intro hit v i hi e
              subst v
              exact ab i (hit _ i hi rfl)
            · change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
              simp only [List.any_eq_true,List.mem_map,id_eq]
              rintro ⟨v,⟨i,hi,rfl⟩,hit⟩
              exact ⟨_,⟨i,hi,rfl⟩,ab i hit⟩
          intro i prev
          dsimp only [step] at prev ⊢
          by_cases early : i < a.length
          · rw [List.getD_append _ _ _ _ early] at prev
            rw [List.getD_append _ _ _ _ (by omega)]
            exact ab i prev
          · rw [List.getD_append_right _ _ _ _ (by omega)] at prev ⊢
            rw [←len]
            by_cases last : i=a.length
            · simpa [last] using gate (by simpa [last] using prev)
            · rw [List.getD_eq_default _ _ (by simp; omega)] at prev
              exact Bool.noConfusion prev
    intro n C mc x y xy
    apply Bool.le_iff_imp.mpr
    apply wires C.gates (List.ofFn x) (List.ofFn y) (fun g hg => (mc g hg).1) (by simp)
    intro i hit
    by_cases hi : i<n
    · rw [List.getD_eq_getElem _ _ (by simpa),List.getElem_ofFn] at hit ⊢
      exact Bool.le_iff_imp.mp (xy ⟨i,hi⟩) hit
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hit
      exact Bool.noConfusion hit
  let rel := fun (d : Bool) (p l : Fin 13) => (if d then l-p else p-l) ∈ ([0,1,3,9] : List (Fin 13))
  let cap := fun d (a : Finset (Fin 13)) => ∀ l, (a.filter (fun p => rel d p l)).card ≤ 2
  let ext := fun d (a : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ a, ¬rel d p l)
  let row := fun (a b : Finset (Fin 13)) (i : Fin 26) =>
        decide ((∃ p ∈ a, i = Fin.castAdd 13 p) ∨ ∃ l ∈ b, i = Fin.natAdd 13 l)
  obtain ⟨C,mc,sz,yes,no⟩ := synthesis
  refine ⟨C,mc,sz,?_,?_⟩
  · intro p l edge
    have h : rel false p l := by
      simpa only [rel,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,
        or_false,Finset.mem_insert,Finset.mem_singleton] using edge
    simpa only [row,Finset.mem_singleton,exists_eq_left] using yes p l h
  · intro a b avoid pc lc
    have ca : cap false a := by
      simpa only [cap,rel,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,
        or_false,Finset.mem_insert,Finset.mem_singleton] using pc
    have cb : cap true b := by
      simpa only [cap,rel,↓reduceIte,List.mem_cons,List.not_mem_nil,
        or_false,Finset.mem_insert,Finset.mem_singleton] using lc
    have ab : b ⊆ ext false a := by
      intro l hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      intro p hp
      simpa only [rel,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,
        or_false,Finset.mem_insert,Finset.mem_singleton] using avoid p hp l hl
    have ordered {a b s t : Finset (Fin 13)} (aa : a ⊆ s) (bb : b ⊆ t) :
        row a b ≤ row s t := by
      intro i
      apply Bool.le_iff_imp.mpr
      change decide _ = true → decide _ = true
      intro hit
      apply decide_eq_true
      rcases of_decide_eq_true hit with ⟨p,hp,e⟩|⟨l,hl,e⟩
      · exact Or.inl ⟨p,aa hp,e⟩
      · exact Or.inr ⟨l,bb hl,e⟩
    obtain ⟨d,t,size,ct,sub⟩ := geometry a b ca cb ab
    have top := no d t size ct
    change circuitFun 26 C (row a b) = false
    cases d with
    | false =>
      have mono := order 26 C mc (ordered sub.1 sub.2)
      exact Bool.eq_false_iff.mpr (fun h => Bool.noConfusion ((Bool.le_iff_imp.mp mono h).symm.trans top))
    | true =>
      have mono := order 26 C mc (ordered sub.2 sub.1)
      exact Bool.eq_false_iff.mpr (fun h => Bool.noConfusion ((Bool.le_iff_imp.mp mono h).symm.trans top))
