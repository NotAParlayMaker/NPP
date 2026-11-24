import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.TopForm

-- Trim unused gates and choose the last shared signal in a binary circuit.
-- If it implies the output, replace its later uses with false and join it back by OR.
-- If the output implies it, use true and AND. Both distinct live consumers disappear.
-- Every later surviving wire has at most one consumer, so contraction cannot add sharing.
-- An earlier surviving shared signal retains its function when wire numbers change.
-- A circuit with only comparable shared signals therefore yields a strictly smaller formula.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2223_317
    (floor : ∀ F : DMFormula 14, (∀ x, F.eval x=true ↔ ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) →
      DMFormula.rec (motive := fun _ : DMFormula 14 => Prop) (fun _ sign => sign=true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) F → 28 ≤ F.leaves)
    (prune : ∀ n (C : Circuit), IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∃ x : Fin n → Bool, C.eval (List.ofFn x)=true) →
      ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (n ≤ w))).Nodup →
      let use := fun k j : ℕ => n ≤ C.output ∧ j < C.size ∧ n+k ∈ (gateAt C j).inputs ∧ InConeOrSelf n C j (C.output-n)
      (∀ k i j, i≠j → use k i → use k j →
        (∀ x, gateVal n C k x=true → C.eval (List.ofFn x)=true) ∨
        (∀ x, C.eval (List.ofFn x)=true → gateVal n C k x=true)) →
      ∃ F : DMFormula n, F.leaves ≤ C.size ∧ (∀ x, F.eval x = C.eval (List.ofFn x)) ∧ DMFormula.rec (motive := fun _ : DMFormula n => Prop) (fun _ sign => sign=true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) F)
    (mixed : ∀ (C : Circuit) (p l : Fin 7), IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) → C.size ≤ 27 →
      (∀ x, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) →
      (p=l ∨ p=l+1 ∨ p=l+3) → 2≤C.lineDeg 14 {p.val} → 2≤C.lineDeg 14 {7+l.val} →
      let use := fun k j : ℕ => 14 ≤ C.output ∧ j < C.size ∧ 14+k ∈ (gateAt C j).inputs ∧ InConeOrSelf 14 C j (C.output-14)
      ∀ k i j, i≠j → use k i → use k j →
        (∃ x, C.eval (List.ofFn x)=false ∧ gateVal 14 C k x=true) →
        ∀ a b : Fin 7, (a=b ∨ a=b+1 ∨ a=b+3) →
        gateVal 14 C k (pairInput (Fin.castAdd 7 a) (Fin.natAdd 7 b))=true) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  dsimp only
  intro C p l valid flag dp dl
  obtain ⟨small,ops,correct⟩ := valid
  by_cases tree : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
  · exact ⟨C,⟨small,ops,correct⟩,tree,dp,dl⟩
  exfalso
  have memop (g : Gate) (hg : g ∈ C.gates) : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b := by
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨op,a,b,e,ne,_⟩ := ops j g hj
    exact ⟨op,a,b,e,ne⟩
  have ao : AndOrOnly C := fun g h => (memop g h).1
  have shape : IsAO2 14 C := by
    refine ⟨ao,?_,?_⟩
    · intro j hj a ha
      have h := ops j _ (List.getElem?_eq_getElem hj)
      obtain ⟨u,v,e,_,hu,hv⟩ := h.2
      change a ∈ (C.gates.getD j _).inputs at ha
      rw [List.getD_eq_getElem _ _ hj,e] at ha
      rcases List.mem_cons.mp ha with rfl|hh; exact hu
      have eq : a=v := by simpa using hh
      exact eq ▸ hv
    · intro g hg; obtain ⟨a,b,e,_⟩ := (memop g hg).2; simp [e]
  have distinct (g) (hg : g ∈ C.gates) : g.inputs.Nodup := by
    obtain ⟨a,b,e,ne⟩ := (memop g hg).2; simp [e,ne]
  have pos : ∃ x : Fin 14 → Bool, C.eval (List.ofFn x)=true :=
    ⟨fun _ => true, (correct _).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩⟩
  -- The monotone wire argument follows the checked L-meta-1082 proof.
  let m1587_stp (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have m1587_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
      (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
    rcases lt_trichotomy i W.length with h | h | h
    · rw [if_neg (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · subst h
      simp [List.getD_eq_getElem?_getD]
    · rw [if_neg (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

  have m1587_ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
      (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
    rw [h]
    change (g.inputs.map f).all id = true ↔ _
    simp

  have m1587_ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
      (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
    rw [h]
    change (g.inputs.map f).any id = true ↔ _
    simp

  have m1587_mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      (∀ i, W1.getD i false = true → W2.getD i false = true) →
      ∀ i, (gs.foldl m1587_stp W1).getD i false = true → (gs.foldl m1587_stp W2).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro W1 W2 _ _ H; simpa using H
    | cons g gs ih =>
      intro W1 W2 hl hop H
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (m1587_stp W1 g) (m1587_stp W2 g) (by simp [m1587_stp, hl])
        (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
      intro i
      simp only [m1587_stp, m1587_getD_snoc, hl]
      split_ifs
      · rcases hop g List.mem_cons_self with ha | ho
        · rw [m1587_ev_and g _ ha, m1587_ev_and g _ ha]
          intro h k hk
          exact H k (h k hk)
        · rw [m1587_ev_or g _ ho, m1587_ev_or g _ ho]
          rintro ⟨k, hk, h⟩
          exact ⟨k, hk, H k h⟩
      · exact H i

  have m1587_all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
      (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
      ∀ i, x.getD i false = true → y.getD i false = true := by
    intro i hi
    by_cases h : i < n
    · exact H i h hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
      exact Bool.noConfusion hi

  have mon (n : ℕ) (D : Circuit) (ops : AndOrOnly D) (x y : Fin n → Bool)
      (hle : ∀ p, x p = true → y p = true) (k : ℕ) : gateVal n D k x = true → gateVal n D k y = true := by
    apply m1587_mono D.gates _ _ (by simp) ops _ (n+k)
    apply m1587_all_idx n _ _ (by simp)
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
    simpa only [List.getElem_ofFn] using hle ⟨i, hi⟩
  obtain ⟨F,count,eq,positive⟩ := prune 14 C shape distinct pos tree (by
    intro k i j ne ui uj
    by_cases left : ∀ x, gateVal 14 C k x=true → C.eval (List.ofFn x)=true
    · exact Or.inl left
    · right
      push Not at left
      obtain ⟨bad,hval,hbad⟩ := left
      have mixedrow := mixed C p l shape distinct small correct flag dp dl k i j ne ui uj ⟨bad,by simpa using hbad,hval⟩
      intro x hx
      obtain ⟨a,b,incident,ha,hb⟩ := (correct x).mp hx
      apply mon 14 C ao _ x _ k (mixedrow a b incident)
      intro v hv
      change decide (v=Fin.castAdd 7 a ∨ v=Fin.natAdd 7 b) = true at hv
      have mem : v=Fin.castAdd 7 a ∨ v=Fin.natAdd 7 b := of_decide_eq_true hv
      rcases mem with rfl|rfl; exact ha; exact hb)
  have bound := floor F (fun x => (eq x) ▸ correct x) positive
  omega
