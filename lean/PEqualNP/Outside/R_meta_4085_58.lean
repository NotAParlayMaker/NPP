import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- At the nine-gate cut, a binary gate increases the number of required wires
-- by at most one. NOT reads only its first pin, even if a second pin is listed.
-- Ten required wires therefore force every gate of the suffix to be AND or OR.
-- In the narrower case the retained signals cannot all be one-gate functions.
-- Each vertex remains pivotal with any other vertex fixed to either bit.
-- A two-literal AND or OR can therefore never be the sole signal carrying
-- either of its input vertices. Counting occurrences gives at least ten signals.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4085_58
  (shallow : let raw := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
    let target := fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i=true ∧ x j=true ∧
      (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val=true)
    ∀ (P : Circuit) (S : Finset ℕ), S.card≤9 →
      (∀ i ∈ S, ∃ A : Circuit, FanInTwo A ∧ A.size≤1 ∧
        ∀ x : Fin 10 → Bool, A.eval (raw x)=(P.wires (raw x)).getD i false) →
      ∃ x y : Fin 10 → Bool, (∀ i ∈ S, (P.wires (raw x)).getD i false=(P.wires (raw y)).getD i false) ∧ target x≠target y)
  (narrow : ∀ (P D : Circuit) (S : Finset ℕ), FanInTwo P → P.size ≤ 9 →
    FanInTwo D → D.size ≤ 9 → S.card ≤ 9 → (∀ i ∈ S, i < 11+P.size) →
    (∃ i ∈ S, ¬∃ A : Circuit, FanInTwo A ∧ A.size≤1 ∧ ∀ x : Fin 10 → Bool,
       A.eval (List.ofFn x ++ [!x 0])=(P.wires (List.ofFn x ++ [!x 0])).getD i false) →
    ∃ x : Fin 10 → Bool, D.eval (List.ofFn (fun i : Fin (11+P.size) =>
        if i.val ∈ S then (P.wires (List.ofFn x ++ [!x 0])).getD i.val false else false))
      ≠ (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i=true ∧ x j=true ∧
          (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0 ).testBit j.val = true)) x)
  (wide : ∀ (P D : Circuit) (S : Finset ℕ), FanInTwo P → P.size ≤ 9 →
    Monotone2 D → D.size = 9 → (∀ g ∈ D.gates, g.inputs.toFinset.card=2) →
    S.card = 10 → (∀ i ∈ S, i < 11+P.size) →
    ∃ x : Fin 10 → Bool, D.eval (List.ofFn (fun i : Fin (11+P.size) =>
        if i.val ∈ S then (P.wires (List.ofFn x ++ [!x 0])).getD i.val false else false))
      ≠ (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i=true ∧ x j=true ∧
          (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0 ).testBit j.val = true)) x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin x1.size), ∀ x10 ∈ (x1.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (x1.output ∈ x5 → x1.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (x1.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5 := by
  classical
  intro C legal budget _cut
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let agrees (S : Finset ℕ) (w v : List Bool) := ∀ j ∈ S, w.getD j false = v.getD j false
  let pins (g : Gate) := if g.op = .not then g.inputs.take 1 else g.inputs
  let cost (g : Gate) : ℕ := if 2 ≤ (pins g).toFinset.card then 1 else 0
  let total (gs : List Gate) := (gs.map cost).sum
  have count (gs : List Gate) : total gs ≤ gs.length := by
    induction gs with
    | nil => simp [total]
    | cons g gs ih =>
      have c : cost g ≤ 1 := by simp [cost];split <;> decide
      change (gs.map cost).sum ≤ gs.length at ih
      simp only [total,List.map_cons,List.sum_cons,List.length_cons]
      omega
  have strict (gs : List Gate) (h : ∃ g ∈ gs, cost g=0) : total gs < gs.length := by
    induction gs with
    | nil => simp at h
    | cons g gs ih =>
      rcases h with ⟨a,ha,op⟩
      simp only [List.mem_cons] at ha
      simp only [total,List.map_cons,List.sum_cons,List.length_cons]
      rcases ha with rfl|hmem
      · have le := count gs
        change (gs.map cost).sum ≤ gs.length at le
        omega
      · have lt := ih ⟨_,hmem,op⟩
        change (gs.map cost).sum < gs.length at lt
        have co : cost g ≤ 1 := by dsimp [cost];split <;> decide
        omega
  have gateAgree (g : Gate) (w v : List Bool) (h : ∀ i ∈ pins g, w.getD i false = v.getD i false) :
      g.op.eval (g.inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
    by_cases hn : g.op=.not
    · rw [hn]
      cases e : g.inputs with
      | nil => rfl
      | cons i l =>
        have e' := h i (by simp [pins,hn,e])
        exact congrArg Bool.not e'
    · congr 1
      apply List.map_congr_left
      simpa [pins,hn] using h
  have front (gs : List Gate) (leg : ∀ g ∈ gs, g.inputs.length ≤ 2) (n : ℕ) (W : Finset ℕ) :
      ∃ S : Finset ℕ, S.card ≤ W.card + total gs ∧ ∀ a b : List Bool, a.length=n → b.length=n →
        agrees S a b → agrees W (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing n W with
    | nil => exact ⟨W,by simp [total],fun _ _ _ _ h => h⟩
    | cons g gs ih =>
      obtain ⟨T,size,work⟩ := ih (fun q m => leg q (List.mem_cons_of_mem _ m)) (n+1) W
      let P := (pins g).toFinset
      let S := if n ∈ T then T.erase n ∪ P else T
      have cap : P.card ≤ 1 + cost g := by
        have le : (pins g).length ≤ 2 := by
          by_cases e : g.op=.not
          · simp [pins,e]
          · simpa [pins,e] using leg g List.mem_cons_self
        have bound := (List.toFinset_card_le (pins g)).trans le
        dsimp [P,cost];split <;> omega
      have card : S.card ≤ T.card + cost g := by
        by_cases e : n ∈ T
        · have u := Finset.card_union_le (T.erase n) P
          rw [Finset.card_erase_of_mem e] at u
          have pos := Finset.card_pos.mpr ⟨n,e⟩
          simpa only [S,if_pos e] using (show (T.erase n ∪ P).card ≤ T.card + cost g by omega)
        · simp [S,e]
      refine ⟨S,?_,?_⟩
      · have tot : total (g::gs) = cost g + total gs := by simp [total]
        rw [tot];omega
      · intro a b la lb h
        apply work _ _ (by simp [step,la]) (by simp [step,lb])
        intro i hi
        by_cases eq : i=n
        · subst i
          have pinsEq : ∀ j ∈ pins g, a.getD j false=b.getD j false := by
            intro j mem
            exact h j (by simp [S,hi,P,mem])
          simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,la,lb] using gateAgree g a b pinsEq
        · have old : i ∈ S := by by_cases e : n ∈ T <;> simp [S,e,hi,eq]
          by_cases lt : i<n
          · exact (List.getD_append _ _ _ _ (by omega : i<a.length)).trans ((h i old).trans (List.getD_append _ _ _ _ (by omega : i<b.length)).symm)
          · rw [List.getD_eq_default _ _ (by simp [step,la];omega),List.getD_eq_default _ _ (by simp [step,lb];omega)]
  let P : Circuit := ⟨C.gates.take 9,0⟩
  let D : Circuit := ⟨C.gates.drop 9,C.output⟩
  have hp : FanInTwo P := fun g m => legal g (List.mem_of_mem_take m)
  have hd : FanInTwo D := fun g m => legal g (List.mem_of_mem_drop m)
  have ps : P.size ≤ 9 := by change (C.gates.take 9).length≤9;simp
  have ds : D.size ≤ 9 := by change C.gates.length ≤ 18 at budget;change (C.gates.drop 9).length≤9;rw [List.length_drop];omega
  obtain ⟨T,tc,hT⟩ := front D.gates (fun g m => (hd g m).2) (11+P.size) {D.output}
  let S := T.filter (· < 11+P.size)
  have sc : S.card ≤ 1+total D.gates := by have := Finset.card_filter_le T (· < 11+P.size);simpa using le_trans this tc
  have ran : ∀ i ∈ S, i<11+P.size := fun i h => (Finset.mem_filter.mp h).2
  let base (x : Fin 10 → Bool) := List.ofFn x ++ [!x 0]
  let masked (x : Fin 10 → Bool) := List.ofFn (fun i : Fin (11+P.size) =>
    if i.val ∈ S then (P.wires (base x)).getD i.val false else false)
  have runLen (gs : List Gate) (a : List Bool) : (gs.foldl step a).length=a.length+gs.length := by
    induction gs generalizing a with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih];simp [step];omega
  have eq (x : Fin 10 → Bool) : C.eval (base x) = D.eval (masked x) := by
    let w := P.wires (base x)
    have lw : w.length=11+P.size := by
      change (P.gates.foldl step (base x)).length=_
      rw [runLen];change (base x).length + P.gates.length=11+P.gates.length;simp [base]
    have lm : (masked x).length=11+P.size := by simp [masked]
    have a := hT w (masked x) lw lm (by
      intro i mem
      by_cases small : i<11+P.size
      · have hs : i ∈ S := Finset.mem_filter.mpr ⟨mem,small⟩
        simp [masked,small,hs,List.getD_eq_getElem?_getD,w]
      · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)])
    have same := a D.output (Finset.mem_singleton_self _)
    change (C.gates.foldl step (base x)).getD C.output false = _
    conv_lhs => rw [← List.take_append_drop 9 C.gates,List.foldl_append]
    exact same
  by_cases small : S.card ≤ 9
  · by_cases deep : ∃ i ∈ S, ¬∃ A : Circuit, FanInTwo A ∧ A.size≤1 ∧
        ∀ x : Fin 10 → Bool, A.eval (base x)=(P.wires (base x)).getD i false
    · obtain ⟨x,h⟩ := narrow P D S hp ps hd ds small ran deep
      exact ⟨x,(eq x).symm ▸ h⟩
    · push Not at deep
      obtain ⟨x,y,agree,neq⟩ := shallow P S small deep
      have same : masked x=masked y := by
        apply congrArg List.ofFn
        funext i
        by_cases h : i.val ∈ S
        · simpa [h,base] using agree i.val h
        · simp [h]
      by_contra! all
      apply neq
      exact (all x).symm.trans ((eq x).trans ((congrArg D.eval same).trans ((eq y).symm.trans (all y))))
  · have n10 : S.card=10 := by have := count D.gates;change D.gates.length≤9 at ds;omega
    have full : D.size=9 := by have := count D.gates;change D.gates.length≤9 at ds;change D.gates.length=9;omega
    have two (g) (m : g ∈ D.gates) : 2 ≤ (pins g).toFinset.card := by
      by_contra! missing
      have c0 : cost g=0 := by simp [cost,show ¬2≤(pins g).toFinset.card by omega]
      have lt := strict D.gates ⟨g,m,c0⟩
      change D.gates.length≤9 at ds;omega
    have noNot (g) (m : g ∈ D.gates) : g.op ≠ .not := by
      intro e
      have h := two g m
      have le := List.toFinset_card_le (pins g)
      have sz : (pins g).length≤1 := by simp [pins,e]
      omega
    have mono : Monotone2 D := by
      intro g m
      have hn := noNot g m
      have := (hd g m).1
      exact ⟨by simpa [hn] using this,(hd g m).2⟩
    have distinct (g) (m : g ∈ D.gates) : g.inputs.toFinset.card=2 := by
      apply Nat.le_antisymm ((List.toFinset_card_le _).trans (hd g m).2)
      simpa [pins,noNot g m] using two g m
    obtain ⟨x,h⟩ := wide P D S hp ps mono full distinct n10 ran
    exact ⟨x,(eq x).symm ▸ h⟩
