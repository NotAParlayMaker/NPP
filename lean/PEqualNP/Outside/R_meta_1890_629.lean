import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On inputs where the supplied AND is false, each shallow signal is a constant,
-- a literal or a two-literal gate. The first child rules out any decoder of nine.
-- The second keeps only wires the final eight gates can actually use.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1890_629
  (shallow : let raw := fun x : Fin 10 → Bool => List.ofFn x ++ [false]
    let off := fun x : Fin 10 → Bool => (x 0 && x 2)=false
    let target := fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e=>x e.1 && x e.2)
    ∀ (P : Circuit) (S : Finset ℕ), S.card≤9 →
      (∀ i∈S, ∃ A : Circuit, FanInTwo A ∧ A.size≤1 ∧ ∀ x, off x →
        A.eval (raw x)=(P.wires (raw x)).getD i false) →
      ∃ x y, off x ∧ off y ∧
        (∀ i∈S, (P.wires (raw x)).getD i false=(P.wires (raw y)).getD i false) ∧ target x≠target y)
  (residual : let raw := fun x : Fin 10 → Bool => List.ofFn x ++ [false]
    let off := fun x : Fin 10 → Bool => (x 0 && x 2)=false
    let target := fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e=>x e.1 && x e.2)
    ∀ (P D : Circuit) (S : Finset ℕ), FanInTwo P → P.size≤10 → FanInTwo D → D.size≤8 →
      S.card≤D.size+1 → (S.card=D.size+1 → Monotone2 D ∧ ∀ g∈D.gates, g.inputs.toFinset.card=2) →
      (∃ i∈S, ¬∃ A : Circuit, FanInTwo A ∧ A.size≤1 ∧ ∀ x, off x →
        A.eval (raw x)=(P.wires (raw x)).getD i false) →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn (fun i : Fin (11+P.size) =>
        if i.val∈S then (P.wires (List.ofFn x ++ [x 0 && x 2])).getD i.val false else false))≠target x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  classical
  have transport :
      ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin n → Bool) (tail : List Bool),
            D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
    intro n C p hfan
    let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
    have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < n
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x tail
    apply run C.gates _ _ (by simp) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
      have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
          List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left hi
    · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
      simp
  intro old p oldLegal oldSize
  obtain ⟨C,legal,sameSize,changes⟩ := transport 10 old p oldLegal
  have budget : C.size≤18 := sameSize.le.trans oldSize
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
  let P : Circuit := ⟨C.gates.take 10,0⟩
  let D : Circuit := ⟨C.gates.drop 10,C.output⟩
  have hp : FanInTwo P := fun g m => legal g (List.mem_of_mem_take m)
  have hd : FanInTwo D := fun g m => legal g (List.mem_of_mem_drop m)
  have ps : P.size ≤ 10 := by change (C.gates.take 10).length≤10;simp
  have ds : D.size ≤ 8 := by change C.gates.length ≤ 18 at budget;change (C.gates.drop 10).length≤8;rw [List.length_drop];omega
  obtain ⟨T,tc,hT⟩ := front D.gates (fun g m => (hd g m).2) (11+P.size) {D.output}
  let S := T.filter (· < 11+P.size)
  have sc : S.card ≤ 1+total D.gates := by have := Finset.card_filter_le T (· < 11+P.size);simpa using le_trans this tc
  have ran : ∀ i ∈ S, i<11+P.size := fun i h => (Finset.mem_filter.mp h).2
  let base (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
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
    conv_lhs => rw [← List.take_append_drop 10 C.gates,List.foldl_append]
    exact same
  let raw (x : Fin 10 → Bool) := List.ofFn x ++ [false]
  let off (x : Fin 10 → Bool) := (x 0 && x 2)=false
  let target (x : Fin 10 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e=>x e.1 && x e.2)
  have goalEq (x : Fin 10 → Bool) : target x = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x := by
    have test : ∀ y : Fin 10 → Bool, (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e=>y e.1 && y e.2)) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) y := by decide +kernel
    exact test x
  have bound : S.card ≤ D.size+1 := by have := count D.gates;change S.card≤D.gates.length+1;omega
  have saturated (h : S.card=D.size+1) : Monotone2 D ∧ ∀ g∈D.gates, g.inputs.toFinset.card=2 := by
    have len : S.card=D.gates.length+1 := h
    have two (g) (m : g ∈ D.gates) : 2 ≤ (pins g).toFinset.card := by
      by_contra! missing
      have c0 : cost g=0 := by simp [cost,show ¬2≤(pins g).toFinset.card by omega]
      have lt := strict D.gates ⟨g,m,c0⟩
      omega
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
    exact ⟨mono,distinct⟩
  by_cases deep : ∃ i∈S, ¬∃ A : Circuit, FanInTwo A ∧ A.size≤1 ∧ ∀ x, off x →
    A.eval (raw x)=(P.wires (raw x)).getD i false
  · obtain ⟨x,h⟩ := residual P D S hp ps hd ds bound saturated deep
    exact ⟨x,by rw [←changes x [x 0 && x 2],←goalEq x];exact (eq x).symm ▸ h⟩
  · push Not at deep
    obtain ⟨x,y,ax,ay,agree,neq⟩ := shallow P S (by omega) deep
    have same : masked x=masked y := by
      apply congrArg List.ofFn
      funext i
      by_cases h : i.val∈S
      · simpa [masked,h,base,raw,ax,ay] using agree i.val h
      · simp [h]
    by_contra! all
    apply neq
    have ex := all x
    have ey := all y
    rw [←changes x [x 0 && x 2]] at ex
    rw [←changes y [y 0 && y 2]] at ey
    exact (goalEq x).trans (ex.symm.trans ((eq x).trans ((congrArg D.eval same).trans ((eq y).symm.trans (ey.trans (goalEq y).symm)))))
