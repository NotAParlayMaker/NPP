import Mathlib
import PEqualNP.Defs

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity BigOperators

-- Cut the first AND that is true on the designated independent input.
-- Redirecting the cut to either operand can only add accepted inputs.
-- Both strict redirects have separate negative witnesses. Forcing the cut off loses an edge.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_1894_746
    (smaller :
      let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
       (v.val+21-u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let F (x : Fin 42 → Bool) := ∃ u v, E u v ∧ x u = true ∧ x v = true
      ∀ D : Circuit, Monotone2 D → D.size ≤ 123 → ∀ c : Bool,
        (∀ t : DMFormula 42,
          DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
            (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) t →
          (∀ x, t.eval x = D.eval (c :: List.ofFn x)) → 126 ≤ t.leaves) →
        ¬ (∀ x, D.eval (c :: List.ofFn x) = true ↔ F x))
    (critical :
      let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
       (v.val+21-u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let F (x : Fin 42 → Bool) := ∃ u v, E u v ∧ x u = true ∧ x v = true
      ∀ D : Circuit, Monotone2 D → D.size ≤ 123 → ∀ a b : ℕ,
        let w (x : Fin 42 → Bool) (i : ℕ) := (D.wires (false :: List.ofFn x)).getD i false
        let z (x : Fin 42 → Bool) := w x a && w x b
        let r (s : Bool) (x : Fin 42 → Bool) := D.eval (s :: List.ofFn x)
        (∃ k ≤ D.size, a < 43+k ∧ b < 43+k ∧ ∀ g ∈ D.gates.take k, 0 ∉ g.inputs) →
        (∀ x, r (z x) x = true ↔ F x) →
        (∃ u v, E u v ∧ r false (fun i => decide (i = u ∨ i = v)) = false) →
        (∀ s : Bool, ∃ x, ¬ F x ∧ w x a = s ∧ w x b = !s ∧ r true x = true) →
        (∃ S : Finset (Fin 42), S.card ≤ 2 ∧
          (∀ v ∈ S, v.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ)) ∧
          z (fun i => decide (i ∈ S)) = true) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by

  -- On the subcube below the chosen input, every wire before the first active AND is an OR of literal inputs.
  have firstHotAndProfile (n : ℕ) (C : Circuit) (W : Finset (Fin n))
      (mon : Monotone2 C)
      (hot : ∃ k g, C.gates[k]? = some g ∧ g.op = .and ∧
        (C.wires (List.ofFn fun v : Fin n => decide (v ∈ W))).getD (n+k) false = true) :
      ∃ (k : ℕ) (g : Gate) (masks : List (Finset (Fin n))),
        C.gates[k]? = some g ∧ g.op = .and ∧
        masks.length = g.inputs.length ∧ masks.length ≤ 2 ∧
        (∀ M ∈ masks, M ⊆ W ∧ M.Nonempty) ∧
        (∀ i < k, ∀ h, C.gates[i]? = some h → h.op = .and →
          (C.wires (List.ofFn fun v : Fin n => decide (v ∈ W))).getD (n+i) false = false) ∧
        (∀ Z ⊆ W, (C.wires (List.ofFn fun v : Fin n => decide (v ∈ Z))).getD (n+k) false =
          masks.all (fun M => decide ((M ∩ Z).Nonempty))) ∧
        ∃ Z ⊆ W, Z.card ≤ 2 ∧
          (C.wires (List.ofFn fun v : Fin n => decide (v ∈ Z))).getD (n+k) false = true := by
    clear smaller critical
    classical
    let input (Z : Finset (Fin n)) := List.ofFn fun v : Fin n => decide (v ∈ Z)
    let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
    let pre (k : ℕ) (Z : Finset (Fin n)) := (C.gates.take k).foldl step (input Z)
    let val (k : ℕ) (Z : Finset (Fin n)) := (C.wires (input Z)).getD (n+k) false
    let hit (M Z : Finset (Fin n)) := decide ((M ∩ Z).Nonempty)
    have extension (gs : List Gate) (xs : List Bool) : ∃ ys, gs.foldl step xs = xs ++ ys := by
      induction gs generalizing xs with
      | nil => exact ⟨[],by simp⟩
      | cons h ls ih =>
        obtain ⟨ys,eq⟩ := ih (step xs h)
        exact ⟨[_] ++ ys,by simpa [step,List.foldl_cons,List.append_assoc] using eq⟩
    have length (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
      induction gs generalizing xs with
      | nil => simp
      | cons h ls ih => rw [List.foldl_cons,ih]; simp [step]; omega
    have advance (j : ℕ) (hj : j < C.gates.length) (Z : Finset (Fin n)) :
        pre (j+1) Z = step (pre j Z) C.gates[j] := by
      unfold pre
      rw [List.take_succ_eq_append_getElem hj,List.foldl_append]
      rfl
    have read (j : ℕ) (hj : j < C.gates.length) (Z : Finset (Fin n)) :
        val j Z = C.gates[j].op.eval (C.gates[j].inputs.map fun i => (pre j Z).getD i false) := by
      have len : (pre j Z).length = n+j := by
        unfold pre
        rw [length,List.length_take_of_le (Nat.le_of_lt hj)]
        simp [input]
      obtain ⟨ys,heq⟩ := extension (C.gates.drop (j+1)) (pre (j+1) Z)
      have full : C.wires (input Z) = pre (j+1) Z ++ ys := by
        change C.gates.foldl step (input Z) = _
        rw [← List.take_append_drop (j+1) C.gates,List.foldl_append]
        exact heq
      change (C.wires (input Z)).getD (n+j) false = _
      rw [full,advance j hj]
      change ((pre j Z ++ [_]) ++ ys).getD (n+j) false = _
      rw [List.getD_append _ _ _ _ (by simp [len]),List.getD_append_right _ _ _ _ (le_of_eq len)]
      simp [len]
    let Fires (i : ℕ) := ∃ g, C.gates[i]? = some g ∧ g.op = .and ∧ val i W = true
    have hex : ∃ i, Fires i := hot
    let k := Nat.find hex
    obtain ⟨g,get,kind,fire⟩ := (Nat.find_spec hex : Fires k)
    have klt : k < C.gates.length := by
      by_contra! h
      rw [List.getElem?_eq_none h] at get
      cases get
    have kget : C.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem klt).symm.trans get)
    have cold (i : ℕ) (hi : i < k) (q : Gate) (getq : C.gates[i]? = some q) (op : q.op = .and) :
        val i W = false := by
      apply Bool.eq_false_iff.mpr
      intro hotq
      exact Nat.find_min hex hi ⟨q,getq,op,hotq⟩
    have signal (ms : List (Finset (Fin n))) (Z : Finset (Fin n)) (i : ℕ) :
        (ms.map (fun M => hit M Z)).getD i false = hit (ms.getD i ∅) Z := by
      induction ms generalizing i with
      | nil => cases i <;> simp [hit]
      | cons a ms ih => cases i with
        | zero => rfl
        | succ i => exact ih i
    have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have table (i : ℕ) (hi : i ≤ k) : ∃ ms : List (Finset (Fin n)),
        (∀ M ∈ ms, M ⊆ W) ∧ ∀ Z ⊆ W, pre i Z = ms.map (fun M => hit M Z) := by
      induction i with
      | zero =>
        let start := List.ofFn fun u : Fin n => ({u} : Finset (Fin n)) ∩ W
        refine ⟨start,?_,?_⟩
        · intro M hm
          obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hm
          exact Finset.inter_subset_right
        · intro Z hz
          change input Z = start.map _
          unfold input start
          rw [List.map_ofFn]
          apply congrArg List.ofFn
          funext u
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h
            have hu : u ∈ Z := of_decide_eq_true h
            exact decide_eq_true ⟨u,by simp [hu,hz hu]⟩
          · intro h
            obtain ⟨v,hv⟩ := of_decide_eq_true h
            obtain ⟨mem,mz⟩ := Finset.mem_inter.mp hv
            have vu : v = u := Finset.mem_singleton.mp (Finset.mem_inter.mp mem).1
            exact decide_eq_true (vu ▸ mz)
      | succ i ih =>
        have ik : i < k := by omega
        have ilt : i < C.gates.length := by omega
        let q := C.gates[i]
        have qget : C.gates[i]? = some q := List.getElem?_eq_getElem ilt
        obtain ⟨ms,sub,old⟩ := ih (Nat.le_of_lt ik)
        let pins := q.inputs.map fun w => ms.getD w ∅
        have measured (Z : Finset (Fin n)) (hz : Z ⊆ W) :
            q.inputs.map (fun w => (pre i Z).getD w false) = pins.map (fun M => hit M Z) := by
          rw [old Z hz]
          simp only [pins,List.map_map]
          apply List.map_congr_left
          intro w _
          exact signal ms Z w
        have pinSub (M : Finset (Fin n)) (hm : M ∈ pins) : M ⊆ W := by
          obtain ⟨w,_,eq⟩ := List.mem_map.mp hm
          subst M
          by_cases h : w < ms.length
          · rw [List.getD_eq_getElem _ _ h]
            exact sub _ (List.getElem_mem h)
          · rw [List.getD_eq_default _ _ (by omega)]
            exact Finset.empty_subset _
        have withMask (M : Finset (Fin n)) (msub : M ⊆ W)
            (agrees : ∀ Z ⊆ W, q.op.eval (pins.map (fun p => hit p Z)) = hit M Z) :
            ∃ ms' : List (Finset (Fin n)), (∀ A ∈ ms', A ⊆ W) ∧
              ∀ Z ⊆ W, pre (i+1) Z = ms'.map (fun p => hit p Z) := by
          refine ⟨ms ++ [M],?_,?_⟩
          · intro A hA
            rcases List.mem_append.mp hA with hA | hA
            · exact sub _ hA
            · have eq : A = M := by simpa using hA
              exact eq ▸ msub
          · intro Z hz
            rw [advance i ilt]
            change pre i Z ++ [q.op.eval (q.inputs.map _)] = _
            rw [measured Z hz,agrees Z hz,old Z hz,List.map_append]
            rfl
        have kinds := (mon q (List.getElem_mem ilt)).1
        change q.op = .and ∨ q.op = .or at kinds
        rcases kinds with isAnd | isOr
        · have off := cold i ik q qget isAnd
          rw [read i ilt] at off
          change q.op.eval (q.inputs.map _) = false at off
          rw [measured W (Finset.Subset.refl W),isAnd,andEval] at off
          apply withMask ∅ (Finset.empty_subset _)
          intro Z hz
          rw [isAnd,andEval]
          have zero : hit ∅ Z = false := by simp [hit]
          rw [zero]
          apply Bool.eq_false_iff.mpr
          intro h
          have propagated : (pins.map (fun M => hit M W)).all id = true := by
            simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at h ⊢
            intro M hM
            obtain ⟨v,hv⟩ := of_decide_eq_true (h M hM)
            exact decide_eq_true ⟨v,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,hz (Finset.mem_inter.mp hv).2⟩⟩
          rw [off] at propagated
          exact Bool.noConfusion propagated
        · let U := pins.toFinset.biUnion id
          apply withMask U
          · intro v hv
            obtain ⟨M,hm,hv⟩ := Finset.mem_biUnion.mp hv
            exact pinSub M (List.mem_toFinset.mp hm) hv
          · intro Z hz
            rw [isOr,orEval]
            apply Bool.eq_iff_iff.mpr
            rw [List.any_map,List.any_eq_true]
            constructor
            · rintro ⟨M,hM,h⟩
              obtain ⟨v,hv⟩ := of_decide_eq_true h
              exact decide_eq_true ⟨v,Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
                ⟨M,List.mem_toFinset.mpr hM,(Finset.mem_inter.mp hv).1⟩,(Finset.mem_inter.mp hv).2⟩⟩
            · intro h
              obtain ⟨v,hv⟩ := of_decide_eq_true h
              obtain ⟨M,hM,hm⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hv).1
              exact ⟨M,List.mem_toFinset.mp hM,decide_eq_true ⟨v,Finset.mem_inter.mpr ⟨hm,(Finset.mem_inter.mp hv).2⟩⟩⟩
    obtain ⟨ms,sub,old⟩ := table k (le_refl _)
    let pins := g.inputs.map fun w => ms.getD w ∅
    have profile (Z : Finset (Fin n)) (hz : Z ⊆ W) :
        val k Z = pins.all (fun M => hit M Z) := by
      rw [read k klt,kget,kind,andEval,old Z hz]
      simp only [pins,List.all_map,Function.comp_def,id_eq]
      apply List.all_congr rfl
      intro w
      exact signal ms Z w
    have len : pins.length = g.inputs.length := by simp [pins]
    have budget : pins.length ≤ 2 := len.trans_le (mon g (kget ▸ List.getElem_mem klt)).2
    have ne (M : Finset (Fin n)) (hm : M ∈ pins) : M.Nonempty := by
      have yes := (profile W (Finset.Subset.refl W)).symm.trans fire
      obtain ⟨v,hv⟩ := of_decide_eq_true ((List.all_eq_true.mp yes) M hm)
      exact ⟨v,(Finset.mem_inter.mp hv).1⟩
    have inside (M : Finset (Fin n)) (hm : M ∈ pins) : M ⊆ W := by
      obtain ⟨w,_,eq⟩ := List.mem_map.mp hm
      subst M
      by_cases h : w < ms.length
      · rw [List.getD_eq_getElem _ _ h]
        exact sub _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Finset.empty_subset _
    refine ⟨k,g,pins,get,kind,len,budget,fun M hm => ⟨inside M hm,ne M hm⟩,cold,profile,?_⟩
    have choosePins (ls : List (Finset (Fin n))) (ok : ∀ M ∈ ls, M ⊆ W ∧ M.Nonempty) :
        ∃ Z ⊆ W, Z.card ≤ ls.length ∧ ls.all (fun M => hit M Z) = true := by
      induction ls with
      | nil => exact ⟨∅,Finset.empty_subset _,by simp,rfl⟩
      | cons M ls ih =>
        obtain ⟨insideM,v,hv⟩ := ok M (by simp)
        obtain ⟨Z,hz,card,on⟩ := ih (fun A h => ok A (by simp [h]))
        refine ⟨insert v Z,Finset.insert_subset (insideM hv) hz,?_,?_⟩
        · have bound := Finset.card_insert_le v Z
          simp only [List.length_cons]
          omega
        · rw [List.all_eq_true] at on ⊢
          intro A hA
          rcases List.mem_cons.mp hA with rfl | h
          · exact decide_eq_true ⟨v,Finset.mem_inter.mpr ⟨hv,Finset.mem_insert_self _ _⟩⟩
          · obtain ⟨w,hw⟩ := of_decide_eq_true (on _ h)
            exact decide_eq_true ⟨w,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
              Finset.mem_insert_of_mem (Finset.mem_inter.mp hw).2⟩⟩
    obtain ⟨Z,hz,bound,on⟩ := choosePins pins (fun M hm => ⟨inside M hm,ne M hm⟩)
    exact ⟨Z,hz,bound.trans budget,(profile Z hz).trans on⟩

  -- A rectangle and rank count gives one leaf per incidence plus a vertex cover of size 21. The argument adapts R_meta_2638_617.
  have graphFormulaBound1894 (t : DMFormula 42)
      (pos : DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
        (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) t)
      (computes : ∀ x, t.eval x = true ↔ ∃ (u v : Fin 42),
        (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
        x u = true ∧ x v = true) : 126 ≤ t.leaves := by
    clear smaller critical firstHotAndProfile
    have formulaRect (n : ℕ) (t : DMFormula n)
        (positive : DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) t) :
        ∃ (X Y : Fin t.leaves → (Fin n → Bool) → Prop) (lab : Fin t.leaves → Fin n),
          ∀ x y : Fin n → Bool, t.eval x = true → t.eval y = false →
          (∃! i, X i x ∧ Y i y) ∧
          ∀ i, X i x → Y i y → x (lab i) = true ∧ y (lab i) = false := by
      classical
      let Pos : DMFormula n → Prop := DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
      let Cert (t : DMFormula n) : Prop :=
        ∃ (X Y : Fin t.leaves → (Fin n → Bool) → Prop) (lab : Fin t.leaves → Fin n),
          ∀ x y : Fin n → Bool, t.eval x = true → t.eval y = false →
          (∃! i, X i x ∧ Y i y) ∧
          ∀ i, X i x → Y i y → x (lab i) = true ∧ y (lab i) = false
      have combine (p q t : DMFormula n) (e : Fin p.leaves ⊕ Fin q.leaves ≃ Fin t.leaves)
          (lx ly rx ry : (Fin n → Bool) → Prop)
          (route : ∀ x y, t.eval x = true → t.eval y = false →
            ((lx x ∧ ly y) ∧ ¬(rx x ∧ ry y) ∧ p.eval x = true ∧ p.eval y = false) ∨
            ((rx x ∧ ry y) ∧ ¬(lx x ∧ ly y) ∧ q.eval x = true ∧ q.eval y = false))
          (cp : Cert p) (cq : Cert q) : Cert t := by
        obtain ⟨xp, yp, lp, hp⟩ := cp
        obtain ⟨xq, yq, lq, hq⟩ := cq
        let X : Fin p.leaves ⊕ Fin q.leaves → (Fin n → Bool) → Prop :=
          Sum.elim (fun i x => lx x ∧ xp i x) (fun i x => rx x ∧ xq i x)
        let Y : Fin p.leaves ⊕ Fin q.leaves → (Fin n → Bool) → Prop :=
          Sum.elim (fun i y => ly y ∧ yp i y) (fun i y => ry y ∧ yq i y)
        let L : Fin p.leaves ⊕ Fin q.leaves → Fin n := Sum.elim lp lq
        refine ⟨fun i => X (e.symm i), fun i => Y (e.symm i), fun i => L (e.symm i), ?_⟩
        intro x y hx hy
        have localResult :
            (∃! i, X i x ∧ Y i y) ∧
            ∀ i, X i x → Y i y → x (L i) = true ∧ y (L i) = false := by
          rcases route x y hx hy with leftRoute | rightRoute
          · obtain ⟨⟨dx, dy⟩, excl, ax, ay⟩ := leftRoute
            obtain ⟨⟨i, ⟨ix, iy⟩, only⟩, label⟩ := hp x y ax ay
            constructor
            · refine ⟨.inl i, ⟨⟨dx, ix⟩, ⟨dy, iy⟩⟩, ?_⟩
              rintro (j | j) ⟨xj, yj⟩
              · exact congrArg Sum.inl (only j ⟨xj.2, yj.2⟩)
              · exact (excl ⟨xj.1, yj.1⟩).elim
            · rintro (j | j) xj yj
              · exact label j xj.2 yj.2
              · exact (excl ⟨xj.1, yj.1⟩).elim
          · obtain ⟨⟨dx, dy⟩, excl, ax, ay⟩ := rightRoute
            obtain ⟨⟨i, ⟨ix, iy⟩, only⟩, label⟩ := hq x y ax ay
            constructor
            · refine ⟨.inr i, ⟨⟨dx, ix⟩, ⟨dy, iy⟩⟩, ?_⟩
              rintro (j | j) ⟨xj, yj⟩
              · exact (excl ⟨xj.1, yj.1⟩).elim
              · exact congrArg Sum.inr (only j ⟨xj.2, yj.2⟩)
            · rintro (j | j) xj yj
              · exact (excl ⟨xj.1, yj.1⟩).elim
              · exact label j xj.2 yj.2
        obtain ⟨⟨i, hi, unq⟩, labels⟩ := localResult
        constructor
        · refine ⟨e i, by simpa using hi, ?_⟩
          intro j hj
          exact e.symm_apply_eq.mp (unq (e.symm j) hj)
        · exact fun j => labels (e.symm j)
      have go (t : DMFormula n) : Pos t → Cert t := by
        induction t with
        | lit i b =>
          intro hb
          change b = true at hb
          subst b
          refine ⟨fun _ x => x i = true, fun _ y => y i = false, fun _ => i, ?_⟩
          intro x y hx hy
          change x i = true at hx
          change y i = false at hy
          refine ⟨⟨⟨0, Nat.zero_lt_one⟩, ⟨hx,hy⟩, ?_⟩, ?_⟩
          · intro j _
            apply Fin.ext
            change j.val = 0
            have h : j.val < 1 := j.isLt
            omega
          · exact fun _ a b => ⟨a,b⟩
        | and p q ip iq =>
          intro h
          change Pos p ∧ Pos q at h
          apply combine p q (.and p q) finSumFinEquiv (fun _ => True) (fun y => p.eval y = false)
            (fun _ => True) (fun y => p.eval y = true) _ (ip h.1) (iq h.2)
          intro x y hx hy
          change (p.eval x && q.eval x) = true at hx
          change (p.eval y && q.eval y) = false at hy
          cases ax : p.eval x <;> cases bx : q.eval x <;> cases ay : p.eval y <;> cases byq : q.eval y <;>
            simp [ax,bx,ay,byq] at hx hy ⊢
        | or p q ip iq =>
          intro h
          change Pos p ∧ Pos q at h
          apply combine p q (.or p q) finSumFinEquiv (fun x => p.eval x = true) (fun _ => True)
            (fun x => p.eval x = false) (fun _ => True) _ (ip h.1) (iq h.2)
          intro x y hx hy
          change (p.eval x || q.eval x) = true at hx
          change (p.eval y || q.eval y) = false at hy
          cases ax : p.eval x <;> cases bx : q.eval x <;> cases ay : p.eval y <;> cases byq : q.eval y <;>
            simp [ax,bx,ay,byq] at hx hy ⊢
      exact go t positive
    have tableBound (n m : ℕ) (H : SimpleGraph (Fin n)) (X Y : Fin m → Fin n → Fin n → Prop)
        (lab : Fin m → Fin n) (table : ∀ a b v w, H.Adj a b → (v = w ∨ H.Adj v w) →
            (∃! i, X i a b ∧ Y i v w) ∧
            (∀ i, X i a b → Y i v w → (lab i = a ∨ lab i = b) ∧
              ¬ ((H.Adj v (lab i) ∨ H.Adj w (lab i)) ∧ lab i ≠ v ∧ lab i ≠ w))) :
          ∃ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧
            H.edgeSet.ncard + T.card ≤ m := by
      classical
      classical
      let E := H.edgeSet
      let V := Fin n
      let p (e : E) : V := e.1.out.1
      let q (e : E) : V := e.1.out.2
      have ends (e : E) : s(p e,q e) = e.1 := Sym2.mk_fst_out_snd_out _
      have edge (e : E) : H.Adj (p e) (q e) := H.mem_edgeSet.mp (by rw [ends]; exact e.2)
      let pick (e : E) (a b : V) (h : a = b ∨ H.Adj a b) : Fin m :=
        (table _ _ a b (edge e) h).1.exists.choose
      have chosen (e : E) (a b : V) (h : a = b ∨ H.Adj a b) :
          X (pick e a b h) (p e) (q e) ∧ Y (pick e a b h) a b :=
        (table _ _ a b (edge e) h).1.exists.choose_spec
      let cell (e : E) (a b : V) (h : a = b ∨ H.Adj a b) := lab (pick e a b h)
      have cellProp (e : E) (a b : V) (h : a = b ∨ H.Adj a b) :
          cell e a b h ∈ e.1 ∧ ¬ ((H.Adj a (cell e a b h) ∨ H.Adj b (cell e a b h)) ∧
            cell e a b h ≠ a ∧ cell e a b h ≠ b) := by
        have rule := (table _ _ a b (edge e) h).2 _ (chosen e a b h).1 (chosen e a b h).2
        exact ⟨by rw [← ends e]; exact Sym2.mem_iff.mpr rule.1, rule.2⟩
      have near (e : E) (u v : V) (hu : u ∈ e.1) (hv : v ∈ e.1) (hne : u ≠ v) : H.Adj u v :=
        H.mem_edgeSet.mp (by rw [← (Sym2.mem_and_mem_iff hne).mp ⟨hu,hv⟩]; exact e.2)
      have single (e : E) (v : V) (hv : v ∈ e.1) : cell e v v (.inl rfl) = v := by
        obtain ⟨hr,hn⟩ := cellProp e v v (.inl rfl)
        by_contra ne
        exact hn ⟨Or.inl (near e v _ hv hr (Ne.symm ne)),ne,ne⟩
      have across (e d : E) (v : V) (hv : v ∈ e.1) (hd : v ∈ d.1) (diff : e ≠ d) :
          cell e (p d) (q d) (.inr (edge d)) = v := by
        let u := cell e (p d) (q d) (.inr (edge d))
        obtain ⟨hu,hn⟩ := cellProp e (p d) (q d) (.inr (edge d))
        change u ∈ e.1 at hu
        change u = v
        by_contra ne
        have ud : u ∉ d.1 := fun hud => diff (Subtype.ext
          (((Sym2.mem_and_mem_iff ne).mp ⟨hu,hv⟩).trans ((Sym2.mem_and_mem_iff ne).mp ⟨hud,hd⟩).symm))
        rw [← ends d, Sym2.mem_iff] at hd ud
        have adjacent := near e v u hv hu (Ne.symm ne)
        change ¬ ((H.Adj (p d) u ∨ H.Adj (q d) u) ∧ u ≠ p d ∧ u ≠ q d) at hn
        exact hn ⟨hd.elim (fun h => Or.inl ((congrArg (fun k => H.Adj k u) h).mp adjacent))
          (fun h => Or.inr ((congrArg (fun k => H.Adj k u) h).mp adjacent)),
          fun h => ud (Or.inl h),fun h => ud (Or.inr h)⟩
      let win (e : E) := cell e (p e) (q e) (.inr (edge e))
      have winMem (e : E) : win e ∈ e.1 := (cellProp e (p e) (q e) (.inr (edge e))).1
      let lose (e : E) := Sym2.Mem.other (winMem e)
      have loseMem (e : E) : lose e ∈ e.1 := Sym2.other_mem _
      have opposite (e : E) : lose e ≠ win e := Sym2.other_ne (H.not_isDiag_of_mem_edgeSet e.2) _
      let T : Finset V := Finset.univ.image win
      have cover (a b : V) (h : H.Adj a b) : a ∈ T ∨ b ∈ T := by
        let e : E := ⟨s(a,b), H.mem_edgeSet.mpr h⟩
        have memWin : win e ∈ T := Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
        rcases Sym2.mem_iff.mp (winMem e) with eq | eq
        · exact Or.inl (eq ▸ memWin)
        · exact Or.inr (eq ▸ memWin)
      let col (v a b : V) : Fin m → ℚ := fun i => if lab i = v ∧ Y i a b then 1 else 0
      let obs (v : V) (e : E) : (Fin m → ℚ) →ₗ[ℚ] ℚ :=
        ∑ i : Fin m, if X i (p e) (q e) ∧ lab i = v then LinearMap.proj i else 0
      have measure (v u : V) (e : E) (a b : V) (h : a = b ∨ H.Adj a b) :
          obs v e (col u a b) = if cell e a b h = v ∧ v = u then 1 else 0 := by
        let j := pick e a b h
        have hj := chosen e a b h
        have formula : obs v e (col u a b) =
            ∑ i : Fin m, if X i (p e) (q e) ∧ lab i = v then col u a b i else 0 := by
          dsimp only [obs]
          rw [LinearMap.sum_apply]
          apply Finset.sum_congr rfl
          intro i _
          split <;> simp_all only [LinearMap.proj_apply, LinearMap.zero_apply]
        rw [formula, Finset.sum_eq_single j]
        · change (if X j (p e) (q e) ∧ lab j = v then col u a b j else 0) =
            if lab j = v ∧ v = u then 1 else 0
          change X j (p e) (q e) ∧ Y j a b at hj
          by_cases hv : lab j = v
          · simp [hj.1,hj.2,hv,col]
          · simp [hj.1,hv]
        · intro i _ ne
          by_cases hx : X i (p e) (q e) ∧ lab i = v
          · have hy : ¬ Y i a b := fun y => ne ((table _ _ a b (edge e) h).1.unique ⟨hx.1,y⟩ hj)
            simp [hx,col,hy]
          · simp [hx]
        · simp
      let ve (e : E) : Fin m → ℚ := col (lose e) (lose e) (lose e) - col (lose e) (p e) (q e)
      let vt (v : V) : Fin m → ℚ := col v v v
      have vtest (v u : V) (e : E) (hv : v ∈ e.1) :
          obs v e (vt u) = if v = u then 1 else 0 := by
        dsimp only [vt]
        rw [measure v u e u u (.inl rfl)]
        by_cases he : v = u
        · subst u
          simp [single e v hv]
        · simp [he]
      have etest (v : V) (e d : E) (hv : v ∈ e.1) :
          obs v e (ve d) = if v = lose d ∧ e = d then 1 else 0 := by
        dsimp only [ve]
        rw [map_sub, measure v (lose d) e (lose d) (lose d) (.inl rfl),
          measure v (lose d) e (p d) (q d) (.inr (edge d))]
        by_cases he : v = lose d
        · subst v
          by_cases ed : e = d
          · subst e
            have ne : cell d (p d) (q d) (.inr (edge d)) ≠ lose d := (opposite d).symm
            simp [single d (lose d) (loseMem d),ne]
          · simp [single e (lose d) hv,across e d (lose d) hv (loseMem d) ed,ed]
        · simp [he]
      let vec : E ⊕ T → Fin m → ℚ := Sum.elim ve (fun v => vt v.1)
      have independent : LinearIndependent ℚ vec := by
        apply Fintype.linearIndependent_iff.mpr
        intro c hc
        have line (v : V) (e : E) (hv : v ∈ e.1) :
            (if v = lose e then c (.inl e) else 0) +
              (∑ t : T, if v = t.1 then c (.inr t) else 0) = 0 := by
          have z := congrArg (obs v e) hc
          simp only [map_add, map_sum, map_smul, map_zero, Fintype.sum_sum_type, vec, Sum.elim_inl, Sum.elim_inr] at z
          simp_rw [etest v e _ hv, vtest v _ e hv] at z
          have sx : (∑ d : E, c (.inl d) • (if v = lose d ∧ e = d then (1 : ℚ) else 0)) =
              (if v = lose e then c (.inl e) else 0) := by
            rw [Finset.sum_eq_single e]
            · by_cases he : v = lose e <;> simp [he]
            · intro d _ ne
              simp [Ne.symm ne]
            · simp
          rw [sx] at z
          simpa only [smul_eq_mul, mul_ite, mul_one, mul_zero] using z
        have zeroT (t : T) : c (.inr t) = 0 := by
          obtain ⟨e, _, he⟩ := Finset.mem_image.mp t.2
          have mem : t.1 ∈ e.1 := he ▸ winMem e
          have neq : t.1 ≠ lose e := he ▸ (opposite e).symm
          have row := line t.1 e mem
          simp only [ite_eq_right neq,zero_add] at row
          rw [Finset.sum_eq_single t] at row
          · simpa using row
          · intro d _ ne
            have hn : t.1 ≠ d.1 := fun eq => ne (Subtype.ext eq.symm)
            simp [hn]
          · simp
        intro j
        cases j with
        | inl e => simpa [zeroT] using line (lose e) e (loseMem e)
        | inr t => exact zeroT t
      refine ⟨T,cover,?_⟩
      have count := independent.fintype_card_le_finrank
      have countE : Fintype.card E = H.edgeSet.ncard := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_coe_set_eq _
      simpa [Fintype.card_sum,countE,Module.finrank_pi] using count


    let offsets : List ℕ := [0,5,7,17,20]
    let dir (a b : Fin 42) := a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ offsets
    let ab (a b : Fin 42) : Bool := decide (dir a b)
    let adj (a b : Fin 42) := ab a b || ab b a
    have ir : ∀ a : Fin 42, adj a a = false := by decide
    let H : SimpleGraph (Fin 42) :=
      { Adj := fun a b => adj a b = true
        symm := ⟨by intro a b h; simpa only [adj,Bool.or_comm] using h⟩
        loopless := ⟨by intro a; rw [ir]; decide⟩ }
    letI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (adj a b = true))
    have dirs (a b : Fin 42) : H.Adj a b ↔ dir a b ∨ dir b a := by
      change (decide (dir a b) || decide (dir b a)) = true ↔ _
      simp
    let point (i : Fin 105) : Fin 42 := Fin.ofNat 42 (i.val/5)
    let line (i : Fin 105) : Fin 42 := Fin.ofNat 42 (21 + ((i.val/5 + offsets.getD (i.val % 5) 0) % 21))
    have edgeOK : ∀ i : Fin 105, dir (point i) (line i) := by decide
    have listAll : ∀ a b : Fin 42, dir a b → ∃ i : Fin 105, point i = a ∧ line i = b := by decide
    let row (a b : Fin 42) : Fin 42 → Bool := fun w => decide (w = a ∨ w = b)
    let col (a b : Fin 42) : Fin 42 → Bool := fun w =>
      decide ((adj a w = true ∨ adj b w = true) ∧ w ≠ a ∧ w ≠ b)
    -- The only negative tests used for rank are the neighbourhoods of vertices and edges.
    have safe : ∀ a b : Fin 42, a = b ∨ adj a b = true → ∀ i : Fin 105,
        ¬(col a b (point i) = true ∧ col a b (line i) = true) := by decide
    have rowOn (a b : Fin 42) (h : H.Adj a b) : t.eval (row a b) = true := by
      apply (computes _).2
      rcases (dirs a b).1 h with h | h
      · exact ⟨a,b,h,by simp [row],by simp [row]⟩
      · exact ⟨b,a,h,by simp [row],by simp [row]⟩
    have colOff (a b : Fin 42) (h : a = b ∨ H.Adj a b) : t.eval (col a b) = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨u,v,e,mu,mv⟩ := (computes _).1 on
      obtain ⟨i,pu,lv⟩ := listAll u v e
      exact safe a b h i ⟨pu ▸ mu,lv ▸ mv⟩
    obtain ⟨X,Y,lab,cert⟩ := formulaRect 42 t pos
    have part (a b v w : Fin 42) (e : H.Adj a b) (c : v = w ∨ H.Adj v w) :
        (∃! i, X i (row a b) ∧ Y i (col v w)) ∧
        ∀ i, X i (row a b) → Y i (col v w) →
          (lab i = a ∨ lab i = b) ∧ ¬ ((H.Adj v (lab i) ∨ H.Adj w (lab i)) ∧ lab i ≠ v ∧ lab i ≠ w) := by
      obtain ⟨unq,labOK⟩ := cert (row a b) (col v w) (rowOn a b e) (colOff v w c)
      refine ⟨unq,fun i hi hj => ?_⟩
      obtain ⟨ri,ci⟩ := labOK i hi hj
      exact ⟨of_decide_eq_true ri,of_decide_eq_false ci⟩
    obtain ⟨S,cover,lower⟩ := tableBound 42 t.leaves H (fun i a b => X i (row a b))
      (fun i a b => Y i (col a b)) lab part
    -- The twenty-one incidences with cyclic offset zero are a matching.
    let p (i : Fin 21) : Fin 42 := Fin.ofNat 42 i.val
    let l (i : Fin 21) : Fin 42 := Fin.ofNat 42 (21+i.val)
    have matching : ∀ i : Fin 21, dir (p i) (l i) := by decide
    have representatives (i : Fin 21) : ∃ v : S, v.val.val % 21 = i.val := by
      rcases cover (p i) (l i) ((dirs _ _).2 (Or.inl (matching i))) with hp | hl
      · refine ⟨⟨p i,hp⟩,?_⟩
        change i.val % 42 % 21 = i.val
        have hi := i.isLt
        omega
      · refine ⟨⟨l i,hl⟩,?_⟩
        change (21+i.val) % 42 % 21 = i.val
        have hi := i.isLt
        omega
    choose pick picked using representatives
    have inj : Function.Injective pick := by
      intro i j same
      apply Fin.ext
      rw [← picked i,← picked j,same]
    have coverSize : 21 ≤ S.card := by simpa using Fintype.card_le_of_injective pick inj
    let edge (i : Fin 105) : Sym2 (Fin 42) := s(point i,line i)
    let embed (i : Fin 105) : H.edgeSet := ⟨edge i,H.mem_edgeSet.mpr ((dirs _ _).2 (Or.inl (edgeOK i)))⟩
    have unique : ∀ i j : Fin 105, edge i = edge j → i = j := by decide
    have inject : Function.Injective embed := fun i j eq => unique i j (congrArg Subtype.val eq)
    have sur : Function.Surjective embed := by
      intro target
      obtain ⟨e,mem⟩ := target
      induction e using Sym2.inductionOn with
      | _ a b =>
        rcases (dirs a b).1 (H.mem_edgeSet.mp mem) with d | d
        · obtain ⟨i,pi,li⟩ := listAll a b d
          exact ⟨i,Subtype.ext (by change s(point i,line i) = s(a,b); rw [pi,li])⟩
        · obtain ⟨i,pi,li⟩ := listAll b a d
          exact ⟨i,Subtype.ext (by change s(point i,line i) = s(a,b); rw [pi,li,Sym2.eq_swap])⟩
    have count := Nat.card_congr (Equiv.ofBijective embed ⟨inject,sur⟩)
    rw [Nat.card_fin,Nat.card_coe_set_eq] at count
    omega

  -- Remove one gate and route its consumers to an extra input or to an earlier wire. Out-of-range reads retain their false default.
  have cutBoard (n : ℕ) (fr tl : List Gate) (g : Gate) (o p : ℕ)
      (port : p ≤ n+fr.length) (mon : Monotone2 ⟨fr ++ g :: tl,o⟩) :
      let step (w : List Bool) (a : Gate) := w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
      let pre (x : Fin n → Bool) := fr.foldl step (List.ofFn x)
      let run (x : Fin n → Bool) (b : Bool) := (tl.foldl step (pre x ++ [b])).getD o false
      ∃ D : Circuit, Monotone2 D ∧ D.size = fr.length+tl.length ∧
        (∀ h ∈ D.gates.take fr.length, 0 ∉ h.inputs) ∧
        (∀ (x : Fin n → Bool) (b : Bool),
          D.eval (b :: List.ofFn x) = run x ((b :: pre x).getD p false)) ∧
        (∀ (x : Fin n → Bool) (b : Bool) (i : ℕ), i < n+fr.length →
          (D.wires (b :: List.ofFn x)).getD (i+1) false = (pre x).getD i false) := by
    clear smaller critical firstHotAndProfile graphFormulaBound1894
    intro step pre run
    let cut := n+fr.length
    let rho (i : ℕ) := if i < cut then i+1 else if i = cut then p else i
    let ren (f : ℕ → ℕ) (a : Gate) : Gate := ⟨a.op,a.inputs.map f⟩
    let first := fr.map (ren fun i => i+1)
    let tail := tl.map (ren rho)
    let D : Circuit := ⟨first ++ tail,rho o⟩
    have keep : Monotone2 D := by
      intro a ha
      change a ∈ first ++ tail at ha
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
        have m := mon b (List.mem_append_left _ hb)
        exact ⟨m.1,by simpa [ren] using m.2⟩
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
        have m := mon b (List.mem_append_right _ (List.mem_cons_of_mem g hb))
        exact ⟨m.1,by simpa [ren] using m.2⟩
    have ext (ls : List Gate) (w : List Bool) : ∃ t, ls.foldl step w = w ++ t := by
      induction ls generalizing w with
      | nil => exact ⟨[],by simp⟩
      | cons a ls ih =>
        obtain ⟨t,ht⟩ := ih (step w a)
        exact ⟨[_] ++ t,by simpa [step,List.foldl_cons,List.append_assoc] using ht⟩
    have lens (ls : List Gate) (w : List Bool) : (ls.foldl step w).length = w.length+ls.length := by
      induction ls generalizing w with
      | nil => simp
      | cons a ls ih => rw [List.foldl_cons,ih]; simp [step]; omega
    have len (x : Fin n → Bool) : (pre x).length = cut := by
      change (fr.foldl step (List.ofFn x)).length = _
      rw [lens,List.length_ofFn]
    have lift (ls : List Gate) (w : List Bool) (b : Bool) :
        (ls.map (ren fun i => i+1)).foldl step (b::w) = b :: ls.foldl step w := by
      induction ls generalizing w with
      | nil => rfl
      | cons a ls ih =>
        simp only [List.map_cons,List.foldl_cons]
        change (ls.map _).foldl step (b :: (w ++ [_])) = _
        simpa only [ren,step,List.map_map,Function.comp_def,List.getD_cons_succ] using ih (step w a)
    have initial (x : Fin n → Bool) (b : Bool) : first.foldl step (b::List.ofFn x) = b::pre x :=
      lift fr (List.ofFn x) b
    have snoc (w : List Bool) (b : Bool) (i : ℕ) :
        (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
      induction w generalizing i with
      | nil => cases i <;> rfl
      | cons a w ih => cases i with
                        | zero => rfl
                        | succ i => simpa using ih i
    have advance (ls : List Gate) (w v : List Bool) (eq : w.length = v.length) (past : cut < w.length)
        (rel : ∀ i, w.getD (rho i) false = v.getD i false) :
        ∀ i, ((ls.map (ren rho)).foldl step w).getD (rho i) false = (ls.foldl step v).getD i false := by
      induction ls generalizing w v with
      | nil => exact rel
      | cons a ls ih =>
        have arg : ((ren rho a).inputs.map fun i => w.getD i false) = a.inputs.map (fun i => v.getD i false) := by
          simp only [ren,List.map_map,Function.comp_def]
          exact List.map_congr_left (fun i _ => rel i)
        have hw := port
        change p ≤ cut at hw
        simp only [List.map_cons,List.foldl_cons]
        apply ih (step w (ren rho a)) (step v a)
        · simp [step,eq]
        · simp [step]; omega
        · intro i
          change (_ ++ [_]).getD (rho i) false = (_ ++ [_]).getD i false
          rw [snoc,snoc]
          by_cases h : i = v.length
          · have hh : rho i = w.length := by dsimp [rho]; split_ifs <;> omega
            rw [ite_eq_left hh,ite_eq_left h,arg]
          · have hh : rho i ≠ w.length := by dsimp [rho]; split_ifs <;> omega
            simpa only [ite_eq_right hh,ite_eq_right h] using rel i
    refine ⟨D,keep,?_,?_,?_,?_⟩
    · change (first ++ tail).length = _
      simp [first,tail]
    · intro h mem
      have lf : first.length = fr.length := by simp [first]
      change h ∈ (first ++ tail).take fr.length at mem
      rw [← lf,List.take_append_of_le_length le_rfl,List.take_length] at mem
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp mem
      simp [ren]
    · intro x b
      let w := pre x
      let z := (b::w).getD p false
      have lw : w.length = cut := len x
      have rel (i : ℕ) : (b::w).getD (rho i) false = (w ++ [z]).getD i false := by
        rw [snoc,lw]
        by_cases hi : i < cut
        · have ne : i ≠ cut := by omega
          simp [rho,hi,ne]
        · by_cases same : i = cut
          · simp [rho,same,z]
          · have bound1 : (b::w).length ≤ i := by simp [lw]; omega
            have bound2 : w.length ≤ i := by omega
            simp only [rho,ite_eq_right hi,ite_eq_right same,List.getD_eq_default _ _ bound1,
              List.getD_eq_default _ _ bound2]
      change ((first ++ tail).foldl step (b :: List.ofFn x)).getD (rho o) false = _
      rw [List.foldl_append,initial]
      exact advance tl (b::w) (w ++ [z]) (by simp) (by simp [lw]) rel o
    · intro x b i hi
      change ((first ++ tail).foldl step (b :: List.ofFn x)).getD (i+1) false = _
      rw [List.foldl_append,initial]
      obtain ⟨ys,hys⟩ := ext tail (b::pre x)
      rw [hys,List.getD_append _ _ _ _ (by simp [len]; exact hi)]
      rfl

  -- Coordinatewise monotonicity holds with an extra input prepended to the original variables.
  have portMono {n : ℕ} (D : Circuit) (hm : Monotone2 D) (b c : Bool)
      (x y : Fin n → Bool) (hb : b = true → c = true) (hx : ∀ i, x i = true → y i = true) :
      D.eval (b :: List.ofFn x) = true → D.eval (c :: List.ofFn y) = true := by
    clear smaller critical firstHotAndProfile graphFormulaBound1894 cutBoard
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have snoc (w : List Bool) (a : Bool) (i : ℕ) :
        (w ++ [a]).getD i false = if i = w.length then a else w.getD i false := by
      induction w generalizing i with
      | nil => cases i <;> rfl
      | cons v w ih => cases i with
                        | zero => rfl
                        | succ i => simpa using ih i
    have go (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ D.gates) (w v : List Bool)
        (len : w.length = v.length) (rel : ∀ i, w.getD i false = true → v.getD i false = true) :
        ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step v).getD i false = true := by
      induction gs generalizing w v with
      | nil => exact rel
      | cons g gs ih =>
        have kind := (hm g (sub g (by simp))).1
        change g.op = .and ∨ g.op = .or at kind
        have one : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
            g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
          rcases kind with h | h
          · rw [h]
            change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
            simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
            exact fun ok i hi => rel i (ok i hi)
          · rw [h]
            change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
            simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
            rintro ⟨i,hi,ok⟩
            exact ⟨i,hi,rel i ok⟩
        rw [List.foldl_cons,List.foldl_cons]
        apply ih (fun h mem => sub h (by simp [mem])) (step w g) (step v g) (by simp [step,len])
        intro i
        change (_ ++ [_]).getD i false = true → (_ ++ [_]).getD i false = true
        rw [snoc,snoc,len]
        by_cases eq : i = v.length
        · simpa only [ite_eq_left eq] using one
        · simpa only [ite_eq_right eq] using rel i
    apply go D.gates (fun _ h => h) (b :: List.ofFn x) (c :: List.ofFn y) (by simp) _ D.output
    intro i
    cases i with
    | zero => exact hb
    | succ i =>
      change (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true
      by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),
          List.getElem_ofFn,List.getElem_ofFn]
        exact hx _
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
        exact id
  intro C mon small active
  classical
  let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val+21-u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let F (x : Fin 42 → Bool) := ∃ u v, E u v ∧ x u = true ∧ x v = true
  by_contra missing
  have exactF (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔ F x := by
    by_contra fail
    exact missing ⟨x,fail⟩
  have exclude (D : Circuit) (hm : Monotone2 D) (hs : D.size ≤ 123) (c : Bool) :
      ¬ (∀ x : Fin 42 → Bool, D.eval (c :: List.ofFn x) = true ↔ F x) := by
    intro agree
    apply smaller D hm hs c _ agree
    intro t ht calcD
    apply graphFormulaBound1894 t ht
    intro x
    rw [calcD x]
    exact agree x
  let sites : List ℕ := [0,1,2,6,8,18,24,31,33,37]
  let W := Finset.univ.filter fun i : Fin 42 => i.val ∈ sites
  have sameInput : (fun i : Fin 42 => decide (i ∈ W)) = (fun i : Fin 42 => decide (i.val ∈ sites)) := by
    funext i
    simp [W]
  have activeW : ∃ k g, C.gates[k]? = some g ∧ g.op = .and ∧
      (C.wires (List.ofFn fun i : Fin 42 => decide (i ∈ W))).getD (42+k) false = true := by
    rw [sameInput]
    exact active
  obtain ⟨k,g,masks,atGate,isAnd,arity,arityBound,_,_,_,Y,hYW,Ysmall,Yon⟩ :=
    firstHotAndProfile 42 C W mon activeW
  obtain ⟨hk,eg⟩ := List.getElem?_eq_some_iff.mp atGate
  let fr := C.gates.take k
  let tl := C.gates.drop (k+1)
  have shape : C.gates = fr ++ g :: tl := by
    have t := List.take_append_drop (k+1) C.gates
    rw [List.take_succ_eq_append_getElem hk,eg,List.append_assoc] at t
    exact t.symm
  have fl : fr.length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have remaining : fr.length+tl.length ≤ 123 := by
    have h := congrArg List.length shape
    simp only [List.length_append,List.length_cons] at h
    change C.gates.length ≤ 124 at small
    omega
  have mshape : Monotone2 ⟨fr ++ g :: tl,C.output⟩ := by
    intro h hh
    apply mon h
    rwa [shape]
  let step (w : List Bool) (a : Gate) := w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
  let pre (x : Fin 42 → Bool) := fr.foldl step (List.ofFn x)
  let val (x : Fin 42 → Bool) (i : ℕ) := (pre x).getD i false
  let trig (x : Fin 42 → Bool) := g.op.eval (g.inputs.map (val x))
  let R (x : Fin 42 → Bool) (s : Bool) := (tl.foldl step (pre x ++ [s])).getD C.output false
  have correct (x : Fin 42 → Bool) : R x (trig x) = true ↔ F x := by
    have origin : C.eval (List.ofFn x) = R x (trig x) := by
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
      rw [shape,List.foldl_append,List.foldl_cons]
    rw [← origin]
    exact exactF x
  have ext (ls : List Gate) (w : List Bool) : ∃ t, ls.foldl step w = w ++ t := by
    induction ls generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons a ls ih =>
      obtain ⟨t,ht⟩ := ih (step w a)
      exact ⟨[_] ++ t,by simpa [step,List.foldl_cons,List.append_assoc] using ht⟩
  have lens (ls : List Gate) (w : List Bool) : (ls.foldl step w).length = w.length+ls.length := by
    induction ls generalizing w with
    | nil => simp
    | cons a ls ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have lp (x : Fin 42 → Bool) : (pre x).length = 42+fr.length := by
    dsimp only [pre]
    rw [lens,List.length_ofFn]
  have zAt (x : Fin 42 → Bool) : (C.wires (List.ofFn x)).getD (42+k) false = trig x := by
    obtain ⟨t,ht⟩ := ext tl (pre x ++ [trig x])
    change (C.gates.foldl step (List.ofFn x)).getD (42+k) false = _
    rw [shape,List.foldl_append,List.foldl_cons]
    change (tl.foldl step (pre x ++ [trig x])).getD (42+k) false = _
    rw [ht,List.getD_append _ _ _ _ (by simp [lp,fl])]
    rw [List.getD_append_right _ _ _ _ (by simp [lp,fl]),lp,fl]
    simp
  let xY (i : Fin 42) := decide (i ∈ Y)
  have hotY : trig xY = true := (zAt xY).symm.trans Yon
  have srcValid (i : ℕ) (hi : i ∈ g.inputs) : i < 42+fr.length := by
    have all : (g.inputs.map (val xY)).all id = true := by
      change g.op.eval (g.inputs.map (val xY)) = true at hotY
      rw [isAnd] at hotY
      exact hotY
    have on : val xY i = true := (List.all_eq_true.mp all) _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
    by_contra! far
    change (pre xY).getD i false = true at on
    rw [List.getD_eq_default _ _ (by rwa [lp])] at on
    exact Bool.noConfusion on
  have board (p : ℕ) (hp : p ≤ 42+fr.length) :
      ∃ D : Circuit, Monotone2 D ∧ D.size = fr.length+tl.length ∧
        (∀ h ∈ D.gates.take fr.length, 0 ∉ h.inputs) ∧
        (∀ (x : Fin 42 → Bool) (b : Bool), D.eval (b :: List.ofFn x) = R x ((b :: pre x).getD p false)) ∧
        (∀ (x : Fin 42 → Bool) (b : Bool) (i : ℕ), i < 42+fr.length →
          (D.wires (b :: List.ofFn x)).getD (i+1) false = val x i) :=
    cutBoard 42 fr tl g C.output p hp mshape
  have noFit (p : ℕ) (hp : p ≤ 42+fr.length) (c : Bool) :
      ¬ (∀ x, R x ((c :: pre x).getD p false) = true ↔ F x) := by
    obtain ⟨D,hm,sz,_,run,_⟩ := board p hp
    intro all
    apply exclude D hm (by omega) c
    intro x
    rw [run]
    exact all x
  have unary (v : Bool) : GateOp.and.eval [v] = v := by cases v <;> rfl
  have pairAnd (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
  have pair : ∃ a b : ℕ, g.inputs = [a,b] := by
    cases ins : g.inputs with
    | nil =>
      exfalso
      apply noFit 0 (by omega) true
      intro x
      have h : trig x = true := by change g.op.eval _ = _; rw [isAnd,ins]; rfl
      exact h ▸ correct x
    | cons a u =>
      cases u with
      | nil =>
        exfalso
        have hvalid := srcValid a (by simp [ins])
        apply noFit (a+1) (by omega) false
        intro x
        have h : trig x = val x a := by
          change g.op.eval (g.inputs.map _) = _
          rw [isAnd,ins]
          exact unary _
        change R x (val x a) = true ↔ F x
        rw [← h]
        exact correct x
      | cons b rest =>
        cases rest with
        | nil => exact ⟨a,b,rfl⟩
        | cons c t =>
          have h : g.inputs.length ≤ 2 := arity ▸ arityBound
          simp [ins] at h
  obtain ⟨a,b,ab⟩ := pair
  have av := srcValid a (by simp [ab])
  have bv := srcValid b (by simp [ab])
  have trigPair (x) : trig x = (val x a && val x b) := by
    change g.op.eval (g.inputs.map _) = _
    rw [isAnd,ab]
    exact pairAnd _ _
  obtain ⟨D,dm,ds,topD,runD,wireD⟩ := board 0 (by omega)
  have atR (c : Bool) (x) : D.eval (c :: List.ofFn x) = R x c := runD x c
  have monR (x y : Fin 42 → Bool) (c d : Bool) (hc : c=true → d=true)
      (hxy : ∀ i, x i=true → y i=true) : R x c = true → R y d = true := by
    rw [← atR,← atR]
    exact portMono D dm c d x y hc hxy
  have missed : ∃ u v : Fin 42, E u v ∧ R (fun i => decide (i = u ∨ i = v)) false = false := by
    by_contra miss
    apply noFit 0 (by omega) false
    intro x
    change R x false = true ↔ F x
    constructor
    · intro h
      exact (correct x).mp (monR x x false (trig x) (by simp) (fun _ v => v) h)
    · rintro ⟨u,v,e,hu,hv⟩
      let row (i : Fin 42) := decide (i = u ∨ i = v)
      have ok : R row false = true := by
        cases eq : R row false with
        | false => exact (miss ⟨u,v,e,eq⟩).elim
        | true => rfl
      apply monR row x false false (fun h => h) _ ok
      intro i hi
      rcases of_decide_eq_true hi with h | h
      · exact h ▸ hu
      · exact h ▸ hv
  have forks (s : Bool) : ∃ x, ¬ F x ∧ val x a = s ∧ val x b = !s ∧ R x true = true := by
    let pick := if s then a else b
    have hp : pick < 42+fr.length := by dsimp [pick]; split <;> assumption
    have above (x) : F x → R x (val x pick) = true := by
      intro fx
      apply monR x x (trig x) _ _ (fun _ h => h) ((correct x).mpr fx)
      rw [trigPair]
      intro on
      obtain ⟨onA,onB⟩ := Bool.and_eq_true_iff.mp on
      dsimp [pick]
      split <;> assumption
    obtain ⟨x,off,on⟩ : ∃ x, ¬ F x ∧ R x (val x pick) = true := by
      by_contra miss
      apply noFit (pick+1) (by omega) false
      intro x
      change R x (val x pick) = true ↔ F x
      refine ⟨?_,above x⟩
      intro on
      by_contra off
      exact miss ⟨x,off,on⟩
    have actual : R x (val x a && val x b) = false := by
      apply Bool.eq_false_iff.mpr
      rw [← trigPair]
      exact fun actual => off ((correct x).mp actual)
    have chooseVal : val x pick = (if s then val x a else val x b) := by cases s <;> rfl
    rw [chooseVal] at on
    have truthTable (u v s : Bool) (r : Bool → Bool) (off : r (u && v) = false)
        (on : r (if s then u else v) = true) : u = s ∧ v = !s ∧ r true = true := by
      cases u <;> cases v <;> cases s <;>
        first | exact ⟨rfl,rfl,on⟩ | exact Bool.noConfusion (off.symm.trans on)
    exact ⟨x,off,truthTable _ _ _ (R x) actual on⟩
  apply critical D dm (by omega) (a+1) (b+1)
  · exact ⟨fr.length,by omega,by omega,by omega,topD⟩
  · intro x
    change D.eval (((D.wires (false :: List.ofFn x)).getD (a+1) false &&
      (D.wires (false :: List.ofFn x)).getD (b+1) false) :: List.ofFn x) = true ↔ F x
    rw [wireD x false a av,wireD x false b bv,atR,← trigPair]
    exact correct x
  · obtain ⟨u,v,e,h⟩ := missed
    exact ⟨u,v,e,(atR _ _).trans h⟩
  · intro s
    obtain ⟨x,off,xa,xb,run⟩ := forks s
    exact ⟨x,off,(wireD x false a av).trans xa,(wireD x false b bv).trans xb,(atR _ _).trans run⟩
  · refine ⟨Y,Ysmall,fun v hv => (Finset.mem_filter.mp (hYW hv)).2,?_⟩
    change ((D.wires (false :: List.ofFn xY)).getD (a+1) false &&
      (D.wires (false :: List.ofFn xY)).getD (b+1) false) = true
    rw [wireD xY false a av,wireD xY false b bv,← trigPair]
    exact hotY
