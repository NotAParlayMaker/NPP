import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2475_879
    (one : ∀ (q N : ℕ) (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit), 200≤q → N=q^2+q+1 → (∀ l,Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p r, p≠r → ∃! w,I p w ∧ I r w) → Monotone2 C → C.output<N+N+C.size →
      (∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ,g.inputs=[a,b] ∧ a<b ∧ b<N+N+j) →
      (∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true) →
      (∀ x : Fin (N+N)→Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
        (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) →
      let M := fun j : ℕ => ∃ g : Gate, C.gates[j]?=some g ∧ g.op=.and ∧ ∀ i ∈ g.inputs,
        ∃ p : Fin N→Bool, (C.wires (List.ofFn p ++ List.replicate N false)).getD i false ≠
          (C.wires (List.ofFn p ++ List.replicate N true)).getD i false
      (∀ i j,M i → M j → i=j) → N*q≤100*C.size)
    (hard : ∀ (q N : ℕ) (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit), 200≤q → N=q^2+q+1 → (∀ l,Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p r, p≠r → ∃! w,I p w ∧ I r w) → Monotone2 C → C.output<N+N+C.size →
      (∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ,g.inputs=[a,b] ∧ a<b ∧ b<N+N+j) →
      (∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true) →
      (∀ x : Fin (N+N)→Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
        (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) →
      let M := fun j : ℕ => ∃ g : Gate, C.gates[j]?=some g ∧ g.op=.and ∧ ∀ i ∈ g.inputs,
        ∃ p : Fin N→Bool, (C.wires (List.ofFn p ++ List.replicate N false)).getD i false ≠
          (C.wires (List.ofFn p ++ List.replicate N true)).getD i false
      (∃ i j, M i ∧ M j ∧ i≠j) → N*q≤100*C.size) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  classical
  intro flag q N I inst C hq geom num joins mono output inputs pos sound E subset exactFlags budget
  by_cases early : q<200
  ·
    have getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
        (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      split_ifs with h1 h2
      · rw [List.getElem?_append_left h1]
      · subst h2; simp
      · rw [List.getElem?_append_right (by omega)]
        rw [List.getElem?_eq_none (by simp; omega)]; simp

    -- one step of evaluation and one step of the dependency sets
    let wstep (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    let dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
      D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

    have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

    have sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
        W1.length = D.length → W2.length = D.length →
        (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
        ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
          (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
      intro gs
      induction gs with
      | nil => intro W1 W2 D _ _ h; simpa using h
      | cons g gs ih =>
        intro W1 W2 D h1 h2 h
        simp only [List.foldl_cons]
        apply ih
        · simp [wstep, dstep, h1]
        · simp [wstep, dstep, h2]
        · intro w hw
          simp only [wstep, dstep] at hw ⊢
          rw [getD_snoc, getD_snoc]
          rw [getD_snoc] at hw
          rw [h1, h2]
          split_ifs with c1 c2
          · rw [if_pos c1] at hw; exact h w hw
          · rw [if_neg c1, if_pos c2] at hw
            congr 1
            apply List.map_congr_left
            intro j hj
            apply h j
            intro i hi
            apply hw
            rw [Finset.mem_biUnion]
            exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
          · rfl

    have cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
        (∀ g ∈ gs, g.inputs.length ≤ 2) →
        (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
        ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
          T.card + k + gs.length := by
      intro gs
      induction gs with
      | nil => intro D k _ h T; simpa using h T
      | cons g gs ih =>
        intro D k hg h T
        simp only [List.foldl_cons, List.length_cons]
        have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
        · omega
        intro T
        have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
            ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
          intro i hi
          rw [Finset.mem_biUnion] at hi
          obtain ⟨w, hw, hi⟩ := hi
          simp only [dstep] at hi
          rw [getD_snoc] at hi
          rw [Finset.mem_biUnion]
          split_ifs at hi with c1 c2
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
          · rw [Finset.mem_biUnion] at hi
            obtain ⟨j, hj, hi⟩ := hi
            exact ⟨j, Finset.mem_union_right _ hj, hi⟩
          · simp at hi
        have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
        have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
        have h4 := List.toFinset_card_le g.inputs
        have h5 := hg g List.mem_cons_self
        have h6 := Finset.card_le_card hsub
        by_cases hm : D.length ∈ T
        · have h7 := Finset.card_erase_of_mem hm
          have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
          omega
        · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
              T.biUnion fun w => D.getD w ∅ := by
            apply Finset.biUnion_congr rfl
            intro w hw
            simp only [dstep]
            rw [getD_snoc]
            have : w ≠ D.length := fun e => hm (e ▸ hw)
            split_ifs with c1
            · rfl
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          rw [h9]; have := h T; omega

    have base_card (n : ℕ) (T : Finset ℕ) :
        (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
          T.card + 0 := by
      refine le_trans Finset.card_biUnion_le ?_
      rw [Nat.add_zero]
      calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
          ≤ ∑ w ∈ T, 1 := by
            apply Finset.sum_le_sum
            intro w _
            rw [List.getD_eq_getElem?_getD]
            by_cases hw : w < n
            · simp [hw]
            · rw [List.getElem?_eq_none (by simp; omega)]; simp
        _ = T.card := by simp


    have support_bound : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ i < n, ∃ x : List Bool, x.length = n ∧ C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) → n ≤ C.size + 1 := by
      intro n C hfan hdep
      let D0 : List (Finset ℕ) := (List.range n).map fun i => ({i} : Finset ℕ)
      let S := (C.gates.foldl dstep D0).getD C.output ∅
      have hsub : Finset.range n ⊆ S := by
        intro i hi
        rw [Finset.mem_range] at hi
        by_contra hni
        obtain ⟨x, hx, hne⟩ := hdep i hi
        apply hne
        let y := x.set i (!(x.getD i false))
        have hy : y.length = n := by simp [y, hx]
        have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y D0
          (by simp [D0, hx]) (by simp [D0, hy]) ?_ C.output ?_
        · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
          rw [wires_eq, wires_eq]; exact key
        · intro w hw
          by_cases hwn : w < n
          · apply hw w
            simp [D0, List.getD_eq_getElem?_getD, hwn]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
        · intro j hj
          have hji : j ≠ i := fun e => hni (e ▸ hj)
          simp only [y]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_set_ne (Ne.symm hji)]
      have hc := cardb C.gates D0 0 hfan (base_card n) {C.output}
      simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      change n ≤ ((C.gates.foldl dstep D0).getD C.output ∅).card at this
      unfold PEqualNP.CircuitLowerBounds.Circuit.size
      omega
    let P (N : ℕ) := Fin N
    let Input (N : ℕ) := Fin (N+N) → Bool
    let point {N : ℕ} (p : P N) := Fin.castAdd N p
    let line {N : ℕ} (w : P N) := Fin.natAdd N w
    let pair {N : ℕ} (p w : P N) (i : Fin (N+N)) := decide (i=point p ∨ i=line w)
    let singleton {N : ℕ} (i : Fin (N+N)) (j : Fin (N+N)) := decide (j=i)
    let SparseSound {N : ℕ} (q : ℕ) (R : P N→P N→Prop) (C : Circuit) :=
      ∀ x : Input N, Fintype.card {w : P N // x (line w)=true} ≤ q →
        (¬∃ p w, R p w ∧ x (point p)=true ∧ x (line w)=true) → circuitFun (N+N) C x=false
    let Positive {N : ℕ} (R : P N→P N→Prop) (C : Circuit) :=
      ∀ p w, R p w → circuitFun (N+N) C (pair p w)=true

    have dis {N : ℕ} (p w : P N) : point p ≠ line w := by
      intro h
      have h' := congrArg Fin.val h
      simp only [point,line,Fin.val_castAdd,Fin.val_natAdd] at h'
      omega

    have set_other {n : ℕ} (i j : Fin n) (ne : i≠j) :
        (List.ofFn (fun k : Fin n => decide (k=i ∨ k=j))).set i.val
          (!((List.ofFn (fun k : Fin n => decide (k=i ∨ k=j))).getD i.val false)) =
            List.ofFn (fun k : Fin n => decide (k=j)) := by
      have r : (List.ofFn (fun k : Fin n => decide (k=i ∨ k=j))).getD i.val false = true := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
        simp [i.isLt]
      rw [r]
      apply List.ext_getElem
      · simp
      · intro t ht ht'
        have htn : t<n := by simpa using ht'
        rw [List.getElem_set]
        simp only [List.getElem_ofFn]
        by_cases hi : i.val=t
        · subst t; simp [ne]
        · have neq : (⟨t,htn⟩ : Fin n) ≠ i := fun h => hi (congrArg Fin.val h).symm
          simp [hi,neq]

    have off_single {N q} (R : P N→P N→Prop) (C : Circuit) (pos : 0<q)
        (sound : SparseSound q R C) (i : Fin (N+N)) :
        circuitFun (N+N) C (singleton i) = false := by
      apply sound
      · let f : {w : P N // singleton i (line w)=true} → Unit := fun _ => ()
        have injective : Function.Injective f := by
          intro a b _
          have eq : line a.val = line b.val :=
            (of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm
          exact Subtype.ext (Fin.natAdd_injective _ _ eq)
        have c := Fintype.card_le_of_injective f injective
        simp only [Fintype.card_unit] at c
        omega
      · rintro ⟨p,w,_,a,b⟩
        exact dis p w ((of_decide_eq_true a).trans (of_decide_eq_true b).symm)

    have support_size {N q} (R : P N→P N→Prop) (C : Circuit)
        (hq : 0<q) (pnon : ∀ p,∃ w,R p w) (wnon : ∀ w,∃ p,R p w)
        (fan : ∀ g∈C.gates,g.inputs.length≤2)
        (pos : Positive R C) (sound : SparseSound q R C) : 2*N ≤ C.size+1 := by
      have cert (i : Fin (N+N)) : ∃ x : List Bool,x.length=N+N ∧ C.eval x ≠ C.eval (x.set i.val (!(x.getD i.val false))) := by
        induction i using Fin.addCases with
        | left p =>
          obtain ⟨w,hit⟩ := pnon p
          refine ⟨List.ofFn (pair p w),by simp,?_⟩
          rw [set_other (point p) (line w) (dis p w)]
          change circuitFun (N+N) C (pair p w) ≠ circuitFun (N+N) C (singleton (line w))
          rw [pos p w hit,off_single R C hq sound]
          decide
        | right w =>
          obtain ⟨p,hit⟩ := wnon w
          have swap : pair p w = (fun k => decide (k=line w ∨ k=point p)) := by
            funext k; simp only [pair,or_comm]
          refine ⟨List.ofFn (pair p w),by simp,?_⟩
          have cert := set_other (line w) (point p) (dis p w).symm
          rw [←swap] at cert
          rw [cert]
          change circuitFun (N+N) C (pair p w) ≠ circuitFun (N+N) C (singleton (point p))
          rw [pos p w hit,off_single R C hq sound]
          decide
      simpa [two_mul] using support_bound (N+N) C fan (fun i hi => cert ⟨i,hi⟩)

    have small_orders {N q} (R : P N→P N→Prop) [DecidableRel R] (C : Circuit)
        (hq : 100<q) (up : q<200) (order : N=q^2+q+1)
        (count : ∀ w,Fintype.card {p : P N // R p w}=q+1)
        (join : ∀ p r, p≠r → ∃! w,R p w ∧ R r w)
        (mono : Monotone2 C) (pos : Positive R C) (sound : SparseSound q R C) :
        N*q ≤ 100*C.size := by
      have large : 100 ≤ N := by omega
      have pnon (p : P N) : ∃ w,R p w := by
        let zero : Fin N := ⟨0,by omega⟩
        let one : Fin N := ⟨1,by omega⟩
        have diff : zero ≠ one := by intro h; exact Nat.zero_ne_one (congrArg Fin.val h)
        obtain ⟨r,other⟩ : ∃ r : P N,p≠r := by
          by_cases h : p=zero
          · exact ⟨one,h ▸ diff⟩
          · exact ⟨zero,h⟩
        obtain ⟨w,hw,_⟩ := join p r other
        exact ⟨w,hw.1⟩
      have wnon (w : P N) : ∃ p,R p w := by
        have h : 0<Fintype.card {p : P N // R p w} := by rw [count];omega
        obtain ⟨⟨p,hit⟩⟩ := Fintype.card_pos_iff.mp h
        exact ⟨p,hit⟩
      have lb := support_size R C (by omega) pnon wnon (fun g h => (mono g h).2) pos sound
      have e := Nat.mul_le_mul_left N (show q≤199 by omega)
      omega
    exact small_orders I C hq early geom num joins mono pos sound
  let M := fun j : ℕ => ∃ g : Gate, C.gates[j]?=some g ∧ g.op=.and ∧ ∀ i ∈ g.inputs,
        ∃ p : Fin N→Bool, (C.wires (List.ofFn p ++ List.replicate N false)).getD i false ≠
          (C.wires (List.ofFn p ++ List.replicate N true)).getD i false
  by_cases unique : ∀ i j,M i → M j → i=j
  · exact one q N I C (by omega) geom num joins mono output inputs pos sound unique
  · apply hard q N I C (by omega) geom num joins mono output inputs pos sound
    push Not at unique
    obtain ⟨i,j,hi,hj,ne⟩ := unique
    exact ⟨i,j,hi,hj,ne⟩
