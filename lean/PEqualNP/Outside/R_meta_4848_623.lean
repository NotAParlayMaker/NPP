import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Wire evaluation and gate bypass adapted from L-meta-2668, including its credits
-- to willakone (L-meta-1499, PR 3112). The singleton-support argument is new.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_4848_623
(width : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
    IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ →
    ∀ j<C.gates.length,(gateAt C j).op=.and → ¬BelowF G C j →
    let S := fun w : ℕ => Finset.univ.filter (fun u : Fin n => (C.wires (List.ofFn (pairInput u u))).getD w false=true)
    ∃ a b,(gateAt C j).inputs=[a,b] ∧ ((S a).card≤1 ∨ (S b).card≤1))
(consistency : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
    IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ →
    ∀ j<C.gates.length,(gateAt C j).op=.and → ¬BelowF G C j →
    let S := fun w : ℕ => Finset.univ.filter (fun u : Fin n => (C.wires (List.ofFn (pairInput u u))).getD w false=true)
    ∀ a b,(gateAt C j).inputs=[a,b] ∨ (gateAt C j).inputs=[b,a] →
      ∀ u v : Fin n,S a={u} → v∈S b → G.Adj u v) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13 := by
  classical
  have evalAnd (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  have pairAt {n : ℕ} (u v i : Fin n) : pairInput u v i=decide (i=u ∨ i=v) := rfl
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl
  have foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨.or,[]⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD,hj]
  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj
  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)
  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj
  have mono_ops {C : Circuit} (hM : Monotone2 C) :
      ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
    intro k hk
    exact (hM _ (gateAt_mem hk)).1
  have graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
      graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
    change (decide (∃ a ∈ (∅ : Finset _), x a=true) || decide (∃ u v,G.Adj u v ∧ x u=true ∧ x v=true))=true ↔ _
    simp
  let sig (n : ℕ) (C : Circuit) (w : ℕ) := Finset.univ.filter (fun i : Fin n => (C.wires (List.ofFn (pairInput i i))).getD w false=true)
  have of_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (m : Monotone2 C)
      (thin : ∀ r<C.gates.length,(gateAt C r).op=.and → ¬BelowF G C r →
        ∃ a b,(gateAt C r).inputs=[a,b] ∧ ((sig n C a).card≤1 ∨ (sig n C b).card≤1))
      (compatible : ∀ r<C.gates.length,(gateAt C r).op=.and → ¬BelowF G C r → ∀ a b,(gateAt C r).inputs=[a,b] ∨ (gateAt C r).inputs=[b,a] →
        ∀ u v : Fin n,sig n C a={u} → v∈sig n C b → G.Adj u v) :
      ∀ r<C.gates.length,(gateAt C r).op=.and → ∀ u v,gateVal n C r (pairInput u v)=true → G.Adj u v := by
    intro r hr op u v fire
    by_contra wrong
    let z := pairInput u v
    let F (x : Fin n → Bool) (i : ℕ) := val C (List.ofFn x) i
    have crossing {a b : ℕ} {p q : Fin n} (card : (sig n C a).card≤1)
        (small : p ∈ sig n C a) (big : q ∈ sig n C b)
        {r : ℕ} (hr:r<C.gates.length) (g:(gateAt C r).op=.and)
        (bad : ¬BelowF G C r) (order:(gateAt C r).inputs=[a,b] ∨ (gateAt C r).inputs=[b,a]) : G.Adj p q := by
      have eq : sig n C a={p} := Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr small) (by simpa using card) |>.symm
      exact compatible r hr g bad a b order p q eq big
    have ind : ∀ w, w<n+C.gates.length → F z w=true →
        (F (pairInput u u) w=true ∨ F (pairInput v v) w=true) ∧
        (∀ k,w=n+k → (gateAt C k).op≠.and) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro bound on
        by_cases raw : w<n
        · let t : Fin n := ⟨w,raw⟩
          have input (x : Fin n → Bool) : F x w=x t := by
            rw [show F x w=val C (List.ofFn x) w from rfl,val_input (n:=n) (by simp) raw]
            simp [List.getD_eq_getElem?_getD,t,raw]
          rw [input] at on
          refine ⟨?_,fun k eq => by omega⟩
          rw [input,input]
          have h : t=u ∨ t=v := of_decide_eq_true on
          rcases h with h|h <;> simp [pairAt,h]
        · let k := w-n
          have same : w=n+k := by dsimp [k];omega
          have hk : k<C.gates.length := by omega
          let g := gateAt C k
          let valAt (x : Fin n → Bool) (i : ℕ) := if i<w then F x i else false
          have eval (x : Fin n → Bool) : F x w=g.op.eval (g.inputs.map (valAt x)) := by
            dsimp [F,g,valAt]
            rw [same,val_gate (n:=n) (by simp) hk]
          rw [eval] at on
          rcases mono_ops m k hk with and|disj
          · have bad : ¬BelowF G C k := by
              intro below
              have hit : gateVal n C k z=true := by
                change F z (n+k)=true
                rw [←same,eval]
                exact on
              obtain ⟨p,q,pq,hp,hq⟩ := (graph_true G z).mp (below z hit)
              rcases of_decide_eq_true hp with rfl|rfl <;> rcases of_decide_eq_true hq with rfl|rfl <;> first | exact G.irrefl pq | exact wrong pq | exact wrong pq.symm
            obtain ⟨a,b,ab,narrow⟩ := thin k hk and bad
            change g.op=.and at and
            change g.inputs=[a,b] at ab
            simp only [and,ab,List.map_cons,List.map_nil,evalAnd,evalOr,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at on
            have side (i : ℕ) (h : valAt z i=true) : ∃ t : Fin n,(t=u ∨ t=v) ∧ t∈sig n C i := by
              have small : i<w := by by_contra bad;simp [valAt,bad] at h
              have inherited := (ih i small (by omega) (by simpa [valAt,small] using h)).1
              rcases inherited with lu|rv
              · exact ⟨u,Or.inl rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lu⟩⟩
              · exact ⟨v,Or.inr rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rv⟩⟩
            obtain ⟨p,hp,pa⟩ := side a on.1
            obtain ⟨q,hq,qb⟩ := side b on.2
            have edge : G.Adj p q := narrow.elim (fun h => crossing h pa qb hk and bad (Or.inl ab))
              (fun h => (crossing h qb pa hk and bad (Or.inr ab)).symm)
            rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;> first | exact (G.irrefl edge).elim | exact (wrong edge).elim | exact (wrong edge.symm).elim
          · change g.op=.or at disj
            have get (x) : F x w=true ↔ ∃ i∈g.inputs,valAt x i=true := by
              rw [eval,disj];simp [evalAnd,evalOr]
            obtain ⟨i,mem,hit⟩ := (get z).mp (by rwa [eval])
            have small : i<w := by by_contra bad;simp [valAt,bad] at hit
            have inherited := (ih i small (by omega) (by simpa [valAt,small] using hit)).1
            refine ⟨inherited.imp (fun h => (get _).mpr ⟨i,mem,by simpa [valAt,small] using h⟩)
              (fun h => (get _).mpr ⟨i,mem,by simpa [valAt,small] using h⟩),?_⟩
            intro j eq
            have h : j=k := by omega
            simpa [h,show (gateAt C k).op=.or from disj]
    exact (ind (n+r) (by omega) fire).2 r rfl op
  intro n G d tri square C minimal sem
  apply of_local G C minimal.1 (width n G C tri square minimal sem)
  intro j hj op bad a b order u v center member
  exact consistency n G C tri square minimal sem j hj op bad a b order u v center member


