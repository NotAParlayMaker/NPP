import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1578
open PEqualNP.CircuitLowerBounds

private def line (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}
private def offLine (t a : Fin 13) := decide (a ∉ line t)
private def added (p a : Fin 13) := decide (a=p ∨ a ∉ line 0)
private abbrev ev (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) := Circuit.eval ⟨gs,w⟩ (List.ofFn x)
private def eligible (t : Fin 13) := t ∈ ({4,10,12} : Finset (Fin 13)) ∨ t ∈ ({1,5,11} : Finset (Fin 13))

private theorem primary : ∀ t : Fin 13, eligible t → t ≠ 0 ∧
    ∀ p : Fin 13, p=3 ∨ p=9 → ∀ a : Fin 13, added p a=true → offLine 0 a=false → offLine t a=true := by
  unfold eligible offLine added line
  decide

private theorem wire_shape (gs : List Gate) (a : ℕ) (x : List Bool) :
    ∃ ys, Circuit.wires ⟨gs,a⟩ x = x ++ ys ∧ ys.length=gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[],by simp [Circuit.wires],rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => x.getD i false)
    obtain ⟨ys,shape,len⟩ := ih (x ++ [b])
    refine ⟨b::ys,?_,by simp [len]⟩
    change Circuit.wires ⟨gs,a⟩ (x ++ [b]) = x ++ (b::ys)
    rw [shape]
    simp

private theorem input_value (gs : List Gate) (k : Fin 13) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs,k.val⟩ (List.ofFn x) = x k := by
  obtain ⟨ys,h,_⟩ := wire_shape gs k.val (List.ofFn x)
  rw [Circuit.eval,h,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using k.isLt),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
  rw [List.getElem_ofFn]


private theorem append_wires (a b : List Gate) (x : List Bool) :
    Circuit.wires ⟨a++b,0⟩ x = Circuit.wires ⟨b,0⟩ (Circuit.wires ⟨a,0⟩ x) := by
  simp [Circuit.wires,List.foldl_append]

private theorem gate_value (gs : List Gate) (i : Fin gs.length) (x : Fin 13 → Bool)
    (valid : ∀ k ∈ (gs.get i).inputs, k < 13+i.val) :
    ev gs x (13+i.val) = (gs.get i).op.eval ((gs.get i).inputs.map (ev gs x)) := by
  let pre := gs.take i.val
  let post := gs.drop (i.val+1)
  let g := gs.get i
  let w := Circuit.wires ⟨pre,0⟩ (List.ofFn x)
  have split : gs = pre ++ g :: post := by
    change gs = gs.take i.val ++ gs[i.val] :: gs.drop (i.val+1)
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have len : w.length = 13+i.val := by
    obtain ⟨ys,e,sz⟩ := wire_shape pre 0 (List.ofFn x)
    change (Circuit.wires ⟨pre,0⟩ (List.ofFn x)).length=_
    rw [e,List.length_append,List.length_ofFn,sz]
    simp [pre]
  let b := g.op.eval (g.inputs.map fun k => w.getD k false)
  have valAll : ∀ k, ev gs x k = (Circuit.wires ⟨post,0⟩ (w ++ [b])).getD k false := by
    intro k
    change (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD k false=_
    conv_lhs => rw [split,append_wires]
    rfl
  obtain ⟨ys,tail,_⟩ := wire_shape post 0 (w ++ [b])
  have valP (k : ℕ) (hk : k < w.length) : ev gs x k = w.getD k false := by
    rw [valAll,tail,List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ hk]
  have mapEq : g.inputs.map (ev gs x) = g.inputs.map (fun k => w.getD k false) :=
    List.map_congr_left (fun k hk => valP k (len.symm ▸ valid k hk))
  change ev gs x (13+i.val) = g.op.eval (g.inputs.map (ev gs x))
  rw [mapEq,valAll,tail,← len,List.getD_append _ _ _ _ (by simp)]
  change (w ++ [b]).getD w.length false=b
  simp

private theorem earlier_wire (gs : List Gate) (zs : Fin gs.length) (pos neg alt : Fin 13 → Bool)
    (base : ∀ a, pos a=true → neg a=false → alt a=true)
    (ops : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or)
    (valid : ∀ i : Fin gs.length, ∀ k ∈ (gs.get i).inputs, k < 13+i.val)
    (first : ∀ i : Fin gs.length, i<zs → (gs.get i).op=GateOp.and →
      ev gs neg (13+i.val)=false → ev gs alt (13+i.val)=false → ev gs pos (13+i.val)=false)
    (w : ℕ) (before : w<13+zs.val) (on : ev gs pos w=true) (off : ev gs neg w=false) : ev gs alt w=true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hi : w<13
    · let a : Fin 13 := ⟨w,hi⟩
      exact (input_value gs a alt).trans (base a ((input_value gs a pos).symm.trans on)
        ((input_value gs a neg).symm.trans off))
    let i : Fin gs.length := ⟨w-13,by have := zs.isLt; omega⟩
    have atWire : w=13+i.val := by dsimp [i]; omega
    have earlier : i < zs := by change w-13 < zs.val; omega
    rcases ops (gs.get i) (List.get_mem _ _) with ha | ho
    · by_contra! miss
      have blocked := first i earlier ha (atWire ▸ off) (atWire ▸ Bool.eq_false_iff.mpr miss)
      rw [← atWire,on] at blocked
      contradiction
    have active (x : Fin 13 → Bool) : ev gs x w=true ↔
        ∃ k ∈ (gs.get i).inputs, ev gs x k=true := by
      rw [atWire,gate_value gs i x (valid i),ho]
      simp [GateOp.eval]
    obtain ⟨k,km,kp⟩ := (active pos).1 on
    have kn : ev gs neg k=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have := (active neg).2 ⟨k,km,h⟩
      simp [off] at this
    have kw : k<w := atWire ▸ valid i k km
    exact (active alt).2 ⟨k,km,ih k kw (kw.trans before) kp kn⟩

end PEqualNP.Outside.L_meta_1578
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1578

theorem PEqualNP.Outside.L_meta_1578 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  intro L lines gs zs u v l m mono well hl hm hand inputs z0 zl zm pos earliest
  have Leq : L = line := funext lines
  subst L
  have valid (i : Fin gs.length) := (well i).2
  have evAnd (x : Fin 13 → Bool) :
      ev gs x (13+zs.val) = (ev gs x u && ev gs x v) := by
    rw [gate_value gs zs x (valid zs),hand,inputs]
    simp [GateOp.eval]
  have n3 : (fun a : Fin 13 => decide (a=3 ∨ ((3=3 ∨ 3=9) ∧ a ∉ line 0))) = added 3 := by
    funext a
    simp [added]
  have n9 : (fun a : Fin 13 => decide (a=9 ∨ ((9=3 ∨ 9=9) ∧ a ∉ line 0))) = added 9 := by
    funext a
    simp [added]
  rw [n3,n9] at pos
  have active : ev gs (added 3) (13+zs.val)=true ∨ ev gs (added 9) (13+zs.val)=true := by
    exact pos
  suffices solve : ∀ p : Fin 13, p=3 ∨ p=9 → ev gs (added p) (13+zs.val)=true → _ by
    rcases active with h | h
    · exact solve 3 (.inl rfl) h
    · exact solve 9 (.inr rfl) h
  intro p hp live
  have sep (w : ℕ) (mem : w ∈ (gs.get zs).inputs) (on : ev gs (added p) w=true)
      (off : ev gs (offLine 0) w=false) (t : Fin 13) (ht : eligible t) : ev gs (offLine t) w=true := by
    apply earlier_wire gs zs (added p) (offLine 0) (offLine t) ((primary t ht).2 p hp)
      (fun g hg => (mono g hg).1) valid _ w (valid zs w mem) on off
    intro i hi op z0' zt
    have both := earliest i hi op z0' t (primary t ht).1 zt
    rw [n3,n9] at both
    rcases hp with rfl | rfl
    · exact both.1
    · exact both.2
  rw [evAnd,Bool.and_eq_true] at live
  change ev gs (offLine 0) (13+zs.val)=false at z0
  change ev gs (offLine l) (13+zs.val)=false at zl
  change ev gs (offLine m) (13+zs.val)=false at zm
  rw [evAnd] at z0 zl zm
  have su := sep u (by rw [inputs]; simp) live.1
  have sv := sep v (by rw [inputs]; simp) live.2
  change (ev gs (offLine l) u=false ∧ ev gs (offLine m) u=false ∧ ev gs (offLine 0) u=true ∧ ev gs (offLine 0) v=false ∧ ev gs (offLine l) v=true ∧ ev gs (offLine m) v=true) ∨
    (ev gs (offLine l) v=false ∧ ev gs (offLine m) v=false ∧ ev gs (offLine 0) v=true ∧ ev gs (offLine 0) u=false ∧ ev gs (offLine l) u=true ∧ ev gs (offLine m) u=true)
  by_cases uu : ev gs (offLine 0) u=true
  · have vv : ev gs (offLine 0) v=false := by simpa [uu] using z0
    have vl := sv vv l (.inl hl)
    have vm := sv vv m (.inr hm)
    exact .inl ⟨by simpa [vl] using zl,by simpa [vm] using zm,uu,vv,vl,vm⟩
  · have u0 := Bool.eq_false_iff.mpr uu
    have ul := su u0 l (.inl hl)
    have um := su u0 m (.inr hm)
    have vl : ev gs (offLine l) v=false := by simpa [ul] using zl
    have vm : ev gs (offLine m) v=false := by simpa [um] using zm
    have v0 : ev gs (offLine 0) v=true := by
      by_contra! off
      have := sv (Bool.eq_false_iff.mpr off) l (.inl hl)
      simp [vl] at this
    exact .inr ⟨vl,vm,v0,u0,ul,um⟩
