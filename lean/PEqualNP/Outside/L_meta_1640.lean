import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1640
open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

private abbrev ev (gs : List Gate) (x : Fin n → Bool) (w : ℕ) := Circuit.eval ⟨gs,w⟩ (List.ofFn x)

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

private theorem input_value (gs : List Gate) (k : Fin n) (x : Fin n → Bool) :
    Circuit.eval ⟨gs,k.val⟩ (List.ofFn x) = x k := by
  obtain ⟨ys,h,_⟩ := wire_shape gs k.val (List.ofFn x)
  rw [Circuit.eval,h,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using k.isLt),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
  rw [List.getElem_ofFn]


private theorem append_wires (a b : List Gate) (x : List Bool) :
    Circuit.wires ⟨a++b,0⟩ x = Circuit.wires ⟨b,0⟩ (Circuit.wires ⟨a,0⟩ x) := by
  simp [Circuit.wires,List.foldl_append]

private theorem gate_value (gs : List Gate) (i : Fin gs.length) (x : Fin n → Bool)
    (valid : ∀ k ∈ (gs.get i).inputs, k < n+i.val) :
    ev gs x (n+i.val) = (gs.get i).op.eval ((gs.get i).inputs.map (ev gs x)) := by
  let pre := gs.take i.val
  let post := gs.drop (i.val+1)
  let g := gs.get i
  let w := Circuit.wires ⟨pre,0⟩ (List.ofFn x)
  have split : gs = pre ++ g :: post := by
    change gs = gs.take i.val ++ gs[i.val] :: gs.drop (i.val+1)
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have len : w.length = n+i.val := by
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
  change ev gs x (n+i.val) = g.op.eval (g.inputs.map (ev gs x))
  rw [mapEq,valAll,tail,← len,List.getD_append _ _ _ _ (by simp)]
  change (w ++ [b]).getD w.length false=b
  simp


private def orBelow (n : ℕ) (gs : List Gate) (w p : ℕ) := ∀ S : Set ℕ, w ∈ S →
  (∀ i : Fin gs.length, n+i.val ∈ S → (gs.get i).op=GateOp.or → ∀ e ∈ (gs.get i).inputs, e ∈ S) → p ∈ S

private def crosses (gs : List Gate) (x : Fin n → Bool) (ys : Fin n → Fin n → Bool)
    (R : Finset (Fin n)) (i : Fin gs.length) :=
  (gs.get i).op=GateOp.and ∧ ev gs x (n+i.val)=false ∧ ∃ p ∈ R, ev gs (ys p) (n+i.val)=true

private theorem trace (gs : List Gate) (ch : Fin gs.length → ℕ)
    (legal : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or)
    (valid : ∀ i : Fin gs.length, ∀ k ∈ (gs.get i).inputs, k < n+i.val)
    (x : Fin n → Bool) (ys : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (choose : ∀ i, crosses gs x ys R i → ch i ∈ (gs.get i).inputs ∧ ev gs x (ch i)=false)
    (r : Fin n) (hr : r ∈ R) (unique : ∀ k, x k=false → ys r k=true → k=r)
    (w : ℕ) (off : ev gs x w=false) (on : ev gs (ys r) w=true) :
    orBelow n gs w r ∨ ∃ i, crosses gs x ys R i ∧ orBelow n gs (ch i) r := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w<n
    · let k : Fin n := ⟨w,input⟩
      have eq := unique k ((input_value gs k x).symm.trans off) ((input_value gs k (ys r)).symm.trans on)
      exact .inl (fun S hw _ => (congrArg Fin.val eq) ▸ hw)
    have bound : w<n+gs.length := by
      by_contra! outside
      obtain ⟨tail,shape,len⟩ := wire_shape gs w (List.ofFn (ys r))
      change (Circuit.wires ⟨gs,w⟩ _).getD w false=true at on
      rw [shape,List.getD_eq_default _ _ (by simpa only [List.length_append,List.length_ofFn,len] using outside)] at on
      contradiction
    let i : Fin gs.length := ⟨w-n,by omega⟩
    have eq : w=n+i.val := by dsimp [i]; omega
    rcases legal (gs.get i) (List.get_mem _ _) with hand | hor
    · have live : crosses gs x ys R i := ⟨hand,eq ▸ off,r,hr,eq ▸ on⟩
      obtain ⟨hm,hx⟩ := choose i live
      have all : ∀ k ∈ (gs.get i).inputs, ev gs (ys r) k=true := by
        have e := eq ▸ on
        change ev gs (ys r) (n+i.val)=true at e
        rw [gate_value gs i _ (valid i),hand] at e
        simpa [GateOp.eval] using e
      rcases ih (ch i) (eq ▸ valid i _ hm) hx (all _ hm) with h | h
      · exact .inr ⟨i,live,h⟩
      · exact .inr h
    · have anyInput (z : Fin n → Bool) : ev gs z w=true ↔
          ∃ k ∈ (gs.get i).inputs, ev gs z k=true := by
        rw [eq,gate_value gs i _ (valid i),hor]
        simp [GateOp.eval]
      obtain ⟨k,hk,kon⟩ := (anyInput _).1 on
      have koff : ev gs x k=false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have on' := (anyInput x).2 ⟨k,hk,h⟩
        simp [off] at on'
      rcases ih k (eq ▸ valid i k hk) koff kon with found | found
      · exact .inl (fun S hw closed => found S (closed i (eq ▸ hw) hor k hk) closed)
      · exact .inr found

end PEqualNP.Outside.L_meta_1640
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1640

theorem PEqualNP.Outside.L_meta_1640 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true)) := by
  intro q m N L i0 T0 _ _ mq _ sizes _ _ sub msize gs o ch ops _ valid off on choose
  let R := L i0 \ T0
  let x (a : Fin N) := decide (a ∉ L i0)
  let ys (r a : Fin N) := decide (a ∉ L i0 ∨ a=r)
  constructor
  · intro r hr
    apply trace gs ch (fun g hg => (ops g hg).1) valid x ys R choose r hr _ o off (on r hr)
    intro a hx ha
    have inside : a ∈ L i0 := by simpa [x] using hx
    simpa [ys,inside] using ha
  · intro a hout ha
    have count : R.card = q+1-m := by
      change (L i0 \ T0).card=_
      rw [Finset.card_sdiff_of_subset sub,sizes i0,msize]
    have exist : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨r,hr⟩ := exist
    exact ⟨ha,hout ▸ off,r,hr,hout ▸ on r hr⟩
