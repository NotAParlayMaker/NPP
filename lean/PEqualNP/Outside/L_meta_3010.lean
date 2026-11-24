import Mathlib
import PEqualNP.Defs

namespace Canonical3010
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init_seed (n : ℕ) (σ : Fin n → Fin n) (x : Fin n → Bool) (b : Bool) :
    Rel n n σ (List.ofFn (x ∘ σ) ++ [b]) (List.ofFn x ++ [b]) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  unfold wmap
  split
  · rename_i hi
    have hx : (σ ⟨i, hi⟩).val < (List.ofFn x).length := by simp
    have ho : i < (List.ofFn (x ∘ σ)).length := by simpa using hi
    rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ ho,
      List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ ho]
    simp only [List.getElem_ofFn, Function.comp_apply]
  · rename_i hi
    have he : i - n + n = i := by omega
    have hle : n ≤ i := by omega
    rw [he, List.getD_append_right _ _ _ _ (by simpa using hle),
      List.getD_append_right _ _ _ _ (by simpa using hle)]
    simp only [List.length_ofFn]


open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem appendMatched (n : ℕ) (σ : Fin n → Fin n) (u v : List Bool)
    (h : Rel n n σ u v) (b : Bool) : Rel n n σ (u ++ [b]) (v ++ [b]) := by
  cases b
  · simpa [step, relGate, GateOp.eval] using rel_step n n σ u v ⟨.or, []⟩ h
  · simpa [step, relGate, GateOp.eval] using rel_step n n σ u v ⟨.and, []⟩ h

/-- The extension fixes wire 14, which contains the first gate's value. -/
def extend (σ : Equiv.Perm (Fin 14)) : Equiv.Perm (Fin 15) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] theorem extend_raw (σ : Equiv.Perm (Fin 14)) (i : Fin 14) :
    extend σ (Fin.castAdd 1 i) = Fin.castAdd 1 (σ i) := by
  let e : Fin 14 ⊕ Fin 1 ≃ Fin 15 := finSumFinEquiv
  change e (Sum.map σ id (e.symm (e (Sum.inl i)))) = e (Sum.inl (σ i))
  rw [e.symm_apply_apply]
  rfl

@[simp] theorem extend_last (σ : Equiv.Perm (Fin 14)) (i : Fin 1) :
    extend σ (Fin.natAdd 14 i) = Fin.natAdd 14 i := by
  let e : Fin 14 ⊕ Fin 1 ≃ Fin 15 := finSumFinEquiv
  change e (Sum.map σ id (e.symm (e (Sum.inr i)))) = e (Sum.inr i)
  rw [e.symm_apply_apply]
  rfl

theorem extend_val (σ : Equiv.Perm (Fin 14)) (i : Fin (14 + 1)) :
    (extend σ i).val = if i.val < 14 then (σ (Fin.ofNat 14 i.val)).val else 14 := by
  induction i using Fin.addCases with
  | left i => simp [i.isLt]
  | right i => simp

theorem wmap_extend (σ : Equiv.Perm (Fin 14)) (i : Fin (14 + 1)) :
    wmap 14 14 σ i.val = (extend σ i).val := by
  induction i using Fin.addCases with
  | left i =>
    have hi : (Fin.castAdd 1 i).val < 14 := i.isLt
    rw [wmap, dite_eq_left hi, extend_raw]
    rfl
  | right i =>
    have hi : ¬(Fin.natAdd 14 i).val < 14 := by simp
    rw [wmap, dite_eq_right hi, extend_last]
    have hv : (Fin.natAdd 14 i).val = 14 + i.val := rfl
    omega

def sorted {α : Type*} [LinearOrder α] (a b : α) : α × α :=
  if a ≤ b then (a,b) else (b,a)

theorem sorted_lt {α : Type*} [LinearOrder α] {a b : α} (ne : a ≠ b) :
    (sorted a b).1 < (sorted a b).2 := by
  by_cases h : a ≤ b
  · simpa [sorted, h] using lt_of_le_of_ne h ne
  · simpa [sorted, h] using lt_of_not_ge h

def key (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

theorem sorted_key {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → ℕ) (g : β → ℕ) (a b : α) (c d : β) :
    key (f (sorted a b).1) (f (sorted a b).2) (g (sorted c d).1) (g (sorted c d).2) =
      key (f a) (f b) (g c) (g d) := by
  by_cases hab : a ≤ b <;> by_cases hcd : c ≤ d <;>
    simp [sorted, key, hab, hcd, min_comm, max_comm]

def good (op : GateOp) : Prop := op = GateOp.and ∨ op = GateOp.or

theorem sorted_eval {α : Type*} [LinearOrder α] (op : GateOp) (hop : good op)
    (f : α → Bool) (a b : α) :
    op.eval [f (sorted a b).1, f (sorted a b).2] = op.eval [f a,f b] := by
  by_cases h : a ≤ b
  · simp [sorted, h]
  simp only [sorted, h, ite_false]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

def supplied (a b : Fin 14) (c d : Fin 15) (o₁ o₂ : GateOp) (x : Fin 14 → Bool) : List Bool :=
  let w := List.ofFn x ++ [o₁.eval [x a,x b]]
  w ++ [o₂.eval [w.getD c.val false,w.getD d.val false]]

structure Representation (F : (Fin 14 → Bool) → Bool) where
  a : Fin 14
  b : Fin 14
  c : Fin 15
  d : Fin 15
  firstOp : GateOp
  secondOp : GateOp
  suffix : Circuit
  firstOrdered : a < b
  secondOrdered : c < d
  firstGood : good firstOp
  secondGood : good secondOp
  monotone : Monotone2 suffix
  budget : suffix.size ≤ 24
  correct : ∀ x : Fin 14 → Bool, suffix.eval (supplied a b c d firstOp secondOp x) = F x

def Representation.score {F : (Fin 14 → Bool) → Bool} (R : Representation F) : ℕ :=
  key R.a.val R.b.val R.c.val R.d.val

theorem start {F : (Fin 14 → Bool) → Bool} (C : Circuit) (ao : IsAO2 14 C)
    (nodup : ∀ g ∈ C.gates, g.inputs.Nodup) (lo : 2 ≤ C.size) (hi : C.size ≤ 26)
    (computes : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = F x) :
    Nonempty (Representation F) := by
  obtain ⟨g0,g1,tail,shape⟩ : ∃ g0 g1 tail, C.gates = g0 :: g1 :: tail := by
    change 2 ≤ C.gates.length at lo
    cases h : C.gates with
    | nil => simp [h] at lo
    | cons g0 rest =>
      cases rest with
      | nil => simp [h] at lo
      | cons g1 tail => exact ⟨g0,g1,tail,rfl⟩
  have m0 : g0 ∈ C.gates := by simp [shape]
  have m1 : g1 ∈ C.gates := by simp [shape]
  have k0 : good g0.op := ao.1 g0 m0
  have k1 : good g1.op := ao.1 g1 m1
  obtain ⟨a,b,h0⟩ := List.length_eq_two.mp (ao.2.2 g0 m0)
  obtain ⟨c,d,h1⟩ := List.length_eq_two.mp (ao.2.2 g1 m1)
  have rawA : a < 14 := by
    apply ao.2.1 0 (by simp [shape])
    change a ∈ (C.gates.getD 0 ⟨.or, []⟩).inputs
    simp [shape,h0]
  have rawB : b < 14 := by
    apply ao.2.1 0 (by simp [shape])
    change b ∈ (C.gates.getD 0 ⟨.or, []⟩).inputs
    simp [shape,h0]
  have rawC : c < 15 := by
    apply ao.2.1 1 (by simp [shape])
    change c ∈ (C.gates.getD 1 ⟨.or, []⟩).inputs
    simp [shape,h1]
  have rawD : d < 15 := by
    apply ao.2.1 1 (by simp [shape])
    change d ∈ (C.gates.getD 1 ⟨.or, []⟩).inputs
    simp [shape,h1]
  let a' : Fin 14 := ⟨a,rawA⟩
  let b' : Fin 14 := ⟨b,rawB⟩
  let c' : Fin 15 := ⟨c,rawC⟩
  let d' : Fin 15 := ⟨d,rawD⟩
  have ab : a' ≠ b' := by
    have ne : a ≠ b := by simpa [h0] using nodup g0 m0
    intro eq
    exact ne (congrArg Fin.val eq)
  have cd : c' ≠ d' := by
    have ne : c ≠ d := by simpa [h1] using nodup g1 m1
    intro eq
    exact ne (congrArg Fin.val eq)
  let p := sorted a' b'
  let q := sorted c' d'
  let D : Circuit := ⟨tail,C.output⟩
  refine ⟨⟨p.1,p.2,q.1,q.2,g0.op,g1.op,D,sorted_lt ab,sorted_lt cd,
    k0,k1,?_,?_,?_⟩⟩
  · intro g hg
    have hg' : g ∈ C.gates := by
      rw [shape]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)
    exact ⟨ao.1 g hg', (ao.2.2 g hg').le⟩
  · change C.gates.length ≤ 26 at hi
    rw [shape] at hi
    change tail.length ≤ 24
    simp only [List.length_cons] at hi
    omega
  · intro x
    have getRaw (i : Fin 14) : (List.ofFn x).getD i.val false = x i := by
      have h : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
      rw [List.getD_eq_getElem _ _ h, List.getElem_ofFn]
    have firstStep : step (List.ofFn x) g0 =
        List.ofFn x ++ [g0.op.eval [x p.1,x p.2]] := by
      unfold step
      rw [h0, sorted_eval g0.op k0 x a' b']
      change List.ofFn x ++ [g0.op.eval
        [(List.ofFn x).getD a'.val false,(List.ofFn x).getD b'.val false]] = _
      rw [getRaw,getRaw]
    have secondStep (w : List Bool) :
        step w g1 = w ++ [g1.op.eval [w.getD q.1.val false,w.getD q.2.val false]] := by
      unfold step
      rw [h1, sorted_eval g1.op k1 (fun i : Fin 15 => w.getD i.val false) c' d']
      rfl
    have h := computes x
    unfold Circuit.eval Circuit.wires at h
    rw [shape] at h
    change (tail.foldl step (step (step (List.ofFn x) g0) g1)).getD C.output false = F x at h
    rw [firstStep,secondStep] at h
    exact h

theorem move {F : (Fin 14 → Bool) → Bool} (R : Representation F)
    (σ : Equiv.Perm (Fin 14)) (invariant : ∀ x : Fin 14 → Bool, F (x ∘ σ) = F x) :
    ∃ S : Representation F,
      S.score = key (σ R.a).val (σ R.b).val (extend σ R.c).val (extend σ R.d).val := by
  let p := sorted (σ R.a) (σ R.b)
  let q := sorted (extend σ R.c) (extend σ R.d)
  let D := relabel 14 14 σ R.suffix
  have firstNe : σ R.a ≠ σ R.b := fun h => R.firstOrdered.ne (σ.injective h)
  have secondNe : extend σ R.c ≠ extend σ R.d :=
    fun h => R.secondOrdered.ne ((extend σ).injective h)
  have hm : Monotone2 D := by
    intro g hg
    change g ∈ R.suffix.gates.map (relGate 14 14 σ) at hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    simpa only [relGate,List.length_map] using R.monotone g' hg'
  have hs : D.size = R.suffix.size := List.length_map (relGate 14 14 σ)
  let S : Representation F :=
    ⟨p.1,p.2,q.1,q.2,R.firstOp,R.secondOp,D,sorted_lt firstNe,sorted_lt secondNe,
      R.firstGood,R.secondGood,hm,hs.le.trans R.budget,?_⟩
  · exact ⟨S, sorted_key Fin.val Fin.val _ _ _ _⟩
  · intro x
    let y := x ∘ σ
    let oldFirst := R.firstOp.eval [y R.a,y R.b]
    let newFirst := R.firstOp.eval [x p.1,x p.2]
    have firstEq : newFirst = oldFirst := sorted_eval R.firstOp R.firstGood x _ _
    let u := List.ofFn y ++ [oldFirst]
    let v := List.ofFn x ++ [newFirst]
    have related : Rel 14 14 σ u v := by
      change Rel 14 14 σ (List.ofFn y ++ [oldFirst]) (List.ofFn x ++ [newFirst])
      rw [firstEq]
      exact rel_init_seed 14 σ x oldFirst
    have preserved (i : Fin 15) : v.getD (extend σ i).val false = u.getD i.val false := by
      rw [← wmap_extend]
      exact related.2.2 i.val
    let oldSecond := R.secondOp.eval [u.getD R.c.val false,u.getD R.d.val false]
    let newSecond := R.secondOp.eval [v.getD q.1.val false,v.getD q.2.val false]
    have secondEq : newSecond = oldSecond := by
      change R.secondOp.eval [v.getD q.1.val false,v.getD q.2.val false] = _
      rw [sorted_eval R.secondOp R.secondGood (fun i : Fin 15 => v.getD i.val false)
        (extend σ R.c) (extend σ R.d), preserved R.c, preserved R.d]
    have finalRel : Rel 14 14 σ (u ++ [oldSecond]) (v ++ [newSecond]) := by
      rw [secondEq]
      exact appendMatched 14 σ u v related oldSecond
    have sim := (rel_fold 14 14 σ R.suffix.gates _ _ finalRel).2.2 R.suffix.output
    exact sim.trans ((R.correct y).trans (invariant x))

end Canonical3010

open Canonical3010 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_3010 :
    ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro F C ao distinct lower upper computes
  obtain ⟨S⟩ := start C ao distinct lower upper computes
  let possible (k : ℕ) := ∃ R : Representation F, R.score = k
  have feasible : ∃ k, possible k := ⟨S.score,S,rfl⟩
  obtain ⟨R, chosen⟩ := Nat.find_spec feasible
  refine ⟨R.a,R.b,R.c,R.d,R.firstOp,R.secondOp,R.suffix,
    R.firstOrdered,R.secondOrdered,R.firstGood,R.secondGood,?_,R.monotone,R.budget,R.correct⟩
  intro σ invariant
  obtain ⟨T,hs⟩ := move R σ invariant
  have best := Nat.find_min' feasible (show possible T.score from ⟨T,rfl⟩)
  change R.score ≤ key (σ R.a).val (σ R.b).val
    (if R.c.val < 14 then (σ (Fin.ofNat 14 R.c.val)).val else 14)
    (if R.d.val < 14 then (σ (Fin.ofNat 14 R.d.val)).val else 14)
  rw [← extend_val, ← extend_val, chosen, ← hs]
  exact best
