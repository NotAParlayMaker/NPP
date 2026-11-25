import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12308_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenSignedSlice

abbrev Signal (α : Type) := α → Bool
def inv {α} (a : Signal α) : Signal α := fun x => !(a x)
def meet {α} (a b : Signal α) : Signal α := fun x => a x && b x

-- A pool stores both polarities of every paid AND. Old wires remain available.
inductive Run {α : Type} (start : List (Signal α)) : ℕ → List (Signal α) → Prop where
  | nil : Run start 0 start
  | gate {k w} (h : Run start k w) {a b} (ha : a ∈ w) (hb : b ∈ w) :
      Run start (k+1) (w ++ [meet a b, inv (meet a b)])

theorem Run.keep {α} {s w : List (Signal α)} {k} (h : Run s k w) :
    ∀ v ∈ s, v ∈ w := by
  induction h with
  | nil => exact fun _ h => h
  | gate h _ _ ih => exact fun v hv => List.mem_append_left _ (ih v hv)

theorem Run.comp {α} {s w u : List (Signal α)} {k j} (h : Run s k w) (h' : Run w j u) :
    Run s (k+j) u := by
  induction h' with
  | nil => exact h
  | gate h' ha hb ih => exact Run.gate ih ha hb

structure Wire (α : Type) where
  f : Signal α
  lo : Bool
  hi : Bool

def K {α} (b : Bool) : Wire α := ⟨fun _ => b,b,b⟩
def neg {α} (a : Wire α) : Wire α := ⟨inv a.f,!a.lo,!a.hi⟩
def conj {α} (a b : Wire α) : Wire α := ⟨meet a.f b.f,a.lo && b.lo,a.hi && b.hi⟩
def disj {α} (a b : Wire α) : Wire α := neg (conj (neg a) (neg b))

def Good {α} (w : List (Signal α)) (a : Wire α) : Prop := a.f ∈ w ∧ inv a.f ∈ w
def Stable {α} (a : Wire α) : Prop := (∃ b, ∀ x, a.f x = b) ∨ a.lo = a.hi

theorem goodNeg {α} {w : List (Signal α)} {a} (h : Good w a) : Good w (neg a) := by
  refine ⟨h.2,?_⟩
  have eq : inv (inv a.f) = a.f := by funext x; simp [inv]
  change inv (inv a.f) ∈ w
  rw [eq]
  exact h.1

theorem stableNeg {α} {a : Wire α} (h : Stable a) : Stable (neg a) := by
  rcases h with ⟨b,hb⟩ | eq
  · exact Or.inl ⟨!b,fun x => by simp [neg,inv,hb]⟩
  · exact Or.inr (congrArg Bool.not eq)

def Eval {α} (op : GateOp) (args : List (Wire α)) : Wire α :=
  ⟨fun x => op.eval (args.map fun a => a.f x),op.eval (args.map Wire.lo),op.eval (args.map Wire.hi)⟩

def Paid (g : Gate) : ℕ :=
  if g.op.eval [false] then 0 else if g.inputs.length = 2 then 1 else 0

def Effect {α} (w : List (Signal α)) (n : ℕ) (a : Wire α) (inputs : List (Wire α)) : Prop :=
  ∃ c t, Run w c t ∧ c ≤ n ∧ Good t a ∧
    (c = n → (∀ u ∈ inputs, Stable u) → Stable a)

private theorem bin {α} (w : List (Signal α)) (base : ∀ b, Good w (K b)) (a b : Wire α)
    (ha : Good w a) (hb : Good w b) : Effect w 1 (conj a b) [a,b] := by
  classical
  by_cases ca : ∃ t, ∀ x, a.f x = t
  · obtain ⟨t,e⟩ := ca
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = b.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using hb
  by_cases cb : ∃ t, ∀ x, b.f x = t
  · obtain ⟨t,e⟩ := cb
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = a.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using ha
  · refine ⟨1,_,Run.gate Run.nil ha.1 hb.1,le_rfl,?_,?_⟩
    · exact ⟨List.mem_append_right _ (by simp [conj]),List.mem_append_right _ (by simp [conj])⟩
    · intro _ stable
      have ea := (stable a (by simp)).resolve_left ca
      have eb := (stable b (by simp)).resolve_left cb
      exact Or.inr (by simp [conj,ea,eb])

private theorem gateEffect {α} (w : List (Signal α)) (base : ∀ b, Good w (K b))
    (op : GateOp) (args : List (Wire α)) (h : ∀ a ∈ args, Good w a)
    (ok : op = .and ∨ op = .or ∨ op = .not) (sz : args.length ≤ 2) :
    Effect w (if op.eval [false] then 0 else if args.length = 2 then 1 else 0) (Eval op args) args := by
  have zero (z : Wire α) (hz : Good w z) (st : (∀ v ∈ args, Stable v) → Stable z) :
      Effect w 0 z args := ⟨0,w,.nil,le_rfl,hz,fun _ => st⟩
  rcases ok with rfl | rfl | rfl
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .and [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .and [a,b] = conj a b := by simp [Eval,GateOp.eval,conj]; rfl
        rw [eq]
        exact bin w base a b (h a (by simp)) (h b (by simp))
  · cases args with
    | nil => exact zero _ (base false) (fun _ => Or.inl ⟨false,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .or [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .or [a,b] = disj a b := by simp [Eval,GateOp.eval,disj,conj,neg]; funext x; simp [inv,meet]
        rw [eq]
        obtain ⟨c,t,r,k,g,st⟩ := bin w base (neg a) (neg b) (goodNeg (h a (by simp))) (goodNeg (h b (by simp)))
        refine ⟨c,t,r,k,goodNeg g,fun equal stable => stableNeg (st equal ?_)⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | h'
        · exact stableNeg (stable _ (by simp))
        · have hv := List.mem_singleton.mp h'
          exact hv ▸ stableNeg (stable b (by simp))
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      exact zero (neg a) (goodNeg (h a (by simp))) (fun st => stableNeg (st a (by simp)))


def step {α} (v : List (Wire α)) (g : Gate) : List (Wire α) :=
  v ++ [Eval g.op (g.inputs.map fun i => v.getD i (K false))]

theorem get_property {α} (P : α → Prop) (v : List α) (d : α) (i : ℕ)
    (hd : P d) (h : ∀ z ∈ v, P z) : P (v.getD i d) := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

theorem fold {α} (gs : List Gate) (legal : ∀ g ∈ gs,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (w : List (Signal α)) (base : ∀ b, Good w (K b)) (v : List (Wire α))
    (old : ∀ a ∈ v, Good w a) :
    ∃ k t, Run w k t ∧ k ≤ (gs.map Paid).sum ∧
      (∀ a ∈ gs.foldl step v, Good t a) ∧
      (k = (gs.map Paid).sum → (∀ a ∈ v, Stable a) → ∀ a ∈ gs.foldl step v, Stable a) := by
  induction gs generalizing w v with
  | nil => exact ⟨0,w,.nil,le_rfl,old,fun _ st => st⟩
  | cons g gs ih =>
    let args := g.inputs.map fun i => v.getD i (K false)
    have allg : ∀ z ∈ args, Good w z := by
      intro z mem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact get_property _ _ _ _ (base false) old
    have h := gateEffect w base g.op args allg (legal g (by simp)).1 (by simpa [args] using (legal g (by simp)).2)
    obtain ⟨c,t,run,cap,gnew,snew⟩ := h
    have ec : c ≤ Paid g := by simpa only [Paid,args,List.length_map] using cap
    have goodKeep {a} (ok : Good w a) : Good t a := ⟨run.keep _ ok.1,run.keep _ ok.2⟩
    have goodNext : ∀ a ∈ step v g, Good t a := by
      intro a mem
      rcases List.mem_append.mp mem with ov | nv
      · exact goodKeep (old a ov)
      · exact (List.mem_singleton.mp nv) ▸ gnew
    obtain ⟨j,u,tail,limit,done,st⟩ := ih (fun z hz => legal z (List.mem_cons_of_mem g hz))
      t (fun b => goodKeep (base b)) (step v g) goodNext
    refine ⟨c+j,u,run.comp tail,by simpa using Nat.add_le_add ec limit,done,?_⟩
    intro equal previous
    simp only [List.map_cons,List.sum_cons] at equal
    apply st (by omega)
    intro a mem
    rcases List.mem_append.mp mem with ov | nv
    · exact previous a ov
    · apply (List.mem_singleton.mp nv) ▸ snew (by simpa only [args,List.length_map,Paid] using (show c = Paid g by omega))
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact get_property _ _ _ _ (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) previous

def addPair (w : List Bool) (ij : ℕ × ℕ) : List Bool :=
  let z := w.getD ij.1 false && w.getD ij.2 false
  w ++ [z,!z]

theorem Run.program {α} {s w : List (Signal α)} {k} (r : Run s k w) :
    ∃ prog : List (ℕ × ℕ), prog.length = k ∧ ∀ x : α,
      prog.foldl addPair (s.map fun f => f x) = w.map fun f => f x := by
  induction r with
  | nil => exact ⟨[],rfl,fun _ => rfl⟩
  | @gate k w r a b ha hb ih =>
    obtain ⟨p,len,sim⟩ := ih
    obtain ⟨i,hi,ei⟩ := List.getElem_of_mem ha
    obtain ⟨j,hj,ej⟩ := List.getElem_of_mem hb
    refine ⟨p++[(i,j)],by simp [len],?_⟩
    intro x
    rw [List.foldl_append,sim]
    simp only [List.foldl_cons,List.foldl_nil,addPair,List.map_append,List.map_cons,List.map_nil]
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hj)]
    simp [List.getElem_map,ei,ej,meet,inv]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getMap {α β} (h : α → β) (v : List α) (i : ℕ) (d : α) :
    h (v.getD i d) = (v.map h).getD i (h d) := by
  simp [List.getD,List.getElem?_map,Option.getD_map]

theorem aligns {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (gs : List Gate) (v : List (Wire α)) :
    (gs.foldl step v).map h = gs.foldl boolStep (v.map h) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    simp only [step,boolStep,List.map_append,List.map_cons,List.map_nil,he,List.map_map,
      Function.comp_def,getMap h,hd]

theorem outputMap {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (C : Circuit) (v : List (Wire α)) :
    h ((C.gates.foldl step v).getD C.output (K false)) = C.eval (v.map h) := by
  rw [getMap h,hd,aligns h hd he]
  rfl


theorem compile (α : Type) (C : Circuit) (hc : FanInTwo C) (s : List (α → Bool))
    (v : List ((α → Bool) × Bool × Bool)) (constants : ∀ b : Bool, (fun _ : α => b) ∈ s)
    (pins : ∀ a ∈ v, a.1 ∈ s ∧ (fun x => !(a.1 x)) ∈ s ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2))
    (varies : ¬ ∃ b : Bool, ∀ x : α, C.eval (v.map fun a => a.1 x) = b)
    (sensitive : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2)) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length < (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
      ∀ x : α, (p.foldl (fun w ij =>
        let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) (s.map fun f => f x)).getD o false = C.eval (v.map fun a => a.1 x) := by
  let make := fun a : (α → Bool) × Bool × Bool => Wire.mk a.1 a.2.1 a.2.2
  let a := v.map make
  have base (b : Bool) : Good s (K b) := ⟨constants b,constants (!b)⟩
  have old : ∀ u ∈ a, Good s u ∧ Stable u := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hg,hn,hs⟩ := pins z hz
    exact ⟨⟨hg,hn⟩,hs⟩
  obtain ⟨k,t,run,limit,accepted,stable⟩ :=
    fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s base a (fun u hu => (old u hu).1)
  let out := (C.gates.foldl step a).getD C.output (K false)
  have values (x : α) : out.f x = C.eval (v.map fun u => u.1 x) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using
      outputMap (fun u : Wire α => u.f x) rfl (fun _ _ => rfl) C a
  have lo : out.lo = C.eval (v.map fun u => u.2.1) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.lo rfl (fun _ _ => rfl) C a
  have hi : out.hi = C.eval (v.map fun u => u.2.2) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.hi rfl (fun _ _ => rfl) C a
  have lt : k < (C.gates.map Paid).sum := by
    by_contra! ge
    have eq := Nat.le_antisymm limit ge
    have impossible : Stable out := get_property _ _ _ _
      (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) (stable eq (fun u hu => (old u hu).2))
    rcases impossible with ⟨b,h⟩ | e
    · exact varies ⟨b,fun x => (values x).symm.trans (h x)⟩
    · exact sensitive (lo.symm.trans (e.trans hi))
  have zero : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have usable : Good t out := get_property _ _ _ _ zero accepted
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact lt,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  exact values x

end PetersenSignedSlice

namespace ThresholdReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) := Nat.testBit (4276676840 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.or, [1,2]⟩,
  ⟨.and, [1,2]⟩,
  ⟨.and, [0,7]⟩,
  ⟨.or, [0,6]⟩,
  ⟨.and, [0,6]⟩,
  ⟨.or, [7,10]⟩,
  ⟨.and, [3,4]⟩,
  ⟨.and, [5,11]⟩,
  ⟨.and, [9,12]⟩,
  ⟨.or, [13,14]⟩,
  ⟨.or, [8,15]⟩], 16⟩
theorem size : witness.size = 11 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
theorem value : ∀ x, circuitFun 6 witness x = target x := by decide +kernel

abbrev Input := Fin 5 → Bool
def slot : Fin 6 → Nat := ![0, 1, 2, 5, 3, 4]
def held : Fin 6 → Bool := ![false, false, false, true, false, false]
def lift (x : Input) (j : Fin 6) : Bool := if h : slot j < 5 then x ⟨slot j,h⟩ else held j
def sliceTarget (x : Input) := target (lift x)
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- A five-input restriction gives the signed binary lower bound. The two explicit sensitivity rows certify that the restriction removes a binary gate.
theorem pinSlice (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = sliceTarget x := by
  let raw := List.ofFn (fun j : Fin 5 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let pin := fun j : Fin 6 => (fun x : Input => lift x j, Nat.testBit 17 j.val, Nat.testBit 25 j.val)
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    by_cases h : slot j < 5
    · let i : Fin 5 := ⟨slot j,h⟩
      have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      have neg : (fun x : Input => !(x i)) ∈ pool := List.mem_append_right _ (List.mem_map_of_mem pos)
      have both : (fun x : Input => x i) ∈ pool := List.mem_append_left _ (List.mem_append_right _ pos)
      have stable : ∀ j : Fin 6, slot j < 5 → Nat.testBit 17 j.val = Nat.testBit 25 j.val := by decide +kernel
      refine ⟨?_,?_,Or.inr (stable j h)⟩
      · simpa [pin,lift,h,i] using both
      · simpa [pin,lift,h,i] using neg
    · refine ⟨?_,?_,Or.inl ⟨held j,fun x => ?_⟩⟩
      · simpa [pin,lift,h] using constants (held j)
      · simpa [pin,lift,h] using constants (!(held j))
      · simp [pin,lift,h]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = sliceTarget x := by
    simpa [v, pin, sliceTarget, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : sliceTarget (fun _ => false) ≠ sliceTarget (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => Nat.testBit 17 j.val)
    have b := hit (fun j => Nat.testBit 25 j.val)
    simp only [v,pin,List.map_ofFn,Function.comp_def,circuitFun] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = sliceTarget x
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

theorem replacement
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 9 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 6 D x = target x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, hit⟩
  · obtain ⟨p,o,sz,ev⟩ := pinSlice C ok hit
    have paid (gs : List Gate) : (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
        ((gs.map PetersenSignedSlice.Paid).sum = gs.length →
          ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) →
            (g.op = .and ∨ g.op = .or)) := by
      induction gs with
      | nil => simp
      | cons g t ih =>
        have cap : PetersenSignedSlice.Paid g ≤ 1 := by unfold PetersenSignedSlice.Paid; split <;> (first | decide | split <;> decide)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro eq u mem kind
        rcases List.mem_cons.mp mem with rfl | tail
        · rcases kind with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have := ih.1
            simp [PetersenSignedSlice.Paid, h, GateOp.eval] at eq
            omega
        · exact ih.2 (by omega) _ tail kind
    obtain ⟨cap, full⟩ := paid C.gates
    have strict : (C.gates.map PetersenSignedSlice.Paid).sum < C.gates.length := by
      by_contra! fail
      apply mono
      intro g hg
      exact ⟨full (by omega) _ hg (ok g hg).1, (ok g hg).2⟩
    have := sliceLower p o ev
    exact ⟨witness, legal, by rw [size]; change 11 ≤ C.gates.length; omega, value⟩

end ThresholdReplacement

namespace SignedFrontier

abbrev W := BitVec 64

def canonical (w : W) : W := if w.getLsbD 0 then ~~~w else w

def choices (a b : W) : List W :=
  [a &&& b, a &&& ~~~b, ~~~a &&& b, a ||| b]

theorem canonical_not (w : W) : canonical (~~~w) = canonical w := by
  cases h : w.getLsbD 0 <;> simp_all [canonical, BitVec.not_not]

theorem canonical_bit (w : W) : (canonical w).getLsbD 0 = false := by
  unfold canonical
  split <;> simp_all

theorem operation (a b : W) :
    canonical (a &&& b) ∈ choices (canonical a) (canonical b) := by
  cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
    simp_all [choices, canonical, BitVec.not_and, BitVec.not_not]

theorem constants (a b : W) (h : a = 0 ∨ b = 0 ∨ a = b) :
    ∀ w ∈ choices a b, w = 0 ∨ w = a ∨ w = b := by
  rcases h with rfl | rfl | rfl <;> simp [choices]
  · exact Or.inr BitVec.allOnes_and
  · exact Or.inr (Or.inl BitVec.and_allOnes)

-- Read the live gates backwards from the single required output. The two
-- operands can belong to the suffix already when a wire is shared.
inductive Cone (goal : W) : ℕ → Finset W → Prop where
  | done : Cone goal 0 {goal}
  | step {k : ℕ} {needed : Finset W} {a b w : W}
      (rest : Cone goal k needed) (wanted : w ∈ needed)
      (a0 : a ≠ 0) (b0 : b ≠ 0) (ab : a ≠ b) (aw : a ≠ w) (bw : b ≠ w)
      (form : w ∈ choices a b) :
      Cone goal (k+1) (insert a (insert b (needed.erase w)))

theorem Cone.size {goal : W} {k : ℕ} {s : Finset W} (h : Cone goal k s) :
    s.card ≤ k+1 := by
  induction h with
  | done => simp
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    have e := Finset.card_erase_of_mem wanted
    have hn := Finset.card_pos.mpr ⟨w,wanted⟩
    have p := Finset.card_insert_le b (needed.erase w)
    have q := Finset.card_insert_le a (insert b (needed.erase w))
    omega

def add (ws : List W) (ij : ℕ × ℕ) : List W :=
  let w := ws.getD ij.1 0 &&& ws.getD ij.2 0
  ws ++ [w,~~~w]

def available (ws : List W) : Finset W := insert 0 (ws.map canonical).toFinset

theorem available_read (ws : List W) (i : ℕ) : canonical (ws.getD i 0) ∈ available ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp only [available, Finset.mem_insert, List.mem_toFinset, List.mem_map]
    exact Or.inr ⟨_,List.getElem_mem hi,rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [available,canonical]

theorem available_add (ws : List W) (ij : ℕ × ℕ) :
    available (add ws ij) = insert (canonical (ws.getD ij.1 0 &&& ws.getD ij.2 0)) (available ws) := by
  ext w
  simp [available,add,canonical_not]
  tauto

theorem extract (p : List (ℕ × ℕ)) (ws : List W) (g : W) (k : ℕ) (s : Finset W)
    (h : Cone g k s) (hs : s ⊆ available (p.foldl add ws)) :
    ∃ j t, j ≤ k+p.length ∧ t ⊆ available ws ∧ Cone g j t := by
  induction p generalizing ws k s with
  | nil => exact ⟨k,s,by simp,hs,h⟩
  | cons ij tail ih =>
    obtain ⟨j,t,hj,ht,hr⟩ := ih (add ws ij) k s h hs
    rw [available_add] at ht
    by_cases sub : t ⊆ available ws
    · exact ⟨j,t,by simp only [List.length_cons]; omega,sub,hr⟩
    · let a := canonical (ws.getD ij.1 0)
      let b := canonical (ws.getD ij.2 0)
      let w := canonical (ws.getD ij.1 0 &&& ws.getD ij.2 0)
      have ha : a ∈ available ws := available_read _ _
      have hb : b ∈ available ws := available_read _ _
      have hz : (0 : W) ∈ available ws := Finset.mem_insert_self ..
      have new : w ∉ available ws := by
        intro hold
        exact sub (fun z h' => (Finset.mem_insert.mp (ht h')).elim (fun e => e ▸ hold) id)
      have want : w ∈ t := by
        by_contra hn
        exact sub (fun z h' => (Finset.mem_insert.mp (ht h')).resolve_left (by rintro rfl; contradiction))
      have form : w ∈ choices a b := operation _ _
      have diff : ¬ (a = 0 ∨ b = 0 ∨ a = b) := by
        intro bad
        rcases constants a b bad w form with e | e | e <;> apply new <;> simp_all
      refine ⟨j+1,_,by simp only [List.length_cons]; omega,?_,
        Cone.step hr want (fun e => diff (Or.inl e)) (fun e => diff (Or.inr (Or.inl e)))
          (fun e => diff (Or.inr (Or.inr e))) (fun e => new (e ▸ ha)) (fun e => new (e ▸ hb)) form⟩
      intro z hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact ha
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact hb
      obtain ⟨hne,hzt⟩ := Finset.mem_erase.mp hz'
      exact (Finset.mem_insert.mp (ht hzt)).resolve_left hne

theorem Cone.noZero {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s) (hg : g ≠ 0) :
    0 ∉ s := by
  induction h with
  | done => exact fun hz => hg (Finset.mem_singleton.mp hz).symm
  | step rest wanted a0 b0 ab aw bw form ih =>
    intro hz
    rcases Finset.mem_insert.mp hz with e | hm
    · exact a0 e.symm
    rcases Finset.mem_insert.mp hm with e | hm
    · exact b0 e.symm
    exact ih (Finset.mem_of_mem_erase hm)

theorem same_choice (a b w : W) (hw : w ∈ choices a b) (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    w.getLsbD i = w.getLsbD j := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_or,hi,hj,decide_true,
      Bool.true_and,ha,hb]

theorem Cone.agree {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s)
    (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (same : ∀ u ∈ s, u.getLsbD i = u.getLsbD j) : g.getLsbD i = g.getLsbD j := by
  induction h with
  | done => exact same _ (Finset.mem_singleton_self _)
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    apply ih
    intro u hu
    by_cases h : u = w
    · subst u
      exact same_choice _ _ _ form i j hi hj (same a (by simp)) (same b (by simp))
    · exact same u (by simp [h, hu])

def rowMask (r : ℕ) (u : W) := if u.getLsbD r then u else ~~~u

def survivors (r : ℕ) : List W → W → W
  | [], mask => mask
  | a :: tail, mask =>
    if mask = 0 then 0 else survivors r tail (mask &&& rowMask r a)

theorem survivor_sound (r j : ℕ) (hj : j < 64) (s : List W) (m : W)
    (hit : (survivors r s m).getLsbD j = true) :
    m.getLsbD j = true ∧ ∀ u ∈ s, u.getLsbD r = u.getLsbD j := by
  induction s generalizing m with
  | nil => exact ⟨hit,by simp⟩
  | cons a tail ih =>
    simp only [survivors] at hit
    split at hit
    · simp at hit
    · obtain ⟨head,rest⟩ := ih _ hit
      simp only [BitVec.getLsbD_and,Bool.and_eq_true] at head
      refine ⟨head.1,?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | h
      · have v := head.2
        unfold rowMask at v
        cases h : u.getLsbD r <;> simp_all
      · exact rest u h

def covered (g : W) (rows : List ℕ) (s : List W) :=
  rows.all fun r => survivors r s g == 0

theorem Cone.covered {g : W} {k : ℕ} {s : List W} (h : Cone g k s.toFinset)
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false) :
    covered g rows s = true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨limit,off⟩ := neg r hr
  cases hv : (survivors r s g).getLsbD j with
  | false => simp
  | true =>
    obtain ⟨on,same⟩ := survivor_sound r j hj s g hv
    have eq := h.agree r j limit hj (by simpa using same)
    simp [off,on] at eq

def withWire (keep : Bool) (a : W) (s : List W) := if keep then a :: s else s

theorem mem_withWire {u a : W} {s : List W} (keep : Bool) :
    u ∈ withWire keep a s ↔ (keep = true ∧ u = a) ∨ u ∈ s := by
  cases keep <;> simp [withWire]

def after (s : List W) (a b w : W) (ka kb : Bool) : List W :=
  w :: withWire ka a (withWire kb b (s.filter fun u => u != a && u != b))

theorem after_exact (s : List W) (needed : Finset W) (a b w : W)
    (hs : s.toFinset = insert a (insert b (needed.erase w))) (want : w ∈ needed) :
    (after s a b w (decide (a ∈ needed)) (decide (b ∈ needed))).toFinset = needed := by
  ext u
  have mem : u ∈ s ↔ u = a ∨ u = b ∨ u ≠ w ∧ u ∈ needed := by
    rw [← List.mem_toFinset,hs]
    simp
  simp only [List.mem_toFinset,after,List.mem_cons,mem_withWire,decide_eq_true_eq,
    List.mem_filter,Bool.and_eq_true,bne_iff_ne,mem]
  grind

def onePair (s : List W) (f : List W → Bool) (a b : W) :=
  (choices a b).any fun w => w != 0 && !s.contains w &&
    ([false,true] : List Bool).any fun ka => ([false,true] : List Bool).any fun kb =>
      f (after s a b w ka kb)

def moves (s : List W) (f : List W → Bool) :=
  s.any fun a => s.any fun b => decide (a.toNat < b.toNat) && onePair s f a b

theorem swap_choices {a b w : W} : w ∈ choices a b → w ∈ choices b a := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false]
  intro h
  rcases h with rfl | rfl | rfl | rfl <;> simp [BitVec.and_comm,BitVec.or_comm]

theorem after_nodup (s : List W) (hs : s.Nodup) (a b w : W) (ka kb : Bool)
    (diff : a ≠ b) (fresh : w ∉ s) (aw : a ≠ w) (bw : b ≠ w) :
    (after s a b w ka kb).Nodup := by
  have base := hs.filter (fun u => u != a && u != b)
  have ha : a ∉ s.filter (fun u => u != a && u != b) := by simp
  have hb : b ∉ s.filter (fun u => u != a && u != b) := by simp
  have hw : w ∉ s.filter (fun u => u != a && u != b) := by simp [fresh]
  cases ka <;> cases kb <;> simp [after,withWire,base,fresh,Ne.symm aw,Ne.symm bw,diff]

theorem onePair_complete (s : List W) (f : List W → Bool)
    {g a b w : W} {k : ℕ} {needed : Finset W} (hg : g ≠ 0)
    (unique : s.Nodup) (ab : a ≠ b) (rest : Cone g k needed) (want : w ∈ needed)
    (hs : s.toFinset = insert a (insert b (needed.erase w)))
    (aw : a ≠ w) (bw : b ≠ w) (form : w ∈ choices a b)
    (succ : ∀ t : List W, t.Nodup → Cone g k t.toFinset → f t = true) :
    onePair s f a b = true := by
  have nz : w ≠ 0 := fun e => rest.noZero hg (e ▸ want)
  have fresh : w ∉ s := by
    rw [← List.mem_toFinset,hs]
    simp [Ne.symm aw,Ne.symm bw]
  apply List.any_eq_true.mpr
  refine ⟨w,form,?_⟩
  simp only [bne_iff_ne.mpr nz,List.contains_eq_mem,decide_eq_false fresh,
    Bool.not_false,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (a ∈ needed),by cases decide (a ∈ needed) <;> simp,?_⟩
  apply List.any_eq_true.mpr
  refine ⟨decide (b ∈ needed),by cases decide (b ∈ needed) <;> simp,?_⟩
  exact succ _ (after_nodup s unique a b w _ _ ab fresh aw bw) ((after_exact s needed a b w hs want).symm ▸ rest)

theorem moves_complete (s : List W) (f : List W → Bool)
    {g : W} {k : ℕ} {state : Finset W} (hg : g ≠ 0)
    (unique : s.Nodup) (h : Cone g (k+1) state) (eq : s.toFinset = state)
    (succ : ∀ t : List W, t.Nodup → Cone g k t.toFinset → f t = true) :
    moves s f = true := by
  cases h with
  | @step _ needed a b w rest want a0 b0 ab aw bw form =>
    have ha : a ∈ s := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_self ..)
    have hb : b ∈ s := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    apply List.any_eq_true.mpr
    have distinct : a.toNat ≠ b.toNat := fun e => ab (BitVec.eq_of_toNat_eq e)
    rcases lt_or_gt_of_ne distinct with lt | gt
    · refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
      simp only [lt,decide_true,Bool.true_and]
      exact onePair_complete s f hg unique ab rest want eq aw bw form succ
    · refine ⟨b,hb,List.any_eq_true.mpr ⟨a,ha,?_⟩⟩
      simp only [gt,decide_true,Bool.true_and]
      rw [Finset.insert_comm] at eq
      exact onePair_complete s f hg unique ab.symm rest want eq bw aw (swap_choices form) succ

def feasible (g : W) (rows : List ℕ) : ℕ → List W → Bool
  | 0, s => s.contains g
  | k+1, s => s.contains g ||
    (decide (s.length ≤ k+2) && covered g rows s &&
      moves s (feasible g rows k))

theorem feasible_complete {g : W} (hg : g ≠ 0) (rows : List ℕ)
    (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false)
    (cap : ℕ) (s : List W) (unique : s.Nodup) (k : ℕ) (bound : k ≤ cap) (h : Cone g k s.toFinset) :
    feasible g rows cap s = true := by
  induction cap generalizing k s with
  | zero =>
    have hz : k = 0 := by omega
    subst k
    have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
    simpa [feasible] using final h
  | succ cap ih =>
    simp only [feasible,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    cases k with
    | zero =>
      left
      have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
      simpa using final h
    | succ k =>
      right
      refine ⟨⟨by have sz := h.size; rw [List.toFinset_card_of_nodup unique] at sz; omega,h.covered rows neg⟩,?_⟩
      exact moves_complete _ _ hg unique h rfl (fun t nd ht => ih t nd k (by omega) ht)

def Essential (g : W) (raws : List W) :=
  ∀ w ∈ raws, ∃ i j : Fin 64, g.getLsbD i.val ≠ g.getLsbD j.val ∧
    ∀ v ∈ raws, v ≠ w → v.getLsbD i.val = v.getLsbD j.val

theorem Cone.initial {g : W} (hg : g ≠ 0) (raws : List W) (ess : Essential g raws)
    {k : ℕ} {s : Finset W} (h : Cone g k s) (sub : s ⊆ insert 0 raws.toFinset) :
    s = raws.toFinset := by
  have contained : s ⊆ raws.toFinset := by
    intro z hz
    exact (Finset.mem_insert.mp (sub hz)).resolve_left (fun e => h.noZero hg (e ▸ hz))
  apply Finset.Subset.antisymm contained
  intro w hw
  by_contra missing
  obtain ⟨i,j,diff,others⟩ := ess w (List.mem_toFinset.mp hw)
  exact diff (h.agree _ _ i.isLt j.isLt (fun u hu =>
    others u (List.mem_toFinset.mp (contained hu)) (fun e => missing (e ▸ hu))))

def evaluate (p : List (ℕ × ℕ)) (ws : List W) (o : ℕ) : W := (p.foldl add ws).getD o 0

theorem from_check (g : W) (hg : g ≠ 0) (raws ws : List W) (unique : raws.Nodup) (start : available ws = insert 0 raws.toFinset)
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false) (ess : Essential g raws)
    (cap : ℕ) (checked : feasible g rows cap raws = false) (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : canonical (evaluate p ws o) = g) : cap < p.length := by
  by_contra! short
  have sub : {g} ⊆ available (p.foldl add ws) := by
    apply Finset.singleton_subset_iff.mpr
    rw [← hit]
    exact available_read _ _
  obtain ⟨k,s,bound,inside,run⟩ := extract p ws g 0 {g} Cone.done sub
  rw [start] at inside
  have eq := run.initial hg raws ess inside
  rw [eq] at run
  have possible := feasible_complete hg rows neg cap raws unique k (by omega) run
  simp [checked] at possible

-- A mask selects the low positions and the matching high positions of a swap.
structure Switch where
  distance : ℕ
  low : W
  high : W

def Switch.source (s : Switch) (r : ℕ) :=
  if s.low.getLsbD r then s.distance + r else if s.high.getLsbD r then r-s.distance else r

def Switch.apply (s : Switch) (w : W) : W :=
  (w &&& ~~~(s.low ||| s.high)) ||| ((w >>> s.distance) &&& s.low) |||
    ((w <<< s.distance) &&& s.high)

def Switch.Valid (s : Switch) :=
  ∀ r : Fin 64, ¬ (s.low.getLsbD r.val = true ∧ s.high.getLsbD r.val = true) ∧
    (s.high.getLsbD r.val = true → s.distance ≤ r.val) ∧
    s.source r.val < 64 ∧ s.source (s.source r.val) = r.val

theorem Switch.read (s : Switch) (ok : s.Valid) (w : W) (r : ℕ) (hr : r < 64) :
    (s.apply w).getLsbD r = w.getLsbD (s.source r) := by
  obtain ⟨disj,lower,_,_⟩ := ok ⟨r,hr⟩
  change ¬ (s.low.getLsbD r = true ∧ s.high.getLsbD r = true) at disj
  change s.high.getLsbD r = true → s.distance ≤ r at lower
  simp only [Switch.apply, BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,hr,decide_true,Bool.true_and,Switch.source]
  cases a : s.low.getLsbD r <;> cases b : s.high.getLsbD r <;> simp_all

theorem Switch.inj (s : Switch) (ok : s.Valid) : Function.Injective s.apply := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  obtain ⟨_,_,lim,inv⟩ := ok ⟨r,hr⟩
  have e := congrArg (fun u : W => u.getLsbD (s.source r)) h
  simpa only [s.read ok _ _ lim, inv] using e

theorem Switch.not (s : Switch) (ok : s.Valid) (w : W) : s.apply (~~~w) = ~~~(s.apply w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bound := (ok ⟨i,hi⟩).2.2.1
  simp only [s.read ok _ _ hi,BitVec.getLsbD_not,hi,bound,decide_true,Bool.true_and]

theorem Switch.and (s : Switch) (ok : s.Valid) (a b : W) :
    s.apply (a &&& b) = s.apply a &&& s.apply b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [s.read ok _ _ hi,BitVec.getLsbD_and]

theorem Switch.or (s : Switch) (ok : s.Valid) (a b : W) :
    s.apply (a ||| b) = s.apply a ||| s.apply b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [s.read ok _ _ hi,BitVec.getLsbD_or]

theorem Cone.switched {g : W} {k : ℕ} {xs : Finset W} (h : Cone g k xs) (s : Switch) (ok : s.Valid) :
    Cone (s.apply g) k (xs.image s.apply) := by
  have zero : s.apply 0 = 0 := by simp [Switch.apply]
  have inj := s.inj ok
  induction h with
  | done => simpa using (Cone.done (goal := s.apply g))
  | @step k ys a b w rest want a0 b0 ab aw bw form ih =>
    have wanted : s.apply w ∈ ys.image s.apply := Finset.mem_image_of_mem _ want
    have erase : (ys.erase w).image s.apply = (ys.image s.apply).erase (s.apply w) := by
      ext x
      simp only [Finset.mem_image,Finset.mem_erase]
      constructor
      · rintro ⟨v,⟨hne,mem⟩,rfl⟩
        exact ⟨fun e => hne (inj e),v,mem,rfl⟩
      · rintro ⟨hne,v,mem,rfl⟩
        exact ⟨v,⟨fun e => hne (congrArg _ e),mem⟩,rfl⟩
    have operate : s.apply w ∈ choices (s.apply a) (s.apply b) := by
      simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at form ⊢
      rcases form with rfl | rfl | rfl | rfl <;> simp [s.and ok,s.or ok,s.not ok]
    simp only [Finset.image_insert,erase]
    exact Cone.step ih wanted (fun e => a0 (inj (e.trans zero.symm)))
      (fun e => b0 (inj (e.trans zero.symm))) (fun e => ab (inj e))
      (fun e => aw (inj e)) (fun e => bw (inj e)) operate

def reindex : List Switch → W → W
  | [], w => w
  | s :: tail, w => reindex tail (s.apply w)

theorem Cone.reindex {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s) (ops : List Switch)
    (ok : ∀ op ∈ ops, op.Valid) :
    Cone (reindex ops g) k (s.image (reindex ops)) := by
  induction ops generalizing s g with
  | nil => simpa [SignedFrontier.reindex] using h
  | cons op tail ih =>
    have step := h.switched op (ok _ List.mem_cons_self)
    have result := ih step (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    simpa only [SignedFrontier.reindex,Finset.image_image,Function.comp_def] using result

def found (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) (k : ℕ) (s : List W) :=
  let (i,j) := lookup k s
  decide (i < count k) && (s.map (reindex (sym j))).isPerm (words k i)

def closed (g : W) (negative : List ℕ) (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) : ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    !s.contains g && !(moves s fun t =>
      t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) && covered g negative t &&
        !found words count lookup sym k t))

theorem closed_excludes (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 64 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, closed g negative words count lookup sym k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simpa [closed,mem] using checks 0 hk i hi
  | succ k ih =>
    intro hk i hi d hd run
    obtain ⟨absent,reject⟩ := Bool.and_eq_true_iff.mp (checks (k+1) hk i hi)
    cases d with
    | zero =>
      have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
      have mem := List.mem_toFinset.mp (terminal run)
      simp [mem] at absent
    | succ d =>
      let test := fun t : List W => t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) &&
        covered g negative t && !found words count lookup sym k t)
      have next := moves_complete (words (k+1) i) test hg (nd _ hk _ hi) run rfl (fun t uniq ht => by
        dsimp only [test]
        by_cases mem : g ∈ t
        · simp [mem]
        have positive : 0 < k := by
          by_contra! fail
          have dz : d = 0 := by omega
          subst d
          have terminal {u : Finset W} (p : Cone g 0 u) : g ∈ u := by cases p; simp
          exact mem (List.mem_toFinset.mp (terminal ht))
        have size := ht.size
        rw [List.toFinset_card_of_nodup uniq] at size
        have no : found words count lookup sym k t = false := by
          by_contra! yes
          have hfound : found words count lookup sym k t = true := by simpa using yes
          obtain ⟨inside,perm⟩ := Bool.and_eq_true_iff.mp hfound
          have hree := ht.reindex (sym (lookup k t).2) (valid _)
          rw [fix] at hree
          have eq : (t.map (reindex (sym (lookup k t).2))).toFinset = (words k (lookup k t).1).toFinset := by
            ext v
            simp only [List.mem_toFinset]
            exact (List.isPerm_iff.mp perm).mem_iff
          have into : t.toFinset.image (reindex (sym (lookup k t).2)) = (words k (lookup k t).1).toFinset := by
            rw [← eq]
            ext v
            simp
          rw [into] at hree
          exact ih (by omega) _ (of_decide_eq_true inside) d (by omega) hree
        simp [positive,show t.length ≤ k+1 by omega,ht.covered negative neg,no])
      change (!moves (words (k+1) i) test) = true at reject
      simp [next] at reject

end SignedFrontier

namespace SignedFrontier.Packed

-- These packed integers only propose a negative input row. Every proposed
-- obstruction is tested on the original signals before a successor is skipped.
structure Columns where
  w : W
  pos : Nat
  neg : Nat

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
def equalRows (p : Columns) : Nat := fullLanes ^^^ (p.pos ^^^ p.neg)
def bothCols (a b : Columns) : Columns := ⟨a.w &&& b.w, a.pos &&& b.pos, a.neg &&& b.neg⟩
def notCols (a : Columns) : Columns := ⟨~~~a.w, fullLanes ^^^ a.pos, fullLanes ^^^ a.neg⟩
def orCols (a b : Columns) : Columns := ⟨a.w ||| b.w, a.pos ||| b.pos, a.neg ||| b.neg⟩
def variants (a b : Columns) : List Columns :=
  [bothCols a b,bothCols a (notCols b),bothCols (notCols a) b,orCols a b]

end SignedFrontier.Packed


namespace SignedFrontier.Vector
open SignedFrontier.Packed (Columns bothCols orCols notCols variants equalRows fullLanes)

-- Each successive 64-bit lane corresponds to one negative input row.
def lanes (rows : List Nat) (f : Nat → W) : Nat :=
  match rows with
  | [] => 0
  | r :: rs => (f r).toNat ||| (lanes rs f <<< 64)

theorem lane_bit (rows : List Nat) (f : Nat → W) (i j : Nat) (hj : j < 64) :
    (lanes rows f).testBit (64*i+j) =
      match rows[i]? with | some r => (f r).getLsbD j | none => false := by
  induction rows generalizing i with
  | nil => simp [lanes]
  | cons r rs ih =>
    cases i with
    | zero => simp [lanes,BitVec.getLsbD, Nat.not_le.mpr hj]
    | succ i =>
      have bound : 64 ≤ 64*(i+1)+j := by omega
      have sub : 64*(i+1)+j-64 = 64*i+j := by omega
      have off : (f r).toNat.testBit (64*(i+1)+j) = false := by
        change (f r).getLsbD (64*(i+1)+j) = false
        simp [BitVec.getLsbD_of_ge, bound]
      simpa only [lanes,Nat.testBit_or,Nat.testBit_shiftLeft,off,bound,decide_true,
        Bool.true_and,Bool.false_or,sub,List.getElem?_cons_succ] using ih i

def negativeLane (w : W) (r : Nat) : W := if w.getLsbD r then ~~~0 else 0

def coefficient : Nat → Nat
  | 0 => 0
  | n+1 => 2^64 * coefficient n + 1

theorem constant_lanes (rows : List Nat) (w : W) :
    lanes rows (fun _ => w) = w.toNat * coefficient rows.length := by
  induction rows with
  | nil => simp [lanes,coefficient]
  | cons r rs ih =>
    simp only [lanes,List.length_cons,coefficient,ih]
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt w.isLt, Nat.shiftLeft_eq]
    ring

def columns (rows : List Nat) (w : W) : Columns :=
  ⟨w, Packed.positions w, lanes rows (negativeLane w)⟩

def Valid (rows : List Nat) (c : Columns) : Prop :=
  ∀ i j r, j < 64 → rows[i]? = some r →
    c.pos.testBit (64*i+j) = c.w.getLsbD j ∧ c.neg.testBit (64*i+j) = c.w.getLsbD r

theorem columns_valid (rows : List Nat) (length : rows.length = 13) (w : W) : Valid rows (columns rows w) := by
  intro i j r hj hr
  have fast : Packed.positions w = lanes rows (fun _ => w) := by
    rw [constant_lanes,length]
    rfl
  simp only [columns,fast,lane_bit rows _ i j hj,hr]
  cases on : w.getLsbD r
  · simp [negativeLane,on]
  · simp only [negativeLane,on,ite_true,BitVec.getLsbD_not,hj,decide_true,
      Bool.true_and]
    simp

set_option maxRecDepth 9000 in
theorem full_bit {rows : List Nat} (length : rows.length = 13) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 832 := by omega
  have val : fullLanes = 2^832-1 := by decide +kernel
  rw [val, Nat.testBit_two_pow_sub_one, decide_eq_true lt]

theorem valid_and {rows : List Nat} {a b : Columns} (ha : Valid rows a) (hb : Valid rows b) :
    Valid rows (bothCols a b) := by
  intro i j r hj hr
  obtain ⟨ap,an⟩ := ha i j r hj hr
  obtain ⟨bp,bn⟩ := hb i j r hj hr
  simp [bothCols,ap,an,bp,bn]

theorem valid_or {rows : List Nat} {a b : Columns} (ha : Valid rows a) (hb : Valid rows b) :
    Valid rows (orCols a b) := by
  intro i j r hj hr
  obtain ⟨ap,an⟩ := ha i j r hj hr
  obtain ⟨bp,bn⟩ := hb i j r hj hr
  simp [orCols,ap,an,bp,bn]

theorem valid_not {rows : List Nat} (length : rows.length = 13) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 13) (bounds : ∀ r ∈ rows, r < 64)
    {a b c : Columns} (ha : Valid rows a) (hb : Valid rows b) (hc : c ∈ variants a b) :
    Valid rows c := by
  simp only [variants,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact valid_and ha hb
  · exact valid_and ha (valid_not length bounds hb)
  · exact valid_and (valid_not length bounds ha) hb
  · exact valid_or ha hb

def Mask (g : W) (rows : List Nat) (s : List W) (m : Nat) : Prop :=
  ∀ i j, j < 64 → m.testBit (64*i+j) = true → ∃ r, rows[i]? = some r ∧
    g.getLsbD j = true ∧ ∀ u ∈ s, u.getLsbD r = u.getLsbD j

theorem initial (g : W) (rows : List Nat) : Mask g rows [] (lanes rows (fun _ => g)) := by
  intro i j hj hit
  rw [lane_bit rows _ i j hj] at hit
  cases hr : rows[i]? with
  | none => simp [hr] at hit
  | some r => exact ⟨r,rfl,by simpa [hr] using hit,by simp⟩

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 13) {s : List W}
    {m : Nat} {c : Columns} (mask : Mask g rows s m) (valid : Valid rows c) :
    Mask g rows (c.w :: s) (m &&& equalRows c) := by
  intro i j hj hit
  obtain ⟨old,added⟩ := Bool.and_eq_true_iff.mp ((Nat.testBit_and ..).symm ▸ hit)
  obtain ⟨r,hr,hg,same⟩ := mask i j hj old
  obtain ⟨ap,an⟩ := valid i j r hj hr
  have eq : c.w.getLsbD r = c.w.getLsbD j := by
    simp only [equalRows,Nat.testBit_xor,full_bit length hj hr,ap,an] at added
    cases hp : c.w.getLsbD j <;> cases hn : c.w.getLsbD r <;> simp_all
  exact ⟨r,hr,hg,fun w hw => (List.mem_cons.mp hw).elim (fun h => h ▸ eq) (same w)⟩

theorem survivor_complete (r j : Nat) (hj : j < 64) (s : List W) (m : W)
    (on : m.getLsbD j = true) (same : ∀ w ∈ s, w.getLsbD r = w.getLsbD j) :
    (survivors r s m).getLsbD j = true := by
  induction s generalizing m with
  | nil => exact on
  | cons w ws ih =>
    have ne : m ≠ 0 := by rintro rfl; simp at on
    rw [survivors,ite_eq_right ne]
    apply ih
    · have eq := same w List.mem_cons_self
      cases hv : w.getLsbD r <;> simp_all [rowMask]
    · exact fun u hu => same u (List.mem_cons_of_mem _ hu)

theorem clear {g : W} {rows : List Nat} {s : List W} {m : Nat}
    (mask : Mask g rows s m) (coveredRows : covered g rows s = true) : m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro n
  cases hn : m.testBit n with
  | false => simp
  | true =>
    have split : 64*(n/64)+n%64 = n := by omega
    obtain ⟨r,hr,hg,agree⟩ := mask (n/64) (n%64) (by omega) (split.symm ▸ hn)
    have z := beq_iff_eq.mp (List.all_eq_true.mp coveredRows r (List.mem_of_getElem? hr))
    have p := survivor_complete r (n%64) (by omega) s g hg agree
    simp [z] at p


theorem weaken {g : W} {rows : List Nat} {s t : List W} {m : Nat}
    (h : Mask g rows s m) (sub : ∀ w ∈ t, w ∈ s) : Mask g rows t m := by
  intro i j hj hm
  obtain ⟨r,hr,hg,agree⟩ := h i j hj hm
  exact ⟨r,hr,hg,fun w hw => agree w (sub w hw)⟩

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 13) (xs : List Columns)
    (ok : ∀ c ∈ xs, Valid rows c) (s : List W) (m : Nat) (h : Mask g rows s m) :
    Mask g rows (xs.map Columns.w ++ s) (xs.foldl (fun n c => n &&& equalRows c) m) := by
  induction xs generalizing s m with
  | nil => simpa using h
  | cons c cs ih =>
    have rest := ih (fun z hz => ok z (List.mem_cons_of_mem _ hz)) (c.w :: s)
      (m &&& equalRows c) (addMask length h (ok c List.mem_cons_self))
    apply weaken rest
    intro w hw
    simpa [or_assoc,or_comm,or_left_comm] using hw

def branch (_g : W) (seek : List W → Bool) (k len m : Nat) (next : List W) : Bool :=
  decide (len ≤ k) && m == 0 && !seek next

theorem branch_of {g : W} {rows : List Nat} {seek : List W → Bool} {k len m : Nat}
    {next : List W} (dims : len ≤ k) (mask : Mask g rows next m)
    (cov : covered g rows next = true) (miss : seek next = false) :
    branch g seek k len m next = true := by simp [branch,dims,clear mask cov,miss]
def packedPair (g : W) (_rows : List Nat) (seek : List W → Bool) (k : Nat)
    (initialMask : Nat) (s : List W) (t : List Columns) (a b : Columns) : Bool :=
  let cs := variants a b
  cs.any (fun c => c.w == g) ||
    let base := t.filter (fun u => u.w != a.w && u.w != b.w)
    let rest := s.filter (fun u => u != a.w && u != b.w)
    let mask := base.foldl (fun m z => m &&& equalRows z) initialMask
    let ra := equalRows a
    let rb := equalRows b
    let len := rest.length
    cs.any fun c => c.w != 0 && !s.contains c.w &&
      let m := mask &&& equalRows c
      (branch g seek k len m (c.w :: rest) ||
       branch g seek k (len + 1) (m &&& ra) (c.w :: a.w :: rest) ||
       branch g seek k (len + 1) (m &&& rb) (c.w :: b.w :: rest) ||
       branch g seek k (len + 2) (m &&& ra &&& rb) (c.w :: a.w :: b.w :: rest))

theorem pair_of (g : W) (rows : List Nat) (seek : List W → Bool) (k : Nat)
    (s : List W) (t : List Columns) (a b : Columns)
    (initialMask : Nat) (start : Mask g rows [] initialMask)
    (length : rows.length = 13) (bounds : ∀ r ∈ rows, r < 64)
    (stock : t.map Columns.w = s) (valid : ∀ z ∈ t, Valid rows z)
    (va : Valid rows a) (vb : Valid rows b)
    (ha : a.w ∈ s) (hb : b.w ∈ s) (absent : g ∉ s)
    (slow : onePair s (fun u => u.contains g || (decide (0 < k) && decide (u.length ≤ k+1)
      && covered g rows u && !seek u)) a.w b.w = true) :
    packedPair g rows seek k initialMask s t a b = true := by
  have vw : (variants a b).map Columns.w = choices a.w b.w := rfl
  obtain ⟨w,form,test⟩ := List.any_eq_true.mp slow
  obtain ⟨fresh,keeps⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨ka,_,next⟩ := List.any_eq_true.mp keeps
  obtain ⟨kb,_,ok⟩ := List.any_eq_true.mp next
  rw [←vw] at form
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp form
  unfold packedPair
  apply Bool.or_eq_true_iff.mpr
  by_cases hit : c.w = g
  · exact Or.inl (List.any_eq_true.mpr ⟨c,hc,beq_iff_eq.mpr hit⟩)
  · right
    apply List.any_eq_true.mpr
    refine ⟨c,hc,Bool.and_eq_true_iff.mpr ⟨fresh,?_⟩⟩
    have na : g ≠ a.w := fun e => absent (e ▸ ha)
    have nb : g ≠ b.w := fun e => absent (e ▸ hb)
    have stop : (after s a.w b.w c.w ka kb).contains g = false := by
      cases ka <;> cases kb <;>
        simp [after,withWire,List.contains_eq_mem,Ne.symm hit,na,nb,absent]
    dsimp only at ok
    rw [stop,Bool.false_or] at ok
    obtain ⟨first,last⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨dims,cov⟩ := Bool.and_eq_true_iff.mp first
    have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp dims).2
    have miss : seek (after s a.w b.w c.w ka kb) = false := by simpa using last
    let rest := s.filter fun u => u != a.w && u != b.w
    let base := t.filter fun u => u.w != a.w && u.w != b.w
    let m := base.foldl (fun n z => n &&& equalRows z) initialMask
    have shape : base.map Columns.w = rest := by
      change (t.filter (fun u => u.w != a.w && u.w != b.w)).map Columns.w =
        s.filter (fun u => u != a.w && u != b.w)
      rw [← stock, List.filter_map]
      rfl
    have core := foldMask length base (fun z hz => valid z (List.mem_filter.mp hz).1) [] _ start
    have trimmed : Mask g rows rest m := by simpa [shape,m] using core
    have vc := variant_valid length bounds va vb hc
    let mc := m &&& equalRows c
    have raw : Mask g rows (c.w :: rest) mc := addMask length trimmed vc
    have withA : Mask g rows (c.w :: a.w :: rest) (mc &&& equalRows a) :=
      weaken (addMask length raw va) (by simp [or_left_comm])
    have withB : Mask g rows (c.w :: b.w :: rest) (mc &&& equalRows b) :=
      weaken (addMask length raw vb) (by simp [or_left_comm])
    have withBoth : Mask g rows (c.w :: a.w :: b.w :: rest)
        (mc &&& equalRows a &&& equalRows b) :=
      weaken (addMask length withA vb) (by simp [or_left_comm])
    cases ka <;> cases kb <;>
      simp only [after,withWire,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hl cov miss
    all_goals
      simp only [Bool.or_eq_true_iff]
      first
      | exact Or.inl (Or.inl (Or.inl (branch_of (by omega) raw cov miss)))
      | exact Or.inl (Or.inl (Or.inr (branch_of (by omega) withA cov miss)))
      | exact Or.inl (Or.inr (branch_of (by omega) withB cov miss))
      | exact Or.inr (branch_of (by omega) withBoth cov miss)

def packedClosed (g : W) (rows : List Nat) (initialMask : Nat) (words : Nat → Nat → List W)
    (count : Nat → Nat) (lookup : Nat → List W → Nat × Nat) (sym : Nat → List Switch) :
    Nat → Nat → Bool
  | 0,i => !(words 0 i).contains g
  | k+1,i =>
    let s := words (k+1) i
    let t := s.map (columns rows)
    !s.contains g && !(t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
      packedPair g rows (found words count lookup sym k) k initialMask s t a b)

theorem closed_sound (g : W) (rows : List Nat) (initialMask : Nat)
    (maskSpec : initialMask = lanes rows (fun _ => g)) (words : Nat → Nat → List W)
    (count : Nat → Nat) (lookup : Nat → List W → Nat × Nat) (sym : Nat → List Switch)
    (length : rows.length = 13) (bounds : ∀ r ∈ rows, r < 64)
    (k i : Nat) (ok : packedClosed g rows initialMask words count lookup sym k i = true) :
    closed g rows words count lookup sym k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,verified⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    let s := words (k+1) i
    let t := s.map (columns rows)
    let seek := found words count lookup sym k
    have ng : g ∉ s := by simpa [s,List.contains_eq_mem] using absent
    by_contra! fail
    have h : moves s (fun u => u.contains g || (decide (0 < k) && decide (u.length ≤ k+1) &&
        covered g rows u && !seek u)) = true := by simpa [s,seek] using fail
    obtain ⟨a,ha,inner⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,both⟩ := List.any_eq_true.mp inner
    obtain ⟨lt,slow⟩ := Bool.and_eq_true_iff.mp both
    have st : t.map Columns.w = s := by simp [t,columns,List.map_map,Function.comp_def]
    have valid : ∀ z ∈ t, Valid rows z := by
      rintro z hz
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
      exact columns_valid rows length u
    have fast := pair_of g rows seek k s t (columns rows a) (columns rows b) _
      (maskSpec.symm ▸ initial g rows) length bounds st valid (columns_valid rows length a) (columns_valid rows length b)
      ha hb ng slow
    have yes : (t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
        packedPair g rows seek k initialMask s t a b) = true :=
      List.any_eq_true.mpr ⟨columns rows a,List.mem_map.mpr ⟨a,ha,rfl⟩,
        List.any_eq_true.mpr ⟨columns rows b,List.mem_map.mpr ⟨b,hb,rfl⟩,
          Bool.and_eq_true_iff.mpr ⟨lt,fast⟩⟩⟩
    change (!(t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
      packedPair g rows seek k initialMask s t a b)) = true at verified
    simp [yes] at verified

end SignedFrontier.Vector

namespace SignedFrontier.SmallCert

def span (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_member {f n o} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    intro i lo hi
    obtain ⟨first,tail⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.eq_or_lt_of_le lo with rfl | gt
    · exact first
    · exact ih tail i (by omega) (by omega)

theorem span_join {f a o b} (left : span f a o = true) (right : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using right
  | succ a ih =>
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp left
    rw [Nat.succ_add]
    exact Bool.and_eq_true_iff.mpr ⟨first,ih rest (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using right)⟩

end SignedFrontier.SmallCert

namespace SignedFrontier.SmallCert.Restricted

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfee8fe80fee8fe80
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 16, 17, 18, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨6,7,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨5,7,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨3,7,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨3,19,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x300000003000000020002000200020000fffe0000fffe0000ffee0000ffee0000ffea0000ffea0000ffcc0000ffcc0000ffaa0000ffaa0000ff880000ff880000ff0a0000ff0a0000ff000000ff000000fefe0000fefe0000feee0000feee0000fcfc0000fcfc0000fafa0000fafa0000f0f00000f0f00000efee0000efee0000eefe0000eefe0000eeee0000eeee0000eeea0000eeea0000eeaa0000eeaa0000ee000000ee000000eaee0000eaee0000eaea0000eaea0000cccc0000cccc0000afaa0000afaa0000af000000af000000aeee0000aeee0000aeae0000aeae0000aafe0000aafe0000aaee0000aaee0000aaea0000aaea0000aaaa0000aaaa0000aa880000aa880000aa0a0000aa0a0000aa000000aa000000a8fc0000a8fc0000a8a80000a8a800008a8a00008a8a000088f8000088f8000088aa000088aa00008888000088880000880000008800000080800000808000003f0000003f0000002a2a00002a2a00000f0a00000f0a00000f0000000f0000000eee00000eee00000e0e00000e0e00000afa00000afa00000aaa00000aaa00000a0a00000a0a00000a0000000a00000008080000080800000300000003000000020200000202000000fe000000fe000000ee000000ee000000ea000000ea000000cc000000cc000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xffaa0000ffaa0000ff0ff000ff0ff000ff0f0000ff0f0000ff00fe00ff00fe00ff00f000ff00f000ff00ee00ff00ee00ff00aa00ff00aa00ff008800ff008800ff008000ff008000ff000a00ff000a00ff000200ff000200ff000000ff000000fe00fe00fe00fe00fe000000fe000000fc00fc00fc00fc00f000f000f000f000f0000000f0000000ef000000ef000000eeeeee00eeeeee00ee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ea00ea00ea00ea00ea000000ea000000cc00cc00cc00cc00cc000000cc000000af00aa00af00aa00af000000af000000ae00ae00ae00ae00aaffaa00aaffaa00aaccee00aaccee00aaaaaa00aaaaaa00aa88aa00aa88aa00aa0aaa00aa0aaa00aa00ee00aa00ee00aa00aa00aa00aa00aa008800aa008800aa000a00aa000a00aa000000aa000000a800a800a800a8008a008a008a008a0088aaaa0088aaaa0088888800888888008800aa008800aa008800880088008800880000008800000080008000800080007f0000007f00000055000000550000003f0000003f0000003c003c003c003c002a002a002a002a000ffff0000ffff0000ff0f0000ff0f0000f00f0000f00f0000f000a000f000a000f0000000f0000000e000e000e000e000aaaaa000aaaaa000a0a0a000a0a0a000a00aa000a00aa000a000a000a000a000a0000000a00000008000800080008) else (if page < 3 then 0xa0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a0a08080a0a08080a0a02020a0a02020a0a000a0a0a000a0a0a00000a0a00000a080a080a080a080a020a020a020a020a00ff000a00ff000a00fafa0a00fafa0a00aaaa0a00aaaa0a00aa000a00aa000a000f000a000f000a000a0a0a000a0a0a000a000a000a000a0000000a00000008ff000008ff000008aa08aa08aa08aa0888088808880888080a080a080a080a0808aaaa0808aaaa080888880808888808080a0a08080a0a08080808080808080808000008080000080008000800080007ff000007ff000007070000070700000700070007000700050005000500050003ff030003ff030003ff000003ff000003fc03fc03fc03fc03cc03cc03cc03cc030f0000030f00000303fcfc0303fcfc03030300030303000303020203030202030300000303000003020302030203020300fffc0300fffc0300ff000300ff0003000f0003000f000300030003000300030000000300000002ff020202ff020202ff000002ff000002aaaaaa02aaaaaa02aa0aaa02aa0aaa02aa02aa02aa02aa020a020a020a020a0202fefe0202fefe0202eeee0202eeee0202aaaa0202aaaa02020a0a02020a0a02020202020202020202000002020000020002000200020001ff000001ff00000101000001010000010001000100010000ffff0000ffff0000ffaaaa00ffaaaa else 0xf00ff000f00ff000f00efee0f00efee0f00afaa0f00afaa0f00af000f00af000f003f000f003f000f000f0a0f000f0a0f000f000f000f000f000a000f000a000f0003000f0003000f0000000f0000000eff00000eff00000eee0eee0eee0eee0eee00000eee00000eaa0eaa0eaa0eaa0e0eeeee0e0eeeee0e0e0e0e0e0e0e0e0e0e0a0a0e0e0a0a0e0e00000e0e00000e0a0e0a0e0a0e0a0e00eeee0e00eeee0e000e000e000e000ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0bff00000bff00000b0b0a0a0b0b0a0a0b0b00000b0b00000b0a0b0a0b0a0b0a0b000b000b000b000aff0a0a0aff0a0a0aff0a000aff0a000aff00000aff00000afa0afa0afa0afa0afa00000afa00000ace0ace0ace0ace0aaafaaa0aaafaaa0aaaaaaa0aaaaaaa0aaa8aaa0aaa8aaa0aaa2aaa0aaa2aaa0aaa0aaa0aaa0aaa0aaa0a8a0aaa0a8a0aaa0a0a0aaa0a0a0aaa02aa0aaa02aa0aaa00aa0aaa00aa0aaa00000aaa00000a8a0a8a0a8a0a8a0a5a0a5a0a5a0a5a0a2aaaaa0a2aaaaa0a2a0aaa0a2a0aaa0a2a0a2a0a2a0a2a0a0f0a0a0a0f0a0a0a0f00000a0f00000a0e0a0e0a0e0a0e0a0aff0a0a0aff0a0a0afafa0a0afafa0a0af0f00a0af0f00a0acece0a0acece0a0aaaaa0a0aaaaa0a0aaa0a0a0aaa0a0a0a8a8a0a0a8a8a0a0a2a2a0a0a2a2a0a0a0f0a0a0a0f0a0a0a0e0e0a0a0e0e)) else (if page < 6 then (if page < 5 then 0x22aa22aa22aa22aa2222aaaa2222aaaa22222222222222221fff00001fff00001f1f00001f1f00001f00ff001f00ff001f001f001f001f001e1e1e1e1e1e1e1e1111000011110000110011001100110010f010f010f010f010101010101010100fffff000fffff000ffff0000ffff0000fff0f000fff0f000fff0aaa0fff0aaa0fff0a000fff0a000fff03000fff03000fff00f00fff00f00fff00000fff00000ff0ff000ff0ff000ff0f0f00ff0f0f00ff00ff00ff00ff00fef00000fef00000faf00aa0faf00aa0faf00000faf00000faa0faa0faa0faa0f7f00000f7f00000f3f00000f3f00000f3c0f3c0f3c0f3c0f0ffff00f0ffff00f0fff000f0fff000f0ff0f00f0ff0f00f0faaaa0f0faaaa0f0f3c3c0f0f3c3c0f0f0ff00f0f0ff00f0f0f0e0f0f0f0e0f0f0f0a0f0f0f0a0f0f0f080f0f0f080f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0b0a0f0f0b0a0f0f0a0a0f0f0a0a0f0f0a000f0f0a000f0f08080f0f08080f0f03000f0f03000f0f02020f0f02020f0f00f00f0f00f00f0f000a0f0f000a0f0f00000f0f00000f0e0f0e0f0e0f0e0f0e0f0a0f0e0f0a0f0c0f0c0f0c0f0c0f0affaa0f0affaa0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0a0a0f0a0a0a0f0a00000f0a00000f080f080f080f080f030f000f030f000f0300000f0300000f020f020f020f020f00fffa0f00fffa0f00fff00f00fff0 else 0x5500ff005500ff0055005500550055005500000055000000545454545454545450f050f050f050f05050f0f05050f0f050505050505050504ccc4ccc4ccc4ccc44cc44cc44cc44cc444444444444444444440000444400003fff3f003fff3f003fff0f003fff0f003fff0c003fff0c003fff00003fff00003fc03fc03fc03fc03f7f00003f7f00003f3fc0c03f3fc0c03f3f3f003f3f3f003f3f3c3c3f3f3c3c3f3f2a2a3f3f2a2a3f3f0c0c3f3f0c0c3f3f00003f3f00003f3c3f3c3f3c3f3c3f2a3f2a3f2a3f2a3f0f33003f0f33003f0f00003f0f00003f0c3f0c3f0c3f0c3f00ff003f00ff003f007f003f007f003f003f003f003f003f000f003f000f003f0000003f0000003e3e3e3e3e3e3e3e3cfc3cfc3cfc3cfc3ccc3ccc3ccc3ccc3c3cfcfc3c3cfcfc3c3ccccc3c3ccccc3c3c3c3c3c3c3c3c33ff000033ff0000333333223333332233330000333300003300ff003300ff00330033003300330030f030f030f030f030303030303030302fff00002fff00002f2f22222f2f22222f2f00002f2f00002f222f222f222f222f002f002f002f002eaa2eaa2eaa2eaa2e2e2e2e2e2e2e2e2aff00002aff00002aaaaaaa2aaaaaaa2aaa2aaa2aaa2aaa2aaa0aaa2aaa0aaa2a2aaaaa2a2aaaaa2a2a2aaa2a2a2aaa2a2a2a2a2a2a2a2a2a2a0a0a2a2a0a0a2a2a00002a2a00002a0a2a0a2a0a2a0a2a002a002a002a00) else (if page < 7 then 0x88aaaaaa88aaaaaa88aa88aa88aa88aa88aa888888aa888888aa00aa88aa00aa88aa000088aa000088a888a888a888a8888a888a888a888a8888ff888888ff888888f8f88888f8f88888f0f08888f0f08888cccc8888cccc8888aaaa8888aaaa8888aa888888aa888888a8a88888a8a888888a8a88888a8a888888aa888888aa888888888888888888888800888888008888808088888080888808088888080888880088888800888888000088880000888088808880888088088808880888088800ff008800ff008800aaaa8800aaaa8800aa008800aa0088008888880088888800880088008800880000008800000080ff808080ff808080ff000080ff000080aa80aa80aa80aa80888088808880888080aaaa8080aaaa80808888808088888080808080808080808000008080000080008000800080007fff00007fff00007f7f7f007f7f7f007f7f00007f7f00007f00ff007f00ff007f007f007f007f007777000077770000770077007700770070707070707070706e6e6e6e6e6e6e6e6a6a6a6a6a6a6a6a66666666666666665fff00005fff00005f5f00005f5f00005f005f005f005f005a5a5a5a5a5a5a5a55ff550055ff550055ff000055ff000055aa55aa55aa55aa5555aaaa5555aaaa555555005555550055555050555550505555444455554444555500005555000055505550555055505544554455445544 else (if page < 8 then 0xaa00eeeeaa00eeeeaa00eeccaa00eeccaa00ee00aa00ee00aa00af00aa00af00aa00aaeeaa00aaeeaa00aaaaaa00aaaaaa00aa88aa00aa88aa00aa0aaa00aa0aaa00aa00aa00aa00aa008800aa008800aa000a00aa000a00aa000000aa000000a8ff0000a8ff0000a8fca8fca8fca8fca8fc0000a8fc0000a8aaa8aaa8aaa8aaa8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a8a88888a8a88888a8a80000a8a80000a888a888a888a888a800fcfca800fcfca800a800a800a800a2aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a0f0a0f0a0f0a0f0a0aaa0aaa0aaa0aaa0a0f0f0a0a0f0f0a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a00000a0a00000a000aaaaa000aaaaa000a000a000a0009a9a9a9a9a9a9a9a99aa99aa99aa99aa9999aaaa9999aaaa9999888899998888998899889988998898989898989898988fff00008fff00008f8f88888f8f88888f8f00008f8f00008f888f888f888f888f008f008f008f008ccc8ccc8ccc8ccc8aff00008aff00008aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8aaa8a8a8aaa8a8a8aaa0aaa8aaa0aaa8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a8a8a88888a8a88888a8a0a0a8a8a0a0a8a8a00008a8a00008a888a888a888a888a0a8a0a8a0a8a0a8a008a008a008a0088ff888888ff888888ff880088ff880088ff000088ff000088f888f888f888f888f8000088f80000 else 0xaaaaafaaaaaaafaaaaaaaeaeaaaaaeaeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa8aaaaaaa8aaaaaaa88aaaaaa88aaaaaa80aaaaaa80aaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaaa8a8aaaaa8a8aaaaa0a0aaaaa0a0aaaa8aaaaaaa8aaaaaaa8a8aaaaa8a8aaaaa8a88aaaa8a88aaaa88aaaaaa88aaaaaa8888aaaa8888aaaa8800aaaa8800aaaa8080aaaa8080aaaa5a5aaaaa5a5aaaaa55aaaaaa55aaaaaa4444aaaa4444aaaa2aaaaaaa2aaaaaaa2a2aaaaa2a2aaaaa2222aaaa2222aaaa0aaaaaaa0aaaaaaa0a8aaaaa0a8aaaaa0a0aaaaa0a0aaaaa0a00aaaa0a00aaaa0808aaaa0808aaaa02aaaaaa02aaaaaa0202aaaa0202aaaa00aaaaaa00aaaaaa0088aaaa0088aaaa000aaaaa000aaaaa0000aaaa0000aaa8aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa0aaa0aaa0aaa0aa8aaa8aaa8aaa8aaa88ffccaa88ffccaa88aaaaaa88aaaaaa88aa88aa88aa88aa88aa00aa88aa00aa888888aa888888aa880000aa880000aa80aa80aa80aa80aa5aaa5aaa5aaa5aaa55ff00aa55ff00aa55aaaaaa55aaaaaa2aaaaaaa2aaaaaaa2aaa2aaa2aaa2aaa22aa22aa22aa22aa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0aaa00aa0aaa00aa0a0a0aaa0a0a0aaa0a0000aa0a0000aa08aa08aa08aa08aa02aa02aa02aa02aa00ff00aa00ff00aa00fefcaa00fefc)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0xafaa0f00afaa0f00afaa0000afaa0000afa0afa0afa0afa0af8caf8caf8caf8caf50af50af50af50af0faa00af0faa00af0f0000af0f0000af00ff00af00ff00af00af00af00af00af00aa00af00aa00af000f00af000f00af000000af000000aeff0000aeff0000aeeeaeeeaeeeaeeeaeee0000aeee0000aeccaeccaeccaeccaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaaaaaeae0c0caeae0c0caeae0000aeae0000aeaaaeaaaeaaaeaaae0cae0cae0cae0cae00ae00ae00ae00acccacccacccacccacacacacacacacacabff0000abff0000ababaaaaababaaaaabab0000abab0000abaaabaaabaaabaaab00ab00ab00ab00aaffff00aaffff00aaffaaeeaaffaaeeaaffaaaaaaffaaaaaaffaa00aaffaa00aaff88ccaaff88ccaaff8800aaff8800aaff5500aaff5500aaff0a00aaff0a00aaff0000aaff0000aafeaafeaafeaafeaafe0000aafe0000aaef0000aaef0000aaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaeeaa00aaeeaa00aaee00ccaaee00ccaaee0000aaee0000aaeaaaeaaaeaaaeaaaea0000aaea0000aaccaaccaaccaaccaaafaaaaaaafaaaaaaaf0000aaaf0000aaaeaaaeaaaeaaaeaaaaffeeaaaaffeeaaaaffaaaaaaffaaaaaaff00aaaaff00aaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaeeaaaaaaeeaaaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaac0c0aaaac0c0 else 0xccccfcfcccccfcfcccccfcccccccfccccccceeeecccceeeecccceecccccceeccccccdcdcccccdcdccccccececccccececccccccccccccccccccccc8ccccccc8ccccccc88cccccc88cccccc80cccccc80cccccc00cccccc00ccccc4c4ccccc4c4ccccaaaaccccaaaacccc8c8ccccc8c8ccccc8c88cccc8c88cccc8888cccc8888cccc44cccccc44cccccc4444cccc4444cccc0ccccccc0ccccccc0c0ccccc0c0ccccc0000cccc0000ccc8ccc8ccc8ccc8cc44cc44cc44cc44cc00cccccc00cccccc00cc00cc00cc00c4ccc4ccc4ccc4ccc4c4c4c4c4c4c4c4c444c444c444c444c0ffc000c0ffc000c0ff0000c0ff0000c0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0c00000c0c00000c000c000c000c000bfff0000bfff0000bfbfaaaabfbfaaaabfbf0000bfbf0000bfaabfaabfaabfaabf00ff00bf00ff00bf00bf00bf00bf00bbaabbaabbaabbaab0b0b0b0b0b0b0b0afffaf00afffaf00afffaaaaafffaaaaafffaa00afffaa00afffa000afffa000afff0f00afff0f00afff0500afff0500afff0000afff0000aff0aff0aff0aff0afef0000afef0000afafafaaafafafaaafafaf00afafaf00afafaeaeafafaeaeafafaaaaafafaaaaafafa0a0afafa0a0afaf8c8cafaf8c8cafaf5050afaf5050afaf0000afaf0000afaeafaeafaeafaeafaaffaaafaaffaaafaaafaaafaaafaaafaaaaaaafaaaaaa) else (if page < 12 then 0xeeee2200eeee2200eeee0e0eeeee0e0eeeee0e00eeee0e00eeee0606eeee0606eeee0202eeee0202eeee00eeeeee00eeeeee0000eeee0000eeeaeeeaeeeaeeeaeeea0000eeea0000eee0eee0eee0eee0eecceecceecceecceecccccceecccccceeaeeeaeeeaeeeaeeeaaffaaeeaaffaaeeaaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaeeaa0000eeaa0000ee66ee66ee66ee66ee44ee44ee44ee44ee22ee22ee22ee22ee0eee0eee0eee0eee00ff00ee00ff00ee00eeeeee00eeeeee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ececececececececececccccececcccceccceccceccceccceaff0000eaff0000eaeeeaeeeaeeeaeeeaee0000eaee0000eaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaeaea00eaeaea00eaeac0c0eaeac0c0eaeaaaaaeaeaaaaaeaea0000eaea0000eac0eac0eac0eac0eaaaeaaaeaaaeaaaea00eaeaea00eaeaea00ea00ea00ea00e6e6e6e6e6e6e6e6e0e0e0e0e0e0e0e0ddff0000ddff0000dddd0000dddd0000ddccddccddccddccdd00dd00dd00dd00dcccdcccdcccdcccd0d0d0d0d0d0d0d0cfff0000cfff0000cfcf0000cfcf0000cfcccfcccfcccfcccfc0cfc0cfc0cfc0ceeeceeeceeeceeeceee0000ceee0000cecececececececececcceccceccceccccff0000ccff0000cceecceecceecceeccee0000ccee0000ccccffccccccffcc else 0xf0f0faf2f0f0faf2f0f0faf0f0f0faf0f0f0f8f0f0f0f8f0f0f0f2f2f0f0f2f2f0f0f2f0f0f0f2f0f0f0f0f2f0f0f0f2f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0c0f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f0b0b0f0f0b0b0f0f0a0a0f0f0a0a0f0f05050f0f05050f0f03030f0f03030f0f010f0f0f010f0f0f01010f0f01010f0f000f0f0f000f0f0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f050f050f050f050f000ff00f000ff00f000f0f0f000f0f0f000f000f000f000f0000000f0000000efff0000efff0000efefef00efefef00efefeeeeefefeeeeefefaaaaefefaaaaefef0000efef0000efeeefeeefeeefeeefee0f00efee0f00efee0000efee0000efe0efe0efe0efe0efaaefaaefaaefaaef00ef00ef00ef00eeffeeeeeeffeeeeeeffee00eeffee00eeffcccceeffcccceeffaaaaeeffaaaaeeffaa00eeffaa00eeff2200eeff2200eeff0000eeff0000eefeeefeeefeeefeeefe0000eefe0000eeef0000eeef0000eeeeffeeeeeeffeeeeeeff00eeeeff00eeeefefeeeeefefeeeeeeeeeeeeeeeeeeeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeeeaeaeeeeeaeaeeeee0e0eeeee0e0eeeee000eeeee000eeeecccceeeecccceeeeaeaeeeeeaeaeeeeeaaeeeeeeaaeeeeeeaaaaeeeeaaaaeeeeaa00eeeeaa00eeee6666eeee6666eeee6600eeee6600eeee2222eeee2222)) else (if page < 15 then (if page < 14 then 0xfcfc5400fcfc5400fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfcccccccfcccccccfcc0fcc0fcc0fcc0fc3cfc3cfc3cfc3cfc00fc00fc00fc00faff0000faff0000fafafafafafafafafafafa00fafafa00fafaf0f0fafaf0f0fafa0000fafa0000faf8faf0faf8faf0faf8f0f0faf8f0f0faf0fef0faf0fef0faf0faf2faf0faf2faf0faf0faf0faf0faf0f8f0faf0f8f0faf0f2f0faf0f2f0faf0f0f0faf0f0f0faf050f0faf050f0faf00000faf00000faaafaaafaaafaaafa5afa5afa5afa5afa0afa0afa0afa0afa00fafafa00fafafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f0f8f8f8f0f8f8f0f0f8f8f0f0f8f80000f8f80000f8f0faf0f8f0faf0f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f5ff0000f5ff0000f5f50000f5f50000f5f0f5f0f5f0f5f0f5a0f5a0f5a0f5a0f5550000f5550000f500f500f500f500f4f0f4f0f4f0f4f0f3ff0000f3ff0000f3f3f0f0f3f3f0f0f3f30000f3f30000f3f0f3f0f3f0f3f0f300f300f300f300f2f2f2f2f2f2f2f2f2f0faf0f2f0faf0f2f0f2f2f2f0f2f2f2f0f2f0f2f0f2f0f2f0f0f0f2f0f0f0f0fff0f0f0fff0f0f0fff000f0fff000f0ff0000f0ff0000f0faf0faf0faf0faf0f8f0f0f0f8f0f0f0f1f0f0f0f1f0f0f0f0fff0f0f0fff0f0f0ff00f0f0ff00f0f0fefef0f0fefef0f0fef0f0f0fef0f0f0fcfcf0f0fcfcf0f0fafaf0f0fafa else 0xff0aff00ff0aff00ff0a0a0aff0a0a0aff0a0000ff0a0000ff08ff08ff08ff08ff08ff00ff08ff00ff03ff00ff03ff00ff030000ff030000ff02ff02ff02ff02ff01ff00ff01ff00ff00fffeff00fffeff00fff0ff00fff0ff00ffeeff00ffeeff00ffeaff00ffeaff00ffccff00ffccff00ffaaff00ffaaff00ff88ff00ff88ff00ff80ff00ff80ff00ff0aff00ff0aff00ff00ff00ff00ff00fe00ff00fe00ff00f000ff00f000ff00eeeeff00eeeeff00ee00ff00ee00ff00af00ff00af00ff00aaaaff00aaaaff00aa00ff00aa00ff008800ff008800ff007f00ff007f00ff005500ff005500ff003f00ff003f00ff001100ff001100ff000ff0ff000ff0ff000f00ff000f00ff000a00ff000a00ff000300ff000300ff000000ff000000feff0000feff0000fefefefefefefefefefefe00fefefe00fefef0f0fefef0f0fefeeeeefefeeeeefefeaaaafefeaaaafefe0202fefe0202fefe0000fefe0000fefcfefcfefcfefcfefc0000fefc0000fef0fef0fef0fef0fef0faf0fef0faf0fef0f0f0fef0f0f0feeefeeefeeefeeefeeef000feeef000feee0000feee0000feccfeccfeccfeccfeaafeaafeaafeaafe0efe0efe0efe0efe00ff00fe00ff00fe00fefefe00fefefe00fe00fe00fe00fdfd0000fdfd0000fcff0000fcff0000fcfcfcfcfcfcfcfcfcfcfcccfcfcfcccfcfcfc00fcfcfc00fcfcf0f0fcfcf0f0) else (if page < 16 then 0xffee1100ffee1100ffee0000ffee0000ffeaffeaffeaffeaffeaff00ffeaff00ffea0000ffea0000ffe0ff00ffe0ff00ffccffccffccffccffccff00ffccff00ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff80ffc0ff80ffc0ff00ffc0ff00ffc0c0c0ffc0c0c0ffafffaaffafffaaffafff00ffafff00ffafaaaaffafaaaaffaf0000ffaf0000ffaeffaeffaeffaeffaaffeeffaaffeeffaaffaaffaaffaaffaaff88ffaaff88ffaaff0affaaff0affaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaafaaffaaafaaffaaaaaaffaaaaaaffaa5500ffaa5500ffaa0f0affaa0f0affaa00aaffaa00aaffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa8ff00ffa8ff00ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ff8aff8aff8aff8aff88ffaaff88ffaaff88ff88ff88ff88ff88ff80ff88ff80ff88ff00ff88ff00ff888888ff888888ff880000ff880000ff80ff80ff80ff80ff80ff00ff80ff00ff7fff00ff7fff00ff7f0000ff7f0000ff55ff00ff55ff00ff550000ff550000ff50ff50ff50ff50ff3fff00ff3fff00ff3f0000ff3f0000ff3cff3cff3cff3cff2aff2aff2aff2aff0ffff0ff0ffff0ff0fff0aff0fff0aff0fff00ff0fff00ff0ff0f0ff0ff0f0ff0ff000ff0ff000ff0faa0aff0faa0aff0f00f0ff0f00f0ff0f0000ff0f0000ff0eff0eff0eff0eff0affaaff0affaaff0aff0aff0aff0a else (if page < 17 then 0xffff8080ffff8080ffff8000ffff8000ffff7f00ffff7f00ffff7700ffff7700ffff5500ffff5500ffff5000ffff5000ffff3f00ffff3f00ffff3300ffff3300ffff3030ffff3030ffff3000ffff3000ffff2f00ffff2f00ffff2a2affff2a2affff2a00ffff2a00ffff2200ffff2200ffff1f00ffff1f00ffff1100ffff1100ffff1010ffff1010ffff0f0affff0f0affff0f02ffff0f02ffff0f00ffff0f00ffff0e0effff0e0effff0e00ffff0e00ffff0c0cffff0c0cffff0b00ffff0b00ffff0aaaffff0aaaffff0a0affff0a0affff0a02ffff0a02ffff0a00ffff0a00ffff0808ffff0808ffff0800ffff0800ffff0700ffff0700ffff0500ffff0500ffff0302ffff0302ffff0300ffff0300ffff0202ffff0202ffff0200ffff0200ffff0100ffff0100ffff00eeffff00eeffff00aaffff00aaffff0088ffff0088ffff0080ffff0080ffff000affff000affff0002ffff0002ffff0000ffff0000fffefffefffefffefffeff00fffeff00fffe0000fffe0000fffcfffcfffcfffcfffcff00fffcff00fffc0000fffc0000fffafffafffafffafffa0000fffa0000fff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0fff00000fff00000ffefff00ffefff00ffef0000ffef0000ffeeffeeffeeffeeffeeffaaffeeffaaffeeff00ffeeff00ffeeeeeeffeeeeeeffeeaaaaffeeaaaaffee3300ffee3300 else 0xfffffff0fffffff0ffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffff88ffffff88ffffff80ffffff80ffffff0affffff0affffff02ffffff02ffffff00ffffff00fffffefefffffefefffffe00fffffe00fffffc00fffffc00fffffafafffffafafffffaf0fffffaf0fffffa00fffffa00fffff500fffff500fffff0f0fffff0f0fffff000fffff000ffffef00ffffef00ffffeeeeffffeeeeffffeeccffffeeccffffeeaaffffeeaaffffee00ffffee00ffffeaeaffffeaeaffffea00ffffea00ffffccccffffccccffffcc00ffffcc00ffffc0c0ffffc0c0ffffc000ffffc000ffffbf00ffffbf00ffffafaaffffafaaffffaf00ffffaf00ffffaeaeffffaeaeffffae00ffffae00ffffab00ffffab00ffffaaeeffffaaeeffffaaaaffffaaaaffffaa88ffffaa88ffffaa80ffffaa80ffffaa0affffaa0affffaa02ffffaa02ffffaa00ffffaa00ffffa8a8ffffa8a8ffffa800ffffa800ffffa0a0ffffa0a0ffffa000ffffa000ffff8f00ffff8f00ffff8a8affff8a8affff8a00ffff8a00ffff88aaffff88aaffff8888ffff8888ffff8880ffff8880ffff8800ffff8800))))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x100dc89af81ede91e3da722be5fb37f478fd9c0a3c else 0
  | 3 => if page < 1 then 0x75aadd1a91a75acdd5ba357d2ce55ca0c75ace558a228d8fe5beaf08c9029be23c8d902dbe0d77f4e615ca3c806e455ca3c8d902dc5a3c75ace585a13816fe5c0a3c75ace55c23575ace55aa318d902dbe23c8d902d66a3c75ace55b23575ace55ba35828fd5c1a3c75ace57e9af806ce5731af75ae457c9af70cce57c9af828e19691af8b2fd1c1a3c8b2eb5c1ad97b4ce5859af7b4ce55aa358d8fd9c123c7bcdd55ca3c828fd9c0a3c7eceb5c0a3c8d8fd91e09a8d8fd9c0a3c7ece0dc0a3c000fd9c0a3c81efd9c1a3c75adf9bd23c7b4ce5868067ecdf9bc23c8d2fd9c1a3c828f69c8b0d876fd9c1a3c702a7d1e16175ace5809af75ace58585375ace57e1af87eeb5c1adc828f55c1adc75ace5859af8d8fd9c1a3c else 0
  | 4 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x75ace55ca3c32eeb59cab9478685d6b395728f03bbd375ace55ca3c87eeb59cab9479051d7b395728f20a3a4672ae51e3ad672ae51e196828f519cab94790519cab94786560a3ad672ae4a346f75ace55ca3c75ace55ca3c0a11b1eab395728f1eab395728f03a43f7aace55ca3c7aace55ca3c32d1bdeab395728f1eab395728f02846c672ae51e194672ae51e1940e90f5d6b395728f1d6b395728f0d043f672ae51e194672ae51e1963290f59cab94786519cab9478680ca41775ace55ca3c7a4eb59cab9479051eab395728f21f3ad672ae51e3ad672ae51e198828ce55ca3c329051d6b395725221fbad672ae4a24147aace55c944828eb59e2b9479051d6b395728c62abad672ae51e3ad672ae51e0df848eb59cab9478eb59cab951c8f20a3ad6dcae51e41475ad355ca3c828eb59cab939eeb59cab94780b9d6b395f2ae51e41d75ace55ca3c75ace590ab9479051d6b395728f2363de672ae45f41475ace55c8d7828eb55ca3c2b31b1d6b3961a6bdd6b3961a6bc3a3ad672c34d782e75ace586af935f051fb3ad7068f20a3ad672c3429c1475ae0d1e159828eb54fa3c2b3051d6b3961a6be363ad672ae51e3ad672ae51e074 else 0x872eb59cab9478eb59cab947870a2c3395728f0b0c4075ad795ca3c75ace56b2b92e30519cad6572586363ad6bcae51e3ad6bcae51e0748b0eb59cab9290eb59cab92e2522363ad672ae4a43ad672ae4a407488eeb59cab91aeeb59cab931a35e0a3ad672b846bc1475ace4bc0d78d8eb59cab91aeeb59cab91ae1d1d6b8353e8f014bad6c0ce5869af75ace56dab9478eb59cad55728f1d9bad672ae51e3fc75ace55ca3c75ad85b02b9478eb59cab94780edfdbad672ae51e41475ace55ca19842eb59cab9478eb59cae05728f1d6b395728f002bad672ae51e0688b8eb59cab9478eb59cab94782920a3ad672ae446bad672b615c820828eb59cae3427119d6b395728f1d6b395728f0a543375ace55ca3c75ace55ca3c3af051d6b395a66be0a3bb672ae51e414672ae54c23c828eb5b0ab94791b1de3395728f236339572a5d1e45775ace55ca3c75ace55ca3c15d089d6b395728f1d6b39572a711e41475ad795ca3c75ace55ca3c052eb59cad85728f20a3ad672b8ce5c1475ace4d7990828eb5c1adc337051d6b3957263e1fbad672c34d7c3f75ad8d5ca3c75ace5869af32d051eab3961a6be0a3d56c6ae51e414672c34d7994) else (if page < 3 then 0x8d8f79bb2b9479051d6b3961a84e0a3de6ecae42e46c828fd9c1a3c8d8fd9d6b83478002363f67068f1fb3ad7068f03a4147ece0d1e0367b4eb59cb0d05cfd9d6b836fc8f20a3ad7068f026c1475ae0dbd23c828f699cb0d0d9051fb3836f08f20a3f67d8e0d1e4147b4ce5868f98d8e0d4fa3c2c30f1d6b3961a6bdd6b3961a708d7c6c672ae51e1c3672ae551a3c2c31699cab94785860a3395e0ae4b0c3b672ae51e1618d8ce55ca3c384ce55caa247858e163ad672ae51e3ad672ae52c23c828eb59caec35f051d6b675728f2363ad672c3429bad672c343a05375ace58685305ceb59cb0d5f214e0a3ad706de51e41475ace576053828f619cab9479051d6b475728f20a3ad672ae505c6c7b4ce55ca3c828f699cb0d0a6eb59cab9478085d6b395729351e41475aa7d1e15d828ce55ca3c2e1101d6b3961a6be203da672ae51e3ad706a7d1e171828eb5af30d35f051ed35e5728f20a3ad706a7ca44147bcce55c8d775ace55ca3c2e8eb59cab947870e203ad672ae51e41475acf55ca3c828eb59cab9451051d6b39572895d6b395728f0b8c14672ae51e163828eb5aeab9479051d6b395725260a3ad672ae46d46c672ae51e161 else 0x85eeb59cb0d35eeb59cb2161a6be0a3ad672c34ec3ad672be4d78f0828eb5cd2d235eeb59c9af31c0b9d6b7e53e8f0acc6c75ae0d1e15975ae0d1e1590e8eb59cb0d31c0b9d6b836fc8f0acc14798eb5c1a3c8d8eb54fa3c2b2eb54fa3c2b21d2363395728f03c44275ace55ca3579cce55ca3c0e9051d6b396046bdd6b395729011e46c760ce55ca3c8d8e899cab9479121d6b3957288e0a3ad53e8f0adc4275ace5869aa75ace55ca3c2dd051ec33961a6be213d8672ae51e414706a7d1e163828eb5b0b0d35f109d6b615728f20a3ad706a7ca33ad672ae51e1b67b0ce55ca3c0e8fd19cab94785a5fa3395728f0273f4672ae51e0207e8ce55ca3c4371b19cab947858dd6b395b2ae50dbad672b655c969828f61b0ab94790519cad957258e363ad6c2ae51e3ad6c2ae51e07475ace56cab9041051fa33957251a0a33957258ca346c75ace55c94675ace55c9460e9051eeb395723160a3ad672b8862c6c7b4ce5869af828eb55ca3c233051d6b395728de0a3ad672ae51c46c672ae51e04e8d8f619cab94791b1ef2b9478462363da672ae51ac4e75ace55ca3c75ace55ca3c2490b1ed3395728f225bda672ae51e4147b4db95ca3c)) else (if page < 6 then (if page < 5 then 0x828eb5c1a9f1aeeb5bb2b93c20b9d6b73672c34d7bad6728f0c702e75adf95ca3c2b31b1d6ab9478565d6ab94785643a41475aa7d1e09a828eb59cb0b35f1b1d6a9f47826a363ad672c2cd7bad672c35859af000eb59cb0b35f1b19cb0d35e1d1d6b3961ab9cd7c1475ace5869b8828eb59cb0d357051f9bad7068f20a3ad672c342ac1475ae0d1e16b828eb59cb0d35b051d6b3961c6be0a3ad672bf8d7c1475ae0d6d23c828eb59cb0d153051d6a9f47825e0a3ad672bd8d7c2c75ace5869af75ad259cb0d35f051d6b3961a7520a3ad672c34cf46375ace5869af75ace5869af259051d6b8e6726be0a3ad6726bc7a41475ae0d6ba3c828eb59cb0d159051d6b834785b20a3ad672c34ed3b475ace5869af806eb59cb0d35eeb59caf935e0b9d6b3961a6bc1e3fe75ace5869af828eb5869af21b051d6b2d61a6be0a3ad7068f0b43ad6fca7d1e093860eb59cb0d35eeb59cb1461a6be0a3ad672c34ecbad672c34d780675ace5869af0d4eb59caf95cc6be2f3ad672c34d7bad706a7d1e09f828eb5c8b0d35f051d6b8353e235d6b3961a6bc1abad728ce5869af828ce5869af0e7051c333961a6bdd6b9a672be4d7c1475ae0d1e15e else 0x828eb55ca3c21b0a1d6b395728f1d6b395729cd1e45375ace55ca3c75ace55ca3c1cd051d6b915728f1d6b395728f01abad728ce55ca3c828ce55ca3c0e7051c33395728f1d6b7e6a0ae51e3ad672be55c9cb86aeb59cab9478eb59cab9478746223ad672ae51e3ad672ae51e15175ace590ab9396eb59cb245728f1d6b395728f048c1475ac755ca3c75ace55ca3c0eb01dd6b395728f236bad672ae51e3ad672ae51e06e8c4eb59cab9478eb59cab94782420abad672ae51e40675ace55ca3c838eb59cab9478eb59cb255728f1d6b856a0ae51e41475ad415c9ed828eb59cab93bb051d6b396186be0a3ad6c4ae51e41475ace55c94575ace55aa3535f1b1d6b396186be363ad5728f08cc6c75ace55ca378d8eb59cab94711c1d6b395728d6363ad6c4ae51e46c75ace55c9458d8ce55ca3c388eb5a3ab94781d1d6b3957282c3a4147b2ce55ca3c828ce55ca3c2c5051d6b3960c6be0a3ad672be0d7c4175ace55ca3c75ace55ca3c2deeb59cab9478065d6b395728f0e041475ace5391af828eb59cab91a0eb59cb0b4786be1c3ad672c34d7bad672c352c1af828eb5c1ac847912dd6b3961a6bdd6b765727849641475adb9869af) else (if page < 7 then 0x75ace55ca85478eb59cab947831ddfb395728f03a3ad672c115ca1b75ae01a9ab9479051d6b3960e6d20a3ad5728f08d42d75ace55ca3c75ace55ca55479195d6b3957235dd6b3957237c6bc4b75ace55ca3c75ace55ca3c259051d6b3a5728f20a3ad672ae51cbad672ae51e02275ace55ca4f479051d6b3958484e0a3395729ed1e414780db95ca3c75ace55ca94478eb59cab9478382363ec672ae45841475aae546a3c828eb59f2b9479051d6b3b5728f20a3ad672ae51941475adad5ca3c828eb5a62b9479051d6b39572742123ad6dcae51e3ad6fad555ca3c8d8eb5b72b9478eb5b72b94781d20a40b75adf11e41475adb95c85c864eb5a6ab9478eb59cacd51c8f20a3ad6dcb111e46c75ad355ca3c75ad355ca3c0e905205bad59a8f20a3ad69aae42e43675ace55c9cf75ace565ab939f051d6b7c67273e363ad672ae4e7bad672ae4e7874828eb59caf537d051d6b4d5726f9d6b39616ae51e3ad672b9d5ca3c768eb59cab947900dd6b395728f1d6b395728f01e3fe75ace55ca3c83ceb59cab9478eb59cb145728f1d6b395728f0033ad672ae51e06a8bceb59cab9478eb59cab947827dd6b755728f05f414780dd95c85c else (if page < 8 then 0x816eb5b2ab94791b205b645728f20a40b75ae2d1e3f9672b991e02e82902dc32b94791b1d6b3961a84dd6b3961a84c3a3ad672c350982e75ace586af9427051d6b765723420a3ad656ae46846c816fe5c1a3c75ace55ca3c203001d6b395728f1d6b395feae51e3ad672ae51e0b575ace585ab90b8eb59cae75721720a3ad6728f04ec1475ae455c85c828e199cab90b9051d6b895728f1d6b736ccae51e3ad672c0d5ca3c75ace55ca3c3feeb5b72b94780b9d6b6e5f2ae51e3ad5728f0a982e75adf99cab91aeeb59caf54780b9d6b736dcae51e3ad672ae49f82e75adcd9cab91aeeb59cafb5728f1d6b395728f04546c75aae51e11a75acd95ca3c0031b1d6b3a5728f2363ad672ae51cc1475ad395ca3c828eb59cab939ceb5a72b94781d1d6b395727383a3ad672ae51e00e75ace55ca3c1bb095d6b395728f1d6b39572a311e41475ad9d5c85c8d8ce55ca3c0ecfc59cab94781d1d6b39594ae518bad66cae51e00c75ace55ca3c4531b1d73395728f2363ad678ae51e3ad678ae51e07486eeb59cab9463051d6b3957e8c6363ad672ae518bad672ae51887475ace55923c040eb59cab247886e0a3ad672af51741475acf15ca2e else 0x75ace55c88d0e9199d6b6e5728f1d6b7d5728f04fc1475ae457aa3c828eb5beab911b051d6b7d6f88f19cab94781cc17386672ae51e02e672be55ca3c0e6e199caf95728f1d6b99672ae51e3ad70ece55ca3c828ce55ca3c0f9051d63395728f20a3b7672ae51e414710ce55ca3c76ceb59cab9479049d6b395728f1d6b395728f01ec1175ace55ca3c836eb59cab9478eb5cdb395728f2363395728f039b395728f03a07375ace55ca3c00eeb59cab94781c99cab94781cc1ab94672ae51e073672ae51e07300ece55ca3c0e61ca36386672ae51e386672ae51e0748d4eb59cab9478eb59cab9478211c33395728f01ab9470cce55ca3c8d4e199cab9478e199cab94782120a39170cae51e3ad672ae51e08b75ae559cab9479051d6b7c4783c2293ad672ae51e3ad672ae51e0f5854eb59cab9478eb59cab94ca8f20a3865728f07841470cce55c9ed828eb55ca3c271051d6b6e5727b60a3df672ae51e414672ae51e13a8d8f819cab94791b19cab94784e618bad672ae51e3ad672ae51e1f3892eb59cab9478eb59cab94784f1d6b395728b8173ad672be55c9b475ace586ab0436eb5b9ab9478425d6b395f2ae509c0b75add55ca3c)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x75ace57cab91af03df63395728f201b395728f07cbad71ebe55ca3c75adf99cab911eeb5b9b6b5728f1d6b395f2ae4303ad72cce55c9eb7f4ce57cab9478ce57cab94784e9d6b736c2ae51e3ad672be55c8c575aae51e10d05ceb596ab94780b9d6af95728f086bad6fcce55ca19828eb55ca3c237051d6b395728ee0a3ad68cae51e41475ace55ca1a75aae51e10d078ff9d6ab9478436363ad5728f086bad5728f08687475acb55ca3c079039d6b39572866363ad672ae50cbad672ae50c874818eb55ca3c213051d6aaa478425d6b395728f04b3ff75ace55ca3c828df19ca3c0d8ed19cab94781b1da3395728f003403672ae51e06c806ce55ca3c0d505196ab94781b1d6b395728f011bad672ae52b23c898eb59cab9478eb59cab94784a1da3395ccae51e403672b995ca3c828de19cab94330519cab9478279d6b915728f0173ad722be55ca3c75aae51e13505ceb5bf339572235d6b395728f0503ad672c655ca3c828eb5a12b9479051d6b395728820a3ad71eae51e41475ace55c88f8bceb5c8ab9478eb5c533957227e363ad722ae51e3ad722ae51e074828e299cab90b91a5d6b39572235d6b3957227c46c6c75ace55c88d else 0x828ce55ca3c252eb59cab9312171d6b395729742e44b75adb95c85c75adb95c9880b9051d6b6e5ea172363ad6dcae42e3ad6dcae43a05c828eb5b71770b91b1f63395727de0a3ad5728f094c147d8db95c85c8d8eb55ca3c2371b1d6b395728edd6b465728f03a3ad672ae50d074828eb59cb0d367051d6b3961a8460a3ad672c34d8c1475ace5869ec83eeb59cab9478eb59cb115728f1d6b395faae51e3ad672ae51e0ec75ace55ca3c060eb59cb1e5728f20a3ad672c34e3bad672ae51e02f75ace5892b9478eb59cb085728f1d6b395728f0f4bad672ae51e03475ae319cab9479051d6b3961a7aa363395728f03d3ba672ae51e07475aea99cab94791b1da3395728f2283ad672ae50fbad672ae51e0fe75ace55ca3c038eb5be3394780b9d6b3957235c173ad672ae51e20075ace55ca3c020eb5a12b94780b9d6b315728f0173ad672af11e02e75ace55ca1e05ceb5982b947803dd6b395748f0173ad672ae51982e75acf15ca3c05ceb59aab94780b9d6b395728f04dbad672c3d5ca3c75ae01b9ab947900d9cab94781d1d6b96672ae50dbad672c7d5ca3c75ace55ca3c3e2eb5c6b395728f1d6b395728f079bad6fcdb95ca3c) else (if page < 12 then 0x75adf19c8d70e905205bad6f835e31bad6723a46bbad6724b0748d78d8eb59c8e91aeeb59c8e91ae1d23633957235c3a42c75ace55c8d775ad259cab91af0e1d6b3957235dd6b39586ae46bc5a75ace55c8d775ace55c9581af051d6b7d57235e0a3ad6729c11e42475ace55c8d775ad719cab91af051d6b3958835e0a3ad672a986bbad6728f07482575ace5632b91af051d6b394e42b21d3ad672ae46bc3275adb95ca3c86ceb59cab91aeeb5be33951c8f1d6b39596ae46bbad672ae5470d7896eb5b72b9478eb5be3394784b20a3ad6dcbd51e44b75ad355ca3c75ace566a3c259051d6b3959a35e31bad672ae4e7bad672ae4e792c828eb59c9d21af051d6b6e5726f9d6b395728f0b93ad672ae548a3c828eb59cab9299051d6b394ce8f20a3ad6728f0ae44075adb95ca3c8b0eb59cab91af11dd6b6e5728f1d6b7d5728f0b8bad672bc15c97175ace55c9711af12dd6b5e5728f1d6b395c28f09641475adb970a3c8b4eb59cab9290eb59cab92904b20a3ad6faae4a446375ace55c8d775ace55c92c1af051d6b7c67235e0a3ad6723a46bc4b75ace55c8d775ace55c9881af051d6b6e57235e0a3ad672bd46bc1475aae4a98d7 else 0x828eb5b72f4479051d6b7c67236a31b7c6728f07cc4b75adb97aa3c75adf1b43392591b1d6b6e5ea8f1d6b6e5ea8f03a4147f2eb5beaf0828fb1b72f5479051be3686723e63636e5728f03a41475adf56023c828eb5b72b943d05204bad6f88f20a3ad6dcae43041475ada15c915828eb59caf5471081d6b6e5728f1d6b776dcae51e41475adf564a3c828eb5be23c22b051d6b6e5728ba1c3ad6dcae51e3ad6faae52c23c828eb5beacf479169d6b6e5728f1d6b395ea8f09641475ace55c8f2828eb5beaf5478eb5be3394780d1d6b926dcae51e41470cdb95ca3c828eb5b72b9433051d6b8e6727aa283ad6dcae50dc147d2db95ca3c828df19ca3c1ff1b1f636e5728f236414816df11e46c816eb5be23c0011b205b7c47902dd6b7c4781d20a40b6f88f01b46c6f8ce51e0f9876eb5b72b9478eb5b72b94b08f21dbad672ae46bbad672ae52c0d775ace55ca3c04aeb59cab94e28f1d6b395724c46bbad694ce55c8d78d902d93ab91af051d6ab925235e0a3395724a46bc1475ace55f0d7828eb59caad1af051d6b3957236e0a3ad6f6ce46bc1475ace4750d7828eb5b52b947918dd6b7c67235dd6b7c6724b06bc6c75adf19c8d7)) else (if page < 15 then (if page < 14 then 0x75aae51e1290e918dd6ab94784a631b395728f094c6375ad155ca3c8c6eb55ca3c22b12dd6b395728e1d6b3957296d1e3ad672ae51e12f896ec59cab9479141d6b395728d5d6ab94784b094b395728f09612975ace55ca3c2e6eb59cab95248f2363395728f03a40975aae51e12c814ce55ca3c258eb59cabe4784b1d6b39572894963ad672ae51e07f896eb59f2b9479051d6b3e5788f2363ad67cae51e3ad67cae51e0748c6eb59cab944b051d6b3957c8960a3ad672ab512c6c75ace55ca2575ace55ca250e9051d6b3e572879d6b395728f09944b75adad5ca3c8c6eb59cab91b4eb59cab94784cdd6b7b6728f0964146f6ce51e0ff828eb5b5af44791b1d6b6b5728f1d6b6b5728f03a3ad672ae4960da828eb5bdb391b5051d6b391d436a363ad672ae46d3ad672ae46d074828eb5b5ab90c0eb59cab94ba8f1d6b395728f098c3b7d8ce55c9f78d902db42b9479051d6b395ea8ba163ad6dcae51e3ad6dcd255ca3c8c6eb5b72b9478eb5b72b94784b1d6b7c6728f098bad6dcae52ea3c8d8fb1b72b93ef051d6b7c4784a60a37c6728f094c63816eb5be23c896fb1b72b947902dd6b7c4784b20a3ad6dcaf11e41475adf19ca25 else 0x75ace55ca580c0eb59cb175726edfc3395729611e339586ae51e1637a2ce55ca58478eb59cab94bc86dd6b395728f03ebad672ae52d23c75ace55ca60479051f2b395728060a3ad5728f08b41475ace55ca3075ace55ca3c054eb59cade5728f1d6b39572a3d1e3ad672c555ca3c828eb59cab93b90e1d6b4d5728f1d6b565729611e41475ad6966a3c870eb59cab939eeb59cac357273e38bad672ae51ac2c75aae51e12975ad255ca3c2530b19cab94784a5a4b395728f094c6c672ae51e079790ce55ca3c0e8eb59cab9478442363b1672ae51e41975ace55ca35788eb59cab9478eb59cab94bc165d6b39608ae42cbc775ace55ca3c7d2ce55ca3c0e8eb59cab94a486e0a3e9672ae4fd3ad672ae528a3c75ace55ca3c3f7051d6b3f5728f20a3ad672ae51241475ace55ca0e828eb5b6ab9479051d6b395723620a3ad6beae51e41475ace55c947828eb5b62b9479051d6b395723660a3ad69eae51e41475ace55c9cd75ace55ca3c25ceb59cb165728f2283e9672ae4fbc6c672ae51e129672ae51e1290e902dd6ab94784c63640b5728f098c0b64eae51e131816eb5a52b94791b205ab94784a6363275728f094c6c75aae51e129) else (if page < 16 then 0x828eb59cab919ceb59cab9478125f4b395728f03cc0a790ce55ca3c828ce55ca3c257051f4b6b5728f1d6b39608ae51ac1475ae415ca3c828eb59cab911d029d6b745728f1d6b745728f063bad65cae51e0c7828eb59ca3c2b5051eeb745728f20a3ad6e8b891e3ad672ae51e11f75ace55ca1b100eb59cab956686e0a3ad5728f08fc1475a8f0ab91a828eb55ba3c235051d6b385728e20a3ad5728e88c3ad672add1e03975ace55ca3c096fddd6b395728e2043ad696ae51e3ad5728f08d07475ace55ca380e91b1f63395727ea0a3ad5728f08641475ace55ca18810eb5ba2b9478ff9d6b3957284e0a3ad65aae509c1475aae51e122828fa59cab9427051d6b3960e84e0a3ad6e2ae51e41475ace55c8cf75ace55ca3c05aeb59caf75728f2363ec672ae509bad672add1e02075ace55ca3c094eb59cab747886dd6b395728f090c5075ace55ca22876eb59f2b94790b1d6b395728961dbad672ae50f43b672ae51e079876eb55ca3c2350e1d6b395728e2163ad5728f08d43b75ace55ca2e870eb55ca3c22d0b1d6b395728c22b3ad672ae5113ad672ae52ca3c75ace58bab9436eb59cab95208f1d6b6b5729611e3ad692ce55c8da else (if page < 17 then 0x8e2ce55ca350f31c5d6ab946a46a38bad672add1abad672ae55ba35000eb59cab746b1d1d6ab9478471d6b365728f08e3ad672c315ca35828eb59cab94191b15ca3c2341d2363395728e03a3ad672ae52f2358d8ca15ca3c08eeb59cab9478831d6b395728303a3ad672ae52f20c75ace55ca0c0b2fa59cab94bc165d6b395729482cc1475ace55ca2a828eb5a2abe478eb59cab94782060a3395728f040c1475aae51e12a829025d6b7b479051d6b6f5728f20a3ad672ae46b414672ae51e07e8d8ce55c9850f31b19cab946a1e5d6b395728d43cc6475aae51e11075acd95ca3c221051d6abb4784560a3ad5728f08ebad672ad51e22e790d2d5ca3c0e8f459cab93f41d20a3395728f106c6c7b6ce55ca3c828eb59cab93b6ec9d6b395728e2363b55728f08c46c762ce55ca35762ce55ca3c0f2f45d8b395728f20a3a0672ae51e41475adc15ca3c828eb59cab91a9051d6b3956488e0a3ad672ae515bad672c315ca1b75ad2d5ca3c094eb5972b9478129d6b2e5728f07d3ad672c195ca1b8c8eb5a22b9478f29d6b395728f2053ad696ae51e40a696ae51e0747d2ce55c9fa0e8fe1d8b395728f1fc3e9672ae51e41475adc95ca3c else 0x41475ace55ba35828eb55ca3c2391b15ca3c2341e6363ad47855c8d46c672add1e0798d8eb55ba3c2351b1d6b385728e2363ad5728e88c3ad672add1e0038d8eb59cab746b1b1d6ab9478471d6b3956e8f11abad672ae51e11c))))) else 0
  | 5 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x828eb59cab952e8f20a3ad672ae51e040828eb59cab94782960a3ad672b715ca3c828eb5b1ab947829e0a3ad672ae4f30a7828eb59cb0d35e66e0a3ad6c6ae51e19b87eeb59cab94786bdd6b395728f0d7996828f559cab94786be0a3395728f0d7994828eb59cab935e512363ad672ae51e19b75ace55ca3c3361d21fc1475ace55ca3c87eeb59cab947866c0043f75ace55ca3c828eb59cab9478659d6b395728f0cd996000eb59cab947865a0a3ad672ae51e015828eb59cab947866a0a3d575ace55ca3c828f559cab947866c004147aace55ca3c828eb59cab94786520a3395728f0cd9940010519cab94786520a3ad672ae51e051828eb59cab94786660a3ad672ae51e144828eb59cab9336512363ad672ae51e0be75ace55ca3c17c1d20a3ec75ace55c8be828eb59cab917c1721341475ace55ca3c828eb59cab95088f20a3ad672ae51e00c828eb59cab94782e60a3c075ace55ca3c828eb59cab94ee8f20a3ad672ae51e042828eb59cab94782c20a3ad672c355ca3c828eb5bb2b94782fa0a3ad672ae53723c828eb59cab947872e0a3ad672ae51e087828eb59cab947829e0a3ad672ae4f08be8d8eb59cab93c22f9d6b395727845f074828f79d6b395722fa0a3ad672ae49e853828eb55ca3c2f22fa0a3ad572784bc8be828eb59cb0d4786be0a3ad6ecae4f08be001051d6b3961a6be0a3ad672ae51e1af828eb59cab94782f80041475ace55ca3c else 0x828eb59cab947805a0a3ad672ae51e1a2828eb59cab94785860a339572a751e161828eb59cad65728f20a3ad6bcae51e1a3001051d6b5e5728f20a3ad672ae51e148828eb59cab953a5200041475ace55c948828eb59cab947835e0a3ad672ae4ef0d7001051d6b3957235dd6b39572a7d1e02975ad819cab94786be0a3ad6c6ce5869af8d8eb59cadc5728f1d6b395b8ae51e0748bb051d6b395728f20a3ad672ae51e0a3828eb59cab94780a5d6b395b8ae51e029000eb59cab94780a60a3ad672b615ca3c75ace56e2d85728f0003ad672b615ca3c828ff5d6b395728f20a3ad672ae51e0a2828eb59cab94781a60a3ad672b515ca3c828eb59cab94787b63241475ad8d5ca3c828eb59cadc5720820a40b75ad8d5ca3c828eb59cadc5721720a3ad6c6ae51e0be828eb59cae34786be0a3ad706a7d1e1448d8eb59cab9478511d6b395728f0a20748a1051d6b395725120a3ad672ae4a2020828fb1d6b395725120a3ad672ae4a205c828eb55ca3c3222fa1a41475ace55ca3c828eb59cab94787560a3ad672ae51e013828eb59cab947850a0a3cb75ace55ca3c828eb59cab947874e0a3ad672ae51e04c828eb59cab94785020a3ad672c34d78a7828eb55ca3c32229e0a3ad672ae4f31af828eb59cab947866e363ad672ae51e0a775ace55ca3c14e1d211c1475ace55ca3c828eb59cab95348f20a3ad672ae51e00a828eb59cab947829a0a3bc75ace55ca3c) else (if page < 3 then 0x828f699cab94781720a3da672ae51e1f7828f79d6b765728f0004147eceb5c1a3c8d8ce55ca9f4785860a3ad706a7d1e161878eb59cab94786bdd6b395728f0e11af8d90519cab9478586363ad672ae51e1610011b19cab9478585d6b395728f0b0874828ce55ca3c2c20da0a3395728f0c585c828ce55caa74785860a3ec672ae51e161828ce55ca3c3243e61cc1475ace55ca3c872eb59cab94785840043975ace55ca3c828eb59cab9478709d6b39572a891e161000eb59cab947870a0a3ad672ae51e014828eb59cab947857e0a3ec75ace55ca3c828eb59cab94786fa0a3ad672ae51e0f9828eb59cab95328f20a3ad672ae51e19f828eb59cb0d35e14e0a3395728f0c9053828eb59cab94126be0a3ad672ae51e1a38d8eb59cab947814dd6b395728f03a053828eb59cb0d47814c0041475ace586853831051d6b395728f20a3cd75ace55ca3c828eb59cab947800a0a3ad672ae51e052828f69d6b395728f20a3da672ae51e053828eb59cab949c8f20a3ad672ae51e20a828eb59cab947881e0a3ad672ae504853828eb59cb0d35e68e0a3da672ae51e1a3880eb59cab94786bdd6b39572a7d1e171828eb5af2b94786be0a3ad672ae54f948828eb59cab93c235e0a3ad672ae51e0538d8eb59cab947868dd6b395728f0d1874881051d6b395728f2203ad672ae51e1a3001101d6b395728f20a3ad672ae51e17175ace55ca9d4785c4003ad672ae51e171 else 0x828eb59cab94786d20a3ad672ae51e10e828eb59cab95368f20a3ad672ae51e19d828eb59cb0d35e05dd6b395728f0c9817828eb59cab944c6be0a3ad672ae51e1aa8d8eb59cab947805dd6b395728f03a01775ace55ca3c06205dd6b3965cae51e017885051d6b395728f2213ad672ae51e017828ec1d6b395728f20a3ad744ce55ca3c828eb59cab94848f20a3ad672ae51e227828eb59cab947888e0a3ad672ae513017828eb59cb0d35e6aa213ad672ae51e1aa828f619cab94786be0a339572a7d1e163828eb5b0ab94786be0a3ad672ae54f946828eb59cab93c23160a3ad672ae51e0178d8eb59cab94786a9d6b395728f0d507475ace55ca9e478081d6b3965cae51e1aa828eb59cab94785a5d6b39572a791e169828f61d6b395728f20a3d8672ae51e1aa001051ec3395728f20a3ad672ae51e163828ce55ca9e47858c00414672ae51e163828eb59cad95728f20a3ad6c2ae51e1aa001051d6b615728f20a3ad672ae51e146828eb59cab953c5180041475ace55c946828eb59cab94783160a3ad672ae4f00c58d8f699cab94786be0a3da75ace5869af8e1051d6b395728f20a3ad672ae51e04e828eb59cab94780e20a3d675ace55ca3c8d9051ed3395728f2363da75ace55ca3c0011b1ed3395728f1ed3ad672ae51e074828f699cab94780da0a3ad672ae51e105828eb59cab947883e0a40b7b4ce55ca3c828f699cab94783e60a3ad672ae51e213)) else (if page < 6 then (if page < 5 then 0x828fb1d6b3961a6be0a3ad6ecae4f08f9828eb59cb0d35e1720a3ad672c34fb9af828eb5bb33961a6be0a3ad706a7d1e0be828eb59cb0d35e2fa0a3ad6ecae4f09af828eb5c1ab94785660a3ad572a7d1e159001051d6ab94785663641475ace5869af0011b1d6b3961a6be0a3ad672c34d7874000eb59cb0d35e1d20a3ad672c34d7836828eb5ce33961a6be3241475ace5869af828eb59cb0d35e43a0a3ad706a7d1e020828eb59cb2e61a6be0a40b75ace5869af828eb59cb0d35e3e60a3ad706a7d1e05c828eb59cb2761a6be30c1475ace5869af828eb5c1a9f4782620a3ad672c34d782e000eb59cb0d35e0ba0a3ad672c357c9af000eb59cb0d5f26be0a40575ace5869af828eb5c1a9f47824e0a3ad672c34d786c828eb59cb0d5cc6be0a3ad734ce5869af828eb5c1a9f47821e0a3ad672c34d78f0828eb59cb0d5a46be0a3ad706a7d1e159001051d6b834785640041475aa7d1e159885051d6b3961a6be0a3ad672ae51e078828eb5d2b395728f23644275ace55ca3c884eb59cab94781d20a3ad672ae51e113828eb59cab94788b23244275ace55ca3c884eb59cab947843a0a3ad672ae51e22e884eb59cab9478082213ad672ae51e21b828eb5c1a9f4785a6363ad672ae51e16975ace55ca3c2d21d1d6b395728f0c602075ace55caab4785a6283ad672ae51e16975ace55ca3c32643a0a3ce75ace55ca3c828eb59cab947869e2841475ace55ca3c else 0x75ace55ca3c0e8139d6b395728f03a0528d8eb59cab94786be0a3ad672ae51e1b8828eb59cab94786add6b395728f0d7874828f5dd6b395728f20a3ad672ae51e055828eb59cab94785ae0a3ad672ae51e1ad828eb59cab947875a0a3ad672ae51e19c828eb59cabf4786be0a3ad672ae5119af828eb59cab94786de0a3ad672ae51e1ac828eb59cada5728f20a3ad672ae51e0a9828eb55ca9f4784260a3ad672ae50b9af828eb59cab947859e0a3ad672ae51e1a9858eb59cab94786bdd6b49672ae51e1af828eb59cab94787520a3ad672ae51e19e828eb59cab94787060a3ad672ae51e1a88c6eb59cab94786bdd6b395728f0d792c828eb5be3394786be0a3ad672ae4d78d7828eb59cad75728f20a3ad672ae51e0ac828eb59cab94785aa0a3ad672ae543a3c828eb59cabd4786be0a3ad672c1d1e1af828eb59cab94785921c3ad672ae51e1af75ace55ca584786be0a3ad672ae53ea3c828eb59cac24786be25bad672ae51e1af75ace55ca3c3c24b20a3ad6dcae51e1af828eb59cab953e35e0a3ad672bd51e1af75ace55ca3c3c20b9d6b73672ae51e1af828eb59cab947852e0a3ad672ae53323c828eb59cac54786bdd6b395728f0d782e75ace57cab94786be0a3ad672ae51e1598d8eb59cb0d4786bdd6b3961a8f0d787475ace586a3c35e0b9d6b3961abe51e1af8a1051d6b3961a6be0a3ad6ecae4f090e828eb59cb0d35e0820a3ad672c350d9af) else (if page < 7 then 0x828eb5cd3395728f20a3ad672ae51e0f0828eb5a82b947843a0a3ad672ae53721b82902dd6b505728f20a3ad672ae53705c828eb5c1b505728f20a3ad672ae5370be8d8eb59cab947872dd6b395728f0e5874828eb55ca9547843a0a3ad672ae50d9cb828fb1d6b3957272e0a3ad672ae4e585c828eb5662b94782fa0a3ad672c355c9cb88b051d6b395728f20a3ad672ae51e14f828eb59cab947806a0a3ad672ae51e1c8828f71d6b395728f20a3ad672ae51e14d828eb59cab947815e0a3ad672ae51e1c5828eb59caa547821e0ebad672ae51e0be75ae159cab94782fa0a3ad6a0ae51e0be828eb59cab93da2fa363ad672ae51e08775ace55ca3c10e1d20a3ec75ace55c887828eb59cab910e1720ec1475ace55ca3c83aeb59cab947821c0041d75ace55ca3c828eb59cb215728f1d6b85672ae51e087000eb59cb215728f20a3ad672ae51e008828eb59cab947821a0a3b875ace55ca3c828eb59cb1b5728f20a3ad672ae51e03e828eb59cab94782160a3ad6a0ae51e087828eb59cab93da21e0a3ad672b151e0a7828eb59cab93cc2fa0a3ad5728f0f0918828eb59cab946a6be0a3ad672ae51e16d828eb59cab94786ba363ad5728f0f09188d8eb59cab946a6be3846c75ace55ca3c8d8eb59cab94785b6363ad672ae51e0028d8eb59cab94786ba0a3ad672ae51e1c4828eb59cab9478692363395728f0d787475ace55ca3c3881d1d6b395728f0d2074 else 0x828eb59caa64782fa0a3ad672ae4f20be8d8eb59cab94782c1d6b395728f058074828fb1d6b395722c20a3ad672ae45805c849051d6b395728f2123ad672ae51e0b0001091d6b395728f20a3ad672ae54723c75ad719cab94782c0003ad672ae54723c828eb59cab947802e0a3ad672ae51e0af828d5d9cab94782c20a3ad672bc15ca3c828eb5b72b94782c00041475adb95ca3c828eb59cab94d48f20a3ad672b111e0b0001051d6b4d5728f20a3ad672ae51e1cf828eb59caa64782c00041475ace55c9cf828eb59cab93c82c1d6b395728f09e82e75adcd9cab94782fa363ad672c355ca3c75ace586ab94781d230c1475ace55ca3c828eb59cab94782620a3ad672ae51e02e75ace586ab94780b8003ad672ae51e02e828eb59caf95728f1d6b3961abe55ca3c000eb59caf95728f20a40575ace55ca3c828eb59cab947824e0a3ad672ae51e06c828eb59cae65728f20a40b75add95ca3c828eb59cb0d572172363ad6ecae51e0be75add95ca3c17c1d1d6b3961a8f09e82e75add9b9ab94782fa0a3ec75add95c8be828eb5bb2b917c1720a3ad6ecae4bc8be828f01d6b765728f20a3ad6ecae51e0428d8eb59cab94dc8f1d6b395729b91e074828fe5d6b394dc8f20a3ad672b155c85c8a9051d6b395728f20a3ad672ae51e0e4828eb59cab94780920a3ad672ae535a3c828fb9d6b395728f20a3ad672ae51e0e2828eb59cab947818e0a3ad672ae53423c))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x828eb59cab94787320a3ad672ae4f10b9828f019cab917c1723741475ace55ca3c828eb59cab94781920a3ad672ae51e037828ef5d6b395728f2363c075ace55ca3c780eb59cab94781d20a3ad672ae51e10982902de03395728f20a3c0672ae51e0f9828eb59cab947840a0a3ad672ae51e203828f019cab94781720a3c0672ae51e1f7828f3dd6b395722fa32bad672ae51e0be75ace55ca3c1be2fa0a357672ae45f05c828eb59cab91ae2fa363ad672ae53ba3c75ace55ca774781d20a3ad672b395c85c828ce5672b94781720a33959cae51e1f78ab051d6b395728f22abad672ae53ba3c001155d6b395728f20a3ad672ae51e0df75ad5d9cab947837c003ad672ae51e0df828eb59cab947809a0a3ad672ae53a23c82902dd6ab94ee8f20a3ad6aece55c8d7828eb59cb1c5728f20a3ad672ae51e0ad828fb19cab94ee8f20a351672ae51e0f9828eb59cab95028f20a3ad672ae51e05c828eb59cab94787de0a357672ae51e042828eb5a42b94782fa0a3ad672ae50b8be8d8eb59cab9478109d6b395728f03a042828eb55ca3c2f210a0b41475ace55ca3c828fbdd6b395728f20a3ad672ae51e001828eb59cab94781060a3c0672ae51e042828eb59cab94a68f20a3ad690ae51e042828eb59cab94928f20a3ad672ae51e216828eb59cab942e10a0a3c0672ae51e0b0848eb59cab94782f9d6b5c672ae51e0be828eb5b72b94782fa0a3ad672b111e0be else 0x75ace55ca3c17c0b9d6b395f2ae51e0be828eb59cab94781da0a3ad73cce55ca3c8d9099d6b395728f2133ad672ae51e074828eb59cab94784563242675ace55ca3c84ceb59cab947843a0a3ad672ae51e111828eb59cab947888614bad672ae51e020852eb59cab947886e133ad672ae51e02084ceb59cab947886e363ad672ae54223c75ace55ca844781d1d6b395a0ae51e02075ace5682b947886dd6b39594ae51e02075ace5652b947886e0a3f175ace55ca3c828eb59cab94782da0a3ad672c895ca3c828eb59cab94782aa283ad672ae54223c75ad4d9cab947843a0a3ad672ae54423c828eb59cab94780820a3ad672ae51e21b75ad6d9cab94780320a3ad680ae51e0be828eb59caba4782fa0a3ad672ad11e0be828eb59cab94662fa363ad672ae51e00c75ace55ca3c0e8031d6b395728f01880c75ace5972b9478032133ad672ae51e00c828eb9d6b395728f20a3ad750ce55ca3c828eb59cab94888f20a3ad680ae51e00c828eb59cab947c8f20a3ad672ae91e00c001051d6b3c5728f20a3ad672ae51e231828eb59cab44780300041475ace55ca31828eb59cab9466032133ad672ae51e0b9828eb5ba2b94782fa0a3ad672ae4f10be8d8eb59cab94782e5d6b395728f05c87475ace55ca3c2ea081d6b3965cae51e0b975ad6d9cab94782e60a3bf75ace55ca3c828eb59cab94f08f20a3ad672c115ca3c828eb5ba2b94782e60a3ad672ae536a3c) else (if page < 11 then 0x828eb59cab93062fa0a3ad672ae5170be828eb59cab950c8f20a3ad672ae51e0bc828eb59cab94785420a3ad672ae51e0a8828eb5a0ab94782fa0a3ad664ae51e0be828eb59cab947831a0a3ad672ae51e0bb828eb59cb045722fa0a3ad672ae49f0be828eb59cab94d88f20a3ad672ae51e088828eb55ca3c2162fa0a3ad658ae51e0be828eb59cab94f88f20a3ad672ae51e0b8870eb59cab94782f9d6b39586ae51e0be828eb59cab952c2fa0a3ad672ae4df0be828eb59cab947853a0a3ad672ae51e0ab828eb59cab94783720a3ad672ae51e0b78b4eb59cab94782f9d6b395728f0ac0be828eb5beab94782fa0a3ad5728f0a98be828eb59caf05722fa0a3ad672ae49f8be828eb59cab94d28f20a3ad672ae51e08c75ace55ca3c2a40b9d6b7e672ae51e0be828eb59cab92f82fa0a3ad666ae51e0be8a0eb59cab94362fa0a3ad5728f0bd0be8d8fb1d6b395722f9f63ad672ae45f074828eb59cb2b5722fa0a40b75aae53ea3c828eb5acb395722fa1dbad672ae51e0be75ace55ca584782fa0a3ad654ae51e0be8d8eb59cab917c171d6b395722f83a05c828fb19cab917c1720a3ad690ae45f05c828eb59cb2a5722fa0a3ad654ae45f05c828eb59cab91ae17225bad672ae51e0be75ace55ca3c3102fa0a3ad5728f0bd8be828eb59caf54782fa0a3ad6728f0bb8be8d8eb55ca3c2f22f9d6ab94785e45f074828eb59cab93142fa0a3ad5728f0c50be else 0x828eb59cab91421720a3ad672b995c85c828eb5cd3395721720a3ad672ae47805c82902dd6b765721720a3ad672c343385c828fb19cb0d5721720a3ad6ecd995ca3c828eb59caeb5721720a3ad6ecae51e207828eb5bb2b90b810a0a3ad672c342e05375ace55ca3c3ee0b9d6b395f2ae51e1f7896eb59cb0d5728f1d6b76672ae51e12c828eb5b730d5728f20a3ad706ce55c8d7828eb5bb36e5728f20a3ad6ecce55c8d775add99cab94780b9d6b76672be55ca3c828eb5bb2b94783c20a3ad672c355c9ed828eb55ca3c2302fa0a3ad66cae51e0be828eb59cab95148f20a3ad672ae51e0bd8d8eb55ca3c2302fa363ad66cae51e0be8dd1b1d6b395728f2363ad672ae54523c8d8eb59cab9478006363ad672ae51e0bd828eb59cab94783860a3ad672ae51e0b18d8ce55ca3c17c1d1d6b395728f07087475ace55ca3c1621d1d6b395728f03a06475ace55ca3c0e81060a3ad672ae5238be828eb59cab943c2fa0a3ad672ae51e0c9828eb59cab94782ea0a3e575ace55c8be828eb59cab917c1820a3be75ace55ca3c828eb59cab94781120a3ad672ae4c20be828eb59cab95102fa0a3ad672ae51e0c8828eb59cb005728f20a3ad672ae4c08be858eb59cab94782f9d6b49672ae51e0be828eb59cab95022fa0a3ad672ae51e0de8c6eb59cab94782f9d6b395728f0960be828eb5be3394782fa0a3ad6728f0748be828eb5b43395722fa0a3ad672ba95ca3c)) else (if page < 14 then (if page < 13 then 0x75ace5692b94780b9d6b7e672ae51e1ed828eb5cd3395727b6363ad672ae51e1ed75ace55ca3c3da1d20a3ad5a4ae51e0f9828eb59cab93ee7b62541475ace55ca3c828eb59cab94784ee0a3ad672ae51e01b828eb59cab94787ae0a3e075ace55ca3c828eb59cab94784e60a3ad672ae51e058828eb59cab94787a2283ad672ae51e02e8a0eb59caf95728f20a3ad6ecae51e115828eb59cb0d5728b9d6b395728f0ab02e75adcd9cab947843a0a3ad706d515ca3c828eb59cb0d5726d1d6b395728f01702075ace57cab9478081d6b395728f10d82e75ace57cab947886e283ad672c355ca1b7d8eb59cab94780b9f63ad672be55ca3c828fb19cab94781b20a3ec672b995ca3c828eb5bb2b94784260a3ad672c355ca138d902dd6b765728f205bad6ecae51e0747f2eb59cb0d4780ba05bad6ecdcd5ca3c82902dd6b6e5728f20a40b75aae51e093828fe59cb0d4781b20a40b75ad915ca3c82902dbb3645728f20a40b75ae695ca3c828fe5d6b394783c20a3ec75add95c909828fe5d6b3961a84e0a3ad672c351e213001051d6b3961a84e0a40b7f2eb5c1a3c75ace55ca3c2a80b9d6b73672ae51e0f9828ce55ca3c2a81b20a364672ae51e0f9870eb59cb0d5728f1d6b3961aae52c23c828eb5c1b525728f20a3ad672c355c9be75ace55ca3c0b80b9d6b395f2ae51e05c8d8eb59cb0d572171d6b3961aae43a05c75ace586ab90b80b9d6b3961abe55c85c else 0x8d8eb59cae65728f1d6b395ccae51e074828de19cab94781720a378672ae51e1f78bd051d6b395728f22f3ad672b995ca3c001179d6b395728f20a3ad672ae51e09f75ade19cab947827c003ad672ae51e09f828eb59cab94780ae0a3ad672b915ca3c828de19cab947824e0a3ad714ce55ca3c828eb5c8ae65728f00041475ae455ca3c828eb59cab94782360a3ad6f0ce55c88d001051d6b395722360a3ad6dcd915ca3c75ace586ab94780d5d6b94672c355ca3c828ce586ab94781ce0a386672c355ca3c75ae699cab94780b9d6b9a672be55ca3c8d8eb5cd3395728f1d6b9a672ae51e0748d7051d6b395728f20a3ad672ae51e083828eb59cab94780d5d6b9a672ae51e035000eb59cab94780d60a3ad728ce55ca3c75ae69ca3395728f0003ad728ce55ca3c82904dd6b395728f20a3ad672ae51e082828eb59cab94781ce0a39a672ae51e0730010519cab94781ce0a3ad70cce55ca3c828e69c33395728f00041470cce55ca3c75ace55ca3c2680b9d6b7e672ae51e08785eeb59cb0d5728f1d6b39642c355ca3c75ace55ca3c1e00b9d6b395f2ae51e0f0828eb59cab92f821e363ad672ae51e0f075ace55ca3c1e01d20a3ad5728f07c8f0828eb593ab94783c215c1475ace55ca3c828eb59cab94c68f20a3ad672ae51e00f828eb59cab94783ba0a3c275ace55ca3c828eb59cab94c28f20a3ad672ae51e046828eb59cab94783ae0a3ad734ae51e0f0) else (if page < 15 then 0x828eb5c1b3957286602bad672ae51e02e80aeb59caf95728f239c1475ace55ca3c828eb59cab94780fe0a3ad672ae51e03c80aeb59cab94780f0003ad672ae51e03c828ff9d6b395728f202bfe75ace55ca3c000ff9d6b395728f23640575ace55ca3c80aeb59cab94781d20a40575aae51e10d828eb59cab94784340041475aae51e10d829041d6b395728660a3ad672ae51e219001051d6b395728660a40d75aae51e10975ace55ca3c26c0b9d6b7e672ae51e093860eb59cb0d5728f1d6b39628c355ca3c8d8eb59cab947824dd6b395728f04987483d051d6b395728f20f3ad672ae51e093001079d6b395728f20a3ad672c515ca3c75ae119cab947824c003ad672c515ca3c828eb59cab94780260a3ad672ae51e092828eb5a92b947824e0a3ad672ae53123c828eb59cab94787c1d6b395728f03602e75ace57cab94781b20a3395728f09b06c75ace586ab9478019d6b3961aae51e06a8d8eb59cab94781b1d6b395728f03a06c828ce55ca3c0e21720a33964eae51e06c835051d6b395728f20a3b975ace55ca3c828eb59cab9478019d6b395728f036006000eb59cab947801a0a3ad672ae51e06a75ace55ca3c0d81a8003ad672ae51e06a8290159cab94781b20a3ad672ae52ba3c828eb59cab9478809d6b395ccae51e02e75ace57cae65728f20a405672b995ca3c8bceb59cb0d5728f1d6b83672ae51e09f828eb5c8b0d5728f20a3ad706ce55c88d else (if page < 16 then 0x75ace55ca3c26e0ba363ad672ae51e02e75ace55ca3c0e80b9d6b395728f01b02e75ae719cab94780ba323ad672ae51e02e75ace55ca3c21c0b9d6b395728f01982075ace5972b94780ba30bad672ae51e02e828ed1d6b395728f20a3ad73ace55ca3c828eb59cab948a8f20a3ad672ae51e21f768eb59cb0d5728f205bad672ae51e02e75ace55ca3c1f20b9d6b395728f03802e75ace593ab94780b9da3ad672ae51e02e000ed1d6b395728f1d6ba1672ae51e02e75ace55ca3c05c019d6b395728f01702b75ad0d9cab94780b9d6b39660ae51e02e75ace55ca3c05c03dd6b395728f01981b75ace55ca444780b9d6b395728f01900c8c2eb59caf95728f2363ad672be55ca3c75ace57cab94781d1d6b395f2ae51e03675ae719caf95728f2323ad672be55ca3c75ace57cab9478439d6b7e672ae51e02075adf99cab947886dd6b7e672ae51e09882900dd6b395728f20a3ad672ae51e095828eb5cb3395728f20a3ad672ae51e089806eb59cb0d5728f1d6b395f2ae51e02e816eb59caf95728f1d6b395f2ae51e0f975adf99cab9478171d6b7e672ae51e1f7806eb59caf95728f00040375ace55ca3c75adf99cab9478255d6b395f2ae51e06a75ace57cae45728f1d6b98672be55ca3c75adf99cab9478225d6b395f2ae51e0ee75adf99cab94787add6b39608be55ca3c75adcd9cab94782e5d6b3961aae51e03c7fceb59cb0d5728f20a3ad61aae51e10d else 0x8d8eb59cab947826a363ad672ae51e0068d8eb59cb0b5728f1d6b3961ac2d5ca3c000eb59cb0b5728f20a3ad672c695ca3c828eb59cae75728f23633961aae51e07475ace58d2b94781d1d6b3961ab9d5ca3c75ace573ab94781d0003ad672b9d5ca3c75ace55ca3c0e80fdd6b395728f03a06a828eb59cb105728f20a3ad672be95ca3c828eb5bb3455728f20a3ad672c355ca1e829009d6b395728f20a3ad672ae51e06d829025d6b765728f20a3ad672c355c860828eb59cab94782660a3ad672c255ca3c828eb5c1ab94784560a3ad6ecce55ca2e828eb59cb235728f20a3ad672ae51e1ef828eb59cb0e5728f20a3ad672bf95ca3c828eb5cbb395728f20a3ad672ae51e0f1828eb5c1b745728f20a3ad672c355c8c5828eb59cab947825e0a3ad672bd95ca3c858eb59cb0d5728f1d6b83672ae52c23c828eb59cb205728f20a3ad672ae51e1f2828eb5bb3525728f20a3ad6ecce55c9be828eb59cb135728f20a3ad672ba55ca3c8c6eb59cb0d5728f1d6b3961aae51e12c828eb5c73395728f20a3ad672ae51e0f4828eb5c1b6e5728f20a3ad672c355c8d7828eb59cab94781ea0a3ad752ce55ca3c8d9185d6b395728f230bad672ae51e074828eb59cab947845e0a3ad672ae51e2348d1051d6ab9478456363ad672ae51e09875ace55ca3c1301d20a3ba75ace55ca3c828eb59cae85728f20a3ad6a8ae51e098828eb59cab94c88f20a3ad672ae51e1ee))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0x828eb59cab954e35e13c1475ace55c8d7828eb5ac33957235e0a3ad672ae46b80d828eb59cab91ae34a0a3ec75ace55c8d7828eb59cab91ae2c20a3ad672ca95c8d7828eb59cab927e14e0a3ad672b1d5c8d7828eb59cab954835e0a3ad672ae49f88c828eb59cab91ae2b225bad672ae51e0b075ace55ca3c3102c20a3ad5728f0bd8b0828eb59caf54782c20a3ad6728f0bb8b0848eb59cab94787ddd6b395a2ae51e1f7828eb5b72b94787de0a3ad69aae51e1f7828eb59cb2757273e0a3ad672ae4fb9be896eb59cab947868dd6b395728f0ef12c828eb5b72b947868e0a3ad672ae54e8d7828eb59caf547868e203ad672ae51e1f775ace55caa74785c60a3ad6bcae51e1f7828eb59cab954e5220a3ad672c9d5c8d7828eb59cab93ee35e25bad672ae51e05c75ace55ca3c3101720a3ad6dcae51e05c828eb59ca3c2ee1720a3ec672ae51e1f78d8eb59cab9478171d6b395728f03a05c828ce55ca3c2fc1720cc1475ace55ca3c828f0dd6b395728f20a3ad672ae51e003828eb59cab94781660a3ec672ae51e05c828eb59cab93ee172363ad672ae4fb85c75ace55c9f70e817225bad672ae4fb85c75ace55c9f73101720a3ad672ae4bf05c828ce55c9f72fc1720a3ad672bd55c85c828eb5b72b93ee1700041475adb95c85c828eb59c9f72ee1720a3ec75ace55c9f7828fb19cab93ee1720a3ad672ae51e09a828eb59cb0b5728f239c6c75ace55ca3c else 0x8a1051d6b6e5728f20a3ad6f8ce51e10e828eb5b72b94780820a3ad6dcae51e21b828fb1d6b6e5728f000414816eb5be23c828eb5be3394783e60a3ad6dcae51e042828eb59caf547884e31bad672ae51e0d775ace55ca3c25835e0a3ad6f8ce51e0d78d8eb59cab947835dd6b395728f06b8748a1051d6b3957235e0a3ad672ae4c10d7828eb59cab91ae0820a3ad672ae50d8d7828eb59cab92fc35e13c1475ace55ca3c828eb59cab94f28f20a3ad672ae51e00d828eb59cab947834a0a3ad672ae53923c828eb59cab947871a363ad672c9d5c8d775ace593ab91ae1d20a40b75ac9d5c8d782902d9cb2757235e31c1475ace55c8d78c6eb59cb2757235c0046375ace55c8d7828eb59cab925835dd6b3964eae4960d7000eb59cab925835e0a3ad6728f0bb81d828eb59cb2657235e0a33964eae47c8d7828eb5be33964e35e0a3ad6f8ce55c8d7001051d6b7c67235e0a3ad672c9c748d7828eb59ca3c1d235c0041475ace4748d7828eb5b433957235e3641475ace55c8d70011b1d6b3957235e0a3ad672ae46b874000eb59cab91ae1d20a3ad672ae46b836828eb5ce33957235e3241475ace55c8d7828eb59cab921c35e0a3ad6728f0bb820828eb59cb2e57235e0a40b75ace55c8d7828eb59cab91f235e2dc1475ace55c8d7828eb59cab92ac35e0a3ad6728f074820828eb59cab955635e0a3f975ace55c8d7828eb59cab92a835e0a3ad6728f07485c) else (if page < 20 then 0x828ce593ab94783e60a40b75aae51e0f98c6ce593ab94783e59cb275728f0960f9858ce593ab94783e5a4b3964eae51e0f982902d93ab94783e62d3ad672bc15ca3c75ada19cab94784b2363ad672bc15ca3c75ace5782b94781d22fc1475ace55ca3c828eb59cab94782720a3ad672ae51e02c828eb59caed5728f20a3ad672ae51e0ed828eb59cab94787aa0a40b75ada15ca3c8c9051d6b6e5728f20a3ad6dcae51e10e828eb59caf05720820a3ad672bc15ca1b828eb5b72b94783e60a3ad672bc15c9f78d8eb5b72b94787ddd6b6e5728f0fb874828fb1d6b6e5727de0a3ec6dcae51e1f7897051d6b6e5728f225bad6dcae51e1f700112dd6b6e5728f20a3ad6f8ce51e12c75adf19cb274784b0003ad6f8ce51e12c828eb5b72b94780760a3ad6dcae51e1f4828df19cb274783e60a3ad6fabc15ca3c828eb5b72f54787dc0041475adb97aa3c8d9051d6b6e5728f00046c75adb95ca3c828eb5b72b94781d0003ad6dcae51e074828eb5b72b94780da0a3ad738db95ca3c8cf051d6b6e5728f20a3ad6faae51e09c828eb59caf05720b20a3ad6dcda55ca3c828eb5beab947824e0a3ad672bc15c85c8b7051d6b6e5728f20a3ad672bd51e10e828eb5beab94780820a3ad6faae51e21b828fe5d6b6e5728f20a3ad672bd51e0f9828eb5beab94781720a3ad6faae51e1f7828eb5c9b6e5728f20a3ad672bc15c8ed828eb5beab94782320a3ad6f8ce51e1ea else 0x75ace55ca934784b1d6b395728f0ef92c75ace55ca3c2b0271d6b395728f0960d275ace55ca3c31007625bad672ae51e1f7828e8d9cab94787de0a3ad67cae51e1f7828eb59caaf4787de0a3ad672ae50f1f7828eb59cab94787d2363ad672ae51e01d75ace55ca3c0e807625c1475ace55ca3c896eb59cab94780740044b75ace55ca3c828eb5cfb395728f20a3a3672ae51e01d828eb59cab94868f20a3ad67cae51e01d001051d6b3e5728f20a3ad672ae51e225828eb59caaf4780740041475ace55ca25828eb59cab947887a0a3ad672ae50f01d896eb59cab94787d1d6b3964eae51e12c828ce593ab94783fe0a3ad6d6ae51e1f7828eb59cb2757236a0a3ad672ae4fb860828eb59cab9478076363ad672ae51e1f475ace55ca3c3e81d20a3ad672ae51e12c75ace5932b94784b0003ad672ae51e12c828eb59cab94783fe0a33964cae51e0ff828eb59caee5728f20a3ad6d6ae51e1f4001051d6b6b5728f20a3ad672ae51e0da828eb59cb265723680041475ace55c8da828eb59cab94781820a3ad672ae4fa0608d8ce593ab94783e59cb275728f07c8748c6eb59cab94783e5d6b395728f0960f9876eb59cab94787ddd6b395729611e1f78d8eb59cab94783e5d6b395728f07c874859051d6b395728f2163ad672ae51e0f90010b1d6b395728f20a3ad672ae52c23c75ad259cab94783e4003ad672ae52c23c828eb59cab94780460a3ad672ae51e0f6)) else (if page < 23 then (if page < 22 then 0x896eb59cab94780da25bad738ce55ca3c828eb59cab94784520a3ad672ae51e22d8b712dd6b395728f225bad672ae51e10e8b4eb59cab94780822d3ad672ae51e21b828eb59cab94788d625bad672ae51e020896eb59cab947886e25bec75ace55c9f7896fb19cab94787de3644b75ace55ca3c896eb59cab94781d231bad672ae51e011896eb5d33395728f23044b75ace55ca3c896eb59cab947845231bad672ae51e00d8b4eb59cab94788b62d3ec75ace55ca3c896eb59cab94783e62d3ad672ae51e05c8b4eb59cab94787de2844b75ace55ca3c8c6eb59cab947843a25bad672ae51e003896eb59cab94788d625bec75ace55ca3c75ace55ca3c2580d9d6b9c672ae51e12c75ace55ca3c310081d6b3965cae51e12c8a0eb59cab94784b1d6b395728f0ac10e75ace55ca3c258081d6b395728f10d92c8d9051d6b395728f20a3ad672ae51e201828eb59cab94781d20a3ad672ae51e1fa828eb59cab95268f20a3ad672ae51e1a6816eb593ab94784b205b3964eae51e12c8d8eb59cab94787ddd6b395728f0fb8748c6eb59cab94784b205bad672ae51e12c7d8eb59cab94784b1d6b395728f0ac0f975ace55ca3c258171d6b395728f0fb92c8d8eb59cab94784b00046c75ace55ca3c75ace594ab94784b1d6b395728f096074000eb59cab94781d1d6b395728f0960f68c8eb59cab94784b1d6b39650ae51e12c75ace55ca3c258439d6b395728f0c4059 else 0x828eb59cab94786ea0a40b75ad215ca3c828eb59cab94a6172363ad672ae51e20775ace55ca3c40e1d20a3ec75ace55ca0789b051d6b395728f20a3ad672ae51e126828eb59cab947807a0a3ad672ae51e204828eb59caf35728f20a3ad672ae51e0d1828eb5952b947810a0a3ad672ae50985c828eb59cac247814e0a3ad672ae50385c828eb59cab94784c6363ad672ae51e13175ace593ab94784c4003ad672ae51e131828eb59cab94ba8f2363395728f0fb87475ace55ca5d4787ddd6b395729751e074000eb59cab94ba8f20a3ad672ae5239f7828f95d6b395727de0a3ad64eae51e115828eb59cab945c7de0a3ad672ae51e130828eb59cab94787da0a3ad672ae53d23c828eb59cab94786960a3ad672ae51e1fe828eb59cab94787d60a3ad672bbd5ca3c828eb59cab94782ce0a3ad672ae51e125858eb59cab94787ddd6b39586ae51e1f7828eb59cab95027de0a3ad672ae52623c828eb59cab94784b60a3c675ace55ca3c828ec59cab94787de283ad672ae50d9f7828fa59cab94787de363ec672ae51e1f77d8ce55ca3c3ee1d20a3ad672ae51e1298d9051f63395727de363ec75ace55c9f70011b1f63395727ddf63ad672ae4fb874828fb19cab93ee0da0a40b75aae51e129828eb593ab94784a40041475aae51e1298a1051f63395727de0a3ec672ae4fb82082902d9cab94784a60a33964eae51e1290010519cab94784a60a3ad74cce55ca3c) else (if page < 24 then 0x828eb59cab94788760cbad672ae51e020832eb59cab947886e363c375ace55ca3c786eb59cab94781d20a3c875ace55ca3c828eb59cab94780da0a3ad738ce55ca3c7a0eb59cab9478081e83ad672ae51e21b828fc1d6b395728f20a3ad672ae51e0567a0eb59cab947800e0a3b1672ae51e05c828eb59cab946a172363ad672ae51e00375ace55ca3c0e800dd6b395728f01400375ace55caab47800e283ad672ae51e00375ace55ca3c30400e0cbad672ae51e003828ec5d6b395728f20a3b1672ae51e003828eb59cab947a8f20a3ad672ae51e236828eb59cab946a00e0cbad672ae51e059828fa59cab94781720a3ad672ae4fd05c8d8eb59cab9478165d6b395728f03a05975ace55ca3c0cc081d6b39572aad1e0598a0eb59cab9478165d6b395728f0c10597a0eb59cab94781660a3e975ace55ca3c828fa59cab94781660a3ad672ae52923c828eb59cab94788220a3ad672ae4fd0598d8fb19cab9478171f63395728f03a05c8e3051d6b395728f20a3ad672ae51e047828eb59cab94780e60a3e175ace55ca3c8d8fb1d6b395728f1f63ad672ae51e074828fb19cab92fc171d6b395728f03382275ace560ab9478172363ad672ae529a3c75ace55ca534781d228c1475ace55ca3c828eb59cab947840e0a3ad672ae51e02275ace55ca53478088003ad672ae51e022828eb59cab949e8f1d6b3957294d27a3c000eb59cab949e8f20a3ad672ae51e0ca else (if page < 25 then 0x828eb59cadf5728f20a3ad672ae51e141858eb59cab947824dd6b39586ae51e093828eb59caa147824e0f3ad672ae51e0f975addd9cab94783e60a3ad6a4ae51e0f9858eb59cab94782c1d6b49672ae51e0b0828eb59cab95022c2123ad672ae51e0f975ad559cab94783e60a3ad672b111e0f9828eb59cab93ce3e60a3ad672ae4c285c8d8eb59cab930a172363ad672ae51a85c8e31b1d6b395728f2363c875ace55ca3c828eb59cab94bc172363395728f03a05c75ace55ca5e0e8171d6b395727e83a05c75ace55ca3c0f21d1d6b395728f03a047828eb59cab947818a0a3e275ace55ca3c828f15d6b395728f20a3ad672ae51e05b828eb59cab947849e0a3ad672ae51e054828eb59cab94881720a3ad672ae51185c828eb59cab94781860a3ad672ae51e05a828eb59cb045721720a3ad672ae46285c828eb59cab94a08f20a3ad672ae51e043828eb59cab9300172163ad672ae51e05c75ace561ab94781720a3a3672ae51e05c828ce55ca3c2fe172363395728f0bf05c672ae51e17e0e81721dbad672ae51e05c75ace55ca58478172363ad672ae4bf05c75ace55c97e0e81721dbad672ae4bf05c75ace55ca582fc1720a3ad672b3d5c85c828eb55ca3c2523e60a3ad672ae4c385c876ce55ca3c2fc1719cab94b08f0bf05c828ce55ca3c2523e60a3395728f0c385c828eb59cab94781e63641975ace55ca3c832eb59cab94781d20a3ad672ae51e10f else 0x828eb59cab94bc8f21dbad672ae52c23c7f2eb59cab94b08f1d6b395729611e0f98d8eb59cab94b08f1d6b49672ae51e0ff75ace55ca584781d1d6b395729611e1f475ace58c2b94b08f1d6b49672ae51e0b475ace55ca5847832dd6b39586ae51e1bb75ace55ca5e4b08f1d6b49672ae51e04775ace55ca58478081d6b395729611e21b75ad259cab94780460a3ab672ae51e0f9828eb5a2ab94783e6363ad672ae51e01175ace55ca3c0e8046163ad672ae51e011828ead9cab94780460a3ad672ae523a3c828eb5a2ab94780460a3ad672ae51fa3c828eb59cab94788be163ad672ae51e0f6828ce594ab94783e60a40975aae51e0f98d8eb59cab94783d9d6b395728f07b07475ad259cab94783da0a339652ae51e0f6828f95d6b395728f20a40975aae51e0f6828eb59cab95008f20a3ad672ae51e1bf876fb1d6b395728f1f63ad672ae52c23c8d902dd6ab94783e605bad5728f07c87485902dd6ab94783e605bad692ae51e0f9858eb59cab95028f1d6b3959eae52c23c8d8eb59cab95028f1d6b39572a051e07482902dd6ab95028f22b41475ace55ca3c828eb59cab947832e0a3ad672ae51e027828eb59cab94fc8f20a3ad672ae51e0e3828eb59cab947871e1c3ad672ae51e1be75ace561ab94786fa363ad672ae51e1be75ace55ca3c37c1d20a3ad5728f0f28f9887051d6b395728f20a3ad672ae51e165828eb59cab94780620a3ad672ae51e1bb)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0x75ace55ca3c09e08238bad672ae51e21b75ace5972b947811e363ad672ae52ea3c75ad299cab94783e6363395728f07c87475ace55ca3c2623e5d6b395728f098874828eb597ab94783e60a3ad672ae4bf060828ce55ca3c2fc1e60a3c8672ae51e0f9828eb59cab9478402323ad65cae51e0f9828f91d6b395728f20a3ad5728f08a8f9828eb59a2b94783e60a3ad672ae52e23c828eb59cab94783e20a3ad672ae51e166828eb59cab94782ca0a3ad672ae51e0fd828eb59cab94783de0a3e9672ae51e0f9828ce55ca3c2aa3e60a3ad672ae53fa3c828eb59cab9478252363ec672ae51e0f98d8ce55ca3c2a83e6163ad672ae51e036858eb5ce3395728f20a3ad672ae51e1188c90b1d6b395728f2163ad672ae51e10e828eb59cab947844a0a3ad672ae51e2228a10b1d6b395728f21c3ad672ae51e10e858eb59cab9478082163ad672ae51e21b8d90b1d6b395728f2163ad672ae51e074876eb59cab9478076163ad73ece55ca3c8e90b1d6b395728f2163ad672ae51e118876eb59cab94780821dbad672ae51e21b8ad0b1d6b395728f21c3ad672ae51e112870eb59cab9478062163ad672ae51e222858fb1d6b395728f21c3ad672ae51e0f975ace55ca584780d9d6b9c672ae52c23c8b6eb59cab94b08f1d6b395729611e10e75ace561ab9478081d6b39586ae51e21b828eb59cb175728f20a3ad672ae51e0b48a0eb59cab94b08f1d6b49672ae51e10e else 0x7c2eb59cab94781d20a40b75ad2d5ca3c828fb1d6b395727ea38bad672ae51e074762eb59cab94781d2363ec672ae51e074816eb5a5ab94781d1f63ad672ae4fd074828eb59cab94781220a3e775ace55ca3c828fc9d6b395728f20a3ad672ae51e21575ace55ca3c074081fbbad672ae51e020828fb5d6b395728f20a3e375ace55ca3c82902dd6b405728f20a3ec75ace55ca2375ace55caab4780e5fbbad672ae51e21b829011d6b395728f20a3ad672ae51e10a828fe5f4b395728f20a3ec672ae51e0ff82902dd6b745728f20a3ec75ace55c8c57d8eb59cab94780f1ff3ec75ace55ca3c828fb1d6ab94784360a3f975ace55ca198d8eb59cab9478425d6b395728f084874828eb55ca3c21c4260a3ad65cae51e10985d051d6b395728f20a3ad672ae52523c828eb59cab947804a0a3ad672ae51e106828eb59cab95068f20a3ad672ae51e1b9828eb59cab930210a0a40575ace55ca138d8eb59cab947884dd6b395728f109874828eb595ab947843a0a3ad672ae50da1389f051d6b395728f20a3ad672ae51e123828eb59cab947807e0a3ad672ae51e210828eb59caf85728f20a3ad672ae51e0cd8d8fe5f63395728f20a40b75aae51e109828fb1d6b3957284e283ad672ae51e0398a0f85d6b395728f20a3ec672ae51e079828fb1d33395728f1d6b395728f0c1039810eb59cab947843a0a40b790ce55ca3c828fb19cab947880638bad672ae51e020) else (if page < 29 then 0x8d8eb59cab9478315d6b395728f06287475ace55ca3c1d0081d6b39572aad1e0c5828eb59cab93043160a3c175ace55ca3c828eb59cab94ea8f20a3ad672ae537a3c828eb59cab94787260a3ad5728f0bd0b9828eb59cab94366d20a3ad672c1d1e1aa828f619cab947886e0a339572aad1e163828eb5b0ab947886e0a3ad672ae555946828eb59cab9436316283ad672ae51e21b8d8eb59cab9478081d6b395728f03a02075ace55ca3c050081d6b39572aad1e02075ace55ca3c304082283ad672ae51e020828eb59cab9436082363ad672ae50d82075ace55ca1b0e8081d6b3957286c1402075ace55caab4360820a3ad672ae4c102075ace55ca1b3040822841475ace55ca1b8a0eb59cab94360820a3ec75aae51e11a828fe5d6b395728e238c14672ae51e0798e3051d6ab947846a0a3ad672ae51e11a001051d6ab947846a3941475ace55ca38828eb59cab94788e00041475ace55ca388e9051d6ab94784620a3c8672ae51e047828eb5a5ab947811e0a3ad672ae525a3c828eb59cab9478851d6b395728f0278398e2eb59cab94780e60a3ad672ae52423c828eb59cab947887238be175ace55ca3c810eb59cab947811e0a40175ace55ca3c828eb59cab9478116363ad672ae51e0398d8f85d6b395728f20a40b75aae51e118828fb1d6b395728d6363ad672ae51e0478d8fa5d6b395728f23640b75aae51e1188d8fb1d6b395728d5d6b395728f03a039 else 0x75ace55caac47886dd6b395729111e21b75ace55ca4147886dd6b39572acd1e02075ace55caab47886e0a3ad672ae51e11f8a0eb59cab94360da283ad738ce55ca1b8b7141d6b3957286e283ad672ae50d90e8c9051d6ab947847e0a3ad65cae51e11f001051d6ab947847dd6b395728f10d87975ace55cab047886e323ad672ae51e11f75ace5972b947847c003ad672ae51e11f8d8eb59cab9478439d6b395728f08707475ace5972b947843a3241475aae51e10e7a2eb59cab947886e323ad65cae51e10e75ace55caab4786d1f4b395728f10d874814eb59cab947811e0a3e9672ae51e0747d2eb59cab94781d0003e9672ae51e074828fa5ce3395728f1fc3ad672ae51e0207f0eb59cab947886e0a3ad672ae51e108828eb59cab947884a283e975ace55ca3c814eb59cab94784399cb2e5728f07f8748d8eb59cab947886e0a3395728f07f87475ace55ca3c1fe1d20a39c672ae51e0ff8d8eb59cab94783fe0a3ad672ae54123c828eb59cab94786f20a3395728f0bf859828eb59cab94367ea0a3e9672ae51e1f4828eb5b5ab947886e0a3ad672cb95c8da828eb59cab9436181d6b3960eaad1e21b8d8eb59cb045728f1d6b39608ae51e074828eb59cab94781ae0a3ad672b955ca3c828eb59cab94783be0a3ad672ae51e1ec828eb5ba2b9478439d6b39608ae51e020828eb59cb0457286dd6b39608ae51e21b000eb59cb0457286dd6b3965cae50d8c5)) else (if page < 32 then (if page < 31 then 0x11b1d8b395728f20a3b1672ae51e036764eb59cab94780820a3ad672ae51e0fa828eb59cab94787e6283b175ace55ca3c76aeb59cab947843a363a3672ae51e0208d9051cfb395728f2363ad73ece55ca3c828e7d9cab94780d9d6b9f672ae51e074828f99d6b395728f20a3ad672ae51e05f828e8d9cab947800e0a3ad672ae51a820828ec59cab94780760a3ad67cae51e020828eb59caaf4780820a3ad672ae50f02075ace55ea3c050082363ad672ae52223c75ace55ca444781d20a3ad672ae51e05d828eb59cab94787f60a3ad672ae51e0c0828eb59cab94786ca3241475ad015ca3c828eb59cab9488081d6b395729111e02075ace55ca26050082363ad672ae51e22375ace55ca3c4461d1d6b39572ab11e0208a1051d6b3957288e0a3ea75ace55ca3c828eb59cab94783f20a3ad672c195ca3c828eb59cab947830e0a3ad666ae51e00c828eb59e2b94780820a3ad672ad11e020828eb59cab945c0820a3ad672af51e017828eb59cab94460820a3ad672ae51e12075ace55cab547886dd6b3965cae51e1188d8eb59cab9478481d6b3965cae51e120828eb59cab94bc86e363395728f10d87475ace55caab4787e9d6b395729791e21b75ace55ca5e4361d0003ad672ae52f21b75ace55ca1b3f41d20a3ad672ae52323c75ace55ca3c4361d20a3e575ace55ca1b828eb59cab947847a0a3ad672ae54421b828eb59cab94828f1d93ad672ae51e21b else 0x828f219cab94781d1e43ad672ae51e074000f219cab94781d20a3c8738ce55ca3c828eb59cab94784120a3ad672ae51e206672ca55ca3c21c1d20a3395728f10087475ace55ca3c4021d20a39c672ae51e2018d8eb59cab94788060a3ad672bc95ca3c828eb59cab947834e0a339652ae51e047828eb5a5ab947843a0a3c8672ae51e0f6829025d6ab947843a3646475aae51e10e8c8eb55ca3c21c1d2363ad672ae54423c75ace55ca884781d20a3ad672ae51e065828eb59cab94ec8f20a3ad672ae51e0e5828eb59cab947872a363ad672ae51e1b475ace55ca3c3681d20a3ad5728f0f190e828f6dd6b395728f20a3ad672ae51e160828eb59cadd5728f20a3ad672ae51e143828eb59caa04782620a3ad6a8ae51e10e828eb59cab95102e60a3ad672ae4c282075ace55cab5478082363ad672ae4c282075ace55ca3c30a082363ad672ae51a820828eb59cab9478202363395728f03a02075ace55caa8478081d6b395729791e02075ace55ca3c1001d1d6b395728f040020828eb59cab948e0820a3ad74ece55ca3c828eb59cab93060820a3ad5728f08f90e828eb59cab930c081e8bad672ae51e02075ace55ca3c36a081d6b395728f08f90e75ace55ca3c30c0823645075ace55ca3c8a0eb59cab94781d1d6b395728f03c82075ace55cab0478082283ad672ae4c10208d8ec59cab947808238bb175ace55ca3c8d9051d8b395728f2363b175ace55ca3c) else (if page < 33 then 0x828eb59cab94788160a3e575ace55c9f4828eb5ce36b5728f20a3ad738ce55c8da8a1051d6ab947846a2dc1475ace55ca3875ace55ca3c0f200e0a3ad672ae52fa3c828eb59cab94787e20a3395728f03d8118e3051d33395728f20a3e875ace55ca3c828eb59cab947817a36414672ae51e0798d9051d33395728f23241475aae51e1188a1051d6b395728d636450672ae51e0798d8eb59cab94781e40046c672ae51e0798d9141d33395728f2363ad74cce55ca3c8d9191d6ab94784623645075ace55ca358a0eb59cab94788d40045075ace55ca3575ae999cab94781d2283ad74ece55ca3c75ae9d9cab94781d236450672ae51e0748a0eb59cab94787ea0a3395728f03c836828e999cab94780da3241475ad155ca3c8a1051d6b3957287a363ad672ae51e11575ace55ca3c22a1d20a3c975ace55ca3c828eb59cab94787f20a3ad672ae544a3c828eb59cab94786c60a3ad672ae4c200c8b7051d6b3c5728f22dc1475ace55ca318c3051d6b395728ba363ad672ae51e22e75ace55ca3c45c1d20a3eb75ace55ca3c828eb59cab94783ee0a3ad672c295ca3c828eb59cab947830a3241475aae51e1158a1051d6b395728b9d6b3966cae51e10e8d8eb59cab948c8f1d6b44672ae51e10e828eb5942b947843a363395728f08707475ad2d5ca3c21c1d1d6b39650ae51e10e75aca15ca3c21c1d20a3ad672ae4c1060790ce55ca3c21c1d1e8bad672ae51e059 else (if page < 34 then 0x790ce55ca3c0e811dd6b4b5728f03a04775ace55ca4b4781d1d6b395728f10a0748d8ce55ca3c0e8165d6b39572aa11e05975ace55ca3c0cc165d6b395729791e05975ace55ca5e0e8164003ad672ae52f0597d2ce55ca3c0e8165d6b395729491e07475ace55ca3c4101d1d6b395727e83a05975ace55ca3c0de11e0a3395728f040874828ce55ca3c1020d9d6b395728f04087475ace55ca3c1020da363395728f03a0368d8eb59cab9478462363ad672ae51e2358d8eb59cab948e8f1d6b3957291d1e074828eb59cab94783060a3ad672ae51e1b38d8eb59cab9478879d6b395728f10f074828eb59cb055728f20a3ad672ae51e0c4828eb597ab94780460a3ad672ae52381d828eb59f2b94780da0a3ad672ae512836828eb59cab947820636414672ae51e081828e719cab947820400414672ae51e0818d8eb59cab9478205d6b9c672ae51e081000eb59cab9478205d6b9c672ae51e0748d90519cab94781d23639c672ae51e0748d8eb59cab94781d00046c672ae51e07475ace55ca5e4781d1d6b395728f0fd0748d8eb5ce3395728f1d6b395728f03a0368d8eb59cab94780da0a39c672ae51e036828ce55ca3c0e80d9ce3395728f03a0368d9051ce3395728f23639c672ae51e0368d8f95d6b395728f1f2bad672ae51e074828eb59cab947841e0a3ad672ae51e211828eb59cab92fa182363ad672ae51e06075ace55ca3c0e81820a3ad672ae52a23c else 0x23641475aae51e11a8d9051d6b395728e20a3ad672ae545a3c828eb59cab94786c20a3ad672ae4c28038e3051d6b395728d60a3ad672c315ca3c828eb59cab94782fe38c6c672ae51e0798e31b1d6ab947846a363ad672ae51e11a0011b1d6ab947846a3946c75ace55ca388d8eb59cab94788e00046c75ace55ca388e91b1d6ab9478462363ad672ae545a3c8d8eb59cab94786c1d6b395728f0020038d8eb59cab930a00dd6b395728f0c28038e2eb59cab947800e363b1672ae51e0038d8eb59cab947a8f2363ad672ae51e23675ace55cab547800dd6b39572ad51e2358e31b1d6b395728d638bad672ae51e2350011c5d6b395728d5d6b3966cae51e1188d8eb59cb0c5728f2363ad672ae51e0bf8d8eb59cab946a00e0a3ad672ae51e0cc828eb59cab94786f60a3ad672bc55ca3c828eb59cab94783560a3ad650ae51e047828eb59cab94bc165d6b395728f08c07475ace55ca3c46a1d238c6c672ae51e0748d8ce55ca3c2301d2363395728f03a0038d8ce55ca3c46a1d1d6b395728f06607475ace55ca3c37a1d2363ad672ae52f23c8d8ce55ca5e4781d1d6b395e2ae51e07475ace55ca3c1aa1d2363ad672ae51e1fa8d8ce55ca3c3f41d1d6b39572aa11e1fa75ace55ca5e4787ea363395728f03a04775ace5942b947811dd6b285728f03a047)))))) else 0
  | 6 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x828eb59cac55728f05f000828eb59cab94dc8f20a3ad672ae552a3c17c0020a3ad672ae51e1cb828eb59cab94782f843800828eb59cab947821e0a3ad672ae51e0be14e0020a3ad672ae51e1af8d9051d6b395728f0d78008d8eb59cab94786be0a3ad672ae51e1af0e8001d6b395728f0d7874828eb59cab94786bc1b41475ae719cab94786be3241475ace55ca3c35f051d6b395728f0d790e828eb59cab953e8f01041475ace5972b94786be0a40b75ace55ca3c35f051d6b395728f0d78f9828eb59cab953e8f02e41475ace593ab94786be2841475ace55ca3c35f051d6b395728f0f090e828eb59cab94786bc1041475ace55ca3c4366be0a3ec75ace55ca3c35f051d6b395728f0f08f9828eb59cab94786bc2e41475ace55ca3c3ee6be0a3ad6ecce55ca3c35f051d6b39572a7d1e0be828eb59cab94786bc5f41475ace55ca3c3c26be0a3ad672c355ca3c35e0020a3ad672c351e1af0000020a3ad672c34d7c42828eb59cab94786bc00442828eb59cab9479051d6b39572a7d1e169001051d6b395728f0b4c1475ace55ca3c35e05c0041475ace55ca3c02f051d6b395728f0d79aa001051d6b395728f0d54147b4eb59cab94786bc004147b4eb59cab9479051d6b39572a7d1e161001051d6b395728f0b0c1475ace55ca3c35e14c0041475ace55ca3c0a7051d6b395728f0d79a3001051d6b395728f0d1c1475ad8d9cab94786bc0041475ace56e2b9479051d6b39572a7d1e144001051d6b395728f0a241475ace55ca3c35e29c0041475ace55ca3c14f051d6b395728f0d799b001051d6b395728f0cdc1475ace55ca3c3c22f80041475ace55ca3c17c0020a3ad672ae4f08be else 0x105205bad6ecae51e41475add99cab94783e60a3ad672c355ca3c0b80020a3ad672c355c85c828eb59cb0d5728f0fbc1475add99cb0d5728f23641475ace55ca3c17c002363ad672ae51e0be828eb59cab94782f83a00075ace55ca3c17c1d20a3ad672ae51e0be06d051d6b9c672ae51e0be8c9051d6b395728f05f41475ace55ca3c21c2fa0a3ad672ae51e176041051d6b3965cae51e0be82902dd6b395728f05f41475ace55ca3c1f22fa0a3ad672ae51e1760b9051d6b3964eae51e0be8b7051d6b395728f05f41475ace55ca3c2ac2fa0a3ad672ae51e0e7041051d6b39572aad1e0be828fe5d6b395728f05f41475ace55ca3c2a82fa0a3ad672ae51e0e70b9051d6b39572a9d1e0be828eb5c1b395728f05f41475ace55ca3c1ce2fa2841475ace55ca3c17d051d6b395728f0c10be828eb59cab94782f81041475ace55ca3c4362fa0a3ec75ace55ca3c17c0020a3ec75ace55c8be828eb59cab94785f85f41475ace55ca3c17c1700041475ace55c8be0b9051d6b395728f0fb8be828eb59cab94785e45f000828eb55ca3c2f22fa0a3ad672c355ca3c17d051d6b395728f0a90be828eb59cab94784f45f426828eb59cab94782f800426828eb59cab9479051d6b5b672ae51e0be001051d6b39572a111e41475ace55ca3c17c0300041475ace55ca3c019051d6b395728f05f0b9001051d6b395728f05cc14780eb59cab94782f800414780eb59cab9479051d6b57672ae51e0be001051d6b395729dd1e41475ace55ca3c17c1080041475ace55ca3c085051d6b395728f05f0b0001051d6b395728f05841475add99cab94782f80041475ace586ab94780020a3ad6ecae51e0be) else (if page < 3 then 0x828eb59cab94787dcfa000828eb59cab94787d20a3ad672c9d5ca3c1f20020a3ad672ae51e0f90010519cb275728f07cc1475ace57aab94787dc0041475ace5782b94780020a3ad6dcae51e1f70000020a3ad6dcae51e41475ace593ab947835c0041475ace55ca3c1ae0020a3ad672c9d5c8d70000020a3ad672ae46bc1475ace55ca3c3ee2c20a3ad672ae51e1f7347051d6b395728f0fb85c001051d6b395728f02e000828eb59cab93ee1723641475ace586ab9478002363ad672c355ca3c828eb59cb0d5728f03a00075ace586ab94781d20a3ad672c355ca3c06d051d6b9c672c355ca3c8c9051d6b3961aae51e41475ace586ab947843a0a3ad706ce55ca3c041051d6b83672ae51e21b82902dd6b3961aae51e41475ace586ab94783e60a3ad706ce55ca3c0b9051d6b83672ae51e1f78c3051d6b3961aae51e0008c3051d6b395728f20a3ad706ce55ca3c1300020a3ad672ae51e098828eb59cb0d5728f017000828eb59cab94780b8003ad672c355ca3c05c000003ad672ae51e02e828eb59cb0d5f2ae51e000828eb59caf95728f0003ad672c357cab9478000003ad672be55ca3c829015d6b3961aae51e000829015d6b395728f20a3ad706ce55ca3c1260020a3ad672ae51e093828eb59cb0d5728f036000828eb59cab94781b20a3ad672c35732b94780020a3ad672b995ca3c828eb5cd33961aae51e000828eb5cd3395728f20a3ad706ce55ca3c10f051d6b3961aae51e0f0001051d6b395728f07841475ae0d9cab94787b40041475ace55ca3c3db1420a3ad672c355ca3c828eb5bb3395728f08741475ace586ab94780820a3ad672c355ca3c437051f63ad672c355ca3c else 0x828eb5ce3395728f02e45b828eb59cab94781720a3ad672ae51e10e0b9051d6b395728f033820828eb59cab95568f02e4147f2eb59cab94781720a3ad672ae51e0f90b9051d6b395728f03385c8a1051d6b395728f02e41475ace55ca3c3041720a3ad672ae51e05c041051d6b395728f10d85c828eb59cab94785f82e000828eb59cab92fc17000414672ae51e17e0b90660a3ad672ae51e05c0010660a3ad672ae51e4147a0eb59cab947817000414786eb59cab9479051d6b395728f02e003001051d6b395728f001c1475ace55ca3c0b81640041475ace55ca3c0b3051f63ad672ae51e05c001051f63ad672ae51e000828fb19cab94781720a3ad672b095ca3c0b80020a3ad672ae529a3c828eb59cab95528f02e000828eb59cab947881e0a3ad672ae51e05c085051d6b395728f02e053001051d6b395728f0fbc6c828eb59cab94787dc0046c75ace55ca3c3ef051d6b395728f0fb874000eb59cab94787dc3a41475ace55ca3c3ee0da0a3ad738ce55ca3c3ef16e0a3ad672ae51e1f7828eb59cab94787dc8741475ace55caa74780820a3ad672ae555a3c3ef051fcbad672ae51e1f7828eb59cab94787dc7cc1475ace55caa74781720a3ad672ae553a3c3ef1420a3ad672ae51e1f7828eb59cb275728f08741475ace55ca3c3ee0820a3ad672ae51e21b3ef051f63ad672ae51e1f7001051f63ad672ae4fb800828fb19cab94787de25c1475ace55ca3c3ee00225c1475ace55ca3c00112dd6b395728f0fb80000112dd6b395728f20a3ad672c9d5ca3c2580020a3ad672ae51e12c000eb59cb275728f096000000eb59cab94784b20a3ad672ae51e1f703a0020a3ad672ae51e01d)) else (if page < 6 then (if page < 5 then 0x828fb1f0bad672ae51e000828f85d6b395728f2364147d8eb59cab9478002363ec75ace55ca3c828fb1d6b395728f03a0007d8eb59cab94781d20a3ec75ace55ca3c06d051f63ad738ce55ca3c8b7051f63ad672ae51e4147d8eb59cab947843a0a3f975ace55ca3c041051fcbad672ae51e21b829015f63ad672ae51e4147d8eb59cab94784240041475ace55ca3c21305205bad672ae51e042828fe5d6b395728f109800828eb59cab947884e0a3f97d8eb59cab94791420a3ec75ace55ca3c82902dd6b395728f0874147d8eb59cab94780820a3ec75ace55ca3c4371b20a3ad672ae51e0f90011b1d6b395728f07cc1475ace55ca3c1f21d0003ad672ae51e0f90e9051d6b395728f07c836828eb5ce3395728f07cc64828eb59cab94783e60a3ad672ae51e10e1f3051d6b395728f0bf020828eb59cb2e5728f07cc50828eb59cab94783e60a3ad672ae51e1561f3051d6b395728f07c820828eb59cab947886c7cc147d8eb59cab94783e60a3ad672ae51e1541f30b20a3ad672ae51e0f90010b20a3ad672ae51e000858eb59cab94783e400000858eb59cab9479051d6b49672ae51e0f9001051d6b395729611e00075ad259cab94783e40000075ace55ca58479051d6b395728f07c811001051d6b395728f008c1475ace55ca3c1f23d80041475ace55ca3c1ed05205bad672ae51e0f900105205bad5728f07cc1475ace55ca814783e40041475ace55ca81479051d6b395728f0f20f9001051d6b395728f0df41475ace55ca3c1f224e0a3ad672ae51e0f91611b20a3ad672ae51e05c0011b1d6b395728f02e41475ace55ca3c0e8170003ad672ae51e0740b9051d6b395728f02e036 else 0x828eb59cab94780d81041475ae719cab94780822dc1475ace55ca3c041051d6b395728f087020828eb59cab94780a01000075ace55ca3c0500820a3ad672ae51e1820400020a3ad672ae4c1020000eb59cab947860810450828eb59cab947808000450828eb59cab9478002283ad672ae51e020828ec5d6b395728f010000828ec5d6b395728f20a3ad746ce55ca3c0400020a3ad73ece55ca3c828eb59cab947808001c1475ace55ca3c0400760a3ad672af55ca3c0400020a3ad672ae52223c828eb59cab955c8f010000828eb59cab947888e0a3ad672ae51e020019051d6b395728f010017001051d6b395728f10dc6c828eb59cab947886c0046c75ace55ca3c437051d6b395728f10d874000eb59cab947886c3a41475ace55ca3c4360da0a3ad738ce55ca3c43716e0a3ad672ae51e21b828eb59cab947886c8741475ace55caab478080003ad672ae555a3c041051d6b39572aad1e21b000eb59cab95568f10dc50828eb59cab947886c00450828eb59cab9436002283ad672ae51e21b828eb59cb2e5728f087000828eb59cab9478438003ad672cb95ca3c21d051f4bad672ae51e21b001051f4bad672ae51e41475ace5972b94783fc0041475ace55ca3c1ff051d6b395728f10d859828eb59cab947886cfa41475ace583ab947886c0041475ace5822b9479051d6b3965cae51e0c5001051d6b395728f062c1475ace55ca3c4362e60a3ad672ae51e21b355051d6b395728f10d820001051d6b395728f010000828eb59cab943608238c147d8eb59cab947800238c1475ace55ca3c82902dd6b395728f023800828eb59cab947811e0a3ec75ace55ca3c0720020a3ad672ae51e039) else (if page < 7 then 0x1051d6b395728f10f41475ace55ca3c06c0460a3ad672ae51e03603b1b20a3ad738ce55ca3c0011b20a39c672ae51e0008d8eb5ce3395728f20a3ad738ce55ca3c0e80020a3ad672ae51e074000eb5ce3395728f03a000000eb59cab94781d20a3ad738ce55ca3c06c0020a3ad672ae51e036001051ce3395728f01b4147caeb5ce3395728f0004147caeb59cab9479051d6b9c672ae51e0f6828eb5ce3395728f030000828eb59cab94781820a3ad738ce55ca3c3e91c62841475ace55ca3c8a1051d6b395728f03c800828eb59cab94781e63241475ace55ca3c0231420a3ad74cce55ca3c001051d6ba6672ae51e46c8a1051d6b395728f00046c8a0eb59cab94791420a3ad672ae51e074001141d6b395728f03a450828eb59cab94780da2841475ae719cab94791862841475ace55ca3c8a1051d6b395728f08a800828eb59cab94784563241475ace55ca3c01916e0a3ad672ae51e22e001051d6b395728f11745b8a1051d6b395728f23641475ace55ca3c21c002363ad672ae51e10e828eb59cab94784383a00075ace55ca3c21c1d20a3ad672ae51e10e06d051d6b9c672ae51e10e8a1051d6b395728f08741475ace55ca3c2ac43a0a3c875ace55ca3c21c0020a3c875ace55ca3c828eb59cb295728f087000828eb59cab94788060a3ad672ae51e10e08f051d6b395728f0870f68c9051d6b395728f0870008c9051d6ab947843a0a3ad672ae54423c21c0020a3ad672ae54423c828eb59cab947878887000828eb59cab94786d20a3ad672ae51e10e131051d6b395728f0870b98d9051d6b395728f0100008d8eb59cab94780820a3ad672ae51e074040001d6b395728f03a020 else 0x4718d9051d6b395728f23641475ace55ca3c2300020a3ad672ae51e1188d9051d6b395728f001c6c828eb59cab94788d40041475ace55ca3c46a00238c6c75ace55ca3c0011b1d6b395728f08c0008d8eb59cab947800c0046c75ace55ca3c46b1b20a3ad672ae51e0740011b20a3395728f03a41475ace55ca5e4781d00041475ace55ca5e479051d6b395728f0fd074001051d6b395728f0fd41475ace55ca3c0e811e0a3ad672ae51e0740b2002363ad672ae51e074000002363395728f03a00075ace55ca5e4781d0003ad672ae51e1fa0e8001d6b395728f03a047000eb59cab94781d02cc1475ace55ca3c0e80d800414672ae51e07406c001d6b395728f03a0368d9051d6b395728f01b0008d9051d6b395728f00046c75ace55ca3c06c0000046c75ace55ca3c001051d6b9c672ae51e41475ace55ca474780d80041475ace55ca47479051d6b395728f10f036))) else 0
  | 7 => if page < 1 then 0x23641475ace55ca3c0000000046c75ace55ca3c0000020a3ad672ae51e074000000003ad672ae51e0740000020a3ad672ae51e0360000020a3ad738ce55ca3c0000022841475ace55ca3c0000020a3ad672ae51e10e0000020a3ad672ae51e0200000020a3ad672ae51e21b0000020a3ec75ace55ca3c0000020a3ad672ae51e0f90000020a3ad672ae51e05c0000020a3ad672ae51e1f70000020a3ad672c355ca3c0000020a3ad672ae51e0be0000020a3ad672ae51e1af else 0
  | 8 => if page < 1 then 0x41475ace55ca3c else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 51
  | 4 => 1101
  | 5 => 2235
  | 6 => 483
  | 7 => 17
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 2048
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 11)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (11*(k+1)) i)

def bucketCount : ℕ → ℕ
  | 2 => 3
  | 3 => 32
  | 4 => 613
  | 5 => 1348
  | 6 => 338
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 11
  | 3 => 118
  | 4 => 2207
  | 5 => 4855
  | 6 => 1218
  | 7 => 51
  | 8 => 2
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x50001 else 0
  | 3 => if page < 1 then 0x3100340000000100030024000000000001001d00160003001b0001000100000004000100010001000f00030020000a000100070005000f000a0000 else 0
  | 4 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x10000b00010005000500030000000100000009000500000008000600150003000000050001000a0000000c0005000f0012000200020000001000000004000300030004000f00150000000a00050000000200020006000100000005000100000001000200020002000500060004000d00000000000300100000000b00040000 else 0x600010000000a0009000200000005000200000003000b00000008000100000000000000000004000c000b001300050007000e0006000100010006000000070000000900070000000500070000000200030000000100010001000c0006000100000003000000000002000b00040000000300000007000000050009) else (if page < 3 then 0x5000200000000000100040000000900010028000d0002000300050000000200010000000500060001000600020001000100010002000000020024000100070001000500020000001b00000000000000010006000c000300050003000a000e00000010000700070000000f00000003000a000100060008000200030000001a else (if page < 4 then 0x700040007003c00210009000800010000000c0004000000670006000900190007000a00030000000a0002000600040001001100000000002000000017000900130006000000010000000a00040000000d00030000000600000005000a000a000200110002001d0008000100070000000a000000050001000400050000000c else 0xa00010000001000020003000000210008000a00080006000000010000000800040001002d0004000d0003000000100003000000080016000c0001000200000017000500000005002400050000002800030004000e001d00000002000e00000004000100000014001e00010000000900020006000000060005000100010021))) else (if page < 7 then (if page < 6 then 0xf000500000002001f00110000001000010003000a0000000400060000000400070008001c00010005001200010002000100210006000000000000001a00070003001f000700140025000100010000000e000a0000000200a90000006900020003000000030000001000090000000400060005000000020009000000000003 else 0x400050005000e00070003000100000001001000000000001b00130000000400110003005c0000000f0035000b000b0006000000010004000800000009000000190012000700020010000000180013000d00180004000100050006002b000c000700270000000c001b0003000200310011000b000400000002000c0000000a) else (if page < 8 then 0x7000b000b00220019000b001d0000000000210000002400000001001000010005000b000200000001000e0000000d000400110000001d00130003000b000200000007000500090011003100620018000400030002001200110000000700020004000a002900010002000000010008004800010000001f000000120001003b else (if page < 9 then 0x6000e00010008000e00000002000300020002000e001e001a0001000300050004000f00060001000b000400050027001a0022001800250010001200060000003400140004002d00380005001000020045000000000006000300020000002d002600000005000a00030018001b0005002c0005000900000004000800030031 else 0x1000130000000000020005002f001e001500000031000000030004000c000f0006000b000300000011001600190000000600000000001000000019000d000a00140028000000570000)))) else 0
  | 5 => if page < 22 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x10002000000010001000000110005000f00030000000800000006000400040005000100090001000000030003000000070011000800030003000400070001000b0000000500080005002900070004000400030006000b000000000003000000030010001b000c0002000000000003000000100000000000020001000b0003 else 0x400150002000600000000000000060005000500050001002600000020000f0007000400070004000600020000001500000000000000010001001100000004000c0004000900000021000b00020003000f000300070000000100090000000000000018000600080007000d0000000100020022001700010001000100010000) else (if page < 3 then 0x60012003f000600010003000100110000000100010000000200000002000200030000000f00080001000100000009000100060003000000010000000300080003000300090004000500010006000100080005001200010024000300010002002600000000000000020000000200020000000a000100000002000200020000 else (if page < 4 then 0x20006000300020018001000020002000000000000000b000300100032001200020008000200050027000000070002000e00050004001200020002000200020005000500010000000a0000000a00010000000000020001000100070007000700040003000100070005000000020000000900080001000100020002000e0017 else 0x40000000f000300050000000100050007002700040006000000140000000a0001000900010005000c001300020005000200000000000c00080000000c000000000005000100070000000500050000000f0000000100040008000200000001000000070007000d000000020004000100090002000a00050012000000070001))) else (if page < 8 then (if page < 6 then 0x500010000000b000500040005001200060000000000010001001e0002000200080000000000000008000a000100080000000c000a00040008000000120004000f00000002000000050000000e00000002000000050001000000000001002000000001001600040008000e0001000000050003000400010000000800170016 else (if page < 7 then 0x3000200000004000900000004000d002200090002000c0009000f00060007000f00050022000e000b000200070000001200000003001b0000000300030000000c000b00070001000000050006001a000500020016000000000000000a0002001700080001000300000007000a00000002000200010000000300040004 else 0x100000000000010005000000010001000300000023001500010000000300120004000400020000002000000000000900000000001200030000000a00090006000500020006000000010004000000040000000000030006000700000000000a000400020002001000030001002f000700010000000c0000000f000200010003)) else (if page < 9 then 0x2300000019001e00010001000e0001001b0001002d0000000a0000000100020004002700030000000200000003000700010023000200080003000e0015002100050001000400000003000000010001000c00000000000000080003000e00000013001100000002000000060005000300000000000000050003000000000013 else (if page < 10 then 0x4001c000200010001000000050008000100010006001c0000000000140002002000050002000c000600210000000b0017001b0007000100020001000300020002000a0031000e0001000a000900050003000000070000000000000002000600000002000100010001000000010009000000070006000e00110001000e0004 else 0x50004003100150000000100040011000500050000000d0002000000040000000b000100070000000e0018000e00000006000000030001000500000004001c001700000000000b0005000200010004000100000017000000030000000e0007000a000000170019000200010001000d00070002000700020014000600040011)))) else (if page < 16 then (if page < 13 then (if page < 12 then 0x1200010008000e000b00030000000100000002001500020004000d0002000e0000000d00090001000000050008000000050000001100050001000000030001000b000500020004000b000500000003000300030004000d0000000c00030000000f0000000e00000003000f0000000400000000000600020004000b00030004 else 0x5000000000000000b0003000d000000010002000000000000001a001600030003000100010008000d0005000c00030000000300000009000b0000000400010012000100050000000500260002000f0025000c001200170006000000020018000d000c0000000b00070003000400030006002d0006000200000001000d) else (if page < 14 then 0x1000c0021002900010010000000040003000600010001000c0005000a000500010003001c0002000a0018000b00030062000800030000000000000005000b000000020000001a0002000700000019000f00010000000a0001000b000f000200010000000000050003000c0000000800000006000d00000003000800210003 else (if page < 15 then 0x42000300110002001000060006000000040009000000060009002900000031001e00000026001b000000050002001e0000001a00060012000000150003000000020000001200040000000e000900070022000e000400000005000600000028005200040023001b000600030003000a000200340000000400090018000d000b else 0xc000b0006003b0008000300210002000700200005000c00000012000e00030000000400240022000500020000003700000001000200000002000000000015000000040016000600010004000200080000000f00000007001e000b0001000400100000000f00040015004d001400090005000900170005000000290025000d))) else (if page < 19 then (if page < 17 then 0xb00020012002a00090048000400070005000100160012000a000000050002000000010005000000050000000000010003000500030007000800040000000200000008000500080023000d001c0003000000050000001500000005000200030001000100010049000200000000000000660000000000070003002100010000 else (if page < 18 then 0x7000f000900000016000300080000000e00000020000900000006001d0004000200080001000400230000000000130007000800220004000600130019003d000b00030006000600060008000c000e0002000200090004001500000015000000030005000200690000002800000004000300000011001e0009000800040010 else 0x1000b00160000001100140009002a0017002b0035000a001200140000000e0006000b00030002003300000000000b000100030000000e002400000020000b000c000000040005001200310006000a000300120000000200490011000000040002000200050006000000000012000b000d00130013000600060029009b000a)) else (if page < 20 then 0x8000d00040015001f0021000100000002001d00050077002e00080007005900000007000400040004000c00310007000b0018000500160000000c001d0008004e00000008000500020005001d000a000000030001000300000022000000030000000100070001000f000600690002000b00190065001700060023000f0008 else (if page < 21 then 0x1600100004000400010001000100000046000200300000002300140000001f0006000e0021002f00000000004a00000002002900110002001a002200120002003700050024000a0008001a002f000700220000004100210003000a0011002000060015000a00070005001d000a001c0000001100030023000200130011001f else 0x1000000020012))))) else 0
  | 6 => if page < 6 then (if page < 3 then (if page < 1 then 0x4000000050003000e000300160002000000000000000e0001000d00000002000a001b000c0007001100030000000000090009000000060000002a00060003001c00030000000200050004000800010013000f0004000400000002002e00190003002800000001000f00030007000200200005001200040005000300060006 else (if page < 2 then 0x300000000000000000001002f000400170001001100120000000e000600000001000100060003000400000001000f0007002d0001000a0015000c000b000000000012000400000005001800080017001100240004000000000005001500100001001b00010004000200000009000200090015000100000002000300000004 else 0x1d00180003000f0000000e000c0000000c00370006000700010000000400070009000d000300090005001000000000000100090002002200050001000100000002000200000002000300040014000d0016000a0002000300000006000f00000003001600050002000900040006000700000005000000010008000000190002)) else (if page < 4 then 0x13002e0010000600570000000100010000000100020000000b00010002001f0002001c0017002a0033003600020002000500010012000700050002000000c400000002002c0033000000000003000000030009000a0001000a000700260006001d000c00010000000f0000000c000000160000000500110000000900050000 else (if page < 5 then 0x30006000f0010000000250007001400010002002200130000004100010003003a00800000000500000008000a001300010000000e000f0005001e001d0005000900020015000000010000000500110005001b000200020004000500110005000b000000110000001f000c000c000e00270038000000070006000500000003 else 0x1b003f0004001d0010000b001a00030008000500210085007300480002000000040010))) else 0
  | 7 => if page < 1 then 0x100150000000000000002000c0000000000000003000f0000000c else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x20000b000800100000001b00140000000000180003 else 0
  | 3 => if page < 2 then (if page < 1 then 0x6b01280122000001080000007b015c0070011c003b000c000800500103010a00530028016d0109017800480043001b0000004c00d80188006001500120000000580170000000f8009800180000011d000001180148011300000024008b00d30083012500680164007300b50092013800000140009b0190015800e80112 else 0xdc003801800010000900b300a8005b012400880160013a00b80000012c00c0018a014c00030000009000a30121017200f000000000007800e001320149000000a0000000cb013500130002014100000000017a00000000016c0064010b0000011100a90030000000000080) else 0
  | 4 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xeac000008cc000000001160000000000f620240137305901130143b03401c5c06801d3c192500001f0813800f6a036b05000670020016781ab809f02080012008a01ea00bc818bd18a40c1014401dc819c8073b13a4053c0cc90f0c1f1b100a05e3204021e917b808e00671043021440dd00bed11980288000012730fdc05c3 else 0x1b2407c81cfc000004bc07930fac00b80000000005bc00000833056417521b0c1d8a1a480f7a03800e600190002c0000000000000bfc00000000000000000000101818700b7404f80000000000000000096810e800000fb9000000000000000000000cb815b31e28027c000000001c791c98213d0000000017e8003014f00000) else (if page < 3 then 0x1a381cc804a31a59162400f00000000007b01d2c1c30218b0f5819621c000000113821a0130401800000000011f006880000008314600000000000000cfd0f3b1f490b44046b02dc010804dc160c0f1d024c05381eed037d191a00e31f3300002108000021a816e4078813f309b8000015f01ff01ee413f8001a10b000002120 else 0x19a300000000000000000d2111ea0328226100001ae816b5185c0e481b2c1b8000981ed014530a60193b18f402581b010d8019b40860163802f419e8000011d911d31058000010b803300d99000000081c950fa00820002319a2163214bb1dd306c80000100402cb05f101580b7c1fc8205c16ad0c6c1ed10aa30b080a6a16fd)) else (if page < 6 then (if page < 5 then 0x9f800000f1111a00322000020901b90000014610000161020fc01e000000e2818b402b000621108029813181d6b05481ea215300000055014d809fd03501ae00d39064800b00c3b09f10000058801d81b590000003c00cd0ca411fb0cf400001a341bd014aa1a39000014001089000002e005d3185203980000075b164b else 0x8831ff4000000d213190ab20b5808480e490da202f814901d181cb820ac17b4208c16351021000000001b780f12132b07ec000012e80ff10000000016081ee51979000009c00a280cd906b0202800aa0420000009e4160421f8158c0d2400000f6c20d306431e60189302490000193216fc0e900ed803a3000000001c0c0000) else (if page < 7 then 0x20d81fe4007800000fe8015000f3000012281ffd000000000000128002180e3c1ef0000000001ed817cd04031a83000000000370066000000000000018a207d818880cc109731835000013c019ec000000000d78215c0fe203180fe109b21593039c1d441bfc043b00510000000013500f7817f0224807a000691aa80c8c05a8 else 0x14a821d91a5414f8184a00000abb1a3211f10c71062a02d9188d1b600d021ce00ad00ba011e81b881e0418cd0c1c19d00000143a18a803e805931e910c48117011a805f30e6514f41f300000196a000018081038050803f8183d0000000018c82034087c182205330c001bc40afc0000000001a80000000000000000207d0000))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x1f00000051500000dfd21e020b905cb1e101f701a9305280091079b0ae30d1405180a20056c17350000114000001f891cdb00000065222a172400000e98164509300cc01a601f4000001c3c1d40042b169d1d341deb067403130434195c00001b3c04b0182800000751107c0f2209430de116cb13c809ca0ce306d316000000 else 0x89400000000069b087000000348070b13e800380db5133815780e1d18100edd0000091c22500529000018f814820f3a000004480000029c12480da01fdc11200e09000016d01d90189000d1084300001014000020e00998057811e120a0000006931aea127016521db8178a0000000006491834048007a80eb10d6d1e05) else (if page < 11 then 0xde800d00df40ba91cf00a42000000000000000001c80eeb0f28199806b30c1812f8086c00390d50172d13a00910211819880bb015440ff91c690d48016016da002916181e540ab000c8000000001300188409800c2004181891000000940c7810b400000000000000000000000016ac06e317bc000013db0d3c21ea00000ac3 else 0x39301680c44132000d902c01da20988088b10a40a3c2160000018b816f40a291d8d05430b010000066900001858220a0000198912031ce80de022400cfc07300be0199916ca10a81cd2000000000e1a00001ab0146808f80f0900001d5c0000000000001ddb18481dd007e00000000000001c10000016dd1c2c05581e322148)) else (if page < 14 then (if page < 13 then 0x5ab14b009cb05c01c240000062812b8192800000148039000a118e01701179c12c005e0128800001b10000010bb1020057020b31520174d140c21ab000020cb001116ec040817ad12d417fc04781ec51e6803ab09c20ff405530a00170b0c5806300c34009c000002a800001e08131203eb067b0dda0c641d711a5003231f60 else 0x308179803781679147808b00cb5064b0c1317080028038c1a7021100c68090019e01a4018e112a01ef200000ed10d2c11680584000003d80c30215d06001c041a101aa400000000019821f100ab1e7904cb00001d201dc3129317d005201958069800001f210cea0b881a98195000000bd017800790000013c300001db00000) else (if page < 15 then 0x1aa510111bb81f711c2819c2001b21240b601230000016141a7d00a01e6b1700189817f4000000800000004810f813aa0ebc064000001470204804230a501fb1186414a3171219850a7b1a4104640ab91dbb20380fec12681b1d0d401529000019940d19150b000010c81e75166101ab01400130216314e00af00e500e2403b8 else (if page < 16 then 0x1a09114800000850149813a500000cf121f00cb40954179004310b480b240d98000019dc000018990f72000003741d5106f80e780ed91f4a02610e641fd0138817c406680fd820101d141118000015f31cf308e3000016ba158007d0047012fc0000000019951c851fbd0760006818da162814c81cd8211b21c015680cf003c0 else 0x1ef90ca90e011310203c171d179518b50ac8076b1c141e631560000000f814010c401f581d84025b100019f917a51a4c10080a1a109300002208126013fc1d4b21bb107010d818b0000017a00f3000000d8c12640000000010281a2819b00b381f201428000005b311b815a31f1000000959065319f00fc80d5d09d211e9))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0x6f30dbd1a5c0000220408181bd802eb1a2400ac15d00d31133c06e00c3a11781f1a0ffc1cd01bf015b81ac8107103b014cb21e80f502098185d1e5b1ea1000018180a3d0ef31278089802bc02331f2c00000b09000021681a90151018dc11da05d00170000003fb19b81b400f6000e800e2080306c0221a213c0c08156c1e78 else 0x1333196019720cfb000021cc159804611758132815c0009a00a20a800000166c1be40ca80000000008281ba000000e8d03bb1c20165b105402d00e400830038915bb0ef817c80e5b1b7c101a13bc141819140a901c1c04a806c30da31a2c0e081de50d7d12581cac000000000cec160900000000210422280000202c0a0c13ab) else (if page < 20 then 0x1a991b840c901d080280066c10101bf41c5015c115ac02200c28000010b21ea8129b0d9105981a14185015180918000000000000008c1a4a0f010bc005100ba81cc018600c121e5d068317c016b216c00c0c21e220c01f2808d801a0144b00001714000018201e090e9c15b002500e6c1c081804000000c31611136c052c0000 else 0xad203580e2c1b11044c1df01cb11a7807f80f241fa40a3010501af81b741a880ce00d0801001fc00d71063400c4226000000ee100bc17d80b3310e0051110341bb00b18000000e000001b1820e21e5112a803710000000003d00000172c0f7007b8000017b009db07981fe800601ae4150011f801281bcb0270162016881340)) else (if page < 23 then (if page < 22 then 0x1f9c0e342238157102e81bec22091d651aad000011c807581b2516e00b980000104800000ecc1150000006f00ea01741102400500b4002640f4c1c381be0000000000b9501781e920000000000c01aec139811e213b419ea108006380000000015e80e701943094c000009400631222005681f840c2400001b981be810831c74 else 0x37c04c0036807180efc0b2819f811580d7b05b0003321781e1809280f91219c06b800001408087814590ec1131c0f4015d801f81768000010880000163a000000001fd10c381548202407f41c6400000ce900000ee405a30f8803c80bb812c8059c0cf8005a05c800000000155400000f840000046817f805b80118222215fc) else (if page < 24 then 0x8b8201220181c881eaa00dc0fa320f42242009903a01d8121c216f51880003218c014e81eb01f720fa20ff000b51d3814d0020817701db31d7c18c40c7915d9126b22620e80131315380edc1a080fd001d000000fb8146a00000338000003001bdc00000cf921e101c003f4065802a320ec0fb420931d590ee0041318a019f4 else (if page < 25 then 0x1ac900c5120807f00aba15a11ca400001d0021b11378183c11280c8017a81930049b0de30d441f6c1ee80bd112d8072010980bd4057b223014c016bb0808219316d10d7a040000000440189b04541f480e8110431b4804280000006c155816e813ca0000000007bb18c50ff8074b15a0000006eb163005230fc90a982060 else 0x460008809900d2506a00bdd15db20ed13940c9c00da13e01fe0007c08e808a80908102910f00a5b1c180aa810c9219012e0000000001b631f4112381b41207516341b5009c8036018d010cc216a17bd129818141ad81f180a700ad8000011100a320d70032021d8000003f01a301ad01d7912b41e9000ea1918038318e8)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0x14620a23097800001d2811b00f080000040c05a00dc91480108c1afc1e80000000000000000010d0000000001ac204830db0147a0cd5005b19a80580161d1d54222100a41bb3000000181abc0e6108f0070818d1000009d8000004c400000000021022181f4215c8000000f2181d000009e00df509e8038810c318e900000a68 else 0x678093804d821da049000101683000016c500001b3d05db223a0a101f030af200001b201a6808d30c0901aa219800001a041348205418440000186a0b5019a91c44040909580040133021b0037912002214057403db1c4817cc00002188000007c000001af007d415c9000000001d1c0920009d000000000000130b00001ba8) else (if page < 29 then 0x1c40000019491360167012330188045b0014081009e90fd900820858164003e01ef81d980e120f48000007280f99224109480e001528061000001e4805e9171800a80c50000000000dcc0000096000d4000016a002530710138300000b14168b0000040d19080b68182c124312fa04351865206c0c601afd09b311d20f5b0909 else 0x7700a1c192c00000a721dcc225120b207401df20f380a40078221701b6d0d580d820f0218ac01b01df805f005e800a909501b3400d5000000002131000018cc0375000019000cf521aa11d81eb818000dc817c5171920080fc000641b751f78048816440bf00458169114b403f121b806081e741b1c000021500f10026004e0)) else (if page < 32 then (if page < 31 then 0x7541a7c0c9410011fac0c542229206d05f81a790de21b5819801a250110058b1f50029918ad10680000144408c0000021d4102a00891e2317341fb41d48053012180ced09a80a080dd11e9c0000026b13fd023b11f412131ec820e3000001e80fe90a4800000ce8028b1ac0013800000f180000089005f904f000001bf819d8 else 0x212c09d304d0118806db0da806cb1b001e39000005d80c880e201210187812f003d30f541ad102901a1813d112d004eb1190054b0d380e15221916981ce407ab1f91204c07c3110013580ba4064a08400fd10dc01f321a12171014b8157914b207cb0d20000018680d03141b03920874165100ad00001e8c01b80000033c03a8) else (if page < 33 then 0x93306a80c84164811c01b6c1a1914300f420d55218009d00f5a1fca083807230620061c02ea1f9d1b491ae20e41168014200ea41aac0d45000000001da9077815e007dc0d4900000000000000000000007003820ab8194200000000000018d809a01a8c0cc81dea00d820f50b000ae81e4300000090000000000000 else (if page < 34 then 0x1ca50e580880000000eb17781a2a07fc203000610000225c20bc162109630cb9171b0704121b0ddb000000200049039909b00bf81a71125316581668000014140bf91af406d0002213d400000ce10000000011e00000156415e1173c1a610000000000000000000004b8118000001aa0148800000000132317e000000000 else 0x1725127c0b640b850cf31d300228078006900450000009c31f3c0a8b157007b420000d9c0fe01f5a12200d601c341390106418f018bc176205fc00001a80)))))) else 0
  | 5 => if page < 76 then (if page < 38 then (if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1b800378046300000db400001a30351814f53620106d000000000000040b00003762221800e10440000002c300002980131200002fd80000000014dd00002aea1f604520146100001479277527023164201033683fab0000070136bd3f582ad92278296028dc17143e7833fb35ab24952c983d5a26303d530000250d165a4258 else 0x38c9000000003170000011e82248089822fb00003a7545892038000009c028eb000027f400000bf020e83a5a00000083000000001da0000005880000317b0000000011f02ee3119900000000076230703d1000003a9c442033e10b8c20a9434300002b0c235d02a825f00000384d0e9916b0000013802d2022c928400f74) else (if page < 3 then 0x250c24942a803900421b343325a416a01a1022b318111cf8201c026c23fd365918ec38f02b0000003852000016891838402416a80000000000000000293b000041300000000039cd00002a18000022100b843b381120273117403c030e5a1a484110369000000b0a0a8d000020f00f481b102e7b196a00003dac232519800000 else 0x10c229f225f803f937421260335926202a1400d035b016dd3ce811500199050430c52af8021b191045491a6b36f012a020e03aa809d00f812c78165034232a6a136201581bd00c48204326f43af12e28303039482d7438eb085a3050000000292f6b31da050827bc08bb1899000033b400002e42000015c200000b2c)) else (if page < 6 then (if page < 5 then 0x124000002b5b26da13851ce003a411920da001504514326d35c004d80000313400002d53000018641cc026821cf3455021481bc8004c160d2e8000003f7c1c181f6819c028743a901300281000000e813adc4202106015503bd812d40c002b2036781b38396b0dec14410d7518400000000040920620000022c807c11f502df1 else 0x39ea151405801780376a24fa2b181d4c29aa18e832441131000003a900000ecb305b28fb21a027290e5803a000002804271034d8423b22ec428829d805a03bfa40f844724563286c081030981e6844ad39d03a0025100b1c408800002f69000036b811fc2014085813fa39a945784404330017f8391820f40000000000001609) else (if page < 7 then 0x3c8b0000249000001a4c0aa12df0249d0000000015fb2579057c2bd1000023b02ae20000045844a0355d174918802d520000000044002c5029c01be33623305813e814a801a83eb20ee407501f1a0000000008200de90eab326b194207f80a7123980000000001f014950c100000324100000000412000000a70030a1a98 else (if page < 8 then 0x131031a0141d33cb072907b840d027cc0b022bc206fb252808fb280833422e980a903e080e92000029fa000000002260308b13b11c7010b83713232835d8154400000e6100641fbc056830f412d9000018e936ca43db04ac0e89388000652ec23a0824452dbd42e836e53269000021d100001065000033e9450800c5192a24aa else 0x39383c5008c80b6837f4000012e83a20222b0000000000000e1800001361000012e900000000450000000000000036a800003da83ef82ff02f903ecb29451f9321fa2fa400003eb00cb030e043e13a884478000026220000000019403ccc009831ca220100003d9838ac264a3deb0b7b3358145805a8144814e01ac01d32)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x11e0454c16401858372020f53873414c0b480bd80610143d0cf8432843a809aa05ec3229068c180833291278366b1cd04515354111b80c6300ec108510890d6c1c9426f200b0455804c827a31ec835fb248d0760342b30c007880431068930181e7b350100002ae82faa076c021000002d28440c1d30076800000ba100fb09c8 else 0xf2401783fd2000043b0442a10f5000012cd1f401e1c22d1255109f017f24390162824d23ee8083225900c4912410d40333c05213673241d42983dc043320a002f00312822c312f02011153117e0402c344b122022290000084b000000000e64000014e80d8000000a28039807730000000025e801882cca3e983c9834ca0000) else (if page < 12 then 0x19620eaa0dc92ea000000000280100001920291840fb23e03a9903f1217931402990433834c8000028f022b02de031b037883490082b14c029202d58421825ca238500003abc3421430c05930681347a135a03bb000016f12b041b28000000002e3d37d0000004f80000358000000dcc0cb837e33f24014031ba448b055037a3 else (if page < 13 then 0x3c2b1f140000451a2e5342683840000042d80be00f71107045b30c5125d8254a18f9283c3b100c70000022a801d20489000000002a94000000000000426000f034141a503db4043016c5154032182d30248c0d0805d80eb816223282000011600b3800003a1200000000202b31c4000011330000000040d826e835d42924 else 0x22ba3fb821e82c74407300003f7441b4195a3a6827003222000000f800001501000025cc41d2000000002ada000000000000000001b839401971037b00003d5231c00c1112840c5416f200000910029c257429ec009003eb3c333cfd3708375439030b10252d0e68386c29b022281061000034e02f021313000000002fe43763))) else (if page < 16 then (if page < 15 then 0x435c2ac31d8036d822e926b0406d08e82ce206e8448a15952cb335d02e50093c00003ae01f78186000003130217d334c12082f400a8808cc01681f480e000f913fe821090000224110882cfb3c1040612c1c40cd345825002a031734000012c800003cec2a2802d84433173512ab444b000000000d4400004473000000001ac8 else 0x34000d490d4c3fc816e50b08378b00513d5827e02750239001dc3ed01fd823b9000032082ba800002e0815580d181d080061422833c801101b603af80e850560379a06a8443023400000217137492ad824c0135c00c8267b02a01c483454256836ab0bc000001d6137d80000025b43ea01a0331c24ea3d200ea42cb227b207c8) else (if page < 17 then 0x3d5012a41c3b0880181818ba15a800d928b10c520a3826481f2340280ac100002a5917b4123931d021c80000315343f42b28243a179845cb25d510e0389c3bd9274800822f72242838d904483f7842b831830533320127880cd02e4a25b90ed02e681a680ea009881568076914b8264228a80b9d00000000287820d005ab252c else (if page < 18 then 0x344800000000000026c80d38000003180000000000003f1818203958148834c2000007fa00000000000028c800002de40ca00578365100000f6a230000002f782418391900002dbc10980c682d7c0c0839dd000020d300f300e900001861377406a33eaa000022501d64000036100000000015d0409321d83c992b7135e30928 else 0x4488272000003318000019f040e800003cf130aa07a909503f70117d39bc2730005800003f2c00002ef9131b405026d8441408283b683740123b1ec32a680e79000000000bfb381409000000440800000a5a08623c880000356126630e4220b031313160007940f4000002580bd402c03bb10c01004828302b4910e843d30000))))) else (if page < 28 then (if page < 23 then (if page < 21 then (if page < 20 then 0x2c1400000000308326dc2fa805cc32eb457300000000289d15e22bc8210c38b3214b42f90000000000ad0afb000016e400000000058b0000000000002a4c000000000128202a08480fa50d621ecb44481b1804e1019b0ca33a404588054c00cd21500ae50b302f3427a03b0238c800003b6c0000000016022ee0000000003db0 else 0x18b818b115b2000042f40fb814b104b93aeb00001f113cdd000044c117881e48451b0ff83e42428b226833701b881d040ed8062840a4270924981da10bd100003f5a21594528128944ac00001b643b610000148036d012e4141837b8000042303fb3340b00803332238b2bc3114d00000000087b0eb000000d602f7b3d9a2548) else (if page < 22 then 0x32b80f14336400000000000025153320282c0000157000001cec0000000028600000000010da000033b500002ffb21f03be005fa00000a9c0000000040030000233442e039f500000acb070402cb0000068d244c2d382fe01ec000000000096304e0000000000000176c00001de008901c0830380a693c2a20c33a7433d00000 else 0x31582ca0136933302be900001de1000024e332f04498000038ea3828000000000000255d000000000000311c3e4314980bc8090827a241c80000423a28c0040309d842f51cfb39d82a5444c0384c156322533ea828d820ac391a0eb12d9827b017a0003d000035b8072044f0000044b2296a00003b8832b427280f9045300000)) else (if page < 25 then (if page < 24 then 0x418412503ab0136b18430f3800003bf219e02a882b5331903b202e7a4188187238a81d6b2a500f54405a0f2916dc22db039d3a2c1a1b05c4419000fa14ea2e8300001b6b3dcc343029541be024b044e439c210ed0ddc266a3340376826f017f943230019390b359c11f124011e88355831d80f320df10d892c3c4278355a0600 else 0x25703a8036981968161c00003bba45bc25c812b50c690dd92ab804d0301032233a582edb251407d814d5172045620711170543d804490f9940c21c50446b16fc00a10a744483303b15ca316a2efb013803a1187913d03104365837391ff02f351b9339f8340445813e8844db04823e5421603060118812b829380b6d077b0000) else (if page < 26 then 0xf2110f840900a180488222307d01d33203021b010bd235129f83ff834383f2217180e113bc8000018a0000017213fdc0000000000000000000029482a2012c0000014c839733872205835501532187317a90000000032982cd43c58331437f8431b29e923c8445231ea31502cf933501aa833f33d6026881828000036702f73 else (if page < 27 then 0x9c179a343b30e503d015cd22d00ce82930000807ca3c63061b43da00003f28030b0960289405701ce9322800000da4067821d02a74039c0000156c1d600000443d14ec00c02970431405281ea3320c0c2824a82f58176428ea3e591959299b43000e7031e8142830fa1da833040a502bcb2d99018019b03d2429a826b81044 else 0x2f5b0b90172244bb240840543f41207c43a233380aaa2378437029cb0c7412aa336c369c3650349825e141e934b8343902300670188912dd41b03b300000000011b02fc825180000072c229c277b099001e31659198b3c9c00540d030c710320019a0000297c0000000005bb000021b92cf22e18104b000030d12d641a780000)))) else (if page < 33 then (if page < 30 then (if page < 29 then 0x863456b0000000015e015910cdc388c0aca37bc3c380000052a32583a330ce00fe033e8060300a034402530000044da10f030b035bc3c28409a24f0259c2ab3291144103020083b0d642cf83e2a434208402cd018d1093804f444c83b54073332800743386003c837e0220810b20e48059142903522138845802b382cfa0000 else 0x12d117592a782ad40ada35f82448008512513138225800000f79134d09180980449107e008db285317b007fd000019a0123840d9392818ed36f43ba43cf83672174117d03cfc2ee83e4013c937cc00001a08329a000030533701000041fc006c008c08e020b10f7035041859446a00001048432a11b105e903e3000002f03c40) else (if page < 31 then 0x3a7834e93b2c00990fb5000000000f3006842e432d843573080c282827c836282a6220fc39f43ea02478055c074807a000882b7022312dfb398815d921522b69174300e041282db90e1528a53ee017fb0304207043682ddd14782d810dac0000363002d0152400002c0000f503803483323444180360048d29d3233000000000 else (if page < 32 then 0x3ca920f92d4025a83b440e08254c03881ab00fc81d14290d33742a8b29b83f3144110640069b06cb01d0082905f03040191818f825050028108c0b70271924cc085244d40db81ef80b182d5b29551ed02a48076125aa2f712f5012a80ee80c723bb01559341502e5216930e4447028411f5816d933a80ea841e535a808613224 else 0x425006d3209c000029c803b332d807f016e026283c843728000041a216882df438343b89142900f201201cf02f820000000023100a32317842123f902b8800000c900a080b20259d31b2330116783a5b0c6a4160181220593d181d53386d002a0fd80200000013b8186a00002a580bb000001841000024c835f00c141b61048c))) else (if page < 35 then (if page < 34 then 0x109018a139e0403c05a30f1825042a8a00002440000027d00000000008f012901af838d812f83cb0403119003b50312016683bb80dc20aa80a7841c219f30be8041307f413f02928297837702ed8389826a13b903dd00ba8342926180108124a308814c50d131cfa3edb4468101016643d212ebd0000352c000017691ddb1bf0 else 0x2fd43b9c39130aeb1928377c3a930c4000000b500e9018fc1822000019e80f7c0bd9000015083c622bf838c31932003800003d4b321500002f0b25a00a5800c434080000000027693910113943d1396a0fa815693b39144027e800001f280e8000001a6002da185432700d483b8429f000002a52000006e00e6010182efa44ba) else (if page < 36 then 0x2ab164537b019a839e32a9c3ed903704358397c0fc001e0238d137806f0381024532f3b20eb0d242b4245ca37691c6039682ffa2e003f3a207500000000302c39b515903bb90968000020c80798000007c9265114901469216812113fbb15721e000ac40fd93e9022420ed13bf0000024850d5508020000017000000fea1471 else (if page < 37 then 0xe5214510000080323d81d9800003b8a375b381835a03aea2cc3129a071840b01f70000002f82c030a1417b80340000027f027082ed33a522b4010d42d1401182f8813c0000016cd00003cf435c81cc43b08000035682f603068280c081818b412120f8d19eb213b2cea0042223810282cac000016e837790000000044e01bc3 else 0x12c902e0000027b340b51d8834622484068808a817d8174c13e003080f92158a3dea0b311ad00ad218c915622b782c4429a005d02e7332ea0dd019fc29581d9043d23c5918e419491141247508b3190a0ebc3c1c15601db807b934d10eb42fc02dc821a8125802402c8833c036c42c481f6c21e01ca8000014303748059220a4)))))) else (if page < 57 then (if page < 47 then (if page < 42 then (if page < 40 then (if page < 39 then 0x408a21040a9a192143880a2238b21064203909ab342a1510152102c8219a18021beb244d20892e9a09bb027042a8206015852ef81148304c0ccc3b5c45381dda45a304b1413829a215f01dd80f003ed318d920740ab838d12e7802d32068105a2aa41c983ab84432053200003fe012cc395143d0145019b345b9239100000500 else 0x1fb14203ed8000010c433b81eab0f9a28bb000028180978137d08501c2832a000001f9b22a000002ebc30631e7033101a0133fa104019741ffc37603f3427ba1d580970169c40100cf0353c3ac417d910c801d12a643afb0f1036aa4540284c031045c0172d02f4152b00a839083d301210354c2380379345723963419d44f8) else (if page < 41 then 0x2e39082315b100004213443c456a0920450a2dc533882f830a9822d80e5018e03a013ce00be93443212309e00f082ae13f80358828c42d3b423342102f702f983aa03ca0000001483dbc326800913e480e4a000016cc12d02dd40ee024740000000021282bd02868000000003fd004803c682db43f15218823e83ef431011ae0 else 0x28480468000026fa0ea1283833a22480000000001ce802db093004203b4b185242233730197a199c2ad2211914853b400000000010200000153500002370404005f20000000000002cc144533cc10000000030a000000d8d1059000027640000446108f800003b58130800000000000000002d903f60000000000c582b2c)) else (if page < 44 then (if page < 43 then 0x18c225b80000252045a225851e2222120000306b1de8395307b003ac0000141506f800004442373c107d1f3031a800003e8044e80dbc0000446043b828a428f32f282bd83d712fe833a3006800691e5018e1448038d000003c601fa80e13163417703f501b7324bc00003eda434b2aaa17103fc0000043330000279d14f11231 else 0x9400eb50f753fa23a381dfb40a936f818d4115821890e1a37a8177543401449157d028318190000000038833d680b241ee016910f31447939213f230000314809d9000036a000000000110532e03520293a3de134ab273914002e20000032c032f82a3c000000001c030000346c25f93ad40ff0070832f400003a1028d40000) else (if page < 45 then 0x42d01d204038109c35d120790c30336127b8277118680040135000000ab50aea2bf03d6910811cb000d8367b0b622db82fb32f202c8039b041c34320279a247d025000e5000026a91b08000d2bd9000017ea113b25e0408008d8213d18a82470296100000f7800003979309b00000000351a22bb305100000800363837fb2b84 else (if page < 46 then 0xb51039900780dab438c32090df8382431b80f1c2740171a31f53308459c00001e2034c0242c1fa32402000034500000146835490000036428e00000000015492b52287c1c9000000330053b00003ef1000004a83c9000002d8023203df00000243532da15c41912000000003ddb453300001c681c131bb32d0036d100000000 else 0x2436481878394b0bc1318021b8000a09d51d7330001a2803ad214017e2185145902631121344502dd805b00f1117cb12d8109129491e4028e80c941d7b000019d01a3b000000003aa2000031e4000000001e0802980000000044d52cd92134000021510fd01ed3237910ab07f91b7b26e10000124800003950180a00a41ff8)))) else (if page < 52 then (if page < 49 then (if page < 48 then 0x327a26fc2fdc0493028c037337981e782c603bea32391aa012e117894270001021c00658354d24f2175116a901c82e4b00e80073159a0ef0323c00ba3f050e382e8839702f3a311213a216b1375a19c80e3319db3da40e913d88229230f033e003932172195400bd28f223c0288a3afa07a1269913041fb82508247c29db2de8 else 0x2850000033db0c8005381d3a00001db0054326c032880000000035783f6c00001423000022b200000000334811c81a903a4800000000000020b410e538f831c10fd10300131a000027183cd22560445b345131133db83d4a34712415379236d93f9c20bc013013a0279c1750132a30933c301c88258c370009a006382000) else (if page < 50 then 0x3e5a2e48332c1580120c0478408b3f4825b006682dd0366513730b951b9826a01d180e9c06c324582d18449411a81390060843e43272000043082cec18a400002d0a41d80f82341a1778455c19610d982ab035292ad0009a00001fc033600b61000010801dc000000000000036a34283000000000e780000378a30f828b00000 else (if page < 51 then 0xb4014b000003878000001900e3a25e90721000040980000000033940000329508d03460000037d3032429c100000000000000003fd92580197800f400001f8000000000000038a01df0000027f800002f6a3231000017f00000318a324a00000000043911b425b417a81318311000001d38000030a938300ff1000000001a84 else 0x3ab42a90316b28f82a61190800002130389016993d48162d00000f88032b0a6543532f08108d0a302e10000000002598000000001249276c167c000024e820d80d84237302e400000d2814d845521f882fb00ec000001ab800003202000000002b3007c01b4826e9424820b90fe111c0431523d43d910e982ed02c0c35691af0))) else (if page < 54 then (if page < 53 then 0x1d800000000007a37e8185a30ea28fa00002fd0000000002cd8320312d543e8053015203c5b3cf239203744291c1ba820480518132300001b30004132e42ddc2ab2234c0c2922b835391d440d6826500bbb18c80f8341d93aac04f9151d19bc06d800eb1be80a7a17521209034813352880243017c839523ee318103618 else 0x3b643acb00000e3124652f0a43c80000255400003da013f23d40000000000000000023a800003f6800002b3b219b2c28024c38c20438439d0583083107581e7302e81b58225b16901e3b3b6016c83c0b111802203e183600328a079045a82e3c15f800000d1041bc000020330a420000006025d43ff02ea827743eb329b940e0) else (if page < 55 then 0x3e743c200589121d28d028882a40360b029000000000009b1c4343c941400b6013303200111521fb16e1000030ca0de0209006f340bc32cb44b30000445a25b541a30e40000016f93d052e30401c152a1eb803f018d028e436851ef0246030900c91246840080ad0211c43f0145d253529e21a9300002c34000019602af0361c else (if page < 56 then 0x9f42a381698123200004352088818d82b3a4380000000000000000037f011d0000032510000000020f81655158826f818b030d011683e3a352d38200cc000002bca16440d881d993e003fa80a82261340581320146035400000288b208401600000049b3e303559141009f80a4312dc125c358b18902410000000000aa00000 else 0x83340202c90335c0e2826910f59117040f03cb90f800103107830d800001eb315ed05983c7c07a819384148000032b0000033d824dd00001898176803c300002138334300001438078323c50c8802bb15d416d034ec3c5a1730052022982e581c780e8c0d9100893bc006012190348b0000007c33b91831000033eb19ab01c0))))) else (if page < 66 then (if page < 61 then (if page < 59 then (if page < 58 then 0x51000001670000000002af4000001b032d118a900000000275803f842b0000000002a702359122d184908c339e900000b9b1a0039a000001c9b0000246409c13e3b0000167d2bb03078000018f2423217600000000033d4253c000003e0174a160802600998278004b0005925340650000029ab27c227a8002000002e52 else 0x1fe80000000037e2107906bb000022c0000014d00000000016ba094800002198000000003d94000017c914e3000045093de80abb0000000037b900002f800ed434883d383c180a200000000039f03c80437819d800f1272110a800003b0000001cc8000010b3000007e835e814ac000018003cc023880ea92d0b0000) else (if page < 60 then 0xb81881428a36b200bc10cd27fc3a043a50419c2799185015ba21c430a324c527c3439c0278273806601ed807000d420c181a400a6b175a28a900000d6900003af01325422200003b7400000000367a0d21150029883dda3008000024dc04b80000036b06482cc20bec0000000017c423a100000000289c00000bf1 else 0x3e603ec044a4140d2910095c16b9000003e80c9833f81a8c26a800001d283821258820280000044c0943296b3c482da43d080d782b64459d0860114342c0195c279018cc45011b502afb0000385c41e81738000041001dd0215c203204e92aa8173a00002e72205024512b1012a12800000000002e942c202d78435005f841bd)) else (if page < 63 then (if page < 62 then 0x3ca82ef02220000000003aca14b91050000030c400000000364a1b9b00000000379b41a822701680027b39a8436000000eec000000002a7c000015a13f620d191fe000001435000029590ba0274c38f119500f19024800003790423816380000207829e019f80b6b16da04da16d8115513f838e004700f28280903683b690030 else 0x8a01e8041180f44442b42030000184c2973289510080b0b24f8000017fa0000294431521e2b220041702be219d40000000019302e6b22ab1ad80000000039fd00002d883a1a34b01c580228249c00000000000000000000182a00000c3100c100000000000004e80000319a00003b3c0000000000000d3026e02e4024e12421) else (if page < 64 then 0x17e835ec2a510102432214db21f816124158285b08680d9016b82b483469380812681e60407d38890f3907d4307300001d5c18393eab105843a325f24428079c1489447c1234217c08382ec33e58041828233fc31e98269818f0259417843278218045790eca15a038bb1e5b3a28161032bc0de20358000024503f0b0a10 else (if page < 65 then 0xed24223ad813713bfc059b0000351030c10e88000024e0132c000c2ec83e3825c0164800002ce8398343482aec281c2c583d2b0b000ec8112804f13993000018e518c000002170322c3922000023613e28299300000d9c0a79052c164a39591bbb00001ee8000029000000262a22f007280b4400002d241cd82e62432b else 0x1b000ab913d82e9b00b92ac829d025423431063016f82be82d4830b21d50228845c22ca400002f18103411d824443f8c357c000007190af00e3500003eb810410000236840181e90341b00001f183bac023823f026b9359026d21cb8070b052900003b03203c00a50000000023f81470007d2711000000000000000017901742)))) else (if page < 71 then (if page < 68 then (if page < 67 then 0x257819581d3b0c59032828cc43c03998215d202033e2337818c43de01c3024a0000010b02a8336401a9c19883f291830002b00b432930000256d1b201782000002080000000000000000000010843d1a2b980a2a3ac00db03a602eb02bbb36b000000ad81f7435301f082a3003a8383816db303302d90dc841fd2b433c0216f0 else 0x1242000026701b4030b8454127d831e14060246d4034000013c827422a6c3f300ef83a53323011dd04f00d2000ea3e2310ba04c300002f7a03380070326012e017eb378429a31990330c24d0259536e8223022402a984030420a0a8022802cda200827ec230b2051000023183100153a1fc800003e63194800002f1034222555) else (if page < 69 then 0x14f00049245a00000000076d0000133c0000385818b90680029d2f681a58260a00002a8242c8276016fd14a512e50000396210aa3ef00df02b080e20410815181c83000022f5000000000000005c04531230228a00d40f0b0280380008700bd002b8000037580000110d0000162019e300002aa100002db20000000037aa0d0b else (if page < 70 then 0x92b07380693054004a00fe831082e902a102f4827043c890fe2000030bb000033e33e7b000000000000450b00000000000025f4251d23d010bb3ac83d782332240c2a5a2f032ba0084341120c791e102d60352a1ba01493434a228b05e3198211a031682ac009e8000000000000000030ab4178000000000000000022130000 else 0x34a01a042604354a43f807ac1618353a4168095800000000282000000000370943592550246c0000052d000000bb32d440e105db3d04396041803d003bd43c8a393000003892449042290edc34f0009d000031fb000041d3000023fb41e42b5a10003608000000002bba3a622fbb3fa34280350004fa406427aa30012dea0000))) else (if page < 73 then (if page < 72 then 0x3d1242f80000081c43391dc800000f600fe93a0a0b80195133980263338324883efa34784013167900003b182d6c07100c3b001803db42a045d03e6822f41888170841502de50f2c07b118da3f9d05d314e521310000104a287041131bd800000b9c118000001fd0000000000d0039fc265814c934d400003c941970290c else 0x42820b9409b31fc339783d0a127439e5000000002ef3189527ab1a2000000009352134da44820c2018c1152800001e19100c0d58103a2ef20000000000001f002cb828132e3a37d200003df82d500c78191a299800001c2000003594174810a0162c25d9189a32fc01e2284902411ca03f88252504813c0a233901982daa224b) else (if page < 74 then 0x23581bf80c190bb13a182e703e2006632db033a9024212693309052437c000001e3032a8347410290cc3005026902fb800000c4a0a3a3853444a44210ae000142be30df4181a2a1c0dc001001fb013aa06b024381ae82b900f983e10000007c400002e91208c29832b680c7a41f01869299a45b000e4000015b50cac143b2290 else (if page < 75 then 0x3ad013cc060218ac3ec83508252412283688338005b32ae43c7410fd2d083e29183c1601042834f83fb0266005b821c10f0a044134bc404b24b80a481cf217580a621902453b02b02bb826b128443a792b650c503b7c45d1035036a23718251c2a083ea9169d2ef11f3822e024d814fa263807fc3d7036542114373442402341 else 0x2cc82c68420b132238ba28ba00720ab0139a22391715345a00000b5b0000000032e827521a70229322cb0000000000001993000034e232c3000001e8000022e8420800003d8000000011167516c912021342431a308007f12d912a34233800211792209444430f202fa1193a35b3))))))) else 0
  | 6 => if page < 20 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x8230158086c0eeb0000014a07f800f808130c7800000d60000007c1000000000af000000ea003aa04f1037800000d1300f20d6a052304e301900b280e880d920cac03da015b03340000000000000b550f08019101f8000007500b010318000000000b59092100000bf20b1806d806c20e0207c006680000036004a80790052b else 0x33004120ef201e4023d09bb05030b780ca40728035b0ce200000bc0062c0ccc00000aac0000048b059102600c4801bc058809480c9001400aa809200530073003a408b805ec08d80000030908790b840d720de00c2a03ad08a003d00802053c0b5406c3058908fc01ac0ced0bd0031b07da04210a510dc80b030e5b0a23) else (if page < 3 then 0xbb8019c000000000e000cb904f80310012a03e803540000021a080302c900f0000000000141000005c000000da80cc90af30000000006f800000e8a0dea00bb07e9000003e100e800000000088000000e780c0000000b380c100cc8071503000ed20c3a08680e7203980d500e0a089b0000014806700000023000000000 else (if page < 4 then 0xc5c000000000219000008200b680a7104980af8035a02140058041c056103d9040902b8000002010950034300000ac80d930cd100000000037008f205d002880000000001a907780d7b011905e404820ae100000000000009000000075b01b908f100000000056806aa032a06880000009906a903a5044000590558 else 0xbd900000c4200000a3809e306eb0000084a0ac0010009d301990d6b031d06a1075a05b8078b000000000000062404c8036808f003a005480d0a000000000f130af20d780194039d03bc0450056403cc0500036b08480ec002c107f206ab0eaa05540c310ca9083901d80e9402aa06db03c1000003b1068907fb000005510f0c))) else (if page < 7 then (if page < 6 then 0xed0050b09720eb8004302090ca10000038400000d0800000e0803310000000005ca04110269051c000003490a500b20000007f30e38000000000b300b490b400ce3000003f200000968000000c3026c072302e907a008d20b3b00880e6103fc00000000000000000000027d00000000000001300af1000006b00a4800000cf9 else 0xeb3022c04780c980bbb03e20b9800000e1205b4000002b009a9078003c208da087c083c034208c0001003220b6900000abc0ed908700540026d0cda03ac034a0b630bd809c20390042202a806e809a20b410ad80d1b0d8402290e8b0d2b0ee206c106fb018c0939010c098402f9096905280c9a092903500df106b100040000) else (if page < 8 then 0xa7006600c80098909280ec804d009d0041a02a4043809b903b20bea03c803510d7a00000938041903b804200d800cf8044b000005cb069805f00ed30d320d2209e008d1059000000a11000005a50b0a0c9903850e480b10093c092c080a02d00e600630081a00000692000000000000076c000000000000073b000900680138 else (if page < 9 then 0xb0002f005a4000000110f0100000d30000000e208ca0a940c1308d00a300b0804eb034808640228082a0d20095807b806c80d0006b3083206930be901e80afa07d20e2007db0bab0d010ae8097b0db00a22072900000bc800000deb01090e680a6400000e130000000000000250075808e1000000000a8006990149000009b2 else 0x7d10c580ee802900a6a0b2b013203230cc009ab0ba003b302e00bc30070004b03c3000008400738088b00000218085006500168097303b90460059d055c000008e004e0039c07e0000009ea0000050809da02590aa007090a100389017402d10cf10b1b000005dc06da010a0c0306ea000007f000000c6005ac0d120dd80828)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0x121070008ec09a00d100df00c28002801a1013100000000000004700ea20c120ad9017804a009850c0209a301d006b20bf000e00e9107700d880018069a0a5c040808f807e10d9808580e9806a20000000003a8027006480b620ef306b800000b220b320f000ad000000de808520cb005b50ee00aeb090307d007d80e6b0d58 else 0x3c403b400000000000008e2084209aa000008180ae00b1200000c380f1206a30e6407f106e00d4009cb0e80005005c100a8000006f0022d071902db035800000e700df40708080800000edc0580000009b000000188000004b80ef80000059c01100401054c01110cdb03f0076001a003a9097a01b009ca0a280df807140a00) else (if page < 13 then 0xb900000000001d3043309e801390ab8033809d80740099006cb03a106ba064000a907c8054400000cf000000991079801f200000a650000006000000be004100bcb01600000000000000cc40cb4067c086901280483000005e8000001240af905410be10000030808600cd00a6b011a0e9b036400000c40000005ad00000a20 else (if page < 14 then 0x30025807180c1b024806580998098807e3036505b9095c0a490678091005780dc00d68034002c808ea0efa0ea80c1809440c34030304f000000c500eb208c803c504180f04017b009803b50000000007a800000000037c000009c3000005f200000d8a0e280ef005d8000006d00e400cec0000007b0000033b01c109340a1c else 0xb88085c0d4c01b400000b2308900490081b037d069000900d0b01a401540db80108018002dd00000211000007ca000c024003d2080b01030ab40e730b3306e206f204020c4a0a5d0000000009c8000007d908b000000be20efb0112092400b00dfa017007880e580e3003720c0b0a140dfb0b58033a0ed809ba038807930c08))) else (if page < 17 then (if page < 16 then 0xc0a06e30000020407d3079b091c02b508e907e200000000000107fa013a0083000000000eca061c000007e80919056c05180c8803c906f300690bfb03bb04c00dd00c200cb808a803cb0ea306910da0040a0a400b0203e003b003a2032905690f100559025a06c008300d1a0bf80d2a015002c000c803c003e9 else 0xc92081009e20ca80d2800000b4800000d18060805600eb00602011806d202d805490eab03920c220e1003ab026805500d900a0807480c5403f101220d8b068003f90d3801a801b80e0b060300000e6a09b80cc102e802200cb106b90c1a0b1309c009db09eb09180d730200003b074b0e5a016c04b004d8087800a004800000) else (if page < 18 then 0x51005d10320049102e109a100d00bfa000006140b1a05700ecb0b2a0d3309410b0b028003ea07b003f400fa08e806ca03fd09b10000042b01c806d300140960053805f3038b01440bf3072207c90a9800000e180000091409d205200908000003d802f807ea0000099900000be80c6800d801b10a8c0305000006a00d7002f1 else (if page < 19 then 0x8d909f0094009300e5000000020000000000e0303cd0ae90142045804e203bd0ba801980d810000081200000822021003690beb000002a00e9a0e9001050000000007010ca00bd10cbc0c7303ca012906000b70074a0800093107b30f090bb003a3032801200aea040005f80eea03ba046806a80a78038009f80d230ee30638 else 0x9a80298))))) else 0
  | 7 => if page < 1 then 0x2300100000000d00380014007000530008000100520043004900040068000c00000048003a0009003200280058003000200078000b00000080004c0022004200000029000000000060001a0000001b0011000000330018000a0040002c000000500000003b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k 16 (h % b)
  let slot := field targets k 16 ((h / b + shift) % slotCount k)
  (slot / 8,slot % 8)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | 2 => [s01]
  | 3 => [s01, s02]
  | 4 => [s02, s01]
  | 5 => [s02]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def goalColumns : Nat := 0xfee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def checked (k i : Nat) := decide (pool k i).Nodup && Vector.packedClosed target negative goalColumns pool counts lookup steps k i
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 5 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x16 : span (checked 3) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x32 : span (checked 3) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x48 : span (checked 3) 3 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 51 0 = true :=
  (@span_join (checked 3) 32 0 19 (@span_join (checked 3) 16 0 16 chunk3x0 chunk3x16) (@span_join (checked 3) 16 32 3 chunk3x32 chunk3x48))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x16 : span (checked 4) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x32 : span (checked 4) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x48 : span (checked 4) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x64 : span (checked 4) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x80 : span (checked 4) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x96 : span (checked 4) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x128 : span (checked 4) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x144 : span (checked 4) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x160 : span (checked 4) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x176 : span (checked 4) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x192 : span (checked 4) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x208 : span (checked 4) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x224 : span (checked 4) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x240 : span (checked 4) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x256 : span (checked 4) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x272 : span (checked 4) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x288 : span (checked 4) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x304 : span (checked 4) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x320 : span (checked 4) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x336 : span (checked 4) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x352 : span (checked 4) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x368 : span (checked 4) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x384 : span (checked 4) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x400 : span (checked 4) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x416 : span (checked 4) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x432 : span (checked 4) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x448 : span (checked 4) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x464 : span (checked 4) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x480 : span (checked 4) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x496 : span (checked 4) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x512 : span (checked 4) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x528 : span (checked 4) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x544 : span (checked 4) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x560 : span (checked 4) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x576 : span (checked 4) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x592 : span (checked 4) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x608 : span (checked 4) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x624 : span (checked 4) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x640 : span (checked 4) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x656 : span (checked 4) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x672 : span (checked 4) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x688 : span (checked 4) 16 688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x704 : span (checked 4) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x720 : span (checked 4) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x736 : span (checked 4) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x752 : span (checked 4) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x768 : span (checked 4) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x784 : span (checked 4) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x800 : span (checked 4) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x816 : span (checked 4) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x832 : span (checked 4) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x848 : span (checked 4) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x864 : span (checked 4) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x880 : span (checked 4) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x896 : span (checked 4) 16 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x912 : span (checked 4) 16 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x928 : span (checked 4) 16 928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x944 : span (checked 4) 16 944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x960 : span (checked 4) 16 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x976 : span (checked 4) 16 976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x992 : span (checked 4) 16 992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1008 : span (checked 4) 16 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1024 : span (checked 4) 16 1024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1040 : span (checked 4) 16 1040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1056 : span (checked 4) 16 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1072 : span (checked 4) 16 1072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1088 : span (checked 4) 13 1088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1101 0 = true :=
  (@span_join (checked 4) 544 0 557 (@span_join (checked 4) 272 0 272 (@span_join (checked 4) 128 0 144 (@span_join (checked 4) 64 0 64 (@span_join (checked 4) 32 0 32 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 16 chunk4x32 chunk4x48)) (@span_join (checked 4) 32 64 32 (@span_join (checked 4) 16 64 16 chunk4x64 chunk4x80) (@span_join (checked 4) 16 96 16 chunk4x96 chunk4x112))) (@span_join (checked 4) 64 128 80 (@span_join (checked 4) 32 128 32 (@span_join (checked 4) 16 128 16 chunk4x128 chunk4x144) (@span_join (checked 4) 16 160 16 chunk4x160 chunk4x176)) (@span_join (checked 4) 32 192 48 (@span_join (checked 4) 16 192 16 chunk4x192 chunk4x208) (@span_join (checked 4) 16 224 32 chunk4x224 (@span_join (checked 4) 16 240 16 chunk4x240 chunk4x256))))) (@span_join (checked 4) 128 272 144 (@span_join (checked 4) 64 272 64 (@span_join (checked 4) 32 272 32 (@span_join (checked 4) 16 272 16 chunk4x272 chunk4x288) (@span_join (checked 4) 16 304 16 chunk4x304 chunk4x320)) (@span_join (checked 4) 32 336 32 (@span_join (checked 4) 16 336 16 chunk4x336 chunk4x352) (@span_join (checked 4) 16 368 16 chunk4x368 chunk4x384))) (@span_join (checked 4) 64 400 80 (@span_join (checked 4) 32 400 32 (@span_join (checked 4) 16 400 16 chunk4x400 chunk4x416) (@span_join (checked 4) 16 432 16 chunk4x432 chunk4x448)) (@span_join (checked 4) 32 464 48 (@span_join (checked 4) 16 464 16 chunk4x464 chunk4x480) (@span_join (checked 4) 16 496 32 chunk4x496 (@span_join (checked 4) 16 512 16 chunk4x512 chunk4x528)))))) (@span_join (checked 4) 272 544 285 (@span_join (checked 4) 128 544 144 (@span_join (checked 4) 64 544 64 (@span_join (checked 4) 32 544 32 (@span_join (checked 4) 16 544 16 chunk4x544 chunk4x560) (@span_join (checked 4) 16 576 16 chunk4x576 chunk4x592)) (@span_join (checked 4) 32 608 32 (@span_join (checked 4) 16 608 16 chunk4x608 chunk4x624) (@span_join (checked 4) 16 640 16 chunk4x640 chunk4x656))) (@span_join (checked 4) 64 672 80 (@span_join (checked 4) 32 672 32 (@span_join (checked 4) 16 672 16 chunk4x672 chunk4x688) (@span_join (checked 4) 16 704 16 chunk4x704 chunk4x720)) (@span_join (checked 4) 32 736 48 (@span_join (checked 4) 16 736 16 chunk4x736 chunk4x752) (@span_join (checked 4) 16 768 32 chunk4x768 (@span_join (checked 4) 16 784 16 chunk4x784 chunk4x800))))) (@span_join (checked 4) 144 816 141 (@span_join (checked 4) 64 816 80 (@span_join (checked 4) 32 816 32 (@span_join (checked 4) 16 816 16 chunk4x816 chunk4x832) (@span_join (checked 4) 16 848 16 chunk4x848 chunk4x864)) (@span_join (checked 4) 32 880 48 (@span_join (checked 4) 16 880 16 chunk4x880 chunk4x896) (@span_join (checked 4) 16 912 32 chunk4x912 (@span_join (checked 4) 16 928 16 chunk4x928 chunk4x944)))) (@span_join (checked 4) 64 960 77 (@span_join (checked 4) 32 960 32 (@span_join (checked 4) 16 960 16 chunk4x960 chunk4x976) (@span_join (checked 4) 16 992 16 chunk4x992 chunk4x1008)) (@span_join (checked 4) 32 1024 45 (@span_join (checked 4) 16 1024 16 chunk4x1024 chunk4x1040) (@span_join (checked 4) 16 1056 29 chunk4x1056 (@span_join (checked 4) 16 1072 13 chunk4x1072 chunk4x1088)))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x16 : span (checked 5) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x32 : span (checked 5) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x48 : span (checked 5) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x64 : span (checked 5) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x80 : span (checked 5) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x96 : span (checked 5) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x128 : span (checked 5) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x144 : span (checked 5) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x160 : span (checked 5) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x176 : span (checked 5) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x192 : span (checked 5) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x208 : span (checked 5) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x224 : span (checked 5) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x240 : span (checked 5) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x256 : span (checked 5) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x272 : span (checked 5) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x288 : span (checked 5) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x304 : span (checked 5) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x320 : span (checked 5) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x336 : span (checked 5) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x352 : span (checked 5) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x368 : span (checked 5) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x384 : span (checked 5) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x400 : span (checked 5) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x416 : span (checked 5) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x432 : span (checked 5) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x448 : span (checked 5) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x464 : span (checked 5) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x480 : span (checked 5) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x496 : span (checked 5) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x512 : span (checked 5) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x528 : span (checked 5) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x544 : span (checked 5) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x560 : span (checked 5) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x576 : span (checked 5) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x592 : span (checked 5) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x608 : span (checked 5) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x624 : span (checked 5) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x640 : span (checked 5) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x656 : span (checked 5) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x688 : span (checked 5) 16 688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x704 : span (checked 5) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x720 : span (checked 5) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x736 : span (checked 5) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x752 : span (checked 5) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x768 : span (checked 5) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x784 : span (checked 5) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x800 : span (checked 5) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x816 : span (checked 5) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x832 : span (checked 5) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x848 : span (checked 5) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x864 : span (checked 5) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x880 : span (checked 5) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x896 : span (checked 5) 16 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x912 : span (checked 5) 16 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x928 : span (checked 5) 16 928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x944 : span (checked 5) 16 944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x960 : span (checked 5) 16 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x976 : span (checked 5) 16 976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x992 : span (checked 5) 16 992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1008 : span (checked 5) 16 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1024 : span (checked 5) 16 1024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1040 : span (checked 5) 16 1040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1056 : span (checked 5) 16 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1072 : span (checked 5) 16 1072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1088 : span (checked 5) 16 1088 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1104 : span (checked 5) 16 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1120 : span (checked 5) 16 1120 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1136 : span (checked 5) 16 1136 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1152 : span (checked 5) 16 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1168 : span (checked 5) 16 1168 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1184 : span (checked 5) 16 1184 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1200 : span (checked 5) 16 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1216 : span (checked 5) 16 1216 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1232 : span (checked 5) 16 1232 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1248 : span (checked 5) 16 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1264 : span (checked 5) 16 1264 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1280 : span (checked 5) 16 1280 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1296 : span (checked 5) 16 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1312 : span (checked 5) 16 1312 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1328 : span (checked 5) 16 1328 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1344 : span (checked 5) 16 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1360 : span (checked 5) 16 1360 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1376 : span (checked 5) 16 1376 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1392 : span (checked 5) 16 1392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1408 : span (checked 5) 16 1408 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1424 : span (checked 5) 16 1424 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1440 : span (checked 5) 16 1440 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1456 : span (checked 5) 16 1456 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1472 : span (checked 5) 16 1472 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1488 : span (checked 5) 16 1488 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1504 : span (checked 5) 16 1504 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1520 : span (checked 5) 16 1520 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1536 : span (checked 5) 16 1536 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1552 : span (checked 5) 16 1552 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1568 : span (checked 5) 16 1568 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1584 : span (checked 5) 16 1584 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1600 : span (checked 5) 16 1600 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1616 : span (checked 5) 16 1616 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1632 : span (checked 5) 16 1632 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1648 : span (checked 5) 16 1648 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1664 : span (checked 5) 16 1664 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1680 : span (checked 5) 16 1680 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1696 : span (checked 5) 16 1696 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1712 : span (checked 5) 16 1712 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1728 : span (checked 5) 16 1728 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1744 : span (checked 5) 16 1744 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1760 : span (checked 5) 16 1760 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1776 : span (checked 5) 16 1776 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1792 : span (checked 5) 16 1792 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1808 : span (checked 5) 16 1808 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1824 : span (checked 5) 16 1824 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1840 : span (checked 5) 16 1840 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1856 : span (checked 5) 16 1856 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1872 : span (checked 5) 16 1872 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1888 : span (checked 5) 16 1888 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1904 : span (checked 5) 16 1904 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1920 : span (checked 5) 16 1920 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1936 : span (checked 5) 16 1936 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1952 : span (checked 5) 16 1952 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1968 : span (checked 5) 16 1968 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1984 : span (checked 5) 16 1984 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2000 : span (checked 5) 16 2000 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2016 : span (checked 5) 16 2016 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2032 : span (checked 5) 16 2032 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2048 : span (checked 5) 16 2048 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2064 : span (checked 5) 16 2064 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2080 : span (checked 5) 16 2080 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2096 : span (checked 5) 16 2096 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2112 : span (checked 5) 16 2112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2128 : span (checked 5) 16 2128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2144 : span (checked 5) 16 2144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2160 : span (checked 5) 16 2160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2176 : span (checked 5) 16 2176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2192 : span (checked 5) 16 2192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2208 : span (checked 5) 16 2208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2224 : span (checked 5) 11 2224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 2235 0 = true :=
  (@span_join (checked 5) 1120 0 1115 (@span_join (checked 5) 560 0 560 (@span_join (checked 5) 272 0 288 (@span_join (checked 5) 128 0 144 (@span_join (checked 5) 64 0 64 (@span_join (checked 5) 32 0 32 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 16 chunk5x32 chunk5x48)) (@span_join (checked 5) 32 64 32 (@span_join (checked 5) 16 64 16 chunk5x64 chunk5x80) (@span_join (checked 5) 16 96 16 chunk5x96 chunk5x112))) (@span_join (checked 5) 64 128 80 (@span_join (checked 5) 32 128 32 (@span_join (checked 5) 16 128 16 chunk5x128 chunk5x144) (@span_join (checked 5) 16 160 16 chunk5x160 chunk5x176)) (@span_join (checked 5) 32 192 48 (@span_join (checked 5) 16 192 16 chunk5x192 chunk5x208) (@span_join (checked 5) 16 224 32 chunk5x224 (@span_join (checked 5) 16 240 16 chunk5x240 chunk5x256))))) (@span_join (checked 5) 144 272 144 (@span_join (checked 5) 64 272 80 (@span_join (checked 5) 32 272 32 (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288) (@span_join (checked 5) 16 304 16 chunk5x304 chunk5x320)) (@span_join (checked 5) 32 336 48 (@span_join (checked 5) 16 336 16 chunk5x336 chunk5x352) (@span_join (checked 5) 16 368 32 chunk5x368 (@span_join (checked 5) 16 384 16 chunk5x384 chunk5x400)))) (@span_join (checked 5) 64 416 80 (@span_join (checked 5) 32 416 32 (@span_join (checked 5) 16 416 16 chunk5x416 chunk5x432) (@span_join (checked 5) 16 448 16 chunk5x448 chunk5x464)) (@span_join (checked 5) 32 480 48 (@span_join (checked 5) 16 480 16 chunk5x480 chunk5x496) (@span_join (checked 5) 16 512 32 chunk5x512 (@span_join (checked 5) 16 528 16 chunk5x528 chunk5x544)))))) (@span_join (checked 5) 272 560 288 (@span_join (checked 5) 128 560 144 (@span_join (checked 5) 64 560 64 (@span_join (checked 5) 32 560 32 (@span_join (checked 5) 16 560 16 chunk5x560 chunk5x576) (@span_join (checked 5) 16 592 16 chunk5x592 chunk5x608)) (@span_join (checked 5) 32 624 32 (@span_join (checked 5) 16 624 16 chunk5x624 chunk5x640) (@span_join (checked 5) 16 656 16 chunk5x656 chunk5x672))) (@span_join (checked 5) 64 688 80 (@span_join (checked 5) 32 688 32 (@span_join (checked 5) 16 688 16 chunk5x688 chunk5x704) (@span_join (checked 5) 16 720 16 chunk5x720 chunk5x736)) (@span_join (checked 5) 32 752 48 (@span_join (checked 5) 16 752 16 chunk5x752 chunk5x768) (@span_join (checked 5) 16 784 32 chunk5x784 (@span_join (checked 5) 16 800 16 chunk5x800 chunk5x816))))) (@span_join (checked 5) 144 832 144 (@span_join (checked 5) 64 832 80 (@span_join (checked 5) 32 832 32 (@span_join (checked 5) 16 832 16 chunk5x832 chunk5x848) (@span_join (checked 5) 16 864 16 chunk5x864 chunk5x880)) (@span_join (checked 5) 32 896 48 (@span_join (checked 5) 16 896 16 chunk5x896 chunk5x912) (@span_join (checked 5) 16 928 32 chunk5x928 (@span_join (checked 5) 16 944 16 chunk5x944 chunk5x960)))) (@span_join (checked 5) 64 976 80 (@span_join (checked 5) 32 976 32 (@span_join (checked 5) 16 976 16 chunk5x976 chunk5x992) (@span_join (checked 5) 16 1008 16 chunk5x1008 chunk5x1024)) (@span_join (checked 5) 32 1040 48 (@span_join (checked 5) 16 1040 16 chunk5x1040 chunk5x1056) (@span_join (checked 5) 16 1072 32 chunk5x1072 (@span_join (checked 5) 16 1088 16 chunk5x1088 chunk5x1104))))))) (@span_join (checked 5) 560 1120 555 (@span_join (checked 5) 272 1120 288 (@span_join (checked 5) 128 1120 144 (@span_join (checked 5) 64 1120 64 (@span_join (checked 5) 32 1120 32 (@span_join (checked 5) 16 1120 16 chunk5x1120 chunk5x1136) (@span_join (checked 5) 16 1152 16 chunk5x1152 chunk5x1168)) (@span_join (checked 5) 32 1184 32 (@span_join (checked 5) 16 1184 16 chunk5x1184 chunk5x1200) (@span_join (checked 5) 16 1216 16 chunk5x1216 chunk5x1232))) (@span_join (checked 5) 64 1248 80 (@span_join (checked 5) 32 1248 32 (@span_join (checked 5) 16 1248 16 chunk5x1248 chunk5x1264) (@span_join (checked 5) 16 1280 16 chunk5x1280 chunk5x1296)) (@span_join (checked 5) 32 1312 48 (@span_join (checked 5) 16 1312 16 chunk5x1312 chunk5x1328) (@span_join (checked 5) 16 1344 32 chunk5x1344 (@span_join (checked 5) 16 1360 16 chunk5x1360 chunk5x1376))))) (@span_join (checked 5) 144 1392 144 (@span_join (checked 5) 64 1392 80 (@span_join (checked 5) 32 1392 32 (@span_join (checked 5) 16 1392 16 chunk5x1392 chunk5x1408) (@span_join (checked 5) 16 1424 16 chunk5x1424 chunk5x1440)) (@span_join (checked 5) 32 1456 48 (@span_join (checked 5) 16 1456 16 chunk5x1456 chunk5x1472) (@span_join (checked 5) 16 1488 32 chunk5x1488 (@span_join (checked 5) 16 1504 16 chunk5x1504 chunk5x1520)))) (@span_join (checked 5) 64 1536 80 (@span_join (checked 5) 32 1536 32 (@span_join (checked 5) 16 1536 16 chunk5x1536 chunk5x1552) (@span_join (checked 5) 16 1568 16 chunk5x1568 chunk5x1584)) (@span_join (checked 5) 32 1600 48 (@span_join (checked 5) 16 1600 16 chunk5x1600 chunk5x1616) (@span_join (checked 5) 16 1632 32 chunk5x1632 (@span_join (checked 5) 16 1648 16 chunk5x1648 chunk5x1664)))))) (@span_join (checked 5) 272 1680 283 (@span_join (checked 5) 128 1680 144 (@span_join (checked 5) 64 1680 64 (@span_join (checked 5) 32 1680 32 (@span_join (checked 5) 16 1680 16 chunk5x1680 chunk5x1696) (@span_join (checked 5) 16 1712 16 chunk5x1712 chunk5x1728)) (@span_join (checked 5) 32 1744 32 (@span_join (checked 5) 16 1744 16 chunk5x1744 chunk5x1760) (@span_join (checked 5) 16 1776 16 chunk5x1776 chunk5x1792))) (@span_join (checked 5) 64 1808 80 (@span_join (checked 5) 32 1808 32 (@span_join (checked 5) 16 1808 16 chunk5x1808 chunk5x1824) (@span_join (checked 5) 16 1840 16 chunk5x1840 chunk5x1856)) (@span_join (checked 5) 32 1872 48 (@span_join (checked 5) 16 1872 16 chunk5x1872 chunk5x1888) (@span_join (checked 5) 16 1904 32 chunk5x1904 (@span_join (checked 5) 16 1920 16 chunk5x1920 chunk5x1936))))) (@span_join (checked 5) 144 1952 139 (@span_join (checked 5) 64 1952 80 (@span_join (checked 5) 32 1952 32 (@span_join (checked 5) 16 1952 16 chunk5x1952 chunk5x1968) (@span_join (checked 5) 16 1984 16 chunk5x1984 chunk5x2000)) (@span_join (checked 5) 32 2016 48 (@span_join (checked 5) 16 2016 16 chunk5x2016 chunk5x2032) (@span_join (checked 5) 16 2048 32 chunk5x2048 (@span_join (checked 5) 16 2064 16 chunk5x2064 chunk5x2080)))) (@span_join (checked 5) 64 2096 75 (@span_join (checked 5) 32 2096 32 (@span_join (checked 5) 16 2096 16 chunk5x2096 chunk5x2112) (@span_join (checked 5) 16 2128 16 chunk5x2128 chunk5x2144)) (@span_join (checked 5) 32 2160 43 (@span_join (checked 5) 16 2160 16 chunk5x2160 chunk5x2176) (@span_join (checked 5) 16 2192 27 chunk5x2192 (@span_join (checked 5) 16 2208 11 chunk5x2208 chunk5x2224))))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x16 : span (checked 6) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x32 : span (checked 6) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x48 : span (checked 6) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x64 : span (checked 6) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x80 : span (checked 6) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x96 : span (checked 6) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x128 : span (checked 6) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x144 : span (checked 6) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x160 : span (checked 6) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x176 : span (checked 6) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x192 : span (checked 6) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x208 : span (checked 6) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x224 : span (checked 6) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x240 : span (checked 6) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x256 : span (checked 6) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x272 : span (checked 6) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x288 : span (checked 6) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x304 : span (checked 6) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x320 : span (checked 6) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x336 : span (checked 6) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x352 : span (checked 6) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x368 : span (checked 6) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x384 : span (checked 6) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x400 : span (checked 6) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x416 : span (checked 6) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x432 : span (checked 6) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x448 : span (checked 6) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x464 : span (checked 6) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x480 : span (checked 6) 3 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 483 0 = true :=
  (@span_join (checked 6) 240 0 243 (@span_join (checked 6) 112 0 128 (@span_join (checked 6) 48 0 64 (@span_join (checked 6) 16 0 32 chunk6x0 (@span_join (checked 6) 16 16 16 chunk6x16 chunk6x32)) (@span_join (checked 6) 32 48 32 (@span_join (checked 6) 16 48 16 chunk6x48 chunk6x64) (@span_join (checked 6) 16 80 16 chunk6x80 chunk6x96))) (@span_join (checked 6) 64 112 64 (@span_join (checked 6) 32 112 32 (@span_join (checked 6) 16 112 16 chunk6x112 chunk6x128) (@span_join (checked 6) 16 144 16 chunk6x144 chunk6x160)) (@span_join (checked 6) 32 176 32 (@span_join (checked 6) 16 176 16 chunk6x176 chunk6x192) (@span_join (checked 6) 16 208 16 chunk6x208 chunk6x224)))) (@span_join (checked 6) 128 240 115 (@span_join (checked 6) 64 240 64 (@span_join (checked 6) 32 240 32 (@span_join (checked 6) 16 240 16 chunk6x240 chunk6x256) (@span_join (checked 6) 16 272 16 chunk6x272 chunk6x288)) (@span_join (checked 6) 32 304 32 (@span_join (checked 6) 16 304 16 chunk6x304 chunk6x320) (@span_join (checked 6) 16 336 16 chunk6x336 chunk6x352))) (@span_join (checked 6) 64 368 51 (@span_join (checked 6) 32 368 32 (@span_join (checked 6) 16 368 16 chunk6x368 chunk6x384) (@span_join (checked 6) 16 400 16 chunk6x400 chunk6x416)) (@span_join (checked 6) 32 432 19 (@span_join (checked 6) 16 432 16 chunk6x432 chunk6x448) (@span_join (checked 6) 16 464 3 chunk6x464 chunk6x480)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x16 : span (checked 7) 1 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 17 0 = true :=
  (@span_join (checked 7) 16 0 1 chunk7x0 chunk7x16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 1 0 = true :=
  chunk8x0
theorem verified : ∀ k ≤ 8, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 9 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => Vector.closed_sound target negative goalColumns mask_valid pool counts lookup steps (by decide +kernel) (fun r hr => (neg r hr).1) k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Restricted



namespace SignedFrontier.CliqueLink
def target := SmallCert.Restricted.target
def raw := SmallCert.Restricted.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 9 ≤ p.length := by
  have inside : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial target 0 {target} Cone.done inside
  have start : available initial = insert 0 SmallCert.Restricted.raw.toFinset := by decide +kernel
  rw [start] at access
  have bounded := SmallCert.Restricted.lower run access
  omega
end SignedFrontier.CliqueLink

namespace TableLink
open SignedFrontier

def assignment (r : Fin 64) (v : Fin 5) : Bool := r.val.testBit v.val

theorem rawTable : ∀ r : Fin 64, CliqueLink.initial.map (fun u => u.getLsbD r.val) =
    ThresholdReplacement.signedStart (assignment r) := by decide +kernel

theorem goalTable : ∀ r : Fin 64, CliqueLink.target.getLsbD r.val =
    ThresholdReplacement.sliceTarget (assignment r) := by decide +kernel

theorem readDefault (xs : List W) (j r : ℕ) :
    (xs.getD j 0).getLsbD r = (xs.map (fun u => u.getLsbD r)).getD j false := by
  by_cases hj : j < xs.length
  · rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem addRow (xs : List W) (ij : ℕ × ℕ) (r : ℕ) (hr : r < 64) :
    (add xs ij).map (fun u => u.getLsbD r) =
      PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r)) ij := by
  simp only [add,PetersenSignedSlice.addPair,List.map_append,List.map_cons,List.map_nil,
      BitVec.getLsbD_and,BitVec.getLsbD_not,hr,decide_true,Bool.true_and,readDefault]

theorem foldRow (p : List (ℕ × ℕ)) (xs : List W) (r : Fin 64) :
    (p.foldl add xs).map (fun u => u.getLsbD r.val) =
      p.foldl PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r.val)) := by
  induction p generalizing xs with
  | nil => rfl
  | cons ij tail ih =>
    simp only [List.foldl_cons,ih,addRow _ _ _ r.isLt]

theorem wordOfSolution (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) :
    canonical (evaluate p CliqueLink.initial o) = CliqueLink.target := by
  have eq : evaluate p CliqueLink.initial o = CliqueLink.target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 64 := ⟨i,hi⟩
    change ((p.foldl add CliqueLink.initial).getD o 0).getLsbD r.val = _
    rw [readDefault,foldRow p CliqueLink.initial r,rawTable r]
    exact (hit (assignment r)).trans (goalTable r).symm
  rw [eq]
  decide +kernel

theorem sliceRequirement
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 9 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 9 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12308_aux

open PEqualNP.Outside.L_meta_12308_aux

theorem PEqualNP.Outside.L_meta_12308 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
