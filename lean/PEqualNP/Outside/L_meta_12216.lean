import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12216_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (3900762240 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.or, [4,5]⟩,
  ⟨.and, [0,1]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.and, [2,3]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.and, [6,9]⟩,
  ⟨.or, [6,9]⟩,
  ⟨.and, [10,12]⟩,
  ⟨.or, [7,11]⟩,
  ⟨.and, [8,13]⟩,
  ⟨.and, [14,15]⟩],16⟩
theorem size : witness.size = 11 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
theorem value : ∀ x, circuitFun 6 witness x = target x := by decide +kernel

abbrev Input := Fin 5 → Bool
def lift (x : Input) : Fin 6 → Bool := fun j => if h : j.val < 5 then !(x ⟨j.val,h⟩) else false
def sliceTarget (x : Input) := target (lift x)
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- Pin the last input low and complement the five surviving input signals.
theorem pinSlice (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = sliceTarget x := by
  let raw := List.ofFn (fun j : Fin 5 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let pin := fun j : Fin 6 => (fun x : Input => lift x j, decide (j.val < 3), decide (j.val < 3 ∨ j.val = 5))
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    by_cases h : j.val < 5
    · let i : Fin 5 := ⟨j.val,h⟩
      have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      have neg : (fun x : Input => !(x i)) ∈ pool := List.mem_append_right _ (List.mem_map_of_mem pos)
      have both : (fun x : Input => x i) ∈ pool := List.mem_append_left _ (List.mem_append_right _ pos)
      refine ⟨?_,?_,Or.inr ?_⟩
      · simpa [pin,lift,h,i] using neg
      · simpa [pin,lift,h,i] using both
      · have ne : j.val ≠ 5 := by omega
        simp [pin,ne]
    · refine ⟨?_,?_,Or.inl ⟨false,fun x => ?_⟩⟩
      · simpa [pin,lift,h] using constants false
      · simpa [pin,lift,h] using constants true
      · simp [pin,lift,h]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = sliceTarget x := by
    simpa [v, pin, sliceTarget, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : sliceTarget (fun _ => false) ≠ sliceTarget (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (j.val < 3))
    have b := hit (fun j => decide (j.val < 3 ∨ j.val = 5))
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

namespace SignedFrontier

theorem zero_inter (x : W) : (0 : W) &&& x = 0 := BitVec.zero_and

theorem survivors_zero (r : ℕ) (s : List W) : survivors r s 0 = 0 := by
  cases s <;> simp [survivors]

theorem survivors_inter (r : ℕ) (s : List W) (u v : W) :
    survivors r s (u &&& v) = survivors r s u &&& v := by
  induction s generalizing u with
  | nil => rfl
  | cons a tail ih =>
    by_cases hu : u = 0
    · subst u
      rw [zero_inter, survivors_zero, zero_inter]
    · by_cases hv : u &&& v = 0
      · rw [hv, survivors_zero, survivors, if_neg hu]
        rw [← ih]
        rw [BitVec.and_assoc, BitVec.and_comm (rowMask r a), ← BitVec.and_assoc, hv]
        rw [zero_inter, survivors_zero]
      · rw [survivors, if_neg hv, survivors, if_neg hu, ← ih]
        rw [BitVec.and_assoc, BitVec.and_comm v, ← BitVec.and_assoc]

-- Screen the four candidate outputs together. Once the retained inputs agree
-- with a negative row, only the candidate output itself can separate the row.
def screen (g : W) (base : List W) : List ℕ → List W → List W
  | [], candidates => candidates
  | r :: rows, candidates =>
    if candidates.isEmpty then [] else
    let mask := survivors r base g
    if mask = 0 then screen g base rows candidates else
      screen g base rows (candidates.filter fun w => (mask &&& rowMask r w) == 0)

theorem screen_keeps {g w : W} (hg : g ≠ 0) (base : List W) (rows : List ℕ)
    (candidates : List W) (hw : w ∈ candidates) (ok : covered g rows (w :: base) = true) :
    w ∈ screen g base rows candidates := by
  induction rows generalizing candidates with
  | nil => exact hw
  | cons r rows ih =>
    have clear := List.all_eq_true.mp ok r List.mem_cons_self
    have tail : covered g rows (w :: base) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      exact List.all_eq_true.mp ok i (List.mem_cons_of_mem _ hi)
    have hm : survivors r base g &&& rowMask r w = 0 := by
      have h := beq_iff_eq.mp clear
      simpa only [survivors, if_neg hg, survivors_inter] using h
    unfold screen
    have hn : candidates.isEmpty = false := by
      cases candidates <;> simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ih _ hw tail
    · exact ih _ (List.mem_filter.mpr ⟨hw,beq_iff_eq.mpr hm⟩) tail

def fastBranch (g : W) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (candidates base : List W) : Bool :=
  decide (0 < k) && decide (base.length ≤ k) &&
    (screen g base rows candidates).any fun w => !locate (w :: base)

def fastPair (g : W) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (s : List W) (a b : W) : Bool :=
  let choices' := choices a b
  choices'.contains g ||
    let rest := s.filter fun u => u != a && u != b
    let fresh := choices'.filter fun w => w != 0 && !s.contains w
    fastBranch g rows locate k fresh rest ||
    fastBranch g rows locate k fresh (a :: rest) ||
    fastBranch g rows locate k fresh (b :: rest) ||
    fastBranch g rows locate k fresh (a :: b :: rest)

def fastClosed (g : W) (rows : List ℕ) (words : ℕ → ℕ → List W)
    (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) :
    ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    let locate := found words count lookup sym k
    !s.contains g && !(s.any fun a => s.any fun b =>
      decide (a.toNat < b.toNat) && fastPair g rows locate k s a b)

theorem branch_of {g w : W} (hg : g ≠ 0) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (fresh base : List W) (hw : w ∈ fresh)
    (hk : 0 < k) (len : (w :: base).length ≤ k+1)
    (cov : covered g rows (w :: base) = true) (miss : locate (w :: base) = false) :
    fastBranch g rows locate k fresh base = true := by
  have p : base.length ≤ k := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using len
  simp only [fastBranch, hk, p, decide_true, Bool.true_and]
  exact List.any_eq_true.mpr ⟨w, screen_keeps hg base rows fresh hw cov, by simp [miss]⟩

theorem fastPair_of {g : W} (hg : g ≠ 0) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (s : List W) (a b : W) (ha : a ∈ s) (hb : b ∈ s) (absent : g ∉ s)
    (h : onePair s (fun t => t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) &&
      covered g rows t && !locate t)) a b = true) :
    fastPair g rows locate k s a b = true := by
  obtain ⟨w,form,test⟩ := List.any_eq_true.mp h
  obtain ⟨fresh,keeps⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨ka,_,rest⟩ := List.any_eq_true.mp keeps
  obtain ⟨kb,_,ok⟩ := List.any_eq_true.mp rest
  let base := s.filter fun u => u != a && u != b
  have wf : w ∈ (choices a b).filter (fun z => z != 0 && !s.contains z) :=
    List.mem_filter.mpr ⟨form,fresh⟩
  by_cases hit : g ∈ choices a b
  · simp [fastPair,hit]
  · have nw : w ≠ g := fun eq => hit (eq ▸ form)
    have na : g ≠ a := fun e => absent (e ▸ ha)
    have nb : g ≠ b := fun e => absent (e ▸ hb)
    have ng : g ∉ base := by
      intro h
      exact absent (List.mem_filter.mp h).1
    have stop : (after s a b w ka kb).contains g = false := by
      cases ka <;> cases kb <;>
        simp [after,withWire,List.contains_eq_mem,Ne.symm nw,na,nb,absent]
    dsimp only at ok
    rw [stop, Bool.false_or] at ok
    obtain ⟨left,miss⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨dims,cov⟩ := Bool.and_eq_true_iff.mp left
    obtain ⟨positive,len⟩ := Bool.and_eq_true_iff.mp dims
    have hk := of_decide_eq_true positive
    have hl := of_decide_eq_true len
    have hm : locate (after s a b w ka kb) = false := by simpa using miss
    have spec := branch_of hg rows locate k _ _ wf hk hl cov hm
    cases ka <;> cases kb <;>
      simp [after,withWire] at spec <;> simp [fastPair, hit, spec]

theorem fastClosed_sound (g : W) (hg : g ≠ 0) (rows : List ℕ) (words : ℕ → ℕ → List W)
    (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch)
    (k i : ℕ) (ok : fastClosed g rows words count lookup sym k i = true) :
    closed g rows words count lookup sym k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,fast⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    have ng : g ∉ words (k+1) i := by simpa [List.contains_eq_mem] using absent
    by_contra! fail
    have h : moves (words (k+1) i) (fun t => t.contains g || (decide (0 < k) &&
        decide (t.length ≤ k+1) && covered g rows t &&
        !found words count lookup sym k t)) = true := by simpa using fail
    obtain ⟨a,ha,inside⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,both⟩ := List.any_eq_true.mp inside
    obtain ⟨lt,slow⟩ := Bool.and_eq_true_iff.mp both
    have fp := fastPair_of hg rows (found words count lookup sym k) k _ a b ha hb ng slow
    have yes : ((words (k+1) i).any fun a => (words (k+1) i).any fun b =>
        decide (a.toNat < b.toNat) && fastPair g rows (found words count lookup sym k) k
          (words (k+1) i) a b) = true :=
      List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,Bool.and_eq_true_iff.mpr ⟨lt,fp⟩⟩⟩
    simp [yes] at fast


end SignedFrontier

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

namespace SignedFrontier.SmallCert.CliqueFive

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfffefee8fffefee8
def negative : List Nat := [0, 1, 2, 4, 8, 16]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 5 then (if page < 2 then (if page < 1 then 0x4444cccc4444cccc3f003f003f003f002aaaaaaa2aaaaaaa2222aaaa2222aaaa22222222222222220fff00000fff00000ff0fff00ff0fff00ff0f0f00ff0f0f00f00ff000f00ff000ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0aaafaaa0aaafaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a08aaaaaa08aaaaaa02aaaaaa02aaaaaa00ffffaa00ffffaa00ffff0000ffff0000ff000000ff000000f0f0f000f0f0f000eeeeee00eeeeee00ee00ee00ee00ee00eaeaea00eaeaea00cccccc00cccccc00cc00cc00cc00cc00aaffaa00aaffaa00aaeeaa00aaeeaa00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa008aaaaa008aaaaa0088aaaa0088aaaa0088888800888888003cfcfc003cfcfc002aaaaa002aaaaa002a2a2a002a2a2a000ffff0000ffff0000ff0f0000ff0f0000ccccc000ccccc000afaaa000afaaa000aaaaa000aaaaa000a222a000a222a000a0aaa000a0aaa0002aaaa0002aaaa0000fffe0000fffe0000fefe0000fefe0000eeee0000eeee0000eaea0000eaea0000cccc0000cccc0000aaee0000aaee0000aaaa0000aaaa0000a8a80000a8a8000088aa000088aa0000888800008888000080800000808000000ff000000ff000000aaa00000aaa000000ee000000ee000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xcc000000cc000000cacacacacacacacac0f0f0f0c0f0f0f0c0ccccccc0ccccccc0c0c0c0c0c0c0c0aaffffaaaaffffaaaaffff00aaffff00aaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaacceeccaacceeccaaccccccaaccccccaaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaa00aaaaaa00aaaa8888aaaa8888aaaa2222aaaa2222aaaa00aaaaaa00aaaaaa0000aaaa0000aaa8aaa8aaa8aaa8aa00aa00aa00aa00aa000000aa000000a8aaaaaaa8aaaaaaa8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a888a888a888a888a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a09999aaaa9999aaaa9898f8f89898f8f898989898989898988aaaaaaa8aaaaaaa88f8f8f888f8f8f888cccccc88cccccc88aaaaaa88aaaaaa88aa88aa88aa88aa888aaaaa888aaaaa8888f8f88888f8f88888aaaa8888aaaa8888a8a88888a8a8888888aa888888aa8888888888888888888088808880888080aaaaaa80aaaaaa8080aaaa8080aaaa808088888080888880808080808080808000800080008000777700007777000070707070707070705f005f005f005f0055ff000055ff00005555aaaa5555aaaa555555005555550055554444555544445555000055550000550055005500550044cccccc44cccccc44cc44cc44cc44cc) else (if page < 3 then 0xfcccfcccfcccfcccfcccf000fcccf000fcccccccfcccccccfbf0faf0fbf0faf0fbf0f0f0fbf0f0f0fafafafafafafafafafafaf0fafafaf0fafaf0f0fafaf0f0faf0faf0faf0faf0faf0f0f0faf0f0f0faaafaaafaaafaaaf8f8f8f8f8f8f8f8f7f0f7f0f7f0f7f0f7f0f0f0f7f0f0f0f5f0f0f0f5f0f0f0f3f0fff0f3f0fff0f3f0ff00f3f0ff00f3f0f3f0f3f0f3f0f3f0f2f0f3f0f2f0f3f0f0f0f3f0f0f0f2f2f2f2f2f2f2f2f1f0f0f0f1f0f0f0f0f8f8f8f0f8f8f8f0f0faf0f0f0faf0f0f0f0f0f0f0f0f0f0f07070f0f07070f070f070f070f070f000f000f000f000f0000000f0000000eeeefefeeeeefefeeeeeeeeeeeeeeeeeeeeecccceeeecccceeeeaaaaeeeeaaaaeeee6666eeee6666eeee4444eeee4444eeee0000eeee0000eeeceeeceeeceeeceeecececeeecececeeeaeeeaeeeaeeeaeeeaeaeaeeeaeaeaeee0eee0eee0eee0ecececececececececcceccceccceccceaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeac0eac0eac0eac0eaaaeaaaeaaaeaaae6e6e6e6e6e6e6e6e0e0e0e0e0e0e0e0ddddccccddddccccdddd0000dddd0000dcccdcccdcccdccccceeeeeecceeeeeecceecceecceecceeccccfcccccccfccccccceeeecccceeeecccccccccccccccccccc44cccccc44cccccc4444cccc4444cccc0000cccc0000cc4c4c4ccc4c4c4ccc44cccccc44cccccc444444cc444444cc00cc00cc00cc00 else (if page < 4 then 0xffff0a0affff0a0affff0888ffff0888ffff0808ffff0808ffff00aaffff00aaffff00a8ffff00a8ffff0088ffff0088ffff0080ffff0080ffff0008ffff0008ffff0000ffff0000fffefffefffefffefffcff00fffcff00fffcfcfcfffcfcfcfffcfcccfffcfcccfffcccccfffcccccfffafafafffafafafffaf0f0fffaf0f0fff0fff0fff0fff0fff0ff00fff0ff00fff0fef0fff0fef0fff0faf0fff0faf0fff0f8f0fff0f8f0fff0f2f0fff0f2f0fff0f0f0fff0f0f0fff0f000fff0f000fff00000fff00000ffeeff00ffeeff00ffeeeeeeffeeeeeeffccffccffccffccffccff00ffccff00ffccccccffccccccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff88ffaaff88ffaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaaaaaffaaaaaaffaaaa00ffaaaa00ffaa55aaffaa55aaffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff88ff00ff88ff00ff888888ff888888ff80ff80ff80ff80ff77ff00ff77ff00ff22ff00ff22ff00ff0aff0aff0aff0aff0aff00ff0aff00ff08ff08ff08ff08ff00ffaaff00ffaaff00ff88ff00ff88ff00ff00ff00ff00ff005f00ff005f00ff005500ff005500ff000000ff000000fefefefefefefefefeeefeeefeeefeeefcfcfcfcfcfcfcfcfcfcfc00fcfcfc00fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcecfcecfcecfcec else 0xfffffff0fffffff0ffffffc0ffffffc0ffffffaaffffffaaffffffa0ffffffa0ffffff88ffffff88ffffff00ffffff00fffffcfcfffffcfcfffffcc0fffffcc0fffffc00fffffc00fffffac8fffffac8fffffaa0fffffaa0fffffa00fffffa00fffff8f8fffff8f8fffff888fffff888fffff0f0fffff0f0fffff0c0fffff0c0fffff0a0fffff0a0fffff080fffff080fffff000fffff000ffffeeeeffffeeeeffffeee0ffffeee0ffffee00ffffee00ffffeac0ffffeac0ffffe0e0ffffe0e0ffffccccffffccccffffccc0ffffccc0ffffcc00ffffcc00ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaa8ffffaaa8ffffaa88ffffaa88ffffaa00ffffaa00ffffa8a8ffffa8a8ffffa888ffffa888ffffa0a0ffffa0a0ffff88a8ffff88a8ffff8888ffff8888ffff8880ffff8880ffff8088ffff8088ffff8080ffff8080ffff8000ffff8000ffff5000ffff5000))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x12077a8652f337c8dea93923d131287a1be48f449c71dea1 else 0
  | 3 => if page < 2 then (if page < 1 then 0x8b3994e517bb29425d883bd7e6f8bbbd0e15923ad0e6f82b294e29923954e5174b88de2c87385889392bad0e6f923a52c6f923a57e6f8d3bd7e6f923a50e15923b10e6f7bb914e238dbb92c6f94ba10e6f913bd7e6f923a50e13873298c628fbbd0e6f7bbbd0e168bbbd366f7bbbd7e157bbbd8a61923a5346f7bb85881b933a50e6f7bb84de1c923a5425192ba50e6f7bb2968298e3bd0e6f7bb2988278bacd0e6f922c90e6f923a5c421923a44c218dbb90e217bbbd7e218dabd0e6f8732988217bb29425a8bac10e6f68ac90e6f8bbbd186f922b10e21923a50e588bbbd126f803bd186f923894e58922b10e58922a90e6f7bafcde397bbbd0e338bbbd2a6f923a57a6f923a50e32923894e328bbbd7e6f923a50e21922b10e6f923a50e6f else 0x923b50e6f8cbbd806f923c94e15903bd0e6f8db91866f923c10e0b922b50e6f922f10e6f923a90e6f90ab90e6f922ed0e6f88bbd7c6f) else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x7bb2d4ea10441596a7439bdfacd53a1cdf0d6729d0e6f00491588737bdd94a650821eee26529cb0f7652b10e587bb290e7d2c3dd94a750809f0ca53a1cdef76529d0e657bb294ea02a3dda0a743951eea4439bc730e65310de4c7bb294e8719bdd94a73a9bdeeca6224c98f76521cde38813294ea128c15a4a7439bdeeca60a1c43056a29d0e6f7bbbd48871945d94a7438c9eeca5fa9c64f76529c6c217bba5948710bdd94a71308614ca53a1c42f7652dd0e217ba9d0e3710c09a4a7439bdeeca5ea9c64f76529c6c32813294e8737be594a7439bdeeca53a1cb7016529d0e6f7bb294e871ebdd94a7438c9eeca5b21c42f76529c82217d3294e8737bdd94a743961eeca53a1cdef76f2e10e0b7bb794e3f05bddbca74382deece53a1c170d6f29d0e6f6529d0e6f16435bca74382e48db53a1cdf056529d425100491d28737c918ea743885eeca53a84112453a1cde2c63a9d0e6f163dd94a7509460aca53a1cdef76529d0e21 else 0x923a50e6f01c3994c43798a48f174a1cdef765311260e8bbbd0e6f02bdddebf3798648e950a1cdef777afcde0b923a50e6f28c91d28737885eea74392042f7652d10e217bb294e7828bdd94a750875fcca53a1cdef76529d0e4f6529d0e2c10c914e87160858ea7438b0432474b1d0e217bba5c4ca10c91c4a74388648e96521c4200923a50e219231d4e2610bddd2ca13085eeca1509843246da9d0e217bb914e8010c3d94a743885eeca6121c42f76529c68217bb294e7637bdd94a743855eeca621ec430e6529d0e217ba9d0e3e10bdd948737969eeca53a1c34f7652a10e217bb294e8210bdd94a73c0760aca53a1c42f764a9d0e217bb29528710bdd94a741885eeca53a40a2f76aa9d42087bb29424904415aaa7439bdf4ca53a84a2f7652c50e2182b354e8737bdd94ac43885eeca52a84a2f774b290e587bb294e7c10bdd94a72c885eede53a1ca8ca53a1cf26f9229d0e7937bdd94a74f0220aca53a8410f765310e46f) else (if page < 3 then 0x9229d0e6f16bdd94a750971eeca6323ca3126529d42517bbbd48870ac914e873d1be10ca53a1cdef76529d0e1b7bbbd0e6f03491b4a7439be48e553a1cdef765310de0e82b294ea107bdd94c449989eeca53a84c32474ae90e6f8bbbd0e6f05bdddeb54382e48e2539bca2f7653154e51853814e8705bdd94c449945d2ca439bc592474a1cde2c74b1d0e6f1645ddeb5439be0ad553a84a3056aad10e6f853816e87378022eef5f9bdeeca62a9cc3186aa9d0e6f7bb854e870dc3dbca7439bdeed653a1c2b176529d425189b294e8737bdd94a74389e2ed553a1cdf0a6629d0e6f7bb2974873142daaa7439bdeeee53a1c2b0a6f29d0e6f8533d4e8737c1d94a75094612ca53a1cdef76529d0e2383b554e8737c29aaa7439be48ef74a1cdf246da9d0e0b86b794e8701bdd94ba4b18a36ee5d21cdf2474a1cde0b7bb816e8705c45c6a737946532474a1cdf1777a1cde069236d4e8701c91d2e8439be4f2474a1cdef76aa9d420f else 0x8ab294e8737bdd94a74385194a7439bc22f76529d0e6e863294e8737bdd94a74384994a7439bc33167329d0e6f84b5d4e8737bdde4ca53855eeca5385c2b147029d0e6f7bb814e8734479deba439be1adf53a1cdf246ea9d0e6f84b2974873100248ec439be48e753a1c2b1b6521cde1873b290e6f0c491b8a7439be491b72310df278dbbd0e6f7bb91c0a707bed94a7439bdeeca53a1cacf77329d0e0b923614e8705bdd94ba4382a491b77a1cdef7652e90e53833294e8737bdd94a74387deeca53a84a7248dab90e6f7e3814e8705bddbea74382e1ae053a1c06f7652e50e037bb295687313ddb2a74382deeca53a1cbcf7702a10e0b7fb394e8737c1194a7439bdeeca53a1c5d036529d0e6f7bb294e8717bdd948737861eeca621f8def76529d42557bb294ea126bdddea450945eeca53944532469a9d0e6f)) else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0x6529d0e6f25021eed553a1cde087bb290e6f248220aca53a1cde517d3294e8737945eeca52a1cde517bb294e8730145eeca53a1cde4c7bb294ea13782000f76529d42087bb294e93439be0aca53a1cde080041594a7439bdeeca53a1ce46f7bb2d4e873782000fa6529d0e6f7bb294e8737961eeca5321cde08003dd94a743961eeca53a1cde027bb294e8735821eeca53a84a24c82b294e8737931eeca53a1cfe217bb2968873793204ca53a1cde517bb294ea4438c9eeca63a9d0e217bb294e8733885eeca53a450e6f813294e873793001026529d0e6f7bb294e87378c9eeca53a8d0e32003dd94a7438c9eeca53a1cde077bb294e873792deeca53a1cde217bb294e873308400f76529d0e217bb794e873782deeca539bc7e0b7bb294ea14382deeca53a1c400b7bb294ea1439be1aca53a1cde0b7bb294e87399bdeeca53a1cde547bb294e873780deeca53a1cde087bb294e873482d94a7439bc860b6529d0e692182deeca53a810e0b7bb794e873482c00f76f29d0e0b7bb294e691f82deeca53a1c76087bb294ea1379461aca53a1cd20b003dd94a750945eeca53a1cde517bb294e873782c00f76529d0e6f else 0x7bb294e934382deeca5fa9cde5182b294e873782deeca53a58de5182b294ea13794401056529d4251873294e93439be0ad553a1cde5100415aaa7439be3b056529d0e6f7bb294e934383a2eca53a1cde057bb297ea7379862eca53a850e6f7bb854e873782e2eca53a1cde5186c1594a7439bdeeca53a7d0e0b853294e873780deeca5a21cde6283b294ea1439bdeee353a1cde0b7bb554e873782e0eca53a1cde5182b294ea1439bc010d6f29d0e6f0000248e9439be48c753a1cde217bba594873788594a7439bc8e0b7bb294ea14388594a7439bc740b7bb294e871882deeca53a1ca2217bb294e873c1bdeeca53a1cde4e7bb294e8737815eeca53a1cde1d923298ea743884012463a9d0e217bba594c743885eee26529d0e21003ddd2ca43885eeca63a9c4c217bb294e6f1308400f76529c4c217bb6d94a74388648f76529d0e217bb9194a743885eeca539bc800b7bb294e6f1302deeca53a1d00217bb2988a743885eeca539bc6a0b7bb294e873d885eee06529d0e217bb2990a743885eeca53a1c420b7bb294e871e021eeca53a2d0e217bb294e8740885eeca53a1c62057bb294e8710875eeca53a84a208) else (if page < 3 then 0x7bb294e873b82deec853a1c400b6529d1a873782deeca53a350e0b7bb2974a743951eeca53a1cae0b7bb294ea1439521aca53a1cde547bb294e94439bdeeca53a1cde1e7bb294e8737825eee053a1c16037bb214e873780df8ca53a1cde0b7bb294e873602e1aca53a1cde037ba9d0e6f2100deeca53a850e037bb294e871800df8ca53a1cde037bb294e87381bdeeca53a1cde637bb294e8737805eeca53a1cda037bb294ea105821eeca53a20de087bb2d4e873782deeca53a18de0b7bb294e873502deeca53a1cde297bb294e8737941eeca53a1cde557bb294e8737935eeca53a490e6f7bb294e8737891eeca53a1ce26f7bb294e8837945eeca53a1cde2c7bb2974a75094622ca53a10de0b7bb294ea12882deeca5d21cbe51923294e87378b194c753a1cde2c003294e87378b1eeef6529d42517bb29887b3782deeef5221cde517bb298ca75094648c753a1cde037bb294ea12883deeca53a851e519231d4e87378b0012453a1cde2c0031d4e87378b1eeca5a29d42517bb298aa7439bdeeca53a1cde0e7bb294e8737985eeca6224d0e6f00491b6a7439bdeeca53a1cde628dc1594a7439be1cca53a1cde0b else 0x1eeca53a5d0e6f7bbd994a7439bdeeca53a1cde107bb294e87379a1eeca53a1c8a038b3294e873783deeca53a1ce86f7bb294e8737949eeca53a1cde047bb298ca74398a24ca53a850e6f7bbbd94a743855eeca53a650e6f84b294e873798801096529d0e6f7bb294e8737855eee76529d0e15003dd94a7438561aca53a1cde0f7bb294ea14398a470d6529d0e6f7bb2988a73783e22ca53a84de0f7bb2988ba43989eeca5d21cde62003dd94ba4398a49117029d0e6f92435c0a7439bc01248dbbd0e6f7bb294e872202deeca53a1cde647bb294e8737829eeca53a1cde227bb294e872302d94a7439bc8c0b7bb294e9c4382deeca6329d0e0b7bb294e871402e48f77029d0e0b7bb294ea10682deee47029d0e0b7bb294ea11282e22ca53a1ce26f7bb294e9d4382e230d6529d0e6f86b294e872182e1aca53a850e0b86b294e871002df8ca53a1c400b88b294e87399bdeeca53a390e0b7bb2988a7399bdeeca53a290e0b7bb298ca7439bdeeca53a1cde0f7bb294ea2439bdeeca53a1cde0c7bb294e873794e48fc6529d0e6f7bb294e873982e22fc6529d0e6f)) else 0
  | 6 => if page < 1 then 0x3dddeca53a850e6f7bb298ca750a1cde007bb298ca7439be48f76529d0e6f01bdd94a750a1cde0f003dd94a7439bc1ef7653114e873798800f76529d0e6f313dd94ba53a850e6f004461aca53a1cdf117bb294e873782deeca53a1cde0d05bdd94c453a1cde0b7bb294e873789416f76529d0e6f2182c00ca53a1cde4305bdd94a750a1cde0b003dd94a750a1c16f76529d0e6f1582deeca53a1cde2005801eeca53a1c400b86bdd94a7439bc16007bb294ea1439bc010d6529d0e6f05bdd94a74421cde0b003dd94a7439ccdef76529d0e853782c00f76529d0e6f2a3dd94a7439bc1603003dd94a7439bc06f76529d0e6f0582000f76529d0e6f28bdddeca53a1cde517bb294e873d9bc16f76529d488737945eeca5d29d0e6f28bdd94a743a10de0b7bb294e873794416f76529d0e6f2f945eeca53a850e6f28801eeca53a84de5100001eeca53a84a2f7652d14e873794400f76529d2687378020aca53a1cde51000020aca53a1cdef76531d4e873788400f76529d0e6f10801eeca63a9d0e2100001eeca53a1c42f76529d0e6f2882000f76529d0e6f043dd94a7439bca24c003dd94a7439bc98f76529d0e6f3482c00f76529d0e6f05801eeca53a1cd20b else 0
  | 7 => if page < 1 then 0x1eeca53a850e6f00001eeca53a1cde0b00001eeca53a1cde51 else 0
  | 8 => if page < 1 then 0xf76529d0e6f else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 7
  | 3 => 76
  | 4 => 248
  | 5 => 253
  | 6 => 57
  | 7 => 3
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 512
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 9)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (9*(k+1)) i)

def entries : ℕ → ℕ
  | 2 => 23
  | 3 => 242
  | 4 => 720
  | 5 => 876
  | 6 => 229
  | 7 => 40
  | 8 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xe0c73ec2de4893eed694e266d4cb9fa8c9d3f50cb1c28da5ab5231a8a2ac6f81969c1ebb822d32ed820700be7e737d747732b7dd7456031e4433403143e7942c3c3b71b23b82bb14373005842f73a39319e8ae4f1686085e086ca1e8 else 0
  | 3 => if page < 4 then (if page < 2 then (if page < 1 then 0x3ca9e0003c80b44b3bc13d4b3a44a7ff39c3c04b38ddfac437fc639c374e569b3701bd5635b713e235122ff33457dc5332a74e2a30f95e32300ad27d2f1d20c42ef9691e2ef229332d8b26122d523aca2cda181a2b36d5122a568f3e299d650e282635eb27e2d14b276c0a0425530e3924e6778f24cfe5dd2256c9c620e37b161effadd51ddcdd7f1d48dbfc1d146be91c752ec819fece1d19de496b195b1af81893d2bc184a6ce113bbb7e4132cdc0812fae07b11d91232116b3c5210bdc24510b7312c0fababce0e1b0bc20de22ae40dba77220ba905430b76d6790b60b4c90b1643e90af21baf0ac080b20944822e06ae26c3034b9239030b133e01c7af2b else 0x7be7b5067b9a2bfe7b97f0967943ad2c7821cea8773f11f67687ec987639526a72b456eb71dc627170da9fa770b715926fb23f2a6e75fe596e1885716dfa18376db935316d2633376ca4d7ae6c9671fe68263fe067e07c7a6738746d662f485e65cd213664e13bd664c03b1c6401b0fe62720cd560714ea9601472375ecf78715eb4d8265cce774c5cc1e1a95c1d146c5b0a12a859a6ea5c587fa5c357192f8f563bcf0156052faa539617aa52ab0e0651d188f251af6da0519a1b00502c83854fa41a1f4c8c2d364be440db4a226b584a0a1c7548d66e1c4853a1be438f04ac43808c2b429d95b9421635b441ab68cb4148a2903db724d43d6ef51f3d480d70) else (if page < 3 then 0xba6c924eb9dc3bafb9139ec9b8746ca0b72bc75cb720536bb587cedeb5690e47b4b6a086b491c429ae26303ead7fe8a4ad50d99bacbcc841ab94735eab5ec3b6ab0d156eab070b08aa5a25c6a8f44e47a81b4bf2a71a6e9ca68dbc24a6664146a64193aca5c14651a416b4aea365989aa33b2edda15d08a4a141ac05a0d32407a09cdf509f3dbb4f9f165b779ddca9bf9b80fc089af0a5699ad054119a2830de99ae148596f5c1c794a2b68991da1831910dc22b8ee1a6258e71d64f8daac6548d38499e8ccc2a678bb4cf208aa405bf8a10949b89eb5dea8764c68486770567861c19f984fd894583e9266c837ec8908358cc22817495ac812534c880f13abd else 0xff5a8829ff056c88fd689a4dfca6bee4fc4853cafb3b6db0faa9027ff8639fb6f81e8824f77e62a7f3e087f7f3956207f2984700f1d03972efebc0cdef106eeeec382477e9cd2487e91f8ce9e72095dbe6fbeff4e4b625cee1eab895e1b20f8be019d642dfbe7d42dccce7dedc9db417dae02da3daace649d792d15ed6169cb8d5e42ee0d32695bfd24ac290d08e8fb3cacba526ca70416bca384318c884aa41c85445ddc76e99a8c7436e02c656db99c5985358c2ff224fc1993e5ebf887596bd6ac86dba6dc6e7)) else 0
  | 4 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x12ac4389129f5fd412454b9c11bfbb9e11721e0b113ffa9f1126168d1017ebcf0fc901020fb198ad0ec9b8780ea765340e8fb14d0db7c1bb0c53c1270bf053330bea87810ba905430add516f0ac080b20aaedb9c0a57efc20a38514709cdea02091a1d3f08ceb0dd08bce33b088fb395087e3798087259c3084e6e6c07e4647007cf8b8d07c3cf1107ba0ce70783f5640774c6eb06f5d8bb06e6c7d006ae26c306aa3ef206a2747d06960f17061a074d0612b90405dd2f71043bc346041a0ec40409d94303d18ebf0385ca240349dac702e1843a02ac1f1d0286b0e20280c3900251e72d0221db50020266d701ef7fd5013b76d8013031c70080b9c2002af814 else (if page < 2 then 0x290684b928d13d0c27fa6ca9279756a0276c0a04271789c326ebf47c26bb2c952697992f2668899b25caf7be2598e3a9258a9d6e2571dee7255426b0254f42c3251f6079251d3f89251c2a3d2506d79d24cccd11246558842378273a2325549522cf4719228795b222456ab121ddf47821d0137621bd2769215f0f2e2121f1d020f522b320eca07a1fe43e701f9be50a1f22d9261f01210a1edadef11e62e4f71e493d201d8fd48a1d5095bd1d378dab1b7500e41a5fd5de1a42c31a19a3c1c319357c1018d1976e180dca5b17b3bb41162aedae15eef35c15996dbd1557dd4114a22b12145ee866143270bd1408585d13d4efc513ca5f8313424563133c61fa else 0x3e94a7683d993fdb3d8e18923d86b2923d1a4e9c3cbf315d3cb827743c56c6233c3a56bc3c39169a3bd20da53b46e4883aecb73c39fdf28739fd45ec39f5d03739e1126438f5e19438ddfac438b3135f387b9027385e27fa38169979376abcf3370c33e2370241e23666e68c35ba7eaf35b3e6b935b2570135a97c0034f6da1c349cd57a341c05ca3335e12433081aaa3302b5db32fee55e3287c5f0322194c331cdf52c318af61a313dbd8730f95e3230f8738f30d7d7702f3926c32e34f5172e271b9d2dc0b9532d9726322d8fe90b2d764d542cc389122c2b9e4d2c20bbb22bbe3b2d2ab3c6e32a6bbdc82a13d49029d8ec9a29c2910a29a1c3fb294b305a)) else (if page < 4 then 0x57ee8ab957ec37c157dc40fb573d2b47569a2d535667e59b564cd68555fea5165596eef0550e0e0b54e2cbe854cc331c54bdc98454b301cd543eab5e53fa475752e1627b522b3f2051a5d151519397215130476b512a7bb94fe7ed684fc946944f0cd4e64ef178f64e2a18344e1723324df2fd534d2458a84d1ba9574c8d76324b84b3af4adeb36f4abea08549f0766e4932766a48555e3a4836c6a04820cad74820bce347b4ddb847086ccf46d970e446a8646f4699ecbe4639e12045e3d4ef451ed3b3449e2d28447705f9441f257243c5551043c48526422e1f4d420bd9dc41971aec416b885a40825dc8404c119b3eee15bd3ecdbe4a3ecb82b83ec9a6a6 else (if page < 5 then 0x6e8b91d96e6b52da6dbb5eef6d766ea66d150e446ccccb2d6bd604e66b7e01766aee6cf66ab87f036a9cc01b6a86a63a6a7fb7e76a007e6c693a63d9691838636914de1568c4ad7267e07c7a66fccaf666f5c3df66718afe663359d265f4f4c765aa9e666546d4ce6545c14c64f71bed6420bcd16401b0fe63fad57763d70dbc638650e663552b6a63540cca62c6c79662869548625e03316225f81c61f6f4f6616838f46119b59360a7e8bc60a436a46095a156606bfeb5606a0a676010e28d5ef5b2ed5ea5b1635e2aa1665df5e04b5d5eb4e95d3ff0bd5d3231cb5d128bbc5d0bc9da5c3b44f85c1d146c5b0a12a859e12f13591d917958a29e05585c797c else 0x843bdfd98427086083154c1482feed148217c16981f81bac815f4f1981501eb48144b246812534c8811b02ab80560ed28045a51a80306bea8007ddbd800682227fb599987f27debc7e4e024c7e0310327d2c99ea7c7525207c48f6837b6e706e7b3e6a437b36b65f7b0ba3a27a509ed87a46dc867a3324d77a26351b79558c7e7936661978ba138a78480ee278290b9d77a3dda57783714b76b64b527674b878763bd7df7566d17f755749f774f414ac74c18429749ef48973e6a9b2739d73c7739055e3738aa9097344731d72ed394972b456eb726c024671dbaba7715d2c8c713a237f70f97aa770a5d0a97059885470316063702f0c5e6f98ea8f6efabe33))) else (if page < 9 then (if page < 7 then 0xa15b47a9a15aa7f6a11efce1a0870f4ea0722cd1a0548c05a051c47aa04eb70aa006664fa000c1379f43f0ca9f3f4c1b9f15d7729e2e74409dd599f79c9e7b5a9c2f70e89c20c2939bef29a59b81f39f9adca6499ad5107c9a6379799a338e7e99ea288d9808aaf0974e5ca09719384996f5c1c79684af539677816f9675b875965943919462441893f5d67992d259489269fcc7919fb4e89158cd2591566bf2914fe1719085dcbd907211d39025d3158fed15098fd968d68f1adaa88ed47e378e57a2d88e4fe7068d076e0a8cd35c8b8c73083b8c5414858c1849838b3884488b2057d58af7428b89c693f6882fe11f8672db718511367c84a2c079844147b3 else (if page < 8 then 0xb8491bd0b83859fdb7be0f33b7b612b8b767d30eb727c9a4b704dc80b6ae70e4b6a0feddb681658ab65b464db624d06ab45b4a44b438cbe1b407346eb404ce3bb3b2c03fb368493cb247c0e4b1429844b11a431fb0d8bf7ab0a9e8e8b082ca1fb041f114b02870b5afcad618af7dd29faf1d2abbaf0d2ad1aed8ab4faeba3505ae7dd79cae39024ead555bd0ad3b77a3acfa06b8ac366a67ac2326c2ababd37aab90119bab80c6d5a97ea5a4a94ca6dca8b55932a86babe0a81b4bf2a78332f4a751a16ea7321526a6e7ec28a6b264c8a659ab7ba556db11a4c3327aa3a032f5a3598719a30185b5a2ec8699a26b85c7a265ba15a1ef6347a1ea835aa15d08a4 else 0xcca5a9a9cc7efde3cc4a5addcc24ae94cc19e4fbcb41be44cb3ff88ecab07617ca62ac89ca2fbdd8c9f0cc21c9a6cab3c9999b7ac9834d3ec91a294ec7a61c4cc6eda3a6c59d8d82c576753fc54541c1c4aa091ec3dd5890c3a8413bc3618645c3232ab5c2d5b8abc22fb227c20973d8c206f766c1915435c0fc1f2ac0b82ac5c0a1140cc067364fc045615fc041bdbac01fb135c0118237c00c474cbfb9524cbf9b4042bf61ef54bf40224bbe7a9f58bdf86effbcb87927bcb0f138bca8a810bc37c97ebbee1d90bbe8c2a8bb7c440abb71f1f7bae29ff5bab9a0baba943f50ba93bf79ba79eaf9b8f8ca27b8bd1398b8b139f5b8a2da47b89c6e8cb859270c)) else (if page < 10 then 0xe3c69081e2b38ebde2940b81e286d607e2014a27e179f0b2e0cc9cf9e0be054de08c9b23e07bb590e036ed04e02f886ce019d642df8caa52df8b2562df3a0a3bded67679dec123d9ddfb3921dd992d01dce76b74dc84d878dc58755adb00d595dae02da3d9ddeb3fd9c0e33ad9754971d936fb6cd8870c70d73f48cbd6f3e19ad6938854d6421657d630b182d502cee2d4c604bad4879cb6d4749ec0d45a6afbd44b2c57d3fa82a6d3707df0d3335a08d32cf550d3278d79d21e3862d1ddb963d1d568b3d19408bdd1638b82d0b32cf4d08ed828d06093afd0546687cffac2d9cfdab03ecf5c4526ced4ac66ce36a546cdfa5087cdeb09cecce7aab0ccd1b0b6 else (if page < 11 then 0xf9b4bf7cf941fa2af8e94d1ff8e47014f8dafb09f8594ba3f843ffc9f7e734bcf77e62a7f7262c3ef717bff7f6a1690bf609fe3af5c38663f593d030f5384e32f4dc2370f4c7e3bdf4a70378f4802443f47eb612f402b99df3e087f7f3dd6ad0f2ec563cf2c0b64bf2984700f27e9d96f21894c4f1d5c55ff1b6148ff1551297f1461923f12c5d02f0d1e77eefa18fc6ef34d684ef0dbf5dee65ea9dee353d37edd591b4ed5bd8e7ed119febeca7d441ebdbe0ffeba44ce5ea96cf49e9e5e6b9e9de6674e973006de92edf2ce91441b0e8d69330e8b1398be8196bc5e812754fe752b56ee6f30f7ee5ca4643e5c70386e58fbc26e55013b0e4ef05a4e4c337af else 0xfffc5d7eff9010a9ff4daf90ff3fd4a3ff113c29ff056c88fef01e56fe6e117afe571042fd716c36fd4a9044fcfc6c92fc605f91fc5726b4fb9c478bf9f69ffc)))) else 0
  | 5 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x11f36b3111c0552511afd4b110e8f8c510d52724107b2783106e0f0e0fc901020fa14a7a0f31e6f10f2d77450ec9b8780ec3da330e910b5d0e33eb1f0df2e2170ded48200de56d930dd2e28a0db7c1bb0d9b676f0d9b33cb0d998bcf0d384a5d0d1183680cdf08a10bf053330bd60e840b65618d0ab165380a6398880a526ff50a5111250a13272009e9eb9c09a87a7e0965680d094db4e40925a93408bce33b08b8fb6a086cafa907ef6f5f07e464700790ab26072fd627066d6c1a06018bfc05f9ff1f05b3e8d10531c088046916550385ca240331fb1603235bb102b51fb7028960dd02600a640170e5e1015c31b300fedace00ad9748008cca3900363698 else (if page < 2 then 0x24cc3b252417036e23eda1d223b9e87923a36f892317b1e422aad420221acfc221c9b9ad20ca1be31fc6b7f01f8451fe1f66505b1f01210a1ecdfcfa1e6c7bb91df3730d1daa0e5e1d8fd48a1d84f2fc1d4531441d0c5f551ccedb2d1bff940e1bbf41811b11cc4d1ad1e8591ac6378e1a8bbdca1a7c985f1a16b5c2199fb357195770401919258b18b527391882212a17f01a621771ff86173717d91716f07e17140bae16f6a62b16c902a616c8e3a816c336f416aa0bd8168e767b15ee443915d91bfb15b8c4881564472615242c8114f78de414e71641140a430a13df554213d4efc513bd1eee1380961013255cfa12bd13e312454b9c12228d5c11f936e3 else 0x34a5234b347495183414867a33bf6c33332a697533081aaa32fc894132b9aada31cdf52c31c1433e31b3fc4131ae308f313dbd8730d7d77030c82cbb30732f8d302cd6232fd9c0e92f8765002f7e85532f78b9a12ec97e502ea3be822e91683d2e81c7922e6872b12e4a2fb32e05a8382dd8ce082d77ac742d653e562d52ebd92d0057262cc528c12cb6a3eb2c95d6dc2bcdd2262bc54fed2bbd6e272b8371f42b6d10772b5875a42adee2692ab3c6e32a4e63ee2a43a4192a13d49029afe2412921a48228d7131a28d3bf4b28103d1e278d295b278aaf84270aee5926d2f3a6269b0bdd26898a192628bdaa257f9cfb25211524251f607925147e3c250b2269)) else (if page < 5 then (if page < 4 then 0x45db741c44e677b444828f80446676b44417b97b4329589d42fb36b942dfded842c10b244295b5c0425ace134223b77641ef76be410190db40b74d4040a027d340822b73405ff2e3405679ea3fc03cd63f8080843f803cd73f4472343f17b1d23f166c8a3ef02fe13eee15bd3ea44c4a3de0ca1d3dc884de3dc716d03da5c66e3d1b87853d193ff73d10d8f33cc702613bd20da53b6267d93b569aa63b50cef43b16caec3b0bc30f3af1a2233aecb73c3a113ab439e7906d3910fe5a390d11b438c2e72138c06aa438bd420938acd871379932c33792eefa3780a794374aabe337274eb436b615a336a92f5f3648044d36385af235f337f93515a7a434d05dc0 else 0x5680c09a567f477d56672eb555cde0155590c9d55582a04f553ca19c5530ee52552a19d85514572354e4860854d891445437622c542879f8535fa4675307b0a7526dd2215262e971522970815221bc9d51f6a9e0517bc024511e2b15505eec4a505079bf4feeda914f1197cf4edd9eb34ed7d3014ecb0eab4eb3e0c34e9d7f464e75286d4e22b5d04e0001ac4df2fd534dddfb3e4dd2c6504d5b21e34d5408f74d26de1d4ce4894f4c9dd51e4c88827e4b4bfae74b3496474aacfc6f4aa9046d4a71f7814a64a0d1496d262d4968739c4882ab1b487d7c2a480e086b47f141c54790d6e74765582847448e92471a129c46a5a76a4699ecbe46425bde45e973d0) else (if page < 6 then 0x6875633f68417230683ae7af67ee5cf6677c99bc66f5c3df666a9fee665c298b664487b3662f794966190313654425c46542a91664e41b6664aa72e964477e96640bebb86401b0fe63da09b063d08eab630b646d62f37e7662d0617f6264b5b9625c576d6225f81c60a7e8bc5f59cf7b5f3956df5efd7d3b5ec24cc05dfa45865d289a975d0eb66a5d0bc9da5d00f8635cf14f9a5c4b84905c2102755c1d146c5bf5ae385be0352e5ba848525b9897625b508c5d5b2c4df15b26faf75add194f5acf15985ac9a1925a3246b959e9f352594aa9ae594151545902c7a758f725e058cbc3b858c18ef257c800b35787737e56f1886056bb2aef569a2d5356964cca else 0x79558c7e7944665b78dbf16c78d017f6788c43e378480ee2782aadcc781615d977af80a877915bec77854b767772158c776888b176ebc77576b64b5275ddb43275d7e88075c1746675a6595274fe39fb74db973074a8f4d4748b847c74853e9f747d47e573f9e25a73ed8d8873e6a9b273c6e75e73855d14734d9b357344731d731603d472fb986d721217f071d1c56f711e94bc70a87eb070962a9a707452d37037177f6fde1e906f6380876efabe336e30c90d6e2440626e211a0e6d9f77096ceea62e6cb9102b6c882f036c4ede8d6c460d366c3f5ba36c1200f96b34a33b6aed57ad6ab87f036a3436aa69cb733869bd5f866961130169172a0b68e3d62d))) else (if page < 10 then (if page < 8 then 0x8b3884488b149da18afb44cc8a28dbbf8a0ff3bb89ed41b18962cc1589577d0a890d4a218905e205884ec1a88827dc6287ac6ccf8724eeaa86ef56098671bdf785bbc37585ac9c5c856ac59784d42cd684b6a9c2846beb97844147b384267de1840f158c83e50cf6837b48c48343bcb782444b2282236d6a81ab446f81a63aab815282b680d99e3c808e1ae5800682227fe3e8967fde245d7fa547707f6719de7f56b21e7f1088c17e9c4b9f7e33e3a47d949b6b7d5b7c6e7d44b1b97c41e14f7bfc4d7f7b6504ef7b62184d7b5050d77b0ba3a27b07bbd17ad6cde27ad528a37a86a5547a77842c7a18e97679e093c479cd632979c7977779734d267968f73a else (if page < 9 then 0x9dfbf04b9daaabf79ce4cbfe9cb3ccb89c79fa5e9c60c3879c427f449c424af69c26076c9b7d295b9abaa6ce9a48fc849a0c0c639a04823099eb3f5499c71cce991e825c987b258898608932984df282978c1a4a977818a5972cc3f896e976509673348d965de4fe964cf59295ac43f99523527794e3753d94e115c0939d20229399cf489393ae4e9365286a925cf83591bc99e991b6ce3791b4075891ae99bf9163067e913126b290e12a5890665f509021f28c90054c998ff2c7b58f8de0858f5fe9198f442d4a8f23603b8ea9b5408e8622288e3756538e194c858dd6bd9b8dc307ee8dc29de28db0ab268d89b7788d3eb5e58cff1bb58bf7ebfa8b9f7646 else 0xb2609262b25c2bb5b24a875db2263a22b19cc10bb1416a22b12b08a5b109c89ab0f30cb1b0604fafafdbc8a6af7dd29faf6954a5af17a434ae5e327eae39024eadf1d403ad58ee80ad555bd0ad40628aad3b77a3acbd3f67ac3a6422ac3650d4ac03d241ac022995abf9f006ab90119bab5fbec1aae8ede4aacf4869aaade9f6a9e1af61a93e2b93a91c538ba8f6f583a8b415e1a8ab59eea7d07295a77f26bea739b79ca6e7ec28a6aa9d1fa6a5c516a66dc32ba660bab2a611f520a5d501aca556db11a545f0f0a4768976a3de21a7a3a032f5a3364ca1a26b85c7a13cc21ea0cf84e9a05fce039fd760909f2a5dde9ec505ff9e91228a9e42d8a39e1f4ea7)) else (if page < 12 then (if page < 11 then 0xcc7efde3cc235470cbfe5ab9cb612f5dcb57713fcab6edc7ca6e3274c9834d3ec8311f61c811c7eac7d861a9c7d160b6c7c878aec7b21aa7c782e5a2c6e9cc55c694935dc67e31e0c6228b16c5fb73c3c4b78727c4aa091ec392da7fc29f3a26c28f5323c2819d59c27d8f9cc181d587c170abccc1454317c0a1140cbfd9c9dbbe9cf73fbe9a3e8dbe308944bdc9e6d2bdc8ea88bd572af1bd207057bd00e9fdbcb209c4bc09493bbbf6723dbbae3dedbab196bfba67e384ba471675b9aeaea6b8d46160b878848ab8735cccb823b01eb7e81d51b704dc80b6d2e41bb5dc61ceb5a7ed8fb54dcae1b4fbdc8ab4e47627b4a98e7ab47d8719b35908ebb2eee043 else 0xded67679dec123d9de9f66c1ddd1ce0edda1f5e7dd992d01dd954530dd5bef02dd2b8ae4dc65205cdc52d400db8405e9db48c24adb3a6141db26c984db0bb292da95c8e8da85b747da70d062da39158fd9e71357d9ddeb3fd87e39b0d7e89005d7dab2bdd74666ced73651b9d6963efdd65470bdd62f6babd61f4f12d603f25dd5db2494d5d5818dd5bcfb0ed47b876ad4724aedd44b2c57d4273c32d415dccad3c00440d378a1c7d3707df0d357d4b8d3422cf2d2bdcbe9d2aa542cd26997b7d2431d95d177cfcfd166eb89d116a191cf2c5db2cee109e7ceb4ad4cce7dc347ce6cbb82ce5cf638ce336b0ccd98ddb5cd7db56acd7b0e58cd75bb5eccbaa7f7) else (if page < 13 then 0xf39893d7f2984700f2600722f21ee260f20d123df19f2fe9f1367771f0eabc70f07b001ff03ed090f03da498ef9be722ef21059beec15484ee4f2a99ee2d0f9bedf5b962edd03276edcd3cc7ed3da03fecf91234ecd9f99aeccbdce4ebdbe0ffeba799f8eba54c6ceb609c8eeb512cffeab565c1e9e01c53e9d2420ee96c88b2e90d5522e8f1405ee85d2449e8442691e813aa94e7791ce1e7652e3ae6f30f7ee655ec4ee62c60e0e62162fbe4c20116e4398fb8e434cc75e4017745e3ff6758e3f6e79de3c69081e3745acee3209e7de2940b81e2837a02e1cee7b8e1a133f3e110fc4ee0ab1637e0118fcadfdb7e55dfcec6fddf8caa52df087fbfdf003285 else 0xfff18af7ffcece0eff960127ff7f1304ff5a29b0ff57a6c4fe622f53fe571042fe395118fde85718fd04df86fcb698fafaea597efad2ef23fac677f0fac63564fa4e213ff9d20444f9779521f93b2f75f9333550f9232f82f8c8fab6f8a82da7f8910102f8147404f7e092a2f78f4012f772c8f3f73b9cd9f70e7ba2f6fe9d93f66d2b85f65a5a55f63079bbf5bc25e7f5af575bf575de9ff533808bf5127d30f4a70378f4655a9cf3e726c3f3d492fd)))) else 0
  | 6 => if page < 4 then (if page < 2 then (if page < 1 then 0x3de4be3f3dc884de3d2f8df13c7c5d3e3c35de883b569aa63af1a2233aecb73c3ac149093910fe5a384eea693792eefa369bbb9736855a1a34cc642334a5234b339f3ab233081aaa32fc894131c81f8d31b4a7d031b3fc412dba1fef2b5875a42a4e63ee286a0647259ee7012588858424bdcc8e2484af532250ac7d1f21c9521d8739031d84f2fc1cb838941b10e02a17f01a6217140bae16c902a615d91bfb15646ec2154d192a147db1b013e549e11387dabd12bd13e311c0552511097f560e33eb1f0db7c1bb0c49a77e0b4740e30aaa727108bce33b08b8fb6a06698b9104504494040aa0f303eb5d6403a1aa290380dd1a02e8754b02a8746500fedace else 0x84267de183215712824ac4ff80ccb59f7fa872b47e70a3ff7c9f32a47c88d1277c41e14f7ad6cde279cd632977915bec7601275975ddb432732a83eb714aa6e96f1b1c2f6eab9e1e6c1200f96bf6f0606a882660693a5d8a66f5c3df662f7949650452c364aa72e964477e96622daf555f12e2a05ec24cc05baec2325b5090375b508c5d5b26faf75a8128bd59e8c0ee590e73a8583d88f4581ef25356f1886056964cca55e1ffd75590c9d55582a04f5437622c524d1e8b51f6a9e051f2c20f505079bf4ed7d3014d32b31e4ab1ed9c4a38a1734882ab1b46a5a76a4408dd4942c4f42342b17c66425ace13411f3ce840a027d33f4472343f17b1d23e5960ef) else (if page < 3 then 0xd91e5245d783c1f6d6b9d44cd570efa2d4df3593d44b2c57d1c7f727cf60f7b5cee109e7ce6cbb82ce336b0ccb5060dac9834d3ec8217dafc686ed60c5abe9c1c543c9d6c2819d59c170abccc0661484be7e19d1be64231fbe0729e6bca4fd58bc049e66bab196bfba67e384b92dfaf8b8d46160b82a2caab6d2e41bb5a7ed8fb446f540b3025ef3afb93b8aaf693feeaf3dd497ad0a5550aba828c2aaade9f6aa8714faa460c19ca3364ca1a2058a5da1b2393f9daaabf79ccc50fb9c424af698dae7859817655895283d5e941e2ba89365286a93362a2b90665f508f6d78958e8622288bcf7c658b9494b88afb44cc88c86b3088b4f37387de12ef842b68c8 else 0xff960127fefc5f08fde85718fb4cd2e8fb1bc5dbf905d600f855e9e2f72c16e4f678e631f5cadc1df4bdd1fcf24b735cef17b0fbef11e549ed9bc3a5ecf91234ea1ef145e9d2420ee8442691e7b6a8e2e759154ce62f424ee57c119be3c0fd66e2cfc808e14e9ec6e0da3a1bdede5e92de1adc65dc9eef0fdc4d3570db8405e9db2bb46bda95c8e8da21a2b5d9a025f5d94b10a2)) else 0
  | 7 => if page < 1 then 0xf2fc17e3e88e58e8e87ae12bdc65205cdc4ebedfca4e1418bb167defba471675b9aeaea6b2130c43a0e52aa09e1f4ea79cf57ba99c424af69a8736c19814d82194e115c09365286a8d800da782169a357ee7b70a7d4d26bb752a5c7a6b0d2e9b662f794963d08eab626e621d58cbc3b84edd9eb34295b5c03ea44c4a3de0ca1d3af1a22339e7906d3536dd5a2571d7791bca8c1e18f3e8b00f03c24f017826f7 else 0
  | 8 => if page < 1 then 0xf4a70378 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x298026900da030002c0009e0000027501da0280011e00630118009802b301a10198012100040362028902bc021e else 0
  | 3 => if page < 4 then (if page < 2 then (if page < 1 then 0x1f852432015d08bc01b101be1f841a4011de128919b809bc22cc01bc1ade11db18b71cda19b91189215025da003319711adb0fde00de215102031ea0140821550eda20db1ea10049236404f000d81e7125c9153c22da2408035e2482034009761b5a19000f0415080a30015a10031f8003bd243000301080015c178602831d5e else 0x1876143d1c1818830f3c1b9e0c5e073c00580480000613000a0000c01a5b248018821c830f801e0018e000da20da108308bf06bc1d01005e0040118d150407da038819700130005b010603411275008000ce09d41902004b12000a8013f0202d0d001e70065b25cc0d5a0b5500c80c07055a18d50c5f18b008001dda0dda1c5a) else (if page < 3 then 0x17b42532009b18c804711a8618cb07db1c80060008c010000dde1f3c2382188c06bf0e8012db2406004818c9214d1175073d0e4001101a5e055e00db23801a4121da22cd159009bd17c3253c0580214c0400000000cb02401887173013801b030f0802c0230c035a159e0ada1186049816920f300b3d1ebe230023060100085a else 0x19c18cc11c80148073e1d0005db161819bc18cd0003159f005a09cb0054095e10da03bc24f002c10b8616e0224d1c0018da17401600170000020780043c0bf223600c8014f1202a1312065e18001512065a0e5823a41580105a21db0a81224c2404085b)) else 0
  | 4 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x11dd758c04907003355d796968a10f8627025980070054b00f87005a2883061322e3345a3b0603b0000c315d407000030a213480005c3d9c3c120df20e8027003e000a065788210053864c824506345c533c00880d0110100cc0563c438e680031dd0b006cbc3f9862305708503c50bd44b079804a806010670055e406920b09 else (if page < 2 then 0x20204f166c1e2d811dde60032f151a5a4ef310001bdb689e5a10330008604ff54b9b04703a004af0741046813d1236801cdb06106200181f2e8044c34d5d404635da4f137804468069000b4009180089200005c821dd2a81688c6fc2659343920348489f68061e1206691580450002485c802c0e685a3718061628010d847b2d else 0x5b92191542de50803b8320f0258371101b03008a0400650000841d02069356006fec0180513e2f6d31dc090062b35c7533862080379e245a3c60029540db66e30d9271496e6600812e004e003080140504da75820010513c3b001100701a5b5a700d0a80235d538069e042b0489258bd6d1e0092543002846ef0169e46de703c)) else (if page < 4 then 0x600265d255a6f01070c3eda48e0460c30075a83365a290657e62b1867905698265c371e275843841e131963365c09e04d8c350652003c83095b1f00105a10066d02325a4180591e00480500703230dc53da6fed1b0044600018035d6f82355c3e5a27c01480591000e010da6d063f1f660c078623dd325d028124840980315c else (if page < 5 then 0x4d80298044b65d1e7453754a1f824c0c0c004b83385a58806a55175f70006b76470d5b841dda5d800100530800952d80714c1340754b5830051203de2b923d8046820780670c49073d00009402804a8276486d0004dd679161002292701827c656833d60158168a04204440c0acc458100f006e003db34067649545a66f00764 else 0x38842f04104c738652821e836980468348f53400400208062ca93e98585a035a0fcf7452468459f01f01431d571268103cda2780035c47026fc352801a840b414000691209815dc13c081090070261e127823606419e235c54865a1606600b33569b4bb901da225d03d8478077802f6304c84a10268420845dc0533d60801106))) else (if page < 9 then (if page < 7 then 0x1cde53b07770280008006a80659678e06a5a68c8636c1cda4884710072825a806ab33d844668360054800f00738146da6b812c8046856d8c03800a865eb072f15fda2f980a1e558c06503180255b056013c054063780050c7492431e310019953b5c2c0c750848a22260245b029207125e013698485d61805e0025846880025a else (if page < 8 then 0xe0044c24b9014dc4cbc5be048802a06540034dc75326a401718570401c85f402a80028951c82f0726803f8669043e8005024098700248810ba111b0748454da17bc004c118604041b023700235f55002f715d1857e03f4c3980280203c80fc9748560da03004ba14900040132000d8009c862832e01061219e3358073801ddb else 0x4ef6095e07a040da02880782165e0a20399863de229372f008120080369e660e7680709e64dd431c01090911191770484e3c6d012e5d0a0002005d00328015004b866e02770024815b006d8006967581134118206c003a875ada01400ada46c0440e55185a8634da1d002a075bbc740d04806ff0408000b15a00533e7a80181e)) else (if page < 10 then 0x4dc348611da2b9415014510518c7860410046f00a903b80735a4b80108c78f000002f70265f11dc499071f63500395a038205da3a5a3b5a78613f1e1e163f80701b44b41206498d3a5c629b6e6002f0005d461611801f0224806789710d099219921c5b6fc6095f3e7258363f1069811300094d6e0022480ec02edd0601764e else (if page < 11 then 0x60494906338000e34280229537982dda734d00ec0b3d2adc46c84b030769201e4b98640108807b8010cc04cc038312c03a86010803da569e44664af11280431839003c80108007a134812d30040918c0618605694b0c585e0d8113c126811404121b63761e604c006902518e45806cb06360076017c11f8023da0664165a585b else 0x7580470c7a2172764c80734c28045e80098413804b026de402e3438c2ada7280)))) else 0
  | 5 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x15986300112117021ff042214b843b82272d64005703040037694c830a810e021a00598023810c5a43885a8136c86c1f6e9e1a90331357816b8456004904559e742c352a38007b8437e6619e64a00c5c1a9e58021c103b8051924b800b8c5a8e269e02605d016012703c1c832480325c058053806a193f3e0704138037847400 else (if page < 2 then 0x793031692f1b338008714a5a3e066a8028da73636062714c252a0ec02986588816007e0049c8125d79315e692b5c250817db4d985ded340772036681030976f178f16e801f8052800898358828dd56014120728302804c001c9b63907114566007011d0403a15f012c815e095e08228933166ce6356616031e00419006e91b80 else 0x78034014ada1502709019810a8802a141da62860a9851c80c10290054800e0104e02cda0d4c66925f0c6a1c2b002c80285d7286568041100d815f00483c3b004402240015004c802bda3f006a0c3e1e3f2006802cdc1992066966001b0407094681730030662f0073986c1e75122bdc7b800b82056023dd1181719b78215af3)) else (if page < 5 then (if page < 4 then 0x8005af60506652d071224a126986112188209880d5d741274805f8157dd070647803f18670423805d0407630a8009120f415f991b0100e60100096064066004361b3aa35e89299e3d005ba068125de342a10b92010919842d0300e90700308008a16b9907c8348140681aa1480035b078207d8166016288515a65711301475a else 0x318741f75605e8808706382272356833d8104806712741a0a0017de54882f0303887781393c1e80125c65983c002f9207dd75186e010980086374604b064b0876716312230116db7382325a159572801e824600258078f075002a0039c06a025706731508187d010a84493c649e051c1d8474021a043c9f68632c5d59016c02) else (if page < 6 then 0x4eda0be012c0285a2786018076f0052a698000926b9c575c31dc0200686007dc508932de678000812206285c6de9430138a21b0041dd0b207adb0aad08a0038631863d8419f0640725dd7ade460332db541073895d800a8906e04d5a1c03483d56124c68518c7780569058923c023880009869694fe10760125a3200040c0a0c else 0xec157022e9e670071501801568c0ae9272263835f801f001e70584804020a995d4b37982df10308656f0e0061a0310c02890ccc3e003360489f1120200444da54c1348460803499378043895960720646846769352c29065800648061004b005564520e67087468278754c006001406590071836b0c08153e8010800b210790))) else (if page < 10 then (if page < 8 then 0x412278168145d0e3f21672d46022a06742240692f84200157d1269935b2240126522086741870c8272c7a5a455a1e04468016023b02318028005a0c08807670484055727b202c5a03800ae05a845c001f0223004c865b763060575a34001e010a92568d6a0e5f842c5c4400086d6e81610111907a020d8068155ce361603aa1 else (if page < 9 then 0x37e0089e048c62b022000315278009896b122d0624dd42a0145d430027dd6a01370037aa5b7365a0410060601d011ec0050830da14826ea0338443bc008069824220420000e017005812598c40e0218030dc58847ca00d5c668c5792383c3ca07200148035860d000a025682489e742366803ee6368c6c0133813e18710d4d48 else 0x20801ec62e9829981081340634086c184c6631da739a770139bd74984e690c4c270c74862a864b093d047d8062044c6963601a98071575f12000230c50880a8644034e817b1e270e379c64192d5a2e646b802c000fc01a60721b7b9257844f863d0126063086260110000a9c33122b06578035002288349c6880528262010084)) else (if page < 12 then (if page < 11 then 0x16de191e21864f8816062df0051219802d0066823432478214002b860b0671122f061180268e7469738b01894084475d12c107da7d001d811c027980718665800b806c0054006d00648235683d9804821880265d0b0840811aa01c0009860133078c08e90aa13a3e5080770063013603070837126ce04c82325d251c708c3f81 else 0xc0075f00ae6360030082adc3c9e48a3260001061c890d5a5ee96f8034825300411e463068006c801b8449da0212050048806401659e475c389f41184b81641c1f0454867be06fad04920c5d2f5a6a045b9e0cda2a80245a348026073168749e21122f8858806b812f5c07822d88145c090027dc6380360673b545da1503729b) else (if page < 13 then 0x1a8032da580c0c8003a05acb48a1268c265c5c80714e490065691b816b82520c714934302b803704686213007a031001269f3d8040e15a001f01478341210b0040006fe92b5d02982d9248a00fc10460799e26534e180f406706503021043f805d8241dc1b9858602ada3ee02e72421e0d10298042064d807a00718057007ca1 else 0x192048a206926f697c5d3502158018047380630455984700580107cc60980300372d2d843f3c5c631200742d1481358766127c006b6073b311cc571b28800c902cdd568671107504731811da6c193a3c000049014f0c030b)))) else 0
  | 6 => if page < 4 then (if page < 2 then (if page < 1 then 0x100610e015801180091a17920c890584158e0280170806a10a860a88191e0d801360058113880b010a6813981588000014e91b8009000902055a141c17061300160c045d1ada0f060f9818a00800028116880c3c18000ab3099c060019801a01138103da181a1302020203dc069e128c0b001280070202000a80091b16000284 else 0x6040a6903000703172d0a2a0986098806010eed17951b03161e13990ab019200e020a2d14801a0015820c40078000920b9e17e00ddc091803010fa0161f0b8c0060018314060a000e0c0b041a04045a120c0d080ef01b0212001602045c07000ddd0ee30ab20b9f0304138417e319210c3d176804dd17000286138010921282) else (if page < 3 then 0x16211c000ba2158c0e0003dd1b8316200d8210801b000c0105800ba10c00130c16230dda018211921adc0ba014011818168606a001800b800d8c1000198102880ba314181b8201120a0809810a9813861add0203139c099815860f9e18021109176608800a89176900e00b8204dc172a12020a82055d17940a0613680a660903 else 0x12100819840a9a181b16801404141918030f08172c1c0414000f0011e017e20a9b18a108181622098409990a830a2c14080c040d061366098001601c0104da0100189e1500055c0d00)) else 0
  | 7 => if page < 1 then 0x32003d00e800060008009c003c010600330132013300840099010900ac0140008000e000a2013d00a1013c00a000a300920081013000980100010800e60000000900e900aa00ad009e00300040009f else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def search (k h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if field keys k 32 m ≤ h then search k h fuel m hi else search k h fuel lo m
    else lo

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let ix := search k (key xs) 14 0 (entries k)
  let slot := field targets k 16 ix
  (slot / 128,slot % 128)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s14 : Switch := ⟨14,0xcccc0000cccc,0x3333000033330000⟩
theorem s14_ok : s14.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s23]
  | 3 => [s23, s24]
  | 4 => [s24, s23]
  | 5 => [s24]
  | 6 => [s12]
  | 7 => [s12, s34]
  | 8 => [s12, s13]
  | 9 => [s12, s13, s14]
  | 10 => [s12, s14, s13]
  | 11 => [s12, s14]
  | 12 => [s13, s12]
  | 13 => [s13, s12, s24]
  | 14 => [s13]
  | 15 => [s13, s14]
  | 16 => [s13, s24]
  | 17 => [s13, s24, s12]
  | 18 => [s14, s12, s23]
  | 19 => [s14, s12]
  | 20 => [s14, s13]
  | 21 => [s14]
  | 22 => [s14, s23, s12]
  | 23 => [s14, s23]
  | 24 => [s01]
  | 25 => [s01, s34]
  | 26 => [s01, s23]
  | 27 => [s01, s23, s24]
  | 28 => [s01, s24, s23]
  | 29 => [s01, s24]
  | 30 => [s01, s02]
  | 31 => [s01, s02, s34]
  | 32 => [s01, s02, s03]
  | 33 => [s01, s02, s03, s04]
  | 34 => [s01, s02, s04, s03]
  | 35 => [s01, s02, s04]
  | 36 => [s01, s03, s02]
  | 37 => [s01, s03, s02, s24]
  | 38 => [s01, s03]
  | 39 => [s01, s03, s04]
  | 40 => [s01, s03, s24]
  | 41 => [s01, s03, s24, s02]
  | 42 => [s01, s04, s02, s23]
  | 43 => [s01, s04, s02]
  | 44 => [s01, s04, s03]
  | 45 => [s01, s04]
  | 46 => [s01, s04, s23, s02]
  | 47 => [s01, s04, s23]
  | 48 => [s02, s01]
  | 49 => [s02, s01, s34]
  | 50 => [s02, s01, s13]
  | 51 => [s02, s01, s13, s14]
  | 52 => [s02, s01, s14, s13]
  | 53 => [s02, s01, s14]
  | 54 => [s02]
  | 55 => [s02, s34]
  | 56 => [s02, s03]
  | 57 => [s02, s03, s04]
  | 58 => [s02, s04, s03]
  | 59 => [s02, s04]
  | 60 => [s02, s13]
  | 61 => [s02, s13, s14]
  | 62 => [s02, s13, s01]
  | 63 => [s02, s13, s01, s04]
  | 64 => [s02, s13, s04, s01]
  | 65 => [s02, s13, s04]
  | 66 => [s02, s14, s13]
  | 67 => [s02, s14]
  | 68 => [s02, s14, s01, s03]
  | 69 => [s02, s14, s01]
  | 70 => [s02, s14, s03]
  | 71 => [s02, s14, s03, s01]
  | 72 => [s03, s01, s12]
  | 73 => [s03, s01, s12, s24]
  | 74 => [s03, s01]
  | 75 => [s03, s01, s14]
  | 76 => [s03, s01, s24]
  | 77 => [s03, s01, s24, s12]
  | 78 => [s03, s02]
  | 79 => [s03, s02, s24]
  | 80 => [s03]
  | 81 => [s03, s04]
  | 82 => [s03, s24]
  | 83 => [s03, s24, s02]
  | 84 => [s03, s12, s01]
  | 85 => [s03, s12, s01, s14]
  | 86 => [s03, s12]
  | 87 => [s03, s12, s04]
  | 88 => [s03, s12, s14]
  | 89 => [s03, s12, s14, s01]
  | 90 => [s03, s14, s02, s12]
  | 91 => [s03, s14, s02]
  | 92 => [s03, s14, s12]
  | 93 => [s03, s14, s12, s02]
  | 94 => [s03, s14]
  | 95 => [s03, s14, s01]
  | 96 => [s04, s01, s12, s23]
  | 97 => [s04, s01, s12]
  | 98 => [s04, s01, s13]
  | 99 => [s04, s01]
  | 100 => [s04, s01, s23, s12]
  | 101 => [s04, s01, s23]
  | 102 => [s04, s02, s23]
  | 103 => [s04, s02]
  | 104 => [s04, s03]
  | 105 => [s04]
  | 106 => [s04, s23, s02]
  | 107 => [s04, s23]
  | 108 => [s04, s12, s01, s13]
  | 109 => [s04, s12, s01]
  | 110 => [s04, s12, s03]
  | 111 => [s04, s12]
  | 112 => [s04, s12, s13, s01]
  | 113 => [s04, s12, s13]
  | 114 => [s04, s13, s02]
  | 115 => [s04, s13, s02, s12]
  | 116 => [s04, s13, s12, s02]
  | 117 => [s04, s13, s12]
  | 118 => [s04, s13, s01]
  | 119 => [s04, s13]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s23_ok, s24_ok, s12_ok, s13_ok, s14_ok, s01_ok, s02_ok, s03_ok, s04_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 7 0 = true :=
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
theorem chunk3x48 : span (checked 3) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x64 : span (checked 3) 12 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 76 0 = true :=
  (@span_join (checked 3) 32 0 44 (@span_join (checked 3) 16 0 16 chunk3x0 chunk3x16) (@span_join (checked 3) 16 32 28 chunk3x32 (@span_join (checked 3) 16 48 12 chunk3x48 chunk3x64)))

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
theorem chunk4x240 : span (checked 4) 8 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 248 0 = true :=
  (@span_join (checked 4) 128 0 120 (@span_join (checked 4) 64 0 64 (@span_join (checked 4) 32 0 32 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 16 chunk4x32 chunk4x48)) (@span_join (checked 4) 32 64 32 (@span_join (checked 4) 16 64 16 chunk4x64 chunk4x80) (@span_join (checked 4) 16 96 16 chunk4x96 chunk4x112))) (@span_join (checked 4) 64 128 56 (@span_join (checked 4) 32 128 32 (@span_join (checked 4) 16 128 16 chunk4x128 chunk4x144) (@span_join (checked 4) 16 160 16 chunk4x160 chunk4x176)) (@span_join (checked 4) 32 192 24 (@span_join (checked 4) 16 192 16 chunk4x192 chunk4x208) (@span_join (checked 4) 16 224 8 chunk4x224 chunk4x240))))

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
theorem chunk5x240 : span (checked 5) 13 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 253 0 = true :=
  (@span_join (checked 5) 128 0 125 (@span_join (checked 5) 64 0 64 (@span_join (checked 5) 32 0 32 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 16 chunk5x32 chunk5x48)) (@span_join (checked 5) 32 64 32 (@span_join (checked 5) 16 64 16 chunk5x64 chunk5x80) (@span_join (checked 5) 16 96 16 chunk5x96 chunk5x112))) (@span_join (checked 5) 64 128 61 (@span_join (checked 5) 32 128 32 (@span_join (checked 5) 16 128 16 chunk5x128 chunk5x144) (@span_join (checked 5) 16 160 16 chunk5x160 chunk5x176)) (@span_join (checked 5) 32 192 29 (@span_join (checked 5) 16 192 16 chunk5x192 chunk5x208) (@span_join (checked 5) 16 224 13 chunk5x224 chunk5x240))))

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
theorem chunk6x48 : span (checked 6) 9 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 57 0 = true :=
  (@span_join (checked 6) 32 0 25 (@span_join (checked 6) 16 0 16 chunk6x0 chunk6x16) (@span_join (checked 6) 16 32 9 chunk6x32 chunk6x48))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 3 0 = true :=
  chunk7x0

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
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.CliqueFive


namespace SignedFrontier.CliqueLink
def target := SmallCert.CliqueFive.target
def raw := SmallCert.CliqueFive.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 9 ≤ p.length := by
  have inside : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial target 0 {target} Cone.done inside
  have start : available initial = insert 0 SmallCert.CliqueFive.raw.toFinset := by decide +kernel
  rw [start] at access
  have bounded := SmallCert.CliqueFive.lower run access
  omega
end SignedFrontier.CliqueLink

namespace TableLink
open SignedFrontier

def assignment (r : Fin 64) (v : Fin 5) : Bool := r.val.testBit v.val

theorem rawTable : ∀ r : Fin 64, CliqueLink.initial.map (fun u => u.getLsbD r.val) =
    ThresholdReplacement.signedStart (assignment r) := by decide +kernel

theorem goalTable : ∀ r : Fin 64, (~~~CliqueLink.target).getLsbD r.val =
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
  have eq : evaluate p CliqueLink.initial o = ~~~CliqueLink.target := by
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

end PEqualNP.Outside.L_meta_12216_aux

open PEqualNP.Outside.L_meta_12216_aux

theorem PEqualNP.Outside.L_meta_12216 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900762240 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900762240 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
