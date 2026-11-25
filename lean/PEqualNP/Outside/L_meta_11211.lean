import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11211_aux

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

namespace SevenVertexOneNot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def edges : List ℕ := [0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6]
def posted (x : Fin 7 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

theorem table : ∀ x, posted x = target x := by decide +kernel

def witness : Circuit := ⟨[
  ⟨.or, [5,3]⟩,
  ⟨.or, [6,0]⟩,
  ⟨.or, [6,5]⟩,
  ⟨.or, [9,4]⟩,
  ⟨.and, [5,2]⟩,
  ⟨.and, [8,7]⟩,
  ⟨.and, [9,0]⟩,
  ⟨.and, [10,1]⟩,
  ⟨.or, [11,12]⟩,
  ⟨.or, [15,13]⟩,
  ⟨.or, [16,14]⟩], 17⟩

theorem size : witness.size = 11 := by decide +kernel

theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel

theorem rawValue : ∀ x, circuitFun 7 witness x = target x := by decide +kernel

theorem value (x : Fin 7 → Bool) : circuitFun 7 witness x = posted x :=
  (rawValue x).trans (table x).symm

abbrev Input := Fin 6 → Bool
def perm : Fin 7 → Fin 7 := ![3, 1, 0, 5, 6, 4, 2]
def lift (x : Input) (j : Fin 7) : Bool := Fin.cases false x (perm j)
def sliceTarget (x : Input) := target (lift x)
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- Pinning the selected input saves a binary gate.
theorem pinSlice (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = sliceTarget x := by
  let raw := List.ofFn (fun j : Fin 6 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let proto := fun j : Fin 7 => (fun x : Input => (Fin.cases false x j : Bool), decide (j = 4), decide (j = 0 ∨ j = 4))
  let pin := fun j : Fin 7 => proto (perm j)
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    change (proto (perm j)).1 ∈ pool ∧ (fun x => !((proto (perm j)).1 x)) ∈ pool ∧
      ((∃ b, ∀ x, (proto (perm j)).1 x = b) ∨ (proto (perm j)).2.1 = (proto (perm j)).2.2)
    generalize perm j = idx
    refine Fin.cases ?_ (fun i => ?_) idx
    · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    · have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      refine ⟨List.mem_append_left _ (List.mem_append_right _ pos),
        List.mem_append_right _ (List.mem_map_of_mem pos), Or.inr ?_⟩
      simp [proto]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = sliceTarget x := by
    simpa [v, pin, proto, lift, sliceTarget, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : sliceTarget (fun _ => false) ≠ sliceTarget (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (perm j = 4))
    have b := hit (fun j => decide (perm j = 0 ∨ perm j = 4))
    simp only [v,pin,proto,List.map_ofFn,Function.comp_def,circuitFun] at a b ⊢
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
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 7 D x = posted x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, fun x => (hit x).trans (table x).symm⟩
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

end SevenVertexOneNot

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

def essentialRows (g : W) (raw : List W) (xs : List (W × Fin 64 × Fin 64)) :=
  xs.all (fun t => decide (g.getLsbD t.2.1.val ≠ g.getLsbD t.2.2.val) &&
    raw.all (fun v => v == t.1 || (v.getLsbD t.2.1.val == v.getLsbD t.2.2.val)))

theorem essentialOfRows (g : W) (raw : List W) (xs : List (W × Fin 64 × Fin 64))
    (covers : xs.map Prod.fst = raw) (test : essentialRows g raw xs = true) : Essential g raw := by
  intro w hw
  rw [← covers] at hw
  obtain ⟨⟨v,i,j⟩, hv, rfl⟩ := List.mem_map.mp hw
  have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp test (v,i,j) hv)
  refine ⟨i,j,of_decide_eq_true both.1,?_⟩
  intro u hu ne
  have h := List.all_eq_true.mp both.2 u hu
  simpa [ne] using h

end SignedFrontier

namespace SignedFrontier.Packed

-- These packed integers only propose a negative input row. Every proposed
-- obstruction is tested on the original signals before a successor is skipped.
structure Columns where
  w : W
  pos : Nat
  neg : Nat

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 15) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 15) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 960 := by omega
  have val : fullLanes = 2^960-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 15) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 15) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 15) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 15) (xs : List Columns)
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
    (length : rows.length = 15) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 15) (bounds : ∀ r ∈ rows, r < 64)
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

namespace SignedFrontier

def rowMap (f : Fin 64 → Fin 64) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 64 => w.getLsbD (f r).val))).cast (by simp)

theorem rowMap_read (f : Fin 64 → Fin 64) (w : W) (r : Fin 64) :
    (rowMap f w).getLsbD r.val = w.getLsbD (f r).val := by
  simp only [rowMap, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem rowMap_form (f : Fin 64 → Fin 64) (a b w : W) (h : w ∈ choices a b) :
    rowMap f w ∈ choices (rowMap f a) (rowMap f b) := by
  have ab (u v : W) : rowMap f (u &&& v) = rowMap f u &&& rowMap f v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have rwAt := fun z => rowMap_read f z ⟨i,hi⟩
    simp only [rwAt,BitVec.getLsbD_and]
  have ob (u v : W) : rowMap f (u ||| v) = rowMap f u ||| rowMap f v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have rwAt := fun z => rowMap_read f z ⟨i,hi⟩
    simp only [rwAt,BitVec.getLsbD_or]
  have nb (u : W) : rowMap f (~~~u) = ~~~(rowMap f u) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have rwAt := fun z => rowMap_read f z ⟨i,hi⟩
    simp only [rwAt,BitVec.getLsbD_not,hi,(f ⟨i,hi⟩).isLt,decide_true,Bool.true_and]
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp [ab,ob,nb]

-- Equality in the projected gate budget preserves every live image. A live
-- input becoming constant therefore forces at least one further saved gate.
theorem Cone.project {g : W} {k : Nat} {s : Finset W} (h : Cone g k s)
    (f : W → W) (hom : ∀ a b w, w ∈ choices a b → f w ∈ choices (f a) (f b))
    (nz : f g ≠ 0) : ∃ j t, j ≤ k ∧ Cone (f g) j t ∧ t ⊆ s.image f ∧
      (j = k → s.image f ⊆ t) := by
  induction h with
  | done => exact ⟨0,{f g},le_rfl,Cone.done,by simp,by simp⟩
  | @step k needed a b w rest want a0 b0 ab aw bw form ih =>
    obtain ⟨j,t,le,run,ht,full⟩ := ih
    let old := insert a (insert b (needed.erase w))
    have aa : f a ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have bb : f b ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have former (x : W) (hx : x ∈ needed) (ne : x ≠ w) : f x ∈ old.image f :=
      Finset.mem_image_of_mem _ (by simp [old,hx,ne])
    change ∃ j t, j ≤ k+1 ∧ Cone (f g) j t ∧ t ⊆ old.image f ∧ (j = k+1 → old.image f ⊆ t)
    by_cases sub : t ⊆ old.image f
    · exact ⟨j,t,by omega,run,sub,by omega⟩
    · have special (x : W) (hx : x ∈ t) : x = f w ∨ x ∈ old.image f := by
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (ht hx)
        by_cases eq : z = w
        · exact Or.inl (congrArg f eq)
        · exact Or.inr (former z hz eq)
      have used : f w ∈ t := by
        by_contra bad
        exact sub (fun x hx => (special x hx).resolve_left (fun e => bad (e ▸ hx)))
      have fresh : f w ∉ old.image f := fun inside =>
        sub (fun x hx => (special x hx).elim (fun e => e ▸ inside) id)
      have nzW : f w ≠ 0 := fun e => run.noZero nz (e ▸ used)
      have op := hom a b w form
      have good : ¬(f a = 0 ∨ f b = 0 ∨ f a = f b) := by
        intro bad
        rcases constants (f a) (f b) bad _ op with e | e | e
        · exact nzW e
        · exact fresh (e ▸ aa)
        · exact fresh (e ▸ bb)
      let next := insert (f a) (insert (f b) (t.erase (f w)))
      have step : Cone (f g) (j+1) next := Cone.step run used (fun e => good (Or.inl e))
        (fun e => good (Or.inr (Or.inl e))) (fun e => good (Or.inr (Or.inr e)))
        (fun e => fresh (e ▸ aa)) (fun e => fresh (e ▸ bb)) op
      refine ⟨j+1,next,by omega,step,?_,?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact aa
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact bb
        have z := Finset.mem_erase.mp hx
        exact (special x z.2).resolve_left z.1
      · intro eq x hx
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [next]
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [next]
        have cond := Finset.mem_erase.mp hz
        have oldMem := former z cond.2 cond.1
        have dif : f z ≠ f w := fun e => fresh (e ▸ oldMem)
        have live := full (by omega) (Finset.mem_image_of_mem f cond.2)
        simp [next,dif,live]

end SignedFrontier

namespace SignedFrontier

-- Project signed truth tables along any map of rows. Canonicalization allows
-- complemented inputs and high pins as well as low pins.
def signedMap (f : Fin 64 → Fin 64) (w : W) := canonical (rowMap f w)

theorem canonical_choice (a b w : W) (h : w ∈ choices a b) :
    canonical w ∈ choices (canonical a) (canonical b) := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact operation a b
  · simpa only [canonical_not] using operation a (~~~b)
  · simpa only [canonical_not] using operation (~~~a) b
  · simpa only [BitVec.not_and,BitVec.not_not,← BitVec.not_or,canonical_not] using
      operation (~~~a) (~~~b)

theorem signedMap_choice (f : Fin 64 → Fin 64) (a b w : W) (h : w ∈ choices a b) :
    signedMap f w ∈ choices (signedMap f a) (signedMap f b) :=
  canonical_choice _ _ _ (rowMap_form f a b w h)

def signedLower (g : W) (raw : List W) (n : Nat) : Prop :=
  ∀ {k : Nat} {s : Finset W}, Cone g k s → s ⊆ insert 0 raw.toFinset → n ≤ k

-- Test a live suffix after some early gates have been fixed. Its starting
-- signals must all become raw inputs or constants on the chosen restriction.
-- If a live signal becomes zero, the suffix loses one further operation.
def cofactorReject (f : Fin 64 → Fin 64) (raw : List W) (n budget : Nat) (s : List W) : Bool :=
  let ws := s.map (signedMap f)
  ws.all (fun w => w == 0 || raw.contains w) &&
    (decide (budget < n) || (decide (budget ≤ n) && ws.contains 0))

theorem cofactorReject_sound (f : Fin 64 → Fin 64) (g : W) (raw : List W) (n budget : Nat)
    (nz : signedMap f g ≠ 0) (low : signedLower (signedMap f g) raw n)
    (s : List W) {k : Nat} (le : k ≤ budget) (run : Cone g k s.toFinset) :
    cofactorReject f raw n budget s = false := by
  by_contra! bad
  have both := Bool.and_eq_true_iff.mp (show cofactorReject f raw n budget s = true by simpa using bad)
  have stock : (s.map (signedMap f)).toFinset = s.toFinset.image (signedMap f) := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
  have sub : s.toFinset.image (signedMap f) ⊆ insert 0 raw.toFinset := by
    intro w hw
    rw [←stock] at hw
    have h := List.all_eq_true.mp both.1 w (List.mem_toFinset.mp hw)
    simpa [List.contains_eq_mem] using h
  obtain ⟨j,t,small,p,inside,full⟩ := run.project (signedMap f) (signedMap_choice f) nz
  have lower := low p (inside.trans sub)
  rcases Bool.or_eq_true_iff.mp both.2 with short | keep
  · have := of_decide_eq_true short
    omega
  · obtain ⟨h,z⟩ := Bool.and_eq_true_iff.mp keep
    have lim := of_decide_eq_true h
    have zero : 0 ∈ s.toFinset.image (signedMap f) := by rw [←stock]; simpa using z
    exact p.noZero nz (full (by omega) zero)

end SignedFrontier

namespace SignedFrontier

-- Masked rows suffice because every projected row lies on this slice.
theorem signedMap_eq_of_mask (f : Fin 64 → Fin 64) (mask a b : W)
    (covers : ∀ i, mask.getLsbD (f i).val = true)
    (eq : a &&& mask = b &&& mask) : signedMap f a = signedMap f b := by
  apply congrArg canonical
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 64 := ⟨i, hi⟩
  change (rowMap f a).getLsbD r.val = (rowMap f b).getLsbD r.val
  rw [rowMap_read, rowMap_read]
  simpa only [BitVec.getLsbD_and, covers, Bool.and_true] using
    congrArg (fun w : W => w.getLsbD (f r).val) eq

theorem signedMap_zero (f : Fin 64 → Fin 64) : signedMap f 0 = 0 := by
  have h : rowMap f 0 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (rowMap_read f 0 ⟨i,hi⟩).trans (by simp)
  rw [signedMap, h]
  rfl

theorem signedMap_ones (f : Fin 64 → Fin 64) : signedMap f (~~~0) = 0 := by
  have h : rowMap f (~~~0) = ~~~(0 : W) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (rowMap f (~~~0)).getLsbD i = (~~~(0 : W)).getLsbD (f ⟨i,hi⟩).val from
      rowMap_read f _ ⟨i,hi⟩]
    have zero (j : Nat) : (0 : W).getLsbD j = false := by simp
    simp only [BitVec.getLsbD_not, hi, (f ⟨i,hi⟩).isLt, decide_true, zero]
  rw [signedMap, h, canonical_not]
  rfl

def maskedCut (mask : W) (patterns : List W) (bound budget : Nat) (s : List W) : Bool :=
  s.all (fun w => patterns.contains (w &&& mask)) &&
    (decide (budget < bound) || (decide (budget ≤ bound) &&
      s.any (fun w => (w &&& mask) == 0 || (w &&& mask) == mask)))

theorem maskedCut_sound (f : Fin 64 → Fin 64) (mask : W) (patterns base raw : List W)
    (g : W) (bound budget : Nat) (s : List W)
    (covers : ∀ i, mask.getLsbD (f i).val = true)
    (pats : patterns = base.map (· &&& mask))
    (stock : ∀ w ∈ base, signedMap f w = 0 ∨ signedMap f w ∈ raw)
    (nz : signedMap f g ≠ 0) (low : signedLower (signedMap f g) raw bound)
    {k : Nat} (le : k ≤ budget) (run : Cone g k s.toFinset) :
    maskedCut mask patterns bound budget s = false := by
  by_contra! bad
  have both := Bool.and_eq_true_iff.mp (show maskedCut mask patterns bound budget s = true by simpa using bad)
  have yes : cofactorReject f raw bound budget s = true := by
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro y hy
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
      have h := List.all_eq_true.mp both.1 w hw
      have mem : w &&& mask ∈ base.map (· &&& mask) := by simpa [pats] using h
      obtain ⟨v, hv, eq⟩ := List.mem_map.mp mem
      rw [← signedMap_eq_of_mask f mask v w covers eq]
      simpa [List.contains_eq_mem] using stock v hv
    · rcases Bool.or_eq_true_iff.mp both.2 with small | tight
      · exact Bool.or_eq_true_iff.mpr (Or.inl small)
      obtain ⟨h, hz⟩ := Bool.and_eq_true_iff.mp tight
      obtain ⟨w, hw, value⟩ := List.any_eq_true.mp hz
      have z : signedMap f w = 0 := by
        rcases Bool.or_eq_true_iff.mp value with lo | hi
        · have eq : w &&& mask = (0 : W) &&& mask := by simpa using lo
          exact (signedMap_eq_of_mask f mask w 0 covers eq).trans (signedMap_zero f)
        · have eq : w &&& mask = (~~~(0 : W)) &&& mask := by
            change w &&& mask = BitVec.allOnes 64 &&& mask
            rw [BitVec.allOnes_and]
            simpa using hi
          exact (signedMap_eq_of_mask f mask w _ covers eq).trans (signedMap_ones f)
      apply Bool.or_eq_true_iff.mpr
      refine Or.inr (Bool.and_eq_true_iff.mpr ⟨h, ?_⟩)
      simpa [List.contains_eq_mem] using (List.mem_map.mpr ⟨w,hw,z⟩ : (0 : W) ∈ s.map (signedMap f))
  rw [cofactorReject_sound f g raw bound budget nz low s le run] at yes
  contradiction


-- Keep the executable mask and its correctness argument together. A lookup may
-- choose any certificate in this family; each choice has an independent proof.
structure CutCertificate (g : W) where
  mask : W
  patterns : List W
  bound : Nat
  sound : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset →
    maskedCut mask patterns bound budget s = false

def makeCutCertificate (g goal mask : W) (rows : Nat) (dimension bound : Nat)
    (base patterns raw : List W) (nz : goal ≠ 0) (low : signedLower goal raw bound)
    (f : Fin 64 → Fin 64 := fun r => ⟨(rows >>> (6 * (r.val % 2^dimension))) % 64,
      Nat.mod_lt _ (by decide)⟩)
    (covers : ∀ r, mask.getLsbD (f r).val = true)
    (pats : patterns = base.map (· &&& mask))
    (stock : base.all (fun w => signedMap f w == 0 || raw.contains (signedMap f w)) = true)
    (goalEq : signedMap f g = goal) : CutCertificate g where
  mask := mask
  patterns := patterns
  bound := bound
  sound budget s _ le run := by
    apply maskedCut_sound f mask patterns base raw g bound budget s covers pats _ _ _ le run
    · intro w h
      simpa [List.contains_eq_mem] using List.all_eq_true.mp stock w h
    · simpa only [goalEq] using nz
    · rw [goalEq]
      exact @low

-- A certified lower bound can discharge a frontier state without enumerating its successors.
theorem closed_excludes_or (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 64 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, closed g negative words count lookup sym k i = true ∨
      (∀ d ≤ k, ¬ Cone g d (words k i).toFinset)) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    rcases checks 0 hk i hi with check | reject
    case inr => exact reject d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simp [closed,mem] at check
  | succ k ih =>
    intro hk i hi d hd run
    rcases checks (k+1) hk i hi with check | reject
    case inr => exact reject d hd run
    obtain ⟨absent,reject⟩ := Bool.and_eq_true_iff.mp check
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


namespace SignedFrontier.SmallCert.Minor0

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0]
def target : W := 0xe8e8e8e8e8e8e8e8
def negative : List Nat := [0, 1, 2, 4]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,2,3),(0xcccccccccccccccc,1,3),(0xf0f0f0f0f0f0f0f0,1,5)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xf0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x7 else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x7 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 4
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 2)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 3)

def bucketCount : ℕ → ℕ
  | 3 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
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


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 3 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 1 0 = true :=
  chunk3x0
theorem verified : ∀ k ≤ 3, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 4 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 3
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    3 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor0

namespace SignedFrontier.SmallCert.Minor1

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x8ace8ace8ace8ace
def negative : List Nat := [0, 4, 5, 8, 10, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,1,5),(0xff00ff00ff00ff00,2,10)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xff00ff00ff00ff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 8
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 3)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 3 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s01, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok, s23_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 3 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 1 0 = true :=
  chunk3x0
theorem verified : ∀ k ≤ 3, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 4 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 3
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    3 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor1

namespace SignedFrontier.SmallCert.Minor2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x8eee8eee8eee8eee
def negative : List Nat := [0, 4, 8, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,9,13),(0xff00ff00ff00ff00,5,13)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xff00ff00ff00ff00f0f0f0f0f0f0f0f0f000f000f000f000ccccccccccccccccaaaaaaaaaaaaaaaa00f000f000f000f00000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x43 else 0
  | 3 => if page < 1 then 0x11cbc3 else 0
  | 4 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xf else 0
  | 3 => if page < 1 then 0xf else 0
  | 4 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 8
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 3)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 2
  | 3 => 6
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 4
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x20 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x4985 else 0
  | 4 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 4,slot % 4)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s01]
  | 3 => [s01, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 1 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 3 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor2

namespace SignedFrontier.SmallCert.Minor3

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfeeafeeafeeafeea
def negative : List Nat := [0, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,4,6),(0xf0f0f0f0f0f0f0f0,2,6),(0xff00ff00ff00ff00,2,10)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffaaffaaffaaffaaff00ff00ff00ff00fafafafafafafafaf0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa44444444444444440000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1eb else 0
  | 3 => if page < 1 then 0x3b9d else 0
  | 4 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x12 else 0
  | 3 => if page < 1 then 0xf else 0
  | 4 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 8
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 3)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 3
  | 3 => 8
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x8 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x20 else 0
  | 3 => if page < 1 then 0x903c0082 else 0
  | 4 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 8,slot % 8)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s12]
  | 3 => [s12, s13]
  | 4 => [s13, s12]
  | 5 => [s13]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s12_ok, s13_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 1 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 2 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor3

namespace SignedFrontier.SmallCert.Minor4

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x88fe88fe88fe88fe
def negative : List Nat := [0, 8, 9, 10, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xfff0fff0fff0fff0ff00ff00ff00ff00fafafafafafafafaf0f0f0f0f0f0f0f0dcdcdcdcdcdcdcdcccfcccfcccfcccfcccccccccccccccccaaaaaaaaaaaaaaaa303030303030303000f000f000f000f00000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x34d9 else 0
  | 3 => if page < 1 then 0xab8b2b1b else 0
  | 4 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xf else 0
  | 3 => if page < 1 then 0x11 else 0
  | 4 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 16
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 4)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 7
  | 3 => 11
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 3
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x1 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x310 else 0
  | 3 => if page < 1 then 0x4740580 else 0
  | 4 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s01]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 4 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 4 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor4

namespace SignedFrontier.SmallCert.Minor5

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x8aceeeee8aceeeee
def negative : List Nat := [0, 4, 8, 12, 16, 20, 21, 24, 26, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,17,21),(0xff00ff00ff00ff00,18,26),(0xffff0000ffff0000,5,21)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffff0000ffff0000ffaaffaaffaaffaaffaa0000ffaa0000ff330000ff330000ff00ff00ff00ff00ff000000ff000000f0f0f0f0f0f0f0f0f0f00000f0f00000cececececececececcccccccccccccccaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0303030303030303000ff000000ff000000cc00cc00cc00cc0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xa8183e434e187 else 0
  | 4 => if page < 1 then 0x3af1b4d9ecae37 else 0
  | 5 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1b else 0
  | 4 => if page < 1 then 0x13 else 0
  | 5 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 4
  | 4 => 6
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 16
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 4)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 3 => 2
  | 4 => 4
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 5
  | 4 => 17
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 3
  | 4 => 4
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x2 else 0
  | 4 => if page < 1 then 0xc5 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x5c80 else 0
  | 4 => if page < 1 then 0xab650034090280071 else 0
  | 5 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s01, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok, s23_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 4 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 4 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 6 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1 0 = true :=
  chunk5x0
theorem verified : ∀ k ≤ 5, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 6 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 5
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    5 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor5

namespace SignedFrontier.SmallCert.Minor6

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x8aeeeeee8aeeeeee
def negative : List Nat := [0, 4, 8, 12, 16, 20, 24, 26, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,25,29),(0xff00ff00ff00ff00,18,26),(0xffff0000ffff0000,10,26)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffff0000ffff0000ff00ff00ff00ff00ff000000ff000000fcfcfcfcfcfcfcfcfc00fc00fc00fc00fc000000fc000000f500f500f500f500f5000000f5000000f0f0f0f0f0f0f0f0f000f000f000f000f0000000f0000000cfcccccccfcccccccececececececececcccccccccccccccaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a030303030303030300f000f000f000f000f0000000f0000000a0a0a0a0a0a0a0a0000ff000000ff000000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x9a8f349e083b907 else 0
  | 3 => if page < 1 then 0x9c87360e6b1ccc39947320e631cc43027208cc0f98267 else 0
  | 4 => if page < 1 then 0x25b9bd9b36cbb26c5b0be67 else 0
  | 5 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1e else 0
  | 3 => if page < 1 then 0x1f else 0
  | 4 => if page < 1 then 0x15 else 0
  | 5 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 4
  | 3 => 12
  | 4 => 9
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 32
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 5)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 2
  | 3 => 5
  | 4 => 5
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 5
  | 3 => 17
  | 4 => 17
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 3
  | 3 => 5
  | 4 => 5
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x8 else 0
  | 3 => if page < 1 then 0xa02c0 else 0
  | 4 => if page < 1 then 0x1048000 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x40b0 else 0
  | 3 => if page < 1 then 0x520c00b524264148700c0 else 0
  | 4 => if page < 1 then 0x4001027b0e003a001994d else 0
  | 5 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 4 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 4 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 12 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 12 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 9 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 9 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1 0 = true :=
  chunk5x0
theorem verified : ∀ k ≤ 5, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 6 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 5
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    5 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor6

namespace SignedFrontier.SmallCert.Minor7

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xa8fefffea8fefffe
def negative : List Nat := [0, 16, 24, 25, 26, 28, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,8,24)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xf0f0fcfcf0f0fcfcf0f0fafaf0f0fafaf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeecfcecfcecfcecfccccccccccccccccccccc4444cccc4444cccc0c0ccccc0c0ccccc00cccccc00cccccc0000cccc0000cc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00cc00cc00cc00c0c0c0c0c0c0c0c0abaaabaaabaaabaaaafeaafeaafeaafeaaeeaaeeaaeeaaeeaaaaffaaaaaaffaaaaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaa0202aaaa0202aaaa00aaaaaa00aaaaaa0000aaaa0000aa0aaa0aaa0aaa0aaa02aa02aa02aa02aa00aa00aa00aa00a8fca8fca8fca8fca8aaa8aaa8aaa8aaa8a8a8a8a8a8a8a88c8c8c8c8c8c8c8c88cc88cc88cc88cc88888888888888885f5f00005f5f00005f005f005f005f00575700005757000057005700570057005555000055550000550055005500550054545454545454544c4c4c4c4c4c4c4c44444444444444440f0f00000f0f00000f000f000f000f000ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a03030000030300000300030003000300020202020202020200ff000000ff000000fc00fc00fc00fc00cc00cc00cc00cc00aa00aa00aa00aa0000fffc0000fffc0000ffcc0000ffcc0000ffaa0000ffaa0000ff000000ff000000fcfc0000fcfc0000cccc0000cccc0000aaaa0000aaaa0000000000000000 else 0xffffff00ffffff00fffffcfcfffffcfcffffccccffffccccffffaaaaffffaaaaffffa8a8ffffa8a8ffff8888ffff8888ffff00fcffff00fcffff00ccffff00ccffff00aaffff00aaffff0000ffff0000fffcfffcfffcfffcfffc0000fffc0000ffccffccffccffccffcc0000ffcc0000ffaaffaaffaaffaaffaa0000ffaa0000ffa8ffa8ffa8ffa8ff88ff88ff88ff88ff550000ff550000ff0f0000ff0f0000ff030000ff030000ff00fffcff00fffcff00ffccff00ffccff00ffaaff00ffaaff00ff00ff00ff00ff005500ff005500ff000f00ff000f00ff000300ff000300ff000000ff000000fefefefefefefefefdfcfdfcfdfcfdfcfcfefcfefcfefcfefcfcfffcfcfcfffcfcfcfefefcfcfefefcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfcdcdcfcfcdcdcfcfcccfcfcfcccfcfcfc5454fcfc5454fcfc00fcfcfc00fcfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcdcfcdcfcdcfcdcfc54fc54fc54fc54fc00fc00fc00fc00f8f8f8f8f8f8f8f8f5f0f5f0f5f0f5f0f4f4f4f4f4f4f4f4f0fcf0fcf0fcf0fcf0faf0faf0faf0faf0f0fff0f0f0fff0) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x56a0c6b505d6a92ead515d6a4aed5537a6a9a else 0
  | 3 => if page < 2 then (if page < 1 then 0xa0b8222b50081a0a022005063801418600505f801417600405ca01597180505b80141660062a11018684405da11017284405ba1101ba82406da0901b282406ba0901aa824067a090196824063a09018282405fa09017a824059a110162844057a11015a824056883015a00c05055801414e005051801413600504b801411600554380140ea40503910140da405035101403a40500c901402a4052089014022404d089012c224000a9900029e4000a5900028e4000a1900027640009b9000266400097900024640008f90001de4000479 else 0xd15a807356a01c95a806b50301ad40986b501a1) else 0
  | 4 => if page < 2 then (if page < 1 then 0xa02f340566809cd01195c11d402668045c008bac10edc23540471008da00f340166801cd6a09a0112017f802ef0059e01436027ec049d808bb01136021ec042d8083b0103601fec03ed80c370172e02ddc06d780d6f01a9e032bc063780c0f017de02cdc058b80acf00e7a01c74037e806bd00d3a01578028f004de0083a00ff401d780397005ba00974011e8021d0019e002bc004780a19 else 0xe5433c6867850cefa19d14339a867250cd6a19ab43342566846cd0799ad4179ab1f2563d06d9a0cf341966827cd0499a087340f66819cd0319ac60f40be6815cd0299a04f35899e810cd620da03f34076680dcd0199) else 0
  | 5 => if page < 1 then 0xe5fe1fdffcdfc9fadfa1f79f6df67f65f4ff49f3df33f31f2bf29f27f21f1ff17f13f11f09f05f03fa1bacf21d08fa19 else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2a else 0
  | 3 => if page < 1 then 0xd435 else 0
  | 4 => if page < 1 then 0x9c27 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 7
  | 3 => 70
  | 4 => 100
  | 5 => 32
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 128
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 7)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 3
  | 3 => 27
  | 4 => 41
  | 5 => 16
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 9
  | 3 => 96
  | 4 => 150
  | 5 => 61
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 3
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 8
  | 4 => 8
  | 5 => 6
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x30 else 0
  | 3 => if page < 1 then 0x115882140808c60400000481c51c1082040140042 else 0
  | 4 => if page < 1 then 0x3890073d40460d60006266420040041850030000c010f1401c0000081041 else 0
  | 5 => if page < 1 then 0x245009082ec4083900000680 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x46080ca2 else 0
  | 3 => if page < 2 then (if page < 1 then 0x5080002214075c3f28160000003a004d000f8826461236581e0474440064000000377654001000001a3d00787a305a385e84706e6a6c2d685647240008832c7e else 0x822f661d3e2a4e34623c006032424a0a0d204003484c7c71187252862e8a4100) else 0
  | 4 => if page < 3 then (if page < 1 then 0x481d2c008b52212f749a906972a02234004778aa76ba00ad4a5c64324facc69c090fb6701904496d8a7e9626b425c288000006af3e8d68bc465a0d6a00988200 else (if page < 2 then 0xb00a4914e003a000000878994804c00271a8c73b8c4a243a800386000500086006c2b13007c57000042b26230668e1f5800546e15ae400071005eb014c00000 else 0x3c28567a9e44009217a6840008002011be368f230002)) else 0
  | 5 => if page < 1 then 0x589288b198b980601ea0049300011de8e700000000dad632f4d400a9b0301570b1f00994fb831a034bee92501f else 0
  | 6 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 7 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 70 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 70 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 100 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 100 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 32 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 32 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor7

namespace SignedFrontier.SmallCert.Minor10

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xe8eefafee8eefafe
def negative : List Nat := [0, 8, 10, 16, 20, 24, 25, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,2,10),(0xffff0000ffff0000,4,20)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xffff00ccffff00ccffff00aaffff00aaffff0000ffff0000fff0fff0fff0fff0fff0ccc0fff0ccc0ffccffccffccffccffaaffaaffaaffaaff00ff00ff00ff00ff00cc00ff00cc00ff005500ff005500ff000f00ff000f00ff000000ff000000fcfcfcfcfcfcfcfcfafafafafafafafaf8f8f8f8f8f8f8f8f0fff0fcf0fff0fcf0fff0f0f0fff0f0f0fef0fef0fef0fef0fcf0fcf0fcf0fcf0faf0faf0faf0faf0f0fafaf0f0fafaf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeee00ee00ee00ee00eaeaeaeaeaeaeaeacf00cf00cf00cf00ccccfffcccccfffcccccfefeccccfefeccccfcfcccccfcfccccccccccccccccccccc4444cccc4444cccc0c0ccccc0c0ccccc00cccccc00cccccc0000cccc0000cc44cc44cc44cc44cc00cc00cc00cc00c0c0c0c0c0c0c0c0af00af00af00af00aaaafafaaaaafafaaaaaaaaaaaaaaaaaaa22aa22aa22aa22aa00aa00aa00aa0088888888888888885f5f00005f5f00005f005f005f005f00550055005500550050505050505050504c4c4c4c4c4c4c4c44444444444444443f003f003f003f0033330000333300002a2a2a2a2a2a2a2a0f0f00000f0f00000f00ff000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0000fff00000fff00000ff000000ff000000fafa0000fafa0000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa0000000000000000 else 0xffffff00ffffff00fffff0f0fffff0f0ffffccccffffccccffffcc00ffffcc00ffffc0c0ffffc0c0ffffa0a0ffffa0a0ffff8888ffff8888ffff4444ffff4444ffff0c0cffff0c0c) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x944864121 else 0
  | 3 => if page < 1 then 0x198d12102330180644c80462620090c3004841800184c000ba6000767 else 0
  | 4 => if page < 1 then 0x8cf0f19b9e3899bc13366266c84ce3093911331a24e34435e06389073009fc00cf8031d805fb00b760166c02bd808cf0115e0223c04378084f0105e0203c03f7807cf00dee01b5c035b80517009ae010f4020e803fd0077a00d5c017f0028f004ee0087400eb8019e002ae004dc00678008f else 0
  | 5 => if page < 1 then 0x91f79f75f73f69f67f53f3df39f37f2df2bf25f1ff17f13f11f0ff0bf07f05f03f8cf137 else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x25 else 0
  | 3 => if page < 1 then 0x33 else 0
  | 4 => if page < 1 then 0x27 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 9
  | 4 => 48
  | 5 => 24
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 128
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 7)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 19
  | 5 => 15
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 7
  | 3 => 14
  | 4 => 73
  | 5 => 54
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 5
  | 4 => 7
  | 5 => 6
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1 else 0
  | 3 => if page < 1 then 0xa00 else 0
  | 4 => if page < 1 then 0x19941202040403282040002681 else 0
  | 5 => if page < 1 then 0x8e0380c07008401412 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x87 else 0
  | 3 => if page < 1 then 0x8218030163015ea else 0
  | 4 => if page < 2 then (if page < 1 then 0xe003616a60de403c0dc2262c569d49cba492e15baa00450af6a2002600035000158261357330001600007ca87903403d8c0004c3400522 else 0x54b271a277e5c2d1) else 0
  | 5 => if page < 1 then 0x40710068b00001e30561b89980001434f02e02d8c02174424dcad69a1a5fa090460caa805404a43ac else 0
  | 6 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s34_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 9 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 9 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 48 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 48 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 24 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 24 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor10

namespace SignedFrontier.SmallCert.Minor11

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeaeafffeeaeafffe
def negative : List Nat := [0, 16, 18, 20, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,2,18)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffffff00ffffff00ffffaaaaffffaaaaffff0000ffff0000ffccffccffccffccffaaffaaffaaffaaff00ff00ff00ff00fafafafafafafafaf3f0f3f0f3f0f3f0f0f0fff0f0f0fff0f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaffaaaaaaffaaaaaaaaaaaaaaaaaa5555000055550000550055005500550044444444444444440f000f000f000f000000ff000000ff000000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xd4e34aaf2980f6064c173 else 0
  | 4 => if page < 1 then 0x6ee7785df793caf25c7d15c37 else 0
  | 5 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1d else 0
  | 4 => if page < 1 then 0x15 else 0
  | 5 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 6
  | 4 => 10
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 32
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 5)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 3 => 3
  | 4 => 5
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 13
  | 4 => 19
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 2
  | 4 => 4
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 4
  | 4 => 5
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x34 else 0
  | 4 => if page < 1 then 0x1801 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x804a000036190 else 0
  | 4 => if page < 1 then 0x38cf18265600800015212200 else 0
  | 5 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 6 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 10 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1 0 = true :=
  chunk5x0
theorem verified : ∀ k ≤ 5, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 6 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 5
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    5 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor11

namespace SignedFrontier.SmallCert.Minor13

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeafefefeeafefefe
def negative : List Nat := [0, 8, 16, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,18,26),(0xffff0000ffff0000,10,26)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffffaaaaffffaaaaffff0000ffff0000ffaaaaaaffaaaaaaff00ff00ff00ff00ff00aa00ff00aa00ff000000ff000000fafafafafafafafaf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaa5500550055005500550000005500000044444444444444440000ff000000ff000000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xa97963 else 0
  | 3 => if page < 1 then 0x97c548e5254450d3859c28e067 else 0
  | 4 => if page < 1 then 0x4efdf4f4b9745f47 else 0
  | 5 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x18 else 0
  | 3 => if page < 1 then 0x1b else 0
  | 4 => if page < 1 then 0x13 else 0
  | 5 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 8
  | 4 => 7
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 16
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 4)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 4
  | 3 => 18
  | 4 => 19
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 3
  | 3 => 5
  | 4 => 5
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x2 else 0
  | 4 => if page < 1 then 0x220 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x802 else 0
  | 3 => if page < 1 then 0x1c0030c800954029604b40 else 0
  | 4 => if page < 1 then 0x22cd28008550526014001a0 else 0
  | 5 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 4,slot % 4)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s12]
  | 3 => [s12, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s12_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 8 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 7 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1 0 = true :=
  chunk5x0
theorem verified : ∀ k ≤ 5, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 6 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 5
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    5 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor13

namespace SignedFrontier.SmallCert.Minor14

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeafefffeeafefffe
def negative : List Nat := [0, 16, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,8,24)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xf0f0fafaf0f0fafaf0f0f0f0f0f0f0f0eeeeffeeeeeeffeeeeeeeeeeeeeeeeeeeeeecccceeeecccceecceecceecceecceafaeafaeafaeafaeaeaeaeaeaeaeaeadddd0000dddd0000dd00dd00dd00dd00ccccffccccccffcccccccccccccccccccccc4444cccc4444cccc0c0ccccc0c0ccccc00cccccc00cccccc0000cccc0000cc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00cc00cc00cc00c4c4c4c4c4c4c4c4c0ccc0ccc0ccc0ccc0c0c0c0c0c0c0c0aaeeaaeeaaeeaaeeaaaaffeeaaaaffeeaaaaffaaaaaaffaaaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000aaaa0000aa0aaa0aaa0aaa0aaa00ff00aa00ff00aa00aa00aa00aa0088888888888888885f5f00005f5f00005f005f005f005f0055ff000055ff000055550000555500005500ff005500ff005500550055005500550000005500000050505050505050504c4c4c4c4c4c4c4c44cc44cc44cc44cc4444cccc4444cccc444444444444444444440044444400443f3f00003f3f00003f003f003f003f002a2a2a2a2a2a2a2a0f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a00ff000000ff000000cc00cc00cc00cc00aa00aa00aa00aa0000ffcc0000ffcc0000ffaa0000ffaa0000ff000000ff000000cccc0000cccc0000aaaa0000aaaa00005500000055000000000000000000 else 0xffffff00ffffff00ffffccccffffccccffffc0c0ffffc0c0ffffaaaaffffaaaaffffaa00ffffaa00ffff8888ffff8888ffff0a0affff0a0affff00ccffff00ccffff00aaffff00aaffff0000ffff0000ffccffccffccffccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffaa0000ff88ff88ff88ff88ff550000ff550000ff0f0000ff0f0000ff0aff0aff0aff0aff00ffccff00ffccff00ffaaff00ffaaff00ff00ff00ff00ff00aa00ff00aa00ff005500ff005500ff000f00ff000f00ff000000ff000000fcfcfcfcfcfcfcfcfafafffafafafffafafafafafafafafafafaf0f0fafaf0f0faf0faf0faf0faf0f8f8f8f8f8f8f8f8f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f0fcf0fcf0fcf0fcf0faf0faf0faf0faf0f0fff0f0f0fff0f0f0fcfcf0f0fcfc) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x253d44a2e2 else 0
  | 3 => if page < 1 then 0x2d49790c925e2264978892f0d22d4934292f0c432493029924c0a49a3029260b8a49a248b46891249825092f022249808292600880497980125de0049758012dc600496ea0125b4804a4ea01253a80414ea016939804c4e600c53b00416a9013228c04c823012502804936a0124d2804434a0108d2805a346014cd180493320124c480443120160c180273060124ba805a2e6009cb9802724c009c8b004b209012c7c400073a00014380004ee else 0
  | 4 => if page < 2 then (if page < 1 then 0x8db8bb89b87b85b83b81b7fbb77b57b37ad7a77a57a37cafc8fc6fc4fc2fc0fbefb8fb0faefaafa8f9ef9d79b798f6ef6d767d65d63d5fd5dd59d57d4ef49e47e43e40f3af39736f34f3373172ef2bd29d27d25d20f1f71de0cf0af08f02f4ee else 0x125e6a4bccda933c9257324af25a3daae7bb30f6a61e5aacc945ab48ad24fea49ad5a356c869d68d39e1a74934bb468f24c6ad18b3c3169262790c1e61839a307305cef0972492cda255c849b30934d126982552c4b33061de0ae1a14e302ac683bad053a708e921170422ed043cc0876211a8c238c0439208d3004f25e6249a55a3469262401c78029f004fe009bc024ec048d808fb) else 0
  | 5 => if page < 1 then 0xcffcdfc9fbbfb5f99f97f79f61f5bf55f45f3ff3df35f31f25f1bf19f17f15f13f11f0ff09f07f05f93bb57c8f98f34f31725d08f else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x27 else 0
  | 3 => if page < 1 then 0x35 else 0
  | 4 => if page < 1 then 0x9c19 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 53
  | 4 => 127
  | 5 => 35
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 128
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 7)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 28
  | 4 => 56
  | 5 => 17
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 5
  | 3 => 107
  | 4 => 201
  | 5 => 60
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 5
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 7
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x3542007945c04004012b3ac0100443100a0 else 0
  | 4 => if page < 1 then 0x1581486490940860000052810011031c014050214000a00200000409710830400c303042a800001c4089 else 0
  | 5 => if page < 1 then 0xff0e500287080c40012e else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x42 else 0
  | 3 => if page < 2 then (if page < 1 then 0x48b063040002cb7960c52471800001a001900030904cf9516018a156537735ba80001c002c000340002fa08802e9979f88956493680add39 else 0x111a024e2a0ce00b40000180332015c000909638d51689b33a00db8a638a648aec05c007a6bd) else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x8c8a4592d512afb1119900be0000183290e42604846ac874a480e5a60ef656bdf085f213703df4a7b47df741062e00bbbc2d0ccf00dc00ced894f5007e0086b8 else 0x1cc20a5e7bc4d6bf96fc66774b75ef177115b2000052000037c1b9ac004248dee625ee4cb582eaf81a54aa1e3c0068c09a00786ef900000058d483d2e03fca00) else (if page < 3 then 0x203000d900462998002300a0e82a9c36b6026c7688fa003510d0d1e962a2aea8399fdadbb000cc0000a5000000003be208ec64388f939e008e1481e3c55a50 else 0xc6600072b3ba4e5c00)) else 0
  | 5 => if page < 1 then 0x505903408e1b25867400a30089ae460158832d47217cf079a887181e1909f9f480d3004401d0054dc000204963300519000d00000 else 0
  | 6 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 53 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 53 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 15 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 127 0 = true :=
  (@span_join (checked 4) 112 0 15 chunk4x0 chunk4x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 35 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 35 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor14

namespace SignedFrontier.SmallCert.Minor20

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeefafe00eefafe
def negative : List Nat := [0, 8, 10, 16, 20, 24, 25, 26, 27, 28, 29, 30, 31]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,2,10),(0xffff0000ffff0000,4,20)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffff0000ffff0000ff00ff00ff00ff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 8
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 3)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s34_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor20

namespace SignedFrontier.SmallCert.Minor21

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x88eefefe88eefefe
def negative : List Nat := [0, 8, 16, 20, 24, 25, 26, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,17,25),(0xffff0000ffff0000,4,20)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xfaf0faf0faf0faf0f8f8f8f8f8f8f8f8f3f3f0f0f3f3f0f0f2f2f2f2f2f2f2f2f0fff0f0f0fff0f0f0faf0faf0faf0faf0f0fafaf0f0fafaf0f0f0f0f0f0f0f0f0f03030f0f03030f0f00000f0f00000f030f030f030f030f000f0f0f000f0f0f000f000f000f000eeeeeeeeeeeeeeeeee00ee00ee00ee00cceecceecceecceeccccfefeccccfefeccccfcfcccccfcfccccceeeecccceeeeccccdcdcccccdcdcccccccccccccccccbabababababababab0b0b0b0b0b0b0b0aaaafafaaaaafafaaaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa0a0aaaaa0a0aaaaa0000aaaa0000aa22aa22aa22aa22aa00aa00aa00aa00a0a0f0f0a0a0f0f0a0a0a0a0a0a0a0a08888888888888888777700007777000077007700770077007070707070707070333330303333303033330000333300003300330033003300323232323232323230f030f030f030f03030f0f03030f0f03030303030303030222222222222222210101010101010100f0f00000f0f00000f000f000f000f000a0a0a0a0a0a0a0a00fff0f000fff0f000ff00f000ff00f000ff00aa00ff00aa00ff000000ff000000f0f0f000f0f0f000f000f000f000f000ee00ee00ee00ee00aa00aa00aa00aa0000fff00000fff00000ff000000ff000000fefe0000fefe0000fafa0000fafa0000f0f00000f0f00000aaaa0000aaaa00003030000030300000000000000000 else 0xffffff00ffffff00fffffafafffffafafffff0f0fffff0f0ffffaaaaffffaaaaffff8888ffff8888ffff3030ffff3030ffff00aaffff00aaffff0000ffff0000fff0fff0fff0fff0fff0f0f0fff0f0f0fff00000fff00000ffaaffaaffaaffaaff88ff88ff88ff88ff330000ff330000ff110000ff110000ff00fff0ff00fff0ff00ffaaff00ffaaff00ff00ff00ff00ff00f0f0ff00f0f0ff00f000ff00f000ff00aa00ff00aa00ff003300ff003300ff000f00ff000f00ff000000ff000000fefefefefefefefefcfcfcfcfcfcfcfcfafafafafafafafafafaf0f0fafaf0f0) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x11172888b92c45e9e22e4f11627 else 0
  | 3 => if page < 1 then 0x224234188b818622506200b946004c5d101157440445d101117240445c5012620c044683011140c02e4b8011108c0323cc00c8ed002e19100b8324044083012418c048063011018c04402301117040005f9000176400059900024cc0009a700007cc0000ab else 0
  | 4 => if page < 2 then (if page < 1 then 0x880ce941e860398606b880c60187402ee805bd016b602cec056d80a5b010f6020ec040d807fb00fb601eec03cd8077b00eb601cec04fb80997012ee02bbc055780a2f0139e0245c047b808d70116e0225c037d806bb00d36018dc02ad8053b00a3601378025f0047e0087600f3c01db8039b006f600c6c017d802db00576009ec00eb801b70032e005ec009b800ef00136001ec001d805d9 else 0x2cc89d9893a5127120cec443c46c782934c8ff211acc43478457310acec8e9d919382326ec64e20c3b41932a327105cd703ccc073b20d7141ce2039c406b) else 0
  | 5 => if page < 1 then 0xb7fb3fb1fa7fa1f89f83f6df67f65f49f45f41f3ff35f33f2bf29f25f23f21f19f15f11f0df07f05fb3b83b8972bb19707b else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2a else 0
  | 3 => if page < 1 then 0x35 else 0
  | 4 => if page < 1 then 0x9c27 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 31
  | 4 => 90
  | 5 => 33
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 128
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 7)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 3
  | 3 => 16
  | 4 => 36
  | 5 => 16
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 9
  | 3 => 59
  | 4 => 130
  | 5 => 61
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x804 else 0
  | 3 => if page < 1 then 0xe9802104a03180040c84 else 0
  | 4 => if page < 1 then 0xe80847280a0c9c200008b0d44cc0820020411c0280301200040248 else 0
  | 5 => if page < 1 then 0x19057200431fcc008240 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x480610320 else 0
  | 3 => if page < 1 then 0xb6c9280d409a4c4fe3bc04780e828bc5ae4a88c6b4cc807346a700001400000e03602a03d82cbd0639cdd011 else 0
  | 4 => if page < 3 then (if page < 1 then 0x66642d0000a201b2000c0000003478240000a6068c443c0086179d003e4a7282422aa8738a04478e0836658b508410005262149a227c6e760a1b922f97ab2b6f else (if page < 2 then 0x3b7d4e6027199c48129400709f88000e7e9800a40068003900009600acae3100aaa000ad2e0232581e5c5e9e801f90562054a14c8f036a29a3001c417a6c74b0 else 0x5a)) else 0
  | 5 => if page < 1 then 0x1842f862b4ae91a000249ac687ca240c000053800010000022d70d40192400730527970000000287a885007258d0d54f13328020136 else 0
  | 6 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s01]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 5 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 31 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 31 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 90 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 90 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 33 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 33 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor21

namespace SignedFrontier.SmallCert.Minor22

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x88f8fefe88f8fefe
def negative : List Nat := [0, 8, 16, 17, 18, 24, 25, 26, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,20,28),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xff00f000ff00f000ff00aa00ff00aa00ff003300ff003300ff000f00ff000f00ff000000ff000000fafafafafafafafafaf0faf0faf0faf0fa00fa00fa00fa00f8f8f8f8f8f8f8f8f300f300f300f300f0f0fafaf0f0fafaf0f0f0f0f0f0f0f0f0f03030f0f03030f0f00000f0f00000f000ff00f000ff00f000f0f0f000f0f0f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeeeddddccccddddccccdcdcdcdcdcdcdcdcccfcfcfcccfcfcfcccfcccfcccfcccfcccccfcfcccccfcfccccceeeecccceeeeccccccccccccccccaafafafaaafafafaaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa0a0aaaaa0a0aaaaa0000aaaa0000aa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa00aa00aa00aa00a0a0a0a0a0a0a0a08a8a8a8a8a8a8a8a8888aaaa8888aaaa88888888888888887777000077770000770077007700770070707070707070703333000033330000330033003300330030f030f030f030f0303030303030303022222222222222220fff00000fff00000f0f00000f0f00000f000f000f000f000a0a0a0a0a0a0a0a00ff00f000ff00f000ff00aa00ff00aa00ff000000ff000000fa00fa00fa00fa00f0f0f000f0f0f000f030f000f030f000f000f000f000f000f0000000f0000000aa00aa00aa00aa0000ff000000ff000000f0f00000f0f00000aaaa0000aaaa0000000000000000 else 0xffffff00ffffff00fffff0f0fffff0f0ffffaaaaffffaaaaffff8888ffff8888ffff00f0ffff00f0ffff0000ffff0000fff0fff0fff0fff0fff0f0f0fff0f0f0ffaaffaaffaaffaaff88ff88ff88ff88ff0fff00ff0fff00ff0f0000ff0f0000ff0aff0aff0aff0aff00fff0ff00fff0ff00ffaaff00ffaaff00ff00ff00ff00) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xa92c222b0c4541 else 0
  | 3 => if page < 1 then 0x52929114967441c4743887ccb4c322121aa1119c2071040cf0892b0d1501a20221c0089800f3 else 0
  | 4 => if page < 2 then (if page < 1 then 0x9ceceb4cf1d8f3bb14776226a43567069ba0d39618f1031d78699f0d6241a61814c02ce8057d00a7a01474027e8091b00e7601bec035d808d70116e0225c043b808570106e0263c04b78088f00fee01f5c03db8079700eee01c5c036b8067b00c6e0185c02fb805d7008bc010f801ff0037e006bc00c3c017b802db004f60085c00cb80177002ae004dc008d80117001ae002dc044380113 else 0x48773) else 0
  | 5 => if page < 1 then 0x9ff9df9bf93f8ff77f75f65f5ff5bf41f3bf39f33f2bf29f25f23f1ff1df1bf15f0df09f07f05f03f7775f71570d7 else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x27 else 0
  | 3 => if page < 1 then 0x27 else 0
  | 4 => if page < 1 then 0x9c27 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 3
  | 3 => 16
  | 4 => 65
  | 5 => 31
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 128
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 7)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 2 => 2
  | 3 => 8
  | 4 => 25
  | 5 => 15
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 6
  | 3 => 30
  | 4 => 93
  | 5 => 54
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 5
  | 4 => 5
  | 5 => 4
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 3
  | 3 => 5
  | 4 => 8
  | 5 => 6
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2 else 0
  | 3 => if page < 1 then 0x8050121002 else 0
  | 4 => if page < 1 then 0x600000002b04183b823020e1400c0 else 0
  | 5 => if page < 1 then 0x279406050410402 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1300c else 0
  | 3 => if page < 1 then 0x230a002702f8eba34056593f02c0148c027709 else 0
  | 4 => if page < 2 then (if page < 1 then 0x4c17754e36285c715600727044122c00043852275e5a331e761c0074006142001a40313b3c06000a6e00107c000080000800664822000000006300002e252a else 0x586c784a46680c6a00345f5d507a67540e023e237e1418640024200069) else 0
  | 5 => if page < 1 then 0x590200992100da750e8a8aa4a4000669c6fc039c002a1800002e9ecac038d0fb897ccd40765631540 else 0
  | 6 => if page < 1 then 0x0 else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s01]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 3 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 16 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 16 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 65 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 65 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 31 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 31 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor22

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfefefeeafefcfec8
def negative : List Nat := [0, 1, 2, 4, 5, 8, 16, 17, 24, 32, 34, 36, 40, 48, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,2,3),(0xcccccccccccccccc,1,3),(0xf0f0f0f0f0f0f0f0,2,6),(0xff00ff00ff00ff00,1,9),(0xffff0000ffff0000,2,18),(0xffffffff00000000,1,33)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xff00aaaaffaa0000ff000000ff000000fcfc0000fcfc0000fafa0000fafa0000f4f40000f4f40000f0f00000f0f00000ccccaaaaeeee0000cccc0000cccc0000c0c00000c0c00000aaaa0000aaaa0000a0a00000a0a0000050500000505000004444000044440000303000003030000022220000222200000c0c00000c0c00000a0a00000a0a000000fc000000fc00000000fffffafa00000000ffff222200000000ffff000000000000fffafffa00000000ff22ff2200000000ff00ff0000000000fcfcfcfc00000000fafafafa00000000f2f2f2f200000000f0f0f0f000000000cccccccc00000000c0c0c0c000000000aeaeaeae00000000aaaaaaaa00000000aaaa222200000000aaaa00aa00000000aaaa000000000000aa22aa2200000000aa00aa0000000000a2a2a2a200000000a0aaa0aa00000000a0a0a0a00000000088aa88aa000000008888888800000000505050500000000044444444000000003333222200000000333300000000000033223322000000003300330000000000323232320000000030303030000000002a2a2a2a0000000022aa22aa000000002222aaaa0000000022222222000000000c0c0c0c000000000aaa0aaa000000000a0aaaaa000000000a0a0a0a0000000000fa00fa0000000000aaaaaa0000000000aa00aa0000000000220022000000000000aaaa0000000000000000 else 0xf0f0f0f000000000f0f00000f0f00000f00ff000f00ff000f000f00afaaafaa0f000f000f000f000cff0cff0c0c0c0c0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0caeaeaeae0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c00000c0c00000c000c000c000c000aff0a0a0aff0a0a0aaa0aaa0aaa0aaa0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a000a000a0008080808080808080505050500000000050500000505000005000500050005000404040404040404030303030000000003030000030300000300030003000300020202020202020200ffffff00cccccc00ff00ff00cc00cc00ff00ff0000000000ff000a00ff000a00ff000000ff000000fc00fc00fc00fc00fc000000fc000000fa00fa00fa00fa00fa00fa0000000000f5000000f5000000f300f30000000000f000f000f000f000cc00ccaaeeaaee00cc00cc00ee00ee00cc00cc00cc00cc00c000c000c000c000bb00bb0000000000af00af0000000000aa00aa00aa00aa00aa00aa0088008800aa00aa0000000000a000a000a000a000500050005000500044004400440044003f003f00000000003f0000003f00000033003300000000003000300030003000220022002200220022002200000000000c000c000c000c000a000a000a000a0000ffff0000cccc0000ffff000000000000fffc0000fffc) else (if page < 3 then 0x50ff50ff5050505050f050f050f050f050505050fafafafa50505050f0f0f0f0505050507070707050505050505050505050505000000000505000005050000050005000500050004c4c4c4c4c4c4c4c44ff44ff4444444444cc44cc44cc44cc4444cccc4444cccc44444444eeeeeeee44444444cccccccc444444444444444444444444000000004444000044440000440044004400440040404040404040403f3f3f3f3f003f003f3f3f3f0c0c0c0c3f3f3f3f000000003f3f3f003f3f3f003f3f00003f3f00003f003f003f003f0037373737000000003737000037370000370037003700370033ff33ff00cc00cc33ff000033ff00003333ffff0000cccc333333330000000033330000333300003300ff003300ff0033003300bbaabbaa330033003322332233003300330033003232323232323232323232320000000030f030f030f030f03030f0f03030f0f030303030303030303030303000000000303000003030000030003000300030002a2a2a2a2a2a2a2a2a2a2a2a00000000232323230000000022aa22aa22aa22aa2222aaaa2222aaaa2222222222222222222222222200220022222222000000002222000022220000220022002222222222002200220022002020202020202020111111110000000010101010101010100fff0fff0ccc0ccc0fff00000fff00000f0fffff0c0ccccc0f0f0f0f0c0c0c0c else 0xc0c00000c0c00000c000c000c000c000bbbbbbbbbb00bb00bbbbbbbb88888888bbbbbbbb00000000bbbb0000bbbb0000bb00bb00bb00bb00babababababababab0b0b0b0b0b0b0b0afafafafaf00af00afafafaf8c8c8c8cafafafaf00000000afaf0000afaf0000af00af00af00af00aeaeaeaeaeaeaeaeaeaeaeae0c0c0c0caeaeaeae00000000aaffaaff88cc88ccaaff0000aaff0000aaaaffff8888ccccaaaaaaaafafafafaaaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaaaa88888888aaaaaaaa0a0a0a0aaaaaaaaa00000000aaaa0000aaaa0000aa00ff00aa00ff00aa00aa00aaaaaaaaaa00aa00aa22aa22aa00aa00aa00aa00a8a8a8a8a8a8a8a8a2a2a2a2a2a2a2a2a2a2a2a200000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a000a000a0008c8c8c8c8c8c8c8c8a8a8a8a8a8a8a8a88888888aaaaaaaa88888888888888888080808080808080777777774444444477770000777700007700770077007700737373735050505070707070707070705f5f5f5f000000005f5f00005f5f00005f005f005f005f0055ff55ff44cc44cc55ff000055ff00005555555544444444555555550000000055550000ffffaaaa55550000ffff00005555000077770000555500005555000055005500ffaaffaa55005500ff00ff00550055007700770055005500550055005454545454545454)) else (if page < 6 then (if page < 5 then 0xf4f4f4f4f4f4f4f4f4f40000f4f40000f3f3f3f3f300f300f3f3f3f3c0c0c0c0f3f3f3f300000000f3f30000f3f30000f300f300f300f300f2f2f2f2f2f2f2f2f2f2f2f200000000f0fff0ffc0ccc0ccf0ff0000f0ff0000f0f0fafaf0f0fafaf0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f050505050f0f0f0f000000000f0f05050f0f05050f0f00000fafaaaaaf0f00000f0f00000f000f000faaafaaaf000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee44444444eeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeecceecceecceecceeaaeeaaeeaaeeaaececececececececeaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0dddddddd00000000dddd0000dddd0000dd00dd00dd00dd00dcdcdcdcdcdcdcdcd0d0d0d0d0d0d0d0cfcfcfcf00000000cfcf0000cfcf0000cf00cf00cf00cf00cececececececececcffccffccccccccccff0000ccff0000cceecceecceecceecccceeeecccceeeecccccccceeeeeeeecccccccccccccccccccccccc44444444cccccccc00000000cccc4444cccc4444cccc0000eeeeaaaacccc0000cccc0000cc44cc44cc44cc44cc00cc00eeaaeeaacc00cc00cc00cc00c8c8c8c8fafafafac8c8c8c8c8c8c8c8c4c4c4c4c4c4c4c4c0ffc0ffc0c0c0c0c0ffc0c0c0ffc0c0c0c0c0c0eaeaeaeac0c0c0c0c0c0c0c0c0c0c0c000000000 else 0xfff0fff0fff0fff0fff0ff00fff0ff00ffccffccffeeffeeffccffccffccffccffccff00ffccff00ffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffbbffbb00000000ffaaffaaffaaffaaffaaffaaff88ff88ffaaffaaff00ff00ffaaffaacc88cc88ffaaffaa55005500ffaaffaa00000000ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff55ff00ff55ff00ff50ff50ff50ff50ff44ff44ff44ff44ff33ff33cc00cc00ff30ff30ff30ff30ff22ff22ff22ff22ff22ff22ff00ff00ff22ff2200000000ff0cff0cff0cff0cff0aff0aff0aff0aff00fffcff00fffcff00ff00ffaaffaaff00ff00ff00ff00ff00ff00cc00cc00ff00ff0055005500ff00ff0000000000ff000000ffaaaaaaff000000ff000000fefefefefefefefefcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcfc00fcfcfc00fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fcfcfc00fcfcfc00fc00fc00fc00fbfbfbfb00000000fafafafafafafafafafafafafa00fa00fafafafaf8f8f8f8fafafafaf0f0f0f0fafafafac8c8c8c8fafafafa50505050fafafafa00000000fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faaafaaafaaafaaafa00fa00fafafafafa00fa00fa00fa00f8f8f8f8f8f8f8f8f5f5f5f500000000f5f5f500f5f5f500f5f50000f5f50000f500f500f500f500) else (if page < 7 then 0xffffffffc8c8c8c8ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffa0a0a0a0ffffffff50505050ffffffff44444444ffffffff30303030ffffffff22222222ffffffff0c0c0c0cffffffff0a0a0a0affffffff04040404ffffffff00cc00ccffffffff00440044ffffffff000c000cffffffff00004444ffffffff00000c0cffffffff00000000ffffffc0ffffffc0ffffff0affffff0affffff00ffffff00fffffcfcfffffcfcfffffafafffffafafffffafa00000000fffff3f300000000fffff0f0fffff0f0fffff000fffff000ffffccccffffccccffffcc00ffffcc00ffffc8c8ffffc8c8ffffc0c0ffffc0c0ffffbbbb00000000ffffaaaaffffaaaaffffaaaaffff8888ffffaaaaffff0000ffffaaaacccc8888ffffaaaa55550000ffffaaaa00000000ffffaa00ffffaa00ffffa0a0ffffa0a0ffff8888ffff8888ffff5500ffff5500ffff5050ffff5050ffff4444ffff4444ffff3333cccc0000ffff3300ffff3300ffff3030ffff3030ffff2222ffff2222ffff222200000000ffff0f00ffff0f00ffff0c0cffff0c0cffff0a0affff0a0affff00ffcccc00ccffff0000ffffaaaaffff0000ffff0000ffff0000cccc0000ffff000055550000ffff000000000000fffcfffcfffcfffcfffcff00fffcff00fffc0000fffc0000fffafffafffafffafffafffa00000000fff5ff00fff5ff00fff3fff300000000 else 0xffffffffffffccccffffffffffff0000ffffffffffccffccffffffffffccccccffffffffffc0ffc0ffffffffff50ff50ffffffffff44ff44ffffffffff0cff0cffffffffff00ff00fffffffffcfcfcfcfffffffffcfcccccfffffffffcccfcccfffffffffafafafafffffffff0f0f0f0ffffffffeeeeeeeeffffffffeecceeccffffffffddddccccffffffffddccddccffffffffdcdcdcdcffffffffcfcccfccffffffffccccffccffffffffcccccccc))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0xd65fea2e60b81ac949404006b2a3283001acbad4460073759201801d3d64a45006b2a2e91801d3d62c05006b1d2b01801cdd62446006b2506f3001acba9bc6006b1d26f18015194178c005d6a25e18012837978c005d4de5e180000be56a5000035928340000d65223000039bae1c0000e6eb4700003a3ac1c0000e86b07000039fac1c0000e76b07000039b5a1c0000d65407000039b421c0000d64f470000358fd1c0000d63d870000358ab1c0000e6aa0700003588b1c0000731c8e00002505e340000940f4d00002ea3d1c0000e68b870000358051c0000d600870000001859c0000006067 else 0
  | 5 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x45be8a7d10fa0df40be7c7cf4f9e7d3c7a777ce579c7e387c627cbf7972f2d3e59bcb0f959f2abe527ca2f93df273e4a7c937921f22be40bc7ef8f6f1dde397c5d78b5f163e2a7c52f899f12be217c3ef879f0e3e1a7c32f85df09be117c1ef835f063e0b7c14f821f03be057c08f80df013f2876ecb803f else 0xa6bf4c7e96fd19fa15f3ebe7afcf1f9dbf377e6cfcb5f95bf287e4efc7df8abf0c7e12fc1df823f03be04fbf5f7e3efb7decfbd5f783eef7ddcfbb1f73fce37dc4fb79f6bbed47da2fb31f643ec47d7efaf5f5abeb4f564fac7d55beaa7d517a95f525ea3dd44fa81f4e3e9b7d30fa47e483e8f7d1df237e) else (if page < 3 then 0xd600c70052be0051fe00483e003afe00563d00557d00567b0055bb0053bb00523b00513b004d3b005eb7006baf006b6f0068ef0074df00749f00745f00741f0073df00739f0072df00729f00719f00715f00711f0070df00709f00705f006fdf006e9f006ddf006d5f006cdf006c9f006c5f006c1f006a5f006a1f00685f00675f00671f00651f00641f00631f00612f00609f00601f005f5f005e1f005d9f005d1f005cdf005b1f005a1f00596f0057df0056af0055ef00552f00549f00541f else (if page < 4 then 0xbf0817bd8817bc8817b80817b78817d6080fd3080fd2080fd1080fcd080fcc080fcb880fc9880fc7880fc6880fab880fa0880f9a880f97081b8a080f76880f72081769880f69081768081b65880f5f081b5a081d53880f53081750880f4e88174b881b4b081b48881e47081e46881e41080f3e88173c881d3c081d38881e38081e2f080f1e880f94829d88829dd6028f74029e58029d2f028f73019ed600d7bb80d7b200d7d600cf6080d72f00cf1f00d7a8ca1cbad456e9eb07941bdcba9bd6 else 0x58185d4d185790181ebc9817d1180fc6980fab980fa0980f53980f53181748981e9017aebc97a7e9978fe0178fdf178fdd978fdd178fdb978fb2178fa5978f9d978f88978f7d978f7a178f74178f73178f54978f5317a74f978f4897ae45178f30978fe69757d616e788951db21417a8939e37939ed611a7d610e7e98f97e68f4fe00f4f730f4f4f8f4f300f4fab8e2dd6098f73099e2f098fa5081ea3881e92081e91081e90081eac081daa881d91881dac881bab081ba4081ba2081b9a081b))) else (if page < 8 then (if page < 6 then 0x732997e0284f9027debca7d7d627cfd127cfc6a7cfaba7cfa0a7cf53a7cf5327d7e02757b22697e025dbe0259b94255dbaa557d6246ee6a45ee0245e73245e4fa45ee0239ee0235e9a233ac6a32e94231d88a31dbaa317b4a31774231e6ba31ea8a29ed6228fd621e7e0215de0208fe01f57e01e5de01e1d941d9dba9d97e01c5ee01c1e941bfcba9bf6cf1beecd9bdeba9bdeb91bde941bde931bde941bddba9bd7749bde741bde731bde451bded61b27d6192794985de99857be1857d6184f else (if page < 7 then 0xd63ca7e03b4fa8ba5ea8ba1e94ba1e94ba1d943a1da7ba1bbb3a17d63a0fcfba0fa8b99e90399e7c399ebcb997d6398fd1398fc6b98fabb98fa0b98f73b99ee03917b2385774385e94375dbab75773361e88b59de034cfe03497e0341bd63367e6b357e032cf74318f743097e9b05774305ee02f9ba8af5e732f5ea8af3a742edb942e9dbaae97e02d9de02d1de02cdde9ac1de02c1dda2c1d942c1d8aac1dbaac177e2c1d74ac1e742c1dd62a4fe6a9cfe029cf7329cfd629a7e6a997e02997 else 0xe05ed7d65e67e6de57e05e57e9ddd7d65c67e6dc57e05c17e05bd7d65ba7d65b67d65ae7e6da97d659e7e6d997be5917e9eb0fe06b0fdf6b0fddeb0fdd6b0fdbeb0fe0698fe0690fe6e88fe0688fe0668fe0660fe065cfe064cfe063cfe6e34fe0634fd6590fc2d727bad717e6d5cfe055cfe6d4d7bad457d652cfd65167e6d04fe0504fe6d017d64ecfd64e67e04d4fe04b9be6c717d645e7e0450fd6444fe0435de0429dae41b9e0415d94405dbac057e03f1de03eddd63ecfd63e67d63d0f)) else (if page < 9 then 0xe027cbc6b98de5e3aa2e62bb5c094941cd6544a1370358501f588c284dac379426ae0e8714f02523673597f100facbe0807d63984076b1c2201f589a100fac3d8807d6178403b98bc203b5850100fac1006c7e06b0203eb040031c0151947800bad4760067aa370033751780175a8bc00b9545e0070294f00381477801a0a0dc00a8cbba00636537002a328780151933c00e0491e0070244f0035920b801cd903c00e0481e00702b0e80381557401d394ba00e04a5d0070250e802b928740151943a0094ca1d007024ae80381237401c090ba00e0459d0070226e803811274017c88ba00e0565b00702acd802af51ac01c0a43600e0511b0070268d803a7ac5c01acc34e00e05f97 else (if page < 10 then 0xd65f2b92f03592937597fae47acbfd463e9f03583f03597f1f81acbe0fcdd65707e6eb2a23f02b901679bac808fc094ba1ca8ca1cce722a2e66aff5173355ca8b99aa8d39ccd5d6a2e65b5951731d9ea8b98ea8cb1ccd70358e11f9bac6e8fc094b29ca8b998e7545ccc35aa2e65e35acbfaea3e6eb1743d45ccb17381295839acbe2c25e06b1606f3758b01f81ac4f9bc0d62687d65fd2b1f3758951ea2e64ab5cdbba316e6eb1183d45cc7e6b81ac3d8facbe1da5e6eb0ec3f02526f739b7737adcdd61bc794398dee545cc6f6a9ce637b575731bd6d6398de7679cc6f3b1ae6379d41731bce7331cde7399866f59ccbc37b4e6589bdce04a4bc6f03585e1ea2e62f1dc058178d else 0x703412973817794b9c0a8ca5ce6ddea2b682a32caaff7cae63a7d2d729)))) else 0
  | 6 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x337e65fcc9f98ff2efe5bfca7f937f267e4bfc8ff91bf227e43fc7bf8f3f1bfe35fc69f8cff197e31fc61f8bff13fe26fc45f863f0afe14fc1df82bf04fe06fe41f5e77d15f8dbfa6fef9fddbfba7f6efd91fabdf4b7e837cedf88befb7de8fba1f733ea97d4f7a9b74fbe91f914f985f1ede267c14f80df else 0x82ff01fe01fbfff7f7efbfdf5fbe7f7c7ef7fde9fbcff797ef1fdc1fb7ff6efedcfdb7fb6bf6cfed8fdadfb57f67fecefd9bfb03f5d7eb9fd71fadff5b7eaffd5dfab7f567ea9fd4ffa9bf4cfe95fd29fa4ff497e91fd15fa27f43fe86fd09f9dbf3afe74fce7f9bff377e6dfcd9f9aff357e69fcd1f99ff) else (if page < 3 then 0xe0178fd6080f73081e2f080f00733f00727f006fbf006f3f006eff006ebf006e7f006e3f006dff006dbf006aff006abf0068bf00667f0065bf00657f0064bf00647f0063bf00637f0061bf0060ff005e7f005c7f005bbf005b7f005aff005abf0059ff0059bf00577f00573f0056ff0055ff0054ff00547f0052ff00527f00517f0050ff00507f00503f004fff004eff004ebf004e7f004e3f004a7f00487f00483f0047bf00477f00473f0046ff0046bf00467f00463f0045ff0045bf0041bf else 0xc5881fc4081fbf881fbe081fbb881fb2081fb0881faf081fae081fa8881f99881f98081f96081f95081f94881f88881f87881f85881f84081f80881f73081f72881f70881f6e881f6b081f62881f60881f5d081f58081f4f081f4d081f4a881f46081f3f081f3d881f3b081f37881f2f081f2b881f2a081f28081f1f081f1d081f1c081f1b081f10075f1006df10061f10059fe0049fe0041fe0039fe0029f46029f10029f10019f1000df10005fe04a5de06b0fa8b99ee02c1de027dd731bde)) else (if page < 6 then (if page < 5 then 0x731bfe731bdf6e9bfe649bfe5d1bfe5d1bfb4f9bdf461bfee0185fae181fa8981f80981f6e981f5d181f58181f4a981f46181f3b181f37981fe0179fae17afa897af8097af6e97af5d17af5817af4a97af4617af3b17af3797afae15fba895fbe015df5d15fb4a95fbae153de0151f58153d3b153da8943ee0141f46143e37943ee0109fe00f9fae0f6fae0ebbe00e9f4a8ebbae0e3de00e1f3b0e3da88dbee00d9f460dbe378dbea8899fa8893b5d093b5808fdd6081fd3881fd2881fd0081f else 0x80aa5f80a9ef80a9b7e027dfae27dfa8a7df80a7df6ea7df5d27df5827dfe0279fe0269fae257dd3a57bbfa57ba8a57bd6256fe6a55fe0255f80a57b73255f5d257b4fa55f80a47ed0233ebba33ea8a33e94a33dd6232fe6a31fe0231f73231f6b233e58233e58233d4fa31f46229fe0201fa89fbbe01f9f5d1fbbe01edfd29dbdbe1dbdae1dbbd61dafe69d9fe01d9fdb9d9f9d9d9f809dbd731d9f4f9d9f4a9dbd4a9dbbd01bfebb9bfe949bfea89bfbd61befc69befe69bdfe01bdfa09bef) else (if page < 7 then 0xe0579fd6572fe6d71fe0571fae55efd6546fe6d45fe0545fa8d2dfe04c5fa8cb3be04b1fe04a9fe04a5fe042dfe0421fae407dae407bbcc077d6406fd1406fe6c05fe0405fdf405fe03a1fa8b9beae399fa8b99f80b99fe0395fe0385fa8b77ea8b77bd6376fe6b75fe0375f73375fe0359fe0329fa8b27ee0315fe0305fa8aebee42ebbbfaebbae2ebbd62eafe6ae9fe02e9fddae9f962ebb7a2e9f732e9f6eaebb94ac3ee02c3dbe2c3dd62c2fe6ac1fe02c1fdd2c1f7dac1f732c1f6b2c3d else 0xd0547ebbd47ea8ca7e90407ed2d73dbe573dd3d73bbfd73be4547bbfd47bae547beaf01fe9f01fe6701fe3f01fe06b1fe069dfe0695fe0681fe0625fe05fdfe05f1fe05ddfe0589f))) else 0
  | 7 => if page < 2 then (if page < 1 then 0xdeffacff4ffe97fd07f87fefffdf3fbbff60febdfd73fa8ff2ffe59fcabf94ff0efe17fc23f80fee6fdcbfb87f6efed6fd93fb17f60febafd61fa7ff4f7e9afd2bfa33f3ffe7efcf7f9dbf37fe60fcbdf95ff2a7e50fc83f8fbf1d7e38fc6df8aff147e24fc47f883fd65fcd7f80fb99f4fbe607cbd7881f else 0xea7fcdff91ff03f) else 0
  | 8 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x55 else 0
  | 5 => if page < 1 then 0x4310c430c4310c4310c43107c1f else 0
  | 6 => if page < 1 then 0xc4310c4310c43107c1f else 0
  | 7 => if page < 1 then 0x7c1f else 0
  | 8 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 4 => 44
  | 5 => 647
  | 6 => 472
  | 7 => 68
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 512
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 9)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 6)

def bucketCount : ℕ → ℕ
  | 4 => 15
  | 5 => 216
  | 6 => 158
  | 7 => 23
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 4 => 53
  | 5 => 777
  | 6 => 567
  | 7 => 82
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 4 => 6
  | 5 => 7
  | 6 => 7
  | 7 => 6
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 4 => 6
  | 5 => 10
  | 6 => 9
  | 7 => 7
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x215c51011c054c840001 else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0x649c30230142830234007147c01b16180000400002000410006142000020a0206000090800001020000000f4580be0408102005002a00002 else 0x60030a1640883162d48c0e140028e0870008040003a1c105060040306881020c1c1080e40200003c8130e048040848000100c18004b01a5) else (if page < 3 then 0x8410782009c09d08010821e08aad3e0029e042da040e3800a1a4d6850e18012041418002006004800902100030d06080911e0010000b8a87 else 0x2a1401102c80000aa9983128c107240c300080004d)) else 0
  | 6 => if page < 3 then (if page < 1 then 0xc8000000010600100003013a0c080040204080080028308082010a00381160c0000214284140c00010010800200a0400489852808480 else (if page < 2 then 0x44c48e80044030806608003000c0440b860004182025c0004e001090288486000880000101801a601090800080020c30c10183810008201 else 0x200403083b5458202006837a946d40065d84a01c003040c787)) else 0
  | 7 => if page < 1 then 0x68890c116ccd108100304504e0470090c0 else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x87400cf6c000039e60a8aa5d5ae4147263a56813a262dc4940406a100002764408c0103401917e5 else 0
  | 5 => if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x435e6575dd5a09673d6a741d4921933b1a3370003acf018c0000120002076d44f8e400058f22ca435805b0010c000d3000ff6f0007fa2e8a64c1c41e001da00000660bd87e5e9dd1a0000097000000c3 else (if page < 2 then 0x4cd293d1ea5a58b002122ed5f599639d5353180000132248af5403527195391c84f0d68849e00114a10b43b4000009b128e53b92a5c1764397c3e40010c00339816c23d3287d111f60b0007440000800 else 0x78e1778a610cd27555257b54b6fa5b911bd4bd910013f178a7a0e0b7a00f7387c548674910440a6f0940059d991c8002cda72159d0e1e9000ac0026c64800001cc88de194dcd800de41c5a0edd551022)) else (if page < 4 then 0x8ac00a180671282998567c9b41d6681a5715e6100027d969e70927f46da05ecb90ca1a820ea2d8f8074000a24706e0542c0a28c8e3d6272325f001904dd3a6cc8d874f6000798d5055918d76d2b20a45 else (if page < 5 then 0x7ac0018501795bf2f0488ecdd440f33f0cf4754e340b0760c42fc4b6e4890686063a80000c2065ac454009e2139742e609e421daa9ea221897f484e71e8a6765fa3860e000c56205393df4038780026d else 0x720412553025af8b40000000940008c9f8000002803c0016530000001197c4004780000000000006b4000000045942000007cc55824fd0a4e30021e001a9695de3257e11d2d0006f61da10000524000))) else (if page < 9 then (if page < 7 then 0x425225400108000013d92a0f01e3a70a6a9b9d68bd136c846958008a9fc9005c8c0a577c9f00000558000009842a695022c4c04e610e800059000e04895c7158a651ab000ab5f5f552057004818956c else (if page < 8 then 0x8d0300e56f95e749ac8374d1c362641acfb871239c87637ca28fd0051a550f59a45dfd0ae7b048000ddca1923625df09052c349a20c59c000844d9061fc0000118275755d16d001343c43a63cfa2a82a else 0x80c88546282642f50d78285097dc000800050572000002f8742dc0056400706510024242173614684b89a98db732c52356166d93866c1f31d492a46c1cc5f846027ba261007e9264d1b4666ed7724606)) else (if page < 11 then (if page < 10 then 0x630000521b99d54678e243d890023c58528001c69380092e18000931b836364264ecfe09d1f91858994540013970c15000009f8005e84d831e098845000c18cc13000501067919400399b880659530cd else 0x2c0000000535a6568b8865cb08d862d6769c40c05e140f8009cd12218c829000000007bc004458022dff130707706a9c23755e813507b2e8ad67c003680d3454a25000749c9835476c5a80d0000b400) else (if page < 12 then 0x3bd456b996012540fc002a1d714400700f753cae0468540ce936e7c49a6065cb11dc03691830000020215000007e4008f931000007ed62000218820a8915b5adc70613e002318e08a0008f35dba0005d else 0x158961ec0015e020003316e)))) else 0
  | 6 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x88ed74d4d1f8004200975fd9fd2c000000146b09024a649c2ef05f57288bcda000ab7ec70c96955055ee7e440000619bd7eea0000000005db2a000e402741fbcd980054001480034 else 0x60dac000f97e97324600530c901d4b45ca00005b909023c53b06dc37a5da8d2663b800009dc3c008a2724632ff9b00166e41b20808798b1c715af782bcfcb82db9f30589375c0000) else (if page < 3 then 0x3ec4edf559650c000058838013c004de340000521f20075a7c0000e6f547d60000009bbeb80000000cbc217c6244801a7cb0052f381aac2600041dc9a056000017400000047b90d9 else 0xcd120361ea83ce85b1ba434ce13b95ed76550073cf5d108e3c9e08dd49750156180256fc518027af2e70c3acbc1e274d2e37f0a10b5c87649c5635ab74000c002e4470c4f222b663)) else (if page < 6 then (if page < 5 then 0x81d7c037d540008800000de61ae8500000c4001b0b800d38000141676a80000c280001186ad6a8d94e55954f1f000032633920350cf1302b5da003bb272c4a4a00195821971c86a4 else 0x99001186b350833dc2d23d6367bd9afc0159001fc003abe0000080ab05897750000102ea7d6b1c0e97be11435d399b580009aeac018d00624b3477dc72d822000006306ced538a2d) else (if page < 7 then 0x6102c5f53a5412a32870a596887af5a899d3b21988018c5ec13649d959e40cb0323c7729c81d56d578380134fd22acb0fb4384563b09c735e7eb0892adbe257b000dd2100000ec00 else (if page < 8 then 0x9f2404f529a342d1a20e8258d88d09c9529201ef2c4dba02b00531170e5758ce0ca91cc82b0a6f5690bbbf41915bdde5a537c002e7c68a53c85bd46f336dad08724ca9c41ce220a5 else 0x15db038cdd13866174398a074458170200db8f44d179181f70c53e33673c0b08b2e20a5074346ec0049c0095a2945e84700002da99dd80266001ad2401c4)))) else 0
  | 7 => if page < 2 then (if page < 1 then 0x10011a60100f895664bbd3d0c82e26910a704116811ac00354a3d1332a0001c004800b406dd0078dc007000001452fc6000600d0058f830a else 0x73b22a21310a61cb42ca97b66504eb8) else 0
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
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 1,slot % 1)


def steps : ℕ → List Switch
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by simp [steps]

theorem fix (j : ℕ) : reindex (steps j) target = target := by simp [steps,reindex]


def goalColumns : Nat := 0xfefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0x550055 0x594490184080 3 4
    pinBase [0x0,0x550055,0x0,0x440044,0x500050,0x0,0x550000,0x0,0x550055,0x110011,0x50005,0x550055,0x55,0x550055] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0x5555 0x38c288184080 3 4
    pinBase [0x0,0x5555,0x0,0x4444,0x5050,0x5500,0x0,0x0,0x5555,0x1111,0x505,0x55,0x5555,0x5555] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf000f000f000f 0xc31cb38218a3411493001083 4 4
    pinBase [0x0,0xf000f000f000f,0xa000a000a000a,0xc000c000c000c,0x0,0x0,0xf0000000f0000,0xf000f00000000,0x5000500050005,0x3000300030003,0xf000f000f000f,0xf000f000f000f,0xf0000000f,0xf000f] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xff000000ff 0x9259a78218a3105187001083 4 4
    pinBase [0x0,0xff000000ff,0xaa000000aa,0xcc000000cc,0xf0000000f0,0x0,0x0,0xff00000000,0x5500000055,0x3300000033,0xf0000000f,0xff000000ff,0xff000000ff,0xff] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xf0f00000f0f 0xaa88a0288080ae98e12c90c1 4 5
    pinBase [0x0,0xf0f00000f0f,0xa0a00000a0a,0xc0c00000c0c,0x0,0xf0000000f00,0x0,0xf0f00000000,0x50500000505,0x30300000303,0xf0f00000f0f,0xf0000000f,0xf0f00000f0f,0xf0f] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xf0f0f0f 0x6584502480406da4d22ca0c2 4 5
    pinBase [0x0,0xf0f0f0f,0xa0a0a0a,0xc0c0c0c,0x0,0xf000f00,0xf0f0000,0x0,0x5050505,0x3030303,0xf0f0f0f,0xf000f,0xf0f,0xf0f0f0f] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x55555555 0x18408038c28859449079c698 4 5
    pinBase [0x0,0x55555555,0x0,0x44444444,0x50505050,0x55005500,0x55550000,0x0,0x55555555,0x11111111,0x5050505,0x550055,0x5555,0x55555555] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x5555555500000000 0x9a48a0bacaa8db4cb0fbceb8 4 5
    pinBase [0x0,0x5555555500000000,0x0,0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000,0x5555555500000000,0x5555555500000000,0x1111111100000000,0x505050500000000,0x55005500000000,0x555500000000,0x0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xff00ff 0x5511415101005d31c3592182 4 5
    pinBase [0x0,0xff00ff,0xaa00aa,0xcc00cc,0xf000f0,0x0,0xff0000,0x0,0x550055,0x330033,0xf000f,0xff00ff,0xff,0xff00ff] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xffff 0x2880802c90c138c1843cd1c5 4 5
    pinBase [0x0,0xffff,0xaaaa,0xcccc,0xf0f0,0xff00,0x0,0x0,0x5555,0x3333,0xf0f,0xff,0xffff,0xffff] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xff00ff00000000 0xdf6d74cf2c709e69648e2860 4 5
    pinBase [0x0,0xff00ff00000000,0xaa00aa00000000,0xcc00cc00000000,0xf000f000000000,0x0,0xff000000000000,0xff00ff00000000,0x55005500000000,0x33003300000000,0xf000f00000000,0xff00ff00000000,0xff00000000,0x0] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xffff00000000 0xbeeb6caeaa689e69648e2860 4 5
    pinBase [0x0,0xffff00000000,0xaaaa00000000,0xcccc00000000,0xf0f000000000,0xff0000000000,0x0,0xffff00000000,0x555500000000,0x333300000000,0xf0f00000000,0xff00000000,0xffff00000000,0x0] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut16 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0x55555555aaaaaaaa 0xbacaa89a48a0fbceb8db4cb03cd2c91c50c17dd6d95d54d1 5 7
    pinBase [0x0,0x55555555aaaaaaaa,0xaaaaaaaa,0x4444444488888888,0x50505050a0a0a0a0,0x55005500aa00aa00,0x55550000aaaa0000,0x5555555500000000,0x5555555500000000,0x1111111122222222,0x50505050a0a0a0a,0x55005500aa00aa,0x55550000aaaa,0xaaaaaaaa] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut17 : CutCertificate target :=
  makeCutCertificate target Minor20.target 0x3333333333333333 0xe30610a20200e71651a61241f34714b24304f75755b65345 5 5
    pinBase [0x0,0x3333333333333333,0x2222222222222222,0x0,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000,0x1111111111111111,0x3333333333333333,0x303030303030303,0x33003300330033,0x333300003333,0x33333333] Minor20.raw Minor20.nonzero (@Minor20.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut18 : CutCertificate target :=
  makeCutCertificate target Minor5.target 0xf0f0f0f0f0f0f0f 0xc20408e28604d2450cf2c702ca248aeaa686da658efae78 5 6
    pinBase [0x0,0xf0f0f0f0f0f0f0f,0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0x0,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000,0x505050505050505,0x303030303030303,0xf0f0f0f0f0f0f0f,0xf000f000f000f,0xf0f00000f0f,0xf0f0f0f] Minor5.raw Minor5.nonzero (@Minor5.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut19 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xa5a5a5a5a5a5a5a5 0x1c21409e29603ca348beab685d2550df2d707da758ffaf78 5 6
    pinBase [0x0,0xa5a5a5a5a5a5a5a5,0xa0a0a0a0a0a0a0a0,0x8484848484848484,0xa0a0a0a0a0a0a0a0,0xa500a500a500a500,0xa5a50000a5a50000,0xa5a5a5a500000000,0x505050505050505,0x2121212121212121,0x505050505050505,0xa500a500a500a5,0xa5a50000a5a5,0xa5a5a5a5] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0xf0f0f0ff0f0f0f0 0xeb8cb0aa88a079c59438c184ef9cf1ae98e17dd5d53cd1c5 5 7
    pinBase [0x0,0xf0f0f0ff0f0f0f0,0xa0a0a0aa0a0a0a0,0xc0c0c0cc0c0c0c0,0xf0f0f0f0,0xf000f00f000f000,0xf0f0000f0f00000,0xf0f0f0f00000000,0x505050550505050,0x303030330303030,0xf0f0f0f00000000,0xf000f00f000f0,0xf0f0000f0f0,0xf0f0f0f0] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 : CutCertificate target :=
  makeCutCertificate target Minor13.target 0x33333333cccccccc 0x1c60c29648603ce2cab6ca685d64d2d74c707de6daf7ce78 5 6
    pinBase [0x0,0x33333333cccccccc,0x2222222288888888,0xcccccccc,0x30303030c0c0c0c0,0x33003300cc00cc00,0x33330000cccc0000,0x3333333300000000,0x1111111144444444,0x3333333300000000,0x30303030c0c0c0c,0x33003300cc00cc,0x33330000cccc,0xcccccccc] Minor13.raw Minor13.nonzero (@Minor13.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 : CutCertificate target :=
  makeCutCertificate target Minor11.target 0x3333cccc3333cccc 0xbaa9a2f38d3038a182718510beb9e3f79d713cb1c3759551 5 6
    pinBase [0x0,0x3333cccc3333cccc,0x2222888822228888,0xcccc0000cccc,0x3030c0c03030c0c0,0x3300cc003300cc00,0x3333000033330000,0x3333cccc00000000,0x1111444411114444,0x3333000033330000,0x3030c0c03030c0c,0x3300cc003300cc,0xcccc0000cccc,0x3333cccc] Minor11.raw Minor11.nonzero (@Minor11.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut28 : CutCertificate target :=
  makeCutCertificate target Minor22.target 0xff00ff00ff00ff 0x551141510100d71961d309205d31c3592182df39e3db29a2 5 7
    pinBase [0x0,0xff00ff00ff00ff,0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0x0,0xff000000ff0000,0xff00ff00000000,0x55005500550055,0x33003300330033,0xf000f000f000f,0xff00ff00ff00ff,0xff000000ff,0xff00ff] Minor22.raw Minor22.nonzero (@Minor22.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut29 : CutCertificate target :=
  makeCutCertificate target Minor21.target 0xffff0000ffff 0xaa88a0288080bac9a438c184ae98e12c90c1bed9e53cd1c5 5 7
    pinBase [0x0,0xffff0000ffff,0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0x0,0xffff00000000,0x555500005555,0x333300003333,0xf0f00000f0f,0xff000000ff,0xffff0000ffff,0xffff] Minor21.raw Minor21.nonzero (@Minor21.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut31 : CutCertificate target :=
  makeCutCertificate target Minor13.target 0xff00ffff00ff00 0x9e69648e2860df6d74cf2c703ce34c2ca2487de75c6da658 5 6
    pinBase [0x0,0xff00ffff00ff00,0xaa00aaaa00aa00,0xcc00cccc00cc00,0xf000f0f000f000,0xff00ff00,0xff0000ff000000,0xff00ff00000000,0x55005555005500,0x33003333003300,0xf000f0f000f00,0xff00ff00000000,0xff0000ff00,0xff00ff00] Minor13.raw Minor13.nonzero (@Minor13.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut41 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0xffffffff 0x38c1842880803cd1c52c90c179c5946984907dd5d56d94d1 5 7
    pinBase [0x0,0xffffffff,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0x0,0x55555555,0x33333333,0xf0f0f0f,0xff00ff,0xffff,0xffffffff] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut52 : CutCertificate target :=
  makeCutCertificate target Minor13.target 0xaaaaaaaa55555555 0x9c69448c2840bceb4cacaa48dd6d54cd2c50fdef5cedae58 5 6
    pinBase [0x0,0xaaaaaaaa55555555,0xaaaaaaaa00000000,0x8888888844444444,0xa0a0a0a050505050,0xaa00aa0055005500,0xaaaa000055550000,0xaaaaaaaa00000000,0x55555555,0x2222222211111111,0xa0a0a0a05050505,0xaa00aa00550055,0xaaaa00005555,0x55555555] Minor13.raw Minor13.nonzero (@Minor13.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut53 : CutCertificate target :=
  makeCutCertificate target Minor13.target 0xffffffff00000000 0x9e69648e2860beeb6caeaa68df6d74cf2c70ffef7cefae78 5 6
    pinBase [0x0,0xffffffff00000000,0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000,0xffffffff00000000,0x5555555500000000,0x3333333300000000,0xf0f0f0f00000000,0xff00ff00000000,0xffff00000000,0x0] Minor13.raw Minor13.nonzero (@Minor13.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut61 : CutCertificate target :=
  makeCutCertificate target Minor14.target 0x6666666666666666 0x755651345241796692386282f75e71b65a61fb6eb2ba6aa2 5 7
    pinBase [0x0,0x6666666666666666,0x2222222222222222,0x4444444444444444,0x6060606060606060,0x6600660066006600,0x6666000066660000,0x6666666600000000,0x4444444444444444,0x2222222222222222,0x606060606060606,0x66006600660066,0x666600006666,0x66666666] Minor14.raw Minor14.nonzero (@Minor14.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 6 => cut5
  | 8 => cut7
  | 9 => cut8
  | 10 => cut9
  | 11 => cut10
  | 12 => cut11
  | 13 => cut12
  | 15 => cut14
  | 17 => cut16
  | 18 => cut17
  | 19 => cut18
  | 20 => cut19
  | 21 => cut20
  | 22 => cut21
  | 25 => cut24
  | 29 => cut28
  | 30 => cut29
  | 32 => cut31
  | 42 => cut41
  | 53 => cut52
  | 54 => cut53
  | 62 => cut61
  | _ => cut0

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x410410c10410410410410410440410c10c104d101041041043041040000041081 else 0
  | 5 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x24824820b20618018618b00620620d3482092081882192c600f00a24a24824a24924924928a28824924820a249248246 else 0x2882080062c82082c820824820c2c820620a24820820828a18824820920924920824924820818818b2cc2cd206208246) else (if page < 3 then 0x3461861861862c824919218048a28820a28820928a20a28a24828a28a2882082893082c620834824a24b2002c018620a else (if page < 4 then 0x20c20930b20b20924b2cb24c24b20b2cb2492092092082cb20820924820820820b00924d24934834924b24b2c820d208 else 0x28b20820930920820618b2c618d34b2cb34b18d2c618b18b2c000d24820000b00000000634834820c2c820824c2c9249))) else (if page < 8 then (if page < 6 then 0x20b2082c824c24820b2c820820620820824924924924924920b2c82082082082082082082082082082492082cb28a34b else (if page < 7 then 0x18b24924924924d24820820b20930920b249208209249206209249289208206248208249289289249249246208206208 else 0x30620828620930600624024d2cb18634d20b2082492cb2c924b18830c2c82cb24924b2cb20918b34925224820920b2c6)) else (if page < 9 then 0x2c020900d00018934d2cb2cb30b34b2cd20820820820818624820c2c620820828920820924920924934c2c624924d008 else (if page < 10 then 0x34d34000800920820820800820b00a2082060082800002cb1802090082c000924020820800824920820800c000 else 0xa28a286006)))) else 0
  | 6 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xa9e7540004d34c04c00140004d34c04d90145514d34514d65544d34c05934515407aa7aa02a4c04534d3a934400115a0 else 0xf934d34ea79d4d34d34c003e4d14d34d3f934534fe4d34d34d665d4d34d3f934d34d345e7534d3599753454514a9e740) else (if page < 3 then 0x4405514d34514f65556404d34c04c00000004d34c04c0000f93a9e753a9e75179d02a79d03e4d345e7534d34d3000 else 0xd75000035d40000d75000035d40000440000000000000000000000000000000000035d75d56596580d75d75000000580)) else (if page < 6 then (if page < 5 then 0x4c04d30005800000000000000000000000000000004d30134c00000000000160004c04c00000000000134c0000000 else 0x4d34d60000000000004d34d300001301301300003e000000fbef800160004c00000000000004c00134c0000500500014) else (if page < 7 then 0x164c00000004d34c04c00135800000000134c00000005800004d34d30000134d3013f8000000000003e else 0x13000000000016596580000016000016))) else 0
  | 7 => if page < 2 then (if page < 1 then 0x45d79e79e75d75d74001579dfaa79d01179d03ea9e74002a79d000a9e74001d75d75d79d79e79e76aaaa75d011a9d740 else 0x79d56a) else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 6 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then Vector.packedClosed target negative goalColumns pool counts lookup steps k i
   else let c := selectCut (label k i)
        maskedCut c.mask c.patterns c.bound k (pool k i))

theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (Vector.closed_sound target negative goalColumns mask_valid pool counts lookup steps
      (by decide +kernel) (fun r hr => (neg r hr).1) k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change maskedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 44 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 44 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x224 : span (checked 5) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x336 : span (checked 5) 112 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x448 : span (checked 5) 112 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x560 : span (checked 5) 87 560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 647 0 = true :=
  (@span_join (checked 5) 336 0 311 (@span_join (checked 5) 112 0 224 chunk5x0 (@span_join (checked 5) 112 112 112 chunk5x112 chunk5x224)) (@span_join (checked 5) 112 336 199 chunk5x336 (@span_join (checked 5) 112 448 87 chunk5x448 chunk5x560)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x224 : span (checked 6) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x336 : span (checked 6) 112 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x448 : span (checked 6) 24 448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 472 0 = true :=
  (@span_join (checked 6) 224 0 248 (@span_join (checked 6) 112 0 112 chunk6x0 chunk6x112) (@span_join (checked 6) 112 224 136 chunk6x224 (@span_join (checked 6) 112 336 24 chunk6x336 chunk6x448)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 68 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 68 0 = true :=
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
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 9 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full


namespace SignedFrontier.PinnedGraph

def target := SmallCert.Full.target
def raw := SmallCert.Full.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 9 ≤ p.length := by
  have inside : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial target 0 {target} Cone.done inside
  have start : available initial = insert 0 SmallCert.Full.raw.toFinset := by decide +kernel
  rw [start] at access
  have bounded := SmallCert.Full.lower run access
  omega
end SignedFrontier.PinnedGraph

namespace TableLink
open SignedFrontier

def assignment (r : Fin 64) (v : Fin 6) : Bool := r.val.testBit v.val

theorem rawTable : ∀ r : Fin 64, PinnedGraph.initial.map (fun u => u.getLsbD r.val) =
    SevenVertexOneNot.signedStart (assignment r) := by decide +kernel

theorem goalTable : ∀ r : Fin 64, PinnedGraph.target.getLsbD r.val =
    SevenVertexOneNot.sliceTarget (assignment r) := by decide +kernel

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
    (hit : ∀ x, SevenVertexOneNot.signed p o x = SevenVertexOneNot.sliceTarget x) :
    canonical (evaluate p PinnedGraph.initial o) = PinnedGraph.target := by
  have eq : evaluate p PinnedGraph.initial o = PinnedGraph.target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 64 := ⟨i,hi⟩
    change ((p.foldl add PinnedGraph.initial).getD o 0).getLsbD r.val = _
    rw [readDefault,foldRow p PinnedGraph.initial r,rawTable r]
    exact (hit (assignment r)).trans (goalTable r).symm
  rw [eq]
  decide +kernel

theorem sliceRequirement
    (lower : ∀ p o, canonical (evaluate p PinnedGraph.initial o) = PinnedGraph.target → 9 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, SevenVertexOneNot.signed p o x = SevenVertexOneNot.sliceTarget x) : 9 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_11211_aux

open PEqualNP.Outside.L_meta_11211_aux

theorem PEqualNP.Outside.L_meta_11211 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,o⟩
  have ok : PEqualNP.MetaComplexity.FanInTwo C := legal
  have hit : ∀ x, PEqualNP.MetaComplexity.circuitFun 7 C x = SevenVertexOneNot.target x :=
    fun x => (computes x).trans (SevenVertexOneNot.table x)
  obtain ⟨D,mono,bound,evaluates⟩ := SevenVertexOneNot.replacement
    (TableLink.sliceRequirement SignedFrontier.PinnedGraph.lower) C ok hit
  exact ⟨D.gates,D.output,mono,bound,evaluates⟩
