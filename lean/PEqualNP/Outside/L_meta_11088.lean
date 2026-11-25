import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11088_aux

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

def target (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)

def edges : List ℕ := [0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6]
def posted (x : Fin 7 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

theorem table : ∀ x, posted x = target x := by decide +kernel

def witness : Circuit := ⟨[
  ⟨.or, [1,3]⟩,
  ⟨.and, [5,7]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.or, [9,6]⟩,
  ⟨.or, [0,2]⟩,
  ⟨.and, [10,11]⟩,
  ⟨.or, [8,12]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.or, [14,6]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.and, [15,16]⟩,
  ⟨.or, [13,17]⟩], 18⟩

theorem size : witness.size = 12 := by decide +kernel

theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel

theorem rawValue : ∀ x, circuitFun 7 witness x = target x := by decide +kernel

theorem value (x : Fin 7 → Bool) : circuitFun 7 witness x = posted x :=
  (rawValue x).trans (table x).symm

abbrev Input := Fin 6 → Bool
def lift (x : Input) : Fin 7 → Bool := Fin.cases false x
def prism (x : Input) := target (lift x)
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- Pinning input zero saves a paid binary gate, including when a NOT appears elsewhere.
theorem prismSlice (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = prism x := by
  let raw := List.ofFn (fun j : Fin 6 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let pin := fun j : Fin 7 => (fun x : Input => lift x j, decide (j = 3), decide (j = 0 ∨ j = 3))
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    · have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      refine ⟨List.mem_append_left _ (List.mem_append_right _ pos),
        List.mem_append_right _ (List.mem_map_of_mem pos), Or.inr ?_⟩
      simp [pin]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = prism x := by
    simpa [v, pin, prism, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : prism (fun _ => false) ≠ prism (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (j = 3))
    have b := hit (fun j => decide (j = 0 ∨ j = 3))
    simp only [v,pin,List.map_ofFn,Function.comp_def,circuitFun] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = prism x
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

theorem replacement
    (prismLower : ∀ p o, (∀ x, signed p o x = prism x) → 10 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 7 D x = posted x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, fun x => (hit x).trans (table x).symm⟩
  · obtain ⟨p,o,sz,ev⟩ := prismSlice C ok hit
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
    have := prismLower p o ev
    exact ⟨witness, legal, by rw [size]; change 12 ≤ C.gates.length; omega, value⟩

end SevenVertexOneNot

namespace PrismSignedFrontier

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
  | nil => simpa [PrismSignedFrontier.reindex] using h
  | cons op tail ih =>
    have step := h.switched op (ok _ List.mem_cons_self)
    have result := ih step (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    simpa only [PrismSignedFrontier.reindex,Finset.image_image,Function.comp_def] using result

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

end PrismSignedFrontier

namespace PrismSignedFrontier

namespace Prism

def target : W := 0xfffefffcfefeeea0
def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def negative : List ℕ := [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 33, 48]
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun u => ~~~u)

theorem nonzero : target ≠ 0 := by decide +kernel
theorem start : available initial = insert 0 raw.toFinset := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨8,10,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,34,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

end Prism

end PrismSignedFrontier

namespace PrismSignedFrontier.Certificate
open Prism

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 30 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0xa0a0a0a000000000a0a0000000000000a000a000000000008c8c8c8c000000008a8a8a8a0000000088cc88cc0000000088aa88aa000000008888cccc000000008888aaaa0000000088888888000000008888000000000000880088000000000080808080000000005050f0f0000000004444cccc000000003300ff000000000030f030f0000000003030f0f00000000022aa22aa000000002222aaaa000000000fff0000000000000f0c0f0c000000000f0a0f0a000000000f00ff00000000000e0e0e0e000000000ccc0ccc000000000c0ccccc000000000aaa0aaa000000000a0aaaaa000000000a0a0a0a000000000a0a0000000000000a000a0000000000080808080000000000ff00cc0000000000ff00aa0000000000ff00000000000000fa00fa0000000000f0f0f00000000000ee00ee0000000000cccccc0000000000cc00cc0000000000cc00000000000000aaaaaa0000000000aa00aa0000000000aa00000000000000a000a000000000008800880000000000220022000000000000ffaa000000000000fcfc000000000000fafa000000000000eeee000000000000cccc000000000000c0c0000000000000aaaa000000000000aa00000000000000a0a000000000000088880000000000000f000000000000000c0c0000000000000a0a00000000000000cc00000000000000aa0000000000000000 else (if page < 2 then 0xd0d0d0d000000000cfcfcccc00000000cfcccfcc00000000cececece00000000ccffcccc00000000ccfcccfc00000000cceeccee00000000ccccffcc00000000ccccfcfc00000000cccceeee00000000cccccccc00000000cccccc0000000000ccccc0c000000000cccc888800000000ccc0ccc000000000cc88cc8800000000cc0ccc0c00000000cc00ff0000000000cc00cccc00000000cc00cc0000000000c8c8c8c800000000c4c4c4c400000000c0f0c0f000000000c0ccc0cc00000000c0c0f0f000000000c0c0cccc00000000c0c0c0c000000000c000c00000000000bbbbaaaa00000000bbaabbaa00000000bb00bb0000000000babababa00000000b0b0b0b000000000afafaaaa00000000afaaafaa00000000af00af0000000000aeaeaeae00000000aaffaaaa00000000aafaaafa00000000aaeeaaee00000000aaaaffaa00000000aaaafafa00000000aaaaeeee00000000aaaaaaaa00000000aaaaaa0000000000aaaaa0a000000000aaaa888800000000aaaa222200000000aaaa0a0a00000000aaaa00aa00000000aaaa000000000000aaa0aaa000000000aa88aa8800000000aa22aa2200000000aa0aaa0a00000000aa00ff0000000000aa00aaaa00000000aa00aa0000000000a8a8a8a800000000a2a2a2a200000000a0f0a0f000000000a0aaa0aa00000000a0a0f0f000000000a0a0aaaa else 0x3333ffff000000003300ff00ff0000003030f0f0f0f000002222aaaaaaaa00000f0ffffff0f000000f0fffff000000000f00ff00ff0000000c0ccccccccc00000a0aaaaaaaaa000000ffffffff00000000ffffff0000000000ffff00ff00000000f0f0f0f0f0000000cccccccccc000000aaaaaaaaaa00000000fffffafa00000000ffffeeee00000000ffffaaaa00000000ffff000000000000fffefffe00000000fffcfffc00000000fffafffa00000000fff0fff000000000ffeeffee00000000ffccfffc00000000ffccffcc00000000ffaaffaa00000000ffaaaaaa00000000ff88ff8800000000ff00ff0000000000fefefefe00000000fdfcfdfc00000000fcfcfcfc00000000fcfccccc00000000fcf0fcf000000000fcccfccc00000000fafafafa00000000fafaf0f000000000fafaaaaa00000000faf0faf000000000faaafaaa00000000f8f8f8f800000000f0fff0f000000000f0fcf0fc00000000f0faf0fa00000000f0f0fff000000000f0f0fcfc00000000f0f0fafa00000000f0f0f0f000000000f0f0a0a000000000f0c0f0c000000000f0a0f0a000000000eeeeeeee00000000eeeecccc00000000eeeeaaaa00000000eecceecc00000000eeaaeeaa00000000ecececec00000000eaeaeaea00000000e0e0e0e000000000ddddcccc00000000dddcdddc00000000ddccddcc00000000dcdcdcdc)) else (if page < 5 then (if page < 4 then 0xf0000ffff0000000f0000f0ff0000000ccccccccccccc000ccccc0c0ccccc000c0c0ccccccccc000c00cccccccccc000c000ccccccccc000c000ccc0ccc0c000c000c444c444c000aaaaaaaaaaaaa000aaaaa0a0aaaaa000a0a0aaaaaaaaa000a00aaaaaaaaaa000a00aa0a0aaaaa000a000aaaaaaaaa000a0000ffff0000000a0000aaaaaaaa00020002aaaaaaaa0000ffffffff00000000ffff0000ff000000ffff000000000000ffaaffaaffaa0000ff00ffffff000000ff00aaaaffaa0000ff000000ff000000fcfcfcfcfcfc0000fafafafafafa0000f0f0fffff0f00000f0f0ccccfcfc0000f0f0aaaafafa0000f0f00000f0f00000eeeeeeeeeeee0000ccccffffcccc0000ccccf0f0fcfc0000cccccccccccc0000ccccaaaaeeee0000cccc8888cccc0000cccc0000cccc0000cc00cccccccc0000c0c0f0f0f0f00000c0c0cccccccc0000c0c0c0c0c0c00000aaaaffffaaaa0000aaaaffff00000000aaaaff00ffaa0000aaaaf0f0fafa0000aaaacccceeee0000aaaaaaaaaaaa0000aaaaa0a0aaaa0000aaaa8888aaaa0000aaaa0000aaaa0000aa00ff00ff000000aa00aaaaaaaa0000aa00aa00aa000000a0a0f0f0f0f00000a0a0aaaaaaaa0000a0a0a0a0a0a000008888cccccccc00008888aaaaaaaa000088888888888800005555ffffaaaa00005050f0f0f0f000004444cccccccc00003333ffffcccc else 0xbb0000ffff000000af0000ffff000000ae00aeaeaeaeae00aaffffaaaaaaaa00aaffaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaa0aaaaaaaaaa00aa88aaaaaaaaaa00aa22aaaaaaaaaa00aa0aaaaaaaaaaa00aa00ffaaaaaaaa00aa00aaffff00aa00aa00aaffaaffaa00aa00aaf0faf0fa00aa00aaeeaaeeaa00aa00aacceeccee00aa00aaaaaaaaaa00aa00aaaaaa22aa00aa00aaaaaa00aa00aa00aaa2aaa2aa00aa00aa88aa88aa00aa00aa00aa00aa00aa00aa0000000000aa00a0aaaaaaaa00aa0088aaaaaaaa00aa0022aaaaaaaa00aa000aaaaaaaaa00aa0000ffff000000aa0000aaaaaaaa00aa0000aaaa000000a200a2aaaaaaaa00a200a2a2a2a2a200a000a0f0f0f0f000a000a0aaaaaaaa00a000a0a0a0a0a0008c008ccccccccc008a008aaaaaaaaa00880088cccccccc00880088aaaaaaaa0088008888888888005f0000ffff0000004c004ccccccccc004c004c4c4c4c4c0044cccccccccccc003f0000ffff000000330033ffccffcc00330033cccccccc00330000ffff00000030f0f0f0f0f0f000303030f0f0f0f0003000f0f0f0f0f000300030f0f0f0f0002a002aaaaaaaaa0022aaaaaaaaaaaa0022aaaa2222aaaa00222222aaaaaaaa002200aaaaaaaaaa002200aa2222aaaa00220022aaaaaaaa00220000aaaaaaaa000f000ffff0fff0000f000fff00ff00000f000ff0f0f0f0) else (if page < 6 then 0x4cc04cccccccccc03ff0000ffff000002aa02aaaaaaaaaa020a020aaaaaaaaa0202aaaaaaaaaaaa0202aaaa2222aaaa02020a0aaaaaaaaa02020a0a2222aaaa00ffff00ffffff0000ffff00ffff000000ffff00ff00ff0000ff00ffffffff0000ff00ffff00ff0000ff00ff0000000000ff00ccffffcccc00ff00aaffffaaaa00ff00a0ffffa0a000ff0000ffffff0000ff0000ffffcc0000ff0000ffffaa0000ff0000ffff0f0000ff0000ffff000000ff0000f0ff000000ff000000ff000000fc00fc00fc00fc00fa00fafafafafa00fa00fa00fa00fa00fa00aafafaaaaa00fa0000ffff000000f30000ffff000000f0f0f0f0f0f0f000f0f0f000f0f0f000f000f0ffff00f000f000f0fff0fff000f000f0faf0faf000f000f0f0f0f0f000f000f0aafaaafa00f000f000f000f000f00000ffff000000ee00eeeeeeeeee00ee00eeaaaaaaaa00ee00ee00ee00ee00ee00cceeeecccc00ee00aaeeeeaaaa00ee0000ffff000000ec00ececececec00cf0000ffff000000ccffcccccccccc00cccccccccccccc00cccccc00cccccc00cc88cccccccccc00cc0ccccccccccc00cc00ccffff00cc00cc00ccffccffcc00cc00cceeeeeeee00cc00cceecceecc00cc00cccccccccc00cc00ccaaeeaaee00cc00cc00cc00cc00cc000ccccccccc00cc0000ffff000000cc0000cccccccc00cc0000cccc000000c000c0cccccccc else 0xc0cccccfcfccccc0c0ccccccccccccc0c0cccccaeaeeeee0c0ccccc0c0ccccc0c0c0c0cffff0c0c0c0c0c0cfcfcfcfc0c0c0c0cfcfccccc0c0c0c0ceeeeeeee0c0c0c0cecececec0c0c0c0ccccccccc0c0c0c0caeaeaeae0c0c0c0c0c0c0c0c0aff0000ffff00000afa0afaaaaaaaaa0aaaaaaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0aaa0a0aaaaaaaaa0aaa00aaaaaaaaaa0aaa0000ffff00000aaa0000aaaaaaaa0a8a0a8aaaaaaaaa0a2a0a2aaaaaaaaa0a0affffaaaaaaaa0a0afafaaaaaaaaa0a0aaaaafafaaaaa0a0aaaaaaaaaaaaa0a0aaaaaaa0aaaaa0a0aaaaa0a0aaaaa0a0aaa0aaaaaaaaa0a0a8a8aaaaaaaaa0a0a2a2aaaaaaaaa0a0a0f0faaaaaaaa0a0a0aaaaaaaaaaa0a0a0a0affff0a0a0a0a0a0aff0aff0a0a0a0a0afafafafa0a0a0a0afafaaaaa0a0a0a0acececece0a0a0a0aaaaaaaaa0a0a0a0aaaaa0a0a0a0a0a0aaa0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a00aaaaaaaa0a0a0808aaaaaaaa0a0a0202aaaaaaaa0a0a000aaaaaaaaa0a0a0000ffff00000a0a0000aaaaaaaa0a0a0000aaaa00000a0a00000a0a00000a020a02aaaaaaaa0a000a00ff00ff000a000a00aaaaaaaa0a000a00aa00aa0008cc08cccccccccc08aa08aaaaaaaaaa080c080ccccccccc080a080aaaaaaaaa08080808cccccccc08080808aaaaaaaa080808088888888805ff0000ffff0000))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x3333333322222222333333330000000033330000ffff0000333300003333000033223322332233223300ff003300ff0033003300ff00ff003300330033003300323232323232323230f030f0f0f0f0f030f030f030f030f030b030b0b0b0b0b03030f0f03030f0f030303030f0f0f0f030303030b0b0b0b030303030303030302a2aaaaaaaaaaaaa2a2a2a2a2a2a2a2a22ee22eeaaaaaaaa22aaaaaaaaaaaaaa22aa22aaeeaaeeaa22aa22aaaaaaaaaa22aa22aa22aa22aa22aa00aaaaaaaaaa22a222a2aaaaaaaa22a222a2a2a2a2a22222aaaa2222aaaa22222222aaaaaaaa222222222222222222220000ffff000020aa20aaaaaaaaaa0fff0fff000000000fff0000ffff00000f0ffffff0f000000f0fffff000000000f0ff0f0ffff00000f0ff0f0f0f0f0f00f0f0f0ff0f0f0f00f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0000ffff00000f0f00000f0f00000f0c0f0cffccffcc0f0c0f0c0f0c0f0c0f0a0f0affaaffaa0f0a0f0a0f0a0f0a0f00fff0ff00ff000f00ff00ffffff000f00ff00fff0ff000f00ff00ff00ff000f00ff000f00ff000f00cf00ff00ff000f00af00ff00ff000f000f00ff00ff000f000f00cf00cf000f000f000f000f000e0e0e0eeeeeeeee0e0e0e0e0e0e0e0e0e0c0e0ceecceecc0e0a0e0aeeaaeeaa0cff0000ffff00000ccc0ccccccccccc0ccc0ccc0ccc0ccc else 0x8800880088008800880000008800000080cc80cccccccccc80aa80aaaaaaaaaa8080cccc8080cccc8080aaaa8080aaaa8080a0a08080a0a0808088888080888880808080f0f0f0f080808080cccccccc80808080c0c0c0c080808080aaaaaaaa80808080a0a0a0a0808080808888888880808080808080808080000080800000800080008000800077777777000000005f5f5f5f000000005f5f0000ffff00005f5f00005f5f00005f005f00ff00ff005f005f005f005f0055ff55ff0000000055ff0000ffff000055ff000055ff00005555ffff0000000055555555cccccccc55555555aaaaaaaa5555555555550000555555555500550055555555505050505555555544444444555555550000000055555500555555005555505055555050555544445555444455550000ffffaaaa55550000ffff000055550000555500005500ff005500ff005500ff000000ff00550055005500550050f050f0f0f0f0f050f050f050f050f05050f0f05050f0f050505050505050504c4c4c4ccccccccc4c4c4c4c4c4c4c4c44cc44cccccccccc44cc44cc44cc44cc4444cccc4444cccc3f3f3f3f000000003f3f0000ffff00003f003f00ff00ff0033ff33ff0000000033ff0000ffff000033ff000033ff000033cc33cccccccccc3333ffff0000000033333333cccccccc333333333333000033333333330033003333333330303030) else (if page < 10 then 0x88cc00cccccccccc88aaaaaaaaaaaaaa88aaaaaa88aaaaaa88aa88aaaaaaaaaa88aa88aa88aa88aa88aa8888aaaaaaaa88aa00aaaaaaaaaa88aa0000ffff000088aa0000aaaaaaaa888c888ccccccccc888a888aaaaaaaaa8888ffff888888888888ff888888ff888888f8f88888f8f88888cccccccccccc8888cccc8888cccc8888cccc888888888888cc888888cc888888c8c88888c8c88888aaaaaaaaaaaa8888aaaa8888aaaa8888aaaa888888888888aa888888aa888888a8a88888a8a8888888aa888888aa88888888ffff888888888888ff88ff8888888888f8f8f8f888888888cccccccc88888888cccc888888888888cc88cc8888888888c8c8c8c888888888aaaaaaaa88888888aaaa888888888888aa88aa8888888888a8a8a8a8888888888a8a8a8a8888888888cc88cc8888888888aa88aa888888888888cccc888888888888aaaa888888888888888888888888808080808888880088888800888880808888808088880000ffff000088880000cccccccc88880000cccc000088880000aaaaaaaa88880000aaaa0000888088808880888088088808880888088800ff008800ff008800cccc8800cccc8800cc008800cc008800aaaa8800aaaa8800aa008800aa00880088888800888888008800ff00ff0088008800cccccccc88008800cc00cc0088008800aaaaaaaa88008800aa00aa008800880088888888 else 0xa0aaa0aaa0aaa0aaa0aaa0a0aaaaaaaaa0aa00aaaaaaaaaaa0aa0000ffff0000a0aa0000f0ff0000a0aa0000aaaaaaaaa0a2a0a2aaaaaaaaa0a2a0a2a2a2a2a2a0a0ffa0a0a0ffa0a0a0f0f0f0f0f0f0a0a0ececa0a0ececa0a0aaaaaaaaaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0aaa0a0a0aaa0a0a0a8a8a0a0a8a8a0a0a2a2a0a0a2a2a0a0a0a0ffffa0a0a0a0a0a0ffa0ffa0a0a0a0a0f0f0f0f0a0a0a0a0f0f0a0a0a0a0a0a0f0a0f0a0a0a0a0a0ececececa0a0a0a0e0e0e0e0a0a0a0a0b0b0b0b0a0a0a0a0aaaaaaaaa0a0a0a0aaaaa0a0a0a0a0a0aaa0aaa0a0a0a0a0a8a8a8a8a0a0a0a0a2a2a2a2a0a0a0a0a0aaa0aaa0a0a0a0a0a0f0f0a0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a000a000a0a0a0a000000000a0a0a000a0a0a000a0a08080a0a08080a0a00000f0f0f0f0a0a00000aaaaaaaaa0a00000aaaa0000a0a00000a0a0a0a0a0a00000a0a00000a080a080a080a0809999cccc9999cccc9999aaaa9999aaaa99999999cccccccc99999999aaaaaaaa8f008f00ff00ff008c8c8c8ccccccccc8c8c8c8c8c8c8c8c8aaa8aaaaaaaaaaa8a8aaaaaaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a8a8a8888aaaaaaaa8a8a0a0aaaaaaaaa8a8a0000ffff00008a8a0000aaaaaaaa8a0a8a0aaaaaaaaa88ff0000ffff000088cccccccccccccc88cc88cccccccccc88cc88cc88cc88cc)) else (if page < 13 then (if page < 12 then 0xaa00aa00aaaaaa00aa00aa00aaa0aaa0aa00aa00aa88aa88aa00aa00aa22aa22aa00aa00aa0aaa0aaa00aa00aa00aaaaaa00aa00aa00aa00aa00aa0000000000aa00a000aa00a000aa008800aa008800a8fca8fca8fca8fca8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8fcfcfcfca8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a8a8a8a8a0a0a0a0a8a8a8a888888888a8a8a0a0a8a8a0a0a8a88888a8a88888a8a0a8a0a8a0a8a0a888a888a888a888a800a800a800a800a6a6a6a6a6a6a6a6a5a5aaaaa5a5aaaaa5a5a5a5f0f0f0f0a5a5a5a5aaaaaaaaa2aea2aea2aea2aea2aaaaaaa2aaaaaaa2aaa2aaaaaaaaaaa2aaa2aaa2aaa2aaa2aaa2aaa2a2a2a2a2aaa2a2a2aaa2a2a2a2ffffa2a2a2a2a2a2f3f3a2a2a2a2a2a2aeaea2a2aeaea2a2aaaaaaaaaaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a2a2a2a2a2aaa2a2a2aaa2a2a2a2aaa2a2a2aaa2a2a2a2aeaeaeaea2a2a2a2aaaaaaaaa2a2a2a2aaaaa2a2a2a2a2a2aaa2aaa2a2a2a2a2a2aaa2aaa2a2a2a2a2a2aaaaa2a2a2a2a2a2a2a2a2a2a2a2a0a0a0a0a2a2a2a0a2a2a2a0a2a2a0a0aaaaaaaaa2a2a0a0a2a2a2a2a2a2a0a0a2a2a0a0a2a0a2a0a2a0a2a0a0ffa0a0ffffa0a0a0ff0000ffff0000a0f0a0f0f0f0f0f0a0f0a0f0a0f0a0f0a0eca0ecececececa0aaaaaaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa0aaa2aaa2aa else 0xaaaa0a0aaaaa0a0aaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa0000ffff0000aaaa0000fafaf0f0aaaa0000eeeeccccaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa2aaaaaaa2aaaaaaa2aaa2aaaaaaaaaaa2aaa2aaa2aaa2aaa2aaa2a2a2a2a2aaa2aaa0aaa2aaa0aaa2a2a2aaa2a2a2aaa0fff0aaa0fff0aaa0aaaaaaa0aaaaaaa0aaa0fff0fff0aaa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0aaa0a0a0a0a0aaa0aa00aaa0aa00aaa0a0a0aaa0a0a0aa8aaaaaaa8aaaaaaa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa88ffccaa88ffccaa88aaaaaa88aaaaaa88aa88ffccffccaa88aa88aaaaaaaaaa88aa88aa88aa88aa88aa88aa00aa00aa88aa8888888888aa88aa00aa88aa00aa888888aa888888aa80aa80aa80aa80aa55aa55ff00ff00aa55aa55aaaaaaaaaa22aaaaaaaaaaaaaa22aaaa2222aaaaaa22aa22aaaaaaaaaa22aa22aa22aa22aa22aa2222222222aa22aa00aaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa0aaaaa0a0aaaaaaa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0aaa00aaaaaaaaaa02aaaaaa02aaaaaa02aa02aaaaaaaaaa00aaaaaaaaaaaaaa00aaaa0000aaaaaa00aa00ffffaa00aa00aa00ff00ff00aa00aa00ff00aa00aa00aa00faf0faf0aa00aa00fa00fa00aa00aa00eecceeccaa00aa00ee00ee00aa00aa00bb00bb00aa00aa00aaaaaaaa) else (if page < 14 then 0xaaaaaaaabbaabbaaaaaaaaaababababaaaaaaaaaafafaaaaaaaaaaaaafaaafaaaaaaaaaaaeaeaeaeaaaaaaaaaaffaaaaaaaaaaaaaafaaafaaaaaaaaaaaeeaaeeaaaaaaaaaaaaffaaaaaaaaaaaaaafafaaaaaaaaaaaaaeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa88aa88aaaaaaaaaa00aa00aaaaaaaaa8a8a8a8aaaaaaaaa2a2a2a2aaaaaaaaa0a0a0a0aaaaaaaa8a8aaaaaaaaaaaaa88aa88aaaaaaaaaa8888aaaaaaaaaaaa88888888aaaaaaaa22aa22aaaaaaaaaa2222aaaaaaaaaaaa22222222aaaaaaaa0a0aaaaaaaaaaaaa0a0a0a0aaaaaaaaa00aa00aaaaaaaaaa0000aaaaaaaaaaaa00000000aaaaaaa8aaaaaaa8aaaaaaa0aaaaaaaaaaaaaaa0aaaaaaa0aaaaaa88aaaaaaaaaaaaaa88aaaaaa88aaaaaa00ffffff00aaaaaa00ffffaa00aaaaaa00ffff0000aaaaaa00aaaaaa00aaaaa8a8aaaaaaaaaaaaa8a8aaaaa8a8aaaaa2a2aaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa0a0fffff0f0aaaaa0a0ffffa0a0aaaaa0a0ffff0000aaaaa0a0aaaaaaaaaaaaa0a0aaaaaaa0aaaaa0a0aaaaa2a2aaaaa0a0aaaaa0a0aaaa8a8aaaaaaaaaaaaa8a8aaaaa8a8aaaaa88aaaaaaaaaaaaaa88aaaaaa88aaaaaa8888ffffccccaaaa8888ffff0000aaaa8888aaaaaaaaaaaa8888aaaa8888aaaa888888888888aaaa8800ffffcc00aaaa8080aaaaaaaaaaaa8080aaaa8080aaaa2222aaaa2222 else 0xaaf0aaf0aaf0aaf0aaeeeeeeaaeeeeeeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaaeeaaeeaaaaaaaaaaeeaaaaaaeeaaaaaaee00cceeeeccccaaeaaaeaaaeaaaeaaaccaacceecceeccaaccaaccccccccccaaccaaccaaccaaccaaaaffffffff0000aaaaffffaaaaffaaaaaaffffaaaafafaaaaaffffaaaaeeeeaaaaffffaaaaaaaaaaaaffffaaaa0000aaaaffffaa00ff00aaaaffffa0a0f0f0aaaaffff8888ccccaaaaffff00000000aaaafffaaaaafffaaaaaffeeaaaaffeeaaaaffaaffaaffaaaaaaffaaaaaaffaaaaaaffaaaaaaaaaaaaaaff00aaaaff00aaaafefeaaaafefeaaaafafafafafafaaaaafafaaaaafafaaaaafafaaaaaaaaaaaaafaaaaaaafaaaaaaaf0f0aaaaf0f0aaaaeeeeeeeeeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeaaaaaaeeaaaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaaafaaaaaaafaaaaaaaeaeaaaaaeaeaaaaaaffaaaaaaaaaaaaaafaaaaaaafaaaaaaaeeaaaaaaeeaaaaaaaaffffffaaaaaaaaaafffffafaaaaaaaaaffffeeeeaaaaaaaaffffaaaaaaaaaaaaffff0000aaaaaaaafffafffaaaaaaaaaffeeffeeaaaaaaaaffaaffaaaaaaaaaaffaaaaaaaaaaaaaaff00ff00aaaaaaaafefefefeaaaaaaaafafafafaaaaaaaaafafaaaaaaaaaaaaafaaafaaaaaaaaaaaf0f0f0f0aaaaaaaaeeeeeeeeaaaaaaaaeeeeaaaaaaaaaaaaeeaaeeaaaaaaaaaaeaeaeaeaaaaaaaaacccccccc)))) else (if page < 22 then (if page < 18 then (if page < 16 then 0xc4c4cccc44444444c4c4c4c444444444c0f0c0f0f0f0f0f0c0f0c0f0c0f0c0f0c0ccc0ccccccccccc0ccc0ccc0ccc0ccc0c0c0c0c0c0c0c0c0c0c0c000000000bbbbbbbbaaaaaaaabbbbbbbb00000000bbaabbaaffaaffaabbaabbaabbaabbaabb88bb88ff00ff00babababafafafafababababababababab8b8b8b8f0f0f0f0b0b0b0b0b0b0b0b0afaff0f0afaff0f0afafafaff0f0f0f0afafafaf00000000afafaaaaffffaaaaafafa0a0ffffa0a0afafa0a0ffff0000afaf0000ffff0000afaaffaaafaaffaaafaaafaaffaaffaaafaaafaaafaaafaaafa0ffa0afa0ffa0afa0ff00afa0ff00afa0afa0ffa0ffa0afa0afa0ff00ff00af00af00ff00ff00aeaeeeeeaeaeeeeeaeaeccccaeaeccccaeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeae0c0ceeeeccccae0ceeccae0ceeccae0cae0ceecceeccacacececacacececacacccccacacccccacacacacececececacacacacccccccccaaffffffaaaaaaaaaaffff00aaffff00aaffaaffff00ff00aaffaaffaaeeaaeeaaffaaff88cc88ccaaffaafaaaffaafaaaffaaeeaaffaaeeaaffaaaaffffaaaaaaffaa00ffffaa00aaffaa00ffff0000aaffa0f0aaffa0f0aaff88ccaaff88ccaaff0000ffff0000aafeaafeaafeaafeaafafafaaafafafaaafaaafafafafafaaafaaafaaafaaafaaafaaaaaaafaaaaaaafa00f0fafaf0f0aaf0aaf0faf0faf0aaf0aaf0f0f0f0f0 else (if page < 17 then 0xccfcccfcccfcccfcccfcccfccccccccccceecceeeeeeeeeecceecceecceecceecceecccceeeeeeeecceecccceeeecccccceecccccceeccccccecccecececececccccffccccccffccccccffccccccccccccccfcfcccccfcfcccccfcfccccccccccccceeeecccceeeeccccececccccececccccccccffffccccccccccccffccffccccccccccfcfcfcfccccccccceeeeeeeecccccccceeeecccccccccccceecceeccccccccccececececcccccccccececececccccccccceecceecccccccccccceeeecccccccccccccccccccccccccccc4444cccccccccccc0000cccccccccc44cc44cccccccccc0ccc0ccccccccccc00cc00ccccccccc4c4c4c4ccccccccc0c0c0c0cccccccc88888888cccccccc4c4c4c4ccccccccc44cc44cccccccccc4444cccccccccccc44444444cccccccc0c0ccccccccccccc0c0c0c0ccccccccc00cc00cccccccccc0000cccccccccccc00000000cccc4c4ccccc4c4ccccc44cccccc44cccccc0c0ccccccccccccc0c0ccccc0c0ccccc00cccccccccccccc00cccccc00cccccc0000cccc0000cccc000000000000ccacccacccacccaccc4ccc4ccc4ccc4ccc4ccc4c4c4c4c4ccc44cccc4444cccccc44cccc44444444cc44cc4444444444cc0ccccc0c0ccccccc0ccc0ccccccccccc0ccc0ccc0ccc0ccc00cccc0000cccccc00cc00cc00cc00cc00cc0000000000c4ccc4cc44cc44ccc4c4cccc4444cccc else 0xeeceeeceeeceeeceeeccffcceeccffcceecceeeeeecceeeeeecceeccffccffcceecceecceeeeeeeeeecceecceecceecceecceecccccccccceeccaa00eeccaa00eeaeeeaeeeaeeeaeeeaaffaaeeaaffaaeeaaeeeeeeaaeeeeeeaaeeaaffaaffaaeeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaacc00ffffcc00eeaacc00eeaacc00eeaaaaaaeeaaaaaaececeeeeececeeeeececececfcfcfcfcececececeeeeeeeeececececececececececececccccccccececccccececccccececa0a0ececa0a0eccceccceccceccceca0eca0eca0eca0eafaeafaeafaeafaeaeeeaeeeaeeeaeeeaeafafaeaeafafaeaeaeeeeeaeaeeeeeaeaeaeafafafafaeaeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeaeaeaaaaaaaaaeaeac0c0eaeac0c0eaeaaaaaeaeaaaaaeac0eac0eac0eac0eaaaeaaaeaaaeaaadfdf0000dfdf0000df00df00df00df00ddddddddccccccccdddddddd00000000ddddccccddddccccdddd0000dddd0000ddccddccddccddccddccddccccccccccdcdcdcdcdcdcdcdcdcdcdcdccccccccccfcfcfcfcccccccccfcfcfcf00000000cfcf0000ffff0000cfcccfcccfcccfcccfcccfcccccccccccf00cf00ff00ff00cf00cf00cf00cf00cecececeeeeeeeeecececececececececececccceeeeeeeecececccceeeecccccececccccececccccecccecceecceeccccffccccffffccccccff0000ffff0000)) else (if page < 20 then (if page < 19 then 0xf0f0f0f0fcf0fcf0f0f0f0f0fafafafaf0f0f0f0fafaf0f0f0f0f0f0faf0faf0f0f0f0f0f4f4f4f4f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0b0b0b0b0f0f0f0f0a0a0a0a0f0f0f0f050f050f0f0f0f0f05050f0f0f0f0f0f050505050f0f0f0f030f030f0f0f0f0f03030f0f0f0f0f0f030303030f0f0f0f000f000f0f0f0f0f00000f0f0f0f0f0f000000000f0f0aaf0f0f0aaf0f0f000f0f0f0f0f0f0f000f0f0f000f0f0f00000f0f00000f0f0000000000000f050f0f05050f0f0f050f05050505050f000f000f000f000f000f00000000000efaacf00ffffcf00eeeeffffeeeeeeeeeeeeffeeeeeeffeeeeeefefeeeeefefeeeeeeeeeffffeeeeeeeeeeeeffeeffeeeeeeeeeefefefefeeeeeeeeeeeeeeeeeeeeeeeeeeaeaeaeaeeeeeeeee0e0e0e0eeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee44444444eeeeeeee00000000eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeeececeeeeeeeeeeeeececeeeeececeeeeeaeaeeeeeaeaeeeee0e0eeeee0e0eeeeccccffffcccceeeeccccffff0000eeeecccceeeeeeeeeeeecccceeeecccceeeecccceeee4444eeeecccccccccccceeeecccc44444444eeeeaaaaffffaaaaeeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeee4444ffff0000eeee0000ffff0000eeee0000eeee0000eeeceeeceeeceeeceeeaeeeaeeeaeeeaeee0eee0eee0eee0 else 0xfafa0000fafa0000faf8faf8faf8faf8faf0faf0faf0faf0faf0faf0f0f0f0f0faeafaeafaeafaeafac8fac8fac8fac8fabafabafabafabafaaaffaafaaaffaafaaafafafaaafafafaaafaaaffaaffaafaaafaaafafafafafaaafaaafaaafaaafaaafaaaf000f000faaaaaaafaaaaaaaf8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f5fff5ff00000000f5ff000055ff0000f5f5ffff00000000f5f5f5f5f0f0f0f0f5f5f5f500000000f5f5f0f0f5f5f0f0f5f50000f5f50000f5f5000055550000f5f0f5f0f5f0f5f0f5f0f5f0f0f0f0f0f500ff005500ff00f500f50055005500f4f4f4f4f4f4f4f4f4f4f4f4f0f0f0f0f4f4f0f0f4f4f0f0f3fff3ff00000000f3ff0000f3ff0000f3f3ffff00000000f3f3f3f3f0f0f0f0f3f3f3f300000000f3f0f3f0f3f0f3f0f3f0f3f0f0f0f0f0f2f2f2f2f2f2f2f2f2f2f0f0f2f2f0f0f2f0f2f0f2f0f2f0f0ff0000ffff0000f0ff0000f0ff0000f0fcf0fcf0fcf0fcf0fcf0fcf0f0f0f0f0fcf0f0fcfcf0f0f0fcf0f0f0fcf0f0f0faf0fafafafafaf0faf0faf0faf0faf0faf0f0fafaf0f0f0faf0f0f0faf0f0f0f4f0f4f4f4f4f4f0f0ffff00000000f0f0fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fcfcf0f0fcfcf0f0fcfcf0f0f0f0f0f0fcf0f0f0fcf0f0f0fafaf0f0fafaf0f0faf0f0f0faf0f0f0f0f0fcfcfcfcf0f0f0f0fcfcf0f0) else (if page < 21 then 0xff00000000000000fefefefefefefefefefefafafefefafafefef0f0fefef0f0fefeeeeefefeeeeefefeccccfefeccccfefe0000fefe0000fefcfefcfefcfefcfefafefafefafefafeeefeeefeeefeeefeaafeaafeaafeaafdfdfdfd00000000fdf0fdf0f0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcfcf0fcf0fcfcfcfcf4f4f4f4fcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc3c3c3c3cfcfcfcfc30303030fcfcfcfc0c0c0c0cfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcf0f0f0f0f0f0fcfcccfcfcfcccfcfcfcccccfcfcccccfcfcccccccccccccfcf4fcf4f4f4f4f4fcf0fcf0fcf0fcf0fcf0fcf0f0f0f0f0fcccfcccfcccfcccfcccfcccccccccccfbfbfafafbfbfafafbfafbfafbfafbfafbaafbaafbaafbaafafafffafafafffafafafefefafafefefafafafafffffafafafafafafffafffafafafafafefefefefafafafafafafafafafafafafaaafaaafafafafafa00fa00fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa50505050fafafafa00000000fafafaf0fafafaf0fafafaaafafafaaafafaf0f0fffff0f0fafaf0f0ffff0000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaeaeafafaeaeafafac8c8fafac8c8fafaaafafafaaafafafaaaaaffffaaaafafaaaaafafafafafafaaaaafafaaaaafafaaaaaaaaaaaaafafa0000ffff0000 else 0xff550000ff550000ff55000055550000ff50ff50ff50ff50ff50ff50ff00ff00ff50ff00ff50ff00ff44ff44ff44ff44ff44ff44ff00ff00ff44ff00ff44ff00ff33ff33ff00ff00ff33ff3300000000ff33ff00ff33ff00ff330000ffff0000ff33000033330000ff30ff30ff30ff30ff30ff30ff00ff00ff30ff00ff30ff00ff22ff22ff22ff22ff22ff00ff22ff00ff20ff20ff20ff20ff0fff00ffffff00ff0fff00ff0fff00ff0f0000ffff0000ff0cff0cff0cff0cff0cff0cff00ff00ff0cff00ff0cff00ff0aff0affaaffaaff0aff0aff0aff0aff0aff00ffaaff00ff0aff00ff0aff00ff00ffff00000000ff00fff0ff00fff0ff00fff0ff00ff00ff00ffccff00ffccff00ffccff00ff00ff00ffaaff00ffaaff00ffa0ff00ffa0ff00ff00ffffff00ff00ff00fff0fff0ff00ff00fff0ff00ff00ff00ffddff00ff00ff00ffccffccff00ff00ffccff00ff00ff00ffaaffaaff00ff00ffaaff00ff00ff00ffa0ffa0ff00ff00ff5fff00ff00ff00ff55ff00ff00ff00ff33ff00ff00ff00ff30ff30ff00ff00ff0fff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00cc00ff00ff00ff00aa00ff00ff00ff005f005f00ff00ff005500ff00ff00ff0055005500ff00ff003300ff00ff00ff0033003300ff00ff000f00ff00ff00ff000000ff00ff00ff0000000000ff000f00ff00ff00ff000000ff000000))) else (if page < 26 then (if page < 24 then (if page < 23 then 0xffeeffeeffaaffaaffeeffccffeeffccffeeffccccccccccffeeffaaffeeffaaffeeff00ffeeff00ffeeeeeeffeeeeeeffeaffeaffeaffeaffddffdd00000000ffccffff00000000ffccffccffccffccffccffccffccff00ffccffccff88ff00ffccffccff00ff00ffccffcceecceeccffccffccccccccccffccffcc33cc33ccffccffcc33003300ffccffcc00000000ffccff00ffccff00ffccff00ff00ff00ffccccccffccccccffccccccccccccccffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ff00ffc0ff00ffb0ffb0ffb0ffb0ffaaffffaaaaaaaaffaaffff00000000ffaaffaaffffffaaffaaffaafffafffaffaaffaaffeeffeeffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa55005500ffaaffaa00000000ffaaffa0ffaaffa0ffaaff00ffffff00ffaaff00ffff0000ffaaff00ffaaff00ffaaff00ff00ff00ffaaff00aaaaff00ffaaff00aaaa0000ffaafaaaffaafaaaffaaeeaaffaaeeaaffaacc88ffaacc88ffaaaaaaffaaaaaaffaa0000ffff0000ffaa0000ffaa0000ffa2ffa2ffa2ffa2ffa2ff00ffa2ff00ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff88ff00ff00ff88ff00ff88ff00ff80ff80ff80ff80ff5fff5f00000000ff5f00005f5f0000ff55ffff00000000ff55ff55ff00ff00ff55ff5500000000ff55ff00ff55ff00 else 0xffff0f00ffff0000ffff0c0cffff0c0cffff0c0cffff0000ffff0c00ffff0c00ffff0a0affffaaaaffff0a00ffffaa00ffff0a00ffff0a00ffff0500ffff0500ffff00f0ffff00f0ffff00f0ffff0000ffff00ccffffccccffff00ccffff00ccffff00ccffff0000ffff00aaffffaaaaffff00a0ffffa0a0ffff00a0ffff00a0ffff0055ffff0000ffff0000ffffff00ffff0000fffff0f0ffff0000ffffccccffff0000ffffcc00ffff0000ffffaaaaffff0000ffffaa00ffff0000ffffa0a0ffff0000ffff0000ffff0000ff000000ffff00005f5f0000ffff000055ff0000ffff000055550000ffff000033ff0000ffff000033330000ffff000000000000fffefffefffefffefffeff00fffeff00fffcfffcfffcfffcfffcfffcff30ff30fffcfffcff00ff00fffcfffcf0f0f0f0fffcfffcccccccccfffcfffc00000000fffafffafffafffafffafffaaaaaaaaafffafff0fafaf0f0fffafff0f0f0f0f0fffaff00fffaff00fff0ffff00000000fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0ffa0ffa0fff0fff0ff30ff30fff0fff0ff00ff00fff0fff0fcf0fcf0fff0fff0faf0faf0fff0fff0f0f0fff0fff0fff0f0f0f0f0fff0fff0aaa0aaa0fff0fff00ff00ff0fff0fff000000000fff0ff30fff0ff30fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0f0f0f0f0ffeeffeeffeeffeeffeeffeeffccffcc) else (if page < 25 then 0xfffffffcffff0000fffffff0fffffff0fffffff0fffff0f0fffffff0ffff0000ffffffeeffffffeeffffffccffff0000ffffff55ffff0000ffffff00ffffff00ffffff00ffff0f00ffffff00ffff0000ffffff00aaaaaa00fffffefefffffefefffffcfcffff0000fffffafafffffafafffff5f5ffff0000fffff0f0fffff0f0fffff0f0ffff0000fffff000ffff0000ffffeeeeffffeeeeffffee00ffffee00ffffddddffff0000ffffccccffffccccffffccccffffcc00ffffccccffff0000ffffcc00ffffcc00ffffcc00ffff0000ffffc0c0ffffc0c0ffffc0c0ffff0000ffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaa0ffffaaa0ffffaa00ffffaa00ffffaa00ffff0000ffffa2a2ffffa2a2ffffa200ffffa200ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa000ffffa000ffff8888ffff8888ffff8888ffff0000ffff8800ffff8800ffff8080ffff8080ffff5d5dffff0000ffff5555ffff4400ffff5555ffff0000ffff5555aaaa0000ffff555500000000ffff5500ffff5500ffff5500ffff0000ffff5050ffff5050ffff5050ffff0000ffff4444ffff4444ffff4400ffff4400ffff3333ffff0000ffff333300000000ffff3300ffff3300ffff3300ffff0000ffff3030ffff3030ffff3030ffff0000ffff2200ffff2200ffff2020ffff2020ffff1111ffff0000ffff0f0fffff0000ffff0f00ffff0f00 else 0xffffffff00ff0022ffffffff00ff0000ffffffff00fc0000ffffffff00fa0000ffffffff00f50000ffffffff00f30000ffffffff00f000f0ffffffff00f000a0ffffffff00f00000ffffffff00ee0000ffffffff00dd0000ffffffff00cf0000ffffffff00cc00ccffffffff00cc0000ffffffff00c00000ffffffff00bb0000ffffffff00af0000ffffffff00aa00aaffffffff00aa00a0ffffffff00aa0022ffffffff00aa0000ffffffff00a200a2ffffffff00a0a0a0ffffffff00a000a0ffffffff00a00000ffffffff00880000ffffffff00800080ffffffff005f0000ffffffff00550000ffffffff003f0000ffffffff00330022ffffffff00222222ffffffff00220022ffffffff00220000ffffffff00200020ffffffff000f0000ffffffff000c0000ffffffff000a0000ffffffff00020002ffffffff0000ff00ffffffff0000f0f0ffffffff0000ee00ffffffff0000ccccffffffff0000cc00ffffffff0000c000ffffffff0000aaaaffffffff0000aaa0ffffffff0000aa22ffffffff0000aa00ffffffff0000a2a2ffffffff0000a0a0ffffffff0000a000ffffffff00008800ffffffff00008080ffffffff00004400ffffffff00002222ffffffff00002200ffffffff00002020ffffffff00000c00ffffffff00000a00ffffffff00000202ffffffff000000a0ffffffff00000022ffffffff00000000)) else (if page < 28 then (if page < 27 then 0xffffffffa020a020ffffffffa000aa00ffffffffa000a0a0ffffffffa000a000ffffffff8c8c0000ffffffff8c008c00ffffffff8a8a0000ffffffff8a008a00ffffffff88ff0000ffffffff88cc0000ffffffff88aa0000ffffffff88888888ffffffff88888800ffffffff88888080ffffffff88880000ffffffff88808880ffffffff8800cc00ffffffff8800aa00ffffffff88008800ffffffff88000000ffffffff80a080a0ffffffff8080a0a0ffffffff80808080ffffffff80800000ffffffff80008000ffffffff55550000ffffffff44444444ffffffff4400cc00ffffffff33330000ffffffff30303030ffffffff22ff2222ffffffff22aa2222ffffffff22aa0000ffffffff22a222a2ffffffff2222aa22ffffffff2222a2a2ffffffff22222222ffffffff22220000ffffffff2200aa00ffffffff22002200ffffffff20a020a0ffffffff2020a0a0ffffffff20202020ffffffff0f0f0000ffffffff0cff0000ffffffff0ccc0000ffffffff0c0c0c0cffffffff0c0c0c00ffffffff0c0c0000ffffffff0c00cc00ffffffff0c000c00ffffffff0aff0000ffffffff0aaa0000ffffffff0a0a0a0affffffff0a0a0a00ffffffff0a0a0202ffffffff0a0a0000ffffffff0a020a02ffffffff0a00aa00ffffffff0a000a00ffffffff08080000ffffffff08000800ffffffff02020202ffffffff00ff00a0 else 0xffffffffaaffaaaaffffffffaaffaa00ffffffffaaff0000ffffffffaaaaaaaaffffffffaaaaaaa0ffffffffaaaaaa22ffffffffaaaaaa00ffffffffaaaaa2a2ffffffffaaaaa0a0ffffffffaaaaa000ffffffffaaaa8800ffffffffaaaa8080ffffffffaaaa2222ffffffffaaaa2200ffffffffaaaa2020ffffffffaaaa0a00ffffffffaaaa0202ffffffffaaaa00a0ffffffffaaaa0022ffffffffaaaa0000ffffffffaaa2aaa2ffffffffaaa0aaa0ffffffffaaa0aa00ffffffffaaa0a0a0ffffffffaa88aa00ffffffffaa880000ffffffffaa80aa80ffffffffaa22aa22ffffffffaa22aa00ffffffffaa20aa20ffffffffaa0aaa00ffffffffaa02aa02ffffffffaa00ee00ffffffffaa00aaa0ffffffffaa00aa22ffffffffaa00aa00ffffffffaa00a000ffffffffaa008800ffffffffaa000000ffffffffa8a8a0a0ffffffffa8a80000ffffffffa8a0a8a0ffffffffa800a800ffffffffa2a2a2a2ffffffffa2a2a0a0ffffffffa2a20000ffffffffa2a0a2a0ffffffffa222a222ffffffffa200a200ffffffffa0ffa0a0ffffffffa0ff0000ffffffffa0f0a0a0ffffffffa0aaa0a0ffffffffa0aa0000ffffffffa0a2a0a2ffffffffa0a0aaa0ffffffffa0a0a2a2ffffffffa0a0a0a0ffffffffa0a0a000ffffffffa0a08080ffffffffa0a02020ffffffffa0a000a0ffffffffa0a00000ffffffffa080a080) else (if page < 29 then 0xffffffffffaaffaaffffffffffa0ffa0ffffffffff00ff00ffffffffff000000fffffffffefe0000fffffffffcfcfcfcfffffffffcfc0000fffffffffcf0fcf0fffffffffaff0000fffffffffafafafafffffffffafaf0f0fffffffffafa0000fffffffffaf0faf0fffffffffaf00000fffffffff0fff0f0fffffffff0ff0000fffffffff0f50000fffffffff0f0f0f0fffffffff0f0c000fffffffff0f0a0a0fffffffff0f0a000fffffffff0f00000fffffffff0a0a0a0fffffffff000f000ffffffffeeeeeeeeffffffffeeeeee00ffffffffeeeeccccffffffffeeee0000ffffffffeecceeccffffffffeeccaa00ffffffffeeaaeeaaffffffffeeaacc00ffffffffee00ee00ffffffffececececffffffffececa0a0ffffffffeca0eca0ffffffffe0e0a0a0ffffffffe0a0e0a0ffffffffccffccccffffffffccffcc00ffffffffccff0000ffffffffccccccccffffffffcccccc00ffffffffccccc000ffffffffcccc8800ffffffffcccc8080ffffffffcccc0c00ffffffffcccc0000ffffffffccc0cc00ffffffffcc88cc00ffffffffcc80cc80ffffffffcc0ccc00ffffffffcc00ee00ffffffffcc00cc00ffffffffcc008800ffffffffc800c800ffffffffc0c0c0c0ffffffffc0c0c000ffffffffc0c08080ffffffffc080c080ffffffffc000cc00ffffffffc000c000ffffffffb0b0a0a0ffffffffae00ae00 else 0xffffffffffffff00fffffffffffff0f0ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0ffffffffffff0000fffffffffff0fff0ffffffffffccffcc))))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x39dd4da1309dba737a9b42613b74c7f726a6c276e9cbecc4ba84edd39cd4da1309dba739b312ea13b74e3f79ed94ba6e98feed54d84edd39dd4da7909dba73bbbd2ea13b74e858e2e5c276e9d0b1c5b2974dd3935e7b6d2e9ba716c6153697b74e598e2e8c276e9d0b1c5cc84edd37e59897509c57742b9353646374e85726bac276e9d0ae4d6b84edd37e54da1309c57742bab53613b74e856c6a6d096e9c2af3dd185edd3855e7ba3141ba742c7136213b74e85726cc4276e9d0ad8d98974dd395638ba348dba70ac4f74699374e858e2e4b7428fcab1c5c984edd3a15bdb312e9ba742ba966213b74e558e272c276e9cab1c4d984edd3a1638b9309c97742c716c65d12ee8572613b742ddd0ad8cba6e85bb955d1ad709dba742bdd6c65d374e858e2d8cba6e9d0b1c5c984edd3a1638975129ba742c7139213b74e5d84eb94276e984eed54d84edd397613a9b0fdba62bb9353613b74e6153684c276e99025d4a484edd3205e7a9b49167640c4f536992cee1579ea6d3259dd0acb4ba84edd3205e7a6512167730a9b2ea13abae616625d4276e9cc2a6ccb84edd315d4da6709dba742c7172a13b74 else 0
  | 5 => if page < 32 then (if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xca779ea6cba84edd3205e7a9b2e9ba282ccb79ea6cba84edd3205e7a9b2ea13ac2d4f79ea6cba84edd3205e7a9b2ea139b1c8179e5d4276e8737205e7a9b2ea1393ac816aaa6cba6e85ab2054d974dd0b514fc8170aa6c276e85ab2054d97509cb513ae855365d4276e85ab205e7b2f2ea138d0c8179ea6d0884e343205e7a9b2ea450d0c8179ecc4ba84e153205e7a9b42613854c8179ea6cba9181532e5e7a9b2ea13b74c8179ea6cba84eccf765e7a9b2ea13b74d1b79ea6cba84edd3205e7a9b2ea13b11cef79ea6cba84edd3205e7a9b2ea13adfcbf79ea6cba84edd3205e7a9b2ea13b50db979ea6cba84edd327de7a9b2ea13b74c8179ea6cba84ea2b425e7a9b2ea13b74c8179ea6cba84ec3f395e7a9b2ea13b74c8179ea6cba84eb63245e7a9b2ea13b74c8179ea6cba84ed1b635e7a9b2ea13b74ca979ea6cba84edd3205e7a9b2e9ba281cd179ea6cba84edd3205e7a9b2ea13ac1cd779ea6cba84edd3205e7a9b2ea13ad3e5d84ea6cba84edd3205e7ae509dba08fda979ea6cba84edd3205e7a9b2ea13922c8179ea6d3284eb3b6a5e7a9b2ea13acebcf58aa6cba84e48b205e7a9b2ea4eacec8150e5d4276e85ab205e7a9b2ea13b74c815365d427678153205e7b2f2ea13854c8179ea6d0884e153205e7a9b2ea45054c8179ea6cba84e4bb205e7a9b2ea13998c815365d4276e85aaf3d4d97509dba0edcfd79ea6cba84edd3205e7a9b2ea13ace else 0xded79ea6cba84edd32054d97509dba112dcb79ea6cba84edd3205e7a9b2ea138f4e2979ea6cba84edd3205e7a9b2e9ba0fbc815365d4276e83ff205e7a9b2ea4d2ced8d79ea6cf184edd3855e7b532ea13b74d698a2a6cba84edd3205e7b312ea138d0c8179ea6d0984e343205e7a9b2ea460d0d2579ea6cba84edd3205e797509dba28fe1579ea6cba84edd334de7a9b2ea13b74c8179ea6cba84e8f345de7a9b2ea13b74c815365d4276e8a0f685e7a9b2ea13b74c8179ea6cba84e6af2054d97509d9e0d0c815365d4276e8352f3d4d97509dda374d6379ea6cba84edd338de7a9b2ea13b74c8179ea6cba84eb87415e7a9b2ea13b74c8179ea6cba84ec4b56de7a9b2ea13b74c9979ea6cba84edd3205e7a9b2ea13a8cd0779ea6cba84edd3205e7a9b2ea13b18c8179ea6cba84e9f3205e7a9b3c613acec8179e5d4276e85d75a5e7a9b3c213b74d6979ec44ba84edd35a618a9b2ea13b74e795365d4276e85ab205e797509dba177df979ec44ba84edd3815e7a9b2ea13b74c8179ea6cba84ec5b255e7a9b2ea13b74c8179ea6cba84e9fb205e7a9b2e9ba14fd5179ea6cba84edd3205e7a9b2ea139ecc8179ea6cba84e7ab205e7a9b2ea139a5d5385aa6cba84edd3205e7b85535ba14fd5379ec34ba84edd37e5e7a9b3c213b74df9862a6cba84edd3205e7b855361393ac8179ea6c272c24eb205e7b555365d13ac8179ea6cba29e4eb54de7a9b2ea13b74) else (if page < 3 then 0xc8179ea6d2c6e8377205e7a9b2ea4c8ddc8179ed6cba6e8377205e7a9b499ba0ddc8179ea6cba90e377205e7a9b2e9ee0ddc8179ea6ce16e83775bde7a9b2ea13b74c815365d4276e86b3305e7a9b2ea13b74c8179ea6cba84ed0b2054d97509de9b74c8179e5d4277a6dd3725e7a9b2ea13b74c8179ea6cba84e63b79de7a9b2ea13b74c815365d4276e848f205e7a9b09dba1dbd5b79ec4cba84edd383e24a9b2ea13b74d63866a6cba84edd3205e7a9b44613998c8179ecfcba84e4bb56e17a9b2ea13b74c8179ea6d22974697205e7a9b4765d1b0c8179ea6cba37c6975e5e7a9b2ea13b74c9779ea6cba84edd3205e7a9b2ea13a8bccd79ea6cba84edd3205e7a9b2ea13ad9d5979ea6cba84edd3205e7a9b2ea139efc8179ea6cba84e6c3205e7b592e9ba0ddc8179ea6d256e837756de7a9b3ba13b74c8179ee1cba84e69758de7b0f2ea13b74c818baa6cba84e6c3205e7a9b2ea430ddc8179e914ba6e87372054d97509cef9b0c8179e80cba84e737205e797509ce69a5c8186ea6cba84e6632054d97509d16198c8179ec5cba84e663205e797509d15198c8179ea6cba8d4663205e7a9b2e908198c8187ea6cba84e4bb2054d97509d1392ec8179ea6cfc84e4bb205e7a9b09d0a12ec8179ea6cba8f24bb205e7a9b2e90712ecc579ea6cba84edd3205e7a9b2ea13b30dd179ea6cba84edd3205e7a9b2ea1390ac8179ea6cba6e83e7205e7a9b09dba10b else 0xc8179ea1cba84e4bb205e7a9b2ea35acec8179ea6d3293ab3b7e62ba9b2ea13b74da979ea6cba93ab3ba1562a9b2ea13922e8553685cba84edd3205e7a9b4c9ba06fe855365d48f84edd3205e7a9b4c9ba05fc8179ea6c277deb3b205caa8709dba16aac55365d4272d448ba154397509dba16aac550e5d4276e85ab205e7a9b2ea46854d3779ea6cba84eb3b205e7a9b2ea02aced5379ea6cba84eb3af3d62a9b2ea1393ac8185aa6cba84eb3b205e7a872e9ba14fc8179ec34ba84eb3b205e7a872ea1393ac8179ea6ce184eb3b225e7a9b2ea13b74c8179ea6cba84ec9b22de7a9b2ea13b74c8179ea6cba84ec9f2ede7a9b2ea13b74c8179ea6cba84ed57205e7a9b2ea13ae6d6779ea6cba84edd3205e7a9b2ea1397bc8179ea6cba84e3c7825e7a9b2ea13b74c8179ea6cba6e844f595e7a9b2ea13b74c8179ea6cba84e42782de7a9b2ea13b74c8179ea6c276e843b585e7a9b2ea13b74c8179ea6cba84e3db835e7a9b2ea13b74c8179ea6cba6e83f72054d97509dba0bfc815365d4276e82eb2054d97509dba0b5de979ea6cba84edd3205e7a9b2ea13907e5379ea6cba84edd3205e7a9b09dba10dc8179ea6cba84e41394613a9b2ea13b74e5179ee8c276e823f6e5e7b132ea13b74e21896a6cba84edd388619a9b2ea13b74e0f79ea6d326e81d7855e7b132ea13b74e55896a6cba84edd376619a9b2ea13b74e0f84ea6cba84edd3205e7b672e9ba0dd)) else (if page < 6 then (if page < 5 then 0xc815365d48e84edd3205e7a9b48213acec815365d4276725ab8b640bcf536992cec8179ea6d3259c1d72062abcf536992cec8179ee8c056e823f7e54d97509d9e075c8179e994486e8a7b205e7ae52ea13acec8179e5d44884eb3b7e54d97509d9e054c815365d42e6781532054d97506d9e054da979ea6d3284eb3b2059a97509d9e054c81856a6cba84eb3b2054d9a72ea13abac7179eb14ba84e48b204ba84ecf10b054bcf696a6cba84e48af3d62a9b2ea1d922bcf58aa6cba81248b205e7a9b2ea172cec8179ea6cba83cb3b204d397509dba1cdbcf696a6cba84e50b205e7a9b2ea19acec8179ea6cba82ab3b275e7a9b2ea13acebcf58aa6cba84e9eb205e7a9b2ea46a96c8179ea6cba918b3b205e7a9b2ea0d9eac8179ea6cd684eb3b205e7975121ba147c8179ec6cba84eb3b205e7975122139e1da579ea6cba84eb3b205e7a9b2ea029e7c8166a5d48f84edd3205e7b4d09dba05fcd579ea6cba84eb3af3d62a9b2ea13abec8179ea6cba878b3b205e7a9b2ea062cec8179ea6cba8f4b3b205e795709dba1cdd9f79ea6cba84eb3af3d62a9b2ea139aec81876a6cba84eb3b205e7a9b2ae139a2c8179ea6cd584eb3b205e7a9b09df7998c8166a5d427720dd3205e7a9b2ea46809c8179ea6cba88cb3b40de7a9b2ea13acebcf5369a4ba84eb3b635e7a9b2ea13acebcf58aa6cba84e4bb2061ca9b2ea13acec8179ea1cba6e851f205e7b192ea13ace else 0xc8153669cba84eb07205e7a9b2ea06b74e61802a6cba84edd33f5e7a9b2ea13922cfd5365d4276e85ab205e7a9b2ea13adcc815365d4276e8aef205e7ab72ea13acec8179ea1cba84eb3b205e7b9353613acec8179ea6c277de4bb205e7b635365d2cec8179ea6cba59c51f2054d9751c613b74c8179ea6cba84e47f20636a9b2ea13acec815365d42759c5ab3f5e7a9b2ea13acebcf58aa6cba84eb3b205e7a9b32213acec815365d427678b3b2062fa9b2ea13acec8153669cba84e663205e7b9b2ea13acec8179ea1cba84e663205e7a9b4ae5d2cec8179ea6cba8366632054d97509dba35bc815365d4276e83fb205e7a9b48e5d2cec8179ea6cba8364bb955e7a9b2ea13acec8179ea6cba80a4bb205e7b892ea13acec815365d4056e85ab2054d97509dba352c8179ea6cba6e83e320600a9b2ea13acec8153669cba84eb3b205e7a9b2ea1facec8179ea6cc184eb3b205e7a9b2c613acec818a2a6cba84eb3b2054d9a72ea1392ec8179ed9cba84eb3b2054d974dd19e147c8179ea6d2c84eb3b2054d97509d9e12ec81666a6cba84edd3205e7a9b31a13acec815365d427678a9b885e7a9b2ea13acec8179ea6cba80a663205e7b5b2ea13acec8179e5d44884e663205e7a9b49a13acec815365d4276786632054da152ea13b74c8179ea6cd284eb3b2054d97509d9e25fc8189ea6cba84eb3b205e7a9b2ae1392ee1579ea6cba84eb3b205e7a9b2e99c947) else (if page < 7 then 0xc8179ecc4ba84eb3b205e79751221392edd979ea6cba84eb3b204ba89109dba16adb979ea6cba84eb3af3d62a9b2ea13998c81882a6cba84eb3b205e7a9b2ae13998c8179ea6cfd84eb3b7e5e7a9b4b613b74c8179ecd4ba84e152f3da5a9b2ea13854c8179ea6cba91ad1af3da5a9b2ea13875c8179ea6d246e8a7b9862aa9b2ea13b74c8179ed34276e823f8b62ba9b2ea13b74c8179ea6d2d6e81d74f5e7a9b2ea13b74c8179ea6cba84eaeb2054d97509cf1054df979ea6cba84e48af3d83a9b2ea13922c8179ea6cba87648b205e7a9b2ea04922c9d79ea6cba84edd3205e7a9b2ea13a7ad8579ea6cba84edd3205e7a9b2ea139e1d9579ea6cba84edd3205e7a9b2ea139e7cd579ea6cba84edd3205e7a9b2ea13abed9f79ea6cba84edd3205e7a9b2ea139aed7179ea6cba84edd3205e7a9b2ea139a2c8179ea6cba6e851fa1640a9b2ea13922c8172aa6c276e85ab2054d97509cb5122bcf5365d4276723b72054d97509d9c8edc8179ecc4ba836153205e7a9b4260d854c8179ea6cba916153205e7a9b4b64e854c8179ea6cba84eb8b205fca9b2ea13acec815366ecba84eb3b46de7a9b2ea13acebcf5366f4ba84eb3b2054d97521613b74c8179ea6cba84eb6b205e7acf2ea13acec8179e5d44884ea2b47de7a9b2ea13acebcf5366e4ba84eb3b205e7a9b2b613b74c8179ea6cba84eb53205e7ad12ea13acec815365d374678a07205fda9b2ea13ace else 0xdb9802a6cba84edd3205e7a9b2ea1f998db979ea6cc884edd3205e7ae52ea13998e2179eadcba84edd320613a9b2ea13998cfd7d2a6cba84edd3205e7a9b385ba270d8d802a6cba84edd3205e7a9b2ea1f92ee3179ea6cba84edd3205e7a9b2e9ba149d8d84ea6cba84edd3205e7a9b2ea1712edd979ea6cc884edd32054d9750b9ba16ae5d84ea6d3284edd34dde7ab72ea13b74c8179ed04c884e1533f5fea9b2ea13b74c8179eb94276e8ab34de00a9b2ea13b74cfd84ea6cba84edd3205e7a9b2ea172cdcfd7aaa6cba84edd3205e7a9b2ea1728ad3779eac4ba84edd3205e7a9b32213ad6e5579eadcba84edd320613a9b2ea1392ee1579ea6cc884edd320600a9b2e9ba147e5579eb94ba84edd320600a9b2ea1392ec815365d4276e85af09d4d97509dba0a5d3779ea6cba84ed177f5e7a9b2ea13b74c8179ea6cba6e86e36e613a9b2ea13b74c8179ea6cba85c663885e7a9b32213b74c8179eadcba84e663885e7ae52ea13b74c81802a6cba84e66309d4d97509dba0a6d3779ea6cba84ed37675e7a9b2ea13b74c8179ea6cba84e4f785613a9b2ea13b74c8179ea6ce16e851f635e7ab72ea13b74c8179ea6ce184e4bb765e7ae52ea13b74c8153670c276e85ab97613ba353613b74c81802d04ba84e1533f60ca9b2ea13b74c8179ea6c3f6e8ab34dde7a9b32213b74d4379ea6cba84edd3205e7a9b2ea13adbc8184ea6cba84eb3b205e7a9b42613ace))) else (if page < 12 then (if page < 10 then (if page < 9 then 0xc8156e5d4276e83b6f3d5b97509dba0edc8156e5d4276e8357205e7b312ea17054c8179ea6d0985c15309d4d97509dc5374c275365d42771edd346e00a9b2ea13b74cfd79ea6cba84ec474dde7adb2ea13b74c81802a6cba84eb7f515e7ae509dba08fc9f79ea6cc884edd3205e7ae52ea13a8ad09802a6cba84edd3205e7a9b2ea1fb0fca979ea6cc884edd320613a9b2e9ba281d3779eb74ba84edd320600a9b2ea13ac1c275365d4276e82baf3d7297509dba0abc81802a6cba84ed7f955e7a9b32213b74c8179eadcba84e4bb855e7ae52ea13b74cfd79ea6cba6e851f95600a9b2ea13b74cfd79ea6cba84e4bb76613a9b2ea13b74cfd79ea6cc884edd2f3d4d97509dd80a5c8179ea6cba85cd1b7cde7ab72ea13b74c8179ea6ce184e66388613a9b2ea13b74c8179ea6ce16e860f88e00a9b2ea13b74cfd79ea6cba84e65b715e7ae52ea13b74c8179ea6cc884e643205e7a9b2ea13934e15802a6cba84edd3205e7a9b321ba147d8d79eb94ba84edd3205e7a9b3221392edd979eadcba84edd32054d99109dba16acfd802a6cba84edd33f5f7a9b2ea13b74c8179ea6ce16e898f4dde7ae52ea13b74cfd7b2a6cba84edd3205e7a9b2ea1727cd9179ea6cc884edd3205e7ae52ea1391ae2b79eadcba84edd34dde7a9b2e9ba147e5584ea6cba84edd34dde7a9b2ea1392ade1802a6cba84edd32057297509dba151e5d79eb94276e823f205e7a9b2ea1399f else 0xc8179ea6cba84ebd32d5e7a9b2ea13b74c8179ea6cba84ecd360de7a9b2ea13b74ccf79ea6cba84edd3205e7a9b2ea13ae0d8d79ea9cba84edd3345f0a9b2ea13b74c8179ea6ce46e8a077e5e7a9b31613b74c8179eb74ba84e1537e5fda9b2ea13b74c8179ea6cba872153205e7b9353613ac1c8179ea6cba894b07205e7a9add162a81c9379ea6cba84edd3205e7a9b2ea13b6dcbd79ea6cba84edd3205e7a9b2ea13b56c8179e5d4516e8c1f205e79c909dba307e5579eaccba84edd32a5e7a9b31213b74c8183ea6cba6e8a074d5e7add2ea13b74c817fea6cba84eb07205e7a9b4b213ad3c8179eb44ba84eb4f2054d974f21ba281c817f6a6cba84eb4f2054d9a92ea13ac1df979ea6cba84eb4f205e7a9b2ea4ead3b075365d4276e848f205e7a9b2ea4626bc8179ea6cd684e9aef3d4d97509dba0abc8179ea6cba84ed7f7cde7a9b2ea13b74e0179ea6cba84edd3205e7a9b2ea13996dc579ea6cba84edd3205e7a9b2ea13990d9179ea6cba84edd3205e7a9b2ea1391ae2b79ea6cba84edd3785e7a9b2ea13b74c815365d4276e85473a5e7a9b2ea13b74c8179ea6cba84eb5b6e5e7ab72ea13b74d3779ea6cba84e66388600a9b2ea13b74cfd79ea6cba84e6636e5e7ae52ea13b74c8179ea6cc884e663205e7a9b2e9ee270d8d79ea6cc884edd3205e7ae52ea1392ee1579eadcba84edd34dde7a9b2ea1392edd9802a6cba84edd34dd4d97509dba16a) else (if page < 11 then 0xc8179eb8c276e823f205e7a9b49a13ad8c8179eb3cba84eb63205e797512613a8ad1f79ea6cba84eb62f3d4d9b92ea13ad8c8179ea6cba90e9c3205e7a9b37dba270ce179ea6cba84edd3205e7a9b2ea13ad2cff79ea6cba84edd3205e7a9b2ea13acadef79ea6cba84edd3665e7a9b2ea13b74c8179ea6cba84e4af78de7a9b2ea13b74c815365d4276e84ff48de7a9b4c9ba075e1579ebd4ba84edd395606a9b2ea13b74c8179ee4c276e8c1f205e7b632e9ba307d3b79ea6cba84edd3205e7a9b2ea13a85ceb79ea6cba84edd3205e7a9b2ea13ad7d7b79ea6cba84edd3205e7a9b2ea13986d7379ea6cba84edd32054d97509dba1c2c8779ea6cba84edd3205e7a9b2ea13b5ed0f79ea6cba84edd3235e7a9b2ea13b74c8179ea6cba84ed2b20de7a9b2ea13b74c8179ea6cba84ed6323de7a9b2ea13b74c8179ea6cba84ed332060aa9b2ea13b46e85902a6cba84ed1b20590a9b2ea13854bcf692a6cba84e153245e7a9b2ea13b45c8179e5d4276e8c6b635e7a9b2fa13b74d2379eb44ba84edd348dfda9b2ea13b74bcf5365d4277a4dd3205e7a9b4ca4e83fdf979ea6d2c84edd38b628a9b2ea13b74c8179ea6d2c6e81d77e628a9b2ea13b74d8d7a2a6cba84edd37e5e7abd2ea13b74c8179ea6cd684e1538b5e7abd2ea13b74c8179eb44ba6e81d77e5e7ad12ea13b74c8179ea6ccb84e153205e7b3d5365d281c9b79ea6cba84edd3215e7a9b2ea13b74 else 0xc8179ea6cba93accee954d97509dba0ffc8179ea6cba6e8a47765eaa9b2ea13b74cef7dea6cba84edd346de7ad32ea13b74dd979ea6cbd84edd3205e7b892ea13b11dd979eaa4ba84edd346dfca9b2ea13b74cef79ea6cba84ec474ade7adb2ea13b74c8179ea6d2084eb7f205fca9b2ea13adfc815366ecba84eb7f46de7a9b2ea13adfbcf5366f4ba84eb7f205e7af32e9ba263c8179ea6ce06e898f3cde7ba309dba08fe21832a6cba84edd3885fea9b2ea13b74c8179ee6c276e8ab3205e7a9b4adba2acd4179ea6cba84edd32054d97509dba2bccf579ea6cba84edd3205e7a9b2ea13addcb379ea6cba84edd3205e7a9b2ea13b60df179ea6cba84edd3205e7a9b2ea13903c81806a6cba84ed43a1640a9b2ea13b50c81536804ba84e1537e5e7a9b2ea13b50bcf6e2a6cba84e413205e7a9b2ea49b50bcf6dea6cba84e40f205e7a9b09dba2e4db979eaacba84edd33cdf6a9b2ea13b74d1f7faa6cba84edd2f3d4d97509df6b74e218aaa6cba84edd3205e7b9b09dba08fdb97a6a6cba84edd3205e7a9b4ae5d28acb779ea6cba84edd3205e7a9b2ea13b35c8179ea6c4f6e8ab36e5e7a9b2f213b74d1f79eb3cba84edd320605a9b2ea13a8ac8179ebe4276e8ab3205e7b9b2ea13b0fc817daa6cba84ec3f2054d97513213a8ae2179eab4ba84edd327de7a9b30a13b74c8179eb8cba84ea2b425f9a9b2ea13b74c8179ea6cba87cc3f9760da9b2ea13b74)) else (if page < 14 then (if page < 13 then 0xc8179ea6c8c424153a1640a9b2ea46054c816625d42715a153205e7a9b2ea44854c8179ecc4ba418153205e7a9b42506054c815365d427246153205e7b8f09dba08fc815365d4276e8d47205e7a9b2ea139a8c8179ee9cba84e153205e7a9b4ea5d054c815365d42731e153205e7a9b4a9ba075c8179eb1cba84e153205e7a9b2ea21854c815365d4276e8d6b205e797509dba1cfc8179eddcba84e153205e7a9b4f213854c815369ccba84e153a154d97509dba16ec818a2a6cba93a153205e7b672ea4e854c8179ea6d2c93a153a1612a9b2ea13b74e855365d4276e8d23a154d97509dba353e855365d4276e8d73205e7a9b2ea4e9b5dd579ea6cba84edd3205e7a9b4ca4ea9edf979ed9cba84edd37e5e7b312ea13854df979ea6d0984e1537e5e7a9b2ea46054c817aacc4ba84e153205eaa9b42613854e5979ea6cba84edd365de7a9b2ea13b74c8179ea6cba84e483775e7a9b2ea13b74c815365d4276e858b855e7ad32ea13b74e557dea6cba84edd32054da1309dc8374c816625d427720dd39ef16bcf2ea25b74c8178ecc4ba84e153205e3a9b42613854c8179ed9cba6e898f205e7a9b4b1ba263d2779ea6cba84edd32054d97509dba286bcf5365d4276e82d3205e7a9b42613809c8179ea6cba91802775de7a9b2ea13b74c8179ea6cba84e3bf205e7a9b34a13b33c8179ea6d3284eccf2054d97521213854dd779ea6cba84eccef3dd2a9b2ea138ef else 0xc8179ee4c276e85bb205e7b632e9ba16ee858dae4d4d84edd3a16eca9b42613b74e85bb2cc4ba84edd32063697509dba16ee85726a6c276e85ab2063897509cb512ee856c6a6cba6e85aba154d974dd0b5147c818e2e4c276e85aba154d97509cb512ee858e25d4276e85ab2063897509de6b74c8179ee8c276e80a32063897509df3b74c8179ee8c276e80bf7e5e7b672e9ba075df979ea6d2c6e81d7205e7a9b4ca2329ec8179ea6d0d84e153205e7a9b2ea4b054d2179ea6cba84edd3205e7a9b2ea13b0ccfb79ea6cba84edd3205e7a9b2ea13ad5c8179ecdcba84e153205e7a9b2ea49054cf179ea6cba84edd3205e7a9b2ea13ac0cf979ea6cba84edd3205e7a9b2ea13ad0cdf79ea6cba84edd3205e7a9b2ea13ad1cf779ea6cba84edd3205e7a9b2ea13adec815365d4276e8d0f205e7a9b2e9ba1bdcc979ea6cba84edd3205e7a9b2ea13b32cad79ea6cba84edd3205e7a9b2e9ba276ced79ea6cba84edd3205e7a9b2ea13acfc8188ecc4ba84e15320623a9b42613854c815365d4276e8d1f205e7a9b2ea1393cdd979ecc4ba84e1532059897509d0c054e85902cc4ba84e153765e7a9b42613854bcf53684c2744a1532054da1309d0c054c8179ecc50984e153205e7a1309d0b854e85902a6d0984e1532054da1309c56854c8179ecc427424153765e7a9b2ea46054bcf5365d48c44a153205e7b312ea46054c8179e5d48c42e153205e7a9b42646054) else (if page < 15 then 0xe85656a6cba84edd37e54d97509d9c0aec7179e5d4276e85d2f3d4d97509dba174e858c2e4d4d84edd3635e7a9b4c9ba075e558fae8d4d84edd3a1640a9b2ea46009df979ecc4ba84e1d720627a9b4c9ba29ee858aae4d4d84edd320627a9b4c9ba08fe858f6e4d4d84edd3955e7ba309dba028e858e2e4d4d84edd3a1638b632ea13b74e85cbaa6d0984edd3855e7ba309dba08fc81872a6d3293aa7b7e5e7b674b213b74c818e2f3db19744bb93de7b672ea4eb74e4f79ed9cba84edd3205e7b672e9ba08be85902a6d0984e0277e5e7a9b42613875e1579ea6d326e8a7ba1735a9b42613b74e1579ee8c276e80bfa1716a9b42613b74c81872a6d326e81d7a16fca9b42613b74df979ed9cba93add000742c716c65d374e858e2a14ba6e851fa15e7b93535ba147c8179ee8d326e81b37e5f3a9b2ea13b74df979ea6cba84ec5b7e5e7a9b34613b74df979ea6cba9181d7205e7a9b4ca3929ee858e2cf4ba84edd3635e7a9b4ca4ea9edf98a2a6d2c84edd320638bcf7261392edf98a2d9cba84edd320638bcf725ba147e4f8a2a6cba84edd3205e7a9b4b1ba08bdf979ea6cba91822b205e7a9b4b24eaede85cbacc4ba84edd320627ba309dba08fe85c5acc4ba84edd3205e7b194c9ba075e85bf2cc4ba84edd395638ba353613b74001d0b1c5c984edd3a1638a852ea1392ee8579ee4d4d84e4bba15e7b635365d12ee858e25d4276e85bba154297509dba16e else 0xc8179ea6cba84e5f76bde7a9b2ea13b74c815365d4276e85fb6ade7a9b2ea13b74c8179ea6cba84e67b7e5e7a9b4c613b74df979edacba84edd32063897509dba0ffe858d6a6cba84edd3205e7a9b4ca4eb2be738c2a6cba84edd38fde7b6d2ea13b74e85902a6cba84ed7f205e7a9b4c9ba2a7e738c2a6d3284edd38fde7b6d2ea4eb74e2d79edacba84edd39ede7b912ea13b74c8179ea6cba93a4137e629a9b2ea13b74df979ea6d2e84edd3a3f16bcf6da5d374e85c5b1854da64dd3a16fca9b2ea13b4de85c5b1c5b6974dd3205e7b6b2e9ba075c8179ea6d316e81d7205e797509dba101c8179eedcba6e81d6f3dd8a9b2e9ba075bcf536993741521d7205e7ba32e9ba0f8c8179eee4ba6e81d7a1640a9b2ea1398ec8179ea6d326de1d79ce2aa9b2ea13b74e498aaa6cba84edd3205e7a9b2ea4eaafe5d8cea6d3284edd39763cba353613b74e2b8aaa6cba84edd3205e7a9b2ea4e8bce85cbb1554da64dd3a16fca9b2ea13b45e85cbb1c5d184edd3205e7b9f09dba08fc8179ee84276e823f205e7a9b09dba100c8179eedc276e823ef3dd8a9b09dba08fc81746a6c276e83fb7e640a9b2ea13923c8179ee8c236e823fa154d97509dba0d3df979ea6d3232a1d7205e7a9b2ea4eacdd1579ea6d326e81d78b5e7b672ea4eb74e558c2e8d4d84edd32063897509dba170c8179ea6d32708a7ba154d97509dba171c8179ea6d3273aa7b7e5e7a9b2ea13b3a)))) else (if page < 24 then (if page < 20 then (if page < 18 then (if page < 17 then 0xdf979ea6cba84e63b7d5e7a9b2ea13b74c815365d4276e83c2f3dc9a9b09dba09fbcf6c6a6cba6e827ef3d9ea9b2ea1389fddf79ea6cba84edd32054d97509dba153bcf5365d4276e820b205e7a9b2ea13accbcf5365d4276e840b9d633a9b2ea13b74c8179ea6cba918caf205e7a9b42613b2bbcf75aa6cba84e1d7205e7a9b4c1ba29edf98cea6cba84edd375621a9b2ea13b74c8179eecd4d9743c6f3dd9a9b2e9ba075e3f79ee8cba84edd3205e7bad5365d0f9c8179ea6cba1f23c7755e7b192ea13b74c8179ee4d4d84e3c78ae27a9b2ea13b74c8179ee4d4d6e83e7755e7a9b3f613b74c8179ee6cba84e3c78ade7b5b2ea13b74c8179ee6cba6e83e788628a9b2ea13b74e4979eddcba84edd32063ca9b2ea138f1df379ea6d0d84edd32063ca9b2e9ba0f9df379ecc4ba84edd37ce20a9b2ea13b74c817365d4276e83ff205c9a9b09dba0ffc81766a6cba6e83ff2054d974dd07f8f9c8175aa6cba84e3ff2054d97509c7f8f1e855365d4276e83ff2056c97509dba0ffc8150e5d4276e83ff205e7a9b4c5ba00bdf779ea6cba84edd3205e7a9b2ea138eec8179ecdcba84ed7f20621a9b2ea13b5fdf779ea6cba84ed7ef3dd8a9b2ea138eebcf5365d4276e82b3205e7a9b2ea13b61d1379ea6cba84edd3205e7a9b2ea13b0bca379ea6cba84edd3205e7a9b2ea13a75dc179ea6cba84edd3205e7a9b2ea13993bcf5365d4276e82db62de7a9b2ea13b74 else 0xc815365d4116e85ab855fca9b2ea13b74c8179ea6cc76e851f635e7adb2ea13b74c8179ea6cc784e4bb2054d98f09dba16ac8189ea6cba84eb7f205e7a9b2b21392ee1579ea6cba84eb7f205e7a9b2e99f147c815365d42767c5ab205e7a9b2e9ba150c8179e5d4277e6dd3205e7a9b2ea1393bc8179ea6c277e0dd32054d97509dba176d8d85aa6cba84edd3205e7b555365d12edd979ea6d0884edd320636a9b2e9ba14fc8179ee4d4d6e853f205e7a9b2e8a792ed53872a6cba84edd3205e7b85535ba147d8d79ec34ba84edd3205e7b855361392edd979ecbcba84edd320636a9b2ea1393ac8179ee4d4d84e4eb205e7a9b09cb092ec8179ed8d4d9744eb205e7a9b2e8a393ac816c6a6cba6e85ab2054d974dd0b5147c81726a6c276e85ab2054d97509cb512ec818a2d9cba6e81d7205b3974dd0fe875c8179ed9cba6e81d7205e7a9b345ba075c818a2a6d2c6e81d72054da58dd0fe875c8179ed9d2c6e81d7205e7a58dd0fc875c8179ed9b743e41d720628a9b2ea4c875c8179ed9cba9321d7205e7a9b4b24c875c8179ed9cba3c81d7205e7a9b4b0f2075e2d79ed9cba84edd2f3d4d97509dba173e2d79ed9cba6e81d78b5e7a9b4b1ba075c8179ed9cba708dd3205e7a9b4b1c2374e4d79ea6cba84edd3205e7a9b2e9ba0f7bcf5365d4276e8283205e7a9b2ea13b31e855365d4276e848f9a638a9b2ea13b74e5979ea6d3284edd37e5e7a9b2ea13904) else (if page < 19 then 0xc815365d4275825ab205e797509dba1cec81726a6c272d44bb2054d84e5a8ae12ec816c6a6cba2d44bb2054d9745a8a392ec815367e4276e85ab2054d97509cd816ac815365d4796e85ab2054d974dd0e096ac815365d427796dd3205c9a8709dba16aac55365d4272d44bb205b1a872e9ba16ac8150e5d3742d451ee4d62a9b09dba16ac8150e5d4272d44bb8554d97509dba16ac8179ea6cba3c851f2054da4109dba16ac815365d4273c85ab2054da5909dba16ac8179ea6c273ea4bb205e797509df2374db95365d4276e85ab204ba84edd0e496ac815367ec276e85ab2054d97509ccc16ac815365d47a6e85ab2054d974dd0db16ac815365d427798dd36354d97509dba16ac8179ea6cba41e4bb2054d9751adba16ac815365d37441e5ab2054d97509dba2c7c8179ea6cba6e845351d4d97509dba16ac8152e5d4276e85ab8854d97509dba16ac8151a5d4276e85ab2054d9a109dba16ac815365d42762e5ab5354d97509dba16ac815325d4276e85ab4a54d97509dba16ac8152a5d4276e85ab7654d97509dba16ac815125d4276e85ab9554d97509dba16ac815225d4276e85ab2054d99909dba16ac815365d4276205ab2054d9750e9ba16ac815365d4076e85ab765e7a9b42613b74c818daa6cba6e851f765e7b312ea13b74c818daa6cba84e4bb63603a9b2ea13b74c8179ea6cba86c4bb2054d9750d9ba16ae5579ea6cba84ec47205e7a9b2ea0892e else 0xc8179ee24ba84e697765e7b0f2ea13b74c818daa6cba84e6c37662fa9b2ea13b74c8179ea6d206e83e774de7b892ea13b74c8179ea6d2084e5f36b5e7a9b48213b74c8179ee24ba84e3cf765e7b692ea13b74c8179ee24ba6e83eb76628a9b2ea13b74c8179ee24276e82cf76636a9b2ea13b74c817125d4276e83ff905e7a9b2ea13b74c8179ea6cba6e854b76627a9b2ea13b74c8179ea6cba8d64bb765e7a9b48213b74dd979ea8cba84edd3205e7a9b48213b33c8179ea6cba6e86df76620a9b2ea13b74c8179ea6cba8d6663765e7a9b3f613b74c8179ee24ba84e663765e7b5b2ea13b74c818daa6cba84e663205e7a9b2ea13957dd9872a6cba84edd3205e7a9b481ba147dd979ec64ba84edd3205e7a9b4821392edd979ee24ba84edd3204ba84edd0fd16ac81536934276e85ab2054d97509cf296ac812ea13b743985ab2054da1309dba16ac8179e5d37439851f2054d975231ba16ac8179e5d4273984bb42de7a9b2ea13b74c8179ea6cba84ea13475e7a9b2ea13b74c8179ea6cba6e89ff4bde7a9b2ea13b74c8179ea6cba84eaf6a6cba84edd0b996ae7b6c6a6cba6e85ab2054d9b109dba16ac815365d4274f85ab205e7a9b2ea139edc815368fc276e85ab2054d97509cf516ac8179e5d4277c6dd3205c9b63535ba16ac81726a6b742d451f205c9b3d5361396ae7b902e4c276e85ab2054d975129ba16ac815365d3745025ab2054d9c909dba16a)) else (if page < 22 then (if page < 21 then 0xc8179ea6d23974697205e7a9b2e8e092ee1585ea6cba84edd3205e7a9b3f1ba147d8d79ec5cba84edd3205e7b93536139b0c8179ed8d4d9746c3205e7a9b2e8d8147d6379ecc4ba84edd32062ea9b2ea1392ee1579ea6cee84edd32061fa9b2e9ba147db379ecc4ba84edd3955e797509dba1cdc8179e91cba6e87372054d97509cef92ec8179e814ba84e7372054d974dd0ef947d8d79ea6cba84e6632061ca9b2ea13998c8179e5d37439251f205e7b192ea13998c8179e5d4273924bb205e7b935361392ec8179ea6c272b84bb205e7b635365d12ec8179ea6cba28e4bb74de7a9b2ea13b74c8179ea6cba84e5f36b5e7a9b2ea13b74c8179ea6cba84e3cf87de7a9b2ea13b74c8179ea6cba6e83eb765e7a9b2ea13998db979ee24ba84edd3205e7a9b48213998d8d79ea6d2084edd3205e7b892ea1392edd979ed9cba84edd3765e7a9b2e9ba147dd979ea6cba84e4bb1b54d97509dba173dd979ea6d0984e02776623a9b42613b74dd979eb1cba84edd320636a9b2ea13a7cdd979ec54ba84edd320636a9b2ea139eadd979ecc50984edd320636b93535ba147d8d79ec64ba8d6dd3765e7a9b2ea46009dd979ecc4ba84e0279ee36b9353613b74dd988ecc4ba84edd320636b935361392ec818daa6c272b84bb20636b635365d12ec818daa6cba28e4bb765e7a9b32e13b74c818daa6cba6e8a07765e7add2ea13b74c818daa6cba84eb07765e7a9b3be13b74 else 0xc8179ea6c273e44bb205e7a9b2e9ef374c818e6a6cba84e4bb2054d97509c97123bcf60ea6cba84e4bb205e7b312ea1392ec8179ea44ba84e4bb205e7a9b3321392ec8179ea6ca884e4bb205e7a9b2ea1d12ec8179ea6cba8144bb6e5e7a9b2ea1392ec817a6a6cba84e4bb205e4a9b2ea1392ec8179ea6cbc84e4bb205e7a9b2da1392ec8179ea6cba8584bb205e7a9b2ea0e92ed8d79ea6cba84e4baf3d85a9b2ea1392ec817c6a6cba84e4bb20584a9b2ea1392ec8179ec64ba84e4bb205e7a932ea1392ec8179ea6cba8704bb205e7a9b2ea0592ec8179ea6d2184e4bb205e7a9b09cfa12ebcf6e2a6cba84e4bb6361ca9b2ea13b74c8179ee4d4d6e851f635e7b192ea13b74c8179ea6cba8a24bb635f0a9b2ea13b74c8179ea6cba8944bb205e7b93535ba281c8179ea6cba7f64bb205e7a9b2e94092ee1582ea6cba84edd3205e7a9b391ba147c8179ea6ce484e4bb205e7a9b09d6292ec8179ed8d4d974b07205e7a9b2e960947c8183ea6cba84e4bb855e7a9b31213b74c817fea6cba6e851f955e7ae12ea13b74c817fea6cba84e4bb20628a9b2ea13ad3c815366a4ba84e4bb205e7b672ea13ad3c815365d3c86e851f2054d97509de412ec8179ea6d0984e9af205e7a9b2ea139a6c8179ea6cba76cdd3205e7a9b2e9ba1bfc8179ea6c27780dd2f3d4d97509dba1ded8d86aa6cba84edd3205e7a9b4765d12ed8d86ea6cba84edd3955e7a9b2ea139a5) else (if page < 23 then 0xc8179ea6cba9184bb20620a9b2ea1392ec815365d42744c4bb205e7a9b3f61392ec8179ea6c274264bb205e7a9b2ea3d12ec8179ea6cba41a4bb2061ca9b2ea1392ec815365d4274564bb205e797509d1492ed4979ea6cba84edd3205e7a9b2e9ba23dd3f79ea6cba84edd32054d97509dba2c6d9b79ea6cba84edd3205e7a9b2ea139e6c8179e5d4272e64baf3d4d97509cb992ee7b902f3dc984e4bb205e7b936c6a692ec8179ed8d4d2b84bb9ee40bcf6c65d12ee7b79ed8d4d9744bb205e7a9b3621392ec8179ea6c277fa4bb20607a9b2ea1392ec815365d44084e4bb205e7a9b2ea139ebc8179ee4d4d28e4bb205e7a9a570a392ec8189aa6cba84e4bb2054d97509d0392ec8179ea6d1f84e4bb205e7a9b09cfb12ec8179ea6cba7aedd32062fa9b2ea1392ec815365d4273ac4bb205e7b9b2ea1392ec8179ea6d2b9744bb205e7a9b2e8db12ec8179ea6c27782dd3955e7a9b2ea1392ebcf5365d4273ba4bb205e7a9b48e5d12ec8179ea6cba3784bb205e7a9b09de1374c8179ea6cba84e3cb20628a9b2ea1392ec815365d4273fa4bb205e7b672ea1392ec8179e5d4273f24bb205e7a9b4b21392ec8179ea6cba7b0dd3885e7a9b2ea1392ebcf5365d4274084bb205e7b5b2ea1392ec8179e5d4273f44bb205e7a9b49a1392ec8179ea6c273e64bb205e7a9b2e9ed374c8179ea6cba84e417855e7a9b2ea1392ebcf5365d4274104bb20627a9b2ea1392e else 0xc8179ee4d4d84eccb955e7a9b4b213b74c8179ec64ba84e3c7875e7b312ea13b74c8179ec64ba6e845795628a9b2ea13b74c8179ea6d236e82f77ae27a9b2ea13b74c816325d4276e845b955eda9b2ea13b74e5583aa6cba84edd3205e7a9b2ea462b3c8179ea6cba84e4c39561ca9b2ea13b74c8179ea6d2c6e851f955eea9b2ea13b74c8179ea6cba918d1b635e7a9b30613b74c8179ec64ba84eccf635e7a9b4b213b74c8179ecc4ba84e2c786de7b192ea13b74c8179ee4d4d84e3d796e27a9b2ea13b74c8179ee4d4d6e83f3205e7a9b2ea460bce55842a6cba84edd3205e7a9b2ea462a6d8d79ea6cc684edd3205e7b312ea13aa6e3b79ea6cba84edd3205e7a9b2ea139c3e55882a6cba84edd3205e7a9b2ea46198e5579ea6cfd84edd3205e7b312ea13998e2179ec64ba84edd320627a9b2ea13998e55822a6cba84edd3205e7a9b2ea46300d8d79ea6cd284edd3205e7b312ea13a5fd8d89ea6cba84edd38e5e7a9b2ea13b74c8179ea6cba6e855795627a9b2ea13b74e5579ea74ba84edd320628a9b2ea13b46e5579ecc4ba84edd3635e7a9b42613b74c8189ea6cba6e851f955e7b192ea13b74c815365d4276e85b7205e7a9b2e9ba1b9d8d882a6cba84edd3205e7a9b48e5d198d8d79ea6cfd84edd3885e7b312ea13b74c818a2a6cba84e66395630a9b45213b74c8189edb4ba6e81d72059897509dba0aec8179ea6d0984e4bb205e7a9b09d0912e))) else (if page < 28 then (if page < 26 then (if page < 25 then 0xc8179ea6d0984eacf855eba9b2ea13b74c8179ea6cba886acf43de7ac72ea13b74c817cea6cba84ec5b26de7ab92ea13b74e2d7cea6cba84edd3205e7b635365d27cc8179ea6cd884e9f3205e7a9b09dfea7cc8181ea6cba84e9f32054d97510213a7cc8179ea6cba6e881760e1ca9b2ea13b74e1579ea6cba84e7ab60de7a9b42613b74c8179ed9cba84e7ab855e7a9b2e9ba147d8379ec54ba84edd320626a9b2ea139eac8179ea6c273ec7ab20626a9b2e9ba147c815365d37440e51f205e7a9b47dba147c8179ea6cba3d451f875e7a9b2ea13b74c8179ea6cba6e84577ade7a9b2ea13b74c815365d4276e845b86de7a9b2ea13b74c8179ea6cba84e3d78d5e7a9b2ea13b74c8179ea6cba6e83f3855e7b312ea13b74d8d79ea6cba6e851f6e5e7b192ea13b74c8179ee4d4d84e66388627a9b2ea13b74e5579ea6cba84e6636e5e7b312ea13b74c8179ea6d2c84e663205e7b312ea13b00c8179ea6cba91897f855e7b192ea13b74e5579ea6cba6e851f205e7b9309dba173bcf726a6c276e85cf8b628b672ea13b74d8d872a6d1484edd39ee40bcf725ba147e5579ebdcba84edd320628a9b2ea13b16d8d79eae4ba84edd3205e7b9353613a7cd8d79ec54ba84edd320627a9b2ea139eae5579ec54ba84edd320628a9b2ea139ead8d872c64ba84edd3205e7b9367aa6947d8d79ec651484edd3205e7b192ea13b5fc8179ea6cba918abf635e7aa52ea13b74 else 0xc8179ed8d4d9744139661ca9b2ea13b74c8179ed9c276e842f855e7b672ea13b74def79ea6d0984edd3205e7b672ea13904e7b79edb5b1974dd38b5e7b672e9ba017c8153684c276e82bb2061ca9b2ea13b5fe15852a6cba84edd3205e7b635365d2b8c81872a6cba84ed43855e7a9b42613b74c815365d4276e85bf855e7abf2ea13b74c8179ea6cba84e66b6e61ca9b2ea13b74c8179ed8d4d974663855e7a9b3f613b74c8179ed9cba84e663855e7b5b2ea13b74e1579ebecba84edd3205e7a9b42613b00e1579eb0cba84edd3205e7a9b42613a5fc8179ea6cba84e5938561ca9b2ea13b74c8179ea6d266e851f205e7a9b2e8f2947bcf5365d3742e651f205e7a9b425ba147c8179ea6cba34651f205e7a9b2e9dcb74db979ea6cba6e851f20620a9b2e9ba147c815365d3743ac51f205e7a9b3f5ba147c8179ea6cba33051f205e7a9b2e9dbb74c81872a6cba6e851f2054d974dd115947c8179ea6cba6e8b0f885e7a9b2e9ba147c8179ea34ba6e851f205e7a9b341ba147c8179ea6cba62e51f205eba9b2e9ba147c815d2a6cba6e851f205e7a9b2fdba147c8179ea6cba62c51f205e7a9b345ba147c8179ea6cba6d251f205e7974dd0e4147c8179ea6cca6e851f205e7a9b2e999147c8181ea6cba6e851f2054d975101ba147c8179ea6cd86e851f205e7a9b2e93e147c815365d4277dcdd3855e7a9b2fe13b74c8179ed9cba84ec5af3d4d9d72ea1398e) else (if page < 27 then 0xc8179ea6cba84ed3f435e7a9b2ea13b74c8179ea6cba84ec375f5e7a9b2ea13b74c8179ea6cba84e6ab5dde7a9b2ea13b74c8179e5d4276e872b2054d97521213a5fc8179ea6cba84ea4384de7a9b2ea13b74c8179ea6cba6e85ff735e7a9b2ea13b74c815365d4276e860357de7a9b2ea13b74c8179ea6cba6e861f5ade7a9b2ea13b74c815365d4276e86cf625e7a9b2ea13b74c8179ea6cba84e4db555e7a9b2ea13b74c8179ea6cba84e4df61de7a9b2ea13b74c8179ea6cba84e7a3205e7a9b2ea13954c8179ea6cba7b6dd34b5e7a9b2ea13b74c8179ea6cba84e9e7605e7a9b2ea13b74c8179ea6cba84e4d7845e7a9b2ea13b74c8179ea6cba6e853381de7a9b2ea13b74c8179ea6cba6e853755de7a9b2ea13b74c8179ea6cba84e4e35fde7a9b2ea13b74c8179ea6cba84e6b75d5e7a9b2ea13b74c8179ea6cba84e693205e7a9b2e9ba110c8179ea6c276e8577205e797509df1374c8179ea6cba6e85232054d97509df5374c815365d4276e85b3205e7a9b2e9eb374e2579ea6cba84edd3205e7a9b2ea13908d0179ea6cba84edd3205e7a9b2ea13ab8c8179ea6d0984ea9b8861ca9b2ea13b74e1579ea6cba84e663205e7a9b42613998e1579edb4ba6e81d6f3db1a9b2e9ba173e1579ead4ba84edd3205e7a9b42613b50e25872a6cba84edd3205e7b635365d108db979ed9cba84edd3205e7a9b426138b7e1579eabcba84edd37be1ca9b2ea13b74 else 0xc8179ea6cba83641376de7a9b2ea13b74c815365d4276e858f30de7a9b2ea13b74c8179ea6cba84ed3af3d4d97509dba0bbbcf76aa6c276e823ef3dcd97509dba0a6c5f5365d4276e829b6e5e7a9b2ea13b4dcdb79ea6cba84edd3205e7a9b2ea13ab9d9379ea6cba84edd3205e7a9b2ea13927bcf5365d4276e830f6dde7a9b2ea13b74c8179ea6cba84e6a79a630a9b2ea13b74e698c2a6d1484edd38b629a9b2ea13b74c818c2a6d1484e2bb205e7bb5535ba075d1179ea6cba84edd3205e7a9b2ea13b13e7bc5af3db6974dd3885f4a9b2ea13b74c8179ea6d266e89c3465e7a9b2ea13b74c815365d4276e89e3205e7a9b2e9ba293e217b2a6cba84edd3395f4a9b2ea13b74ce779edb4ba6e81d7205e7a9b4b9ba075e2d79edb4ba6e805f205e7b612e9ba075c8179ea6cba84eb97205ebb6d2e9ba075ce77cea6cba84edd385de7a9b2ea13b74c8179ea6cba6e846f795e7a9b2ea13b74c815365d4276e84fb285e7a9b2ea13b74c8179ea6cba84ea2320631a9b2ea13998e2f8aaa6cba84edd3205e7b9d09dba08fd3979ea6cba84edd3205e7a9b2ea13a77c815365d4273ac63b205e7a9b2ea2298ec8179ea6cba7fe63b20590a9b2ea13b00c8179ea6cba84ec6768de7a9b2ea13b74c8179ea6cba84e493865e7a9b2ea13b74c8179ea6cba6e85136f5e7a9b2ea13b74c8179ea6cba84e61370de7a9b2ea13b74c8179ea6cba84e62ef3d4d97509dba0a7)) else (if page < 30 then (if page < 29 then 0xc8179ed6cba84eb63205e797512613998c815365d4277d0663205e7a9b2ea139a7c815365d4277d2dd3205e7a9b2ea139b2c8179e5d4277c2dd3205e797509dba1d0c8179ea6cba7aadd32054d97509dba1dcdb986aa6cba84edd3205e7a9b4765d198e2179ea6cef84edd3205e7b512ea13998e2179ed64ba84edd32062fa9b2ea139a5c8179ee6cba84e697205e797509d04998c8179ea6d2b974697205e7a9b2e8e0998db985ea6cba84edd3205e7a9b48a5d198db979ea6cfc84edd3885e7b0f2ea13b74c81892a6cba84e6632062fa9b2ea139b0c815365d427414663205e7b9b2ea139b0c8179ea6d2b9746c3205e7a9b2e8df198db987ea6cba84edd36e5e7a9b3ba13b74c8179ee1cba84e663885e7b4f2ea13b74c818baa6cba84e6632062f97509dba1cdc8179e95cba6e87372054d97509cef998c8179e884ba84e737205e797509ce6998c818bea6cba84e6632054d97509ceb198c8179ee6cba84e663205e797509ce4998c8179ea6d2b974663205e7a9b2e8db198c8179ee6d2b6e823f205e7b9add0db08fc818bee6c276e823f2062fa9b4adba08fc818bea6d1084e23f205e7b9b09ccc08fc8179ea6d2b33023ef3d4d97509dba1dae5d79ee6c276e823ef3d4d97509dba111def79ecdcba84edd32063aa9b09dba10be6979ee9cba84edd32063aa9b2ea13904c815365d42721e413205e7bb553613904c8179ea6c27216413205e7a9b2ea1e904 else 0xc818be5d42739266397640bcf53695998c818bea6cba36c663205e7974724db198e2179ea6cba84e662f3d4d97509d02198c8179ed6cba84e663205e797509cfd198c8179ea6d2684e663205e7a9b09cf9998c8179ea6cba7b2dd3205e7a9b2ea13978bcf53675cba84e663205e7ac92ea13998c8179e71cba84e663205e7a9b2d613998c8179ea6cba888663205e7a9b2ea00198db979ea6cba84e662f3d4d9db2ea13998c817eaa6cba84e6632054d9d92ea13998c8179ea6cfd84e663205e7a9b2da13998c8179ea6cba884663205e7a9b2ea00998c817a2a6cba84e663205e5a9b2ea13998c8179ea9cba84e663205e7a932ea13998c8179ea6cba856663205e7a9b2ea0f198c815365d42744c48af3d4da692ea13998db9882a6cba84edd36e5e7a9b3f613b74e2179ed6cba84edd3205e7a9b2ea27998e2179ea6ccf84edd3205e7ac12ea13998e2179eb3cba84edd3205f6a9b2ea13998c818bea6cba84ea2b2056aa9b2ea13998c8179ee6cba84ea2b205e7a832ea13998c8179ea6cba51c6636e604a9b2ea13b74c8179ea6cba868663205e7af92ea13998e2179ebc4ba84edd320605a9b2ea13998c818bea6cba84ec3f2054d97513213998c8179e5d4277c0663205e7a9b4ae5d30fc8179ea6cba8266636e5f9a9b2ea13b74c8179ea6cba87c6636e5e7a9b30a13b74c8179eb8cba84e6632060da9b2ea13998e2179ea6cba84eb63205e7a9b2ea03198) else (if page < 31 then 0xe0379ea6cba84edd3205e7a9b2ea1392dcd979ea6cba84edd3205e7a9b2ea13acbc8179ea6cba84ea4b2ade7abd2ea13b74db579ea6cba84edd3205e7a9b2ea139a0d5d79ea6cba84edd3205e7a9b2ea139a1d6d79ea6cba84edd3205e797509dba1cbdb179ea6cba84edd3205e7a9b2ea13906e3779ea6cba84edd3205e7a9b09dba10cdcf79ea6cba84edd3205e7a9b2ea13979e2779ea6cba84edd3205e7a9b2ea1397ac5f5365d4276e876af3dcd97509dba1dadb9882d04ba84edd36e5e7b413f613b74db9882a6cfd84edd36e5e7b412ea3d374e218aad6cba84edd3205e7a9b4adba2a7c8179ea6cfd84eccf73de7b5b2ea13b74c8179ea6d2684e5e78862fa9b2ea13b74c8179ea6d266e82e389e20a9b2ea13b74c8179ea6d2b9745eb6e5e7b9b2ea13b74c8179ea6cfd84e3c720620a9b2ea13b5fe6579ea6cfd84edd3205e7b5b2ea13906c8179ed6cba6e82cb95e20a9b2ea13b74c8179ed6c276e8433205e7a9b2ea3d104e4579ea6cba84edd3205e7a9b2e9ba1c4e21882a6cba84edd3885e7a9b3f613b74db979ed6cba84edd3885e7aa12ea13b74c818bea6cba84ed4320620a9b2ea13998c8179ea6c27426663205e7a9b2ea3d198d3379ea6cba84edd3205e7a9b2ea13a87c8179ea6c273b4662f3d4d97509ced198e5d8bea6cba84e6632062fb9b2ea13998e5d902f3dcd84e6632062fa9b4ae5d198c817365d4273ac663205e7b9b4ae5d198 else 0xdbb79ea6cba84edd3205e7a9b2ea13992d8f79ea6cba84edd3205e7a9b2ea13926bdf5365d4276e8296f3d4d97509dba0c0dbf79ea6cba84edd3205e7a9b2e9ba185dc779ea6cba84edd3205e7a9b2ea13991dfb8aaa6cba84edd3205e7b8b09dba08fc8166a5d4276e848f2054397509dba123c81536804ba84ea9b205e7a9b2ea13ae3da779ea6cba84edd3205e7a9b2ea13925))))) else 0
  | 6 => if page < 40 then (if page < 20 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0xc8179ea6cba84edd118640bcf5365d45984edd354de7a9b2ea13b7446200354de7a9b2ea13b74c8179ea6cba84edd09d640bcf5369fcba84e4e800640bcf5365d427275902f3d4d97509dba033c8179ea6cba84edd117e40bcf5365d4276e85ab2054da7f2ea13b742d40032054d97509dba16ac8179ea6cba84edd068640bcf5365d42766e3434dde7a9b2ea13b744ad902f3d4d84efbdba256c8179ea6cba84e8602a640bcf5365d427670153205e7b415365d4270a9902f3d4d97509c94854c8179ea6d1497509c2a640bcf5365d42732a153205e7a9b2ea4ec270a9902f3d4d97509cf1854c8179ea6cba93b09dba6fcbcf5365d4276e8153205e7a9b2ea13b906e9902f3d4d97509dba263c8179ea6cba84edd004e40bcf5365d4276e8137205e7a9b2ea13ba76e9902f3d4d97509dba2acc8179ea6cba84edd00a640bcf5365d4276e811b205e7a9b2ea13bc46e9902f3d4d97509dba307c8179ea6cba84edd011640bcf5365d4276e80ff205e7a9b2ea13bb06e9902f3d4d9750b9ba0540019faf3d4d97509dba640bcf5365d4276e8b3b205e7a9b2ea0db740a8003205e7a9b2ea13acec8179ea6cba84edd00e640bcf5365d4276e80db205e7a9b2ea13b620a979ea6cba84edd10f054bcf5365d4276c48782a640bcf5365d427432153205e7a9b2ea13b370a9902f3d9fa9b2ea13854c8179ea6cba84e4a02a640bcf53688cba84e153205e7a9b2ea139940a9902f3d4d97526a13854c8179ea6cba84e78c1b640bcf5365d49d6e895b7e5e7a9b2ea13b620a9902f3d4d9750b9b1054c8179ea6cba836d882a640bcf5365d4276e895b205e7a9b2ea13b740a8003205e7a9b2ea13b74 else 0xe85902a6cba84edd0685e7a9b2ea13b7445c152f3d4d97509dba22e0eb902f3d4d97509d9c0d0c8179ed054d97509c68640bcf53613b742c023f205e7a9b4525d4271a1902f3d4d974dd0e0075c8179ea6cba93b09c68640bcf5365d4273dc153205e7a9b4525d4276e9902f3d4d97509dba075c8179ea6cba84eea1ba640bcf5365d4276e88df205e7a9b2ea13b74035902f3d4d97509dba0cac8179ea6cba84ef19ba640bcf5365d4276e8917205e7a9b2ea13b7404d902f3d4d97509dba0c7c8179ea6cba84ef51ba640bcf5365d4276e894b205e7a9b2ea13b74057902f3d4d97509dba0c4bcf5365d4276e88b81b640bcf5365d42759c95b205e7a9b2ea13b674ad902f3d4d97509dba231df979ea6cba84edd01b5e7a9b2ea13b7443c0db205e7a9b2ea4ec2706d902f3d4d97517e13b74d6979ea6cba84edd01b640bcf5365d427716dd3205e7a9b2ea13b744e3902f3d4d97509dba006c8179ea6cba84edd01ae40bcf5365d427740dd3205e7a9b2ea13b7456d902f3d4d97509dba011c8179ea6cba84edd01a640bcf5365d427770dd3205e7a9b2ea13b74615902f3d4d97509dba01fc8179ea6cba836dd01b640bcf5365d4276e897f205e7a9b2ea13b6706d902f3d4d9e309dba231d5379ea6cba84edd12b640bcf782a6cba84e4eb20616a9b2ea13b744ad902f3d4da812e9ba14fc81862a6cba84edd12b640bcf536a04ba84e4eb2054da812ea13b742d5902f3d4d97509db10d0c8179ea6d3284edd118e40bcf536794ba84edd320616a9b2ea13b74462003815e7a9b2ea13b74c8179ea6cba84edd0a7e40bcf5369fcba6e853c00640bcf5365d37429f902f3d4d97509dba064) else (if page < 3 then 0xc8179ea6cba84ee05ba640bcf5365d4276e89b3205e7b132ea13b7447fab6f3d4d97509dba256c8179ef054d97509cd2e40c2f5365d4276e895b205e7a9b2ea53427361ac6f3d4d97509dba256c8179ef04ba84edd0e6e40bcf5365d4276c4663205e7a9b2ea13b6225d902f3d4d97509dba065c8179ea6cba8b709dba6adbcf5365d4276e88fc006adbcf5365d4276e9902f3d4d97509dba1a5c8179ea6cba95309cd2800c8179ea6cba84e697205e7a9b2ea37c276e99030bd4d97509dba23f001af2f3d4d97509dba640bcf5365d4276e86c3205e7a9b2ea52c27360003205e7a9b2ea139b0c8179ea6cba84edd01ee40bcf5365d4276e88fb205e7a9b2ea13b741bb902f3d4d975039ba0ddc8179ea6cba8bb09dba640bcf536774276e88fc006b1bcf5365d4276e9902f3d4d97509dba1cdc8179e5d4a984edd0e6800c8179e5d4276e8737205e7a9b2ea13b74331902f3d4d97509d4e198001902f3d4d97509ccc640bcf5365d4276e84bb205e7a9b2ea13af825c003205e7a9b2ea1392ec8179ea6d3697509dba640bcf5365d4276e8057205e7a9b2ea13b7410b902f3d4d97509dba2e8c8179ee054d97509dba640bcf5365d4276e8063205e7a9b2ea13b74139902f3d4d97509dba328c8179edcd4d97509dba640bcf5365d4276e825b205e7a9b2ea13b74637902f3d4d97509dba2eee8588af3d4d97509dba640bcf5365d4276e8daba16b4bcf5365d4276e9902f3d4d97517e13854e7bad2f3d4d97509dba640bcf5368f4ba6e81d7976b4bcf5365d4276e9902f3d4d9e309dba08fd6979ea6cba84edd03ae40bcf53678c276e8a7b5a5e7a9b2ea13b740a9902f3d4d975269ba256 else (if page < 4 then 0xc8179ea6d327f2dd047f42bcf5365d4276e83b6f3de0a9b2ea13b741da002f3d4d97509dba0edc8179edd54d97509dba640bcf5365d4276e825f205e7a9b2ea13b74639902f3d4d97509dba0a3c8179ea6cba84edd1a0e40bcf5365d4276e8c8320638b235365d4276e9902f3dd19e92ea13b74c8179ea6cba84edd1a2e40bcf5365d4276e8293205e7a9b2ea13b74689ca37e5e7a9b2ea13b74c8179ea6cf497509c2a73de0f79ea6cba84edd3205e7b575365d3740ebc1ef3d4d97509dba08fc8179ec4cba84edd17cf07bcf5365d4276e81d7205e7a9b44613b7453dc1f7e5e7a9b2ea13b74c8179ec8d4d97509c2a5e7a9b2ea13b744161d7205e7a9b2ea0b3741bb79ea6cba84edd0f008fc8179ea6cba81edd06ee40bcf6daa6cba6e8377205e7a9b2e9ba14e0eb902f3d4da652e9ba0ddc8179ea6cba84e6bc2a640bcf5365d49d6e8377205e7a9b2ea139390a9902f3d4d97509dba26bc8179ed054d97509dba640bcf5365d4276e89c3205e7a9b2ea13b7411f902f3d4d97509dd1b74c8179ea6cba84edd11d640bcf5365d42777cdd3205e7a9b2ea13b74497902f3d4d97509dba024c8179ea6cba84edd06b640bcf5365d42773cdd3205e7a9b2ea13b7446979ea6cba84edd105865c8179ea6cba84ec552b640bcf5365d42768095b205e7a9b2ea13b7447f902f3d4da652e9ba065c8179ea6d3284edd032e40bcf5367a4ba84edd383de7a9b2ea13b740cb902f3d4d97509dc3374c8179ea6cba84edd13ee40bcf5365d4276e802b205e7a9b2ea13b9a6e9902f3d4d97509dba2b4c8179ea6cba84edd180640bcf53658c276e8197205e7a9b2ea13b7454d902f3d4d975065ba065 else 0xc8179ea6cba84edd132e40bcf5365d4276e88e3205e7a9b2ea13b744e5902f3d4d97509dba240e5579ea6cba84edd12b640bcf5365d4277f24bb20636a9b2ea13b744ad902a6cba84edd12b16ac8179ea6d23974dd12b640bcf5365d4274ac4bb205e7b635365d3744ad902f3d4d974dd12b147c8179ea6cba8b909dba640bcf5365d4276e845f205e7a9b2ea13b741c1902f3d4d97509dba24dc8179ea6cba84edd133640bcf5365d4276e88d720600a9b2ea13b744ad902a6cd397509dba256c8179ea6cba87edd12b640bcf5365d42767295b205e7a9b2ea13b744e9902f3d4d97509dba24cc8179ea6cba8bd09dba640bcf5365d4276e83a7205e7a9b2ea13b8f6e990309d4d97509dba256c815365d4276e8cf12b640bcf5365d42e6e895b205e7a9b2ea13b741c9902f3d4d97509dc5374c8179ea6cba866dd12b6ecbcf5365d4276e895b2054d97509dba3622d590313d4d97509dba256c8179ea6cba94d09c9770abcf5365d4276e895b205e7a9b2e9ba36228f902f3d4d975231ba256c8179ea6cba84edd06fe40bcf5365d42770add3205e7a9b2ea1e3744adb72f3d4d97509dba256c8179ef054d97509ccc640c415365d4276e895b205e7a9b2ea53427331c42f3d4d97509dba256c8179ea6cba84efe4cc640bcf5365d47a6e895b205e7a9b2ea13b741ab902f3d4d97509dc0374c8179ea6cba88cdd12b6c6bcf5365d4276e895b205e7bc15365d42725d9030e54d97509dba256c8179ea6d40974dd0a3e40c515365d4276e895b205e7a9b5025d42725d902f3d4d9751adba256c8179ea6cba84edd076e40bcf6daa6cba93a95b205e7a9b4c9fcb740eb902f3da0a9b2ea4ea56))) else (if page < 7 then (if page < 6 then 0xc8179ea6d3297509d67000c8179ea6d3284eb3b2054d97509dba33c0a80032054d97509d9e054da9902f3d4d97509d67000da979ea6cba84eb3af3d62a9b2ea13b74244002f3d62a9b2ea13922c8179ea6cba84eb3822640bcf5365d4056e89332061ebcf5365d42759d79eb154d97509dba142c8179ea6cba80add037e40bcf5365d427672a5b205e7b1d5365d42759d902f3d4397509dba12cc8179ea6c277dedd02fe40a9b2ea13b74678943205e7a9b35e5d42759d79ea6cba8ab09dba075c8179ea6cba84ece404e40bcf5365d42759ca7b205e7a9b2ea4ec2759c003205e7a9b2ea4eacec8179ea1cba84edd0b5000c8150e5d4276e85ab205e7a9b2ea13b390a9902f3d4d97509d67231c8179ea1cba84edd00e69bbcf5365d4276e8153205e7a9b2ea13b6a0a99031554d97509dba01cc815365d4276e87f00e640bcd5365d4276e80733f5e7a9b2ea13b74039902f3d4d97509dcc374c8179ea6cba84edd1aa640bcf5365d4276e8043205e7a9b2ea13b7402d902f3d4d97509dbd374c8179ea6cba84edd192e40bcf5365d4276e8017205e7a9b2ea13b74027902f3d4d9750b9ba036c8179ea6cba84ed9c2a640bcf5365d4276e839b205e7a9b2ea13b744a9902f3d4d97509dba273c8179ea6cba84edd12367ebcf5365d4276e895b205e7a9b2ae13b744ad902f3d4d9e72ea13b74c8179ea6cba84edd075640bcf5365d4276e8957205e7a9b2ea13b744c9902f3d4d97509dba232c818bea6cba84edd12b640bcf536a04ba84e663205e7a9b4ae5d3744ad902f3d4d97509d2b198c8179ea6cba8b509dba640bcf5365d4276e8607205e7a9b2ea13b741cb902f3d4d97509dba253 else 0xc8179ea6cba84edd02fe40bcf5365d4276e8943205e7a9b2ea13b7453d902f3d4d975275ba2cec81536a1cba84edd0b5640bcf53696c1b6e8153205e7a9b06dba1f10a95365d4276e8cf10f054c815365d4276788782a640bcf5365d41b430153205e7a9b2ea0db380a9902f3da0a9b2ea0d854c8179ea6cba8364a42a640bcf5368a4ba836153205e7a9b2ea0d9950a9902f3d4d9752760d854c8179ea6cba8367902a6fcbcf5365d41b6e8153205e7ad35365d42759d902a6cba84edd19e263c8179ea6cba836dd004e40bcf5365d41b6e8137205febcf5365d42759d902a6cba84edd19e2acc8179ea6cba836dd00a640bcf5365d41b6e811b48e40bcf5365d42759d902f3d4d9b52ea13acec8179ea6cba836dd011640bcf5365d41b6e80ff205e7a9b2ea13bdc59dd0b205e7a9b2ea13acec8179ea6cba80add02a640a9b34e5d4276e81539ee40bcf5365d42759d902f3d4d95709dba075c8153669cba84edd03ae40bcf50e5d4276e8a7b20638bcf5365d42759d902f3d4d95709dba054c8179e5d44884edd02a72ec8179ea6cba84eb3b205e7a9b2ea0db7411f902f3d4d97509d6708fc8179ea6cba95d09d67640c6179ea6cba84eb3b205e7a872ea13b740eb902f3cba89109dba075c815365d4276e8cf14f640bcf746a6cba84eb3b205e7a872ea13b740a9902f3d4d84efbdba054e2d902f3d4d97509d67640bcf5365d4276721d7205e7a9b2ea13ace0eb902f3d4d975015ba29ec818aaf3d4d97509d67640bcf5365d42767223f205e7a9b2ea02b7411f902f3d4d97509e07acec8179edb54d97509d67640a9b2ea13b746781d7205e7a9b09df7b740eb902f3cba89109dba29e) else (if page < 8 then 0xc8179eb94ba84edd047800c8179eb94276e823f20613a9b2ea13b7411fa6ef3d4d97509dba2f9c81802a6d1497509dba640bcf5ca5d4276e81d7205e7ab72ea13b740eb9030054d97509dba29ec81802a6cba93b09dba640bcf5ca5d4276e8153205e7a9b32213b740a9bff3f5e7a9b2ea13b74c8179ea6cba84ef702de7ebcf5365d4276e811f205e7a9b2ea13bb04df9fb11de7a9b2ea13b74c8179ea6cba84ef703ae40bcf5365d4277601d7205e7a9b2ea1737453d9faf3da0a9b2ea13b74c81802a6cba84edd047e40bcf56e5d4276e823f3f5e7a9b2ea13b745f39faf3d4da292ea13b74c81802a6cba84edd03ae40bcf536644276e81d73f5e7a9b2ea13b7453d9faf3d4d97527613b74c81802a6cba84edd02a640bcf5365d43f6e8153205e7a9b4b613b740a9902f3d4d84edd0f8854c8179ea6cba83678c2a640bcf5365d4273c8153205e7a9b4ca13b7459d902f3d4d97509d9e054df9902f3d4d97509d675e7ac55365d4276e8153205e7a9b2ea13ace0a990311de7a9b2ea13acebcf58aa6cba84edd03ae40bcf5365d4056e81d7205e7a9b2ea13b3953d902f3da0a9b2ea13acebcf5365d45584edd047e40bcf53613bef6e823f205e7a9b2ea13af959d902f3d4da292ea13acec8179ea6cba836dd03ade7a9b2ea2ac276e8153205e7a9b2ea2ac270a9902f3d4d9751de13b74da979ea6cba84edd167000da979ea6cba84edd3205e7a9b2ea13b74245902f3d62a9b2ea13922001902f3d4d97509c91640bcf5365d4276e8113205e7a9b4165d4276e9902f3d4d97509dba142c8179ea6cba84edd037e40bcf5365d4276e8a5b205e7a9b2ea47c276e9902f3d4d97509dba12c else (if page < 9 then 0xc8179ea6cba84edd137f3dcfd79ea6cba84edd3205e7a9b2ea173740ebcbb3f5e7a9b2ea13b74cfd79ea6cba84edd047e40bcf536644276e823f205e7ab72ea13b745f3c5b3f5e7a9b2ea13b74cfd79ea6cba84edd03ae40bcf5365d43f6e81d7205e7a9b32213b7453dbf33f5e7a9b2ea13b74cfd79ea6cba84edd02a640bcf5365d4277b815309d4d97509dba21e0a979ea6cba85cdd10f054c8179ea6cba85c8602a640bcf5365d42e670153205e7b415365d42e0a9902f3d4d9750b894854c8179ea6d149750b82a640bcf5365d42e32a153205e7a9b2ea4ec2e0a9a6ef3d4d97509cf1836df979ea6cba85cdd02a640bcf56e5d427720dd320613a9b2ea13b744c7902f3d4d9750b9ba009c8179eadcba84edd026e40bcf5366442774edd320613a9b2ea13b74559902f3d4d9750b9ba014c8179ea6cba85cdd023640bcf5365d43f788dd320613a9b2ea13b7460f902f3d4d9750b9ba022c8179ea6cba85cdd01ff42cfd79ea6cba84edd3205e7a9b2ea13bb00a9a6ef3d4d97509dba036c8179ea6cba85cdd12ff47cfd79ea6cba84edd3205e7a9b2ea17374117a6ef3d4d97509dba075c8179ea6ce184edd14f69bbcf5365d49d84edd320613a9b2ea13b740a9cc73f5e7a9b2ea13b74c8179ea6cc884edd04969bbcf5365d4276e81ff205e7ab72ea13b745ffa6ef3d4da292ea13b74c8179ea6ce184edd03ae40c275365d4276e81d74dde7a9b2ea13b7453d90309d4d97527613b74c8179ea6ce184edd02a640bcf56e5d4276e81538ce7ebcf5365d4276e9902f3d4d9750fdba07acfd79ea6cba84edd036e40bcf536644276e8ac74dde7b415365d4276e800397613a9b2ea13b74 else 0xc8179ea6cba84ededba640bcf5365d42a6e808800648bcf5365d4276e9902f3d4d97509dba346c8179ea6cba842dd011000c8179ea6cba84ed1b205e7a9b2ea13b6e045902f3d4d97d09dba03fd8d79ea6cba84edd02a640bd15365d4276e8153205e5a9b2ea13b740a9902f3d5397509dba054c8179ea4cba84edd02a640bcf5365d42b6e8153205e7a9b2ea0f3740a9902f3d4d97509db2854c8179ea6d3284edd01fe40bcf53613b743e00ff205e7a9b4525d42707f902f3d4d97509cca83fc8179ea6cba93b09c1fe40bcf5365d4273c60ff205e7a9b2ea394276e9b1af3d4d97509dba03f001b1af3d4d97509dba640bcf5365d42770edd3205e8a9b2ea13b7407e0032a5e7a9b2ea13b74c8179ea6cba84edd140e40bcb5365d4276e80fc00640bcf5365d374503902f3d4d97509dba007c8179ea6cba84edd01f640bcf5365d427736dd3205e7aa72ea13b7407e003345e7a9b2ea13b74c8179ea6cba84edd160e40bcf5265d4276e80fc00640bcf5365d427583902f3d4d97509dba012c8179ea6cb484edd01fe40bcf5365d427738dd3205e7a9b2ea15b7407e00335de7a9b2ea13b74c8179ea6cba84edd169e40bcf5365d41e6e80fc00640bcf5365d4275a7902f3d4d97509db283fd3779ea6cba84e78c2a72ebcf5365d427760dd3205e7a9b0fe13b7411f902f3d4da7d2ea13b74c8179ea6cba84edd045e40bcf68ea6cba84edd3205e7a9b2ea13b740ff902f3d4d97509dba092c8179ea6cba84edd17fe40bcf5368ccba84edd3205e7a9b2ea13b740db902f3d4d97509dba07ac8179ea6cba84edd158e40bcf5365d4a384edd3205e7a9b2ea13b7408f902f3d4d97509dba05b)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0xc8179ea6cba84edd134e40bcf5368bcba84edd3205e7a9b2ea13b740d1902f3d4d97509dba078c8179ea6cba84edd152e40bcf706a6cba84edd3205e7a9b2ea13b74137902f3d4d97509dba05ac8179ea6cba84edd135742d2379ea6cba84edd3205e7a9b2ea13bc40a9cf748de7a9b2ea13b74c8179ea6cba86edd03af2ed2379ea6cba84edd3205e7a9b2fa13b7411fa46f3d4d97509dba075c8179ea6cbe84edd14f640bcf5365a42732a153205e7a9b2ea139980a9d0af3d4d97509dba307c8179ea6cba8a709c2a5e7a9b36a5d4276e81d7205e7a9b36a5d3740eb902f3d4d97509d8729ec8179ee8cba84edd183e40bcf5365d42761c153205e7b6d2ea13b7460f902f3d4d975041ba075c8179ed04ba84edd183e40bcf53657c276e823f9ede7a9b2ea13b7460f902f3d4d9752d213998c8179ea6cba8ff09dba640bcf5365d4276e860b205e7a9b2ea3ec276e9902f3d4d97509dba189c8179ea6cba84edd024e40bcf5365d47c84edd3205e7a9b2ea13b7432f902f3d4d97509dba061c8179ea6cba84edd121e40bcf5365d427718dd3205e7a9b2ea13b74017902f3d4d97509dba2f9c8179ea6cb484edd01168abcf5365d4276e8153205e7a9b2ea153740a9902f3d4d975085ba054c8179ea6cba84edb82a640bcf536994276e808b205e7a9b09dba1f0045bf2f3d4d97509dba022bcf5365d4276e887811640bcf5365d427778dd3455e7a9b2ea13b74045902f3d4d97509dbeb74c8179ea6cba84edd1a5e40bcf5365d4276e800f205e7a9b2ea13b74043902f3d4d97509dbe374c8179ea6cba84edd1a4e40bcf5365d4276e8013205e7a9b2ea13b74041902f3d4d97d09dba022 else 0xcdd79ea6cba84edd02a640bcf5365d4296e8153205e7a9b2ea123740a9902f3d4d97509db8854df979ea6cba84edd00a5e7a9b2ea13b7443c053205e7a9b2ea4ec27029902f3d4d97509cf1814c8179ea6cba84ee75ba66ebcf5365d4276e8053205e7a9b2ea13b7e6e9902f3d4d97509dba36bc8179ea6cba84edd000e40bcf5565d4276e8053205e7a9b2ea13b796e9902f3d4d97509dba323c8179ea6cba84ee5dba640bcf5365d4296e80500065fbcf5365d4276e9902f3d4d97509dba350c8179ea6cba848dd00a000c8179ea6cba84ed43205e7a9b2ea13b71029902f3d5597509dba046db979ea6cba84edd02a640bd35365d4276e8153205e4a9b2ea13b740a9902f3d4d97909dba054c8179ea6cb684edd02a640bcf5365d42c6e8153205e7a9b2ea0eb740a9902f3d4d97509db2054c8179ed054d97509c23640bcf5365d42725211b205e7a9b2ea3d4276e9b72f3d4d97509dba046001b72f3d4d97509dba640bcf5365d427706dd3205e9a9b2ea13b7408c00327de7a9b2ea13b74c8179ea6cba84edd145640bc95365d4276e811800640bcf5365d427515902f3d4d97509dba008c8179ea3cba84edd023640bcf5365d427774dd3205e7a9b2f213b7408c003425e7a9b2ea13b74c8179ea6cba84edd187e40bcf5365b4276e811800640bcf5365d42761f902f3d4d97509dd0b74c8179ea6cba858dd023000ce579ea6cba84edd3205e7a9b2ea13b745b1902f3d4d975075ba046001902f3d4d97509d6c640bcf5365d4276c811b205e7a9b2fa139950a9902f3dd197509de2374c8179ec154d97509c2a640bcf5365d4a284edd3205e7a9b2ea13b74085902f3d4d97509dba059) else (if page < 13 then 0xc8179ea6cb584edd02a640bcf5365d42d6e8153205e7a9b2ea0e3740a9902f3d4d97509db1854c8179ea6cba8d709dba6ecbcf5365d4276e8134006ecbcf5365d4276e9902f3d4d97509de1b74c8179ea6cbd84edd026800d1b79ea6cba84edd3205e7a9b2ea13b74623902f3d4d96b09dba04d001902f3d4d97509d88e40bcf5365d42774cdd3205e7aa92ea13b7409a0033bde7a9b2ea13b74c8179ea6cba84edd16fe40bcf5365d41c6e813400640bcf5365d4275bf902f3d4d97509db184dc8179eaacba84e4a42a640c715365d42774edd3205e7a9b3aa5d4270a9902f3dd197509dd3b74c8179eb7d4d97509c2a640bcf5365d4a084edd3205e7a9b2ea13b74077902f3d4d97509dba057c8179ea6cba84edd12f640bcf5365d4276e8297205e7a9b2ea13b740f7902f3d4d97509dba2b2c8179ea6cba84edd02ee40bcf5365d4276e89bba1679bcf5365d4276e9902f3d4d97509dd3854e7b9e6f3d4d97509dba640bcf5365d4316e81d73cde7a9b2ea13b7411f902f3d5597509dba2f9df99e6f3d4d97509dba640bcf5365d4277ca153205e7a8f2ea139290a9902f3d4d97509c97054bcf5365d44d84edd047e40bcf53626c276e823f205e7a9b2ba13b74559902f3dd1a9b09dba2acc8179ea6cba84eafc2a640bcf536994276e8ab3205e7a9b2ea13b3d0a9902f3d4da2909dba2acc8179ea6cba82edd03af2ebcf5365d4276e8ab3205e7a9b51e5d42725d902f3d4da072ea13b74c8179ea6cba84edd0a0640bcf5365d47584edd3205e7a9b2ea13b7423b902f3d4d9751b613b74c8179ea6cba84edd0ace40bcf5365d4276e813b205e7a9b2ea13b886e9902f3d4797509dba014 else (if page < 14 then 0xc8179eb4d4d974dd03ae40bcf5365d4276e82bb205e7a9b2ea13b7412b902f3d4d97509dba306c8179ea6cba84edd03ee40bcf5365d4276e8aaf205e7a9b2ea13b740c1902f3d4d97509dba262e85962f3d4d97509dba640bcf5365d42772015352de7a9b2ea13b740eb79ea6cba8ad09dba075c8179ea6cd784edd14f640bcf53613bf16e8a7b8b658bcf5365d4276e9902f3d4d97512dba075df9962f3d4d97509dba640bcf5365d4277e2153205e3a9b2ea13b380a979ea6cba84efd9ba075c8179ea6cba82cdd131e40bcf6daa6cba6e898f205e7a9b2e9fd3740eb902f3d4da652e9ba263c8179ea6cba84ea242a640bcf5365d49d6e898f205e7a9b46a5d4276e9902f3d4d97509dba0dbc8179ea6cf797509dba640bcf5365d4276e8367205e7a9b2ea324276e9902f3d4d97509dba0cbc8178ea6cba84edd004e52bcf5365d4276e8153205e7a9b2ea143740a9902f3d4d975099ba054c8179ea6cba84edcc2a6fcbcf5365d4276e8026f3d4d97509dba21e013902f3d4d97509d0c009c8179ea6cba84ece004e40bcf5368a4ba84e027205e7a9b2ea13995013902f3d4d97527613809c8179ea6cba84e78c04e40bcf5365d427708dd3295e7a9b2ea13b74013902f554d97509dba009c8179ea6cba84edddba640bcf5365d4276e8bcf205e7a9b2ea13b956e9902f3d4d97509dba32ec8179ea6cba84ee59ba640bcf5365d4286e80240065cbcf5365d4276e9902f3d4d97509dba333c8179ea6cba84cdd004800c8179ea6cba84eccf205e7a9b2ea13b73013902f554d97509dba04ddd979ea6cba84edd02a640bcf5525d4276e8153205e7a912ea13b740a9902f3d4d97b09dba054 else 0xc8179ea6cba84e7dc2a73dbcf5365d427714dd3205e7a9b43e5d4270a979ea6ce997509dba054c8179ea6d3284e6542a640a9b2ea13a182d0153455e7a9b2ea139950a9902f3d4d9d32ea13854bcf53674cba84e6542a640bcf53673cba84e153205e7a9b2ea1398c0a9902f3d65a9b2ea13854c8179ea6cba6e86d005e40bcf5368a42732a153205e7a9b2ea234270a9902f3d4d974dd0db075bcf5365d4276e88b42a640c395365d4276e81532054d97509dba22b0a9902f3d8c97509dba054c8179e5d4276e88a42a640bcf5365d46b6e8153205e7a9b2e9ba20f0a9902f3d4d97525e13854bcf5365d4276e887805e40bcf5365d48384e153205e7b835365d4270a9902f3d4d97509cab054c8179ea6d3e97509c2a640bcf5365d42738a153205e7a9b2ea4e9fe0a9902f3d4d9752760b054c818aaf3d4d9752742a640bcf5365d49d1b4153205e7b6d5365d49d0a9902f3d4d975274a2854c8179ea6d329752742a640bcf5365d49d368153a15e7a9b2ea13b8f6e9902f3d4d97526213854c8179ea6cba84edd04fe40bcf5365d4276e8cafa16fcbcf5365d4276e9cf77e5e7a9b2ea13b74c8179ea6d32974dd03af2edf979ea6cba84edd3205e7a9b4ca13b7411fbf2f3d4d97509dba075c8179ea6d3284edd14f6fcbcf5365d42743c1537e5e7a9b2ea13a180a9bf2f3d4d97509d9c054df979ed054d97509c2a6fcbcf5365d4272521537e5e7a9b4525d4270a9bf2f3d4d97509cca854df979ea6cba93b09c2a6fcbcf5365d4273c6153205eaa9b2ea13b380a9d0af3d4d97509dc8374c8179ea6cba8ad09c2a640c715365d427720dd3205e7a9b35e5d4270a99031854d97509dc8374))) else (if page < 17 then (if page < 16 then 0xbcf5365d4276e88903ae40bcf5365d42743415308de7a9b2ea13b740a990311d4d97509d9c054bcf5365d4276e88942a640bcf6625d4276e8153205e797509dba2170a9902f3d4da1309dba054c8179ea6c276e88482a640bcf5365d48c6e8153205e7a9b2e9ba20c0a9d0b2054d97509d9c054c815365d4276702b42a6ecbcf5365d427670153205e7a9b2ea13a250a979ea6cba84ece112854c815365d4276708602a640bcf662a6cba84e153205e7b312ea13b380a8003205e7b312ea13854c8179e5d42767085c2a640bcf53684cba84e153205e7a9b42613b380a8003205e7a9b42613854c8179ea6c276708482a640bcf5365d48c84e153205e7a9b2ea463380a8003205e7a9b2ea46054c8179ea6cba6708302a640bcf672a6cba84e153205e7b1f5365d4270a99031c5e7b412ea13854c8179ed04ba84e39c2a640bcf5365d4273a2153205e7ba36825d4270a9902f3da097509ce3854c8179ea6cba84e7ec2a72ebcf5365d42770add3205e7b3b5365d4270a979ec0d4d97509dba054cdd79ea6cba84e4a42a640bcf606a6cba84e152f3d81a9b2ea139290a9902f3d7fa9b2ea13854c8179ed04ba84e4a42a640bcf53666cba84e153205e7a9b2ea1e4270a9902f3d4d84edd0ae08fbcf5365d4276e88a02a640c415365d4276e81532054d97509dba2260a9902f3d4d9fb09dba054c8179ea6c276e884c2a640bcf5365d47a6e8153205e7a9b2e9ba20d0a9902f3d4da1d2ea13854c8179e5d4276e871c0be40bcf5367fcba84e153205e7baf5365d4270a9902f3d4d97509cb2854c818c2f3d4da2909c2a640bcf5368a4271c2153205e7ba35368a4270a9902f3d4da2909cad054 else 0xc8179ea6cba84e87c2a640bcf5365d4276e85bb205e7a9b2ea13b840a99031454d97509dba054c815365d4276e87f42a640bcf6ce5d4276e8153205e797509dba1f90a9902f3d4da5909dba054c8179ea6c276e87c82a640bcf5365d49984e153205e7a9b2ea13baf6e9902f3d4d97509d0d854c8179ea6cba84ed142a640bcf5365d4276e8d23205e7a9b2ea13b740a3902f3d4d97509dba133c8179ea6cba84edd01be40bcf5365d42773a153205e7a9b2ea13b400a9902f3d4d97509dba0dcc8179ea6cba84edd028710bcf5365d4276e8152f3d4d97509dba2040a9902f3dad97509dba054c8179e5d4276e87e82a640bcf536934276e8153205e7a9b09dba1f30a9902f3d4d97521e13854c8179ea6cba84e7942a640bcf5365d4276e8c23205e7a9b2ea13b74059902f3d4d97509dba353c8179ea6cba84edd025e40bcf5365d4277e8153205e7a9b2ea13a7b0a9902f3d4d97509dba14bc8179ea6cba84edd01ce40bcf5365d427778153205e7a9b2ea13b150a9902f3d4d97509dba146c8179ea6cba84edd02570abcf5365d4276e8152f3d4d97509dba2080a990313d4d97509dba054c815365d4276e88182a640bcf536904276e8153205e7a9b09dba1f50a9902f3d4d9751ca13854c8179ea6cba84e7a42a640bcf5365d4276e8adf205e7a9b2ea13b7405b902f3d4d97509dba35cc8179ea6cba84edd022e40bcf5365d4276e857f205e7a9b2ea13b7436b902f3d4d97509d11854bcf5365d4276e888c2a640c715365d42743015320630a9b2ea13a180a9902a6cba84e860ea854c8179ea6cba84eeac2a640bcf602a6cba84e153205e7a9b3a25d4270a9902f3d4d97515213854) else (if page < 18 then 0xc8179ee8cba84edd036742c81662a6cba84edd3205e7b194ca13b7453c0037e628a9b2ea13b74e8579ea6d4297509c97640c7179e5d4276e85bb205e7a852ea13b742dd902f3d4da651adba29ee8579ea6cba84edd0b5742a9b50a5d4276e85a800742a9b2ea13b742d5bf2f3d4d975059ba075c8179ea6cba84e8882a640bcf5365d427442153205e7a9b2ea13b742bd902f3d4d97509dc6054c818daa6cba84edd02a640a9b2ea13b742d4153205e7b9353613b740a9902f3d4d84edd0ae054c8179ed8d4d974dd02a640bcf5365d37428e153205e7b3d5365d4270a9902f3d4d97509dd2b74c8179ea6cba84e8742a640bcf5365d4276b2153205e7a9b2ea13b745e1902f3d4d97509dba053c8179ea6cba84edd074640bcf5365d427440153205e7a9b2ea13b74375902f3d4d97509dc4054c818bea6cba84edd02a640a9b2ea13b743ac153205e7b9b2ea13b740a9902f3cba84edd0e4854c8179ea6d2b974dd02a640bcf5365d37436c153205e7a9b4425d4270a9902f3d4d97509ddfb74c8179ea6cba84e8702a640bcf5365d42769a153205e7a9b2ea13b74645902f3d4d97509dba052c8179ea6cba84edd0cee40bcf5365d4276e8103205e7a9b2ea13ba20a9902f3d4d97509d9f854c8179ea6cba84edd071640bcf5365d4276e813f955e7a9b2ea13b740a979ea6cba84edd0ee854c8179ee24ba84edd02a640bcf2ea13b74398153205e7a9b48e5d3740a9902f3d4d974dd0de054c8179ea6d0297509c2a640bcf5365d427346153205e7a9b2ea13b7455d902f3d4d97509dba023c8179ea6cba84edd196e40bcf5365d4276e8133205e7a9b2ea13b74377902f3d4d97509dba15b else (if page < 19 then 0xc8179ee8d4d97509ccc710bcf5365d49d84edd3205e7a9b4ca5d427331bf36e5e7a9b2ea13b74df9902f3d4d97509ccc716bcf5365d4276e822f205e7a9b4525d4275ddbf2f3d4d97509dba0aec8179ea6cba93b09db5640bcf5365d3743fe1d7205e7a9b2ea0fb740ebd0b295e7a9b2ea13b74c8179ea6cba93b09d2fefcbcf5365d3743fe1d6f3d4d97509dba1ff0ebbf2f3d4d97507dba075df979edb54d974dd03aefcbcf5365d37428a1d77e5e7a9b4ca5d3740ebbf2f3d4d97509d0c075df979ed054d97509c3aefcbcf5365d4272521d77e5e7a9b4525d4270eb902f3d4da64dd0ca875e8579ea6cba84ee31ba6fcbcf5365d4276e802f20638a9b2ea13ba26e9bf2f3d4d97509dba017c8179ee8cba84eef1ba6fcbcf5365d4277081d7205e7a9b2ea4eb744bfbf2f3d4d97509db3875e4f79ea6cba84edd03aefcbcf5365d49d84e1d7205e7a9b4524ec2753db1af3d4d97527613b74e85902f3d4d97509c97640c395365d49d84edd320638bcf5365d37428f9031454d97527613b74c818e2f3d4d97509c976fcdd979ea6cba84edd320638a9b2ea13b742d5c5b205e7a9b4c9ba29ec8179ea6d326e8a783ae40c5579ea6d326e8a7b205e7ba309e01b7411fbf2f3d4d97509d9c075c8179ea6d32806dd14f640bcf5369f49d84ea7b205e7a9b4fa13b7453d902f3d4d975059ba08be85902a6cba84ece004e40bcf5369949d84ea7b205e7a9b4ca4eb7453c003205e7a9b4ca4ea9ec8179ee8cba8e509dba6c6bcf536994276e8a78006fcbcf536964276e99031c5e7a852ea1392ec818e2a6d0297509dba640c39536994276e8a78006fcbcf6ce5d4276e9d0af3d4da852e9ba147 else 0xc8179ea6d29974dd03aefcbcf5365d4276e8c037e5e7a9b2ea13995045902f3d4da64dd03a865c8179ea6d32974e11ba640c4f5365d49d84edd3205e7ba35365d42725dc2af3d4d97527613b74c8179ee8d4d974dd0a3efcc8179ea6cba84e4bb765e7a9b2ea4ec276e9902e8d4d97509dba16ae5d79ea6cba84edd04fe40bcf682a6cba84ecaf7e5e7a9b2ea13b7414b902f3d4d97527613b45e5db1af3d4d97509dba6fcd8d79ea6cba84edd3a36fcbcf5365d4276e9902f3d4d975276138a5e8bcbaf3d4d97509dba640bcf682a6cba84e22fa0efcbcf5365d4276e9902f3dd197509dba0a5e5d79ea6d3284edd04fe40c555365d4276e802f205e7ba36825d427657902f3da097509dba32be85cbaf3d4da6509dba742c815365d4276e8d17976fcbcf536994276e9bf2f3da0a9b2ea138a5c818aaf3d4d975275a2e40bcf5365d49d6e8d17a172ec555365d4276e9d0b8b62aa9b2ea13b74e5d902f3d4da64dd03af42df98aaa6cba84edd3205e7a9b09dba1d811f902f3d4d96f09dba08fe85956f3d4d97509dba640bcf5365d49d84e9af2054d97509dba1fc017902f3d4da4f09dba08fc8179eeed4d84edd047e40bcf5365d42725222f9ee40bcf74613b7411f902f3d4da64dd047875c8179ee8da084edd047e40bcf536993741b423f20638bcf74613b7411fcbaf3d4da6509dba08fc8179ee8d4d84ee21ba640bcf536994ba6e802f205e7a9b4ca5d39d6e9902f3dd197509ddfb74c8179ea6d2884edd047efcbcf5365d4276e8a9b7e5e7a9b2ea13929029902f3d4da64dd047865e85902a6cba84edd135edcbcf5365d49d84edd3a1640bcf5365d4273319031054d97527613b74))))) else (if page < 30 then (if page < 25 then (if page < 22 then (if page < 21 then 0xc8179ea6cba84edd00ce40bcf5365d4276e81d3205e7a9b2ea13bc76e9902f3d4d97509dba2fac8179ea6cba84edd013e40bcf5369f4ba84ebbb205e7a9b2ea40c276e9902f3d4d97509dba0b1c8179ea6d0c97509dba640bcf5365d4276e82cb205e7a9b2ea13b740e3902f3d4d97509dba29bc8179ea6d3597509dba640bcf5365d4276e82cf205e7a9b2ea13b74109902f3d4d97509dba2e7c8179ea6cba8d6dd1776fcbcf5365d4276e822f205e7a9b2ea4ec275dd902f3dd1a9b09dba09fc8179ea6d3284edd195e40bcf536994ba6e822f7e5e7a9b2ea4ec27117902f3d4da652ea4eaeec8179ea6cba93add177742df98e2a6cba84edd38b5e7a9b2ea13b7413f902f3d4da292ea13b2bdf979ea6cba84edd04de40bcf5365d49d84ec839eedcbcf5365d4276e9d1f7e5e7a9b2ea13b74c818e2a6cba84edd057716bcf536994ba6e827f8b5e7a9b2ea13b74017902f3dd1a9b45213b2bc8179ea6d1484edd195e40bcf746a6c276e826f9eefcbcf7465d4276e9d0b2054d97509dba34de8fc5af3d4d97509dba640bcf6daa6cba6e822f9eefcbcf6da5d4276e99031c5e7b6d2e9ba075df979ea6d1497509c4de40bcf6daa6cba93ac83205e7a9b2ea4eb74641d0b8b630a9b2ea13b74e85bf31854d97509dba640bcf5365d3744041d7205e7a9b2ea12b740ebd0b2bde7a9b2ea13b74c8179ea6cba93add1385e7a9b2ea13b743fc02f205e7a9b49e5d3740eb902f3ddda9b2e9ba075c8179ea6cba6e859c3ae40c6179ea6d326e81d7205e7a9b4c9ba0e10eb902f3dd1a9b4c9ba075e2d79ea6d32974dd03ae40bcf7465d427718dd3a1640a9b2ea13b745679031c54d97509dd2b74 else 0xbcf536a14ba84edd04fefcbcf5365d4276e827f9d5e7a9b2ea13b7413f902f3d4d97509dc7374c8179ea6cba84edd133e40bcf5365d4276e803b205e7a9b2ea13ba46e9902f3d4d97509dba29fc8179ea6cba84ee25ba640bcf5365d4276e895f205e7baf5365d4276579031654d97527613b74c8179ee8d4d97509c78f1fbcf5365d49d84edd3205e7ba35365d3741f3c92f3d4d97527613b74c81746a6cba84edd07fde7b8d5365d4276e81d7205e7a9b2ea13b5953d902f3d4d97527613b2bc8179ea6cba92b09dba6eabcf5365d4276e8cac006eabcf5365d4276e9902f3d4d97509dba0f1c8179ee354d97509c78800c8179ea6cba84e3c7205e7a9b4365d4276e990310d4d97509dba32b001c56f3d4d97509dba640bcf5365d4276e83e7205e7b8d5365d3741f2003205e7a9b2e9ba0f9c8179ec64ba84edd195e40bcf5367ec276e8caf205e7a9b2ea414276e9902f3d4d975209ba32b001be6f3d4d97509dba640bcf5365d4276e83ff205c6a9b2ea13b741fe0032054d97509dba0ffc8179ea6cba84add005de7a9b4ca5d4276e82af205e7ba35365d4276bf9031a5e7a9b2ea13b74c8179ea6cba84edd001640bcf5365d4276e82aef3ddda9b2ea13b74156002f3d4d97509dba0abc8179ea6cba84edd1afe40c7d79ea6cba84ed7c00640bcf5365d4276bf902f3ddfa9b2ea13b74c8179ea6cba84edd050e40bcf5365d4276e8cdba2de7a9b2ea13b7415d9030154d97527613b74c8179ee8d4d97509d99e40bcf5365d42744402793de7a9b2ea13b74117902f3d4d97509dc9b74c8179ea6cba84edd12c640bcf5365d4276e8033205e7a9b2ea13baa6e9902f3d4d97509dba2a0) else (if page < 23 then 0xc8179ea6cba9330583ae40bcf5365d4163c81d7205e7a9b45213b7453dc5af3d4d975059ba075c8179ea6c5084edd14f640bcf5365d49484edd3205e7a9b2ea13b7401f902f3d4d97526e13b74e8579ea6cba84edd052efcc8179ea6cba84ed17205e7a9b2ea4f4276e9902f3d4d97509dba2f5e859baf3d4d97509dba640bcf5365d49d84ea9b2062fa9b2ea4ec276e99031c5e7a9b2ea13998c8179ea6d3897509dba640bcf5365d4276e871ba16dcbcf5365d4276e9902f3d4d97527613998c8179ea6cba84edd006e40bcf5365d49084edd37e5e7a9b2ea13b7414d902f3d4d97527613b4dc8179ea6cba93f09dba640bcf5365d4276e8bcb7e657bcf5365d4276e9902f3d4da652e9ba270e859cef3d4d97509dba640bcf5365d49d84eacf205e7a9b2ea50c276e9902f3d4d97509dba32fe85a2af3d4d97509dba640bcf5365d49d84ec03955e7a9b2ea4ec276e9902f3d4da652ea1392ec8179ea6d3b97509dba640bcf5365d4276e8563856fcbcf5365d4276e9902f3d4d975275ba147e85b1af3d4d97509dba640bcf5365d49d84e4bb20636a9b2ea4ec276e9902a6cba93b09dba16ac8179ea6cba90109dba640bcf5365d4276e82a3205e7a9b2ea13b746af9031dde7a9b2ea13b74c8179ea6cba84edd055640bcf5365d4276e8d77205e7a9b2ea13b7415f902f3d4d97509dba370e7f79ea6cba84edd052f36bcf5365d4276e826f2ade7a9b2ea13b74017902f654d97509dba00bc8179ea6cba84edd9ba640bcf5365d4276e8bc7205e7a9b2ea13b946e9902f3d4d97509dba32cc8179ea6cba84edd5ba640bcf5365d4276e8bbf205e7a9b2e9ba20201779ea6cba84edd054875 else (if page < 24 then 0xc8179e5d4276e873047e40a9b2ea13b742d423f2054d97509dba2f92d5902a6d1497509dba16ac8179e5d4276e87303ae40a9b2ea13b7453c5ab205e7a9b2ea139e406d902a6cba88309dba16ac815365d427808dd0b5640bcf53613b743ea0bf2054d97509dba16a283902a6cba84ef35ba16ac815365d4276e8c24b5640bcf2ea13b743980a32054d97509dba16a24379ea6cba84edd11284dc8179ea6d0984edd026e40bcf53613b74424137205e7b312ea13b7409b902f3d4d974dd10604dc8179ea6cba8d6dd14f640c075365d4276e8a7b2054d97516213b7453da56f3d4d97509dba29ec8179e5d45784edd14f640c395365d4276e88c7205e7a9b4fe5d37428fb1af3d4d97509dba231c8179ea6d3f97509c97640bcf5365d46b6e88c720616a9b2ea13b7453d902f3d4da852e9ba14fd5379ea6cba84edd14f640bcf536a14ba84e4eb2054da852ea13b742d59031454d97509dba075c815365d4276e87f43ae40bcf6ce5d4276e81d7205e797509dba1f90eb902f3d4da5909dba075c8179ea6c276e87c83ae40bcf5365d49984e1d7205e7a9b2ea139e40eb902f3db6a9b2e9ba075c8179ea6cba6e85143af16bcf5365d4276e81d7205e7a9b2ea13ba26e9902f3d4d97509dba2b3c8179ea6cba84edd00be40bcf5365d4276e81b3205e7a9b2ea0b3740eb79ea6cba84edd0ff075bcf5365d4166e87f83ae40c515365d4166e81d72054d975059ba1fd0eb902f3db3a9b2e9ba075c8179ed9cba82cdd03a800c8179ed9cba6e81d7205e7975059ba1f90eb902f3d4d974dd0a286cc8179ea6d2c974dd03ae40bcf536964166e81d400640bcf536963740eb902f3d4d82cdd0f9075 else 0xdd979ea6cba84edd019640bcf7125d4276e8ca792eecbcf5365d4276e9902f3d4d9751adba086dd979ea6cba84edd018e40bcf536904276e8ba720636a9b4525d4276e9902f3dc497509dba075c818daa6cba84edd14f6ecbcf5365d4276e802776623bcf5365d4276e9bb2f3da0a9b2ea13b74c818daa6cba84edd047e40bcf7125d4276e823f765e7a9b2ea13b745f3bb2f3d4da292ea13b74c818daa6cba84edd03ae40bcf536904276e81d7765e7a9b2ea13b7453d902f3db1a9b2e9ba16ac8179ea6cba6e85a8a3e40bcf726a6c276e85ab205e7a9b2ea1396a25d9031554d97509dba16ac8179ea6c276e87d447de7a9b2ea13b7444a23f2054d97509e07b742d590311d4d97509dba16ac8179ea6cba6e883c3ade7a9b2ea13b7444a1d72054d97509dba3382d5902f3d4d97509df3b74c8179ea6cba84edd14ce40bcf5365d4276e80bf205e7a9b2ea13b74283902f3d4d97509de6b74c8179ea6cba84edd128e40bcf5365d4276e80a3205e7a9b2ea13b74243cf6a6d4297509dba16ac816c6a6d42974dd0b5640b635365d4276e85a800640b635365d3742d5902f3d4d84edd0fa86cc81536a14ba6e85a8a3e40a9b2ea13b742d451c00640a9b2e9ba16a28f902a6cba84f009ba16ac81726a6d4284edd0b5640b3d5365d4276e85a800640b9353613b742d5902f3d4d974dd10783fc81536a14ba84e5a897640a9b2ea13b742d44b800640a9b2ea1396a25d902a6cba84edd17c16ac8150ea14ba84edd0b5640c6d5365d4276e85ab9ee40a9b2ea13b742d5902db54d97509dba16ac8179ea6c276e87d43ae40a9b2ea13b742d41d72054d97509e01b742d5902d054d97509dba16a))) else (if page < 27 then (if page < 26 then 0xc815365d4276e88ac1fe40bcf6325d4276e80ff205e797509dba22907fb1af3d4d97509dba29ec817a2a6cba84edd14f640bcf536a14ba6e8a07345e7a9b2ea13b7453d902f3d4997509dba29ec8179ea6cba856dd14f640bcf5365d40c6e8a7b205e7a9b2ea13b384d7c2af3d4d97509dba23fc8179ea6cba6e8be0a3e40c4f5365d4276e88ff205e7a9b2ea52c2725d902f3d4d9751ca13a3fc8186aa6cba84edd14f640bcf5365d4aa84e6975e5e7a9b2ea13b7453d902f3d4da852ea139b0c8179ea6cba8cedd14f640bcf2ea554276e8737205e7a9b2ea13a9e331902f3d4da852ea1392ec81872a6cba8d709dba640c6d79ea6cba6e851f635e7a9b2ea35c276e99031b5e7a9b2ea1392ec8179edfd4d97509dba640bcf5365d4276e80cb205e7a9b2ea13b7413b902f3d4d97509dba329c8179ea6d3797509dba640bcf5365d4276e80c7205e7a9b2ea13b7410d902f3d4d97509dba2e9e5dbb2f3d4d97509dba6ecbcf5365d4276e823f205e7a9b48213b7411f902f3dc497509dba2f9e2dbb2f3d4d97509dba6ecbcf5365d4276e81d7205e7a9b2ea35b740eb902f3d4da4109dba29ec8179ea6d148d6dd14f6ecbcf5365d427670027205e7b8940a5d4276e99030e54d9751adba29e001bb2f3d4da1309dba640c6d5365d4276e851f20636a9b50a5d37428e00320636a9b2e9ba147c8179ea6d2084edd0366ecbcf5365d4276e8a57205e7a9b482394276e9b1af3d4d9751adba29e001bb2f3d9897509dba640c6d5365d4276e84bb20636a9b50a5d42725c00320636a9b2ea1392ec8179ea6cba8d6dd01fe40bcf536904276e88ff9aeecbcf5365d4276e9902f3d4da4109dba09d else 0xc8179ea6cba84efc9ba640bcf5365d4276e88db205e7a9b2ea13bc56e9902f3d4d97509dba248c8179ea6cba84edd012e40bcf5365d4276e8473205e7a9b2ea13bdf6e9902f3d4d97509dba298e7b902f3d4297509c9773dbcf536a14ba84e4bb205e7b93536a142725d902f3dc9a9b2ea1392e001902f3dc9a9b09c97640bcf536a14272b84bb205e7a9b09dba15c25c003205e7a9b09cae12ec8179ed8d4da852e897640bcf6c6a6cba84e4b800640bcf6c6a6cba25d902f3d4d97509cf486cc8179ea6d4297451c97640bcf5365d42728e4b800640bcf5365d14725d902f3d4d97509e0112ec8179ecf54d97509c9773dc8179ea6cba84e4bb97640bcf5365d42725d902f3d4d974dd0de08fc8179ea6cba84e4b847e40bcf5365d4ae84e4bb20630bcf5365d42725d902f3cba84edd114875c8179e5d4276e885c3ae40bcf5365d4aa84e4bb8b640bcf5365d42725d902f3d4d97509cf4875c8179ea6cba84e4b83ae40bcf5365d42782c4bb2062abcf5365d42725d902f3d4d97509cf488fc8179ea6cba6e883047e40bcf5365d42781e4bb205e7b6d5365d42725d902a6cba84edd103075c8179ea6c276e85703ae40bcf5365d4278064bb205e7b035365d42725d902f3d4d84edd0f9065c817caf3d4d97509c97640bcf5faa6cba84e4bb205e7a9b2e9ba20c063902f3d4d97509c97121c8179ed054d97509c97640bcf5365d42725c11b205e7a9b33a5d42725d902f3d4d97529e1392ec8179ea6cba6e86f012e40bcf5365d42725c473205e7a9b2ea1ec2725d902f3d4d97509e0412ec8179ea6cba84e7a416e40bcf5365d42725c45ef3d4d97509dba22d07f9030e54d97509dba03f) else (if page < 28 then 0xc8179ec651484edd14f6c6bcf5368a4276e8a7b955e7a9b40a5d4276e9b1b0e54d97509dba29e001b1b0e54d97509dba640bcf726a6c276e851f205e7b93536a137428e003205e7b93535ba147c8189ea6cba84edd0366c6bcf5365d4276e8a5720627a9b2ea394276e9b1af3d8c97509dba29e001b1af3d8c97509dba743d8d79ea6cba84edd3205e7a9b2ea3942710fcaaf3d4d97509dba023c8179ea6d23974dd17573ed8d79ea6cba84edd3205e7a9b48e5d37413dcaaf3d4d97509dba025c8179ee4d4d84edd195640bcf536964276e823f20628a9b2ea13b74017caaf3d4da292ea13b74c8179ee4d4d84edd03ae40c4f5365d4276e81d7955e7a9b2ea13b7453dc7b635e7a9b2ea13b74c8179ea6cba918dd04572abcf5365d4276e80a3205e7a9b4b213b745dbcaaf3da0a9b2ea13b74c8179ecc4ba84edd047e40c4f5365d4276e823f955e7a9b2ea13b745f390313d4da292ea13b74c8179ecc4ba84edd03ae40bcf6325d4276e81d720627a9b2ea13b7453db1af3d4d97509dba022c8179ea6cba918dd1a2ec6c4779ea6cba84edd3205e7b3d5365d4270eb902f3d4d9751ca13875c8179ea6cba918dd14f6c6bcf682a6cba84edd320628a9b2ea13b7411f902f3d8c97509dba08fd8d79ea6cba84edd17cec6bcf5368a4ba84edd000716c515365d4276e9902f3dc9a9b09dba12ec8179ed8d4d974dd097640bcf5365d37428e4bb20623bcf5365d42725d79ea6cba84edd116875c8179ea6cba6e88303ae40bcf5365d4276704baf3d4d97509dba1dd11f902f3d4d97509d7c92ec8179ea6d1497509c975e7a9b2ea13b743ba1d7205e7a9b2e9ba1bc0eb902f3d4d97509d4f12e else (if page < 29 then 0xc8179ea6cba6e8c50a3e40bcf5365d42734608f205e7a9b2e9ba14722f79ea6cba84edd10406cc81872a6cba84edd14f640bcf5365d4326e8a7b205e7a9b2ea0ab7453d902f3d4d97509d9fa9ec8179ea6cba84edd14ae4dbcf5365d4276e8a7b205e7a9b50a5d4274f9902f3db697509dba06cc8179ea6d0297509dba70abcf5365d4276e81b00070abcf5365d4276e9902f3d4d97509dddb74c8179ea6cbf84edd036000d0f79ea6cba84edd3205e7a9b2ea13b7462d902f3d4d96709dba06c001902f3d4d97509d8b640bcf5365d4186e81b3205e7a9b2ea13b826e9902f5d4d97509dba06c001936f3d4d97509dba640bcf5365d4276e89f3205e7a9b2ea13b690d8003205e7a9b2ea13a7cc81872a6cba84edd14ae40bcf536a14ba6e851f60de7a9b2ea13b7453d902f3d4d97509e019eac8179ea6cba8d2dd14f640bcf5365d42782c7ab205e7a9b2ea01b7428f902f3d4d9751a613b74d8379ea6cba84edd14a800d8379ea6cba84edd3205e7a9b2ea13b743d5902f3d4d97509e011ea001902f3d4d97509cf5640bcf5365d4276e851f205e7a9b2ea0137428e003205e7a9b2e9ba147e1579ea6cba8e509dba640bcf67aa6cba6e851f205e7a9b2ea13b7410f902f3d4d97509dba2eac8179edf54d97509dba640bcf5365d4276e827b205e7a9b2ea13b74655902f3d4d97509dba08ac8179ea6cba84edd176e40c47662a6cba84edd39eec6bcf5365d4276e9caaf3d4d97509dba075c8179ea6d23974dd03ae40bcf726a6c276e8a7b635e7a9b2ea13b7411f902f3d8c97509dba2f9e2db1af3d4d97509dba6c6bcf5365d4276e81d7205e7a9b2ea463740eb902f3d4da5909dba29e else 0xe5dc2af3d4d97509dba70abcf5365d4276e823f205e7a9b42613b7411f902f3db397509dba2f9e1579ea6cba84edd03ae40bcf53684c276e8a7b2061ca9b45213b7453dce3855e7a9b2ea13b74c8179ea6d0984edd04d70abcf5365d4276e80bf205e7b672ea13b7463fc5b855e7a9b2ea13b74c8179ed8d4d974dd03af0abcf5365d4276e805f2061ca9b2ea13b7469b9030e54da292ea13b74001c5af3db397509dba721e1579ea6cba84edd3205e7a9b40a5d427133c2af3d4d97509dba02dc8179ed8d4d974dd18f70ac4779ea6cba84edd3205e7a9b40a5d4270eb902f3db1a9b2e9ba29ee1579ed054d97509dba640c395365d4276e823f205e7b672ea13b7411fc2af3d4d97509dba2f9e1579ea6d1497509dba640c395365d4276e81d7205e7a9b42613b740ebc2af3d4d97509dba29ec818aaf3d4d974dd0a3de7a9b2ea13b7441023f205e7a9b09dba21211f902f3d4d97503dba147bcf5365d4276e88203ae40bcf5365d4277eadd3205e7a9b2ea13b74477902f3d4d97509ddeb74c8179ea6cba84edd12173dbcf536a14ba6e851f205e7b635365d37428fcf7205e7a9b2e9ba147c8188ef3d4d974dd0a3e40a9b2ea13b744561d7205e7a9b09dba2120eb902f3d4d974dd19c147c8179ed054d974dd0a3e40bcf5365d42734623f205e7a9b2e9ba14711f902f3d4d974dd17c947c8179ea6d14974dd0a3e40bcf5365d4273461d7205e7a9b2e9ba29e28f902fade7a9b2e9ba147c8179eb9d4d974dd0a3e40bcf53613b744240cb205e7a9b2e9ba147283902f3db6a9b2e9ba147c8179ea6d45974dd0a3e40bcf5365d37428e1d7205e7a9b2e9ba1470d9902f3d4d974ef5ba147)))) else (if page < 35 then (if page < 32 then (if page < 31 then 0xc8179ea6cba84edd120e40bcf5365d46584edd3205e7a9b2ea13b74199902f3d4d97509dba03cc2379ea6cba84edd004e40bcf5365dc276e81d7205e7a9b2e213b740eb902f3d4d97509dc2036c8179ea6cba84edd0b3640bcf5365d4276e8a77205e7a9b2ea13b7455b902f3d4d97509dba249c8179ea6cba8e109dba640bcf5365d4276e85c7205e7a9b2ea13b74535902f3d4d97509dba33bc8179ea6cba84edd11ce40bcf536634276e8a7b205e7a9b2ea13b4053d902f3d4d97509dba2b5c8179ea6cba84edd14bf10bcf5365d4276e8a7b205e7a9b2ea13c03331902f3d4da4d09dba29ec8179ea6cba84ece0cc640bcf5365d46884edd3205e7a9b2ea13b7431b902f3d4d97509dba170c8179ea6cba84edd14a640bcf5365d4276e8ceb205e7a9b2ea13b74467902f3d4d98309dba29ec8179ea6cba84ec554f640bcf536694276e8a7b205e7a9b2ea13b384bf902f3d4d97509dba2a9c8179ea6cba84edd127640bcf5365d46684edd3205e7a9b2ea13b74295902f3d4d97509dcfb74c8179ea6cc384edd14f640bcf5365d4276e84cb205e7a9b2ea13b996e9902f3d4d99b09dba29edb979ea6cba84edd14f640bcf536a14ba84e66320620a9b2ea13b7453d902f3d4d9752aa13998c8179ea6cfd84edd14f640bcf5365d47a6e8a7b205e7a9b2ea13c16331902f3d4d97509dba173c815365d4276e8ce057640c4779ea6d1484ea7b205e7b6d2ea01b740ebcf6f3d4d97509dba173bcf536a14ba84edd0b9800bcf5365d4276e85cf205e7a9b2ea13b74135902f3d4d97509dba31fc818c2a6d0297509dba640bcf5365d4276e8d37205e7a9b2ea13b74133902f3d4d97509dba31e else 0xc8179ea6cba84edd152640bcf5365d4276e81db205e7a9b2ea13b74547cf7455e7a9b2ea13b74c8179ea6cba86add03af2ed1579ea6cba84edd3205e7a9b30613b7411fa2af3d4d97509dba075c8179ee74ba84edd03ae40bcf2ea13b743901d6f3d4d9d32ea13b740eb902f3da0a9b2ea13b00c8179ea6cb084edd047e40bcf5368a4ba84ec03205e7a9b2ea093740eb902f3d4d9d32ea13998c8179ea6cba91109dba640bcf5365d4276e860f205e7a9b2ea3f4276e9902f3d4d97509dba18ac8179ea6cba84edd02e640bcf5365d47b84edd3205e7a9b2ea3db74600003725e7a9b2ea13b74c8179ea6cba84edd0c7640bcf53664cba84e63800640bcf5365d42731d79ea6ce997509dba022c8179ea6cba84edec3ae40bcf5365d4276de1d7205e7a9b2ea103740eb902f3d4d98309dba065c8179ea6cba832dd03ade7a9b2ea13bf76e81d7205e7b6d5365d3846e9902f3d4d9a52e9ba075c8179ea6d1b97509dba640bcf5365d4276e80e3205e7a9b2ea13b74101902f3d4d97509dba2c8c8179ed0d4d97509dba640bcf5365d4276e8107205e7a9b2ea13b74129902f3d4d97509dba302c8179ea6d1597509dba640bcf5365d4276e8123205e7a9b2ea13b740f9902f3d4d97509dba2a8e7b94af3d4d97509dba640bcf5365d4506e81d797652bcf5365d4276e9902f3d4d9a509dba08fca579ea6cba84edd03ae11bcf5365d4276e81d7205e7b415365d4274bf902f3d4d84eff1ba08fc8179ea6d1497509d2fe40bcf5365d37451a1d7205e7a9b3e65d4276e9902f3d4d97509dba0c6c8179ea6cba84edd035640bcf5367c4ba84edd3205e7a9b2ea13b74193902f3d4d97509dba069) else (if page < 33 then 0xc8179ea6cf597509dba640bcf5365d4276e835f205e7a9b2ea314276e9902f3d4d97509dba0c8c81786a6cba84edd005e55bcf5365d4276e81d7205e7a9b2ea13b8c08dc42f3d4d97509dba075c8179ea6cba84ee0c3ae40bcf5365d4276d01d7205e7a9b30213b740eb902f3d4d96509dba075c8179eab4ba84edd03ae40bcf51a5d4276e81d739de7a9b2e9ba1450eb9031854d97509dd1374c8179ebbd4d974dd03ae40bcf5365d4276e815b205e7a9b2ea13b744bb903195e7a9b2ea13b74c8179ea6cba84edd053640bcf5365d4276e8243205e7a9b2ea13b745fb902f3d4d97509dba05ec8179ea6cba84edd136f3dce779ea6cba84edd3205e7a9b2ea183740eb902f3d45974dd0a2875bcf5daa6cba84edd03ae40bcf5daa6cba6e81d7205e7a9b4525d427567902f3d4d9751ce13b74c8179ea6cba84edd08c640c475365d4276e8acf205e7a9b2ea3a4276e9902f3d4d97509dba12ac8179ea6cba8dd09dba640bcf5365d4276e850f205e7b6d2e9ba07502f902f3d4597509dba017ce779ea6cba84edd03ae40bcf5365d4226e81d78b5e7a9b2ea13b7402f902f3cba84edd0fc017c8179ea6cba84edfdba640bcf5365d4276e8db339de7a9b2ea13b7402f902f3d4d975089ba017c8179ea6cba84ede1ba640bcf5365d4276e8c87205e7b6d2e9ba0750d9902f3d5797509dba06cc817aea6cba84edd03ae40bc55365d4276e81d7205e7a9b2fe13b740eb902f3d4d96709dba075c8179ea6cba830dd03ae40bcf5365d4277041d7205e7a9b2ea13b690eb902f3d4d97509dba058c8179ea6cba84edd134640bcf5368b4ba84edd3205e7a9b2ea13b740cd902f3d4d97509dba077 else (if page < 34 then 0xc8179ea6cba84edd0ce640bcf5365d4276e838f205e7a9b2e9ba2030eb79ea6cba84edd101875c1379ea6cba84edd03ade7a9b2ea13b744081d7205e7b5b2ea13b740eb902f3cba84edd0fd075c8179ea6d2684edd03ae40bcf53613b743e61d7205e7a9b2ea43c270eb902f3d4d97509cf2875c8179ed754d974dd03af3dc8179edb4ba6e81d7205e7b6d2e9ba0a20eb902f3d4d974dd0e9875c818c2a6cba84ee7dba640bcf6bea6cba6e81d7205e7a9b2ea13bac6e9902f3d4d97509dba072c8179ea6cba84edd069e40bcf5365d42775add3205e7a9b2ea13b740e1902f3d4d975149ba075c8179ea6cba6e8a003ae40bcf5365d4276e834b205e7a9b2ea13b740759baf3d4d97509dba075bcf606a6cba84edd03ae40bcf5365d4276e84bf205e7a9b2ea13b740ddb72f3d4d97509dba075bcf5365d4276e88a03ae40c415365d4276e81d72054d97509dba2260eb902f3d4d9fb09dba075c8179ea6c276e884c3ae40bcf5365d47a6e81d7205e7a9b2e9ba20d0eb902f3d4d97509dba303c8179ea6cba84edd018640bcf5365d42775cdd3205e7a9b2ea13b740d7902f3d4d97509dba0d1c8179ea6cba84edd0ccf3de2d79ea6cba84edd38b5e7a9b2e9ba1fe0ebc5af3db6a9b2e9ba075e2d79ea6cba6e85143ade7a9b2ea13b7443e1d79ede7a9b2ea13b8c6e9902f3d4d9b72e9ba075c8179ea6cba84edd041e40bcf5365d4276e8b37205e7a9b2ea13b740fd902f3d4d97509dba2aac8179ea6cba84edd031640bcf5365d4276e89872bde7a9b2ea13b7411f902f3d5d97509dba2f9bcf5365d4277d8dd047e40bcf5365d40f6e89c3205e7a9b2ea30c276e9902f3d4d97509dba0ce else 0xc8179ea6cba84ef29ba5e7a9b2ea574276e829b205e7a9b2ea13b4d5f3902f3d4da7b2ea13b74c8179ea6cba84edd0ea716db979ea6cba84edd320623bcf5365d427331c42f3d4da292ea13b74c8179edb54d97509ccc640bcf5367d4ba84edd2f3db6a9b2ea13b74157903185e7a9b2ea13b5fc8179ea6cba84ef3dba640bcf5365d4276e8c07205e7a9b2ea13b74055902f3d4d97509dba08ec8179ea6cba84eecdba640bcf5365d4276e8a9f205e7a9b2ea13b7403b902a6cba84edd07601ce4f902f3d4d97509db5640bcf652a6cba84edd3205e7a9b2ea13b74185902f3d4d97509dba08dc8179ea6cba84edd17be40bcf5367dcba84edd3205e7a9b2ea13b74183c5af3d4d97509dba0a6c8179ea6d1497509da6f3dbcf6da5d4276e829b20630c475365d42769b90311d4d97509dba34de7bc5af3db697509dba000e7bc5af3db6974dd320630a9b2ea13b7415dcbaf3d4d97509dba09bc8179ed054d97509d9073dbcf5365d4276e829720623bcf5365d42768b902f3d4d84edd0ec88fc8179ea6cb984edd047f3dcdd79ea6cba84edd3205e7a9b4525d42754db72f3d4da292ea13b74e7b902f3d4d97509ccc640c415368a4ba84edd320630bcf5365d427331902f3d4da292ea13998db988ef3d4d97509dba716c8179ea6cba84e663205e7a9b2e9ba2010eb902f3d4d974dd100075c8179ea6cba84edd0cde40bcf5365d42f6e81d72062fa9b2ea13b740eb902a6cba84edd0eb075c8179ee6cba84edd03ae40bcf2ea13b743921d7205e7a9b4ae5d3740eb902f3d4da212ea13875c8179ea6cba84e6603ae40bcf5365d42776add3205e7a9b2ea13b74649902f3d4d97509dba073))) else (if page < 37 then (if page < 36 then 0xc8179ea6cae84edd047de7a9b2ea13b743ae23ef3d4d95d09dba1d711f902f3dcd95d09dba08fc8179ea6d2b84edd047800c8179ee6c276e823f205e7a9b2b9ba1b611f90317d4d95d09dba08fc8179ea6cae84e66047e40bcf6825d4276e8be7975e7a9b2ba13b7411f902f3d4da252ea13b74c8179ea6cba84edd058640bcf5365d4276e8dcb205e7a9b2e9ba20102fd02f3d4d97509dba0a6c8179ea6cba84ef45ba640bcf5365d4276e8bf3205e7a9b2ea13b8d6e9902f3d4d97509dba259c818caf3d4d97509da6f2cc4779ea6cba84edd3205e7b6d53613b74217cd2f3d4da292ea13b74c8179edb54d97509c82640bcf5369d4ba84edd3205e7b372ea13b7469a003965e7a9b2ea13b74c8179ea6cba84edd085e40bcf6baa6c276e842c00640bcf53613b74217902f3d4d97524a13b74def79ea6cba84edd1a6800def79ea6cba84edd3205e7a9b2ea13b74209902f3daea9b2ea13904001902f3d4d97509c82640bf15368a4ba84edd320630bcf5365d4276a1902f3d4d97509d10814c8179ea6cba84ee49ba640bcf5365d4276e896b205e7a9b2ea13ba96e9902f3d4d97509dba2a1c8179ea6cba84edd00de40bcf5365d427762dd3205e7a9b2ea13b74545902f3dc1a9b2ea13b20c8179ea6cba92309dba640bcf5365d4276e82df205e7a9b44e5d4276e9902f3d4d97509dba0b8c8179ea6cfe97509dba640bcf5365d4276e82e7205e7a9b2ea3d374641902f3d4d97509dba01ec8179ea6d0697509dba640bcf5368e4ba84edd3205e7a9b2ea13bd06e9cf72ade7a9b2ea13b74c8179ea6d1497509d35de7a9b2ea13b7414c23ef3daea9b2ea13b7411f902f3d4da312ea13b74 else 0xc8179ee6cba95d09ccc000c8179ee6cba84e663205e797509dba1c9331902f3cba95d09ce4998001902f3cba84e724cc640bcf53695cba95c663205e7a9b4ae5d427330003205e7a9b4ae5d198c8179ea6cba95c6d8cc640bcf5365d37436c66000640bcf5365d1b6331902f3d4da212ea13998e5d902f3d4d97509ccc640c5579ea6cba84e663205e7a9b2ea139e511f902f3cba84edd0fd08fc8179ea6cba84f03ccc640bcf5365d37436c197205fbbcf5365d427331902f3d4d9cd2ea13998c8179e5d4276e87e818640bcf5365d427330637205e7acd5365d427331902f3d4d9c52ea13998c8179ea6c276e87cc17640bcf5365d427330623205e7a9b2ea1399807f902f3d4d97511e13998c8179ea6cba84eff8cc640bcf5365d4273ca0b3205e7a9b2ea1399830379ea6cba84edd114046c81882a6cba84edd023640a9b2ea13b7444c11b205e7a9b3f613b7408d902f3d4d84edd109846c8179ea6cba8f4dd023640bcf5365d37441a11b6e5e7a9b2ea13b745f393ef3d4d97509dba2f9c8179ea6cba95d09d45684bcf5365d4276e8be7205e7a9b2ea0a3745f3a62f3d4d97509dba2f9c8179ea6cba84f03d6c6dcbcf5365d4276e88ff205e7a9b2ea54c273319031054d97509dba23fc8179ea6cba94b09ccc640bcf5367ec276e88ff205e7a9b2ea13bf8331902f3d4d9751e9ba23fd5b79ea6cba84edd17ce40bcf5365d4ae84e6975e5e7a9b2ea13b745f3902f3d4d9752ba139b0db379ea6cba84edd17ce40bcf2ea574276e8737205e7a9b2ea57427331902f3dcd97509dba08fc8179ea6cba6e86d847e40c5f5365d4276e823f205e7a9b2ea1399811fcbaf3d4d97509dba08f) else (if page < 38 then 0xc8179ea6cba84edd04c640bcf5365d4276e8c77205e7a9b2ea13b74113902f3d4d97509dba2ece5db72f3d4d97509dba6dcbcf5365d4276e823f205e7a9b3f613b7411f902f3dad97509dba2f9c8179ed04fd97509dba640c416825d4276e8be76e5e7b412ea13b745f3902f3d4d9fb1ea13b74db9882a6cba84edd17c800db9882a6cba84edd320620a9b2ea3d4276e9b72f3d4d9fb09dba2f9001b72f3d4d9fb09dba6dcbcf5365d47a84edd320620a9b3f613b745f2003885e7b5b2ea13b74e89b72f3d4d97509dba640bcf5365d48784e227885e7a9b2ea13b74059902f3d4da572e9ba2ece2179ea6cba84edd005f33db979ea6cba84edd3205e7a9b3f613b74131c42f3d4d97509dba02ec8179ed6cba84edd18ef23db979ea6cba84edd3205e7a9b2ea3d374111c42f3d4d97509dba030c8179ea6d2684edd175f10bcf682a6cba84edd3205e7b5b2ea13b7411f9031054d97509dba08fe2179ea6cba84edd17cedcbcf5365d4276e80536e5e7b415365d4276e80038862aa9b2ea13b74c818bea6cba84edd0cc640bcf7365d4276e8663205e7a9b4ae5d374331902f3da0a9b2ea13998bcf5365d4276e881047e40bcf53613b743e623f205e7a9b2ea13af9331902f3d4d97509df5b74c8179ea6cba84edd122640bcf5365d4277ccdd3205e7a9b2ea13b74495902f3d4d97509dba02ec8179ea6cba84edd0c4640bcf5365d4277badd3205e7a9b2ea13b7449fcbb205e7a9b2ba13998e5d79ea6cba95d09ccc640c5f79ea6cba84e6632062fa9b2ea574273300032062fa9b2ea13998c815365d4276e8758cc640a9b2ea574273ac66000640a9b2ea139d6331902f3dcda9b2ea13998 else (if page < 39 then 0xe5d79ea6c276e875c47e40bcf5365d4276e8157205e7a9b2ea13b744b9902f3d4d97509dba091c8179ea6cba84edd17f640bcf5365d4276e81e7205e7a9b2ea13b74561cbb375e7a9b2ea13b74c8179ea6cc684edd047e40c6f5365d4276e823f2054d97509dba16911f902f3da0a9b2ea13aa6c8179ea6c276e8b1047e40bcf536824ba84edd3205e7a9b2ea13b74233902f3d4d9751da13b74c8179ea6cba84edd08f640bcf5365d46c84edd3205e7a9b2ea3637454c00379de7a9b2ea13b74c8179ea6cba84edd091e40b035365d4276e848c00640a9b2ea13b7424779ec0d4d97509dba014c8179ea7cba84edd047e40bcf5365d4236e823f205e7a9b2ea17b740cbcbaf3d4d97509dc4374c8179ea6c4e84edd047e40bcf5365d4276e8207205e7a9b2ea13b74593902f3da2a9b2ea13b74c8179ea6cba84edd021e40bcf5365d4276e824f205e7a9b2ea13b74609902f3d4d97509dba063c8179ea6cba84edd130640bcf5365d46084edd3205e7a9b2ea13b7418b902f3d4d9ed2ea13b74c8179ea6cba84edd06c640bcf5365d4276e819f205e7a9b2ea31c276e9902f3d4d97509dba0cfc1379ea6cba84edd005e40bcf5365d4277100ff205e8a9b2ea13b7411f902f3d4d97509db308fc8179ea9cba84edd047e40bcf5365d41a6e823f205e7ab32ea13b7411f902f3d4d975079ba08fc8179ea6cba84edd0e9640bcf5365d4276e8bdb205e7a9b2ea13b7460b902f3d4d97509dba247c8179ea6cba8f109dba640bcf5365d4276e876b975e7a9b2ea13b743b579ea6cba95d09dba1da00179ea6cba84edd0ed640bcf5365d4276e8223205e7a9b2ea13b745d7902f3dbca9b2ea13b74 else 0xc8179ec954d97509dba640bcf5365d427722dd3205e7a9b2ea13b744b7902f3d4d97509de7374c8179ea6cba84edd17de40bcf5365d4276e80a7205e7a9b2ea13bb26e9902f3d4d97509dba2afc8179ea6cba84e88011663bcf682a6cba84edd32062abcf5365d42768d90316de7a9b2ea13b45c8179ea6cba93909dba640bcf5365d4276e82f3205e7b275365d4276e9902f3d4d97509dba0bdc8179ea6d0797509dba640bcf5365d4276e82fb205e7a9b09dba1da11f79ea6cba84edd0ed08fc8179ea6cba84ef25ba640bcf5365d4276e8233205e7a9b2ea13b741bd902f3d4d97509dba131)))))) else 0
  | 7 => if page < 6 then (if page < 3 then (if page < 1 then 0x1902f3d4d97509dba03fc8179ea6cba85d09dba054001902f3d4d97509dd8374001902f3d4d9750b9ba0540000033f5e7a9b2ea13b74c8179ea6cba84f06dba054001902f3d4d97509dba2ce001902f3d4d97506dba054000003205e7a9b2ea13acec8179ea6cba84edd05681c001902f3d4d97509dba01cc8179ea6cba84edd02a036001902f3d4d97509dba256c818e2f3d4d97509dba256c8179ea6cba94d09dba054c8179ea6d4097509dba256e5d902f3d4d97509dba256c8179ea6cba84edd12b08fc8179ea6cba95d09dba256c818c2f3d4d97509dba256c8179ea6d4097509dba075c8179ea6cba94d09dba075c8179ea6cba95509dba256c8179ee8d4d97509dba256c8179ea6d4097509dba054c8179ea6cba84efe5ba054c8179ea6cba94d09dba256c8179ea6d3297509dba256c8179ef054d97509dba054c8179ea6cba84edd12b054c8179ea6cba84edd1b1256c8179edb54d97509dba256c8179ef054d97509dba075c8179ea6cba84efe5ba075c8179ea6cba84edd19c256c8179ed054d97509dba256c8179ea6cba84edd1b108fc8179ea6cba84efe5ba08fc8179ea6cba84edd17ca56c8179ea6d1497509dba256c8179ea6cba84edd1b1075c8179ea6cba84edd12b075c8179ea6cba84edd14f256c8179ea6cba93b09dba256001902f3d4d975275ba256c8179ec4d4d97509dba256001902f3d4d9e92ea13b74c8179ef054d97509dba0dd001902f3d4d97509dba0ddc8179ea6cba84efe5ba065001902f3d4d97509dba065c8179ea6cba84edd12b23f001902f3d4d97509dba23fc8179ea6cf197509dba256001902f3d4d97517e13b74c8179ef054d97509dba0d0001902f3d4d97509dba0d0c8179ea6cba84edd12b036001902f3d4d97509dba036c8179ea6cba84edd12b231001902f3d4d97509dba231c8179ea6cba84edd1b1054001902f3d4d97509dba054001902f3d4d97509db1054 else (if page < 2 then 0xc8179ea6cba84edd03a854c8179ea6cba84f059ba054c818aaf3d4d97509dba054c8179ea6cba84edd0fe054c8179ea6cba84edd06d054c8179ea6cba84f03dba054c8179edb54d97509dba054c8179ea6cba84edd0fc054c8179ea6cba84edd0a2854c8179ea6cba84f00dba054c8179ea6d3297509dba054c8179ea6cba84edd0b4054c8179ea6cba84edd0da054c8179ea6cba84edd10f05400179ea6cba84edd10f054c8188ef3d4d97509dba054c8179ea6cba84edd10c054001902f3d4d97509d0c054c8179ea6cba84edd066854c8179ea6cba84edd19c054001902f3d4d97509d9c054c8179ed054d97509dba054001902f3da0a9b2ea13854c8179ea6cba84edd10a854c8179ea6cba84edd094854001902f3d4d97509c94854c8179ea6cba84edd17c854c8179ea6d1497509dba054001902f3d4da292ea13854c8179ea6cba84edd108854c8179ea6cba84edd0ca854001902f3d4d97509cca854c8179ea6cba84edd14f054c8179ea6cba93b09dba054001902f3d4d97527613854c8179ea6cba84edd075854c8179ea6cba84edd0f1854001902f3d4d97509cf1854df9902f3d4d97509dba054001902f3d4d97527613b74001bf2f3d4d97509dba054c817aaf3d4d97509dba054001902f3d4d97509dc8374c8179ef1d4d97509dba054001902f3d4d97509dba263c8179ea6cba84edd02a009001902f3d4d97509dba009c8179ea6cba84edd02a04d001902f3d4d97509dba04dc8179eaad4d97509dba054001902f3d4d97509dd3b74c8179ea6d4797509dba054001902f3d4d97509dba2acc8179ea6cba84edd02a014001902f3d4d97509dba014c8179ea6cba84edd02a046001902f3d4d97509dba046c8179ea6cbe97509dba054001902f3d4d97509de2374c8179ea6cba96909dba054001902f3d4d97509dba307c8179ea6cba84edd02a022001902f3d4d97509dba022c8179ea6cba84edd02a03f else 0xe5d902f3d4d97527613b74c8179ea6cba93b09dba08fc8179ea6d3297509dba2f9c818c2f3d4d97527613b74c818e2f3d4d97509dba075c8179ee8d4d97509dba075c818e2f3d4d97509dba29ec8179ee8d4d97527613b74c8179ee0d4d97527613b74001902f3dc1a9b2ea13b74e85902f3d4d97509dba00b001902f3d4d97509dba00bc8179ea6d3297509dba09f001902f3d4d97509dba09fc8179ee8d4d97509dba32b001902f3d4d97509dba32bc8179ea6d3e97527613b74001902f3d4da7d2ea13b74e85902f3d4d97509dba009c8179ea6cba93b09dba08b001902f3d4d97509dba08bc8179ea6d3297509dba2ee001902f3d4d97509dba2eec8179ea6d3297527613b74001d0b7e5e7a9b2ea13b74c8179edb54d97527613b74001cf77e5e7a9b2ea13b74e85902f3d4d97509dba075c8179ea6d3297509dba075001902f3d4da652e9ba075c8179ee8d4d97509dba29ec8179ed054d97527613b74001cbb7e5e7a9b2ea13b74df9902f3d4d97509dba08fc8179ea6d3297509dba08f001902f3d4da6509dba08fc8179ea6cba93b09dba2f9c8179ea6d1497527613b74df9902f3d4d97509dba075001bf2f3d4d97509dba075c8179ea6cba93b09dba075c8179ea6cba93b09dba29e001902f3d4da6509dba29ee85902f3d4d97509dba054c8179ea6cba84edd056854e7b902f3d4d97509dba054c8179ea6cba84edd0b9054c8179ea6cba84edd051054c8179ea6d4297509dba054c818e2f3d4d97509dba054c8179ea6cba84edd073854e5d902f3d4d97509dba054c8179ea6cba84edd0eb854c8179ea6cba84edd047854c8179ea6cba95d09dba054c818c2f3d4d97509dba054c8179ea6cba84edd0ea854c8179ea6cba84edd070854c8179ea6cba95509dba054c8179ee8d4d97509dba054c8179ea6cba84edd0e3854c8179ea6cba84edd0ad054e2d902f3d4d97509dba054c8179ea6cba84edd0ff054)) else (if page < 4 then 0x1902f3d4d97509dba29ec8179ea6cba84ee11ba075001902f3d4d97509dc2374c8179ea6cba84edd1b3875001902f3d4d97509dba25fc8179ea6cba84edd066809c8179ea6cba84edd03a836e7b902f3d4d97509dba29ec8179ea6cba95509dba075c8179ea6d4297509dba29ec818aaf3d4d97509dba29ec8179ea6cba84edd19c08fc8179ea6cba84f00dba08fc8179ea6cba84f03dba29ec8179edb54d97509dba29ec8179ea6cba84edd19c075c8179ea6cba84edd14f075c8179ea6cba84f00dba29ec8188ef3d4d97509dba29ec8179ea6d4297509dba075c8179ea6cba84f00dba075c8179ea6cba84edd19c29ec8179ed054d97509dba29ec8179ea6cba84f059ba08fc8179ea6cba84edd14f08fc8179ea6cba84edd17ca9ec8179ea6d1497509dba29e001902f3d4da2909dba29ec81872f3d4d97509dba29e001902f3d4da052ea13b740019030e54d97509dba29e000003855e7a9b2ea13b74c8179ea6d4297509dba147001902f3d4d97509dba147001902f3d4da852e9ba147000003205e7a9b2e9ba147c8179ea6cba84f00dba06c001902f3d4d97509dba06cc8179ea6cba84edd14f295001902f3d4d97509dba295c8179ec654d97509dba29e001902f3d4d9751ca13b74001b1af3d4d97509dba29e000003635e7a9b2ea13b74c8179ea6d4297509dba12e001902f3d4d97509dba12e001902f3d4da852ea1392e000003205e7a9b2ea1392ec8179ea6cba84edd14f03fc8179ea6cba84f00dba23fc8179ea6cba8d709dba29e001902f3d4d9751ae13b74001902f3d4d9751adba29e000003765e7a9b2ea13b74c8179ea6d4297509dba16a001902f3d4d97509dba16a001902a6d4297509dba16a0000032054d97509dba16ac8179ea6cba84edd19c04dc8179ea6cba84edd14f231c8179ea6cba84f059ba075001902f3d4d97509dba075001902f3d4d975059ba075c818e2f3d4d97527613b74 else (if page < 5 then 0xc8179edb54da292ea13b74c8179ea6d3ea292ea13b74c8188ef3d4d97509dba0ae001902f3d4d97509dba0aee7b902f3d4d97509dba01ce2d902f3d4d97509dba36a001902f3d4d97509dba36ac8188ef3d4da292ea13b74001cf78b5e7a9b2ea13b74c8179ed054da292ea13b74e2d902f3d4d97509dba08fc8179ea6d1497509dba08fc8179ea6d1497509dba2f9e7b902f3d4d97509dba075c8179ea6cba84edd051075e5d902f3d4d97509dba075c8179ea6cba84edd0eb875c8179ea6cba84edd047875c8179ea6cba95d09dba075c818c2f3d4d97509dba075c8179ea6cba84edd0ea875c8179ea6cba84edd070875c8179ea6cba84edd0ff07500179ea6cba84edd0ff075c818aaf3d4d97509dba075c8179ea6cba84edd0fe075c8179ea6cba84edd06d075c8179ea6cba84f03dba075c8179edb54d97509dba075001902f3db6a9b2e9ba075c8179ea6cba84edd0b9075c8179ea6cba84edd0a2875001902f3d4d974dd0a2875c8188ef3d4d97509dba075c8179ea6cba84edd10c075c8179ed054d97509dba075c8179ea6cba84edd10a875c8179ea6cba84edd094875c8179ea6cba84edd17c875c8179ea6d1497509dba075c8179ea6cba84edd066875c8179ea6cba84edd0ca875e2d902f3d4d97509dba075001902f3d4da292ea13b74001c5af3d4d97509dba075c817b2f3d4d97509dba075001902f3d4d97509dc6374c8179ef0d4d97509dba075001902f3d4d97509dba270c8179ea6cba84edd03a80bc8179ea6cba84edd051046c8179eabd4d97509dba075001902f3d4d97509dd1374c8179ea6d4597509dba075001902f3d4d97509dba2b3c8179ea6cba84edd03a817001902f3d4d97509dba017c8179ea6cba84edd03a86cc8179ea6cc197509dba075001902f3d4d97509dde374c8179ea6cba96309dba075001902f3d4d97509dba300c8179ea6cba84edd0ca822c8179ea6cba84edd03a865 else 0xc818aaf3da0a9b2ea13b74c8179ee0da0a9b2ea13b74c8179ed054d97509dba0a5001902f3d4d97509dba0a5e5d902f3d4d97509dba022c818aaf3d4d97509dba345001902f3d4d97509dba345c8179ea6cba84edd0eb88f00179ea6cba84edd0eb88fc8179ed054d97509dba08fc8179ea6cba84edd06d08fc8179ea6cba84edd09488fe5d902f3d4d97509dba08f001902f3da0a9b2ea13b74001cbaf3d4d97509dba08f001902f3d4d97509dba2f9c8179ea6cba85f09dba08f001902f3d4d97509dceb74c8179ea6cba84f065ba08f001902f3d4d97509dba2a6c8179ea6cba84edd094814c8179ea6cba84edd047865c8179ea6cba84ee21ba08f001902f3d4d97509dc4374c8179ea6cba84edd1b288f001902f3d4d97509dba26bc8179ea6cba84edd06d00bc8179ea6cba84edd04783fc818aaf3d4d97509dba2f9c8179ea6cba84edd17c88fc8179ea6cba84f03dba2f9c8179ed054d97509dba2f9001902f3da097509dba2f9c8179ea6cba8f509dba2f9001902f3d4d9751ea13b74001b72f3d4d97509dba2f90000036e5e7a9b2ea13b74c8179ea6cba95d09dba198001902f3d4d97509dba198001902f3d4d9752ba13998000003205e7a9b2ea13998c8179ea6cba84edd17c846c8179ea6cba84edd17ca3fc8179ea6cba95d09dba08f001902f3d4d97509dba08f001902f3d4d95d09dba08fe7b902f3d4da292ea13b74c818caf3d4da292ea13b74001903195e7a9b2ea13b74e7b902f3d4d97509dba017c8179edb54d97509dba0a6001902f3d4d97509dba0a6c818c2f3d4d97509dba34d001902f3d4d97509dba34dc8179eebd4da292ea13b74e7b902f3d4d97509dba014c8179ea6d1497509dba09b001902f3d4d97509dba09bc8179edb54d97509dba320001902f3d4d97509dba320c818aaf3d4da292ea13b74c8188ef3d4d97509dba08fc8179edb54d97509dba08fc818c2f3d4d97509dba2f9))) else 0
  | 8 => if page < 1 then 0x1902f3da0a9b2ea13b74000003205e7a9b2ea13b7411e00000640bcf5365d4276e8be400000c8179ea6d1497509dba000001902f3d4d97509dba075000003205e7a9b2ea13b7453c00000640bcf5365d49d84edd000000c8179ea6cba84edd02a000001902f3d4d97509dba256 else 0
  | 9 => if page < 1 then 0x3205e7a9b2ea13b74 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 4 => 62
  | 5 => 2002
  | 6 => 2520
  | 7 => 384
  | 8 => 9
  | 9 => 1
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
  | 4 => 51
  | 5 => 1307
  | 6 => 1674
  | 7 => 300
  | 8 => 20
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 4 => 183
  | 5 => 4703
  | 6 => 6030
  | 7 => 1079
  | 8 => 73
  | 9 => 2
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x2400040000001500030000000100060007000000000004000400000013000200020004000000120002000600020005000000050025000500000001000d000e000100000010001000020001000400050005000700060006000100020008000000010001 else 0
  | 5 => if page < 21 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x10011000100080008000400000000000000010001001d0014000d000d000000000014000300010005000f000c000200000002000b000400000000000000050000000200050031001100000006000b0000000000030003000a000e000400000008000a00030014000c00030001000000000003000100050016000900000000 else 0x30000000300170004000c000100060004000000120003000000000000000900060003004900050003000c0000000500000000000500010001000400020005000200000001000a0000000a000400000007000c000b002c00100001000c00070002000000000000000100080001000100050002000100070001000c001e0001) else (if page < 3 then 0x100010015000a000500000009001200020000000100000016000e0005000100010001000f00000012000000060001000100020000000e00000005000500010001000000010005000200030001000000010001000100000002000b001400030000000000000009000100020000001000030002001000000001000000090002 else (if page < 4 then 0x2000800030010000000080000000300020006001a00060000000900000005000000020018000500010000000000020005000100040000000800050001000f0000000000020001002c0000000000070000000700070000000b00110002000000020004000d000300010006001c00040000000000020000000000130000000b else 0x50009000000000006002600040005000100020000000000000000000000000000000a00020002001500020001000000010000000600010001000100020000000100080008000300010008000100020002000200000001000200040004000000000001000a001b0000001f00020001001200120000000000030007))) else (if page < 7 then (if page < 6 then 0x5000a000c00000005000b0014000f000700020002000500020002001f000d000100100000000200120001000000000006000b00010004000000100026000900000007001700000000000e000500000000000a00020001001300010002001c000e0003000000000002000b000500070002000d000900060005000500020005 else 0x17001400130000000100060004000600020029001200080003000e000000030000000200000000000d000c000100040002000a00000000000a0004000000070000002a00020032001a0001000b00300000000000190007000700000007000000060000000000060004000000020003000100000004000500050019002f0000) else (if page < 8 then 0x800000000000800000001000500020004000c0000001b000000030004000100020016000900000000002700000004000800050001001a00000000000c000200040003002300000003000b00090013000000000000000200000019001c00010000000800000000000000010007000600030000001c00070009001200610034 else (if page < 9 then 0xa000000190004000600000003003500160003000a000000380015000300030004000000000001000300020004000000000006000000100015000400050000001c00000000001f00020017000200000002000000160001000e0000000d0016000a000b0002000600250005000000010000000300000000000c000400040017 else 0x800000006000400160005000b0000000900110005000000040002001d003600250000000b000f001f001f000a0008000800000000000000000000000000030000001500010013000100000000000a000000000013000000000016001100040023000100010000000000040001000400020002000100060002000100010006)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0xe0004000f000000300002001c00040003000200050009000e0004000200030003000c000700040000000300020005001f0022000200170000001400010009001f00040009001200330006000000030000000b000700100009001900000001000000040004000100070027000500220046000900010001000200030007000b else 0x13002d0002002900060000000400010000000800000008000c001100010002000200000000000500000004002700000009000000030003000c000c00050006000400140004000600180007000300040003000e00170000000e0002000300090016000500070006002700010003000300040007000600010000001000030002) else (if page < 13 then 0x600010046000b001500010006000000160008000d002600010000001b00040007000b0000002200000003000000020001000500000024000d001e000d00000017000a00050004000e001400110003000600070000000e0004002700000000000100040011000a000500010001000b00030003000400120002000300000004 else (if page < 14 then 0x12000400020005000100080002001a000100100010000000130003000100180001001b000c000000020020000000000003000d00000011001a000400030000000000060007000000010000000300190000000b00240005000000000000000f0000000c000000000001001f0018000000040001001a0003000500180004000e else 0x5000a0003000100080023000e0000002200080001003f00400006000f000800110002000200090000001d000400030031000f000d0000000700050009000100000000000a000700060001000b00000008000300000040000d0002004400000000002e00040003000300070000000500050001000500000001003e00010000))) else (if page < 18 then (if page < 16 then 0x49000a0005000a000f0000000d00000000000d0000000a002100030008000b003b003400090002000a00070000000b000000120012002d000c00030028000e003c00380017000300100003000c00020004001b0003001800020011000200000025000000030014000300020022000000010028000000010008000e00030004 else (if page < 17 then 0x100110009000900000000004000150007000c000e00190000000300000004001a00490010001f000b002e007b001200120005002c000100020004004500000015000000020002000000010015001900070053000800040010000300000001000d001c0007000a00000002000800050021000a000000050027000300010007 else 0x200390002000000000015001300000001001f0018000000010001000300050027000b00150006000000020014000000060000005c0006000b005000060000001700000033000b001b00200001003100020005000000240000001d0041001400220004000c001d000000020013001e0005002c001900060005000300090001)) else (if page < 19 then 0xb0003001a0018003f00210000000b0022000300460008000500000001001a0038001f0006000000000000000c0007000b000000170005006e00060015000000010004000a0001000a000400000000000400010004000f003300050002001d00000018000200000001000e0002001a00050000000b00000005001300000013 else (if page < 20 then 0x1c0000001d002e000200310008001300010054000000010000000b000300000049000d00000005001600020000000700010050000f004e000100160012000200000019001b0003001d000100260001000b000700050025001c00070018000000040038000200210015000000130004005800150000003600260005003c0000 else 0xd0018005d000a000f001200010039003a000000050001004e001a00050018002800110022000100000004004500150005000a001e))))) else 0
  | 6 => if page < 27 then (if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x3000a00000001001400030005000a0001000200020007000500020000001700000000000200020001000f0005001e000b0006000200110000000000170005000a000b000000080001000000040011000d00090001000c000000000000000000000004001500080002000100000000000000000004000300020012000a else (if page < 2 then 0xe0000000000040000000000000001000100010029000d0000000100010000000300030006000000020004000a000400010002000000000003001000040009000500070003001a000500000006000100020004000b000e000000000001000800000000000000010001000000000001000e0000000300040005000a00000000 else 0xb000000020011000300000000000000050002000200010002000f001800010014000200090004000b00030000000400000003001e0001000400050000000b000000010000000b000d0000000100020000001300010003000100100002000100010004000200020006000100170004000500080000000e0007000d0002)) else (if page < 4 then 0x2000b00010006000500060006000700010011002100060000000a00090000000000010000000300090000000400000006000300090000000500020002003800060001000600010000000a001100000010000c0000001e0000001100060000000d000000000003000000000000000400030007000000040000000b00040001 else (if page < 5 then 0x20006000b00000000000000000003001200010004000100000008000a0007002e00020000000e000300010015000000000000000a000000120002000100030006000500020007001200000003000300050005002c00010004000c00180004002e000400080004000100010007001d000f0001000c00120002000700100014 else 0xc0001002100050004000d000000000014000e001200000013000100030000000100020008000b000100000000000000020000000200060001000b000b00040008002f00060007000100050004000e00000000000000010002000500020000000600000027000100000002000a002400030002000000000004000a00000013))) else (if page < 9 then (if page < 7 then 0x100000000000b0005000000030000000000010006000f000300180003000600410002000a0008000b001300110004000a0003000000030002001200000003000a000c000c00040004000d0005000500010003001a000a000000070003000100000002000000000014000300170003000000000001001f000b000200100001 else (if page < 8 then 0x2400040000000000190011000000050003000a00000009000200000001001a000a001b000400030002000000000017000b0006000000010020000100010001000c000a000100030003000d000100090001001100060000000800050005000b00000001000000050008000100170000000d0003000100060003000200080000 else 0x70011000200050001000100090006000a0001000a000000000005000a00050002001200000001000000020000002d00030005000000030000000100020000000d000000000003000c000100030000000100020001000200000002000000040024000200040000000000060004000a0001000a0005000300160001000a0004)) else (if page < 11 then (if page < 10 then 0x200020000000900000001000a001d0000000b000300100000000000050000004b00050002000000000001000200010002000b0007000b00050000004e000100290005000700000000000400060002000d0007000000140000000a00080011000d0003000400000016000b00050006000500020000001c000000050003 else 0x1500050004000100110008000f0000000e00000000001f0008000400000000000000000001000100000000000a00020001000500100000001f00030000000000010002000000000006001a00040001001400090009000400000000000400000030001500010000001a000c000400000000000000010000000200000000) else (if page < 12 then 0x1000d00150000000100030005000300000000000b00000005000500030006000300100006000b000900040006000a000c00000006001b0017000000150002000200010002000200030000000000040000000100000003000000150007000500020001000000000002000700470000000600020004001f000200000009000a else 0x1000600050001000100020005002700000001000f000500010000001100090009000800010006000b00010001000400010055001c001b001d006d0001001a00070001001500020001000f000300110010000100230003000a0004001500000000000800030000000b000000000027000f0002004500030013001900000001)))) else (if page < 20 then (if page < 16 then (if page < 14 then 0x6600020008000e000400030017000b0007000d0006000000180003000c00010000000300110004000e000300190000000c00280000000300270008000300020000002d0004000500000000000400040012002d000b000400030002000b00080004000300070003000000110005003900060009000200000018001d0000 else (if page < 15 then 0x220000000100030019000100000006000c0014000000000018003800000000002f0001000b0026000400040005000100060012001300000005000100010001000100000000005800000007000000010001000400050009000000020008000600010019000100240007000700060007000b000400070014000a000700100016 else 0xb001200180000000000020000000b00190005000700030004000000000028001e000000060000000400030000000a00010007000400010000001b000f000400010000000000020003000100130003000100030004000000080000000e0001000b000700010000001b00010016004d0000002f0002000d0001000b00060002)) else (if page < 18 then (if page < 17 then 0x2b000000020008000100090008000000020008000a00000002000600010000000100010003004900040002000000480027000000020000000100270000001000000010000000330003000800020026000b00000052000b000000040003000000030003000100040002000d00070002000800030001000300030004000b0001 else 0xa0001000000220000000d00010008000d000600040000000b000e00050001001b0000000c00000035000800230013001b00000000000a00020018000600000018000e0005000100400003000300160007001a0007000000000016000400040006000000060001000300110011000800030003001800090010001400040000) else (if page < 19 then 0x9000e0002000a001c001e0006001a000d0002003e002800000010001400050007000400080006003a00030000001800030006006c000600000003000000030000001d00090008000200010006000b00020005000a0001000200310003000400510000000b000000050000000a000000070002000f000000000000004f else 0xb000100000008000e0006003d000300000011000a0006000200000010000000010003004300010003000700060000000c0001001100000003000000120011000100360004000a00030004000b00010002000900050012001b00020006001000020000000200220014000c0007000800030011000200360001000300020000))) else (if page < 23 then (if page < 21 then 0xd00370018000a000100040005000b0001000400160006000000000001000a004600120001001900320006001600110004000f000000000003000000140001000200000022000100030032000b0001000a0004000000250010000100050003000000090014001e002400000049000900080003001c00060000001600010000 else (if page < 22 then 0x16003200030010001b00050000000500100023000e0024000500000002001900000014000000040009000a0015000b00000000000200380001000000100004001b000000350004001a0000000f0004001b0000000c00030016003100000004001e00000000000a00100009000100010026000400090000000c000000040000 else 0x50005000a001800000003000100010006000000010030000b003b000a0029003c00000000001c00020034001e0003000a0000000000010001001000120003000b000200000049000700330033000d00170000004100000000000a0001000000040010001600110000000000000004000000130000000400000000000d000c)) else (if page < 25 then (if page < 24 then 0x900050028000a000000020006001700060004000600040006004a00000000000100000009000900010012003c000800010022001f003c00010018000000000054001100050004000300000004000100040005001d0003000c0001000a000e000100000098000000120022001c0002004c0007000000110032002a00000016 else 0x40012001700000015000200010034002f0001000f009a00120005000b000100020000002b0020000700530007000d000a00100015000e000f0001001200020000002400060006000400440022000d0011000b0002000f002e0005000100010000000900090009000d00070002004200010000000a00000035001a00010003) else (if page < 26 then 0x180002001b000000140014000a000000140007002a00000005000a00080011000000020011001900110008000400050000000100030001000300050019000d00090014000100070007000d000200000000000000000000000100170001000500020039000000000008005d000100000017000f00000010000100000000003f else 0xa0004000000150005000d0000000000110010))))) else 0
  | 7 => if page < 5 then (if page < 2 then (if page < 1 then 0x5000200120001000700000000000200040000000600030001000400000001000d0004000b000a000d0001000200070021000400000006002300050001000a00000001000500260005000000020018000200020002001c00050001002500050001000100120000000400020010000100010000000400000000000c00010000 else 0x1000100010002000c00010000001d000000060005000300000003000e000000010003000d000400010004000000000000000c0002000e000200000006000a0000000000010000000600000001000100210000000a0008001c000000140008000f00000003000b0005001500050000000400020003000d00020009000e0000) else (if page < 3 then 0xa0008000e000000020001000d00250012001800010000001e000b0001000f000500050008001b0000000e0000001600000000000300170001000100040002000b00180000000100000002003000010000000600010013000500080003001100030004000300000009000a00160012000c002200030000000a00180003000d else (if page < 4 then 0x1000200050008000100030000000800010009000000000008001e00010001001d000400040009006a00010004000100030005000800000008000400010002000400010002001600000003000f00040017000b000000000008000000040000000000000008000a00030002000d0000000c00010005000100070001002e else 0xa000d00030000003c00240001000400070009000000090030000b0016000100000003004500020001000200180004000a0001000b000a001e00010000000e0000000000170002000a00140004001c0012000a000c0001))) else 0
  | 8 => if page < 1 then 0x5000400000004000d00000000000a000500020002000f00040007000100000000000300020001 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 3 then (if page < 1 then 0x3020000000000000076020500000258006a00f401080000020402a202b202c103bb01480086012b000800680338000001f00216017002370271024101090287014701240245009200a601b302630082000002b7012a0158018b0127004a0398039103280117000000ea036b01f402f600800126002900b801590160005000d5 else (if page < 2 then 0x3880227006103a80128033901cb0031026000ca00d402d00130035902b10253004002030268019002a7011800000000001b01310138029002f4007200eb029a01db03c902810231000001b801190215012201e502f801a8010b03d903760311000900c701a5005200f5018001460000028602e2000000000000000000000000 else 0x1a00950221024801d10137000000000000015703000000012901b50000016701e700700136038101f7023203480337017700b10039000000000120000000070000036a0028018701c2000000000000019702e802d4000000000321016b0280003802e603100249035802060327)) else 0
  | 5 => if page < 74 then (if page < 37 then (if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x6282370a452000295c9044d333f00d0a0000000000005d46000000002eeb3097652013e236c125d02f1200002762024420e400000feb3e2000003b60763044f8111068130000000019981fb81a190a5202073d0a71e353a079d930d3681007704617192031f30b3901f04ca4005b4c3000003bf1606165a754ab3450128275c0 else 0x4900029225833e6430c04a5051c05e18000053b4307b1b41139409757319463005156080542b3b376c99000055b71b2b18222f4131180c33155a0e510bf0254a70206cf10000158428d5000004a214b41df51d450b8213c215605c000b00104200000000138951b671d0176270b8052400000000031031b07aa8420207810aa0) else (if page < 3 then 0x60120de9685304a04b84235740b01bf23102485746e000b6048038201b9258e0020258507c6822574667787027c001c84a443bb75bb43a102e90004b3b203aea0572538002db0f8a48822ce253d64373786823792b3026861f0010a326d14ff000423c805fa253722b3b0aa200007c502cdb78f06ff038802f363689480b42c0 else 0x39b0b36000046c742d000001a90000002b527514600752a78a05067019002594f3b3f714ffb640b680025304594045244660b1025c000b74dc463853b570018510a00b838c166fb7ceb26e5000053207282030055a028f8658003306d203e39471514e26a96689000e231f925f21faa2f84644143a00bd077106f90711a042b)) else (if page < 6 then (if page < 5 then 0x36b200e05c40332045993c8524c074955f3b09700000000044b0642059501bc72ee31efb707169120184425b0ca6000015c86e627baa3ce0000000000000000520e945400215000000000df01f837ad266a8545461d44592019831f22d642b8b1bc56ed96a3b418b0487000050301547324061e909c04c815a6b704a2f324984 else 0x6d085a511a8b25172ff20000401a000000004ab4400075123d73000003f632b800000d2b3dd03fdb690900005c46000000005fbb01581db815a2292047b7371800c711150e1a096057f57100000069a24f7b000009d60000730b1b2041027af034a0061931cb242759c000000f205827013221562c06017465705670683168d7) else (if page < 7 then 0x68f919921ac12374161074d30c433d6b639a2c654a673c343ea142db784444281bd141eb014b193058a700510b3b76804bf7375b2da00b181cc82dbb08846b6355930000613700003724000000005f174e070000665b453500000000000050e71e07001057405dd023e847ba0000154b05a07a7008b700801ff74ec108e706d7 else (if page < 8 then 0x791201852b594e9532e83a340115338401070514677a16480e0225a028fb7640281a74f5774009a00e774b203b665fc302a41c86067a674263b916971b861f775a814f4270992d9a46242b6226c232164ea27b523ea060e04d8701d75e1444d234533de051ca28a0739736d159a010616bd417b90e7301b81ce633c06aa11040 else 0x208722021e062d02d30476777520000235262a770e84dc044d83e7600001ef40dc41362252b014263b44d3900005d18713b738a3a5015e2413b09301d9213205d4004847cca3c70017a51393750599016bb63a628d83a123310239b5a092b4211f175b850602485059b28c8004a563117d7270b5e3645c0450201354b6208f4)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x43b500006d35000069d76594102161500000386649c031693b58000002110000023863103f136ab76efb096b381b00001480639400b400003764000000005199276a1ff6295a78ca78402ed35cd6421b71bb2816034474ab49a16a0632b02d1001b236f91da12852419b618149954fa00eb051806790010a5cf829e14c072bf9 else 0x5e8500001b4b14ea00000000668175f925c143910890747a06060000384060ca7998293b76a0307000003cfa0beb000001aa54c2380032d93a55005a5e981f406fdb1ba936921b8552da2b9000001d00736b37374410089734800000535013da52d001e8064478205d8962f00b4b12c6538439326f1a2727000000004af04fe2) else (if page < 12 then 0x7291684807940b5a178801f41d862c355bc067e531425f53575047563c4b7345000042a000004da42a560c0005993712025868a04c403c62103b0f104ef747e2387a20b03b1703ab2f78000040d0000034e05cd0000059405d611022044027b947f6067b531b71f4099b00894d941f1124a23d8b326a56c000000d4350a7679a else 0x59e51d3700002476734003704c734f5b45a0234502512ddb78005b772d2445f772500af92c9b1782377001d25bc128e045b06f014ad43bd923ab13b2212759d204c729f12417302966211f52451a000009e43c1a00000000000037205b703d181d547a9030d05ed93345654436e0483702102d200f996e533b522d3208607410)) else (if page < 15 then (if page < 14 then 0x10a13a90486366734e4817b74d1673a425aa08f00f704fc40000634159b80ab205627765590b003259240000428011913cb023fa000009d204f1267b00001c7703b02b01000000005c5003202010000053e0107100007cf052f0528055cb737b16824c1000004e49475a000000001a707c3b3c203e2a1753200b15ba1f640000 else 0x374000005db900f068b51cb7000039005c3027c4000000002d5200000000679300000000556b59e02d4b392b41b10000000005b144a0100b49a73b8000001637250172000000123a45ba6fb2467400000b93038b334166d5000024fb00007a762d3816523868000034212d35703008b077704861715a5a10055810800d2a3143) else (if page < 16 then 0x21a201e93d1412db40f02d3a6dd100004d011f5916a200000539000056000ee46c06033b05f600005a5b525002204f1b00004c8000003ee650b050f1000000000000000065b8259031c101bb21066371233600000000000007632073645708a37885756a3f6705342ce906516e9749e0000027a200006922000070000000 else (if page < 17 then 0x22b347070000093b4ac75e2110145620000000005e47725818b25f25000044f51970682b15d400003a4a60d30f6300002fa209903a7a64f4756425a416e241093cdb1ceb46047434234b2f627466448a33a050c0171779656e0923655a976880365438e117bb01783e90632400004870319079100a600264050a44c803b679c1 else 0x7120643765f470f401a35d370000000000003944533146f400000ff6020002282dea54d717d8286a0000411008e0012853a574b40bb0566000003a214096536048e709820000000040aa000001e46f604aa7000001ab1112000008590fca00004bb068d16f933859000000000000000034eb42fa5dc02288350a605042306241))))) else (if page < 27 then (if page < 22 then (if page < 20 then (if page < 19 then 0x37c93f603904608648775ae03cf07aeb66246f7810d54db468ab248132115870740404f500000000000006c9000064a46df43c905df50000704073f200004747035400000000000057b019803ad01cb322eb000000004de04d744240000008124c9071350058477700004c27000074ca0000066a55c0547b00005e3009b07a52 else 0xe593e600000000072a0000000000000024700007a7133590000701038c03bd70000516008770000000000007bd901b500000000512500001081000000004f416cb050490000000016c6000041a10000000031fb422371b04df928325e6a52fb48074d67468728aa4e814eb8619513f24b24527044530000458219f467da3f30) else (if page < 21 then 0x212000069577b7030b940837b307300113400000000000005bb44a200004b90526b1e3852207bf414c2152b08c8013b42b829d6391a078a77f0194a7111000000003be00000327051100e90000044c70000000000002ad302270000000012fb528b47d6000008712ef25ba04f0247574ee100003f9457d000003b3800003830 else 0x36d02a0a798b1ea1294831f53d701e7021575ca5102035761c7001c114c03c564b641602489420670f52227b57302d166d4600003071744634b60000415b00db00006ba262c01270380b1cfb6dfa4b30698917c930cb19000a25175b52a455170bc93fb579253b65130001b668495ec07222000000003430000028903d200301)) else (if page < 24 then (if page < 23 then 0x54ca45d0526120614270068b3ef44e50012177203a6b429067d845606d1931912a6221cb40b1311162705d5046602739000043e12181264a737213092ec001a14570417b0af0000035a058d56cd8404148806eb031f40e2162b0413070905f7b0b7501a55ac0531032917ab467702593421042ab745420f9688736b0635547d7 else 0x55b4600849e7004052ca7bbb05d210c92e31027452875ce16320709426074844295928d07506479664142e8060781d114beb3dd270d40000000000002feb77aa00002edb0000000024a772f000006b15000061bb03a5000063e83bc900000d3b6094000031212f07000065d0000031d0719b49f00bf941cb024b459064820a99) else (if page < 25 then 0x4ed032a73912000027d200003e784c840000738b0000000000005af0281849320000000000000000319437c807053b9738a444d450e43ffb2a4528a22731000028042134717543b014694a641fc5358277f70d9b5de50cb14e754400032956e07c401d58051309101a3408302b243b485974103a00000167000013a2541a7600 else (if page < 26 then 0x46e75101231759100b1a0000589a00000000000033a3225966341e2b3cf9011165d7299a0a91508001e06a72000046b74684000057ab4746023b28ab2eca55fb5ac700000a4b1802000045e01b507be777b00920599b14267b0b28db37c012d94d424b4052c018f263e04f21353a19e7160544b11aa82afb01402e4254913ef2 else 0x5b1900003b8a28d361d72e8b5ebb1bd244723490326b2dc0514001d1789656d016c253c7000062c617720170027079fb3a012f900000095b28c27a81000078721b9044d072971cc45ba17ac90ecb38474cc75b53395b12a000000c35000009d176d5266100fb000059824150000070d06ae0074901d521d01dc63640)))) else (if page < 32 then (if page < 29 then (if page < 28 then 0x72110a90000000000000610237d75c20000053c0000052030000367900002bf439d00000000028e45c103400031900006d7b12bb42504ee600002f59000015f400006a6569b600005596308a00006791000051d0000000004b104860438b0000000000f50000594b540b6f3425e031770ee00fb034ab2387024170c000002ae0 else 0x4a22229a0dd254202842789163d76a1b1dd74991000079325810617a24b54ce0008a39640000000021bb01b9540037eb0000000000005b8b09c9024a39f25a430e6231e073b8412048f47c7904040c6005a200a01fab02e16bc6000000003e5078600000715b00004ac019a913c062e35ab00a455a1b456859f0478b0f79459a) else (if page < 30 then 0x7544000058f04a30188217b83d9a52403790548873a57ab81f4b78c03f5806f30290000067d023252eb3590000001e424694336a0ff71fc459b0000000000000063706220000739b0000000054e24954000036f8010b1e8202eb356b5cb71f0745c4586029a1000000007830696765a07bb167990f643e18432757e2656013a0 else (if page < 31 then 0x2c846d2b62d800002194007748153b0200c122d1212612b017422047000040ea1e5863374b3400007930697704d45db0558b3fe9638143fa00003d243280370003571b5908d054a777e05bd01af431d16dc04b50000063d2016072073f06000775506aa501041aea561000000cba6161071920150000777b1365089164451fd7 else 0x64330000344141f94a1057107cdb7a80000000004591667628ca137008a000000d60627400003c00323b3044503b58d01cd76f6159f7030b238235e235f958071ee85070198b67aa348603962a795414310722bb134058b268c05d746e5000002a113d503c553f460df21d62534062a00c0900c54a576f0027840000144101da))) else (if page < 34 then (if page < 33 then 0x21db0dc3496428b025e241d1324b32b9000075303d6024212d2804a170a00000181b1cd37a205c3434c90650478a08140000217a0dbb0000035001b10000328102f93b7b079804b61f706b574e0269992263000046591a9b12d00401679813e65f664edb42e06fab5be12be24c6017470da037023cea4aa4518737605e530000 else 0x240700007b900000780b63162cf2598065c76df00b49000031f01d1830e0349951e405b04e3a00003db9000039e7408853021ad00cb54c5402aa00001e79000002e0486949505c0634da1376365922a91ca5001b0dda38585f055468457a000049a53135000015f7385b382760d549d00dd1000028712dca66d01f2b47a74fc5) else (if page < 35 then 0x72e710012f79000000004480000075720000000000005c2a000039c73e3000444927201224114e114bd07cb60cb013753aa100000ef572890752019601a2000040c00ba200000236033400000000000053ba397800001a27000052810000000000006423000017cb195a7810000000007c375daa000016b261100b99529702a0 else (if page < 36 then 0x7058341043a360c4769a6610525474477794388236277aa4482600d9151a104110e64f9b32c734b3378440f146d177d06867000000006e103220461b2e71300b23d824c8572062c100004c94202b0c9a44183fc02c583d404e100000000038d04e003a923cb47b4b781815120000557700002632797b00000bd960b600000000 else 0x23040000039841402ab70fd00000622300000000000000004fbb62a66271727000004a7740ab01f20000000000000000054b70ea00000000407215826c5b000010994a007a50651401a62450000049b026981da0134914121d7b0bab153a48b44cc5205b05604fc14b00094252aa02506d046d866c9b419009d51a02485a0490)))))) else (if page < 55 then (if page < 46 then (if page < 41 then (if page < 39 then (if page < 38 then 0xf4044e8606a4bb47cab307a74126fc11bb200000000000000003891398200005de038b1052028596f680447000064e04b97024000004d802dfa015000f706f16c8070e50057583b453036d202e711c57c1022b602c834700000000009da43351f6b464706017d0a1d04000011b1313400000000000071cb1a606dd039c027c1 else 0x1d900000586771a06040672176207b9705490014163b526746370ff8000077d20a3609b91495352002fb4ad55f680bc020a54cc17c644e2b47da6a61000071e94b14247a05e54851000000414776515810027b844a0726f31678000054703d373af100005ee0450073bb6795000000003db85bd901335831000056b0000000f2) else (if page < 40 then 0x6a56fe16f70150b04e04e8010277a6069131910436523f82ac50000223700006de048275b9000000000468000002cc0477268b062986ee85af415b700004fe91c935a710000321b3a6000003bb51d49000028a57b8b02c209f214f702f02fb404e71242079a000051a04f032b8334c000004db06a5a14077c22000000007730 else 0x244b02a30d0b1af0308900000000156271740000000005b400005b47553b2c8a5a6139b0651007eb63453e2b0bb92aea000068520cab07303f3a47a618620863561700004bc027f75a90144b00000af70000000019c61452736a000010180000005077eb5c70000000001bb0393a00000b093eca7a966524687000000a020000)) else (if page < 43 then (if page < 42 then 0x211961f8000b6eaa6ac43f92330102860000000076b000003d0900000000000000000000009004620001060031eb00005a670000000000002f914ad868d25fe22de062e700000000545b000010003ba033b0091a3ca818c204276ac002c758a0497443c042c116801c6303847c78612b74670ddb3e521ad27592000049fb0124 else 0x147b05b22d70708a351b19b2199643db6e043a816e5b7cd650e04512277b00596c270000000000000000000000000000012900003be1251000000c9839d700c06f801c97593002b153472d400000000009403a5639560000000006556284014501c0000000000000595a00001d2607210000758414320ff036c260a141804170) else (if page < 44 then 0x338389a000033300fe7228628a80d1a29951aa0346018f72d0567f02c593c2763f7281002fa0e7260240b465f814c722759502167b075b657001f3b76d00b1b26ab0f5748e40fab7a4348144cb143051c0167035cc516e932c05ea370981c5439e83d945855000000006a2641e04de7638003eb75994840490728b265473030 else (if page < 45 then 0x4548000010b5555700000000660059ab7484355900003a304ca3031161d0052163e674e406f471a272d076c03da240d42f024922706a72a544901393715013526b4152a06cea2d42752722784552698b673a000030321b6076706c461ca90000000032026ae468aa06f0361904e63c240c21187562e6000004d05ba750c81507 else 0x1b7000617c2b3c106e496e3b67e41f8b702a3ccb166237973867783a77c7072b6b7120b9514100003c1400000000387166402203000060c20a191f535ef500001ed03e4b000057703d343cc0090043312595310100cb309b68e200004d5000003a3831f80000000000002790000040c1246204ab291200000000000062802090)))) else (if page < 50 then (if page < 48 then (if page < 47 then 0xaaa000000000f955b3154b700000000000047f728ba000038ba6ea000002794000030427b1402331ef000006cd010a443f0138b410051b05b87718000007a1b7018000004a90000512059db000000f15aa0641233885d0a262b6630128008b1693738102d33000000006b8b75c407404792562b0908114700005be073d9569b else 0x306013802dd80d7b6287000002823ec341c03865000000000f6028c17320735600007081330050502513483b717a31ea08da11a7000014b36d5b00006361325b00002a9121350000009153f063f275d956f02bd245100be9576060f04a8a00000fe16f423e4909d017320000521b000047e70000000065b40950163800006eb2) else (if page < 49 then 0x9f000006ec331a0679704022a8a000012c0214711322db03128000000022f85497036f06bf801fb546b132b4a912ea26e1837fb139002b03f483c4008d5505403801702396028f95c4548765c693c604d22000065341a5a000001010000000078da6eba3b185b7b70b06db733222968023052e42d397190000014a07324 else 0x33ea69e4533725b10a65500954366170208b38175d8177c044f040eb7650619076902ec4118222c770f033d051e04a2423614c34195827171d702fe005062f70197766e04866015944140e3952e22fc035c21d757555494307d06b7b022a30ab0c1b455075793f184470443061690d1b6e23112431c0297a01a4000000004c1b)) else (if page < 52 then (if page < 51 then 0x3e92552600001aba77a011f206894fa179e237b0399010720e0707503f70000054901be7102b6a40000000001592000001794ed736fa02672c46274a0000613468c366b470606de2196456241b7200000a9b3eb2591b2b170239481866e60aeb4cd06cc037da4883000044d95ff278b00dd013d746b402840278023434160030 else 0x1a415626009800000000000000004c5078e800b00000434a29b10f8436ea352a6f92000000002d8b31db323000000000000000003f8b259200000fa05da018527ab0524100000a460000539545d700000ab0224508fa7790054672db000052b400000d841d8b452a4980647151ab615135d90cbb70e02fc109d914540cd50ea7) else (if page < 53 then 0x2bf506bb5a0049b73da014960b254513009b016b53fb4c6716771c746eca294104140a4700000c200000309a000036e23207583005821b084ae746c06034625b3f614f805a8700003dc8282b079915c0480a785076600000509067fb00000130000008c0774400006dd860eb0000000020606cab2f670000000002624d5a0000 else (if page < 54 then 0x73ca57c01640199731fa74554da12a25258728207110002829e5023704aa6f2700720c734cfa1d9514365e2275013420784a321540900a4103773ab037e01eb5082b7aa057a028da67060000713a24e96c7b17230000000045f100003e1025db5c1757db5a57000024d214db27420000687359cb000034297b2b610a6adb1310 else 0x1f274df0220a79002849689a00d16b9b00003edb51fb003837011e65000009690a402cb2000014a21f9950f9000304b37a77000000003ea862630000591a6d61000074ba3641288469fb0db96abb57f038f2440a16490ceb76e071540000000050d0727a00002d00001916f202420000498754bb00005bf076f06ad775d03951))))) else (if page < 64 then (if page < 59 then (if page < 57 then (if page < 56 then 0x63130000000029810235582000006530134b6e84066b0000000061431737147936a01f4439f00000000000000000000000001e165f2000001c22431b2c0b5f4752d466370000581102b255e45b025cc03a804cb05d25251851cb5680406944b2251101ca72356331754866a30112530074a53f2b18ab0c50122a60901b3061a3 else 0x66606eb36060000000001fb9000037a0066810475d23483a00002d3660e44ba0019a04b4000004cb3ed000000afb00000000000020f70e42000000000b210000523b164b64d4000029da53907a32000077806e2b2031308161e373e500004e302ae24cd417aa196071401ed600005ce000000000157264c42f375e41101615a7) else (if page < 58 then 0x6af53080485b3ae051060099000000006477715701b00000607544d101e200c32bb237b974035dd80141018348a059154610788a4ba400006be75f410000081b00000b05329007f100001ec9199000000000753500000000000071f0286400005a08060716221da96c145379473555ab5bc73d8646f075ab39400731079b4359 else 0x749b776016d2343639b33b27472b7ccb261225a353e20b61222b4b70288a30f03ae845d402b928b1121101365842000029f020db452373f04f0016a05c85065847aa62044dc60ccb6540000054f7124a1c5b6d9439846d18011b7743000032fb0000000061e1142b5837621863012512326871da00003a0a00006bb5650065e0)) else (if page < 61 then (if page < 60 then 0x3af221075b274fd0000001ba02d0211849b166b0339023b02fdb780a25771e99516733404e7a27a7115443100bbb4da0327101f74f623d364e600b277a8702790164033720d372e03aa23994021b0ed07435506b2e2a44e075a53baa302b640a10104c9751375f143f00060b45f06e13347a01970fe0532b1d3a49f7 else 0x38f057807474726551193319038a00541b6200000000000015d7569073db64360ad0321a22f60047000000003b9558eb000000000000084272b600005dc44b0415272247682a748a39a407391fe46faa60a061176ed057410d5b00003fbb432162b14e544f9a5df0405a02e21fd64584676602a20e6a04100000038100000000) else (if page < 62 then 0x804245637770a500b0346eb18465b93036000004ee342ca0510427b5a303fa2717038b439663a7054ea10f536506da01797536b396777c22bc52c274c0b70684160125051920f475b80000027b43af7297051d121d36a5663c76047444505b57c8a0430315737306f5479ba3e0a5132523a46403b451c1269480000443b6f59 else (if page < 63 then 0x13a00000000000000000000000028d26440574734d0023101c632505f65758a15e55d605790071237c1675b000000007a033f200000501703c76ec602bb4e70110900005e0b5118166029f2189250872e593ee11bf100006a9a37b1588b7c9129ca384b77b41ebb12010fd20b010ee200004be800002b311b40000032a06e64 else 0x4cd735304304296b1712126b35bb12ea3f31366249131570399116980c5a0b2b5ad05448742b4572360236c46f8833e0318474c5782558c7377459671c315150514806e4560767b12cc7742a2a321dcb65c066c655d7435b1de733b30f0063c24c3b24010c403b0773e65650140a78f802261039000000004706003664b00000)))) else (if page < 69 then (if page < 66 then (if page < 65 then 0xf010c145f9a24944d4a1c0261400000116479a675e136a100000a800cf04d7a000034f00000131238920000761020c10000502900003ec61ec2657726571f94721643c71d2b18e21b1507cb44ba3ac256d71625472a21100e87194824b10f285627683028cb4d6017f76ea21179069645a86689403106fa60b43e800deb1650 else 0x2f546f133eb315cb33f6039917e425511017000039702c745a174ae000005ee871300f8037ab5170000029a67700116019d556143bc80000015a08014a4062ca787734403a426b814d3140ca6661371b078237544766726000003e3a5bf71db10248000038e00420698a6717018000376b207d1121c3509105326c3523c03b70) else (if page < 67 then 0x401b4651603034c11fe502a1662070d3716013b00720702b451b6e704960476a0f6b65503ee044da01101f3473cb07b3423b6c6346b0133b1a80088006026f764461018b00002d29000000003210246b2e9b6b0258c07c0b596000005bb000001f20544b000000001ee100004db75a7437800000033a512154db00003a47 else (if page < 68 then 0x724036342e6b5e78000048455cd7065258003e81039502c074eb11e31f16221609e30ef125f05fdb2abb1be5588011d13df04c6403d45a2004b02cf9007033383c7a13301c1b000025816a8b4fd52f22183202d10000000053d002c90000733216f74b7704006ca911c743445890298a494b047002610c803fc627ca5f12 else 0x5b6001a03abb00001707087010513c304b80161b1d0927e90000305b00006f47000000002b793bc749b635425e107178623b28e82642690814161bab214602016351148246900000223900000000795b319246705c805640000000000000000069c5340134b00a7b426351d80000000000003ca000002aab00005c5a39aa0000))) else (if page < 71 then (if page < 70 then 0x4733153268c248c005160000001a0000687806f2646761c070a46eab371000124fba4a70554738a0081a557b006062900000710266c02ca5222100002499645515520000517700004a900f3000002df24881528400000000000030db6124723014d73dea4947390b290271c052b76862724505c950aa52600071010930102ba2 else 0x24333920000037f0000047c44a37000034f921f50000052300003a2a70fa24380ac44a0407ab012268b44f0167a054303200080a2ff0380772fb06592e115f085a402055449a026b023a000061b01c697bc2040b226517674cb5055772c000000000337b33d83b4003405f00550528772b9b129064611ed966076794649372c2) else (if page < 72 then 0x2c1444a100000045000000002aa7000053566ea7258028397070751b0000359942b600005aab32a91b144b5b1c80012518d200002b9300eb2e0a320146a0000064511c8b0ef255872d2b00007a6502320f2700000000000004b25adb74d947e6216b1b3105500000678432d03d0b51e572b07b6b00003af45be704946efa0000 else (if page < 73 then 0xb1100c200000000070b4e6147c5794a71320c6226bb0000464b678000004dd8256446205d9520143a221f47000062f21200000068324850450b00005d7060d80f8365904c47385763f1640000000b2056a0529078540a70000046a41d66402a0387000067c20ae72ef715b4548b0f3448d0045a5e550a443837000000001c41 else 0x5f552be0587639575002125b01db0be06b3700000000000038db00003f806f84471b28c074fa103024450000000078a50fe262e06693782a33500397))))))) else 0
  | 6 => if page < 95 then (if page < 47 then (if page < 23 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x310b087a978777bb2af033181e9005106d40096a79c084eb0ce1683155e703a7635038f050861a128fc465c6021678f68358000000004b94000000008fc800006ca407a81320155824c000000000000000002f6054c336970000817a46140b827b800d5b933a535300003ad79bf02a7b52f009bb87203d1254d57f38 else 0x7e7a8e3a295a20a633939340645b60a000005ab933c0221b05e87cb000000000001b2ba200000d3399b00000000070900f0b632925322b2a21a951b7000000001d3a3b4052541bc0458383d478240bc006f43c7764794b0213a32077416b297b3f135bd05b3a522000004dc200007606000000007241183200008a403a6921a0) else (if page < 3 then 0x78468210489047548dbb325b824000008e1a346246f66a5b84e3000000000000811a80e14fe00ca22270842b88f074370fc88f5455c09a375b4344120000436b9b840000885400000000000088d0000000004dd9174b957011203268000073d00000495070655d6b0000906b5b003c701d3124c71b4098c010f464265e300000 else (if page < 4 then 0x342000000000000000008b0000000000000007f03791810200007e2256335bc00e5978b088e0945a3b50062b8f5a523a6529000009503c688a5b81ab796800008d561986604436bb1870000000000000277a00007f600000000000005cd200003eb665e355410000000017db80e9830601f40d77371a51777534643414b90c1b else 0x7597281152a009a075e101743ce68a10636837257fa0722058f66fb006d25d9590f57f8200c136b376c80000459b7e4200004f200000000000009a89000000007d3084b3000000006ac80000316000003f001607000000004d4a20c86670035721c0800320736e0580402bb55e37010097502c4402384b0006020196997b0000))) else (if page < 8 then (if page < 6 then 0x3d6b1ca075e078f04d92395a02e11ce06ec895607ecb00a45d306605391212c816f40000189023ba799488008855439044624d3023f0399b00007e6a12eb504293903aa000005b618d0015710000752b73237a8051c00000011a0000706435b0027776080f938b0400002dd300000000000015926fd550e16b107dab2a841eea else (if page < 7 then 0x15a31d513d591f524e00477067d75d90484094e7839859fa3d5028a202d603113bb053b050c60f7800001efb692600004003000040a4060300006df80752978056e01c21288819926eb71ff9000052f5351a2a2a5d1b0c635fb24b115ab001d36da0364b00004f5800007ba300618b233b021d632ef2662314f6000021377c32 else 0x8cab542a54a60000621742a96c67000050ca3dc0484b3b7215661d020da390d08d1258aa000015d07a7900003b70814576f9655009602fa015da3b20733424204f7034705083009097e8000077e08eb066c581d664966c5a73043a70012331226e586700520742628b7b0497870035525e85471468006d9069db01795c100147)) else (if page < 9 then 0xd3007426ff462d1947009434f3080f091b0417a00005f80000097103f066f9761b34231411102f04be89048000055f025f46039869277327560406b8730316102c96b7b542054e585d91fe5208639b138c10d4b70943d401c2a88c019d0789373d460e0432b93183870900083782810000017e202c411029d553e8085307340 else (if page < 10 then 0x255044c0774791327d2b000087800000000039257f494c403c500000064093a0286b226862e2000016770c1425128f029a800cb04d600000000061400c027f005f220e009b8a20304f80394b436a00008a24699020d41442468672d432634a44285000007e5a639786db32274270322a000011b609d58ff227903a8a26b43920 else 0x208b417100005ec31cd005594a9000002460188315106647825019b8863b73430cd40eb663c519e079440e30826a89828970189223d3847103ab14543ce043b01bd007b94e6015590051000000000000000000007a9025f1390a6010241600004bf50d2005c2000047f390ab6710852000004ca900000e61000022b082204edb)))) else (if page < 17 then (if page < 14 then (if page < 12 then 0x6b307bc3000033c8004010c074902f3b1e66877200008f640000173300117ada909669b0116b60d7224068e088406cb091c06fb448353ed96b3751d051494eb0850352c252112fb91e37132201a1500b5c3030207547269139a001f72ae091b167436de8006344715f1428624cf85a0b4a780b489d2101aa5eb79c0024b36067 else (if page < 13 then 0x478443c0000000000339000089d6355a32206de671b43aa15cea00007de000001d79607078a16b8a762a4eea6024024b5cf2408b0b435a785d489b6889b60000836800007f160020459a75c70c3b55ab654385b443e972a2783559cb1598732a6ee05ec04b4a6c73915600000000413993d03451763610503e6281633cb0727a else 0x80104b310eea4340117900006cbb0000000033f000004750891571b012f806ba000084c13de04a2002b400000662000067d06a6017d0896a714786e01710896904271e50000089c05c860000000000004d00084000002f69000027f204eb18f96389716651082d07000073f06e404a7037e00000867000001ce126e57930)) else (if page < 15 then 0xcb395157faa000000006460000031d4000021505e500f328cd515548aa6000000607a841d5a375b5d4036f69b4703c04d244e9a3ca1000015510000814413a00000000000002cf40000000037e100003212952539740000000085105fe4498a8799619160c0000063768f224cd41e8926715c8202610000000057561acb76d3 else (if page < 16 then 0x51b01f875c3a25d05bf08e2a11306681049409b53e7600001f408f806dd800002900000000001fa50000000096852c6000003d79861600003a90000000001bf337d4000052b02a1b000065e09d348d8b07901f504e320799000000000000000038280744178b8ea43ffb1140000097400000319a6ce07c703dd0731058670000 else 0x5e3b7b61983462372670768077d436940a491de53cc00a2042550000000069a020ab374300004b810b6a6fa065f0000089a0467b63845db80000653416a77b5815a233b01d647a51000023b9071400003010520001386ea2925038735416426095e22ba5703a3f0308c09b58000000000ff49864000022d07f408dcb2af412e0))) else (if page < 20 then (if page < 18 then 0x50d200001373000064a13c6086180cd60b208770058431c039340b7b166745a06cd28c3132771638669a41193cd937216d503ed03531458448b05c7060e737c04fe99c40764024ba0d9474f716303cb47ea013823c37477700c06328530046e400005a4b040332f73f90702a02ba850106511274232274d84ab03e2088670480 else (if page < 19 then 0x77a04dc8000061412f371c3a48048f0a00000025496100003c00000018549c6b00000a7027e06247938569f001a45c6a1f8a00009d202c3b00006c97601700005e7500000c250000425013922d481df00000771a1e4984c541d00d9a507085c02ad0000046e029568d47772063244d70000052700000481929f72e204fd28874 else 0x72a849f03e998760993a8b121707000000006540077916d57eb8071b8a00401001e68a4800008fb89a004f3482240000000036296f7071a442909b280000109b33b111d46e608d7867f7111061aa1c4b00000cd52dd0629018530000007000006cb7000059b1000006893f8769e072654ef011fa0000357932867fca6f4076f2)) else (if page < 21 then 0x6b5016ca0e8444428f9098b58fa05c6251e5000055407aa4000098549a6462e76d20494417f053f246618fb45ef044708c5340e62d869cc200153aa54d5a69eb1a2061ab5b797ae60c560c477cda165010f066137626520148950a600bf0315028b030cb63a21384904408b10000520b123b707003f286906ad7134255483400 else (if page < 22 then 0x184019f482173c8a343067ab356a10136a388c35000095c06780241a24d2852a0cea70b46e6689997a47474a6ce47c1b03f188600000873b8f70910681147e904ba22bd4995444b98d06744718a15250979672038b7011a219b774ea197544b41d007b40436007b0472b09c06fc046c06040902a390b7c91882300107c904c62 else 0xc1038db000000005ea1673426966ac01a60000044aa756712a1044300000000256a65614760000073e2000045b56dd50cc052a52f802646405095886beb94fb76389be0300004001952635161c0231b5ad134993c40517801508bf380720000397a4807025b96e0332695282f143e188e00429a5d6a98814e8475f090048505))))) else (if page < 35 then (if page < 29 then (if page < 26 then (if page < 24 then 0x26c21bd14c002e7000000000351085785ee300007d2800009430664b26047735000065859cfb14d600001b302e0a00002dd7000000000000418000000000000080179aab00008683085280b016a100007867201800000dcb728060800cd32bdb00002b1030b80000000095e84cb01396000015a63304366b7351000085c7 else (if page < 25 then 0x6aa047572d5545014c3100006d6047303f823280807875139c337f5290e071d612aa8c873b9042b06f805a8100008d308ff03a340000232010707cfa416a000051542fd033916d1052c714a02df65f50000074100e94557016e900005150765900007420075600008cb07bc24bd451da0000139a019335f02983000070d50000 else 0x724567201f6928d591a096a3245a46fa36a0383b83e90e713c2678b11108486093620165091347f822380e0b38f744a00000238a16801d8239302110302637803c904240286a0ec0196062a400007e8186004cd88a350000000087c01805769b00006396000071c005fa00009830000094505b801580389b6973001a4159)) else (if page < 27 then 0x260a469b0000000001c08c206c3000006fe0000027ca119a33ca000078e14d51598756c696088b34029b0000000049a600000523394100000367648400004612974736ab68104de099687eb34d841ee371b1709a7540081a59c0000044006df90000000059130cd120643c745f340000296b11520c94505012180bbb609008a2 else (if page < 28 then 0x41f08ee403b7696019064ea00000000045fa708b8f265be50a1200f033a146b04b807c5530e023e03b5761074ef40ba012236f2092210000000008a300000000000024a65210000000009771326083f669c15f616b57776024ea4f107eb707eb00004146000003e600003fdb7d266e9a09db24910a5934d470f2000048805ff8 else 0xb1049575c2245e848ca51400000959100001de800004ca044608a430f6000001f2053f4581007e00b5069780000882438f49d1a738a81e712da2356000000000000000000004e147b6001f11bfb6a423af0650000000000345030c04b7254b4000044db7f90087200009790000039f06380993000000000506000008d9a0000))) else (if page < 32 then (if page < 30 then 0x79a000000000000005b00000393293e000005c608314023a84a59200934b3f2091918ddb069b5fe031f128a390105c0076763132000080339210103871d47d342db633098a1109805d9837070000000000002b333c69000000008a420000750199e436e57730813522a097d27d936b0061b600000000903094002cca00005c80 else (if page < 31 then 0x7e137e4046f030774dca4120809048f061205876093a4bb038825268474000000000000000009bc40000000081540da02148000000007d85000014190000374b000081c7549029a007d04f441483000001211b5076465275000000004df0691b4a82162059d893701c551154526020060321000084d898806b4b00005a13329b else 0x62b02958419127b03a7b407075043e3054525d147610644b912000006e8545106fa76a1b00009b742a3011f256fb713323ca156760165940434343f37dc00d015ed813b0444a5ac05e5761848c1066201d8009a78ec16a502e804be28de0443b428001ab69ab4e918b6000006fa4507476007f802b9a5110403020f268800000)) else (if page < 33 then 0x8d803a1165d07c330f3120413e82000068b000008d2a1d7b3dd427501cc30000000000003922000000003e5100000e39538b000096d67ac65bd4506247d0504097201420517b0d90466021400eca60d463389054874062e0317a71102c17186124f1089241bb66409b3305db41e19b06000032b0001835c07b3100001c7b else (if page < 34 then 0x5809b381077599a1de10000000012586f90653000005bfa40db396211da037302408bd05217195005b2125b25e65fd490507743569013e07d6b8a84736a0320637765a188d16ff023c90f063731016219762bc348e456d10000000048302b2278a05aba51f065a0737018d872c028924c900dca1dab599b80807aa850b03e09 else 0x7ca054227507645717f2120b49203b3260b07ab2020b8ceb42e097516ef55880404b9a3247f095b22a92000000000000000070c24d835d706aa4089a02708b892e1021b034e70782482009d492d000000000000006db00007a10000000003c935bb32f208f634960000000003fb3000020609678000000005d8229ba32d200d9)))) else (if page < 41 then (if page < 38 then (if page < 36 then 0x5293327091100ef000002db75796298b7c0b00002eca5c691e2497a00df05bf261601692026054294f596905301b2b363d4865e900e079d155f400008a063f705350517023ea23d05f10701293d77579000000004f505e400000000000003a004da142a095506890267b68f07c620e14881b000093f4000039d131a8000000c7 else (if page < 37 then 0x6c90323300005fd70437009263d8947421f05d452e306c473f610d00930832c88ba67210908506eb54c01362199009da4dd815404c967f9473b697609bd329b76db98423000093b045400000748000000000000000000000000000002be00c30795a0f61740076b15a1000001a8b3660000068b724c1000000000000000020b3 else 0x4b88000000002a3b00004b901a52074a2c2018b019322484000000001721950875d37fe24c609564840b0761000022c01fb78e897f3401b010a02ab1252033548b9400008a5a738138c96ed5162b7d6416d099f325004c2017a0597410b200002ca92c1b62c00fc901b242f0493042425d073ea473f4153178901ae08a317510)) else (if page < 39 then 0x8c912f7a59963afb84f4050000002ffa19f0845a00004bba000030400000733218c361106f87000096f0000024666420954065212ba01a3060004aa06d9600006667000012b48e88000051968ae3000053d498a041902c26000032c09cb38a29000061902b903ba96b20322174305b990000000000004d567d00000043630650 else (if page < 40 then 0x51600000000000000000000000000000000037ea5cc0220002d1000000004baa000053e37c05242274b0463064e70b4a000070606c5800000000000000005280014195100a4084f04d405fd0000000003dab1611000057a03f9637a0129a57b54d50957a5c581fd659846cda1319336264408281270018aa000039185f980cf4 else 0x8f007ff5495447b7663292f37152213358c4454167f05b6a72768a341b00865004504c106da402a269e575c0331040270c607a601f985c209582889a09204e332f394cc41cf228a400006a8b4ec34ad01f7a8ed8691068d300005d4a41a00e600000562b52c00000000044d015794c8300008ba1396587d175b1452b84d00000))) else (if page < 44 then (if page < 42 then 0x8fb077c675b095b82be560a47b461e80714052816a94179b474278685b3903e315292dc15e4481e073c0531481b07ed6462b49bb1190865287248a282f9466509c97393337683f163013000054f5052100000e09000042c03b4776780000000089400a615d424d149a237c3045c774e277fa3ec951911640829660f43a972f3a else (if page < 43 then 0x2b0061292403d20855307a4672602586bbb126b8620085a4dd300001da002437c85182938bb00002ff065f63ad07c840000000029408fd08ab217635e2081590ed06d046f139b1b00001b803fb05bc263402e404970000000005cf700000000000000007cc468600f4000000000435a1fc85d4105ca6590061038b173334700 else 0x15e851c773b0737292a00000622000004fb00000000026937d122eaa3fc064e026e0184269d05a6b51810275405b0000000000005fa7000043a439e0732078e04ed82de92b0a77b088c50540782256c03db002211de004d05b605b0b01a300005cf033b7000000004c507fc2000048d4158434827a35165100008ba701e82db0)) else (if page < 45 then 0x4e720dda67509870666039b001107de14774412702308d376310574639b5236251a00cd78850012b79f171278da71062180622e08a013f41457b6e541af028364a500ac00e5b1608393a49680000000062441b20292a99082680566b01fb00003c170a76864089105a3a0e20000043a97a302d101ad2000074f40000769380d0 else (if page < 46 then 0x49eb86b865466bd4582130d67537965743d04fc071d7876503f030293a1001b12e7142108dda17705d55513b74f03c3091e010e09d70774894a27ebb383343802c9208c10dab56517bf63ac42ab319e7448062113ef02f903fc113c041f899a38bea4cab9770490054504c5950476e7789505cd13a608c466c41263b15a08456 else 0x560b09051ec040b06f7800003cc744a200006c107a508803731182c227706770000011c2000000000000377a751686c880c01080181400002bd700007c4b108a153006c94ca344950000000001880000896000005340000044f00000000003d4669452f109eb352318e26c12589081624f4b0000003015625dd05aa06d707920)))))) else (if page < 71 then (if page < 59 then (if page < 53 then (if page < 50 then (if page < 48 then 0x844a85e612b26308532b3ea524b01a92941000aa00003bf500004ed1000017c945a29a064de17156390284315a205028613090e7048b71c14e7049454090133424424c3011c64a304e103f1005822a498f603ee75d0223217355102270733410944a023b00000000000000004ca475d0905a5de781102ee038202e904bc70000 else (if page < 49 then 0xb4b1bd7489123a66f301bb0291021210fb75c5004b27312387a358b02d7161050204bf08c4a826441d257e024d41d24546069497bf067310e8a2de476f453a065d4047019d285000ad872e221886654106a05a66a70645036c3000000002c1032045bd35d2235aa59f22f55000089a75c872b02920b289087071dd230576f56 else 0x4db2299a265008c36740001246d06a2b1df114700000933b2e60166035ea63a7926007c03c56074b92906d3100003c102fab0000072b670614521360618039c42df06dc642b194d91f134f4071f087e066b64cc274140000000004a70000017800008c064d2000005cda4561871000000b4202d030eb3d107c6340f168725035)) else (if page < 51 then 0x5523511189f86e31182b3c801f09895265b196985a277f7064106ab421e45034692008f372b40a0b412225b70e105dd7093213f8589a491326846840249b4aa92970228166f694c58b8800009a1553f02d9033404d3380f4234944e05cf818fb01eb5e718fa8545a35e0717314d564b3361443ca81250e4879d08ad9190507bb else (if page < 52 then 0xeaa8f92384028c0643028e27a00239864c05c4018c42ac01bc28258651599c11e99261b06c6588839630000948a62a78014559b662132e002fb36728b7a5f3035d0720699492ba64d6151906e70259700b089e01b7b3e503d80214119171d9267e066878a160f86000000001f006afb8fe09ba219856a7b856b07009b40905b else 0x216023a491e98a7689f239f10c9a4e2a6170318095f2143352306794467030d00be186304e9569341057357194b035704b53556368041a021324000006208a200000824454b0884b49181d9006985a701010359b0e9100000b9502921eb761e07ef8029316742aa217d9864a753067469860413095d9276059563f7601678cf3))) else (if page < 56 then (if page < 54 then 0x9a480970468b5c9000d10a5b8ad8815800005ec82c725811000000008dba6260316700003a30123947d453450aeb000002bb31e097b1000000000c75000021164e0b7af1023979b80000000094c90000000055371472000000006ba0343900008e68377678202804669069402c5077163ac000005fa000007be400000a507772 else (if page < 55 then 0x3bb200006ca071670ca687027470000000005a5a081095115472231021db7a939ad0810059e0229071465d040000000000005fe84870577003043d04000000000000000000006850000001f9831001e180a0025926923ca000007258217000005f4400000000350050802e5000004c06000077f38e443adb00006e1274e82b4a else 0x39240350279100003569000064236e55104476db77a4936000002d602cd485a04a6849e097b6302a899050bb8ef400008b5301fa8c1a8580593048521beb18300511573b08c413803fa00dc5000000001440948b010b71577bba1ec900000000999b000000000000421980253ae04a34499014f90ab62c6893940de052a13a80)) else (if page < 57 then 0x76667f8a3beb6ea05deb62d02a957a131b8b0000000065794ca600002190000000000111000000003716713664714e9089b095b03db1337036d00000000000007463744463c15d203e336cc70b442128000000003d601cea762008300380000007800f662b816c0441106c0b0b337034499706415ca010904a1193241b6073b7 else (if page < 58 then 0x4a40000085e0092491c45db055d026f00000580013520c173949000031c650fa77a1471b38487f101fc1272060300fd96c20068000003a440000022046c4000070500000000058d21884757100800000082405f0000000000f57000061c48a7000009cc04b5200003bf16a0700007bb000003d8b40d176e034f643756db02011 else 0x42280000166489ca76304e6849f2738678251fe9576130f440471c9b0cc4000045f06c6157a900002de833e04ee000004afa3b1256eb30a00231646b76c0278076a34f9b4cf42852314085b08e7b8e9a45908e013950571b49aa33a06f607f20456064f120e838900c901370518a6d717eeb26d45c12640241b20f3355030000)))) else (if page < 65 then (if page < 62 then (if page < 60 then 0xcf16bb20000597a8f11000013e776482ed1000053a44b3016820000146753415d2a13e4121b5e0711b038a9000034c98f230860064749c057508ccb966012830050512108022f26000038103e6068a02bf335a082f793802b5440157731671591f06ac162a01cb0215511e030d98c30868009d0465b74a2198069aa00001aa0 else (if page < 61 then 0x31740b51000000004b713e4196397e00000059b860c73bc078da62872f483ea08e7a396669978234233a73480eb07b7735b179b100002a5056b398868ac60c390fb150303df026c000005dc044ea2acb0000213562c74cc8980248d047645b051e623549955502da52715c8a5a7307708c70620254a388902ba461a20ca3 else 0x63d06e2877118f888c904b7014a137f7381504c794b122265ffa491017e06167415157d45b5309730b5a014b5bd201a86ae77d5428d000d047e10ca582b073300ea000001750000069505159802875b93ab0953a392b01619afb32a66f083255313529e5000088b4000064d06c600000000000007a8320c171202e0000000000)) else (if page < 63 then 0x7fb09d498ed055367f2961946a008446823b758447b069885f955dca40003c4446481dcb30ab000034ba25705e811c600ff001f66d804a0052e00d11482470a173662da87cba392a156a4f0247c25a565f7082b35f2a134044ca02a02be803487f50000090c00000529b000064d763b08f40000045d091a39cab29c400007b27 else (if page < 64 then 0x3540509a77ea783164670f4571d300008140710357f071e20c0015505d4b194027407bf11f5615d438b0148010cb1c2871d014e062800000668b518088701b106a771fa93b60393509902a6486fb25f089803b109320350811785d1633d0572600002b9426a019e80000991006001e215e91000000007d7600004ada62304924 else 0x6c373f2900000c364e50492500006b4026a15f0382ba3d903e2a644700005cd01db038088480116090d4000000009100000038fb583008447404469009a10125791656a06d0091671c345d0a82c0792b000024c2046569276081000083c9481200000000000000007df290f0211b3e0017b074c76084266839ea9ae01e008c61))) else (if page < 68 then (if page < 66 then 0x59004ae41568000060d031a346207a205ce300003b80000016903de7785444e1146028123a2295d8648086ab4f269335049091d000000000000088306b92186a43e701370000602006c02d30742461f342ba92c000001b908fc0000000005f40000023003b8b47ab4b6142d0802042fb6f6471c85fc70b402a607670633a0280 else (if page < 67 then 0xa07230344087a06210449066ab7df079742cb0000081908dca01b59c8b008a6df0000055e000002ba30000356001c8113b558b71a02d75000052e2126600009055394a15f01f944ae059014b6077944982205055131f77000032d70db2841363b89d6841407660013600005849622300009c2015f83b0055b12d2978238593 else 0x866a28f14bc15c0549d089c40000059b99200e2b193023e9000003bb000046405d0b0000496960503bf09844627089306cf0202208d64b211d421bf44e9601a00000607456d03a40000065933e40386142d1000048a074d4354265e100007a7027d18e50849278870000257b000000007335000037b2634859e9000063707b4b)) else (if page < 69 then 0x74352b70daa704643a00a950f381590000000004cb810740000011b000015a5000078c85ce04a6a5d1a69303921000007401ea4000000006157981319f37a717733000000000000681b5ed97aea5d600000000049a000000000000088b24d90000000003e87000008802606554237024efa4831000078037690000000009460 else (if page < 70 then 0x1cf022f07ae412c77dc4457073a601e07f5b902800000df2000001208ffa43955d63000001e7332a46009ce911e815f16a3071622f6a40f08230161805f278b800006560781177a5743445c07a348ad746d7494093a538d00e491dc921aa43b8000092303e73282b00000f054db05b500000000076a0996513c398d84e542851 else 0x3960000091f6120878d039c008a574974f600000053066368d6b4ed05eb1000060140000954a87bb02c016ab9b9407578888000049fa833800005d58000060e4420b09769c5217cb0000000018138f660000934a1ef21eba46a43bcb14002dd13f5008637aa000000e70067b7fd450d090208a1a75275da0234a38e05d13))))) else (if page < 83 then (if page < 77 then (if page < 74 then (if page < 72 then 0x5a1ed05ee097f6428930f00f3000001922770057c8875359605a8059a79ac129500dc28f102b726b7086010532357a43188f985c34241072612de04e6a88f15daa41707728130302db45d42f096c705a16798b81703ae65bca2b1491868af6000020b78b95568b947501854b4010200578391000004ac0000069c0000046a0 else (if page < 73 then 0xc8885404a9b0000000024e04f7b77c20000295b01f08590000000004ce06a485b1497889b3400002dc02fc151e000008f8a237991d70000000000000000365500000000233000002464000007c903290000119400008a650000949a6e880000000000000000309050f0739600002f7b36e1012a79f414689c7426749a5073c1 else 0x5ab67500225b060414014df11d103e10731307481bd26a200000000035903b680d6400008bba12208920919b000011261246904046413eb0946b6a8759b057a308010000699b70e37c710000237a0000000050e082602db100000aa5134400000000452097667900162131941d40000087b0621448818fe2875000005fb04e80)) else (if page < 75 then 0x6c2a1a00438263e444b07cab00002c37000098f0191857d060f093f05cc1513040601c3300006d5b7e105caa033b92f4031894405c980000932b71863f5339731c6a57e421007440156b2df724017040548b6aeb4f88978200000000676432f2634124f001ba7e124909435b0cd21a7060cb4cd9546b675170675ac400008904 else (if page < 76 then 0x18d7258010d84daa6c8079866fc428e009ab2df809b43f3028c260f72f7099f49175774061d00ee395a07c3a480050a181fb4e40996b481478302a281fba24763d30989036b047204af088a07a0489d078023b2268c035a83cf08926025066eb567b1ed58a3031104977068207db34a063118a80000016a20cd0446a147a2b50 else 0x397433058a43c3272f0388000005491553097c4473b00001c19245903848ad128004fa685f0282230ba0f3925494e3466d62c6a03c485528afa08b929b00c12029a7754047464931e202364838807c129811e3a58e82952510274a06294673096c8019b2eb0781078c75a9024b238f36ae08de130880ca008500000000082a4))) else (if page < 80 then (if page < 78 then 0x3d39092b71244ad44a5600008050561b292006d0722772506c3b19a808e47bdb5ef13d34000015d96de000000000000000008460000000000000000000005787099100007f125a3474500000000010391cd1096b719300003226069902e000002dbb94800670000081508a0a570961ea000007fb0000000045388aeb62d8 else (if page < 79 then 0x6a900000358062635b225df087297dd033345f0042110291242a25a02a1090773ee003d06d30368b99fb61e131da6057528548e093e408001ff5048119209abb30186301014537538974879062f00000000000003f8000006a677ab0855039480000000064b08672000001bb01ea9516761223968f3063f051a78ec500000000 else 0x4e44457300007d400d3900000dc100008160442039d00fe951f8000090384b10825300000642935038606c4053c990b007098203933429b432a0000000003ec01fdb052b6257303700000000000095968be04ec0093769675b7b7ad109ca000053586ba74780000071a100002620000042305ad700627c040632391a9306)) else (if page < 81 then 0x282a1f65698089005fc046b1200b59445da949b00a34217587aa8502250143705fba5c55000003473fe075a502e927304ea3000070a7758094b500002f30719609fb376000000000098731b403704bd05be80a85515a619719a750f8790529300000403a19c50000958300007ad6124b9196000045e02a67000000007b937650 else (if page < 82 then 0x397043982c1459b3625051611be093c041b09cf03fd000000473000000004ba082d30000022a000000000000706b0b0b2f8100004428209871765cb011a00082118082f177463ab724a000000000270170f10152874105b873ea6a8069703a206031861b67c06adb354a67fb1e7704f079e4352b2a0b4b2015a4529027aa0c20 else 0x39159cda25c49730000076874eb1564071607004633653e800000b60145051d888a392f00f511c0718e052d0000011d05b900331838000000000111597a1436232ca487300000271536b2960249374d00000903265f300004e20018000005ff200000000888069f618d05a402ab06cc079674d7a2c4072906b143b9265c30d93)))) else (if page < 89 then (if page < 86 then (if page < 84 then 0x128703f86ad012d7245683b072144b505ae4389a72a059572c0032e847ca5b7023e41dd080704c70000001d4000068201d234f74160040d00000000084201284007100000ed3801b774a72988579027496b089d89d0277ba2c808f784ee439008ad099d0779015c20200911b37351628609409b05a9a28bb000000005c7a0000 else (if page < 85 then 0x2a871db208f0294395c658b000000000083a99641182880800002a000000000060072aa5000063000000865b5da47e327da00000000032401e304bc03f21617739133125444062fa6a105980469175648bc282b26af7000024a8036800009c2594c85c4406305d46000052ea0750243414e9595a268a37f239147fa24a80 else 0x55729a4000005d7526b0000087f23550797a8975000000003951002163189a75778030661e4071927af0000095970000000016c10000501000002ce0455b1bb46f840000082039402389214b93306004657140cb18b2071838a0000000001353000061a800005c7210d95d4420910000368027104f862f9200001c8b0000)) else (if page < 87 then 0x77108bc86100000067b0311b7d7013c92c23039b6c8b3390718279b000005be096114da8057039014f11479b8b13795b8a4a7fb69538765400008300000082e04a6074c40000668085225a98398000003b52698183aa000060601cda5cf6140328f03d2453751d1200005b1a2b4258a00000000095b700003e9000e836c10000 else (if page < 88 then 0x3e91000036095ba030f76ab087863f409d2574aa9141282062263a0a35201bb750175d622b6a78775aca766a708038504e6614c1052086c0318600002fb05120817416a07db514820de90000000040208b1000000760014200009a9b38112a7000001be9962000003f7300005e10194200002d4144828328964891970303 else 0x7bcb1e7a46b59b7657ea35308c88000028759820012238f209815eb05af0444b4c1b2690755075572dd64f90818072888060016b454806ab60474ef1543b88ea0afb9c1021935555580800004310695741506bc97a1100007fb37b100db3509050f1000076e83bd015e001cb75f767c492f92a460330000051f60000029057fb))) else (if page < 92 then (if page < 90 then 0x3252618741e04cf08eb500006b6700006b6031004a1097005b206ea46150284767e408a03b30066016b1404038f5041748c0196284e000000000000013003ba000002e9126d0943877d01e10476794056c076d1a3f6083488df100b9951a000050a0520800003c20761799f81000000015112f732fe038001a425c482d3b else (if page < 91 then 0x4ff038725d4300000000000000006f76705a21a8000031ba00008ac0000034317010296879971ba04abb00005d5058b176b532710000000039477c26000009ba000043fb92b67f0b1f3b5854295983908df04f00954514902a5b2b620a7801284160000000000db08f3100008a642ba705c02fc07520286065695336000053e0 else 0x11a81ab040da056460b41c623a507db10f6333845ed000008ab02354000045b0026a000089da822b108662f6000089f02d40718353934d1800000000000088d547e70000000063607b00000001701e5986c26e0892e200006240000010401670000000002ba148b10fa083a0187297618b9026006a6b13d60dd03cd05da20000)) else (if page < 93 then 0x3cfb00008f3499860bd03a9b6af052407a96000085215e60525a8ff406010f124f674308309b959054484cc019c69b70901885fb9420623b8c0067cb627185d08fa40d4074c03d70387b92805c645df444588b4552613e7064c75920971638c00d42873a74b7900a93116fd83636893b6bf5696b4da0048a61d73d0882702f76 else (if page < 94 then 0x49e384330000655413b80d860e50715000005ce47910098b7ce38f5071721ea8714259674100700a3efb774b0000499415b252b241c870209776919001b432950f21000029d643f06c008a9a9bb68f03770685763675019a42764d803fb692fb150692750736289a76815d8098e820680b4500004fd00000000000005ce28389 else 0x3aea524659475310021b3fa9540b07516d4336fa6f94450052d46bb0))))))) else 0
  | 7 => if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x7d917a90162085811f01405138000000ae0068b080115d700000dd701d001a000b70000000000001600000016ea053b0f1605e00db300000f0100000000135208100f1016f0173a0222017008ca0ac20285152a08e8159a158b16330e611551151011d012e80e94000017141750000008e716e601161272071004e00ca11223 else 0x15f00a8015b700d808c40b9702c5051a00000950048016300a5114430e030846000005d0000000a017f10df717400f70019012d4131007500d2b0f14096016a80793003015b1000002390000125008f0006009e817c704600adb00001340002a00000a6301c0047802d00000000001a800a204c000b605f009a2008907a91265) else (if page < 3 then 0x11a015a506b10200000010c008fb15c01772099a026401c7117000000c220093000000000d270c8700b2130b0c1a125611b00079096402f017a810d8062014d30f60171012db0e40010b179207660d8015d60e8008940ba00a5b00d413660bb0153403a001150981124909270b5b04200000036815660ab011c1041503da0000 else 0x12a00a490a0200211628098a0000000011600000051007800000000000000a34000003f814201648000017990000030007d00000077000001766000000000000000014940c3a03f4065100000b94063004770612135801d90e5007c014e70da0010904970b49057015e0019112f70f75019717a30f3006a10171001a01fb071b)) else (if page < 6 then (if page < 5 then 0xbf509b608a8002004940f8016c2000009b708b70dc701b812b000000ad915560be201a300d001c617d715e70aa40da302b802d408cb0a0617230e3009e00fc0149002f40ee31190155700000e440ed1078500000b05038008b0068303f00f410f281060166106da069105810d44164012d009e10a7112c003b9167015aa1626 else 0x10000558051b07a2113a146414300f20095316b910a015c713a217a2123002820ed001800c120de711420000000006341350118402500be0154412430aa30e821470111813000602028002a515001278000004d6000002121793023b024313b714560ab215c1154a17341248000000000ee00d7008a00001069607090ae21360) else (if page < 7 then 0xb4b11200d740470000011970500140008e00af017c0084008f71150089a015209d016110970000008c512420c77132b00e40e96000007b602b00e880454012211960a7a0b9814381367129007f00000000004a008500763000004bb0cf005400000090800000a5a1305077411e911c601a415e60e70171a00520f5204990d54 else 0x12810000000000000a3009b103e0073001d207d315f60866000014a503920ec000000c2a02030a330a01043b00000000070116780315000009ea125a02b70b6702c200000000089502c0000006d000000d1b00c2000003580b240b7016321361000000000000000000000c0006800000000011c71567029502a60000))) else (if page < 12 then (if page < 10 then (if page < 9 then 0xa000000065007400000041b157a0a150faa17680340117a0e2508800b33157413e009720263168005ca0a40089006a00000118011910000000009540ff21690144602a00ed90242047101e011a4061013c112100000133612c8174800d30a57035702f506c005e20000000006fb019202020000000014131631137a00001220 else 0x182137208c00e971280014000000000000006c90000000011321226000000000b40000006900e900c301344000000000000126015940ce31233000000c00220000015750000000000000000159b140609b00278000a135a0ea006b01780069714530000094907d80d660bd30184059a0252143211a906b907490a660bc807a8) else (if page < 11 then 0x29211300132075412d5089b081a04140cd016f80316133417e613840a4b0c67123607900412099115600f501044000006f011520a6012f00bd00b160150000000000ef40eb0007b06560b7206a608000000006213200bf40bf0000008200a9315d017d000000000000009fa165600000d17000001b008120000000000000b46 else 0x101201d1017a0b4a15d11761165a17e109d8059110290a240be800000000000012e000000c1016c7000000000000000014c306230d6305b0000000000d0b06e017c100b017e716d80ecb17ba032712da05f4049005600990000015b61487133000000885130a000013270e78124001960f0909c811e0024002700e670d5017d6)) else (if page < 14 then (if page < 13 then 0x24415851767000008b2000010300e660f3309100fd001e4000012791520000001b10b63072011e100000cb0152410770000087713f010b610501584148b026005a006440bb8168806c100e3153a158a09d3130411b317f009f10f22162104f006eb08d0136415610c510000013017580b6017bb01f002980900000007b00bd1 else 0x501610154007c500b3147400000b2309d40a100b900ce617030571157b0fb107ba1665176002e2177013310f40000013480b66162709a013f30b82015401c10ef00310067012f200000000044017c601f9041015a40940028600b102c80ba500420b340b80169813370ea4064015ab01c2000008880f780000094b06690000) else (if page < 15 then 0xbc009a407e20000092b0000021017d107600870139209620e740ba600000cc0008b09fb0000000006600f5802d506570000086002e00e1009c314f00f0014600f870b61009407960664000006a7000000000eb30000000015c60d0700000e8a00000000000007a307e000000d3b0fe000000ac00c40000017b4041a06791620 else (if page < 16 then 0x7ea0a200e6404000a620855126109b215b017980ec701600ed40c3203c0120016d017e00674037202900a07098007a015e10a9414b5052007000600115a049b16b40c9709c40120141016a00bc50d4015500b620a23027711c010700b590845091902060a1604760bb70d3700fb0b0617300f900bc2092012c50d90003210fb else 0xaf20a1410e00000001101e3093000000e9108300000127000000000075307c1023009c012190b1501ba00000000004004f107d20000000009f40f131080110015951421033109f50a8205d200000320000005c00eb613d10590057a00f90cf402e810970519127317b511bb0e60))))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x4a008300120016004500630020001b00490073002100240001007a001100400042001500380074008200410047005100480013003200000027001900430018000000260005000000300014001a003600700000001000570031000000250046001700000056005800070052000400600000005000060080004b003700440072 else 0x6200000000000000000071) else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

-- The hash proposes a successor. The permutation check verifies its complete wire set.
def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let delta := field shifts k 16 (h % b)
  let ix := (h / b + delta) % slotCount k
  let slot := field targets k 16 ix
  (slot / 16,slot % 16)

def s15 : Switch := ⟨30,0xcccccccc,0x3333333300000000⟩
theorem s15_ok : s15.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s25 : Switch := ⟨28,0xf0f0f0f0,0xf0f0f0f00000000⟩
theorem s25_ok : s25.Valid := by unfold Switch.Valid; decide +kernel
def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel
def s05 : Switch := ⟨31,0xaaaaaaaa,0x5555555500000000⟩
theorem s05_ok : s05.Valid := by unfold Switch.Valid; decide +kernel
def s35 : Switch := ⟨24,0xff00ff00,0xff00ff00000000⟩
theorem s35_ok : s35.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s45 : Switch := ⟨16,0xffff0000,0xffff00000000⟩
theorem s45_ok : s45.Valid := by unfold Switch.Valid; decide +kernel
def s14 : Switch := ⟨14,0xcccc0000cccc,0x3333000033330000⟩
theorem s14_ok : s14.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s15, s24]
  | 2 => [s01, s25, s34]
  | 3 => [s01, s02, s03, s04, s05]
  | 4 => [s02, s35]
  | 5 => [s02, s13, s04, s15]
  | 6 => [s03, s12, s45]
  | 7 => [s03, s14, s25]
  | 8 => [s04, s13]
  | 9 => [s04, s15, s02, s13]
  | 10 => [s05, s01, s12, s23, s34]
  | 11 => [s05, s14, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s15_ok, s24_ok, s01_ok, s25_ok, s34_ok, s02_ok, s03_ok, s04_ok, s05_ok, s35_ok, s13_ok, s12_ok, s45_ok, s14_ok, s23_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel

def checked (k i : ℕ) := decide (pool k i).Nodup && closed target negative pool counts lookup steps k i

theorem root : pool 9 0 = raw := by decide +kernel

theorem lower_from_checks
    (verified : ∀ k ≤ 9, ∀ i < counts k, checked k i = true)
    (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) :
    10 ≤ p.length := by
  by_contra! short
  have access : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [← hit]
    exact available_read _ _
  obtain ⟨k,s,bound,inside,run⟩ := extract p initial target 0 {target} Cone.done access
  rw [start] at inside
  have eq := run.initial nonzero raw essential inside
  rw [eq,← root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 9
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => (Bool.and_eq_true_iff.mp (verified k hk i hi)).2) 9 le_rfl 0
    (by decide +kernel) k (by omega) run


end PrismSignedFrontier.Certificate

namespace PrismSignedFrontier.Packed

-- These packed integers only propose a negative input row. Every proposed
-- obstruction is tested on the original signals before a successor is skipped.
structure Columns where
  w : W
  pos : Nat
  neg : Nat

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
def offPositions (w : W) : Nat := (if w.getLsbD 0 then 0xffffffffffffffff else 0) ||| (if w.getLsbD 1 then 0xffffffffffffffff0000000000000000 else 0) ||| (if w.getLsbD 2 then 0xffffffffffffffff00000000000000000000000000000000 else 0) ||| (if w.getLsbD 3 then 0xffffffffffffffff000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 4 then 0xffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 6 then 0xffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 8 then 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 12 then 0xffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 16 then 0xffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 24 then 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 32 then 0xffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 33 then 0xffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) ||| (if w.getLsbD 48 then 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0)
def asColumns (w : W) : Columns := ⟨w, positions w, offPositions w⟩
def equalRows (p : Columns) : Nat := fullLanes ^^^ (p.pos ^^^ p.neg)
def bothCols (a b : Columns) : Columns := ⟨a.w &&& b.w, a.pos &&& b.pos, a.neg &&& b.neg⟩
def notCols (a : Columns) : Columns := ⟨~~~a.w, fullLanes ^^^ a.pos, fullLanes ^^^ a.neg⟩
def orCols (a b : Columns) : Columns := ⟨a.w ||| b.w, a.pos ||| b.pos, a.neg ||| b.neg⟩
def variants (a b : Columns) : List Columns :=
  [bothCols a b,bothCols a (notCols b),bothCols (notCols a) b,orCols a b]

end PrismSignedFrontier.Packed


namespace PrismSignedFrontier.Vector
open PrismSignedFrontier.Packed (Columns bothCols orCols notCols variants equalRows fullLanes)

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

set_option maxRecDepth 4000 in
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

end PrismSignedFrontier.Vector

namespace PrismSignedFrontier.Certificate
def goalColumns : Nat := 0xfffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0fffefffcfefeeea0

theorem goalColumns_valid : goalColumns = Vector.lanes Prism.negative (fun _ => Prism.target) := by decide +kernel

def guidedChecked (k i : Nat) := decide (pool k i).Nodup &&
  Vector.packedClosed Prism.target Prism.negative goalColumns pool counts lookup steps k i

theorem originalChecked {k i} (good : guidedChecked k i = true) : checked k i = true := by
  obtain ⟨nd,ok⟩ := Bool.and_eq_true_iff.mp good
  exact Bool.and_eq_true_iff.mpr ⟨nd,Vector.closed_sound Prism.target Prism.negative goalColumns
    goalColumns_valid pool counts lookup steps (by decide +kernel)
    (fun r hr => (Prism.neg r hr).1) k i ok⟩
end PrismSignedFrontier.Certificate

namespace PrismOneNotBound
open PrismSignedFrontier

def assignment (r : Fin 64) (v : Fin 6) : Bool := r.val.testBit v.val

theorem rawTable : ∀ r : Fin 64, Prism.initial.map (fun u => u.getLsbD r.val) =
    SevenVertexOneNot.signedStart (assignment r) := by decide +kernel

theorem goalTable : ∀ r : Fin 64, Prism.target.getLsbD r.val =
    SevenVertexOneNot.prism (assignment r) := by decide +kernel

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
    (hit : ∀ x, SevenVertexOneNot.signed p o x = SevenVertexOneNot.prism x) :
    canonical (evaluate p Prism.initial o) = Prism.target := by
  have eq : evaluate p Prism.initial o = Prism.target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 64 := ⟨i,hi⟩
    change ((p.foldl add Prism.initial).getD o 0).getLsbD r.val = _
    rw [readDefault,foldRow p Prism.initial r,rawTable r]
    exact (hit (assignment r)).trans (goalTable r).symm
  rw [eq]
  decide +kernel

theorem prismRequirement
    (lower : ∀ p o, canonical (evaluate p Prism.initial o) = Prism.target → 10 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, SevenVertexOneNot.signed p o x = SevenVertexOneNot.prism x) : 10 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end PrismOneNotBound

namespace PrismSignedFrontier.Certificate

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x0 : span (guidedChecked 4) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x16 : span (guidedChecked 4) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x32 : span (guidedChecked 4) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x48 : span (guidedChecked 4) 14 48 = true := by decide +kernel

theorem layer4 : span (guidedChecked 4) 62 0 = true :=
  (@span_join (guidedChecked 4) 32 0 30 (@span_join (guidedChecked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (guidedChecked 4) 16 32 14 chunk4x32 chunk4x48))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x0 : span (guidedChecked 5) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x16 : span (guidedChecked 5) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x32 : span (guidedChecked 5) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x48 : span (guidedChecked 5) 16 48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x64 : span (guidedChecked 5) 16 64 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x80 : span (guidedChecked 5) 16 80 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x96 : span (guidedChecked 5) 16 96 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x112 : span (guidedChecked 5) 16 112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x128 : span (guidedChecked 5) 16 128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x144 : span (guidedChecked 5) 16 144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x160 : span (guidedChecked 5) 16 160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x176 : span (guidedChecked 5) 16 176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x192 : span (guidedChecked 5) 16 192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x208 : span (guidedChecked 5) 16 208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x224 : span (guidedChecked 5) 16 224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x240 : span (guidedChecked 5) 16 240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x256 : span (guidedChecked 5) 16 256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x272 : span (guidedChecked 5) 16 272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x288 : span (guidedChecked 5) 16 288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x304 : span (guidedChecked 5) 16 304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x320 : span (guidedChecked 5) 16 320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x336 : span (guidedChecked 5) 16 336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x352 : span (guidedChecked 5) 16 352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x368 : span (guidedChecked 5) 16 368 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x384 : span (guidedChecked 5) 16 384 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x400 : span (guidedChecked 5) 16 400 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x416 : span (guidedChecked 5) 16 416 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x432 : span (guidedChecked 5) 16 432 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x448 : span (guidedChecked 5) 16 448 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x464 : span (guidedChecked 5) 16 464 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x480 : span (guidedChecked 5) 16 480 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x496 : span (guidedChecked 5) 16 496 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x512 : span (guidedChecked 5) 16 512 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x528 : span (guidedChecked 5) 16 528 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x544 : span (guidedChecked 5) 16 544 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x560 : span (guidedChecked 5) 16 560 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x576 : span (guidedChecked 5) 16 576 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x592 : span (guidedChecked 5) 16 592 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x608 : span (guidedChecked 5) 16 608 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x624 : span (guidedChecked 5) 16 624 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x640 : span (guidedChecked 5) 16 640 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x656 : span (guidedChecked 5) 16 656 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x672 : span (guidedChecked 5) 16 672 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x688 : span (guidedChecked 5) 16 688 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x704 : span (guidedChecked 5) 16 704 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x720 : span (guidedChecked 5) 16 720 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x736 : span (guidedChecked 5) 16 736 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x752 : span (guidedChecked 5) 16 752 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x768 : span (guidedChecked 5) 16 768 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x784 : span (guidedChecked 5) 16 784 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x800 : span (guidedChecked 5) 16 800 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x816 : span (guidedChecked 5) 16 816 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x832 : span (guidedChecked 5) 16 832 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x848 : span (guidedChecked 5) 16 848 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x864 : span (guidedChecked 5) 16 864 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x880 : span (guidedChecked 5) 16 880 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x896 : span (guidedChecked 5) 16 896 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x912 : span (guidedChecked 5) 16 912 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x928 : span (guidedChecked 5) 16 928 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x944 : span (guidedChecked 5) 16 944 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x960 : span (guidedChecked 5) 16 960 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x976 : span (guidedChecked 5) 16 976 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x992 : span (guidedChecked 5) 16 992 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1008 : span (guidedChecked 5) 16 1008 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1024 : span (guidedChecked 5) 16 1024 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1040 : span (guidedChecked 5) 16 1040 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1056 : span (guidedChecked 5) 16 1056 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1072 : span (guidedChecked 5) 16 1072 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1088 : span (guidedChecked 5) 16 1088 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1104 : span (guidedChecked 5) 16 1104 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1120 : span (guidedChecked 5) 16 1120 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1136 : span (guidedChecked 5) 16 1136 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1152 : span (guidedChecked 5) 16 1152 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1168 : span (guidedChecked 5) 16 1168 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1184 : span (guidedChecked 5) 16 1184 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1200 : span (guidedChecked 5) 16 1200 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1216 : span (guidedChecked 5) 16 1216 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1232 : span (guidedChecked 5) 16 1232 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1248 : span (guidedChecked 5) 16 1248 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1264 : span (guidedChecked 5) 16 1264 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1280 : span (guidedChecked 5) 16 1280 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1296 : span (guidedChecked 5) 16 1296 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1312 : span (guidedChecked 5) 16 1312 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1328 : span (guidedChecked 5) 16 1328 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1344 : span (guidedChecked 5) 16 1344 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1360 : span (guidedChecked 5) 16 1360 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1376 : span (guidedChecked 5) 16 1376 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1392 : span (guidedChecked 5) 16 1392 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1408 : span (guidedChecked 5) 16 1408 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1424 : span (guidedChecked 5) 16 1424 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1440 : span (guidedChecked 5) 16 1440 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1456 : span (guidedChecked 5) 16 1456 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1472 : span (guidedChecked 5) 16 1472 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1488 : span (guidedChecked 5) 16 1488 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1504 : span (guidedChecked 5) 16 1504 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1520 : span (guidedChecked 5) 16 1520 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1536 : span (guidedChecked 5) 16 1536 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1552 : span (guidedChecked 5) 16 1552 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1568 : span (guidedChecked 5) 16 1568 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1584 : span (guidedChecked 5) 16 1584 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1600 : span (guidedChecked 5) 16 1600 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1616 : span (guidedChecked 5) 16 1616 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1632 : span (guidedChecked 5) 16 1632 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1648 : span (guidedChecked 5) 16 1648 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1664 : span (guidedChecked 5) 16 1664 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1680 : span (guidedChecked 5) 16 1680 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1696 : span (guidedChecked 5) 16 1696 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1712 : span (guidedChecked 5) 16 1712 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1728 : span (guidedChecked 5) 16 1728 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1744 : span (guidedChecked 5) 16 1744 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1760 : span (guidedChecked 5) 16 1760 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1776 : span (guidedChecked 5) 16 1776 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1792 : span (guidedChecked 5) 16 1792 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1808 : span (guidedChecked 5) 16 1808 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1824 : span (guidedChecked 5) 16 1824 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1840 : span (guidedChecked 5) 16 1840 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1856 : span (guidedChecked 5) 16 1856 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1872 : span (guidedChecked 5) 16 1872 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1888 : span (guidedChecked 5) 16 1888 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1904 : span (guidedChecked 5) 16 1904 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1920 : span (guidedChecked 5) 16 1920 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1936 : span (guidedChecked 5) 16 1936 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1952 : span (guidedChecked 5) 16 1952 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1968 : span (guidedChecked 5) 16 1968 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1984 : span (guidedChecked 5) 16 1984 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x2000 : span (guidedChecked 5) 2 2000 = true := by decide +kernel

theorem layer5 : span (guidedChecked 5) 2002 0 = true :=
  (@span_join (guidedChecked 5) 1008 0 994 (@span_join (guidedChecked 5) 496 0 512 (@span_join (guidedChecked 5) 240 0 256 (@span_join (guidedChecked 5) 112 0 128 (@span_join (guidedChecked 5) 48 0 64 (@span_join (guidedChecked 5) 16 0 32 chunk5x0 (@span_join (guidedChecked 5) 16 16 16 chunk5x16 chunk5x32)) (@span_join (guidedChecked 5) 32 48 32 (@span_join (guidedChecked 5) 16 48 16 chunk5x48 chunk5x64) (@span_join (guidedChecked 5) 16 80 16 chunk5x80 chunk5x96))) (@span_join (guidedChecked 5) 64 112 64 (@span_join (guidedChecked 5) 32 112 32 (@span_join (guidedChecked 5) 16 112 16 chunk5x112 chunk5x128) (@span_join (guidedChecked 5) 16 144 16 chunk5x144 chunk5x160)) (@span_join (guidedChecked 5) 32 176 32 (@span_join (guidedChecked 5) 16 176 16 chunk5x176 chunk5x192) (@span_join (guidedChecked 5) 16 208 16 chunk5x208 chunk5x224)))) (@span_join (guidedChecked 5) 128 240 128 (@span_join (guidedChecked 5) 64 240 64 (@span_join (guidedChecked 5) 32 240 32 (@span_join (guidedChecked 5) 16 240 16 chunk5x240 chunk5x256) (@span_join (guidedChecked 5) 16 272 16 chunk5x272 chunk5x288)) (@span_join (guidedChecked 5) 32 304 32 (@span_join (guidedChecked 5) 16 304 16 chunk5x304 chunk5x320) (@span_join (guidedChecked 5) 16 336 16 chunk5x336 chunk5x352))) (@span_join (guidedChecked 5) 64 368 64 (@span_join (guidedChecked 5) 32 368 32 (@span_join (guidedChecked 5) 16 368 16 chunk5x368 chunk5x384) (@span_join (guidedChecked 5) 16 400 16 chunk5x400 chunk5x416)) (@span_join (guidedChecked 5) 32 432 32 (@span_join (guidedChecked 5) 16 432 16 chunk5x432 chunk5x448) (@span_join (guidedChecked 5) 16 464 16 chunk5x464 chunk5x480))))) (@span_join (guidedChecked 5) 256 496 256 (@span_join (guidedChecked 5) 128 496 128 (@span_join (guidedChecked 5) 64 496 64 (@span_join (guidedChecked 5) 32 496 32 (@span_join (guidedChecked 5) 16 496 16 chunk5x496 chunk5x512) (@span_join (guidedChecked 5) 16 528 16 chunk5x528 chunk5x544)) (@span_join (guidedChecked 5) 32 560 32 (@span_join (guidedChecked 5) 16 560 16 chunk5x560 chunk5x576) (@span_join (guidedChecked 5) 16 592 16 chunk5x592 chunk5x608))) (@span_join (guidedChecked 5) 64 624 64 (@span_join (guidedChecked 5) 32 624 32 (@span_join (guidedChecked 5) 16 624 16 chunk5x624 chunk5x640) (@span_join (guidedChecked 5) 16 656 16 chunk5x656 chunk5x672)) (@span_join (guidedChecked 5) 32 688 32 (@span_join (guidedChecked 5) 16 688 16 chunk5x688 chunk5x704) (@span_join (guidedChecked 5) 16 720 16 chunk5x720 chunk5x736)))) (@span_join (guidedChecked 5) 128 752 128 (@span_join (guidedChecked 5) 64 752 64 (@span_join (guidedChecked 5) 32 752 32 (@span_join (guidedChecked 5) 16 752 16 chunk5x752 chunk5x768) (@span_join (guidedChecked 5) 16 784 16 chunk5x784 chunk5x800)) (@span_join (guidedChecked 5) 32 816 32 (@span_join (guidedChecked 5) 16 816 16 chunk5x816 chunk5x832) (@span_join (guidedChecked 5) 16 848 16 chunk5x848 chunk5x864))) (@span_join (guidedChecked 5) 64 880 64 (@span_join (guidedChecked 5) 32 880 32 (@span_join (guidedChecked 5) 16 880 16 chunk5x880 chunk5x896) (@span_join (guidedChecked 5) 16 912 16 chunk5x912 chunk5x928)) (@span_join (guidedChecked 5) 32 944 32 (@span_join (guidedChecked 5) 16 944 16 chunk5x944 chunk5x960) (@span_join (guidedChecked 5) 16 976 16 chunk5x976 chunk5x992)))))) (@span_join (guidedChecked 5) 496 1008 498 (@span_join (guidedChecked 5) 240 1008 256 (@span_join (guidedChecked 5) 112 1008 128 (@span_join (guidedChecked 5) 48 1008 64 (@span_join (guidedChecked 5) 16 1008 32 chunk5x1008 (@span_join (guidedChecked 5) 16 1024 16 chunk5x1024 chunk5x1040)) (@span_join (guidedChecked 5) 32 1056 32 (@span_join (guidedChecked 5) 16 1056 16 chunk5x1056 chunk5x1072) (@span_join (guidedChecked 5) 16 1088 16 chunk5x1088 chunk5x1104))) (@span_join (guidedChecked 5) 64 1120 64 (@span_join (guidedChecked 5) 32 1120 32 (@span_join (guidedChecked 5) 16 1120 16 chunk5x1120 chunk5x1136) (@span_join (guidedChecked 5) 16 1152 16 chunk5x1152 chunk5x1168)) (@span_join (guidedChecked 5) 32 1184 32 (@span_join (guidedChecked 5) 16 1184 16 chunk5x1184 chunk5x1200) (@span_join (guidedChecked 5) 16 1216 16 chunk5x1216 chunk5x1232)))) (@span_join (guidedChecked 5) 128 1248 128 (@span_join (guidedChecked 5) 64 1248 64 (@span_join (guidedChecked 5) 32 1248 32 (@span_join (guidedChecked 5) 16 1248 16 chunk5x1248 chunk5x1264) (@span_join (guidedChecked 5) 16 1280 16 chunk5x1280 chunk5x1296)) (@span_join (guidedChecked 5) 32 1312 32 (@span_join (guidedChecked 5) 16 1312 16 chunk5x1312 chunk5x1328) (@span_join (guidedChecked 5) 16 1344 16 chunk5x1344 chunk5x1360))) (@span_join (guidedChecked 5) 64 1376 64 (@span_join (guidedChecked 5) 32 1376 32 (@span_join (guidedChecked 5) 16 1376 16 chunk5x1376 chunk5x1392) (@span_join (guidedChecked 5) 16 1408 16 chunk5x1408 chunk5x1424)) (@span_join (guidedChecked 5) 32 1440 32 (@span_join (guidedChecked 5) 16 1440 16 chunk5x1440 chunk5x1456) (@span_join (guidedChecked 5) 16 1472 16 chunk5x1472 chunk5x1488))))) (@span_join (guidedChecked 5) 256 1504 242 (@span_join (guidedChecked 5) 128 1504 128 (@span_join (guidedChecked 5) 64 1504 64 (@span_join (guidedChecked 5) 32 1504 32 (@span_join (guidedChecked 5) 16 1504 16 chunk5x1504 chunk5x1520) (@span_join (guidedChecked 5) 16 1536 16 chunk5x1536 chunk5x1552)) (@span_join (guidedChecked 5) 32 1568 32 (@span_join (guidedChecked 5) 16 1568 16 chunk5x1568 chunk5x1584) (@span_join (guidedChecked 5) 16 1600 16 chunk5x1600 chunk5x1616))) (@span_join (guidedChecked 5) 64 1632 64 (@span_join (guidedChecked 5) 32 1632 32 (@span_join (guidedChecked 5) 16 1632 16 chunk5x1632 chunk5x1648) (@span_join (guidedChecked 5) 16 1664 16 chunk5x1664 chunk5x1680)) (@span_join (guidedChecked 5) 32 1696 32 (@span_join (guidedChecked 5) 16 1696 16 chunk5x1696 chunk5x1712) (@span_join (guidedChecked 5) 16 1728 16 chunk5x1728 chunk5x1744)))) (@span_join (guidedChecked 5) 128 1760 114 (@span_join (guidedChecked 5) 64 1760 64 (@span_join (guidedChecked 5) 32 1760 32 (@span_join (guidedChecked 5) 16 1760 16 chunk5x1760 chunk5x1776) (@span_join (guidedChecked 5) 16 1792 16 chunk5x1792 chunk5x1808)) (@span_join (guidedChecked 5) 32 1824 32 (@span_join (guidedChecked 5) 16 1824 16 chunk5x1824 chunk5x1840) (@span_join (guidedChecked 5) 16 1856 16 chunk5x1856 chunk5x1872))) (@span_join (guidedChecked 5) 64 1888 50 (@span_join (guidedChecked 5) 32 1888 32 (@span_join (guidedChecked 5) 16 1888 16 chunk5x1888 chunk5x1904) (@span_join (guidedChecked 5) 16 1920 16 chunk5x1920 chunk5x1936)) (@span_join (guidedChecked 5) 32 1952 18 (@span_join (guidedChecked 5) 16 1952 16 chunk5x1952 chunk5x1968) (@span_join (guidedChecked 5) 16 1984 2 chunk5x1984 chunk5x2000)))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x0 : span (guidedChecked 6) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x16 : span (guidedChecked 6) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x32 : span (guidedChecked 6) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x48 : span (guidedChecked 6) 16 48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x64 : span (guidedChecked 6) 16 64 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x80 : span (guidedChecked 6) 16 80 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x96 : span (guidedChecked 6) 16 96 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x112 : span (guidedChecked 6) 16 112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x128 : span (guidedChecked 6) 16 128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x144 : span (guidedChecked 6) 16 144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x160 : span (guidedChecked 6) 16 160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x176 : span (guidedChecked 6) 16 176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x192 : span (guidedChecked 6) 16 192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x208 : span (guidedChecked 6) 16 208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x224 : span (guidedChecked 6) 16 224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x240 : span (guidedChecked 6) 16 240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x256 : span (guidedChecked 6) 16 256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x272 : span (guidedChecked 6) 16 272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x288 : span (guidedChecked 6) 16 288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x304 : span (guidedChecked 6) 16 304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x320 : span (guidedChecked 6) 16 320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x336 : span (guidedChecked 6) 16 336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x352 : span (guidedChecked 6) 16 352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x368 : span (guidedChecked 6) 16 368 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x384 : span (guidedChecked 6) 16 384 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x400 : span (guidedChecked 6) 16 400 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x416 : span (guidedChecked 6) 16 416 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x432 : span (guidedChecked 6) 16 432 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x448 : span (guidedChecked 6) 16 448 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x464 : span (guidedChecked 6) 16 464 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x480 : span (guidedChecked 6) 16 480 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x496 : span (guidedChecked 6) 16 496 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x512 : span (guidedChecked 6) 16 512 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x528 : span (guidedChecked 6) 16 528 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x544 : span (guidedChecked 6) 16 544 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x560 : span (guidedChecked 6) 16 560 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x576 : span (guidedChecked 6) 16 576 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x592 : span (guidedChecked 6) 16 592 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x608 : span (guidedChecked 6) 16 608 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x624 : span (guidedChecked 6) 16 624 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x640 : span (guidedChecked 6) 16 640 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x656 : span (guidedChecked 6) 16 656 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x672 : span (guidedChecked 6) 16 672 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x688 : span (guidedChecked 6) 16 688 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x704 : span (guidedChecked 6) 16 704 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x720 : span (guidedChecked 6) 16 720 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x736 : span (guidedChecked 6) 16 736 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x752 : span (guidedChecked 6) 16 752 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x768 : span (guidedChecked 6) 16 768 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x784 : span (guidedChecked 6) 16 784 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x800 : span (guidedChecked 6) 16 800 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x816 : span (guidedChecked 6) 16 816 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x832 : span (guidedChecked 6) 16 832 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x848 : span (guidedChecked 6) 16 848 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x864 : span (guidedChecked 6) 16 864 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x880 : span (guidedChecked 6) 16 880 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x896 : span (guidedChecked 6) 16 896 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x912 : span (guidedChecked 6) 16 912 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x928 : span (guidedChecked 6) 16 928 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x944 : span (guidedChecked 6) 16 944 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x960 : span (guidedChecked 6) 16 960 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x976 : span (guidedChecked 6) 16 976 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x992 : span (guidedChecked 6) 16 992 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1008 : span (guidedChecked 6) 16 1008 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1024 : span (guidedChecked 6) 16 1024 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1040 : span (guidedChecked 6) 16 1040 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1056 : span (guidedChecked 6) 16 1056 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1072 : span (guidedChecked 6) 16 1072 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1088 : span (guidedChecked 6) 16 1088 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1104 : span (guidedChecked 6) 16 1104 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1120 : span (guidedChecked 6) 16 1120 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1136 : span (guidedChecked 6) 16 1136 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1152 : span (guidedChecked 6) 16 1152 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1168 : span (guidedChecked 6) 16 1168 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1184 : span (guidedChecked 6) 16 1184 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1200 : span (guidedChecked 6) 16 1200 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1216 : span (guidedChecked 6) 16 1216 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1232 : span (guidedChecked 6) 16 1232 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1248 : span (guidedChecked 6) 16 1248 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1264 : span (guidedChecked 6) 16 1264 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1280 : span (guidedChecked 6) 16 1280 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1296 : span (guidedChecked 6) 16 1296 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1312 : span (guidedChecked 6) 16 1312 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1328 : span (guidedChecked 6) 16 1328 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1344 : span (guidedChecked 6) 16 1344 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1360 : span (guidedChecked 6) 16 1360 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1376 : span (guidedChecked 6) 16 1376 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1392 : span (guidedChecked 6) 16 1392 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1408 : span (guidedChecked 6) 16 1408 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1424 : span (guidedChecked 6) 16 1424 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1440 : span (guidedChecked 6) 16 1440 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1456 : span (guidedChecked 6) 16 1456 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1472 : span (guidedChecked 6) 16 1472 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1488 : span (guidedChecked 6) 16 1488 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1504 : span (guidedChecked 6) 16 1504 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1520 : span (guidedChecked 6) 16 1520 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1536 : span (guidedChecked 6) 16 1536 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1552 : span (guidedChecked 6) 16 1552 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1568 : span (guidedChecked 6) 16 1568 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1584 : span (guidedChecked 6) 16 1584 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1600 : span (guidedChecked 6) 16 1600 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1616 : span (guidedChecked 6) 16 1616 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1632 : span (guidedChecked 6) 16 1632 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1648 : span (guidedChecked 6) 16 1648 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1664 : span (guidedChecked 6) 16 1664 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1680 : span (guidedChecked 6) 16 1680 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1696 : span (guidedChecked 6) 16 1696 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1712 : span (guidedChecked 6) 16 1712 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1728 : span (guidedChecked 6) 16 1728 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1744 : span (guidedChecked 6) 16 1744 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1760 : span (guidedChecked 6) 16 1760 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1776 : span (guidedChecked 6) 16 1776 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1792 : span (guidedChecked 6) 16 1792 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1808 : span (guidedChecked 6) 16 1808 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1824 : span (guidedChecked 6) 16 1824 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1840 : span (guidedChecked 6) 16 1840 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1856 : span (guidedChecked 6) 16 1856 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1872 : span (guidedChecked 6) 16 1872 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1888 : span (guidedChecked 6) 16 1888 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1904 : span (guidedChecked 6) 16 1904 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1920 : span (guidedChecked 6) 16 1920 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1936 : span (guidedChecked 6) 16 1936 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1952 : span (guidedChecked 6) 16 1952 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1968 : span (guidedChecked 6) 16 1968 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1984 : span (guidedChecked 6) 16 1984 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2000 : span (guidedChecked 6) 16 2000 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2016 : span (guidedChecked 6) 16 2016 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2032 : span (guidedChecked 6) 16 2032 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2048 : span (guidedChecked 6) 16 2048 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2064 : span (guidedChecked 6) 16 2064 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2080 : span (guidedChecked 6) 16 2080 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2096 : span (guidedChecked 6) 16 2096 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2112 : span (guidedChecked 6) 16 2112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2128 : span (guidedChecked 6) 16 2128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2144 : span (guidedChecked 6) 16 2144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2160 : span (guidedChecked 6) 16 2160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2176 : span (guidedChecked 6) 16 2176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2192 : span (guidedChecked 6) 16 2192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2208 : span (guidedChecked 6) 16 2208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2224 : span (guidedChecked 6) 16 2224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2240 : span (guidedChecked 6) 16 2240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2256 : span (guidedChecked 6) 16 2256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2272 : span (guidedChecked 6) 16 2272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2288 : span (guidedChecked 6) 16 2288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2304 : span (guidedChecked 6) 16 2304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2320 : span (guidedChecked 6) 16 2320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2336 : span (guidedChecked 6) 16 2336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2352 : span (guidedChecked 6) 16 2352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2368 : span (guidedChecked 6) 16 2368 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2384 : span (guidedChecked 6) 16 2384 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2400 : span (guidedChecked 6) 16 2400 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2416 : span (guidedChecked 6) 16 2416 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2432 : span (guidedChecked 6) 16 2432 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2448 : span (guidedChecked 6) 16 2448 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2464 : span (guidedChecked 6) 16 2464 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2480 : span (guidedChecked 6) 16 2480 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2496 : span (guidedChecked 6) 16 2496 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2512 : span (guidedChecked 6) 8 2512 = true := by decide +kernel

theorem layer6 : span (guidedChecked 6) 2520 0 = true :=
  (@span_join (guidedChecked 6) 1264 0 1256 (@span_join (guidedChecked 6) 624 0 640 (@span_join (guidedChecked 6) 304 0 320 (@span_join (guidedChecked 6) 144 0 160 (@span_join (guidedChecked 6) 64 0 80 (@span_join (guidedChecked 6) 32 0 32 (@span_join (guidedChecked 6) 16 0 16 chunk6x0 chunk6x16) (@span_join (guidedChecked 6) 16 32 16 chunk6x32 chunk6x48)) (@span_join (guidedChecked 6) 32 64 48 (@span_join (guidedChecked 6) 16 64 16 chunk6x64 chunk6x80) (@span_join (guidedChecked 6) 16 96 32 chunk6x96 (@span_join (guidedChecked 6) 16 112 16 chunk6x112 chunk6x128)))) (@span_join (guidedChecked 6) 80 144 80 (@span_join (guidedChecked 6) 32 144 48 (@span_join (guidedChecked 6) 16 144 16 chunk6x144 chunk6x160) (@span_join (guidedChecked 6) 16 176 32 chunk6x176 (@span_join (guidedChecked 6) 16 192 16 chunk6x192 chunk6x208))) (@span_join (guidedChecked 6) 32 224 48 (@span_join (guidedChecked 6) 16 224 16 chunk6x224 chunk6x240) (@span_join (guidedChecked 6) 16 256 32 chunk6x256 (@span_join (guidedChecked 6) 16 272 16 chunk6x272 chunk6x288))))) (@span_join (guidedChecked 6) 160 304 160 (@span_join (guidedChecked 6) 80 304 80 (@span_join (guidedChecked 6) 32 304 48 (@span_join (guidedChecked 6) 16 304 16 chunk6x304 chunk6x320) (@span_join (guidedChecked 6) 16 336 32 chunk6x336 (@span_join (guidedChecked 6) 16 352 16 chunk6x352 chunk6x368))) (@span_join (guidedChecked 6) 32 384 48 (@span_join (guidedChecked 6) 16 384 16 chunk6x384 chunk6x400) (@span_join (guidedChecked 6) 16 416 32 chunk6x416 (@span_join (guidedChecked 6) 16 432 16 chunk6x432 chunk6x448)))) (@span_join (guidedChecked 6) 80 464 80 (@span_join (guidedChecked 6) 32 464 48 (@span_join (guidedChecked 6) 16 464 16 chunk6x464 chunk6x480) (@span_join (guidedChecked 6) 16 496 32 chunk6x496 (@span_join (guidedChecked 6) 16 512 16 chunk6x512 chunk6x528))) (@span_join (guidedChecked 6) 32 544 48 (@span_join (guidedChecked 6) 16 544 16 chunk6x544 chunk6x560) (@span_join (guidedChecked 6) 16 576 32 chunk6x576 (@span_join (guidedChecked 6) 16 592 16 chunk6x592 chunk6x608)))))) (@span_join (guidedChecked 6) 320 624 320 (@span_join (guidedChecked 6) 160 624 160 (@span_join (guidedChecked 6) 80 624 80 (@span_join (guidedChecked 6) 32 624 48 (@span_join (guidedChecked 6) 16 624 16 chunk6x624 chunk6x640) (@span_join (guidedChecked 6) 16 656 32 chunk6x656 (@span_join (guidedChecked 6) 16 672 16 chunk6x672 chunk6x688))) (@span_join (guidedChecked 6) 32 704 48 (@span_join (guidedChecked 6) 16 704 16 chunk6x704 chunk6x720) (@span_join (guidedChecked 6) 16 736 32 chunk6x736 (@span_join (guidedChecked 6) 16 752 16 chunk6x752 chunk6x768)))) (@span_join (guidedChecked 6) 80 784 80 (@span_join (guidedChecked 6) 32 784 48 (@span_join (guidedChecked 6) 16 784 16 chunk6x784 chunk6x800) (@span_join (guidedChecked 6) 16 816 32 chunk6x816 (@span_join (guidedChecked 6) 16 832 16 chunk6x832 chunk6x848))) (@span_join (guidedChecked 6) 32 864 48 (@span_join (guidedChecked 6) 16 864 16 chunk6x864 chunk6x880) (@span_join (guidedChecked 6) 16 896 32 chunk6x896 (@span_join (guidedChecked 6) 16 912 16 chunk6x912 chunk6x928))))) (@span_join (guidedChecked 6) 160 944 160 (@span_join (guidedChecked 6) 80 944 80 (@span_join (guidedChecked 6) 32 944 48 (@span_join (guidedChecked 6) 16 944 16 chunk6x944 chunk6x960) (@span_join (guidedChecked 6) 16 976 32 chunk6x976 (@span_join (guidedChecked 6) 16 992 16 chunk6x992 chunk6x1008))) (@span_join (guidedChecked 6) 32 1024 48 (@span_join (guidedChecked 6) 16 1024 16 chunk6x1024 chunk6x1040) (@span_join (guidedChecked 6) 16 1056 32 chunk6x1056 (@span_join (guidedChecked 6) 16 1072 16 chunk6x1072 chunk6x1088)))) (@span_join (guidedChecked 6) 80 1104 80 (@span_join (guidedChecked 6) 32 1104 48 (@span_join (guidedChecked 6) 16 1104 16 chunk6x1104 chunk6x1120) (@span_join (guidedChecked 6) 16 1136 32 chunk6x1136 (@span_join (guidedChecked 6) 16 1152 16 chunk6x1152 chunk6x1168))) (@span_join (guidedChecked 6) 32 1184 48 (@span_join (guidedChecked 6) 16 1184 16 chunk6x1184 chunk6x1200) (@span_join (guidedChecked 6) 16 1216 32 chunk6x1216 (@span_join (guidedChecked 6) 16 1232 16 chunk6x1232 chunk6x1248))))))) (@span_join (guidedChecked 6) 624 1264 632 (@span_join (guidedChecked 6) 304 1264 320 (@span_join (guidedChecked 6) 144 1264 160 (@span_join (guidedChecked 6) 64 1264 80 (@span_join (guidedChecked 6) 32 1264 32 (@span_join (guidedChecked 6) 16 1264 16 chunk6x1264 chunk6x1280) (@span_join (guidedChecked 6) 16 1296 16 chunk6x1296 chunk6x1312)) (@span_join (guidedChecked 6) 32 1328 48 (@span_join (guidedChecked 6) 16 1328 16 chunk6x1328 chunk6x1344) (@span_join (guidedChecked 6) 16 1360 32 chunk6x1360 (@span_join (guidedChecked 6) 16 1376 16 chunk6x1376 chunk6x1392)))) (@span_join (guidedChecked 6) 80 1408 80 (@span_join (guidedChecked 6) 32 1408 48 (@span_join (guidedChecked 6) 16 1408 16 chunk6x1408 chunk6x1424) (@span_join (guidedChecked 6) 16 1440 32 chunk6x1440 (@span_join (guidedChecked 6) 16 1456 16 chunk6x1456 chunk6x1472))) (@span_join (guidedChecked 6) 32 1488 48 (@span_join (guidedChecked 6) 16 1488 16 chunk6x1488 chunk6x1504) (@span_join (guidedChecked 6) 16 1520 32 chunk6x1520 (@span_join (guidedChecked 6) 16 1536 16 chunk6x1536 chunk6x1552))))) (@span_join (guidedChecked 6) 160 1568 160 (@span_join (guidedChecked 6) 80 1568 80 (@span_join (guidedChecked 6) 32 1568 48 (@span_join (guidedChecked 6) 16 1568 16 chunk6x1568 chunk6x1584) (@span_join (guidedChecked 6) 16 1600 32 chunk6x1600 (@span_join (guidedChecked 6) 16 1616 16 chunk6x1616 chunk6x1632))) (@span_join (guidedChecked 6) 32 1648 48 (@span_join (guidedChecked 6) 16 1648 16 chunk6x1648 chunk6x1664) (@span_join (guidedChecked 6) 16 1680 32 chunk6x1680 (@span_join (guidedChecked 6) 16 1696 16 chunk6x1696 chunk6x1712)))) (@span_join (guidedChecked 6) 80 1728 80 (@span_join (guidedChecked 6) 32 1728 48 (@span_join (guidedChecked 6) 16 1728 16 chunk6x1728 chunk6x1744) (@span_join (guidedChecked 6) 16 1760 32 chunk6x1760 (@span_join (guidedChecked 6) 16 1776 16 chunk6x1776 chunk6x1792))) (@span_join (guidedChecked 6) 32 1808 48 (@span_join (guidedChecked 6) 16 1808 16 chunk6x1808 chunk6x1824) (@span_join (guidedChecked 6) 16 1840 32 chunk6x1840 (@span_join (guidedChecked 6) 16 1856 16 chunk6x1856 chunk6x1872)))))) (@span_join (guidedChecked 6) 320 1888 312 (@span_join (guidedChecked 6) 160 1888 160 (@span_join (guidedChecked 6) 80 1888 80 (@span_join (guidedChecked 6) 32 1888 48 (@span_join (guidedChecked 6) 16 1888 16 chunk6x1888 chunk6x1904) (@span_join (guidedChecked 6) 16 1920 32 chunk6x1920 (@span_join (guidedChecked 6) 16 1936 16 chunk6x1936 chunk6x1952))) (@span_join (guidedChecked 6) 32 1968 48 (@span_join (guidedChecked 6) 16 1968 16 chunk6x1968 chunk6x1984) (@span_join (guidedChecked 6) 16 2000 32 chunk6x2000 (@span_join (guidedChecked 6) 16 2016 16 chunk6x2016 chunk6x2032)))) (@span_join (guidedChecked 6) 80 2048 80 (@span_join (guidedChecked 6) 32 2048 48 (@span_join (guidedChecked 6) 16 2048 16 chunk6x2048 chunk6x2064) (@span_join (guidedChecked 6) 16 2080 32 chunk6x2080 (@span_join (guidedChecked 6) 16 2096 16 chunk6x2096 chunk6x2112))) (@span_join (guidedChecked 6) 32 2128 48 (@span_join (guidedChecked 6) 16 2128 16 chunk6x2128 chunk6x2144) (@span_join (guidedChecked 6) 16 2160 32 chunk6x2160 (@span_join (guidedChecked 6) 16 2176 16 chunk6x2176 chunk6x2192))))) (@span_join (guidedChecked 6) 160 2208 152 (@span_join (guidedChecked 6) 80 2208 80 (@span_join (guidedChecked 6) 32 2208 48 (@span_join (guidedChecked 6) 16 2208 16 chunk6x2208 chunk6x2224) (@span_join (guidedChecked 6) 16 2240 32 chunk6x2240 (@span_join (guidedChecked 6) 16 2256 16 chunk6x2256 chunk6x2272))) (@span_join (guidedChecked 6) 32 2288 48 (@span_join (guidedChecked 6) 16 2288 16 chunk6x2288 chunk6x2304) (@span_join (guidedChecked 6) 16 2320 32 chunk6x2320 (@span_join (guidedChecked 6) 16 2336 16 chunk6x2336 chunk6x2352)))) (@span_join (guidedChecked 6) 80 2368 72 (@span_join (guidedChecked 6) 32 2368 48 (@span_join (guidedChecked 6) 16 2368 16 chunk6x2368 chunk6x2384) (@span_join (guidedChecked 6) 16 2400 32 chunk6x2400 (@span_join (guidedChecked 6) 16 2416 16 chunk6x2416 chunk6x2432))) (@span_join (guidedChecked 6) 32 2448 40 (@span_join (guidedChecked 6) 16 2448 16 chunk6x2448 chunk6x2464) (@span_join (guidedChecked 6) 16 2480 24 chunk6x2480 (@span_join (guidedChecked 6) 16 2496 8 chunk6x2496 chunk6x2512))))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x0 : span (guidedChecked 7) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x16 : span (guidedChecked 7) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x32 : span (guidedChecked 7) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x48 : span (guidedChecked 7) 16 48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x64 : span (guidedChecked 7) 16 64 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x80 : span (guidedChecked 7) 16 80 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x96 : span (guidedChecked 7) 16 96 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x112 : span (guidedChecked 7) 16 112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x128 : span (guidedChecked 7) 16 128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x144 : span (guidedChecked 7) 16 144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x160 : span (guidedChecked 7) 16 160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x176 : span (guidedChecked 7) 16 176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x192 : span (guidedChecked 7) 16 192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x208 : span (guidedChecked 7) 16 208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x224 : span (guidedChecked 7) 16 224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x240 : span (guidedChecked 7) 16 240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x256 : span (guidedChecked 7) 16 256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x272 : span (guidedChecked 7) 16 272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x288 : span (guidedChecked 7) 16 288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x304 : span (guidedChecked 7) 16 304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x320 : span (guidedChecked 7) 16 320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x336 : span (guidedChecked 7) 16 336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x352 : span (guidedChecked 7) 16 352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x368 : span (guidedChecked 7) 16 368 = true := by decide +kernel

theorem layer7 : span (guidedChecked 7) 384 0 = true :=
  (@span_join (guidedChecked 7) 192 0 192 (@span_join (guidedChecked 7) 96 0 96 (@span_join (guidedChecked 7) 48 0 48 (@span_join (guidedChecked 7) 16 0 32 chunk7x0 (@span_join (guidedChecked 7) 16 16 16 chunk7x16 chunk7x32)) (@span_join (guidedChecked 7) 16 48 32 chunk7x48 (@span_join (guidedChecked 7) 16 64 16 chunk7x64 chunk7x80))) (@span_join (guidedChecked 7) 48 96 48 (@span_join (guidedChecked 7) 16 96 32 chunk7x96 (@span_join (guidedChecked 7) 16 112 16 chunk7x112 chunk7x128)) (@span_join (guidedChecked 7) 16 144 32 chunk7x144 (@span_join (guidedChecked 7) 16 160 16 chunk7x160 chunk7x176)))) (@span_join (guidedChecked 7) 96 192 96 (@span_join (guidedChecked 7) 48 192 48 (@span_join (guidedChecked 7) 16 192 32 chunk7x192 (@span_join (guidedChecked 7) 16 208 16 chunk7x208 chunk7x224)) (@span_join (guidedChecked 7) 16 240 32 chunk7x240 (@span_join (guidedChecked 7) 16 256 16 chunk7x256 chunk7x272))) (@span_join (guidedChecked 7) 48 288 48 (@span_join (guidedChecked 7) 16 288 32 chunk7x288 (@span_join (guidedChecked 7) 16 304 16 chunk7x304 chunk7x320)) (@span_join (guidedChecked 7) 16 336 32 chunk7x336 (@span_join (guidedChecked 7) 16 352 16 chunk7x352 chunk7x368)))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk8x0 : span (guidedChecked 8) 9 0 = true := by decide +kernel

theorem layer8 : span (guidedChecked 8) 9 0 = true :=
  chunk8x0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk9x0 : span (guidedChecked 9) 1 0 = true := by decide +kernel

theorem layer9 : span (guidedChecked 9) 1 0 = true :=
  chunk9x0

theorem verified : ∀ k ≤ 9, ∀ i < counts k, guidedChecked k i = true := by
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
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)

theorem prismLower (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : canonical (evaluate p Prism.initial o) = Prism.target) : 10 ≤ p.length :=
  lower_from_checks (fun k hk i hi => originalChecked (verified k hk i hi)) p o hit

end PrismSignedFrontier.Certificate

end PEqualNP.Outside.L_meta_11088_aux

open PEqualNP.Outside.L_meta_11088_aux

theorem PEqualNP.Outside.L_meta_11088 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,o⟩
  have ok : PEqualNP.MetaComplexity.FanInTwo C := legal
  have hit : ∀ x, PEqualNP.MetaComplexity.circuitFun 7 C x = SevenVertexOneNot.target x :=
    fun x => (computes x).trans (SevenVertexOneNot.table x)
  obtain ⟨D,mono,bound,evaluates⟩ := SevenVertexOneNot.replacement
    (PrismOneNotBound.prismRequirement PrismSignedFrontier.Certificate.prismLower) C ok hit
  exact ⟨D.gates,D.output,mono,bound,evaluates⟩
