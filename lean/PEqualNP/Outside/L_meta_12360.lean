import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12360_aux

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
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2)) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length ≤ (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
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
  have zero : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have usable : Good t out := get_property _ _ _ _ zero accepted
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact limit,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  exact values x

end PetersenSignedSlice

namespace ThresholdReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) := Nat.testBit (4278124160 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [0,1]⟩,
  ⟨.and, [2,6]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.or, [2,8]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.and, [3,4]⟩,
  ⟨.or, [5,10]⟩,
  ⟨.and, [5,10]⟩,
  ⟨.or, [11,13]⟩,
  ⟨.and, [7,12]⟩,
  ⟨.and, [9,14]⟩,
  ⟨.or, [15,16]⟩], 17⟩
theorem size : witness.size = 12 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
theorem value : ∀ x, circuitFun 6 witness x = target x := by decide +kernel

abbrev Input := Fin 6 → Bool
def sliceTarget (x : Input) := target x
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- A signed binary program stores each wire together with its complement.
-- The entire six-input function is preserved, and NOT gates cost no steps.
theorem compileFull (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ p o, p.length ≤ (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = sliceTarget x := by
  let raw := List.ofFn (fun j : Fin 6 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let wire := fun j : Fin 6 => (fun x : Input => x j, false, false)
  let v := List.ofFn wire
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    have pos : (fun x : Input => x j) ∈ raw := List.mem_ofFn.mpr ⟨j,rfl⟩
    exact ⟨List.mem_append_left _ (List.mem_append_right _ pos),
      List.mem_append_right _ (List.mem_map_of_mem pos),Or.inr rfl⟩
  obtain ⟨p,o,small,ev⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins
  refine ⟨p,o,small,fun x => ?_⟩
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = target x
  rw [←start]
  exact (ev x).trans (by simpa [v,wire,circuitFun,List.map_ofFn,Function.comp_def] using hit x)

theorem replacement
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 11 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 6 D x = target x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, hit⟩
  · obtain ⟨p,o,sz,ev⟩ := compileFull C ok hit
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
    exact ⟨witness, legal, by rw [size]; change 12 ≤ C.gates.length; omega, value⟩

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

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 33) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 33) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 2112 := by omega
  have val : fullLanes = 2^2112-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 33) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 33) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 33) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 33) (xs : List Columns)
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
    (length : rows.length = 33) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 33) (bounds : ∀ r ∈ rows, r < 64)
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

end SignedFrontier.SmallCert.Minor1

namespace SignedFrontier.SmallCert.Minor2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfee8fee8fee8fee8
def negative : List Nat := [0, 1, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,2,3),(0xcccccccccccccccc,1,3),(0xf0f0f0f0f0f0f0f0,1,5),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xfff0fff0fff0fff0ffccffccffccffccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffa8ffa8ffa8ffa8ff88ff88ff88ff88ff80ff80ff80ff80ff08ff08ff08ff08ff00ff00ff00ff00fefefefefefefefefcfcfcfcfcfcfcfcfcecfcecfcecfcecfcccfcccfcccfcccfafafafafafafafafaf0faf0faf0faf0faaafaaafaaafaaaf8f8f8f8f8f8f8f8f0f0f0f0f0f0f0f0f000f000f000f000eeeeeeeeeeeeeeeeeaeaeaeaeaeaeaeadcccdcccdcccdcccccccccccccccccccaaeeaaeeaaeeaaeeaaaaaaaaaaaaaaaaaaa8aaa8aaa8aaa8aa00aa00aa00aa00a8a8a8a8a8a8a8a88aaa8aaa8aaa8aaa88aa88aa88aa88aa8888888888888888808080808080808055005500550055002aaa2aaa2aaa2aaa0ff00ff00ff00ff00ccc0ccc0ccc0ccc0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a02aa02aa02aa02aa00fe00fe00fe00fe00ee00ee00ee00ee00aa00aa00aa00aa0088008800880088000a000a000a000a0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2a898b2022c854b2052c5d4 else 0
  | 3 => if page < 1 then 0x2cae219d9392c688202978c0b1d302770c07d1a0193b00b0a301a28c0808c0092300783a0190b00b201000a1c0027700099c002570004f80010e0002f8000a70002380006e00015c0000f else 0
  | 4 => if page < 1 then 0xae9764ed9ce7688e643ea437483e30371c3e64ec023f019f018f015f011f00ff00ef00df008f004f003f002f001f0277008e else 0
  | 5 => if page < 1 then 0x67dde3f else 0
  | 6 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x24 else 0
  | 3 => if page < 1 then 0x2d else 0
  | 4 => if page < 1 then 0x21 else 0
  | 5 => if page < 1 then 0x13 else 0
  | 6 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 27
  | 4 => 25
  | 5 => 3
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 64
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 6)

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
  | 2 => 5
  | 3 => 18
  | 4 => 19
  | 5 => 8
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 20
  | 3 => 64
  | 4 => 73
  | 5 => 38
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 5
  | 4 => 5
  | 5 => 4
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 8
  | 3 => 10
  | 4 => 10
  | 5 => 7
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x102d5 else 0
  | 3 => if page < 1 then 0x2049823884c3691e018805 else 0
  | 4 => if page < 1 then 0x460189801bc0040a2309c00 else 0
  | 5 => if page < 1 then 0xc001010 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x600023112c1088222600204d315000702f000030 else 0
  | 3 => if page < 1 then 0xc42c3c8600481c224280082828426058070a06d051300940006823000287644003a541000002306d18c555580000320002e5d2000001c42a5a13419098de0501d270000a8311002d100101182f21c6e4 else 0
  | 4 => if page < 2 then (if page < 1 then 0xac64490092002b000220182355200098312084e00028280a64a1c5000281341339c81118a86280004d8000814940c427020000010001e0b9a52103052840070568b0588000e10000034461626e0211a3 else 0xa031300304b005159800) else 0
  | 5 => if page < 1 then 0x50000b4040980034d240020b40003ac0002801282000000240004709800010caa2 else 0
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
  (slot / 32,slot % 32)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s12]
  | 3 => [s12, s13]
  | 4 => [s13, s12]
  | 5 => [s13]
  | 6 => [s01]
  | 7 => [s01, s23]
  | 8 => [s01, s02]
  | 9 => [s01, s02, s03]
  | 10 => [s01, s03, s02]
  | 11 => [s01, s03]
  | 12 => [s02, s01]
  | 13 => [s02, s01, s13]
  | 14 => [s02]
  | 15 => [s02, s03]
  | 16 => [s02, s13]
  | 17 => [s02, s13, s01]
  | 18 => [s03, s01, s12]
  | 19 => [s03, s01]
  | 20 => [s03, s02]
  | 21 => [s03]
  | 22 => [s03, s12, s01]
  | 23 => [s03, s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s12_ok, s13_ok, s01_ok, s02_ok, s03_ok]

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
theorem chunk3x0 : span (checked 3) 27 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 27 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 25 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 3 0 = true :=
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
def target : W := 0x80fe80fe80fe80fe
def negative : List Nat := [0, 8, 9, 10, 11, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffaaffaaffaaffaaff00ff00ff00ff00f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f0faf0faf0faf0faf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaaa0aaa0aaa0aaa0aaa00aa00aa00aa008a8a8a8a8a8a8a8a88aa88aa88aa88aa88888888888888880f000f000f000f000a0a0a0a0a0a0a0a00aa00aa00aa00aa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x59301f60eb06d82380dc05e else 0
  | 4 => if page < 1 then 0x47d7e7f278fc5e1f else 0
  | 5 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1b else 0
  | 4 => if page < 1 then 0x13 else 0
  | 5 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 7
  | 4 => 7
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 3 => 4
  | 4 => 8
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 17
  | 4 => 38
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 3
  | 4 => 4
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x180 else 0
  | 4 => if page < 1 then 0xc001010 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1402112932c601540000019030 else 0
  | 4 => if page < 1 then 0x2c0022028b000b230025160029c000cc83430000100008298c0030519 else 0
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
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 7 0 = true :=
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

end SignedFrontier.SmallCert.Minor4

namespace SignedFrontier.SmallCert.Minor5

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xe8e8e8fee8e8e8fe
def negative : List Nat := [0, 8, 9, 10, 12, 16, 17, 18, 20, 24, 25, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,1,9),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 4 then (if page < 2 then (if page < 1 then 0x5f5f5f005f5f5f005555ff005555ff00555555aa555555aa5555550055555500555500005555000050505050505050503f3fff003f3fff003f3f3f003f3f3f003f3f00003f3f00003f00ff003f00ff003f003f003f003f003c3c3c3c3c3c3c3c333333003333330033003300330033002a2aaaaa2a2aaaaa2a2a2aaa2a2a2aaa2a2a2a2a2a2a2a2a2a2a2a0a2a2a2a0a22222222222222221f1f1f001f1f1f001f001f001f001f000f0fff000f0fff000f0ff0f00f0ff0f00f0f0ff00f0f0ff00f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f00000f0f00000f0a0f0a0f0a0f0a0f00ff000f00ff000f003f000f003f000f000f000f000f000f0000000f0000000e0e0e0e0e0e0e0e0a0aaaaa0a0aaaaa0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a00ff000a00ff000a000a000a000a00080808080808080803030300030303000300ff000300ff000300030003000300020202020202020200ffff0000ffff0000ff000000ff000000aaaaaa00aaaaaa0000ffaa0000ffaa0000ff880000ff880000ff000000ff000000fefe0000fefe0000eeee0000eeee0000aaaa0000aaaa0000aa000000aa00000088880000888800003f0000003f0000000f0000000f0000000a0a00000a0a000000fe000000fe000000ee000000ee000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xeeeeeeaaeeeeeeaaeeeeee00eeeeee00eeaaeeaaeeaaeeaaee00ff00ee00ff00ee00ee00ee00ee00ecececfcecececfcececececececececeaeaeaeeeaeaeaeeeaeaeaeaeaeaeaeaeaeaeaaaeaeaeaaaccccccfeccccccfeccccccfcccccccfccccccceecccccceeccccccdcccccccdccccccccccccccccccccccc44cccccc44cccccc0ccccccc0cc0ff0000c0ff0000c0c0c0c0c0c0c0c0bfbfbf00bfbfbf00bf00bf00bf00bf00afafafaaafafafaaafafaf00afafaf00afaaafaaafaaafaaaf00ff00af00ff00af00af00af00af00aeaeaeaeaeaeaeaeaaaaffaaaaaaffaaaaaaff00aaaaff00aaaaeeeeaaaaeeeeaaaaaafaaaaaaafaaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaaa88aaaaaa88aaaaaa2aaaaaaa2aaaaaaa0aaaaaaa0aaaaaaa02aaaaaa02aaaaaa00aaaaaa00aaaa00aaaaaa00aaaaaa0000aaaa0000aa88aa88aa88aa88aa2aaa2aaa2aaa2aaa0aaa0aaa0aaa0aaa00ff00aa00ff00aa00aaaaaa00aaaaaa00aa00aa00aa00aa000000aa000000a8a8aaaaa8a8aaaaa8a8a8aaa8a8a8aaa8a8a8a8a8a8a8a8a0a0a0f0a0a0a0f0a0a0a0a0a0a0a0a08a8a8a8a8a8a8a8a8888ff888888ff888888aaaa8888aaaa888888aa888888aa888888888888888888888800888888008800ff008800ff00880088008800880080808080808080807f7f7f007f7f7f007f007f007f007f00) else (if page < 3 then 0xffffccccffffccccffffc0c0ffffc0c0ffffaf00ffffaf00ffffaaaaffffaaaaffffaa88ffffaa88ffffaa00ffffaa00ffffa8a8ffffa8a8ffff8888ffff8888ffff8800ffff8800ffff8080ffff8080ffff5500ffff5500ffff3f00ffff3f00ffff3300ffff3300ffff0f00ffff0f00ffff0a00ffff0a00ffff0808ffff0808ffff0300ffff0300ffff0088ffff0088ffff0000ffff0000fffeff00fffeff00fff0fff0fff0fff0ffeeffeeffeeffeeffbfff00ffbfff00ffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaff88ff88ff88ff88ff7fff00ff7fff00ff77ff00ff77ff00ff55ff00ff55ff00ff3fff00ff3fff00ff1fff00ff1fff00ff0fff00ff0fff00ff0aff0aff0aff0aff00ffaaff00ffaaff00ff00ff00ff00ff00aa00ff00aa00ff003f00ff003f00ff000f00ff000f00ff000000ff000000fefefefefefefefefefefe00fefefe00fe00fe00fe00fe00fcfcfcfcfcfcfcfcfafafafafafafafaf8f8f8faf8f8f8faf8f8f8f8f8f8f8f8f8f8f8f0f8f8f8f0f8f0f8f0f8f0f8f0f1f1f1f0f1f1f1f0f1f0f1f0f1f0f1f0f0fff000f0fff000f0ff0000f0ff0000f0f0f8f8f0f0f8f8f0f0f0fef0f0f0fef0f0f0faf0f0f0faf0f0f0f8f0f0f0f8f0f0f0f2f0f0f0f2f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f000f0f0f000f0f0f00000f0f00000f000f000f000f000eeeeeeeeeeeeeeee else 0xfffffff0fffffff0ffffffeeffffffeeffffffccffffffccffffffc0ffffffc0ffffffaaffffffaaffffffa8ffffffa8ffffff88ffffff88ffffff80ffffff80ffffff0affffff0affffff08ffffff08ffffff00ffffff00fffff000fffff000ffffee00ffffee00)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xc29478c99477c29477a19477c2947694773894382f746126745b26946c5f945f38945f2c7a5f26755f26745f26725f26 else 0
  | 3 => if page < 2 then (if page < 1 then 0xc6911e1488e8e44785203c28f1e1470f0a34785143c2891e4440f0a207850e3c2861e12f1b0970d84b66c25a3612a9a8948d849e6c24e33b9c1a50e1328703c2341e1189b08c0d925e6c22f3509798e0bcd845c6c2281ba1325d098ac24c34c26194130cfc70c7c166330429e8198f00cc7802694380ba1304031ce018c700c5380619c0308e0158700a9380521c0284e014070096380361c0104e007270038380161c00a0e000a7 else 0xc2949380c2918046c2946d2fc29c9477be9c9477c293795fc294775fc288735fc285745bc2856f5bc2887159c293714dc2858047c6858046c2858046a3858046c2858045c2945f38946d5f38ad947735945f3735c2945f34c26d5f34c2745f26945f3326c285791cc2858018ad94770e88713c0385703c0300c29477ad9c9477c292715f) else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0xc2911e1440f096cd845e63c0330048ec023f6011bb008ad80446c0319e0184f00c07805ebc02ede0174f00b97805c3c02dde016cf00b4780593c02c5e0160f00af780573c0285e013570095b803e5c01aee00cf70063b802df80157c00a77004ff0024dc0112e0081700387801b5c00d6e0069b0031f0017f800aee005570029d8014bc008ee00457001ab800b5c004de001f7000eb8006bc0022e018c700c2380509c00e0e0001f else 0x6d34ce117baf8bdd845e7352fb61151e08a8f844e7c8263e1131e1098e664c7c2243e1119e2c8cf84427c1213d9909e3084f06433c2203e10f9f0878f843a7791ce610e1f086cf843278018e610c1f085cf842a7c2143e1099e604cf84227c2103c8874f0838f741c7b80e3d9071cdc38e5e1d6c20c3e1059e882ce7816ec20a3da851f0824f7c107c2073e0839e0c1e7840c7c2043e4019f080ce7806e3c033e1011f0804f28ef8) else (if page < 3 then 0xc2aa3e1541f0a9cf794e7c2a63e3529f0a94f714a7c29f3de4f9f0a78f853a7c29b3e14c9f0a60f852e7c2803e13f9f09f8f84fa7c27b3e13b9f09a8f84d27c2683e1331f0994f84c87c2633e1311f0980f84ba7c25b7612d9f2164f84b27c2563e12a1f094cf84a47c2513daa89f0940f269bac24d3e1251f0920f848e78046e63231f0918f468c7c2453e1219f0908f847076d383bb9adb08d4f7c6a7b4353b71a9cdcd4f28699 else 0x949380c614a498f230964d8550b26c28059348c023630a0119971008ccc280462e148a30e51b4d6328da5f8c26d2f36661130f0aac98785264c3c2ab211e1400e1b0a4c70784b2386c24b1c3611e0e1b08e8707845a38680460ea612c859b095c2cd84781663b0e0b36144018f09c00cb84b2066c23c03361402310024de720128ef900c2915805c48ac030a216019590700cbc238064611c031b08e0189847)) else 0
  | 5 => if page < 3 then (if page < 1 then 0x9ffcf7e77f37f99fcc7e5ff01f7dfbdfddfed1f66fb2fd93ec5f59fab7d53ea7f52fa8fd43e9bf4afa47d1be87f42f9afcbfe4df24f91fc87e41f1ff8f7c73e33f18f8afc53e23f10f877c33e17f0af84fc1fe0df03fc8ef09f74fb87d93d4ee6b72ff11dc3af847 else (if page < 2 then 0x6d2ff61133e088ef5643bc221bd410df0885f6442f8b217c090dcc886f0039e931cde10e3d2c73c7439b2d1cf61075ef03af501d7c20e7cc075e003aec81d7580ebab875d443ae8c1d7250eb90875c703ae241cfc20bbe105bef02deae17e3b0bf1d85bc482de1c1770e0ab8703df080df91847c2a83e14c1f0a00f84b27c2513c023730918f844c7c2213e10e1f0838f84167c203380647c030be0155f00a8f8053fc029be014bf else 0x2524f79184fc2bc7dfde3f0aa1f8530fc2807e12cbea147d84a37a851be128bee945f008dd9146de1233ee119eda6b7)) else 0
  | 6 => if page < 1 then 0x185fa8fcc7e03ea3f46f90fc73e1df0bfe13c3af847 else 0
  | 7 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x30 else 0
  | 3 => if page < 1 then 0x1002b else 0
  | 4 => if page < 1 then 0xec2b0ac2b else 0
  | 5 => if page < 1 then 0x2b0ac1b else 0
  | 6 => if page < 1 then 0x1b else 0
  | 7 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 16
  | 3 => 97
  | 4 => 236
  | 5 => 146
  | 6 => 13
  | 7 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 256
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 8)

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
  | 2 => 12
  | 3 => 58
  | 4 => 155
  | 5 => 117
  | 6 => 15
  | 7 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 42
  | 3 => 208
  | 4 => 558
  | 5 => 428
  | 6 => 54
  | 7 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 5
  | 3 => 6
  | 4 => 8
  | 5 => 6
  | 6 => 6
  | 7 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 8
  | 3 => 11
  | 4 => 12
  | 5 => 12
  | 6 => 8
  | 7 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x184ab0cc000488 else 0
  | 3 => if page < 1 then 0x11c70850c404c1d92820461c30c2483686b1504100300b00180008104014c00000b44804c280400700385 else 0
  | 4 => if page < 3 then (if page < 1 then 0x213150011060300040d0c0002020a071802020000040b00070504031704090c0f00001314020f00031b000001000003030116030100050011000007000600 else (if page < 2 then 0x50000060f0710001900040106020c0f0f1a09090d1117160e063c05060300060903002f010003000e02070004360204000a0004140f1b000300000400051405 else 0x111d2406060e13210318080700208301000c0004301f0b28240002)) else 0
  | 5 => if page < 2 then (if page < 1 then 0x3404c000e0410011800410c040608001b30004001428400058111505300900a3400420870021000401002811884c530b else 0x3cd6463060c900001940508600a1480004841cf0821cb04b0c02900a01c808c7820045c15c50c2) else 0
  | 6 => if page < 1 then 0x51c0100180080bc4005002 else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xa1a7808002890a050d0d6401254104800e638880022e0a600d400c6446618f614b67016c10030600056 else 0
  | 3 => if page < 4 then (if page < 2 then (if page < 1 then 0x4a0001640843f08e1398cb06612e6d8b809046cc02e3226b114897b0d032811dc86009acd88c02400e0b000c221163108001d87615e0d40009c055a4c5404e8002a10006a000000472370529181f8bc0441ec9e8 else 0x1820024d000900002533608c03c2289b42a0000b94268f0a18a11c29ed0cad31eab8f2c1301c8504d4968b02050f8850800000002f8440650a59b80002800028c88125400000036aa424584136a606180000000100000000) else (if page < 3 then 0x16c0005a062c00000000780b5e422c196d79ab05b208104138246a4135dcc3a8420b9c942807a0729701740004c2aa4f00010812b5d18acf819910054076aeb380829542e82349a1140000001c158800416b70a40b020a else 0xa1402184c0321441338004ecd01ac2b0060c29f42a6)) else 0
  | 4 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x65041aac63a8770000e309086e24606444f010950020b6e8000660cb67c60f88f000065276215074069b340910030e202512a82e10e92a16f03c06142619283070002179b0000bb0000b300004f6c863419194181564127e09203daa14280000 else 0x1c0d6a000867cd2000e063c6d827e61f08562e0000678000e16057180bc1ad06400009850000000003b0000799bd15200000d8dc8600d72690aa0c264066048b2630000e17a505e00009f8a378c95f03d83a0000c809a90004209715d0016) else (if page < 3 then 0x506541be41a0672d216b2c711ea3a2510000590e728505c08667d1b90546301290a90e41527450e508767a9b70a063b68f28d0b50be0b002a0a40040de8c007603505b1668000eb0af8e512290004d20000000f9181000aa64e60009e85b04b9 else 0x5705c41e8902000e80c3000015700098100066a000050cc00004a80bb0a7000e340007727f6000ae4701d305077746a0071525a8a3605a00009d00000007b1c70e603f0c612e9144da47d64b10e84d1d108463e28b0620e74780860ce0000cd0)) else (if page < 6 then (if page < 5 then 0xaf02b01c7000b650219740006648d8d500009369c09fa9b6670bd0a164b868864206011914656066295061671948b9c4a70be6744430490c429902d07d0768d660d0ac40005171244f4000de01d7a04b71000489c10e00330000000890000d11 else 0x666000531a269706d09c6000e70806c501b14f1d31521c32820591d5a362c20176810930d070d99778d2422470750167a6a5616c9a748a2be1551530118061b28ea22f1944dc4af20700812c1913000000270388a543100003704c6000ce2000) else (if page < 7 then 0x5c668acf0e10c98ca0e90bf2c402f0782830a945f61202169a03209766e0997580606000000000db8000730a60d004b0d90137720b201c6481d40a20056000700ea85a1440da0980b793e0d60000456482ba1436710a46cf6000a24556654571 else (if page < 8 then 0x732bb4000ac00002314d0000ae6c52410dc2000bf0000d980009ab9ea956581000000246702708498000000000000000000000d92000db0d70dd0000000000729000000480446940000000758d788866f8000390000840b10a44d20d807c0699 else 0x2306c06b8281c605404b26b0300000b40966000454ea0b61bb6b801267b0dc08a0942610c92199954100ab0090df08e07e19b40cb1f7000000987df6e40c24dd82c0cb0000)))) else 0
  | 5 => if page < 7 then (if page < 3 then (if page < 1 then 0x4215465545504a80004b06320005b74a08f50f07f65a75746600005971668a60000002526c03e07a050481014020061a6d03445b00913c16760007680003040d28b80cb3606c44f47002695202267e28072f05902944810c10008300b47a4000 else (if page < 2 then 0x2080006540008f70004910576665c05917b20f42a18900000e07122e60601468857c04e08218225e74a632443124040173233b2b78281c87b92417e06227501646c62d98a08662270000007b14766406147980295e60004905768f1167512000 else 0x6d17b05c17e84411568811014c22427215f76180009128d07242db0716928446d43766103612e48c10d91118f06203564f04801a90114642965108844365e15a08d446048572a1ab0000008f61300008704a20900f64106a00001100000001f0)) else (if page < 5 then (if page < 4 then 0x3748875064f68c05950b65f191819881186418033a0003403826416124667404b81c21200461701820004703906745d00000006010001e92f46169048d60007920005180003b82300007b30001c02168200c23a06f04427c86e0900730670850 else 0x6000000000c06311816110008800006860008e18b17701922b50008f48066b08b20006809060007282865685805f01217900000001f26a17204d25e54c00008a46507800002c75003d03e17184d80003f16907384505606b12b1584290414474) else (if page < 6 then 0x2020705405f50e13063164870005860000004a40000000000e20a00003107227606568400d84165301500007105620800000470000c96e17540000007260006280000007d95344aa0007440001846840d0000000000000556000278000698 else 0x2a65d10000000364400006d66916610102f61605e04005704b21441b070a1d85360b05446642636428600008863140000006308b00007a27b88e36484d04c85e4638))) else 0
  | 6 => if page < 1 then 0x37300080410050988411b67081907285000058525631c000b59220366963b710000062a086b187b03521340040b4685a7861605400 else 0
  | 7 => if page < 1 then 0x0 else 0
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
  (slot / 16,slot % 16)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s12]
  | 3 => [s12, s34]
  | 4 => [s01]
  | 5 => [s01, s34]
  | 6 => [s01, s02]
  | 7 => [s01, s02, s34]
  | 8 => [s02, s01]
  | 9 => [s02, s01, s34]
  | 10 => [s02]
  | 11 => [s02, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 7 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 16 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 16 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 97 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 97 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x224 : span (checked 4) 12 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 236 0 = true :=
  (@span_join (checked 4) 112 0 124 chunk4x0 (@span_join (checked 4) 112 112 12 chunk4x112 chunk4x224))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 34 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 146 0 = true :=
  (@span_join (checked 5) 112 0 34 chunk5x0 chunk5x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 13 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 13 0 = true :=
  chunk6x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 1 0 = true :=
  chunk7x0
theorem verified : ∀ k ≤ 7, ∀ i < counts k, checked k i = true := by
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
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 8 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 7
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    7 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor5

namespace SignedFrontier.SmallCert.Minor6

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfee8e888fee8e888
def negative : List Nat := [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨9,13,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨5,13,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨5,21,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffff0000ffff0000fff0fff0fff0fff0ff00ff00ff00ff00fafafafafafafafaf0f0f0f0f0f0f0f0f000f000f000f000eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a08888888888888888303030303030303022222222222222220000f0f00000f0f00000aaaa0000aaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0x3bf9fafcfdbebf4f9fcbe3f else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0x13 else 0
  | 8 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 7 => 10
  | 8 => 1
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
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 7 => 48
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 7 => 5
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 7 => 8
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0x22180791003e31c0b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0xa1389113615715633389110011400006088832082535200398059061286709407263204005040305800000000907400 else 0
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
  (slot / 16,slot % 16)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s23]
  | 3 => [s23, s24]
  | 4 => [s24, s23]
  | 5 => [s24]
  | 6 => [s01]
  | 7 => [s01, s34]
  | 8 => [s01, s23]
  | 9 => [s01, s23, s24]
  | 10 => [s01, s24, s23]
  | 11 => [s01, s24]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s23_ok, s24_ok, s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x55555555 0x210620a30e41251661a71e 4 7
    pinBase [0x0,0x55555555,0x0,0x44444444,0x50505050,0x55005500,0x55550000,0x55555555,0x11111111,0x5050505,0x550055,0x5555] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x33333333 0x110520930d41151561971d 4 7
    pinBase [0x0,0x33333333,0x22222222,0x0,0x30303030,0x33003300,0x33330000,0x11111111,0x33333333,0x3030303,0x330033,0x3333] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut46 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xffff0000 0x7de75c6da6585d65544d2450 4 7
    pinBase [0x0,0xffff0000,0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000,0xffff0000,0x55550000,0x33330000,0xf0f0000,0xff0000,0x0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut47 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xff00ff00 0x7de75c6da6583ce34c2ca248 4 7
    pinBase [0x0,0xff00ff00,0xaa00aa00,0xcc00cc00,0xf000f000,0xff00ff00,0xff000000,0x55005500,0x33003300,0xf000f00,0x0,0xff00] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 16 => cut15
  | 47 => cut46
  | 48 => cut47
  | _ => cut14

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0xc0fc0f3cf40fbcf else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 6 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then fastClosed target negative pool counts lookup steps k i
   else let c := selectCut (label k i)
        maskedCut c.mask c.patterns c.bound k (pool k i))
theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (fastClosed_sound target nonzero negative pool counts lookup steps k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change maskedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 10 0 = true :=
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
  · simp [counts]
  · simp [counts]
  · simp [counts]
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

end SignedFrontier.SmallCert.Minor6


namespace SignedFrontier.SmallCert.Minor7

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfeeafcc0feeafcc0
def negative : List Nat := [0, 1, 2, 3, 4, 5, 8, 9, 16, 18, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,16,17),(0xcccccccccccccccc,4,6),(0xf0f0f0f0f0f0f0f0,2,6),(0xff00ff00ff00ff00,2,10),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffff0000ffff0000ffaaff00ffaaff00ff00ff00ff00ff00fafaf0f0fafaf0f0f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaaaaaa0000aaaa00004444cccc4444cccc0000aaaa0000aaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x975 else 0
  | 3 => if page < 1 then 0x4998c9806e else 0
  | 4 => if page < 1 then 0x1bd7ee else 0
  | 5 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x18 else 0
  | 3 => if page < 1 then 0x1b else 0
  | 4 => if page < 1 then 0xf else 0
  | 5 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 3
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
  | 3 => 3
  | 4 => 2
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 3
  | 3 => 12
  | 4 => 7
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x2 else 0
  | 4 => if page < 1 then 0x2 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x20 else 0
  | 3 => if page < 1 then 0x240000008528104c0 else 0
  | 4 => if page < 1 then 0x5a6020010 else 0
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
  (slot / 16,slot % 16)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s12]
  | 3 => [s12, s13]
  | 4 => [s13, s12]
  | 5 => [s13]
  | 6 => [s04]
  | 7 => [s04, s23]
  | 8 => [s04, s12]
  | 9 => [s04, s12, s13]
  | 10 => [s04, s13, s12]
  | 11 => [s04, s13]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s12_ok, s13_ok, s04_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 5 0 = raw := by decide +kernel

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
theorem chunk4x0 : span (checked 4) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 3 0 = true :=
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

end SignedFrontier.SmallCert.Minor7

namespace SignedFrontier.SmallCert.Minor8

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfeeeeee8feeeeee8
def negative : List Nat := [0, 1, 2, 4, 8, 12, 16, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  | 0 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xaaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa00a0a0a000a0a0a0008888880088888800333300003333000030fff00030fff00030ff300030ff3000303030003030300022222200222222000ffff0000ffff00000fffa0000fffa0000fff00000fff00000ff000000ff000000fefe0000fefe0000feee0000feee0000fcfc0000fcfc0000fafa0000fafa0000faaa0000faaa0000f0fe0000f0fe0000f0f00000f0f00000f0a00000f0a00000f0300000f0300000f0000000f0000000eeee0000eeee0000e0e00000e0e00000cccc0000cccc0000baba0000baba0000b0b00000b0b00000aaaa0000aaaa0000aaa00000aaa00000a8a80000a8a80000a2a20000a2a20000a0f00000a0f00000a0aa0000a0aa0000a0a00000a0a00000a0000000a000000088aa000088aa0000888800008888000080800000808000007676000076760000707000007070000066660000666600003330000033300000323200003232000030f0000030f000003030000030300000300000003000000022aa000022aa00002222000022220000202000002020000010100000101000000ff000000ff000000aaa00000aaa000000fa000000fa000000f0000000f0000000ee000000ee000000aa000000aa000000a0000000a00000008800000088000000300000003000000022000000220000000a0000000a0000000000000000 else 0x3030f0f03030f0f03030baba3030baba3030707030307070303030f0303030f0303030303030303030303000303030003030000030300000302030203020302030103010301030103000f0f03000f0f03000f0003000f000300030f0300030f03000303030003030300030003000300030000000300000002a2a2a2a2a2a2a2a22aaaaaa22aaaaaa22aa22aa22aa22aa2222f2f22222f2f22222aaaa2222aaaa222222aa222222aa2222222222222222222200002222000022202220222022202020aaaa2020aaaa2020a0a02020a0a020203030202030302020222220202222202020202020202020002000200020001111eeee1111eeee11110000111100001110111011101110103050f0103050f01010f8f81010f8f81010f0f01010f0f01010303010103030101010f0101010f0101010101010101010001000100010000fff0f000fff0f000fff00000fff00000f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0a0f0a0f0a0f0a0f00ff000f00ff000f000f000f000f000aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa00fffff000fffff000ffffaa00ffffaa00ff00f000ff00f000ff000000ff000000fafafa00fafafa00f0fff000f0fff000f0f0f000f0f0f000f0f00000f0f00000f000f000f000f000eeeeee00eeeeee00cc00cc00cc00cc00aaffaa00aaffaa00aaf0fa00aaf0fa) else (if page < 3 then 0xa000a000a000a000a0000000a00000009898f8f89898f8f898989898989898988c8c8c8c8c8c8c8c8a8a8a8a8a8a8a8a88aaaaaa88aaaaaa8888f8f88888f8f88888aaaa8888aaaa8888a8a88888a8a8888888aa888888aa888888888888888888808880888088808080a0a08080a0a0808088888080888880808080808080808000800080008000777700007777000077707770777077707700770077007700767676767676767673507350735073507070ff707070ff7070707770707077707070707070707070700070707000707070007000700070005f005f005f005f0055ff000055ff0000555555005555550055555050555550505555444455554444555500005555000055505550555055505500ff005500ff0055005500550055005500000055000000545454545454545450f050f050f050f05050f0f05050f0f0505050505050505044444444444444443f3f00003f3f00003f003f003f003f0033ff000033ff00003333f0f03333f0f03333aaaa3333aaaa333333cc333333cc3333333033333330333300003333000033323332333233323330fff03330fff033303330333033303300ff003300ff0033003300330033003232fafa3232fafa32323232323232323230faf03230faf0322232223222322230ff303030ff303030f0f0f030f0f0f030f030f030f030f03030fff03030fff03030ff303030ff30 else 0xcccc0000cccc0000ccc0ccc0ccc0ccc0cc0ccc0ccc0ccc0ccc00cc00cc00cc00cacacacacacacacac8c8c8c8c8c8c8c8c0f0c0f0c0f0c0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0bbbabbbabbbabbbabbb0bbb0bbb0bbb0bababababababababaaabaaabaaabaaab3a0ffa0b3a0ffa0b3a0b3a0b3a0b3a0b0b0b0b0b0b0b0b0b0a0b0a0b0a0b0a0b000b000b000b000afaf0000afaf0000af00af00af00af00aaff0000aaff0000aafafafaaafafafaaaeeaaeeaaeeaaeeaaaafffaaaaafffaaaaafefeaaaafefeaaaafcfcaaaafcfcaaaafafaaaaafafaaaaaf0f0aaaaf0f0aaaaeeeeaaaaeeeeaaaaccccaaaaccccaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa2222aaaa2222aaaa00aaaaaa00aaaaaa0000aaaa0000aaa8aaa8aaa8aaa8aaa0fff0aaa0fff0aaa0aaa0aaa0aaa0aa0aaa0aaa0aaa0aaa00aa00aa00aa00aa000000aa000000a8a8fcfca8a8fcfca8a8a8a8a8a8a8a8a888a888a888a888a2a2a2a2a2a2a2a2a0f0f0f0a0f0f0f0a0a0ffa0a0a0ffa0a0a0f0f0a0a0f0f0a0a0ececa0a0ececa0a0b0b0a0a0b0b0a0a0aaaaa0a0aaaaa0a0a2a2a0a0a2a2a0a0a0f0a0a0a0f0a0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a000a0a0a000a080a080a080a080a020a020a020a020a000f000a000f000a000aaaaa000aaaaa000a0a0a000a0a0)) else (if page < 6 then (if page < 5 then 0xf0e0f0e0f0e0f0e0f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0aaf0aaf0aaf0aaf0a0ffaaf0a0ffaaf0a0ffa0f0a0ffa0f0a0f0f0f0a0f0f0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0a0a0f0a0a0a0f080ff88f080ff88f080f080f080f080f050f050f050f050f030f030f030f030f020f020f020f020f010f010f010f010f00ff000f00ff000f00af00af00af00af000fff0f000fff0f000ff00f000ff00f000faaaf000faaaf000f0f0f000f0f0f000f0e0f000f0e0f000f0a0f000f0a0f000f030f000f030f000f000f000f000f000a000f000a000f0003000f0003000f0000000f0000000eeeefefeeeeefefeeeeeeeeeeeeeeeeeeeeeeecceeeeeecceeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eeeceeeceeeceeeceeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceeaaeeaaeeaaeeaaecececececececececcceccceccceccceaeafafaeaeafafaeaeaeaeaeaeaeaeaeac0eac0eac0eac0e8e8e8e8e8e8e8e8e0e0f0f0e0e0f0f0e0e0eeeee0e0eeeee0e0e0e0e0e0e0e0e000e000e000e000df00df00df00df00ddddccccddddccccdcdcdcdcdcdcdcdcd0d0d0d0d0d0d0d0cfcf0000cfcf0000cfc0cfc0cfc0cfc0cf00cf00cf00cf00ccff0000ccff0000ccccfcfcccccfcfccccceeeecccceeeeccccececccccececcccccccccccccccccccc4444cccc4444cccc0c0ccccc0c0c else 0xfefe0000fefe0000fefafefafefafefafef0fef0fef0fef0feeefeeefeeefeeefe88fe88fe88fe88fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfcccccccfcccccccfbfafbfafbfafbfafaff0000faff0000fafafffafafafffafafafefefafafefefafafafafafafafafafafa00fafafa00fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0a0afafa0a0afafa0000fafa0000faf0fff0faf0fff0faf0faf0faf0faf0fac8fac8fac8fac8faaafaaafaaafaaafaaaf000faaaf000faaaaaaafaaaaaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f888ff88f888ff88f888f888f888f888f5f0f5f0f5f0f5f0f3f3f3f0f3f3f3f0f3f3f300f3f3f300f3f2f3f2f3f2f3f2f3f0f3f0f3f0f3f0f3f0f0f0f3f0f0f0f3a2f3a2f3a2f3a2f333f000f333f000f2f2f2f2f2f2f2f2f222f222f222f222f1f0f1f0f1f0f1f0f0fff0f0f0fff0f0f0fff000f0fff000f0ff0000f0ff0000f0faf0faf0faf0faf0f0fffaf0f0fffaf0f0fff0f0f0fff0f0f0ff00f0f0ff00f0f0fefef0f0fefef0f0fafaf0f0fafaf0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f05050f0f05050f0f03030f0f03030f0f000f0f0f000f0f0f00000f0f00000f0eef0eef0eef0eef0e0ffe0f0e0ffe0) else (if page < 7 then 0xffffa0a0ffffa0a0ffffa000ffffa000ffff88f8ffff88f8ffff8888ffff8888ffff8080ffff8080ffff3300ffff3300ffff3030ffff3030ffff2222ffff2222ffff2020ffff2020ffff0f00ffff0f00ffff0500ffff0500ffff00f0ffff00f0ffff00aaffff00aaffff00a0ffff00a0ffff0088ffff0088ffff0030ffff0030ffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffafffafffafffafffafff0fffafff0fffafafafffafafafff8fff8fff8fff8fff3fff0fff3fff0fff2fff2fff2fff2fff0fffafff0fffafff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeff00ffeeff00ffeeeeeeffeeeeeeffeeee00ffeeee00ffcfff00ffcfff00ffccffccffccffccffccff00ffccff00ffccccccffccccccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff00ffaaff00ffaacc88ffaacc88ffaaaaaaffaaaaaaffaaaa00ffaaaa00ffa0fff0ffa0fff0ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ff88ff88ff88ff88ff888888ff888888ff50ff50ff50ff50ff33ff00ff33ff00ff30ff30ff30ff30ff222222ff222222ff0fff00ff0fff00ff0f0f00ff0f0f00ff0f0000ff0f0000ff0aff0aff0aff0aff00fff0ff00fff0ff00ffaaff00ffaaff00ff00ff00ff00ff00cf00ff00cf00ff000f00ff000f00ff000000ff000000fefefefefefefefe else 0xfffffffafffffffafffffff0fffffff0ffffff00ffffff00fffffcfcfffffcfcfffffafafffffafafffff0f0fffff0f0fffff000fffff000ffffeeeeffffeeeeffffeee0ffffeee0ffffee00ffffee00ffffeac0ffffeac0ffffe8e8ffffe8e8ffffe0e0ffffe0e0ffffcf00ffffcf00ffffccccffffccccffffcc00ffffcc00ffffc8c8ffffc8c8ffffc0c0ffffc0c0ffffaaf0ffffaaf0ffffaaaaffffaaaaffffaaa0ffffaaa0ffffaa00ffffaa00ffffa8a8ffffa8a8ffffa0f0ffffa0f0))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xde6964d21eae5a9721e76429721e5e429721eae3e9721de62a9721de61a9721d7e427f21de6127f21d7e425521de6125521d7ea64d21d7e42425cde612425cc258a4231c852e4231e66129721e0e129721dee129721de6129721d8e129721d7dee9721d7d869721d7d2e6b21d7dd634e1e74fe04e1db4fe04e1eacfa04e1d7e1242bdd7e12425dc252e4217cf52e04e1d7d0204e1 else 0
  | 4 => if page < 6 then (if page < 3 then (if page < 1 then 0x908139bc90b3ad231802e9d00473a008bf40116e80207d0073de00e6bc01cb78038af0070de00e0bc01c078037ef006f9e00debc01bc780376f006dde00da3c01b2780362f006c1e00b0dc0141b8027fb004fb6009d5c0135b8025b7004ab60094ec00f2b801ccf002a7600546c00a7d8014db00243a00436c0081d800ffb001f76003e6c0076d800e9b001b3c0035f800617800bdb001736002d6c004c78008f7000e6e001c5c0035780062f000c1e00163c012d980001f else (if page < 2 then 0xe59657b42caf4a589f58987ea930fa5261f024c3f54967ea920f6f23ce9e479f588e7e911cf88239e84479c8c8f33d91e7d6231faa463e248c7ea914f211df3aa3a3f546e7b30ce78a199f10333ce0673968ce72a19ce4c339c8c673390ce65619ccac333c785cebc0b9754172f362e3e285c7bf8ad77a15cee42b5d5056ba98ad78a159e582b9a1056b2b8ae65715acae2b3e28507a409d74313ae3e22e48441c908679210af2a8115e74227c5044f2605cf02073c800dc else 0xd2c927d6919fab233e2a4679346a77a87ce590f9ed1e0bd2bbe7a5774faaea3f11c0e90b679266c4e42d2e485a3c90af39215c7242b6e48569c90ac792656ce42abe6d94ebda29d78253ce58a79e954b3932327b443af4a859c64ff98b9ff3923fcf0c7f9f08febdf9fd7b63faf687f5e08ff3519fd7143deb8c7b5ed0f6bd29e27a53b4f4a759f54e93d29ce7d6394f4a729d3ce53e51c8fb6391faa713c5cd9cc91b2d86365b7e6c76d0d8ea91b1d433669326cd6f0d4e)) else (if page < 4 then 0xeae50fc8c91fab913f571e7eae2cfd0c51f898a3f0b147dfe28fbcc51f718a3edb147db61cfc2c31f79863edb0c7db614fb4a4afab3f9e967f3d2cee74f9d4f4b399f5a713d2ce27999c4f0d389f1a70bda4e174f9c4f6d383e966f3e94d97d59b1f4b349e1a653da4c97a598cf4b2f9e965d3d2cb67a595cfad2a9f56553d2caa792954f212a9e32553c34aa7c2952f7f2a5ef254bd2ca27a593cfad269eae4d3d4c9a7a8934f4b269d3e4d3db498f2d934f4b259f564a7 else (if page < 5 then 0xeae04d66eae54d46e2628d4690ad0b98bcdbcb38b1484b38de484b2ceadbc8c3ead248c3eac8c8c3ea9ec8c3eb498663e9498663e8c98663d29586639315866390ad062cbcc845d8b1484578c8484574de48456cead98563ead8c563eace0563eaca8563eb498563eac98563db498563eac8c563ce9ec563ea9c8563ea95c5639315c563eb498503c84844f4de4844ecd2d98452908bc44ce24841cceac8c103006a643c0059e43c0058a43c0058243c006b637c005e629c0046629c0048625c006f242d005da2f9005be2f90053e2f9007222ed006da2ed004f62f9004b22f5004aa2f900743407007573e7007232e7007132e7007572c70075b2a7007572a7 else 0x3abc9cc4849a593485690007538921600393c490b001d2de485800e86f242c007137921600393b390b001bcd2c85800de60242c0071edf216003212690d001bc93485800d2e72374005e6df14c002f3218a60016290c3f000de4861ec005e642e5c003ab9abc9401d5e4dd4a00e76724250075735212803938a909401a593472200eae062e50075b89261803abb4930c01c3d2c98600de6964c30075b45261803ad42930c01d6d2c8c600e96964630075a4d231803316f6bc801a5b335e400eac999a30072e42b4600369215a30013f90ad3000954856980075702a718034b7545c401d5c09f060090be8f78006d2f27b4803ad813d8c01a5ba9ca200d2c98d92))) else 0
  | 5 => if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x1dfc6ff1b7c69f19fc63f177c5bf15fc55f14fc51f13fc4df127c47f117c43f107c3ff0f7c3bf0e7c37f0d7c33f0c7c2df0a7c27f097c23f087c1ff077c1bf067c15f04fc11f03fc0df02fc09f01fc05f00fee9d8bf796fe03f7efde3f68f9fee55b53ecffb3b6cb9b27788f718bc01f else (if page < 2 then 0xc2fe0ff03f7ffbefdcfee3f6ffb5fda7ecff65fb1fd87ebff5bfaafd3fe97f25f91fc7fe37f19f8bfc47e1ff0bf80fbffdfbef7f7afbc7ddfeedf75fb9fdcbee3f6dfb57da3ecff66fb2fd93ec7f62faffd73eb7f59fac7d3be91f47fa37d0fe83f40f9ffcfbe79f else 0xa87e9ffa77e9bfa67e95fa4fe7ff9e7e77f9c7e6df997e61f95fe55f93fe4df92fe49f91fe45f8d7e2bf8a7e27f88fe21f87fe1df7b7debf7a7de7f78fde1f77fdddf757dd1f73fdcbf727dc7f717dc1f6cfdb1f6bfda7f697da3f67fd9df66fd99f65fd93f647d8ff637d8bf627d87f)) else (if page < 4 then 0x4f839f6f046e9208dc9811b3d823655046c9e08dc840dee2019edf03794406f2700d73501bdd5ca9f898a3e96713d2caa7d6934e9f269f5646790b4b9b43daf4a729f548c7930ce600ebfc01d6f8035df006b3e00d5fc01aaf80353f006a3e00d3fc01a6f8034bf0068fe00c07c017ef802fbf005f3e00b9fc0171f802e1f005bfe00b77c0169f802d1f0059fe00b37c0165f802c9f0058be00b07c015ef802bbf00573e00adfc015af802b3f00563e00abfc0156f802abf else (if page < 5 then 0x250ade4915bfa4287f4450f2b0a1e49143fa0277f104efa109de8e13bcc02778ac4efb308bd21117a3c22f47445e8a08bd0c1179d222f39445e7188bd9b115f3222be28457c308afc6113f68227ddc44fa9089f43116e5422db7845e6e88bcdc1179b622f34045e5088bca011793e22f24c44f4108b67f116cdc22f1b045e3488bc6011789a22f0bc44fb78736970e6ede11df5422fe9045fb908be8e11dc2422f4b84765408eca411792422f9083bbc4073dba0ef2801de else 0xc00af76f15eeda2bddb057bb58af76a15eed02bdd9857bb18af76215eeae2bdd4457ba60af79715df242bbe40577eb0adfd515bfa22b7f0856fdf8adfbc15bf742b7ee456fdb0adf4915ee8c2bdd1057b9c0af73215ee542bdc9857b918af71d15bde82bdbc057b768af6ed15bdd82bdbac56f570adeac15dd4e2bda5456f4a0aee9315bd142bba1c57b410af67f15ecf62bd9e457b390af67015f8dc2bf1b057e2c8af65615ecac2b795457b2a8ade5315eca22bd94057b))) else (if page < 9 then (if page < 7 then 0x4b9b3dd535fb586af5bcd5eb31abcf43579ca6af6d0d4f951ab6ca3579346af5bcc7e7a18fd6f31ed7463f25cc7b9097371d2e6ef259ec2cb3dd296770f2ced7459f4989de9193bda523df0247bdbc8dbea919fd2233f0446bc988db9191b67b236ede3ef4847de6a8fbcd41f79383ef26c7de350fbd9819df0c33bf5866fe90cdf4219ee4c33b9ec67bc00c5f6f18be42317c845debc8bb7d5173fa62e7f485cfe20b9eff173d3e2e79ec5db350bbd1f15f6322bec5c57d else (if page < 8 then 0x859efb053df7ac7bdeb0f7bd29ef7a33def1c7bde18f7bb79ef7683deebe7bdd3cf7ba61ef7ca3dbf847b7efcf6fdb9edfb63dbf687b7ec0f6fc19eef823dde7a7bdcccf7b961eef2a3dee1e7bdc34f77851ef7083dedfc7bdbf4f7d7e9ef6fb3dedf47bdbe0f7b729ef6cd3ded767beaecf7b539ef6a43ddd3c7bda74f774c1ef6973decfe7bdc18edb449db7753977aa72be94e57c61caef9396f026ff748d9ee21b3da5367ade6cf508d9e931b3cda36798c6cf27cd9e else 0xcc343d6f687af2cdddbd9bbc9b36fd566bfa4cd7d099bb9333776f657a42caf71194fb7b1bd66637a30c6f4518de7a31bce5637aecc6dd3d8dbe4319fc6633f6cc67ed18cfc131af3d636e58c6bca98db6b31bd665ffb88b77b696feda2d1f2a5a6faaa7de954fbc0a9f72653ef5a8bede517dcc22ef8043f6f287ec850fdd2a1f78141efaa7fdf48ffbe21ff7a53fef307fde04ffbb79ff7423fee4c7fdc24ffb6d1ff6d53fed8c7fdf10fbbea9f37753df6327bec5cf7d)) else (if page < 11 then (if page < 10 then 0xead9afa5b35f315bbe629f7eb5277a5a4ef433fde627fbcc4f2f989cefa538deb271bd2ce37d59c5f4b38bf4a65bd2ccb76f996fa52adf1255bd2cab798956edf2ade96557eb49afd5935f4926be5e4d7c949af90935f1b26be324d7c549af86935f7f267efa4cfde499f4f935e8726dcaa4dbe948dfd191bf97217ed242f9fc8772a90ef010fddbe1fbe5c3df2687eef2f4ee95e9bd2bc377972efaae57f49c8fe4b89fac6bfaded7f661af7c034bd6f697a42d2edbda5b else 0xe248444ee950844bd2c98453e227c44e9090845c9089445ce91ec22beae04107eac98113eae040c7e4f1242ceac9856300726ebd005d24dd005d247d006b643d005d643d0069639d007562fd006962fd006722fd006062fd005e62fd0049a2fd004862fd0049a2dd005e61fd0045e1fd0048617d007260bd004860bd0072609d005e609d0074ba0f0075b88f0075388f0074b88f0074788f0072788f007577ef0074b7ef007277ef007137ef0074b78f0071378f0072772f0071372f0074b70f0072770f0075768f0074b68f0071368f0075766f0074b66f0072766f0070f4af006ff4af006f34af00722def0071edef0071adef006dadef006d6def006d2def) else (if page < 12 then 0x85a5cf795d25cf7ad2a24f73d2c98e53d29ece53b7c84d5ce9710d4ee4f10d4ed2c98d53b79ecd5ab79ecc7a90ad0b3cb79ecb3aeae048c7eae047c7d2c98673e95bc5cbbcc84579c35bc573eadbc56be95bc56bc15bc573eae60567eae18567eae08567eae04567ead2456bead0856beac98573d2c98573c3498573eac9856be949856be8c9856bc1498573eac9856790ad057ceaa24567bc9ec579829ec579c31ec573ea9ec56be91ec56bdc9ec56bc11ec573849ec56b801ec579b79a857a9315856bea95456bb792456bea924567d2924567a112456b9312456b3d92456bea910567930c8573d2c98513eac98507e4c844ed90ad04fce4c8445cbcc8445c else 0xce5be43cbcdbe43ce972642de4f1242dbcc861f9eaf27307eaf13307d2e62713eb74a4d3eaf4a4d3eb6964d3e96964d3e8e964d3e26964d3d66964d3d2e8a4d3d2dbe4d3d2d9a4d3eaf124c7e950a4cbead0a4c7d2c9a473eac9a467d2c9a433d2e61af6d2c99af3bcc85a5cbcdbda5abcdbd8daeae058c7d2c998d3d2c997f3d2c8569cc048569c9348569c90c3d69cd2c99693d2e71175d2c99173b7c850fcbcdbd0f9b7c84f7ad2de4f79bcdbcf79e9724f6be9710f6be9604f6beae04f67d2c98f73bcbdcf79b7b18f7ad2a70f73bca5cf79)))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x4f889e6a117b4b269c8569c0075be00d67c01a3f80301f005bfe00b47c0166f802c5f0056fe00abfc014cf80293f004e3e00997c0123f80243f00453e0087fc00f4f801e1f0038fe006bfc00d2f801a1f00337e00637c00bff8016ff002d3e00587c00a7f80117f0021fe003ffc007bf800e5f001b3e00357c0063f800b3f0011be001f7c0033f8005df000afe00147c0027f80045f00073e000cfc0011f8001df00023e00037c0117e8037ef006f1e0053ec007fd800d9e else 0x8208bf01117dfe22fbdc45f6d08bec6117d6822fa7c45f4b88be96117d1c22f9ec45f3508be49117c8822f90845f1e88be2b117c4a22fb1839f11073eb40cfc4419ff2423f3d847fc9077cd40ef8881dfea823fd5037c4406fde643de9711fc9e23fab26be964d7b7b1bd176376dec6defd8cf90ad3bbc5a3d68a7dbfcffbbc9efba53deede7bdbdcf7b4b9ef6ff367ade6af484d5d5a1abc963576de2bdf5456fe90adf4215ee4c2bd9ec57b9088bdc4113db422f27c45e) else (if page < 3 then 0x7a1efed53dfd8c7bfae8f7f5a1efe9c3dfd2e7bfa24f7f931cbe7b397dfe6cfe94d5fbc9abf6f357eae6afc98d5f909abf0a357dee6afb18d5f5a1abe97357d2c6af9ecd5f6318fe7b31fcd463fc84b3f3d967f81237f023efe9467fb78bbfd515ffa42bff1057fd28aff9815ff022bfdbc57fa10aff2615fe422bfb6857f6a8afec615fd682bfa3857f448afe7b15fcd42bfc9851f9089ffd2117f9222ff1045fd288bf79117ede22fd3045fa288bf42117e4c22fc8445f else (if page < 4 then 0xd65bffa5b7ff396ffe62dffc05bff79b7ffab49fe6271fe949bfd1937f8926fe964dfb7c9bf66937e8526fc9a47fd2c87f8090fedf21fc9a43f90c3ffa56bfef2d2ff558dfd2b1bf9c637f30c6fe498dfc0b1bf79637edec6fc998df90b1bf17637df8c6fbdd8df6ab1bf265ffd8cbffe9569fb7ad3f625a7e4cb4fc8569f632d3ec6587d68b0fad14ffd2a2ff6f43fdfe7fff54f7fd29eff9c3dff307bfe30f7fc09eff793dfede7bfc98f7f909eff073dfdf87bfbdcf7f else 0xeb697fd2d2ff59a5ff56dff))) else 0
  | 7 => if page < 1 then 0xd2fedff937e43f637d69f3dfcd5f15fc45f else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x48 else 0
  | 4 => if page < 1 then 0x14c410bc2f0bc2f else 0
  | 5 => if page < 1 then 0x41104410bc2f0bc2f0bc2f0bc1d06c1d else 0
  | 6 => if page < 1 then 0x2f0bc2f0bc2f else 0
  | 7 => if page < 1 then 0x1d else 0
  | 8 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 33
  | 4 => 370
  | 5 => 821
  | 6 => 260
  | 7 => 10
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 3 => 21
  | 4 => 202
  | 5 => 469
  | 6 => 210
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 75
  | 4 => 728
  | 5 => 1687
  | 6 => 756
  | 7 => 48
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 5
  | 4 => 7
  | 5 => 8
  | 6 => 8
  | 7 => 5
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 10
  | 4 => 13
  | 5 => 14
  | 6 => 13
  | 7 => 8
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x100c0ae004d4bc00a20f738ca3 else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x5008082060c2001214481000008a0004b801e04000021808300180030c1c8810008008000010e0004501044c00500141831a0c4810604480 else 0x3c0c80d0048287000400704001801e00a010008700020c68812242870c001020424381041008002099151800010005400f061c09004d4702) else (if page < 3 then 0x18480006001e192274023a45c18700049060608f83103400d08500071004d0a5e90104002000000001bbf20428f040419018587800030003 else 0x4a40104804802201)) else 0
  | 5 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1203060304010202000e0607000201030008000019050a010003000b1a0420001000021f0200001110021900000100020d030316030d00000003000130040000 else 0x1010305000b0c142400110103070402060006100e080c000b0600010a01020e00020702010504140100020004180106050000000100030607010103140000) else (if page < 3 then 0xc04010c02030813110500061008010004032f020e02000200020409010500000201160216010300230201000513023204010002000501000a030000000f0602 else 0xe023215010600002315020806010702050c060315012701020b000202023100050001020a00030400000020120301080b0303040000001d0901020300070404)) else (if page < 6 then (if page < 5 then 0x8150c081a090105000e3604063c050001180019282c30080c02002c00050f09040327001b01040105000108051c04011a0207010001030905220a150c000c00 else 0x81400060729060c08020602033a0b0100000437110b1200030202090a020009041a010d02142300111800230000002c120400040e1000060e00030b00041e0d) else (if page < 7 then 0x140d2323160a0d02181214050e35030a008824091a001e0f002600000d02010c11051d180b0b0022010906141c02002000090707010b2e00020c0b0004000300 else 0x32d05052c120006062b0330082500040000280301))) else 0
  | 6 => if page < 4 then (if page < 2 then (if page < 1 then 0x1608010000010f02000500000f0114010c2713050b03130800000302031402110700000c00080000021205090102000501080001000b00000a00050002000007 else 0x3305000206190702020309080044000000010f190003010309020300010c07060b0117002d03201000010615021501031108001816050b1c0802000d00020900) else (if page < 3 then 0x61300000101100a1005201b12070009083e170600020004060806226e0115030e100011000d060100070010080b2103000130b00300000a07000029061600 else 0xe010300010803130e69010e190a000119)) else 0
  | 7 => if page < 1 then 0x22180791003e31c0b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 2 then (if page < 1 then 0x681806413449400700f47cc00441b02c923400004d4c059061541b4000d4385e365120344108004074511280f7085a1141b5289c300000000c2380b158000510905c0206458200071789013c09521000 else 0x1d04c0005d140000040d400341f0) else 0
  | 4 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x5bc00011b003d8001da800080005d8524c945d032429202d1b800000e8715000020ce1c02d087833112e05101c00000001031b008002bd311200014000010a0b0004a67ab4930c85601f262406383d523693f9010a7a9fa66d000000008b11364209181396193 else (if page < 2 then 0xa103bc88273b35a04650ca25a52fb47802762a10005a042b6000b403180ced713ad20001d080000000ad8ba16a40000c803a42e15108000000cf42430000f48000af82129181712b7b17826a0b201400c157eccc043d0002cc4000000508ca247e05a859da0cb5aa else 0x1526e74704150fccb48000b11a700f672700004c514210506dbb8891606400bc9240fe07616288a4258053013b0001d481ca0fa4c00000fe08f83042de84d04950315d6a45739892c4ab2000541000000000013957996aca524a4be81214000ae937cd9a8000)) else (if page < 4 then 0x54000000000000000000009f000017c71d220800016540000000000f86040a81d7d9001170183cf00900e3200000013571963c9d78e4a15c326abe92180f83738d0a6bad677b1cd4d0760b00b7900024a4c302b03812dc8b9299035500000000001404548093 else (if page < 5 then 0x5603082442de0332dac15e09ba1198d5064ee1183227e8d6058118a3e467609da6713c02940000aa85c406006101b8262cf4767026010c43e40e90000c62da96f17888bc16e52f07b28800000693739bfcda20000000404dae000013c51aad6c0000000000346a70 else 0x4a000202000000048c1d00000a0500010b400000040666e1190a2011d00000001a88a08180f100001bc1d350205201d000006247aaa398000ef323814ce9c94005d0d4829804a26e89b8e380bb0b7bce82620eb09a03e156cc6b31d156e5fa12006a0cf42834390))) else (if page < 9 then (if page < 7 then 0x1311cd4648cb1000020574556000000016602420c003ea6c000000000025415305e02f4c0000002095a411e80009ea5740b205cab1000001460002702341c84000ae4310287345016a4241a28d4064207198674b1000254000022200000000cb6100000000000000 else (if page < 8 then 0x733d694d2d0533381bdaa8061155a8c0ecc14f09ab4fc220099a228d8d9e86304b680c45b28585310494e8b30b87f415005448909788b828e7650568524ad88be09289080a4071148d15c2a210454701c0240a4f534043a0668733ae153292650b062a100e3402c0 else 0x9e20e9a8c03a00004f15b8ea3a3701b01400000b7c4e1ab676291983200d4751194000000000006920f00e280b56d08ed8e207737d28c0562cd7468249829008d733a3c800003d0000052e2c00003b2cb82c900009681bc4000140018034254cf331584859284f71)) else (if page < 10 then 0x3d900015760842f415213306009142942000250878ab6cfb39758001ac0d840000d086a05c04453b041a96ba90821a8e607d0b19b0002854d481183c1ca28e169a22819220149728040ecd6a046d13c0b764418a04602ac31d063218c06c12e30000002100000 else (if page < 11 then 0x89180270739150a4480e414d021b1990be13901f80611a8b0740000000001570129ce011ad2404a0a88c000f2200008543654848184499fe05b044909467c7590290b2a970c931b7059195c08d13a82581d02fc3b68d2c15412b038ac3080c20000493b80000192 else 0x7104a40ee0a308699790d0c5911f0298d41676097485acf060001b1469870822040ba3e80015a6)))) else 0
  | 5 => if page < 27 then (if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x6d5a5503c552c09e0c5065a40fb00cd2fa6bf80a3017832c17d810a1ca8020a01ad922b0d08c65f81d102a430900000000cc000002f800b07ec40000000fa00000b3037433100859a23a600bd5c788000b65a6630181e204dc924000000006506a760002c3000000000000000344a592 else (if page < 2 then 0x6f002608d6f226412ac50300a3a09025e5608069c643c2ee6658608b8dee03946c16273662b547f042b695d5820826c0f68f697c41b01516a8015266bd7210b2c1630868a09ab041f5046dc8860901486318a7112166dc0c704b7175843d37f4e33641542a26902614a60570005ca782 else 0xca02e20081859773081400b9a951bc404c101149861d81c2a9fd90c86bd2051a728000c01a6724f818700001d561a2800089804000001f7033c19a0c680f2345000e084cc0002c93211ab020eb0001610c20506084c70d66c41f966252f80a7467a3a512a10672578200000000001d60)) else (if page < 4 then 0xc619a55a791b4066269e1a1c09907601e10390635551944f07805fb93b91880500dca238029c8a7131b092e26002e0ad502c155f1a3481e2c741a3104c03a00c85d9095c28b128ce2c219da31800d83200002ab0c2c29c75742d2031cdf91c264d708f0000000008362c40000a3c0106 else (if page < 5 then 0x1890b2122b8ae80394a75d6004204000a161a760000000580400000000000001df1000000000025247ac103600000000002971295000000018c6adc72d04c2a0746ac1e50be1acb402017b0425c6a60752db0666452138c30d0668c3718519501048f2b05bcc1d67e01d41b841fe0 else 0x4ba80008c1b1606800463c95142056d4000b3c2ce5ab80e503b4a551a181aa00000163172a190c1832d1a585593591a510558100a2884000bac69b540d02d0bf027b034d82b146e98b3000304021ec000b7c87b614ad6500000b21000017300000000000000000000062c00006840000))) else (if page < 9 then (if page < 7 then 0xabda0dba2c28a10d010700000000000000000017200002be0000000089c01d0ba815f479d6166aa0000000000000001d5000026730b58000b250000634195057c897690c202656595e42e41f73152c00026003e60002ef504e71990000000c9c04130002894846d7e35f955e00001354 else (if page < 8 then 0x2ec68fa5e8100403f38dc13b0a959fb3c324ac668468197f014c11fa8490ca40000734f0a67e5c000a1180008a98ec3598000057c0ae10d057e1b3d1f423bd1cd6b081ff679000e100014a69d48bb00001bd07561ca7688400000023879a9120000013040001f583224000 else 0x65cc7b0cb10000118258598c1450000188400000000000000730000000017e45fc5db0cca8000cd000006c026706acaa903ccd8b50044e66bc80e80bac18a1339a70a2e8c000680c00099940858a9c23a2d4f291974000099c71c2a918515128512054027c20dc293a47c2a36ac81030)) else (if page < 11 then (if page < 10 then 0x29c07105bd58bb4f008079855ad0c1c6662cc90000314c1900a423b06e0507706d6b36474891600002040000b650002af00001902000204b68041b4cc19c0a60c02c29f885f327d9471000000000023200000000000086b000000000000a10000e6000008395bc332670e8a4597d5932 else 0x1fe800000000004b4000099d2ce320c00007cc20aa1f50000368c3c05d827732b428e142da2440d88000a980fc2b59a53271a9bc60f66837994459093022f046aad707781f791801162c5c08976588000832e186a4800004240a76a0d9ed1300e5b000004310000ae461008a20000000) else (if page < 12 then 0xbec20fba740000bad59f2000077352c06d042831505bd2da312c10c092407c1b3830a0178c996738062b6490e90b10ad21242a38036801831fc0d63b742020a9c1fb673980000001a700000ee19fc0cc000000000001ac638d98b950d411023a800076ab2e29cc86b022408386000330 else 0x968ad60a7025723401d11c442c1403c2a203705a86a4050b44a430c3b5864368702df000010711a81080ac0000000009b23a8400051556b092d92324d9b0c0938b1c05fc193415980002f968c1331ac70000000000007a3c8c111065480000dc89506204f501d111e64a89a430249be9)))) else (if page < 20 then (if page < 16 then (if page < 14 then 0xe4637aa7c0000a89a00011cd7107281dc10000e311958000ba01ac018808103e241a0a004550631e76a0b2558683ab3300000000b001fb049c22e063858e09e4cf749d029041745470bc016f2aa827924082c014dc18502a82b9116594439c1c9265116322a2d1d96b5010d02d498a0 else (if page < 15 then 0x55c2b404c82b163c067e07c029da00024109a1000036c00440002130160000000002364f426445696bb091e949695d14542f4aee165800c05808a103e4c00000000009f4c00018400004418000000005a00002f10291c8a00029a000014f6000000000028d1b40000000005200002661 else 0x2f8a74200032b4b2900007c064d0b600fe0cc59b2023db222c482450251a7a288523abb181fb8a54248ac1a41b12500e34458112a04d8c69b4411e04b5cf490002da63588000742800000000000002220c7830300000000bf993240000591adc1c5a6c1974159c191200021967990c34)) else (if page < 18 then (if page < 17 then 0xc7c09a608c0eb038909d27a807c02c014130001cd26d943109c90000b201a201cd558457ce5844709d3195cd3601086d51b681410c60069002108b9c8014334042d914e40496ae42f7053000008b6000014a96c000000002d4030600012b6a5d2c403352f60881202899143a1120c5e2 else 0x9990000925872000011a021e800037805ba02889f04f4d3a487c5bf7b0d87e4a11ecf500018916ac5460a4c17e607698416dd206b4d4288057d72f3b789ef1cbd1425a5c24263dcaec01188e3737d196865986404608c2984282217eca9e526ccec2bb064e16a410764e012f07dda1a0) else (if page < 19 then 0x4840a205cc00005345172a6c0000ad826e75b969410000bf21aea2d0ac051520609920b781944000178000010e700000000e030f22dce2b0bb81c4a8c01f10b9813b4b506b509ad25e07e830935b90d52bd430b6416c7c60ec134281685f0324ed301d41fd64a811244099a4682e8b83 else 0x20830869a5000007d9fd064c5bb000023105e800002988000641800000000000ed27d25358000c18e4f00000000a350441994025043442725bc6a402359a800000000000000089553848e425009299a02c3c000003440007c830101c01282a780443c6400001809ad66500c490002075))) else (if page < 23 then (if page < 21 then 0x4fc489a0542f947bc144000008430000c200002e443fe8025431a07a2e4d9e6bf412227340b4351902e05795f9090830506440fc00a44e13b35207ba75a59005c05a470918100459c1100021508fe7240c880322af40000b6404531b817865009c7a95c700000023d0000000085c9ae5 else (if page < 22 then 0x88c52b013511c93b802079b51ae443040000a003b141109e061a8d466400ec05b402000001cd10fa61d38d1496030402fa49827b3ba42ff62beb0206e800004dc54c4000000015826c45542bfa058800094cc000ac19d76b9c21820706cd052c80000002a3000015c600021564e52460 else 0xac986ca6301a6567cf0a92a197506347342c3828e06cc2010409000050c27f2000000074824417718000c3df07018c8390b80800000006f224e8000670c09307c00008a4c0004c40f6324d8a551943061bcc236531c82969889fc2a858f59b800000bbc2f907904f837f60000c500ab0)) else (if page < 25 then (if page < 24 then 0x1b0b906994bd00000900eff06422911cb08e4000004a0000018000005704fd24c139c106b75c0b04360c0007f48c600bd9e301e12b807fc022ab30214014e8ca020cc3e08e2a2a087098741403130270133001c254144000007f64fd0af2a620678095a812b32583eb327774132a else 0x7019d30c470a15a80d820bc17d04668ce414c4920161a12952d8bc00d5d3260bd179066cd98053800009980fa300017700001cf34d02e94a708000b9464f100000000000d3200004d54dd258019aa9d4a6eae9610193d285c15b64f930962ed639a67c310093800003d800000489b90) else (if page < 26 then 0x86007464e1a1b3050d93097004e0574479085c6823b8c3343818d0147068a0643995369418000a4da0a700c0bc20403260000000000022814942ed0c9d10b15b86a507b8c360ab418f034c168032c3314b94275372662a1be455465f061e47b05da099d412976191305398220c64e560 else 0x84900029903482b1063c7321768400061810007a45a30569a8a485810da00026f7b242e4072c0dc0))))) else 0
  | 6 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x4a93f05ee0ff15e824840006a15a0bce0000f5400000000008d1338a68de4000071c93195e0fe200000000008d40000001400867360a1096c21334ba3b00e84fa07e88000000df85a200000000003033940000000740358176cc73588000138a3e43b83a81480000 else (if page < 2 then 0x3e00000000d360400000a4200080835cc68480a570081042cea64898000882cdb000074d9200007620001c82e022bb3300f2e5d06892440fc01867b8b58c5e46e06bca7c5aec3322e006c0ac2cb048a9e519703b003183503c44d33781809dc6ae340319451341f0 else 0x5d93cc80000002e915810a21665182c88000d333b00b9d060f721f00228bc87c60001241ae09320000000f608a400000001a2b40428195186c0a4620c058060f002419591e800000000000b40d6273c324800064004d026c00000021200002841295d02b01ca6000)) else (if page < 4 then 0x3bb0f8466662900023ca0062a0431229c422612690174cf228b47ba3d81300d39580aa01dac5224501f401028aa3c80189c027504f1adc0a40e261a80f407267120788105544eb2175152c120c104aa87020124205d9b061364ce000503d16b42c04b896010ec01a else (if page < 5 then 0x1680001da0e610421214160b0065900000000003c0201177273412b25155c44a63c5324c0000003da34c98e000001119a8b84950681ab4966c7a22680000940cb60000000356a70345b741da60606fb16c08a4c0666d01cd00ea52048850d84068a5f800012a68b0 else 0x4190fc0d48c21624350056c2895821da9880608589800020018040029810e0e304d83945f043c04511f1d180a137f300012667da3b3a94d866b901c12ad8546fd02fd12c086c9200002795fc2e692308c80eccb120002349c40df34b12ccd38800076ca2c40004c0))) else (if page < 9 then (if page < 7 then 0x5411841d06288479b7c97c40a07f011c400077770424144cc8e01fd0d8d02c1810d52a80000eb00000000a4cc600000c0db62f10000000188c0000002005942d7800014198642f348a14d8e20ca96c0ba59b20e7676c0e0d222dc07292c8c6c40236fc9d50aa60b1 else (if page < 8 then 0x81807411420000002bd8dc423a21a36019e01e3301a09d66011000000005200204ea0001e6c7a10003d593026b020813493e03800001cc0bea050698330caa4fc05a32354000c001d3209050c7a04ca97dc2c000080029097c6e00000324400000061c89814a01c6 else 0x304a080e82da022000019925f10002ec0000e720003d40000650034b400e80e890f018cd2a80007932ee000000077881015a001b60ca34de250203b92e04c0095119185e9ae4b807c190e91a0d84420048c0000e042920a86201d27f4188c86e4f0759a64d7c2276)) else (if page < 10 then 0x521c089be04506a834e102094423a2f017c0ee035012450cc4ea0623544a944b63e100015066b2189288c0000003482688000a90000054000000000017d190000028038cda20c42059054847600056b0000800196561b84000000000000016403a00a00001f60000 else (if page < 11 then 0x3409044ff06d308998707020000000a60b7600010c50c07001d08001c0c0003f8344d54c9120000341e628900189541da4b323988dd9de84304b01b41ce2c504e8b645de03430a9ab4c644ee22880924de43402b8398174282139132a1560de0050b744b022a2 else 0x1050baa8840002c1800022329433d9ce000047080019400003601e580000006588404ce0c117982411f26ec11082201cd00347203204e40b602c8286554640a61831986acd546d811918f23733cd2b08000000)))) else 0
  | 7 => if page < 1 then 0xa1389113615715633389110011400006088832082535200398059061286709407263204005040305800000000907400 else 0
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
  (slot / 16,slot % 16)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s23]
  | 3 => [s23, s24]
  | 4 => [s24, s23]
  | 5 => [s24]
  | 6 => [s01]
  | 7 => [s01, s34]
  | 8 => [s01, s23]
  | 9 => [s01, s23, s24]
  | 10 => [s01, s24, s23]
  | 11 => [s01, s24]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s23_ok, s24_ok, s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf000f 0x4d24500c2040 3 4
    pinBase [0x0,0xf000f,0xa000a,0xc000c,0x0,0x0,0xf0000,0x50005,0x30003,0xf000f,0xf000f,0xf] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0f 0x2ca2480c2040 3 4
    pinBase [0x0,0xf0f,0xa0a,0xc0c,0x0,0xf00,0x0,0x505,0x303,0xf0f,0xf,0xf0f] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xff 0x1c61440c2040 3 4
    pinBase [0x0,0xff,0xaa,0xcc,0xf0,0x0,0x0,0x55,0x33,0xf,0xff,0xff] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0x55555555 0x71851030810079a59238a182 4 6
    pinBase [0x0,0x55555555,0x0,0x44444444,0x50505050,0x55005500,0x55550000,0x55555555,0x11111111,0x5050505,0x550055,0x5555] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0x33333333 0x718510308100759551349141 4 6
    pinBase [0x0,0x33333333,0x22222222,0x0,0x30303030,0x33003300,0x33330000,0x11111111,0x33333333,0x3030303,0x330033,0x3333] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x5555aaaa 0x3cd2c91c50c179c698594490 4 5
    pinBase [0x0,0x5555aaaa,0xaaaa,0x44448888,0x5050a0a0,0x5500aa00,0x55550000,0x55550000,0x11112222,0x5050a0a,0x5500aa,0xaaaa] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x3333cccc 0x3ce2ca1c60c275c658554450 4 5
    pinBase [0x0,0x3333cccc,0x22228888,0xcccc,0x3030c0c0,0x3300cc00,0x33330000,0x11114444,0x33330000,0x3030c0c,0x3300cc,0xcccc] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf0f0f0f 0xc20402ca2484d24506da658 4 5
    pinBase [0x0,0xf0f0f0f,0xa0a0a0a,0xc0c0c0c,0x0,0xf000f00,0xf0f0000,0x5050505,0x3030303,0xf0f0f0f,0xf000f,0xf0f] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xff00ff 0xc20401c61444d24505d6554 4 5
    pinBase [0x0,0xff00ff,0xaa00aa,0xcc00cc,0xf000f0,0x0,0xff0000,0x550055,0x330033,0xf000f,0xff00ff,0xff] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xffff 0xc20401c61442ca2483ce34c 4 5
    pinBase [0x0,0xffff,0xaaaa,0xcccc,0xf0f0,0xff00,0x0,0x5555,0x3333,0xf0f,0xff,0xffff] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x55aa55aa 0x5d54d179c6981c50c138c288 4 5
    pinBase [0x0,0x55aa55aa,0xaa00aa,0x44884488,0x50a050a0,0x55005500,0x55aa0000,0x55005500,0x11221122,0x50a050a,0xaa00aa,0x55aa] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x33cc33cc 0x5d64d275c6581c60c234c248 4 5
    pinBase [0x0,0x33cc33cc,0x22882288,0xcc00cc,0x30c030c0,0x33003300,0x33cc0000,0x11441144,0x33003300,0x30c030c,0xcc00cc,0x33cc] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x5a5a5a5a 0x6d979c4d15942c938c0c1184 4 5
    pinBase [0x0,0x5a5a5a5a,0xa0a0a0a,0x48484848,0x50505050,0x5a005a00,0x5a5a0000,0x50505050,0x12121212,0xa0a0a0a,0x5a005a,0x5a5a] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x3c3c3c3c 0x6da75c4d25542ca34c0c2144 4 5
    pinBase [0x0,0x3c3c3c3c,0x28282828,0xc0c0c0c,0x30303030,0x3c003c00,0x3c3c0000,0x14141414,0x30303030,0xc0c0c0c,0x3c003c,0x3c3c] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xf00ff00f 0x7de75c4d24503ce34c0c2040 4 7
    pinBase [0x0,0xf00ff00f,0xa00aa00a,0xc00cc00c,0xf000f000,0xf000f000,0xf00f0000,0x50055005,0x30033003,0xf000f,0xf000f,0xf00f] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xf0f00f0f 0x7de75c2ca2485d65540c2040 4 7
    pinBase [0x0,0xf0f00f0f,0xa0a00a0a,0xc0c00c0c,0xf0f00000,0xf0000f00,0xf0f00000,0x50500505,0x30300303,0xf0f,0xf0000f,0xf0f] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 7 => cut6
  | 8 => cut7
  | 9 => cut8
  | 10 => cut9
  | 11 => cut10
  | 12 => cut11
  | 13 => cut12
  | 14 => cut13
  | 15 => cut14
  | 16 => cut15
  | _ => cut0

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x20084000010842000061 else 0
  | 4 => if page < 6 then (if page < 3 then (if page < 1 then 0x21021084210842109021080810842408001084010842208421184210842110c01084210842630021 else (if page < 2 then 0x8421084230842108421084210906108421084210842210842104210842108421300442002108403 else 0x8421084210842420484000842040108421080010842108421084210842108421084221084210844)) else (if page < 4 then 0x18420000410800108401184211842108421084210842108421088210840108420084220082108421 else (if page < 5 then 0x18000080010842108421000000042108421084210840010081000800842020421084210800310021 else 0x2000000001094000044000021104200842108421000000842508422))) else 0
  | 5 => if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x2208000000421080200821084410842108839d073908431008010843908822104221082150820004 else (if page < 2 then 0x410842100421084210800110a5000000000014054210842108010842208420108420804a00900084 else 0x254022108481082a008421084000828100420004200542100021455108020084401004110421084)) else (if page < 4 then 0x2210840104210042000840129221000180b581a0000084b5a9035ad2012402008200000252001009 else (if page < 5 then 0x2908424c6000000114a028000280a0000a50144210840008a02884228802110041ce841d0021087 else 0x214842808000000290000100400080210842108429084210a5010842940421084200a4210000008))) else (if page < 9 then (if page < 7 then 0x200040000001004410840290842108401284a108420842108920000000006b400000c03000002808 else (if page < 8 then 0x42000401084000000008401084210802108420a52a0a8420a52a000420aa021284212a2008a01084 else 0x2110840108410842200842000020084200822084000080218e035c0025485200a421085010002008)) else (if page < 11 then (if page < 10 then 0x20000216b02d0b401084210a4010802500400080210802508420000000842100400000008471084 else 0x2280400100000000210000008001082210801c0700000000004008021c00381000000040000401a8) else (if page < 12 then 0x4200841000001004252000100420000280a02100421000010840108421004000a028000010900000 else 0x1080000840100424000000802100000000000002100000082a008)))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x211e4001e0210047908f7940428005290840108421080014a02108001000840042120479084210a4 else 0x21000210842100020000200042108000084000800000f21084210850000501484210008400021084) else (if page < 3 then 0x28005000a029080210a42108520080000000020000000800000000000000000040008420004 else (if page < 4 then 0x4000000000f000000008000000000840008021000200802100421084000a00140001400280a5 else 0x0))) else 0
  | 7 => if page < 1 then 0x200 else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 5 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then fastClosed target negative pool counts lookup steps k i
   else let c := selectCut (label k i)
        maskedCut c.mask c.patterns c.bound k (pool k i))
theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (fastClosed_sound target nonzero negative pool counts lookup steps k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change maskedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 33 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 33 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x224 : span (checked 4) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x336 : span (checked 4) 34 336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 370 0 = true :=
  (@span_join (checked 4) 224 0 146 (@span_join (checked 4) 112 0 112 chunk4x0 chunk4x112) (@span_join (checked 4) 112 224 34 chunk4x224 chunk4x336))

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
theorem chunk5x560 : span (checked 5) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x784 : span (checked 5) 37 784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 821 0 = true :=
  (@span_join (checked 5) 448 0 373 (@span_join (checked 5) 224 0 224 (@span_join (checked 5) 112 0 112 chunk5x0 chunk5x112) (@span_join (checked 5) 112 224 112 chunk5x224 chunk5x336)) (@span_join (checked 5) 224 448 149 (@span_join (checked 5) 112 448 112 chunk5x448 chunk5x560) (@span_join (checked 5) 112 672 37 chunk5x672 chunk5x784)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x224 : span (checked 6) 36 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 260 0 = true :=
  (@span_join (checked 6) 112 0 148 chunk6x0 (@span_join (checked 6) 112 112 36 chunk6x112 chunk6x224))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 10 0 = true :=
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
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor8


namespace SignedFrontier.SmallCert.Minor10

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x80aaaafe80aaaafe
def negative : List Nat := [0, 8, 10, 12, 14, 16, 18, 20, 22, 24, 25, 26, 27, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,2,10),(0xffff0000ffff0000,2,18)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 5 then (if page < 2 then (if page < 1 then 0x4c4c4c4c4c4c4c4c4444cccc4444cccc4444444444444444440044004400440040404040404040403f3f00003f3f00003f0c3f0c3f0c3f0c3f00ff003f00ff003f003f003f003f003c3c3c3c3c3c3c3c3333000033330000330033003300330030303030303030302e2e2e2e2e2e2e2e2a2a2a2a2a2a2a2a22222222222222220f0ff0f00f0ff0f00f0f0f000f0f0f000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f00fff00f00fff00f00ff000f00ff000f000f000f000f000f0000000f0000000e0e0e0e0e0e0e0e0c0cfcfc0c0cfcfc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0c000c000c000c000a0afafa0a0afafa0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a000a000a000a000808080808080808050005000500050004040404040404040300030003000300020202020202020200ffff0000ffff0000ff000000ff000000cccccc00cccccc00aaffaa00aaffaa00aaaaaa00aaaaaa0000fffc0000fffc0000ffcc0000ffcc0000ffaa0000ffaa0000ff000000ff000000fefe0000fefe0000fcfc0000fcfc0000eeee0000eeee0000cccc0000cccc0000cc000000cc000000c0c00000c0c00000aaaa0000aaaa0000aa000000aa0000008888000088880000550000005500000044440000444400000f0000000f0000000c0c00000c0c00000a0a00000a0a000000cc000000cc000000aa000000aa0000000000000000 else 0xc0ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0fcfcc0c0fcfcc0c0f0f0c0c0f0f0c0c0ccccc0c0ccccc0c0c4c4c0c0c4c4c0c0c0ccc0c0c0ccc0c0c0c0c0c0c0c0c000ccccc000ccccc000c000c000c000b0b0b0b0b0b0b0b0afaaafaaafaaafaaafaaaaaaafaaaaaaaf00ff00af00ff00af00af00af00af00aeaeaeaeaeaeaeaeaaff0000aaff0000aaaaffaaaaaaffaaaaaaeeeeaaaaeeeeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaa0000aaaa0000aa88aa88aa88aa88aa0aaa0aaa0aaa0aaa00ff00aa00ff00aa00aaaaaa00aaaaaa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a0a0f0f0a0a0f0f0a0a0a0a0a0a0a0a08c8ccccc8c8ccccc8c8c8c8c8c8c8c8c8c0c8c0c8c0c8c0c8a8a8a8a8a8a8a8a88cccccc88cccccc88cc88cc88cc88cc88aaaaaa88aaaaaa8888cccc8888cccc8888aaaa8888aaaa88888c8c88888c8c888888cc888888cc88888888888888888800cccc8800cccc88008800880088008080cccc8080cccc80808080808080807f007f007f007f005f505f505f505f505f005f005f005f005c5c5c5c5c5c5c5c5a5a5a5a5a5a5a5a5555ff005555ff005555aaaa5555aaaa5555550055555500555500005555000055445544554455445500ff005500ff005500550055005500550000005500000054545454545454545050505050505050) else (if page < 3 then 0xf0f0f4f4f0f0f4f4f0f0f3f0f0f0f3f0f0f0f2f2f0f0f2f2f0f0f0fcf0f0f0fcf0f0f0faf0f0f0faf0f0f0f0f0f0f0f0f0f03030f0f03030f050f050f050f050f000f0f0f000f0f0f000f000f000f000eeeeeeeeeeeeeeeeeecceecceecceecceeaaeeaaeeaaeeaaee00ff00ee00ff00ee00ee00ee00ee00ececececececececeaeaeaeaeaeaeaeaddccddccddccddccdd00dd00dd00dd00dcdcdcdcdcdcdcdcd4d4d4d4d4d4d4d4d0d0d0d0d0d0d0d0cfcccfcccfcccfcccf00cf00cf00cf00cececececececececcfcccfcccfcccfcccccffccccccffccccccfcfcccccfcfccccceeeecccceeeecccccccccccccccccccccc44cccccc44cccccc0ccccccc0ccccccc00cccccc00cccc4444cccc4444cccc00cccccc00cccccc0000cccc0000ccc4ccc4ccc4ccc4ccc0ccccccc0ccccccc0ccc0ccc0ccc0cc8ccc8ccc8ccc8ccc88cccccc88cccccc88cc88cc88cc88cc4ccc4ccc4ccc4ccc44cccccc44cccccc44cc44cc44cc44cc444444cc444444cc0ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0ccc04cc04cc04cc04cc00ff00cc00ff00cc00cccccc00cccccc00cc44cc00cc44cc00cc0ccc00cc0ccc00cc00cc00cc00cc000000cc000000c8c8ccccc8c8ccccc8c8c8c8c8c8c8c8c4c4f4f4c4c4f4f4c4c4ccccc4c4ccccc4c4c4c4c4c4c4c4c444c444c444c444c0f0c0f0c0f0c0f0c0ccf0fcc0ccf0fc else (if page < 4 then 0xffccccccffccccccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaff88ff88ff88ff88ff55ff00ff55ff00ff555500ff555500ff550000ff550000ff44ff44ff44ff44ff0fff00ff0fff00ff0cff0cff0cff0cff0aff0aff0aff0aff00ffccff00ffccff00ffaaff00ffaaff00ff00ff00ff00ff00fc00ff00fc00ff00dd00ff00dd00ff00cc00ff00cc00ff00aa00ff00aa00ff005f00ff005f00ff005500ff005500ff000f00ff000f00ff000000ff000000fefefefefefefefefe00fe00fe00fe00fcfcfcfcfcfcfcfcfcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafaf7f0f7f0f7f0f7f0f5f5f5f0f5f5f5f0f5f5f0f0f5f5f0f0f5f4f5f4f5f4f5f4f5f0fff0f5f0fff0f5f0f5f0f5f0f5f0f5f0f0f0f5f0f0f0f4f4fcfcf4f4fcfcf4f4f4f4f4f4f4f4f4f0f4f0f4f0f4f0f3f3f3f0f3f3f3f0f3f2f3f2f3f2f3f2f3f0fff0f3f0fff0f3f0f3f0f3f0f3f0f3f0f0f0f3f0f0f0f2f2fafaf2f2fafaf2f2f2f2f2f2f2f2f2f0f2f0f2f0f2f0f1f0f1f0f1f0f1f0f0fff0f0f0fff0f0f0fcfcfcf0fcfcfcf0fcf0fcf0fcf0fcf0fafafaf0fafafaf0faf0faf0faf0faf0f0fffcf0f0fffcf0f0fffaf0f0fffaf0f0fff0f0f0fff0f0f0fefef0f0fefef0f0fcfcf0f0fcfcf0f0fcf0f0f0fcf0f0f0fafaf0f0fafaf0f0faf0f0f0faf0f0f0f8f8f0f0f8f8f0f0f5f0f0f0f5f0 else 0xffffffccffffffccffffffaaffffffaaffffff00ffffff00fffff0f0fffff0f0ffffccccffffccccffffc000ffffc000ffffaaaaffffaaaaffff8080ffff8080ffff5500ffff5500ffff4400ffff4400ffff0500ffff0500ffff00aaffff00aaffff0088ffff0088ffff000affff000affff0000ffff0000fffcfffcfffcfffcfff0fff0fff0fff0ffeeffeeffeeffeeffccffccffccffccffccff00ffccff00))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xe5274794711780a25e02093a07a401579007c1c010b900406400fb9 else 0
  | 4 => if page < 3 then (if page < 1 then 0xeabf35ecaf43da0ecdf66bb31d97ecaf653b27d92ec8f643b1fd8eec6762fb15d87ec2760fb05d7febdf5ebaf3d77eb95dabccb75eeaef573ab5d58f2bf557aa9d52ea8753ae9bb4bda5792b692f48f243ce7a71736d9974bf65ef2bd936c8b632f16b8a3c41e01f else (if page < 2 then 0x560932aa12654824c9f0499560832a4106622193ba032788854ef9089dee1139e01f95503728106e4f80dcbe4147001cfc00367800e1d801c1b0037b6006eec00dcd801b7b0036b6006cec00d8d801afb0035b6006aec00d4d801a7b0034b60068ec00d0d8019fb0033760065ec00c9d80191b0031f600636c00c5d80189b0030f600616c00c1d80181b002ff6005f6c00bdd80179b002ef600873c010c780216f00429e0084bc010878020ef00419e0077dc00eeb801d77 else 0x1b8aecb1d4b961a8f30b6e2de2c39ba987388ba8f0d751e16ea3c49d0788ba0ef9741d9493cc2126d7ba4dab849e59c8ccadd1996ca272cc44e58a89cc0d07972a0f2e241e5b283cc40f79819ef2e53de5c47bcb14f79821e32e73c65ca78cab0f19521e32e53b65be659c2cc6788988edf2be5f257a994af53015f2d929e58a53cb949f97411cef7219cf041caa87b93e0f72e51be5ca36c9e06d9728c72ac14e54c29ca90539)) else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0x20fc7ff1f7c7bf1e7c77f1bfc63f177c5bf167c55f14fc51f13fc4bf127c47f10fc41f0ffc3df0efc39f0dfc35f0bfc2bf09fc25f08fc1ff077c1bf067c17f057c13f047c0ff037c0bf027c07f017c03f6e6db3b6a6da3b63ed8bb61ee16f843dd5749f521d467507d3df4cb72ef4afd else 0xedff67fabfd3fe8ff3ff97fc9fe3fdafed3f67fb1fd87ebff5dfadfd67ea7f51fa7fd2fe93f47f9ffccfe5bf27f90fc6fe33f13f88fc37e0fef7f78fbb7dd3ee3f70fb77db7ed3f67fb37d97ec9f63fb17d87ebbf5bfabfd5bea7f51fa7fd33e8ff45fa27d0fe85f) else (if page < 3 then 0x2009363412746624da9c41d818836e5106dc420da0c41d2f883c4010788020d8cc41b6384771108be1a117ba02374e847a6308dc8c11786022f6283770f06bd720dda701bd44837a7806f4a60de8d41bd1a835e3406f4660de8c01bd6182b6f1055e220a7c3414f7502ae9e0574d00af11815e23029e18053e22e83b94f190044fe00897c0111f80209f0040be0080fc0100f801fff003fbe007efc00fcf801f7f003ebe007cfc00f6f801ebf003d3e0079fc00f2f801e3f else 0x88ba1f0d743e1e89ec0513d72a27ab544f60289bc0cf1b729e36e23c6dfa63f444c777e98eeb529fa0253eb94a7d5a94fafd21f9b843dc2c86f7410ee6f21bcc643b96487d5a8f7cd91eed123de9e07bd3a8f76531ef55229ec4053b818a76e514edc429dad85373f0a7a4014ee0624db9449b710936891274f024e94c49d)) else 0
  | 6 => if page < 1 then 0x88fe03f7efdd1f72fd6bf44fcf1f31fca7f21fc7bf14fc49f107c23f06fc15f else 0
  | 7 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x2d else 0
  | 4 => if page < 1 then 0x2f0bc1b else 0
  | 5 => if page < 1 then 0xbc2f06c1d else 0
  | 6 => if page < 1 then 0x1d else 0
  | 7 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 10
  | 4 => 186
  | 5 => 236
  | 6 => 18
  | 7 => 1
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 3 => 6
  | 4 => 94
  | 5 => 129
  | 6 => 14
  | 7 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 24
  | 4 => 337
  | 5 => 468
  | 6 => 48
  | 7 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 2
  | 4 => 7
  | 5 => 6
  | 6 => 5
  | 7 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 6
  | 4 => 10
  | 5 => 10
  | 6 => 7
  | 7 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xde1 else 0
  | 4 => if page < 2 then (if page < 1 then 0x4101205a38f87000890218302001600300000c0031c05ca11e080860e080000a0d1881ca008d000c0051404d1d100409934440870204481 else 0x6bf2a244940218190080c20732081ba091501084045800e3871a) else 0
  | 5 => if page < 3 then (if page < 1 then 0x16082500000846188107281000012181187c020031001820000c000301700e0002c708000110018c48008710e041009 else (if page < 2 then 0x10025c24f280141d420a42000c200057110198d50b02c00400108624008020175410604428118000b10cb94340082003 else 0x2b)) else 0
  | 6 => if page < 1 then 0x22180791003e31c0b else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x9048400006000484142952cc65c960005 else 0
  | 4 => if page < 6 then (if page < 3 then (if page < 1 then 0x981e4079c800048068bf5396c35d11b10467106826ec832e90001fc6d8f26a852000009d5d0182d6002d2000fc00027b82792e62995e9c680394552473880660006693a2d6819a0a14d98e7b2da0f440 else (if page < 2 then 0x9f2557f982559ee33070418868616a9323d57010aa576a4434b007a3b9c69b07f01481618c5a3050765f47d80476264425b878016002d8500e936c00002a57aa7d5e9d10028800192001a40009aae610 else 0x472145c8999d2845562c5e04cabdfa88800000fd174410020b73eb39b400ae22419cb30c5b00005497a784b838612a1000001c800000006f21f7000000000001f181c000000000120000007700062826)) else (if page < 4 then 0x574008d0f80001b965cc0000000000000000029d704009c08d0346b18abc50a5c0f1601561924208652cc375026b0595892c0b2b5254d3520f0450bba029934008000001380007ca46a2305414d98800 else (if page < 5 then 0x9054ca50d51b99c001cb5117e08adc756478e15e08cc21e09c3dd186c8b7346458305f8090d29a501dce52a498312d031e434a0f992558528ceb52ad1a436000dfac53c00000878000000005cb848400 else 0x1647c9684944ab91546988b38c442b60a961306882a))) else 0
  | 5 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1429b82051000000028a00000000b83a338c80963b806a900058aee7c870b73280567c0023c0054b76b665d1325a7a4834000027e18420232681f0100007467244d93981d800e76112f000328ac2e64c else 0x800c400000e00c88c0d8b980000000002651f79f97400af9821b5a20032c4a68f61430aa78aae21915d220a0e4b3ba0e731cd50e5a87160e8be4ac2c20378cacb2e0788c981da1f1b0002e29c5fdc000) else (if page < 3 then 0xa834c9380073299eb1b40017eea7500012751400c6854572b05a2934592e4f72a16f922dcde92000299cd8e4003800030ca06b0009c4005b0dcba000c3800aa0f735909c62b45e93819991683a8e4d63 else 0x96000195eccd00000000652d4d83120017c00000ad40000000000fc27000cc0948111c15417bfa5c8958f78803ba81bb807961eecd7282b30d30d9f46cddc826fad1060da000002f954324b5809c8b00)) else (if page < 6 then (if page < 5 then 0xc9e1cd001f46154000528d7a57a23264ca82619eb7a6a43090000003d60c0018100000138887e400991648b58b9d534be23d19085c26830029c76000a41a80038c1c710d7504965960033c0009d0fa94 else 0x6f8ed2bb5253240000d46aa989e2c8112f675b4228a60dd2fc14e2c505e4e79201005db16ede1034c50a4a219abc28c8a37513308dca3ee41ba11868940f0205c2b12d0712e447ad21738e001d077614) else (if page < 7 then 0x9b000c12548a76c854000034800261c1af4eb4001223a3b2b14f00000000a100d69a9a002867f400ca5bf881b200270002c0b630c7000009400001718745a00394a56aca039945e41753582b4faccebc else 0x728009d11de472eb27154437c21100d155833800162c1002da))) else 0
  | 6 => if page < 1 then 0x202608734557a82e7218602500006101e8e78952003ac968410d17440a60b0c008901258000000109c00 else 0
  | 7 => if page < 1 then 0x0 else 0
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
theorem root : pool 7 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 10 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 74 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 186 0 = true :=
  (@span_join (checked 4) 112 0 74 chunk4x0 chunk4x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x224 : span (checked 5) 12 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 236 0 = true :=
  (@span_join (checked 5) 112 0 124 chunk5x0 (@span_join (checked 5) 112 112 12 chunk5x112 chunk5x224))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 18 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 18 0 = true :=
  chunk6x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 1 0 = true :=
  chunk7x0
theorem verified : ∀ k ≤ 7, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 8 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 7
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    7 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor10

namespace SignedFrontier.SmallCert.Minor11

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x80fefefe80fefefe
def negative : List Nat := [0, 8, 16, 24, 25, 26, 27, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,17,25),(0xffff0000ffff0000,9,25)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffffff00ffffff00ffff00aaffff00aaffff0000ffff0000ffaaffaaffaaffaaffaaaaaaffaaaaaaff00ff00ff00ff00ff00aa00ff00aa00ff000f00ff000f00ff000000ff000000f3f0f0f0f3f0f0f0f2f2f2f2f2f2f2f2f0fafafaf0fafafaf0f0fafaf0f0fafaf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa00aa00aa00aa00aa000000aa0000008a8a8a8a8a8a8a8a88aaaaaa88aaaaaa88888888888888880f000f000f000f000f0000000f0000000a0a0a0a0a0a0a0a00aaaaaa00aaaaaa0000ffaa0000ffaa0000ff000000ff000000aaaa0000aaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xbca28bda0fbd60fbd20fbce0fbca0ebca0dbca0abca09bca0f else 0
  | 4 => if page < 1 then 0x7ee7e5cfbb9ef13dd87bacf1472e83dce7b98f729ee43dc47b84e0aec13d83cf066e0c5c17781de02bc01bc02782e7 else 0
  | 5 => if page < 1 then 0x3ffe7eff8fd9f47cff2fc5f0feef13ee7 else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x28 else 0
  | 4 => if page < 1 then 0x1f else 0
  | 5 => if page < 1 then 0x15 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 10
  | 4 => 25
  | 5 => 13
  | 6 => 1
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
  | 3 => 7
  | 4 => 19
  | 5 => 15
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 24
  | 4 => 82
  | 5 => 54
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 3
  | 4 => 6
  | 5 => 4
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 8
  | 4 => 9
  | 5 => 8
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x171d06 else 0
  | 4 => if page < 1 then 0x201041401800421830c2103006 else 0
  | 5 => if page < 1 then 0xf89506170fc2602 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x704020723a50008838000090006000004b28521218824962 else 0
  | 4 => if page < 2 then (if page < 1 then 0x7140182a2891244118005d80000b20000090812068851000000000000e2e800004426d60b80400150a034210b04900022eaa3002cc71004d16b3073001e00000359f0e85b940d000 else 0x58c82b04ba9391c0f20000000d4006018000) else 0
  | 5 => if page < 1 then 0x313730008041b60000840058708190728500215256b700c000b592003669638700116286a0b1b035986068344010b4205a7861505400 else 0
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
  (slot / 16,slot % 16)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s12]
  | 3 => [s12, s34]
  | 4 => [s01]
  | 5 => [s01, s34]
  | 6 => [s01, s02]
  | 7 => [s01, s02, s34]
  | 8 => [s02, s01]
  | 9 => [s02, s01, s34]
  | 10 => [s02]
  | 11 => [s02, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 10 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 25 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 13 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 13 0 = true :=
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
  · simp [counts]
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

end SignedFrontier.SmallCert.Minor11

namespace SignedFrontier.SmallCert.Sub12x0

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x82fe82fe82fe82fe
def negative : List Nat := [0, 8, 10, 11, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨0,1,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,2,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,4,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffccffccffccffccffaaffaaffaaffaaff00ff00ff00ff00fcfcfcfcfcfcfcfcfc00fc00fc00fc00f5f0f5f0f5f0f5f0f4f4f4f4f4f4f4f4f0fcf0fcf0fcf0fcf0faf0faf0faf0faf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeecccccccccccccccccc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00cc00cc00cc00c0c0c0c0c0c0c0c0aeaeaeaeaeaeaeaeaaeeaaeeaaeeaaeeaaaaaaaaaaaaaaaaaa0aaa0aaa0aaa0aaa00aa00aa00aa008c8c8c8c8c8c8c8c8a8a8a8a8a8a8a8a88cc88cc88cc88cc8888888888888888550055005500550044444444444444440f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a00fc00fc00fc00fc00cc00cc00cc00cc00aa00aa00aa00aa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1e4a408f010e039606ec0d5819b03ae05740a680ee019a02f80568037 else 0
  | 4 => if page < 1 then 0x21f83def5fd3f4bcdf27c8f1fc6f17c4f0bc1f else 0
  | 5 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1f else 0
  | 4 => if page < 1 then 0x15 else 0
  | 5 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 15
  | 4 => 15
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 64
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 6)

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
  | 3 => 7
  | 4 => 8
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 23
  | 4 => 38
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 4
  | 4 => 4
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 5
  | 4 => 5
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xb10002 else 0
  | 4 => if page < 1 then 0xc001010 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x38004b4782c04ce5c125db4038291 else 0
  | 4 => if page < 1 then 0xe005016c005c500a9700d2003a458c000200085ea00698f else 0
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
theorem chunk3x0 : span (checked 3) 15 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 15 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 15 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 15 0 = true :=
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

end SignedFrontier.SmallCert.Sub12x0

namespace SignedFrontier.SmallCert.Sub12x1

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x88fe88fe88fe88fe
def negative : List Nat := [0, 8, 9, 10, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨0,1,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,2,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,4,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

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

end SignedFrontier.SmallCert.Sub12x1

namespace SignedFrontier.SmallCert.Sub12x2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x8efe8efe8efe8efe
def negative : List Nat := [0, 8, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨0,1,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,2,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,4,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨4,12,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xfff0fff0fff0fff0ffaaffaaffaaffaaff88ff88ff88ff88ff0aff0aff0aff0aff00ff00ff00ff00fafafafafafafafafa00fa00fa00fa00f8f8f8f8f8f8f8f8f300f300f300f300f0faf0faf0faf0faf0f0f0f0f0f0f0f0f030f030f030f030f000f000f000f000eeeeeeeeeeeeeeeedcdcdcdcdcdcdcdccececececececececcfcccfcccfcccfccceecceecceecceeccccccccccccccccaafaaafaaafaaafaaaaaaaaaaaaaaaaaaa22aa22aa22aa22aa0aaa0aaa0aaa0aaa00aa00aa00aa00a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a08a8a8a8a8a8a8a8a8888888888888888770077007700770070707070707070703300330033003300303030303030303022222222222222220f000f000f000f000a0a0a0a0a0a0a0a00fa00fa00fa00fa00f000f000f000f000aa00aa00aa00aa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x5934d303a5872526498 else 0
  | 3 => if page < 1 then 0x85a364bc6873582568234026018d017d016d015d01fb01db02470237020701e701bb01a7011e010e00ee00ce00a7009b00370027 else 0
  | 4 => if page < 1 then 0x26f97e1f6bd9f3fcdf2fc8f1fc6f17c4f0bc1f69c27 else 0
  | 5 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1f else 0
  | 3 => if page < 1 then 0x21 else 0
  | 4 => if page < 1 then 0x15 else 0
  | 5 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 26
  | 4 => 17
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 64
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 6)

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
  | 2 => 3
  | 3 => 11
  | 4 => 9
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 16
  | 3 => 46
  | 4 => 45
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 4
  | 4 => 4
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x3b420036330 else 0
  | 4 => if page < 1 then 0x906343520 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x7000205006400080 else 0
  | 3 => if page < 1 then 0x9cb02e00f340590c80013030a00b00cedbd82000290000240a07848ea19c69500c880 else 0
  | 4 => if page < 1 then 0x34001271e2800181002400160003c068c55018838081d0141570000020007c0011 else 0
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
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 5 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 26 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 17 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 17 0 = true :=
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

end SignedFrontier.SmallCert.Sub12x2

namespace SignedFrontier.SmallCert.Minor12

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x888e8efe888e8efe
def negative : List Nat := [0, 8, 12, 13, 14, 16, 20, 21, 22, 24, 25, 26, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨0,1,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,2,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,4,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨4,12,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨4,20,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0xf0000000f0000000eeee0000eeee0000ee000000ee000000e0e00000e0e00000cccc0000cccc0000bb000000bb000000baba0000baba0000b0b00000b0b00000af000000af000000aafa0000aafa0000aaaa0000aaaa0000aaa00000aaa00000aa880000aa880000aa220000aa220000aa0a0000aa0a0000aa000000aa000000a8a80000a8a80000a2a20000a2a20000a0f00000a0f00000a0aa0000a0aa0000a0a00000a0a00000a0000000a00000008a8a00008a8a000088aa000088aa00008888000088880000880000008800000080800000808000007770000077700000770000007700000070700000707000003f0000003f000000333000003330000033220000332200003300000033000000323200003232000030f0000030f00000303000003030000030000000300000002a2a00002a2a000022aa000022aa0000222200002222000022000000220000002020000020200000110000001100000010100000101000000f0a00000f0a00000f0000000f0000000e0e00000e0e00000aaa00000aaa00000a0a00000a0a00000a0000000a00000008080000080800000300000003000000020200000202000000fa000000fa000000f0000000f0000000ee000000ee000000aa000000aa000000a0000000a00000008800000088000000300000003000000022000000220000000a0000000a0000000000000000 else 0xa0a2a2a0a0a2a2a0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a080a080a080a080a020a020a020a020a00aa000a00aa000a000f000a000f000a000a0a0a000a0a0a000a000a000a000a0000000a000000080888880808888808080a0a08080a0a08080808080808080800080008000800070077000700770007000700070007000606060606060606050500000505000003030300030303000302030203020302030033000300330003000f0003000f0003000300030003000300000003000000020222220202222202020a0a02020a0a02020202020202020200020002000200010001000100010000ff00f000ff00f000ff00aa00ff00aa00ff000000ff000000fafafa00fafafa00f8f8f800f8f8f800f0fff000f0fff000f0f0f000f0f0f000f0f00000f0f00000f000f000f000f000eeeeee00eeeeee00cc00cc00cc00cc00aaf0fa00aaf0fa00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa00a0a0a000a0a0a00088888800888888007070700070707000303030003030300022222200222222000a0a0a000a0a0a0000fffa0000fffa0000fff00000fff00000ffaa0000ffaa0000ff300000ff300000ff000000ff000000fefe0000fefe0000fcfc0000fcfc0000fafa0000fafa0000fa000000fa000000f3000000f3000000f0f00000f0f00000f0a00000f0a00000f0300000f030) else (if page < 3 then 0x302030203020302030103010301030103000f0003000f00030003300300033003000303030003030300030003000300030000000300000002f222f222f222f222a2a2a2a2a2a2a2a2a002a002a002a0023002300230023002222ff222222ff222222f2f22222f2f22222aaaa2222aaaa222232322222323222222222222222222222220022222200222022202220222022022202220222022200aa002200aa0022003300220033002200222222002222220022002200220022000000220000002020a0a02020a0a020203030202030302020222220202222202020202020202020002000200020001f001f001f001f0013001300130013001111110011111100111100001111000011101110111011101100330011003300110011001100110011000000110000001010303010103030101010101010101010001000100010000fff00000fff00000f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0f00000f0f00000f0affaa0f0affaa0f0a0f0a0f0a0f0a0f08ff880f08ff880f00fff00f00fff00f00ff000f00ff000f00afaa0f00afaa0f003f000f003f000f000f000f000f000f000a000f000a000f0003000f0003000f0000000f0000000e0eeeee0e0eeeee0e0e0e0e0e0e0e0e0e000e000e000e000c0c0c0c0c0c0c0c0b000b000b000b000a0aff0a0a0aff0a0a0afafa0a0afafa0a0acece0a0acece0a0aaaaa0a0aaaaa else (if page < 4 then 0x77777700777777007777000077770000777077707770777077707700777077007770707077707070773355007733550077007700770077007700700077007000770000007700000073507350735073507272727272727272707070707070707070007000700070005f005f005f005f005555550055555500555550505555505055554444555544445555000055550000555055505550555055445544554455445500ff005500ff00550055005500550054545454545454545050f0f05050f0f05050505050505050444444444444444440404040404040403f3f3f003f3f3f003f3f00003f3f00003f303f303f303f303f2a3f2a3f2a3f2a3f0f33003f0f33003f003f003f003f003f0000003f0000003b0a3b0a3b0a3b0a3a3a3a3a3a3a3a3a3333333033333330333333003333330033330000333300003330fff03330fff033303330333033303322ffaa3322ffaa332233223322332233103310331033103300ff003300ff003300f3f03300f3f03300bbaa3300bbaa33003330330033303300330033003300330030003300300033002200330022003300110033001100330003003300030033000000330000003232fafa3232fafa32323232323232323200320032003200310031003100310030f030f030f030f03030ff303030ff303030f0f03030f0f03030baba3030baba30303030303030303030300030303000 else 0xaa00bb00aa00bb00aa00af00aa00af00aa00aaaaaa00aaaaaa00aaa0aa00aaa0aa00aa22aa00aa22aa00aa0aaa00aa0aaa00aa00aa00aa00aa00a000aa00a000aa008800aa008800aa002200aa002200aa000a00aa000a00aa000000aa000000a8a8fcfca8a8fcfca8a8a8a8a8a8a8a8a800a800a800a800a2a2a2a2a2a2a2a2a200a200a200a200a0f0a0f0a0f0a0f0a0aaa0aaa0aaa0aaa0a0ffa0a0a0ffa0a0a0f0f0a0a0f0f0a0a0ececa0a0ececa0a0b0b0a0a0b0b0a0a0aaaaa0a0aaaaa0a0a2a2a0a0a2a2a0a0a0f0a0a0a0f0a0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a000a0a0a000a080a080a080a080a020a020a020a020a000f000a000f000a000aa00a000aa00a000a0a0a000a0a0a000a000a000a000a0000000a00000008f88ff888f88ff888f888f888f888f888e8e8e8e8e8e8e8e8c8c8c8c8c8c8c8c8a8a8a8a8a8a8a8a8a008a008a008a0088f8f8f888f8f8f888aa88aa88aa88aa8888fff88888fff88888ff888888ff888888f8f88888f8f88888aaaa8888aaaa8888a8a88888a8a888888a8a88888a8a888888aa888888aa888888888888888888888800888888008880fff08880fff0888088808880888088088808880888088800aa008800aa008800888888008888880088008800880088000000880000008080a0a08080a0a0808088888080888880808080808080808000800080008000))) else (if page < 7 then (if page < 6 then 0xc4c4c4c4c4c4c4c4c0f0c0f0c0f0c0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0bbbbbbaabbbbbbaabbbbbb00bbbbbb00bbbabbbabbbabbbabbb0bbb0bbb0bbb0bbaabbaabbaabbaabb33aa00bb33aa00bb00bb00bb00bb00bb000000bb000000bababababababababa30ba30ba30ba30ba00ba00ba00ba00b3a0b3a0b3a0b3a0b0b0b0b0b0b0b0b0b000b000b000b000afafafaaafafafaaafafaf00afafaf00afaf0000afaf0000afaeafaeafaeafaeafaaafaaafaaafaaafa0afa0afa0afa0af8caf8caf8caf8caf0faa00af0faa00af00af00af00af00af000000af000000aeaeaeaeaeaeaeaeae0cae0cae0cae0cacacacacacacacacab00ab00ab00ab00aaaafffaaaaafffaaaaaffeeaaaaffeeaaaaffaaaaaaffaaaaaafefeaaaafefeaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaaaafaaaaaaafaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaa22aaaaaa22aaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8a8aaaaa8a8aaaaa2222aaaa2222aaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa000aaaaa000aaaaa0000aaaa0000aaa2aaa2aaa2aaa2aaa0fff0aaa0fff0aaa0aaa0aaa0aaa0aa88ffccaa88ffccaa88aa88aa88aa88aa22aa22aa22aa22aa20aa20aa20aa20aa0aaa0aaa0aaa0aaa02aa02aa02aa02aa00ff00aa00ff00aa00faf0aa00faf0aa00fa00aa00fa00aa00eeccaa00eecc else 0xf0f00000f0f00000f0c0f0c0f0c0f0c0f0a0ffaaf0a0ffaaf0a0f0a0f0a0f0a0f050f050f050f050f030f030f030f030f010f010f010f010f000ff00f000ff00f000faaaf000faaaf000f300f000f300f000f0f0f000f0f0f000f030f000f030f000f000f000f000f000a000f000a000f0003000f0003000f0000000f0000000efeeefeeefeeefeeeeeeffeeeeeeffeeeeeefefeeeeefefeeeeeeeeeeeeeeeeeeeeeee00eeeeee00eeee0000eeee0000eee0eee0eee0eee0eecceecceecceecceeaaeeaaeeaaeeaaeeaacc00eeaacc00ee0eee0eee0eee0eee00ff00ee00ff00ee00eeeeee00eeeeee00ee00ee00ee00ee000000ee000000ececececececececeaeaeaeaeaeaeaeaeac0eac0eac0eac0e0e0f0f0e0e0f0f0e0e0eeeee0e0eeeee0e0e0e0e0e0e0e0e000e000e000e000ddccddccddccddccdd00dd00dd00dd00dcdcdcdcdcdcdcdcdc00dc00dc00dc00d8d8d8d8d8d8d8d8d0d0d0d0d0d0d0d0cfcccfcccfcccfcccf00cf00cf00cf00cececececececececcff0000ccff0000ccccfcfcccccfcfccccceeeecccceeeeccccdcdcccccdcdccccccececccccececcccccfcccccccfccccccceecccccceecccccccccccccccccccc4444cccc4444cccc0c0ccccc0c0ccccc0000cccc0000cc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00ff00cc00ff00cc00cc00cc00cc00cacacacacacacacac8c8c8c8c8c8c8c8) else (if page < 8 then 0xff000000ff000000fefefefefefefefefefafefafefafefafeeefeeefeeefeeefe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fbfafbfafbfafbfafafafffafafafffafafafefefafafefefafafafafafafafafafafaaafafafaaafafafa00fafafa00fafa0000fafa0000faf0faf0faf0faf0faf0f0f0faf0f0f0faeafaeafaeafaeafac8fac8fac8fac8faaafaaafaaafaaafaaaf000faaaf000fa32fa32fa32fa32fa0afa0afa0afa0afa00fafafa00fafafa00fa00fa00fa00fa000000fa000000f8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f888f888f888f888f777f000f777f000f5f0f5f0f5f0f5f0f500f500f500f500f3f3f3f0f3f3f3f0f3f3f300f3f3f300f3f30000f3f30000f3f2f3f2f3f2f3f2f3f0f3f0f3f0f3f0f3f0f0f0f3f0f0f0f3a2f3a2f3a2f3a2f333f000f333f000f300f300f300f300f3000000f3000000f2f2f2f2f2f2f2f2f222f222f222f222f1f0f1f0f1f0f1f0f100f100f100f100f0ff0000f0ff0000f0f0fffaf0f0fffaf0f0fff0f0f0fff0f0f0ff00f0f0ff00f0f0fefef0f0fefef0f0fafaf0f0fafaf0f0f8f8f0f0f8f8f0f0f0faf0f0f0faf0f0f0f0f0f0f0f0f0f0f030f0f0f030f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f05050f0f05050f0f03030f0f03030f0f000f0f0f000f0 else (if page < 9 then 0xfff08880fff08880fff00f00fff00f00fff000f0fff000f0fff00000fff00000ffeeffeeffeeffeeffeeffaaffeeffaaffeeeeeeffeeeeeeffeaffeaffeaffeaffe0ffe0ffe0ffe0ffdcffdcffdcffdcffccffccffccffccffccccccffccccccffbbffaaffbbffaaffbaffbaffbaffbaffafffaaffafffaaffaeffaeffaeffaeffaafffaffaafffaffaaffeeffaaffeeffaaffaaffaaffaaffaaff00ffaaff00ffaaf0a0ffaaf0a0ffaacc88ffaacc88ffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ff88ff88ff88ff88ff888888ff888888ff707070ff707070ff33ff30ff33ff30ff33ff22ff33ff22ff33ff00ff33ff00ff33f030ff33f030ff33aa22ff33aa22ff330000ff330000ff32ff32ff32ff32ff30ff30ff30ff30ff303030ff303030ff22ff22ff22ff22ff222222ff222222ff0fff0aff0fff0aff0fff00ff0fff00ff0ff000ff0ff000ff0faa0aff0faa0aff0f0000ff0f0000ff0eff0eff0eff0eff0aff0aff0aff0aff0a0a0aff0a0a0aff00fffaff00fffaff00fff0ff00fff0ff00ffeeff00ffeeff00ffaaff00ffaaff00ff00ff00ff00ff00fa00ff00fa00ff00f300ff00f300ff00f0f0ff00f0f0ff00f000ff00f000ff00aa00ff00aa00ff005500ff005500ff003300ff003300ff003000ff003000ff001100ff001100ff000f00ff000f00ff000300ff000300 else 0xfffffffafffffffafffffff0fffffff0ffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffffa0ffffffa0ffffff88ffffff88ffffff30ffffff30ffffff22ffffff22ffffff0affffff0affffff00ffffff00fffffafafffffafafffff888fffff888fffff0f0fffff0f0fffff000fffff000ffffeeeeffffeeeeffffccccffffccccffffaaaaffffaaaaffffaa00ffffaa00ffffa0a0ffffa0a0ffff8888ffff8888ffff3300ffff3300ffff3030ffff3030ffff1100ffff1100ffff0f00ffff0f00ffff0a0affff0a0affff00f0ffff00f0ffff00aaffff00aaffff000affff000affff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffafffafffafffafffafff0fffafff0fffaffaafffaffaafffafafafffafafafff8fff8fff8fff8fff8f8f8fff8f8f8fff88888fff88888fff3fff0fff3fff0fff2fff2fff2fff2fff0fffafff0fffafff0fff0fff0fff0fff0ffa0fff0ffa0fff0ff00fff0ff00fff0f0f0fff0f0f0fff0f000fff0f000)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x905ac3fe646b0fb else 0
  | 3 => if page < 1 then 0x992416b10c7fdc76b0ff991c74305882d0c21c4b99249625589a2416255890589560ff945c76b0fc9460b6b0fb99189560fb else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x65c4b6c8225ae3e12d6f1896b8944b3b3625ad1712dc7c89673d04b590e25ae4112271f0907240483c8222ae07114f2108538f4429c7a212e3c10971e884781c4238b8212e420f8eff81277fc083cc9208e3d10860032fd00249d80120ec0088f6003dbb001e3d800f16c007636003a3b001c9d800e46c00989e004c0f0025a7801243c008fde0040f7001e078008ddc0045fc0022bb001137800853c003f2e001f7b000f9b8007c5c003d360012370008fb800385c001776000b7b00050d80025bc00091e004807 else 0x956073cd0ff9e657fcf203fe77fdf03c78f29dff770f1e3aa7911cc3c82e29e40714effb8a78f1b33c10d99e60688f323427991643bf48bf24145f4f922fa7b917d3948bea0745ed1ca19c7f90ce3f88671ad4338d2a19c4650ce35885f1ac4278d61ffc7fcff3b587ef18f3e6b209f33980f93c787c9d503e6d321ee77e8f5ccc07a2e073d27321bc765c96cbc647ce5a23ce7f11e73d08f9cc0461dcc230f321127714893a1844710c21f88c0fbc4306ee32e2de65a16d68b8b7a3e45b9bfe2d1e64160e860b1c) else (if page < 3 then 0x7e9f23d70fd2187ae1fa7c8f4c4c8ff9e83992413046ffb8a608e3c6ccc11cc92096036b10c23e92221843e1fe43087c3c68610f89690c21d8861f243d10c3d087c4c9208fa37fdc516c6d62182de1ac4304b64891f09039123d108732478210e4181c421c7aff8843905b310868610e216241164421c102c884381c591086ff8b2210e44120421c7c2408438f44810871e090210e64910111cc32201037fdc5020722022040c0090597c80103b2f5001c565f2003f4cae40098244580132482b0025a9056004ab20ac0091208580120c0f3002077ba600482f2cc007e1e59801303c6b0020778e600482eacc0077dd59801223a13002607296004c3211c009924138013244c700260894e004c9121c009921a38012d40e7 else 0x25a7e9f24311323fed621847e9f2430f98001323fecb9400992619106004c930c8430026191242180132489208c00912429046004c920be43002647fde3180120bfee28c007fdf2714600478f9366300264905ac180132482920c00991ff45cc003f4f92198002416b10cc0013035886300081dac4328004c920a183)) else 0
  | 5 => if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0xd7e1a7c33f865f0c7e17fc2ef85bf0b3e15fc2af853f0a3e137c25f847f08be10fc20f83ff07be0efc1cf837f06be0cfc18f82ff05be0afc14f827f04be08fc10f81ff03be06fc0cf817f02be04fc08f80ff01be02fc04f807f00be00fd97eb17d9076f1ee607cb4f81eefddd55f1e9b16f625bc477801f else 0x89fc47e1ff0df84fc1fe0bf03f7ffbf7df7ef9f7bfbd7de7ef1f77fbb7dd7ee9f73fb97dc7edff6cfb5fdabed3f68fb3fd9becbf64fb1fd8bebdf5bfac7d5beabf52fa8fd3fe9df4dfa5fd27e91f47fa2fd13e87f42fa0fd03e7ff3ef9efcf3e75f39f9c7cdfe6df) else (if page < 3 then 0xd6fea7f4bfa3fd0fe7ff3bf9bfccfe5ff27f91fc7fe37f13f87fc2fe0ff03f7ffbefdefef3f77fbafdcfee3f6dfb5fda7ecff63fb0fd7febbf5bfacfd5feabf51fa7fd37e97f49fa3fd17e87f41f9efcefe73f37f9afccfe63f2df93fc97e43f1df8dfc67e2ff15f else 0x9e7e77f9d7e73f9c7e6ff9b7e6bf99fe65f98fe5ff967e57f957e53f93fe4df92fe49f91fe45f90fe41f8ffe3df8efe39f8d7e2df897e23f87fe1df86fe19f85fe13f847e0ff837e09f81fe05f80fe01f7ffdfbf7d7deff7b7de9f79fdc9f717dc3f707dbdf6efdb9f6dfdb5f6c7daff)) else (if page < 6 then (if page < 5 then 0xd97f63fd87f5ffd77f5bfd5ff53fd37f4bfd1ff45fd0ff3ffcf7f39fcdff35fbdfef5fbcfef1fbbfeedfba7ee7fb97ee3fb87edffb77edbfb67ed5fb4fed1fb3fecdfb27ec7fb17ec3fb07ebffaf7ebbfae7eb7fad7eb3fabfeabfaa7e97fa57e93fa37e8bfa27e85fa0fe81f9ffe7df else 0x863f0bfe16fc2bf853f097e11fc21f83ff077e0dfc19f81ff01fe02fc03f803efffdfefbfbf7f3efdfdf5fbe9f7cfef97df1fbe1f7bbef67debfbd5f7a7ef47de7fbcdf797ef27de3fbc3f777eee7ddafbb3f75feeb7dd4fba7f74bee87dcefb9bf72fee57dc5fb7bf6f3edd7db9fb6ff6dbedafdb4fb67f) else (if page < 7 then 0x7fc087b8a046d55023c4b011b23008b896043c48021eaa00de3c406f4c9039dff714ef922fa7f90ce21843f23c10970388477fc083801377c009b7e004d9f0026af80134fc009a3e004cff00266f80132fc00943e0049df0024df801267c0092fe00495f00247f801237c00917e00489f00243f801217c00907e00477f0023af8011cfc008e3e0046ff00233f801197c008c7e00461f0022ff801177c008afe00455f00227f801137c00893e00445f00221f801107c0087fe0043df0021cf8010dfc0086be00433f else (if page < 8 then 0x21c42d8c2215c5b10b62c885b12c427894213e440ff72207f78383fbc021fdc8c0fee2c87fb9903e7cbe1f3e5d0f9edf87cf3643e793e1f3c5f0f9e2107cf5cc39f2ee1af9730d7cad86be65c35ecc01abe590d5f1e06af7e4357b201abd170d7c8a06be3c435f1e01af8ef0d7c4b86af18435b8961abc460d5e25868f56c2bf2a015f84b081ec7837d9601b7b880ded8706fb2e82ef91011dcc808be07046edf822f18411b8b208ec4b045e21022f81c0ebaa60778f003bc3081d762c08ecc2043e54021f008117 else 0x3e448b9e8246cdf122e30891718048b896243dfe11def908ef6b0477cc622be61115f2e88af7fc457b0c22bcee115e4a08af1b445789022bd9710bac6885d62c42ec88216e3e10b71e085b84c42dbdc216de310b6ec885b89442bcc0213e5b109f2d084f960427ca8213e53109f1e084f8a0427c3a213e13109f03885781c427bfe213dcd109ee2885b70c42db82216dc010b6d5084f66c42dad6213d5510bca9085e4b842da2e2178fe109e7c88573d042d9c6213cc510b64b884f25842d92a216c94109e44884f)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x7c85bdb582ded2416f6860b7b3045bd9602dec7d16f6860a9e39854f488263df2131f36896f9904b7cc225be5d12df27096f9104b7c7825be2d12df07096f7fc4b7be425bdcd12dedf896f6cc4b7b5825bd5f12dea7096f5344b7a9425bd3912de92096f4304b79b225bcd712de67896f3044b796025bc9412de46096f1f44b7cd4253e64129f2e894f6fc4a79dc253d97123af1891b91048bc4e245e25122f0d891783848bcb4243e55121f07090f7bc487bb6243dc5121edf890f68848baca245d17123c7f090f else 0x9088cbc58465e25232f1011978588cbc22465e5a231f1e118f81c8cbbca465dd5232ee291977048cdb70465d43232e8b919e3f88c79f2465cf4233669919723c8cbb6644de4421f6ff10fb7c887da1843f4c121f65810fd26487da4840790c203c73901e39880f2ee3ef9731f7cb48fbe58c7df32e3ef6411f76ec8fbb9807d7c0e3edd7d1f76aa0fbe5287df2903ef9321f7c980fbe4a07df22e3ef9101f7c808fbe3c47df1da3ef8ec1f7c748fbe3987df1ca3ef88f1f6efb0d177c864da643278e9193c738c9b) else (if page < 12 then 0x714c1db7c60edbb3076cd983b614c1eb0860f5813076c0183b460c1ea3060ecf4307674183b39cc1da485bf8e72dfccb96bd5ccb0f4685875fe2c3afb961d65cb0eb1e5876412c3730160f81cb0bb085875542c3ca5161e3c4b0f1da5878ec2c3c74961e3a4b0ebf4527597293af9149b39ca4db444e5d97267acd933b9b496dc884b6df225b66092db93892dc88496df224b673925b9108fbc5a47ddf223eed991f76b08fba7247dd2423ee8611f733c8fb98247dcb023eecb919d78c8cdb94466e64232f2a1197 else (if page < 13 then 0x6fcf9bb667cde643d37221e9b7fcf4db667a6e6437ef169bf76ccdfbcd66d763536bafd1b5d6b0daec9e6bf63535fafd1afd6b0d7ec786bbe3b357b1a9abd7e8d5eb586af64434ef169a775cccff32e67f59133fac799fd638cfec8467de2d33ef1619f789ccfbc3667de1133ef0619f781ccfbc0a67ddde33eec419fd61ccfeafe67f51833fa7919f73accfbae66479fe323afd191d6b0c8ea18647a4430f6f9187b5ccc1f3ee60f5a0307acb983d63cc1eb1c60f6413076f9183b7b8c1db9460ee60305f039837 else 0x7c94af358a57a3c529ef9291e8b548bc88a1dd734e7cb1a73e56d39f2b49cf9974e7b21273788139bc0e9cddf64e6ec1a73754539f2a09cf9fe4cbcf9265e7c932dbe49879394c3d22257b7c928f3d492799f493cb9a49e56d24f2b4927997493b20a49b76524dcc0923e07492ebea49b51d24f28a927a6445fd2222fe8b517f3fe8bf9f245fcd9a2fe7c917da728bf92445fd16a21e7c910f4688675fe433afd219d7dd0ceb2e86758f433b20a19b9810c7c0e865d45433cfd203d990f9bcc27cde443e6eff9f37))) else (if page < 16 then (if page < 15 then 0x969ff7caaffbe0e7fdeff3f77981f27c14f95e077caefdbe57939e5bc88f2ddff796f223ab78b5d5bbfeeade6471b736b8bb911c5dbe4e2ee61715f3038af7fdc57c88de6df26f36f9375b911b8bbc6d9edca6cf7223677909b3bc4ed9de256cef0db677839b3bc18d9de5a6cdf03b677819b3bc08d9de016ceee0b67b905acdba2d66e606b1f2bb58f81dacbbf6d65dac692f3234578eda2bb66d15dac677722337b7f99bdbe4cdee64596ed9acb77e961dcc8ab7a64557d352a9e7c954f358aa7a44533d27295e else 0x7e997ebe4cbf5b365fad632fd65d96ebf4ca7597653afd327d7e991ecbcc7f661633b32317d9918aecc3226e44907730c2bb91207dc8900ee417cb6fd3e5b985eedbf4f76e6478f7223c7b7fde3dbe4f1ee617676fd3b3b7e9d3dcc2e6ee6172b6fd395b991c8dcc9303e61981f304baf9865c7cbd2e3e6496df2f4b6f9925a7cc32d3e5d969f30cb2f992587cbd2c3e61959f30caaf97a557cc92a3e6494df2f4a6f96a447ca5223e61839f30c15798609bcdb03de6381ef30c0f791207bc5b03de6481df16c097) else (if page < 17 then 0x7e90c193930c8825ae649104b3c88d9896b911b312cf2211825ae61910489cc92209079123c120f2237e241dac43048e37e4609079104b120f32488214e61910425c891e084b911ff109730c0e211e616fc425c88d988537fdb3108ed6218217261250425cc23088479845910972a0b2212e01164429bfe2c884b7fc59108f22096212e44120429c8824084b73448109722090211e0e120423c022408477fc48108ee0090212dbf120425918240847164481097220841fcdff1083f3b588607dc9104b0457323fe041e4412c083c882101137fc42020f323fe031e64986441bf4f921987fc59108722090210c0097999e800fd333d001ac667a004c8cbf40091197e8011b32fd0023565fa0045acbf4007fd97e800ff32fd else (if page < 18 then 0x9926181cf30cc1039e6d991ff3cd5323fe7991ff7c8f324c2e2ae647fdc53cc32236739123c6cd7223e4d9ce448f1b33bfedfb667991ff6b0f323feaa1e358b548b3f4f9265a991ff490eff3e48671fa7c90ce4c8d6219c911ac43391db588671ff6b10ce3fcd6219c6cdac4338d63448671ac66d0ce3f4f92199991ff430f323fe6d1e358b4d5ac6b1699f57e9f23232f92e660e9fa7c8c1ccc8ff9827911b33066f922e60e9f2430c1d3f473983965ce730728b9ce60e9fa7c8b0cbf4e996197e9942c33323fe581dfa4c8b0e3f486161c7e8e92c38fd1ce5865ac4309ce35886133c992612597323fe4b1e649108c9c891e118b99261230ed62184672642508c3b588610fc991ff1f4efd2183ef1f23987dd218428fbc else 0x99261911730c8903ce61906079cc930c887))))) else 0
  | 6 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x3e7e7a7cdff9b5f35fe6afcd3f99ff32be647cc3f983f2ebe5bfcb2f961f2a7e527c9cf933f25be497c8ff919f227e43fc80f8fbf1dbe397c68f8c9f16fe2a7c4bf895f123e22fc42f87ff0fbe1afc30f857f09fe0f7c1bf82ff047e077c08f80df65fb20ede3dcc0f969f03dd17f1f373d3647dc5bd896f else 0x86ff0cfe16fc23f83bf067e07fc0df813f00fdfffbfdf7cbef77deafbcbf78feecfdd5fba7f737ee57dc5fb79f6ebedc7db5fb67f6c3ed67da7fb45f67fecdfd77faebf5cfeb7fd69facbf58feaefd5bfab5f553ea57d48fa8ff517ea1fd3dfa73f4d3e997d30fa57f4a3e927d1dfa2ff443e867d05fa03f) else (if page < 3 then 0x78d0cdcb4863d0c3e6e861e9b8d4cfec5a67dd8233ee7519f75ccc1f3f460f5f23076be183b45cc1f1ce60edfa2c3ad6161d430b0f1cc5875bf23ef22119b9908cbb66465df21f76920fbe4307df1ce3ef8e71f76730fbe7fc5bdc8825be44122f32090f7fc48bb7e243c8c122e2f890f91042dcc2213dff109edf885b25042d928213c5910b624084f974357a9a1af8ee0d7c7706af991ff3b588670009b7e004d5f00264f801277c00913e00485f00241f8011dfc008b7e00459f00229f80113fc00897e00441f else (if page < 4 then 0x43035f9dc1afcea0d7e7386bf39835f9b21afccf0d7e6086bf2c035f9281afc8c0d7e4286bf1f435f8be1afc590d7e2b86bf14c35f8901afc420d7e1d86bf4e430f890187c350c3e92057f1082bf86a15fd0c09fe1a84ff9781ef99e0f7c4807bf2f037f3041bf8840dfe5e05fe5802ff0d417fcc208fc8c047e24023f9840ef8fa077c3503bf32011f10808fcc8037c3501bf30c89b905ffdbf4f96e64985f2f4baf98607bcc8ffbe446cf7223677981b37bfed9de2d4e7d16a7377c924f3e4926dfa433ad6219d else 0x30448f960247c94123e46091f1f448f8be247df2117f32085f98442fcba217e4410bf16885f83842fc02217dff10bef9085f6fc42fb66217dac10bead885f54042fa9a217d3910be92085f43042f9b2217ccf10be60885f2c042f928217c8c10be3e885f17c42f8b2217c4810bed987ff1203ff8841ffdac0fbf3206bf98435fcbc1afe5d0d7f2206bf8d435fc5a1afe0c0d7f0286bf7fc35fbf41afdf20d7ee506bf70835fb7e1afdb30d7ed606bf63835fb101afd860d7ec106bf5f035fa9a1afd390d7e9206bf))) else (if page < 7 then (if page < 6 then 0x23089fb5843fdbf203f320fbf9107dfc6a3efe2d1f7f088fbf7fc7dfbf43efdf21f7eef0fbf6cc7dfb583efd911f7ec10fbf5fc7dfaf83efd391f7e920fbf4307df9d43efce71f7e730fbf33c7df9823efcb01f7e460fbf2147dfa723b7c8c1dbe3e8edf43072f8fa397dfa1a3e678d1f23068fbf4327cb0193e3e8c9f7fc5bfbfe2a7e4412ff16895f99048fcc2247e5d123f22091f8b448fbfe247df2123ee6891f70048fb7e247db3123ed6091f57448fa9e247d4d123e9c891f49048fa18247cd9123e67891f else 0x33cbaf9825d7d7c2dfec3165f990b0fc88587e352c3f16961f864b0fbfe587dfa2c3ef9161f74cb0fb66587dac2c3ecc161f650b0fb04587d7c2c3e9c961f490b0fa18587cea2c3e73961f398b0f99e587cc12c3e9c953f33ca9f96054fd24293e60949f2c0a4fb584e7ccf273ed6133f30499fcc84b7e2d24bedf91ff9908cfcc2467e5d233f2b119f9108cfc5a467dff233ef9119f73c8cfb7e467db3233ed6119f5a48cfa9a467d39233e96919f4908cfa18467cd9233e67919f3048cf960467c94233eff913f) else (if page < 8 then 0x49101fa1880fd0c3e7e861e9f5f0dffcc86d7e4435ff169abf618d3fcc867fe6133ff2f19ff974cffcb267fe4433ff1a99ff8b4cffbfe67fdfa33fef919ff764cffb7e67fdb333fed619ff640cffb0c67fd8233febf19ff5f0cffaee67fd4d33fe9c99ff490cffa2867fd0c33fe7719ff3a8cff9b267fdff32be67995f7c8c8fb0c61fe64307f22183f8d4c1fc5a60fe1b307eff983f7e8c1fbe460fdb3307ed6183f648c1fb0460fd7c307eb9983f4e4c1fa4860fd17307e86183f3a8c1f9ce60fccf307ed9975f else (if page < 9 then 0x911acfc76d67e2d6b3effb59f7f9acfbe4d67db36b3ed6345f6b19bfcc8aa7e4452bf1aa91f99139fcc29cfe5e4e7f2ea73f97139fc889cfe354e7f16a73f7fd39fbf49cfdf24e7ef7273f6fd39fb669cfdac4e7ed4273f61939fb049cfd4d4e7effa69f4e534fbf4997e64493f22249f8d524fc5a927e27493effa49f7e924fbe4927db3493ed6249f68124fb04927d7c493e9ca49f6cd1dfa728efd24477f32219f9110cfc5a867e25433effa19f7c90cfbc6867db3433ed6219f4e50cfa48867d39417e8620bf else 0x26d993f354c9f9b644fcc9227e61913f27489f9aa2dfcc916fe618b7f2f45bf9762dfc9d16fe448b7f1dc5bf8d62dfcc303fe5d81bf323fff911fffc82fffe2d7fff14bfff991f2fc9cf97e447cbf1abe5f8b5f2fbfef97dfe7cbefd3e5f7c9e5fcc8e2fe2d6f3f32367f985b3fcc0d9fe5d6cff22367f8b5b3fbfed9fdf26cfef5367f6fdb3fbfed87db36c3f32359f)))) else 0
  | 7 => if page < 1 then 0x264fc89f8b7efffdf2fb67f6b3e9cfd24fa19f33fe60fcb0f919f1f7e247c42f86bf else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x3c else 0
  | 3 => if page < 1 then 0x50 else 0
  | 4 => if page < 1 then 0x16c470cc33 else 0
  | 5 => if page < 1 then 0x4711c470cc330cc330cc330cc330cc3307c1d0741b06c1f else 0
  | 6 => if page < 1 then 0xcc330cc330cc330cc3307c1f else 0
  | 7 => if page < 1 then 0x1f else 0
  | 8 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 10
  | 4 => 214
  | 5 => 1156
  | 6 => 622
  | 7 => 18
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 1024
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 10)

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
  | 4 => 91
  | 5 => 516
  | 6 => 360
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 3
  | 3 => 14
  | 4 => 328
  | 5 => 1858
  | 6 => 1294
  | 7 => 48
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 4
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 3
  | 3 => 6
  | 4 => 10
  | 5 => 13
  | 6 => 12
  | 7 => 7
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x1900 else 0
  | 4 => if page < 2 then (if page < 1 then 0x441000604002800d2848018005060414482180c080020000106200860e1c100001440b000000440003010210a01400048308082020004000 else 0x18189001c5003a1c00140000951e0410500204870a00880) else 0
  | 5 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x828102080012e20600060c181161c2011a14c9a1000c02160010202287822a044880004301100000e02004841c080841e140060000000 else 0xa340040c1048a0604100000838000480001e00513240410102541030004080020018304105023e34282123849604240823030002122c100) else (if page < 3 then 0x20182060400212047050014205004c397000090408000151e0808d0205e810a003800809b8006083860000181061c8000600000000000a else 0xe680020a0000002001873210206021c4080218000041c10e3e5ce8a0810182301829e060408056000810624100107040014204810040183)) else (if page < 6 then (if page < 5 then 0x148040855b820800180440030810015801c04000000010200101003c205a01600580140068e0c0c90a000c397062c0050019d82081420c else 0x608116003910b0e1088a0800002001808c1208a0b0900002026cda906007801a3401b20042884a0c20702d4ed00c0410120181831230202) else (if page < 7 then 0x1034304040801c0a68b800800780444cc030e082991e084800a003802258d01380810304f0304005c1350e30682122030902001000828208 else (if page < 8 then 0x3450d5c00104044811500c020600ac094411c616300879246180011e045860abc0010a143060712a00124cb8832021002c00a1b16b4588 else 0xb812e)))) else 0
  | 6 => if page < 6 then (if page < 3 then (if page < 1 then 0x1070800001f0004010e0602010005050c020802000003060e0600010f050108080104030014001d020107060000030612010205000e0000000401040703010c else (if page < 2 then 0x16000701020000003a0300000405051c021c1f1409000005012b0e37050501210201060d0114050b07030f18060000010304020a0600090101000200030200 else 0x406080107170a000f020100030003000305270001070201070a010005030a090a030b15000d4100030305011b000d00120305020003110203020100000e0001)) else (if page < 4 then 0x2070a0207010202030a180805080d101104082000000d0600021c0800034310050000020001004211185201030801070d031b0d0e39012707000101050920 else (if page < 5 then 0x5030558031100000900000849011b04460e0d0c0a20140515030701210700170e0307031204000c071901002a060005060e05170009590a0003140e08130e00 else 0x1c008e010006010000042d19183e000208130706012201020403121f070008030b220320c234021a))) else 0
  | 7 => if page < 1 then 0x22180791003e31c0b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x4 else 0
  | 3 => if page < 1 then 0x30000460942420080051c else 0
  | 4 => if page < 6 then (if page < 3 then (if page < 1 then 0xc0078532c91917600200521d429529810000000072730011dc9d678d5400ae1e6327181654017274c2249872f44893000000351c47422ab6124c1410a734a07750a53380a520bab210000000000960b8 else (if page < 2 then 0x154512ec00000381e3790003200096b247b0bd44134000008c33d53800a445db026884348312505e17ca67355c1c8230a8cb1d82819c9149511ad08b4ec002443d34c9b328d52a1930007325c8e000 else 0x22b4071004f2d93e50dbea843707400298302400016c1b4000004000218611dd2d0000000086454000003412c6f9b8002ccd0000c40e80b2b16208893508d05f412000002fc00344c123c0020c142dd)) else (if page < 4 then 0x99b0c0e56066166734008ad5206262181c06d15882000c7290880001c3393e000454926928db95b200000b346ccf24800035ab1389f0147f2f08b019bf949000240003c0004dac03046000000f500180 else (if page < 5 then 0xaa3141da647e1ac642a4d3594211716a169b72801a0fe2c65420174644ac030211f16427000af214410e4b513526326a22360010c2c2f80a2e05709433114b21a0000d84a02d3c22600000002a0631f0 else 0xb12399c2e82f0007a51c))) else 0
  | 5 => if page < 30 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0xca212a1f02380000a000010804c243223586c80e902a21bad340250a51adeb5405303b4c3ab6e0c08bfcea8ace8de39d148095e0003c900004b25500e8df8a0000c63fd0000248814000141c032000072d87cf7838f1a4208911429c2a15e624382908d300b9178 else (if page < 2 then 0xcc000000083d61234990d906424c3c65c60e08598aba1ef8f4c5780000e849400a422523181d46f13674994010322bae9d3a0083f214a4af663c1913a210f830e4e69c205b89720328a85fe02203b10840efc00036600012ecbca6fc31d1448ebd8421d49e4305c else 0x1622290f48c4c4e43b01ee02688c80000190c9b000262800035551507680003d25ed0001c9252879ec3d53c03d45822b21450de403232404c066953fb581750d0d01b3ba5714c9a8500001074fd22382b40000c683043b2c0009c490210300009007d202b23484cc)) else (if page < 5 then (if page < 4 then 0x38a10f14aa9c245425350a2f0227036d116c2b688e0d6074e7f013a0a71ee89465d631200883da3fab5503e08c133c1cb55070f95c812f13545742beaac9928b686ac3070b88d3043c8000bd21201f92632020e0a00004a224200024038a112041016632f96c00f0 else 0x68231077e8dc00011794d05600000b495b000081a27408c400000000000000001742df03409246c60001a8800028c1cb20611340003455de8f6c068c2b0b9262865ca94005009c8041d70362bae5ca2d301ec1496174260a204ac1261af0b282cd80d3cd612ae70) else (if page < 6 then 0x2fe30416610b437a4701680f34000000066c4b826c954909c73d27ec51000011843c0910d407248244088c611d83ac341000027c8fc1ddc00000018d0000e9b054552432441109c00040f18402e05370c4137a127808ae20000000862000056000000047a44605e4 else 0x64f8bba1e89de6800261732cc800027c1228c3c0eb3e680007501cab29cf9a5d07138f7e198f1154e1ff578313087e1e00a0ea905460ce08a42b85e42301980b35370100c0001500f8877d170dfa0b823223307b52cf1139ad249e5162878918d8a65da6e41d0fed))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x37b10ac110fec46e8a382e8aec0361b79c4cebc7469f25f202e936e12d22ecccc582bf1225038813611b88ac1584852b91e100f30aa3da0c080c018100002d0e9416bac40d3800062e0ee964acce1359c240000005042b453a200010287d1894804807a9200009c6 else 0x3320f3073250807e3a30dca138380311a1230e40e20061aa102c048c57800022d1758da0000fb40003d00c748800342b5831c3b60003190cda0005092c853040000001bf162217e89d2bb590a04c37eafa5de039d6883795168c7c00000022186a811229b1cc88a9) else (if page < 10 then 0x29600000002093de108c0008646ea1fe44fc52400047319e09bc0000001d469f43a58670e40b8c09619405a076d0000001b00ece0000454a625a8699000000016c19327f176076f75c48351a02738b841f023a00030c4831ec30d91d708f0e2600007129d9524f59 else 0x12ca5207d0fe43e884e4de10680c514553405f548e21d4cc260089e1c300002a53620fec0400481863350f7c84d2c600000bad4100031b0068c2871c0160e780a9000000016cd19050000000042e43e8001dfa00064f0431a0303851ea350a841405110fcde70000)) else (if page < 13 then (if page < 12 then 0x3f40b6940c9c97760c29f905b483612415c317e6d90cc1fc40ae7362f70e731c25bf1a250b909d000128633901e3d823c400000036c0df800071804f1118be88604d4386a1a07115e882d1d8cf943a20370d80a2e4d62ed0fc00193301e715b88cb35734819d8eb4 else 0x6bc1dedfb8aac14f08112705be7a0800000000008315680010bc0000000000ef803c0001c0f0b80001764e800007ae3e816383968e80b95ff8648124bef106846950241c0000c1e0cd3754350cf840d16a5dcb01807d28e12886950481c5e2902887a224a1bde82e) else (if page < 14 then 0x6401ce084d0000764305f385dc65184f0ce2e7c7d84820e3843a7f000009f81b4000211000056d34000122a000084a0000ca305d6e40000bdab520000001b28000848000158c0004be0000000db64ca4721aeab828aa1eb841ef653ec37d51b00050e8321d950d09 else 0x4660141ca11b845e27e19bc4326d32440e0aa158ee8ab47e28581b61da86486d480b143d79843083c2831de27a50e12be102c06022bbf043d0a1806226900f2ea86cc185e2e90f05c70679f18df743596596a0101077a9e176cdb077cac21a38f1e2300000982bc0)))) else (if page < 22 then (if page < 18 then (if page < 16 then 0x2d980011563e637b5d48f0457e15a0be262c051c315d08bf262c2b000008a00002554d6800032480000000000003c40000d381f02ca132000066c1be0000c887aa00018100000f234ba0120143dc0b002146925ba311100111823f02e9b2c99200005f078c0d9 else (if page < 17 then 0x8fe005a3c20002ba96922b81d81d54650f90f8812ea55037000028e45a00005907400000000be05f80331ab87940002dc11cae3544e8001c2032a6742cb40009745ef07386e83908f22671f70000000000200cce76d18000000a101ff1a100000000508000001015 else 0x22f80000000000000a4266d3100750dcd29a06b4a7234435c00000010a131f000027aed40003ad4a020000000002368dbe49e32e1e303075e326c14c80000001e210188ac2a4a7913d098070a462000060c0583140100000348bfa1b208e47ff0210000250)) else (if page < 20 then (if page < 19 then 0x70f00959a09a185400011aa8b58e3c4b1d5a5d410e9ac162a4407b20bd10800da13897a1cb8f1416c159192479d6713b80da00740de851106c5ac8803934268dd00000af0e68ddc346c5920e8d482d90c493d86ac4421199380f988c1905c3f8d4c0000000000000 else 0x2a837f006041980200000002e10003b48000ff50000c500003803b02570000b19000303039918100042659fa04069e9958f4078406da454764e3c000254014408186a2a59a54c4269d2ae18ac32c78abd58fb8eac90014f02c2c6022d0900f8803848d3859f7b16c) else (if page < 21 then 0x26e21c28095a437d02980000000000000a5900000022b40703dc80006baf795ce9070ce0d7c37646a2038a2607fb5914b8eb1274000222000000029c0910baa3872410a9c61925200010791f04141e30e32ed86580000000db80002a512b0efc4668450178000 else 0x7ccb5614fa4300000f417207e400076600033080005b82039121c5840a00000000007301ca4395fa05f93d400016b2e787a832b87ee6e81558be8cbecd512911ca1d099800000000007f465a3fd8ab82145010000000d240000001d94ba454380017da000))) else (if page < 26 then (if page < 24 then (if page < 23 then 0x995e58e9157a0bb2118ed54080d2218116080a12a92e00000003e117f8c12241291186ee6244c1dc01d44d178b15011ecd2860c0000d490b06e0c7d19cc00023d0000b80f0c0000000000e5442a0001c8000089c00018022286f596600da5a000030517fcc38 else 0x32100008a0820309989136834000013c1c62b864a60484f820005ae000090c8fc4b402b5fb400049e9250c687fc3e03e015684f403e2a680000754593a6000066810125820b0e418d84290530c3333a000230e14151831e09900008200955bb460d0f28ec00007c6) else (if page < 25 then 0x32c0000000ee127d2f517ac00026eb9a867aa740c921c052477f06a3830c9a9454b60f211db1c525cc75532cff87a4b2b11102342a336b8d28ba05ec00000000b70004615c54cbc4b743b07082b417800306e01320839d90ae29b600034310604d51fe2621cb002c else 0x210000000000000000177000000035c46ca96516400001fc9782c200000009e2580c09a2b0daa059bce5a2e6ed3d7a480b1512d3ea04358083c34ec2619fa831d00000000000003720000000b786c22db00c400029800012f2a9814780003dcc8c8d00001c44000)) else (if page < 28 then (if page < 27 then 0x4bd2751c00000000000000000000023857ea0e48832b244300000003eb23c000007c00016884744572af03100000000000e520d81fa86900007d08c90fb0000865000271567209213799f41121780000a11618ff200000019a443e88400003c4434428450211092c else 0x696414000081c00025a8d740000003914b007ec3cc23a07685cd0000074922000510000224aaa50000000000caa8f437c00000947aeaa24000dc400044f80008e000005d5f503000002364048b3d3a30000a0088c3b424d1988aa979498864124ec13c2090000698) else (if page < 29 then 0x1b090d9e1ae4844e41322c408c8072fea298c220b2800117e3796651550eac0090003ac030a79076e29317790606d601523d8f4d4b20eb00784e42ec1ed02b880d14e9c4098c11258908559e8a354c69c11a6c9304e62a796b0be42f00d454c0fcc47c26398e0000 else 0x7438c))))) else 0
  | 6 => if page < 21 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x19f8694090005543fd0008350000007b148800000000000000000027007028842249a0008a400056e9308ea00015e00000059d8bc2cc3e16c82712436e900060848e00028c00055c6ea03015a7b90191a086d0783843691ce3e93f80009603aa else 0x9084188701664903ff64159180192d1320d224837852814a3f357c50c80d8723953a48f427d4143e044c2e07326d672d50e39c62e00c6262285f247c51a25c5495a20f615630271d39870e06995e56a37a2340863fb04b5a04cc0d8278000000) else (if page < 3 then 0x1bc0006b80b09b085e7a45b049d1c60008000a02f591500000055a00000078e5cd2f92254a170c4a45b82e62c26f654015200053549c0007780000004048624918341819688440d73e49198846580523fc7bc4ed9654179672381e13196fc430 else (if page < 4 then 0x2e83340006f925873c3d80006555aa8980000009a937700065c60000095903b8fd3ec3f25880247b43641992d481c89f2da1956e693c7d300096c0001801107440602ac2988e420973491e6308588245382ee0004980008d47763e82400008ce else 0x6ca97c7ab04c3108a86c461690040c84199500000000000045d2d813f4282195600001260008809485d15445450007a90004da3c90003c881e00000000033104a4408649975dc3fe22c3084120005ca0c000000003c5460000008e0000401000))) else (if page < 7 then (if page < 6 then 0x4740000000dc8f927c00000051c8968b02600006f80005e58c94a02c00000008828284002c88e143d79495163929e4c86ec2793042f04d87e472a40f7125e96c05145f56610004a22844ac33c0007085c284c2304bc8c774829a7f067c else 0x35d4c400000046485400043c1787c60004b067026c0547db0ee0004ec0000002644dd5025b560c62a2656a575185664a9281d053090c76608793d44447d57805c8882dc00043f7cd4d40007d400013b6105298ad00075b94d0000000002b5000) else (if page < 8 then 0x1b05800005362fc0000009100684c17d800020e0006989807a05a80bc5ba5e03ba0000008d84f96241724810004589902160007ba85c00035836c8182b80341a89548147140000000000b84c540e0004809a26096180000008c853482d1885ec else (if page < 9 then 0x7703b800032d9ac2d26040003cb1620c24528cc2a46b06a800983097903d24c4080008680824c03507ee43e10099a00000000068800000086e7260006b91f15ae0f22e405d60a8cf51e5d49567546149186949256e42ec98c2964547b65185a6 else 0x3d36ee3c405017496463161e6cc08d74214c01c0000f763831c79c5c409880e3549043b47d90000430007ea0000743830463947606999849264f52696c68487a34504354a894a7520003c73cd4fe2507280005583c553c0a55de8d216c095)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0x8f689773072968c2293188dc0008650000000000000000001437987c000000000052483c7043cc4341fd5f71185210b58ec65d56c8d687a45f2810000005e449692432043b66c00000061c4787882ad8a500056419120569c8715a406d3f4044 else 0x3b646500035f5cc12334400416a7685ee0006b47a61486ac4c28742541c47e07c83bc1ec74c88c2c64bd8943240b452c8b481082a87604564496d20c54d9313ac07c2010fc4556c90006803597741087802903b06794b8000920051146249000) else (if page < 13 then 0x4297200286a265472c2a06156a69404d00403d938800000000000000000000070d4920000006e89a000043a62c4480000805d80006560005d01b73f00000003000003860003d204845b0003c07a14f80569140f00000000004828c14ee261690 else (if page < 14 then 0x8f52943700ec41c89d57678c42b7ef1c18f873e6294fd1d813d7a86196285bc0e80e730611a0008f779b33830c2212158ba7c20007775056aa18c7e80000202444d92746bc6ba00029c67821860d51258c0005da00000021c6644b21641de6d8 else 0x5206120bd0c74f044e95206c71c71080f1b899934048946c2b06848498aa22489c7643717455fc8255095708506e14dc86c4849b21f85c03dd5150108ae11518607a8da8e575c64c08485277c9a41c01145484242be9701374e537c99b24d94c))) else (if page < 18 then (if page < 16 then 0x8af1cc48c7f88f00009a86206dd0007f432942c08e68980c95598862274e8cd03283e7b87fc7903601542046b123c7052805ed6dc0fd64025d0e26e55903358fc5861f00116745841ac1d40ca9340380007ac37d0000971044681589583d01e8 else (if page < 17 then 0x7d712e4a64380410470000590004e197574d2085f061d4261350004105065ce34a2320007da5f80009623146a40000004ae7d014e91611d8ac11f39048d0000006420146b678f7755c854c7003288400cd3d62114e038f09c12c702785966090 else 0x95c8c07356d45a94617188290006da85517e4e889082b12a4621e55e11637243ee91c0006482f87bb65974913150d0ac00045c2592683a039e9948c404d3d473660e0884210000000f84f41730001053db87c0000000000005946d00007cc000)) else (if page < 19 then 0x4aa3ef2bc02e7564635105086a04d24fc4994b40a82472c45ea8386687501a49865398cb0650cc7e689a0004947c46c12f43488084200000009b453e00051600001d3a17b71c800042384a7df80a3a86458152d00000000de8957845001f9000 else (if page < 20 then 0x7380007f50009502ba7d58e88ab9380008208040002a88604a900063c0000005e81fc8a04705c10ce5987b05041900000001160009446f36347a28b865074057734c91259c4b558176c55099800010d82c92c0000394606e008c22a77d2923dc else 0x4e45b45920003f60004fa79699c1f55ac0008b61b6))))) else 0
  | 7 => if page < 1 then 0x1c25f8534458a63a7a084024000058f9e9478a54003ed158210d98440658e0c009101854000000101c00 else 0
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
  (slot / 4,slot % 4)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s01]
  | 3 => [s01, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0f0000 0x61969b411493 3 4
    pinBase [0x0,0xf0f0000,0xa0a0000,0xc0c0000,0x0,0xf000000,0xf0f0000,0x5050000,0x3030000,0xf0f0000,0xf0000,0x0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf000f00 0x61969b20928b 3 4
    pinBase [0x0,0xf000f00,0xa000a00,0xc000c00,0x0,0xf000f00,0xf000000,0x5000500,0x3000300,0xf000f00,0x0,0xf00] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0000f 0x515597001083 3 4
    pinBase [0x0,0xf0000f,0xa0000a,0xc0000c,0xf00000,0x0,0xf00000,0x500005,0x300003,0xf,0xf0000f,0xf] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf00f 0x30d38f001083 3 4
    pinBase [0x0,0xf00f,0xa00a,0xc00c,0xf000,0xf000,0x0,0x5005,0x3003,0xf,0xf,0xf00f] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xff00 0x30d38f20928b 3 4
    pinBase [0x0,0xff00,0xaa00,0xcc00,0xf000,0xff00,0x0,0x5500,0x3300,0xf00,0x0,0xff00] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0x44444444 0x79a59238a182 3 4
    pinBase [0x0,0x44444444,0x0,0x44444444,0x40404040,0x44004400,0x44440000,0x44444444,0x0,0x4040404,0x440044,0x4444] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 : CutCertificate target :=
  makeCutCertificate target Sub12x2.target 0x55555555 0x692282796386610200714304 4 6
    pinBase [0x0,0x55555555,0x0,0x44444444,0x50505050,0x55005500,0x55550000,0x55555555,0x11111111,0x5050505,0x550055,0x5555] Sub12x2.raw Sub12x2.nonzero (@Sub12x2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 : CutCertificate target :=
  makeCutCertificate target Sub12x2.target 0x33333333 0x651241755345610200714304 4 6
    pinBase [0x0,0x33333333,0x22222222,0x0,0x30303030,0x33003300,0x33330000,0x11111111,0x33333333,0x3030303,0x330033,0x3333] Sub12x2.raw Sub12x2.nonzero (@Sub12x2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xcccccccc 0xc21c62ca3ce4d25d66da7de 4 5
    pinBase [0x0,0xcccccccc,0x88888888,0xcccccccc,0xc0c0c0c0,0xcc00cc00,0xcccc0000,0x44444444,0x0,0xc0c0c0c,0xcc00cc,0xcccc] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xaaaaaaaa 0xc11c52c93cd4d15d56d97dd 4 5
    pinBase [0x0,0xaaaaaaaa,0xaaaaaaaa,0x88888888,0xa0a0a0a0,0xaa00aa00,0xaaaa0000,0x0,0x22222222,0xa0a0a0a,0xaa00aa,0xaaaa] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Sub12x1.target 0xf0ff0f0 0x3ce34c6da6581c61444d2450 4 5
    pinBase [0x0,0xf0ff0f0,0xa0aa0a0,0xc0cc0c0,0xf0f0,0xf00f000,0xf0f0000,0x5055050,0x3033030,0xf0f0000,0xf00f0,0xf0f0] Sub12x1.raw Sub12x1.nonzero (@Sub12x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 : CutCertificate target :=
  makeCutCertificate target Sub12x1.target 0xff00ff0 0x5d65546da6581c61442ca248 4 5
    pinBase [0x0,0xff00ff0,0xaa00aa0,0xcc00cc0,0xf000f0,0xf000f00,0xff00000,0x5500550,0x3300330,0xf000f00,0xf000f0,0xff0] Sub12x1.raw Sub12x1.nonzero (@Sub12x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut16 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xffff0000 0x41149351559761969b71d79f 4 5
    pinBase [0x0,0xffff0000,0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000,0xffff0000,0x55550000,0x33330000,0xf0f0000,0xff0000,0x0] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut17 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xff00ff00 0x20928b30d38f61969b71d79f 4 5
    pinBase [0x0,0xff00ff00,0xaa00aa00,0xcc00cc00,0xf000f000,0xff00ff00,0xff000000,0x55005500,0x33003300,0xf000f00,0x0,0xff00] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xc3c3c3c3 0x65f45724f04761e41620e006 4 6
    pinBase [0x0,0xc3c3c3c3,0x82828282,0xc0c0c0c0,0xc0c0c0c0,0xc300c300,0xc3c30000,0x41414141,0x3030303,0x3030303,0xc300c3,0xc3c3] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut22 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0x55aa55aa 0x55745314704371e61a30e20a 4 6
    pinBase [0x0,0x55aa55aa,0xaa00aa,0x44884488,0x50a050a0,0x55005500,0x55aa0000,0x55005500,0x11221122,0x50a050a,0xaa00aa,0x55aa] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut23 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0x5555aaaa 0x34f24b14704371e61a516412 4 6
    pinBase [0x0,0x5555aaaa,0xaaaa,0x44448888,0x5050a0a0,0x5500aa00,0x55550000,0x55550000,0x11112222,0x5050a0a,0x5500aa,0xaaaa] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut25 : CutCertificate target :=
  makeCutCertificate target Sub12x0.target 0xcc33cc33 0x29a01039e1142db0513df155 4 6
    pinBase [0x0,0xcc33cc33,0x88228822,0xcc00cc00,0xc030c030,0xcc00cc00,0xcc330000,0x44114411,0x330033,0xc030c03,0x330033,0xcc33] Sub12x0.raw Sub12x0.nonzero (@Sub12x0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut28 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0x33cc33cc 0x59749318708371d61930d209 4 6
    pinBase [0x0,0x33cc33cc,0x22882288,0xcc00cc,0x30c030c0,0x33003300,0x33cc0000,0x11441144,0x33003300,0x30c030c,0xcc00cc,0x33cc] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut29 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0x3333cccc 0x38f28b18708371d619515411 4 6
    pinBase [0x0,0x3333cccc,0x22228888,0xcccc,0x3030c0c0,0x3300cc00,0x33330000,0x11114444,0x33330000,0x3030c0c,0x3300cc,0xcccc] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut30 : CutCertificate target :=
  makeCutCertificate target Sub12x0.target 0xaa55aa55 0x25901035d1142db0923df196 4 6
    pinBase [0x0,0xaa55aa55,0xaa00aa00,0x88448844,0xa050a050,0xaa00aa00,0xaa550000,0x550055,0x22112211,0xa050a05,0x550055,0xaa55] Sub12x0.raw Sub12x0.nonzero (@Sub12x0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut32 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf0f0f0f 0x6da6584d24502ca2480c2040 4 5
    pinBase [0x0,0xf0f0f0f,0xa0a0a0a,0xc0c0c0c,0x0,0xf000f00,0xf0f0000,0x5050505,0x3030303,0xf0f0f0f,0xf000f,0xf0f] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut33 : CutCertificate target :=
  makeCutCertificate target Sub12x2.target 0xff00ff 0x5d65544d24501c61440c2040 4 6
    pinBase [0x0,0xff00ff,0xaa00aa,0xcc00cc,0xf000f0,0x0,0xff0000,0x550055,0x330033,0xf000f,0xff00ff,0xff] Sub12x2.raw Sub12x2.nonzero (@Sub12x2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut34 : CutCertificate target :=
  makeCutCertificate target Sub12x2.target 0xffff 0x3ce34c2ca2481c61440c2040 4 6
    pinBase [0x0,0xffff,0xaaaa,0xcccc,0xf0f0,0xff00,0x0,0x5555,0x3333,0xf0f,0xff,0xffff] Sub12x2.raw Sub12x2.nonzero (@Sub12x2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 5 => cut4
  | 6 => cut5
  | 7 => cut6
  | 9 => cut8
  | 10 => cut9
  | 11 => cut10
  | 12 => cut11
  | 13 => cut12
  | 16 => cut15
  | 17 => cut16
  | 18 => cut17
  | 22 => cut21
  | 23 => cut22
  | 24 => cut23
  | 26 => cut25
  | 29 => cut28
  | 30 => cut29
  | 31 => cut30
  | 33 => cut32
  | 34 => cut33
  | 35 => cut34
  | _ => cut0

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x1000000 else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x410400810430400410410410410410410410410410010431c30c30410410400411820401860000c3042043001041041 else 0x410410420420410410410c30410410810471c71c01c71c00000c30c30c31c10410400450410410401c11c10410c1000) else (if page < 3 then 0x1c70410410400001c71c71c10400010410410400410410410410410410410470410410810c30c00030c3041041080041 else 0x1c01c1041041081001041001047000000)) else 0
  | 5 => if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x2492492492512492492492514512cb2cb44b2c92492492cb34d34924924b25145124924b2492cb88944944b2498512c9 else 0x8802e28806002492492492622492492492622cb2e22cb2492492c08400002492c92514512cc4514514502d145131144c) else (if page < 3 then 0xb0002ca2cb2cb00b2cb00a00a2cb2d02cb2cb0092c000b24924924b24924b2492612cb2cb2cb2cb2d100c8408528a2 else 0x24924924924900924900c00c24c2492492502492490090002492492492492492492490000220094007400220212cb00b)) else (if page < 6 then (if page < 5 then 0x41034b2cb00000000b88a0002d02c02c02c088b00c00a40c00c31f00088a02130c30c30c28c24924024024924030030c else 0x124a10122404514494514514512cc2cb30c30930024c00c0007c03222402c02cb00088902245144944030a480892490) else (if page < 7 then 0x4514514914494510092c08d144c34b3114514512cc40c31041041049288b30b31230c30c30c00024000b2cb0002cb009 else (if page < 8 then 0x1186145141045041044b3112cb45130c30c3114638e324930c32345145144944b2cb44989134d36234d34934d451451 else 0x8808914512cc2cc34c4513113118514618638400000114514514638e38514514514514638614518618c0861861451463)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x84084084084925030d44d45041249144044d40045145248001149200045200c44c44c0004924924514518e34518a2023 else 0x4924924920128a28a18628a102286286200b30c2cb2c924924c30c30c00084084924924924924930c30c24c84b2492c9) else (if page < 12 then 0x84b84b28a84a28a2a184924b2cb2cb2cb00000a24930c2cb2cb2c924b2cb35000031030c4228500228408a10210004a1 else (if page < 13 then 0x220210218a240b2cb2cb2cb2d22cb2cb8a22cb2cb2d249248b4928a288a28a2a288b2cb2cb8612cb2cb2cb021000840 else 0x24948926230c30c3124a28a22492c924926124c30c30c30002102124902124026124924924b2ca2cb2c000024a8808a2))) else (if page < 16 then (if page < 15 then 0x45148b84c00c3228a28a24514a14514923218800104924924920228a242100b00b00b2e22e22e12cc890011451249410 else 0x2cc84b2cb2cb2cb35144088089000000000000900b2cd34045145145145145125144b34d45145101044d34d34d8a2462) else (if page < 17 then 0x2c049041001248000048084000d36100034d86184000000044045145144002144b0114a14510000002cb2c084b2cc00b else (if page < 18 then 0x45145101146142140001148000c00000b00b00b2c001149202184086102186100b2c02ca2c02cb45149000000b000240 else 0x0))))) else 0
  | 6 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x24928000028a68028a5892492496960008a28802492496898890008808e200924925a589889009022262262249262880 else 0x98c90098a22a28802498a22622898890002a28e28892a228088a00a8a22a200a249249262249249263249249249249) else (if page < 3 then 0x2492496a22a259600a5800092498e28a22492492498808a28a38a20008e38e30002492498890178978a3897249889263 else (if page < 4 then 0x2492492630002630002630002638e326224900924979a89e5807892408a20092400002408800000228a28a2249249289 else 0x8e20220238e30000008c08c00000230000230000230008c08e28800238e32400092498c02492630092498c0009249))) else (if page < 7 then (if page < 6 then 0x8808c000024900024900924024024924924900024000988924901a8802498a20178a38e28a20228a38808a28e20008e2 else 0x69628a00028924028924024924a28924924924a2896892562406805805e38800228a28808808808808a2000022000022) else (if page < 8 then 0x2492492800172a200a01a88a8a228068088a68a29a29a02201a28088a89a00a00028058028000a58a29600058a0002a2 else (if page < 9 then 0x24000900000001d880009262889880249022249022262240000009240009009240009889240009240249009249249 else 0x220005e20002578978806228a28a20000002400000005e20220228a2022022880)))) else 0
  | 7 => if page < 1 then 0x0 else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 6 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then fastClosed target negative pool counts lookup steps k i
   else let c := selectCut (label k i)
        maskedCut c.mask c.patterns c.bound k (pool k i))
theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (fastClosed_sound target nonzero negative pool counts lookup steps k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change maskedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 10 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 102 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 214 0 = true :=
  (@span_join (checked 4) 112 0 102 chunk4x0 chunk4x112)

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
theorem chunk5x560 : span (checked 5) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x784 : span (checked 5) 112 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x896 : span (checked 5) 112 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1008 : span (checked 5) 112 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1120 : span (checked 5) 36 1120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1156 0 = true :=
  (@span_join (checked 5) 560 0 596 (@span_join (checked 5) 224 0 336 (@span_join (checked 5) 112 0 112 chunk5x0 chunk5x112) (@span_join (checked 5) 112 224 224 chunk5x224 (@span_join (checked 5) 112 336 112 chunk5x336 chunk5x448))) (@span_join (checked 5) 336 560 260 (@span_join (checked 5) 112 560 224 chunk5x560 (@span_join (checked 5) 112 672 112 chunk5x672 chunk5x784)) (@span_join (checked 5) 112 896 148 chunk5x896 (@span_join (checked 5) 112 1008 36 chunk5x1008 chunk5x1120))))

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
theorem chunk6x448 : span (checked 6) 112 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x560 : span (checked 6) 62 560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 622 0 = true :=
  (@span_join (checked 6) 336 0 286 (@span_join (checked 6) 112 0 224 chunk6x0 (@span_join (checked 6) 112 112 112 chunk6x112 chunk6x224)) (@span_join (checked 6) 112 336 174 chunk6x336 (@span_join (checked 6) 112 448 62 chunk6x448 chunk6x560)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 18 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 18 0 = true :=
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
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor12


namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfefefe80fe808000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 32, 33, 34, 35, 36, 37, 38, 40, 48, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,14,15),(0xcccccccccccccccc,13,15),(0xf0f0f0f0f0f0f0f0,11,15),(0xff00ff00ff00ff00,7,15),(0xffff0000ffff0000,7,23),(0xffffffff00000000,7,39)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x8888880000000000888088800000000088088808000000008800ff00000000008800888800000000880088000000000088000000000000008080aaaa000000008080888800000000808080800000000080008000000000007f007f00000000003f3f3f00000000003f2a3f2a000000003f00ff00000000003f003f00000000003f000000000000002a2aaaaa000000002a2a2a2a000000002a002a00000000001f001f00000000000f080f08000000000f000f00000000000e0eeeee000000000e0e0e0e000000000e000e00000000000a0a0a0a000000000a000a0000000000080888880000000008080808000000000800080000000000070007000000000003030300000000000300ff00000000000300030000000000030000000000000002020202000000000200020000000000010001000000000000fefefe0000000000eeeeee0000000000888888000000000000ffee000000000000ff88000000000000ff00000000000000fefe000000000000eeee000000000000ee00000000000000eaea000000000000aaaa000000000000a8a80000000000008888000000000000880000000000000080800000000000003f000000000000002a2a0000000000000e0e0000000000000a0a00000000000008080000000000000300000000000000020200000000000000ee00000000000000880000000000000000 else (if page < 2 then 0xee00ee00ee000000eaeaeaeaeaea0000cccccccccccc0000aaaaaaaaaaaa0000a8a8fcfcfcfc0000a8a8a8a8a8a800008a8a8a8a8a8a00008888ff00ff8800008888f0f0f8f800008888aaaaaaaa00008888888888880000888800008888000088008888888800008800880088000000808088888888000080808080808000003f003f003f0000003c3c3c3c3c3c00002a2a2a2a2a2a00000e0e0e0e0e0e00000a0a0a0a0a0a000008080808080800000300030003000000020202020202000000eeeeeeeeee000000aaaaaaaaaa000000888888888800000000ffffff0000000000ffffeeee00000000ffff888800000000ffeeffee00000000ffaaffaa00000000ff88ff8800000000ff00ff0000000000ff00ee0000000000ff00880000000000ff003f0000000000ff00030000000000ff00000000000000fefefefe00000000fe00fe0000000000fcfcfcfc00000000f0f0f0f000000000ef00ef0000000000eeeeeeee00000000eeeeee0000000000ee0eee0e00000000ee00ff0000000000ee00eeee00000000ee00ee0000000000ee00000000000000eaeaeaea00000000ea00ea0000000000bf00bf0000000000af00af0000000000ab00ab0000000000aaaaaaaa00000000aa80aa8000000000aa2aaa2a00000000aa00aa0000000000a8a8a8a800000000a800a800000000008f008f000000000088888888 else 0x80000000800000007070700070707000700070077007700070007000f000f0007000700070007000700000007000000050500000505000005050000000000000303030303030300030303030000000003030300ffffff000303030003030300030303000300030003030000030300000303000000000000030203020302030203020300030203000300ff00ff00ff000300ff000300ff0003000300ffff030003000300ff00ff0003000300ff00030003000300030303000300030003020302030003000300ff0003000300030003000300030003000000030001000300010003000000ff0000000300000003000300030000000300000003000000000000000202aaaaaaaaaaaa02028a8a8a8a8a8a02020202ff02ff0202020202aa02aa02020202020202aaaa02020202020202020202020002020200020002000202020202000200020002000200000002000000010101000101010001000100030003000100010001000100010000000100000000ffffff0000000000ff00ff0000000000eeeeeeeeeeeeee00aaaaaaaaaaaaaa00888888888888880000ffffffff00000000ffff000000000000ffeeffeeffee0000ff88ff88ff880000ff00ff00ff000000ff000000ff000000fefefefefefe0000fe00fe00fe000000fcfc0000fcfc0000f0f00000f0f00000eeeeff00ffee0000eeeeeeeeeeee0000ee00eeeeeeee)) else (if page < 5 then (if page < 4 then 0x2a002a00aa00aa002a002a003f003f002a002a002a2a2a2a2a002a002a002a002a0000002a00000022222222222222221f1f1f001f1f1f001f0000001f0000000f0f0f0f0f0f0f000f0f0f0f000000000f0f0f000f0f0f000f0f0f000f000f000f0f08080f0f08080f0a0f0a0f0a0f0a0f080f08ff88ff880f080f080f080f080f00ff00ff00ff000f000f00ff00ff000f000f008f888f880f000f000f000f000f0008000f0008000f0007000f0007000f0000000f0000000e0eeeeeeeeeeeee0e0eaeaeaeaeaeae0e0e0e0eff0eff0e0e0e0e0eeeeeeeee0e0e0e0eee0eee0e0e0e0e0e0e0eeeee0e0e0e0e0e0e0e0e0e0e0e000e0e0e000e000e00ee00ee000e000e000e0e0e0e0e000e000e000e000e0000000e0000000c0c0c0c0c0c0c0c0b0b0b000b0b0b000a0afafafafafafa0a0aaaaaaaaaaaaa0a0aaaaa0a0aaaaa0a0a8a8a8a8a8a8a0a0a0a0aff0aff0a0a0a0a0afa0afa0a0a0a0a0aaaaaaaaa0a0a0a0aaa0aaa0a0a0a0a0a8a8a8a8a0a0a0a0a0a0afafa0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a000a000a0a0a0a0a000a000a000a000a0000000a000000080888888888888808080808ff08ff08080808088888888808080808880888080808080808088888080808080808080808080800080808000800080088008800080008000f000f0008000800080808080800080008000800 else 0x7f7f7f007f7f7f007f0f77007f0f77007f007f00ff00ff007f007f007f007f007f0000007f0000007777ffff000000007777777700000000777700007777000077007700ff00ff00770077007700770070707070f0f0f0f070707070707070705f5f5f5f000000005f005f005f005f0055555555000000005555000055550000550055005500550054545454545454544c4c4c4c4c4c4c4c444444444444444440404040404040403f3f3f3f3f3f3f003f3f3f3f000000003f3f3f00ffffff003f3f3f003f3f3f003f3f3f003f003f003f3f00003f3f00003f3f0000000000003f2a3f2affaaffaa3f2a3f2a3f2a3f2a3f2a3f003f2a3f003f00ff00ff00ff003f00ff003f00ff003f003f00ffff3f003f003f00ff00ff003f003f00ff003f003f003f00bfaabfaa3f003f00bf00bf003f003f003f3f3f003f003f003f2a3f2a3f003f003f00ff003f003f003f003f003f003f003f0000003f002a003f002a003f0015003f0015003f000000ff0000003f0000003f003f003f0000003f0000003f000000000000003c3c3c3c3c3c3c3c3c3c3c003c3c3c0033333333333300003333330033333300330033003300330030303030303030302e2e2e2e2e2e2e2e2a2aaaaaaaaaaaaa2a2aaaaa2a2aaaaa2a2a2a2aff2aff2a2a2a2a2aaaaaaaaa2a2a2a2aaa2aaa2a2a2a2a2a2a2aaaaa2a2a2a2a2a2a2a2a2a2a2a002a2a2a00) else (if page < 6 then 0x8a0a8a0a8a0a8a0a8888ff88ff88ff888888f8f8f8f8f8f88888aaaaaaaaaaaa88888888ffffff8888888888ff88ff8888888888ff88888888888888f8f8f8f888888888f888f88888888888aaaaaaaa88888888aa88aa88888888888888ff88888888888888f8f8888888888888aaaa8888888888888888888888888888880088888888008800888888888800000000888888088888880888888800ffffff0088888800888888888888880088888800888888008800880088880088008800888888000088880000888800000000000088808880fff0fff0888088808880888088808800888088008808880888888888880888088808880888080808880808088800ff008800ff00880088888888888888008800ffff880088008800ff00ff0088008800f8f0f8f08800880088888888880088008888880088008800888088808800880088008888880088008800880088008800880000008800800088008000880008008800080088000000ff00000088000000888888888800000088008800880000008800000088000000000000008282828282828282808880888088808880808080ff80ff8080808080aaaaaaaa80808080888888888080808080808080808080008080800080008000aa00aa00800080008888888880008000880088008000800080808080800080008000800080000000800000007f7f7f7f00000000 else 0xaaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaa88aaaaaa88aaaaaa88aa88aa88aaaaaa22aaaaaa22aaaaaa0aaaaaaa0aaaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aa00aa00aaaa888888888888aaaa8080aaaa8080aaaa222222222222aaaa0000aaaa0000aaa0aaa0aaa0aaa0aa88aa88aaaaaaaaaa88aa88aa88aa88aa888888aa888888aa80aa80ffc0ffc0aa80aa80aa80aa80aa2aaa2aaa2aaa2aaa2a2a2aaa2a2a2aaa22aa22aaaaaaaaaa22aa22aa22aa22aa222222aa222222aa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa020202aa020202aa00aaaaaaaaaaaaaa00aa00ff00ff00aa00aa00eac0eac0aa00aa00aaaaaaaaaa00aa00aa00aa00aa008000aa008000aa002a00aa002a00aa000000aa000000a8a8a8a8ffa8ffa8a8a8a8a8fcfcfcfca8a8a8a8a8a8a8a8a8a8a800a8a8a800a800a800fcfcfcfca800a800a8a8a8a8a800a800a800a800a8000000a8000000a2a2a2a2a2a2a2a2a2a2a2a222222222a222a222a222a222a0aaa0aaa0aaa0aaa0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a020202020a0a0a0a000a000a0a0a0a0a000000000a000a000a000a00099999900999999008f8f8f008f8f8f008f888f88ff88ff888f888f888f888f888f0f88008f0f88008f008f008f008f008f0000008f0000008e8e8e8e8e8e8e8e8a8a8a8a8a8a8a8a))) else (if page < 10 then (if page < 8 then 0xeaeaeaeaeaeaeaeaeaeaeac0eaeaeac0eaeaeaaaeaeaeaaaeaeaea00eaeaea00eac0eac0eaeaeaeaeac0eac0eac0eac0eac0c0c0eac0c0c0eaaaeaaaeaeaeaeaeaaaeaaaeaaaeaaaeaaac000eaaac000ea00ea00eaeaeaeaea000000ea000000e0eee0eee0eee0eee0e0e0e0e0e0e0e0dcdcdcdcdcdcdcdcd500d500d500d500cfcccfcccfcccfcccececececececececcccfcfcfcfcfcfccccceeeeeeeeeeeeccccccccfcfcfcfcccccccccfcccfccccccccccceecceeccccccccccccccffccccccccccccccfcfccccccccccccceeeecccccccccccccccccccccccccccc0000cccccccc44444444cccccc88cccccc88cccccc00cccccc00cc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0c0c0eaeaeaeac0c0c0c0c0c0c0c0c0c0c0c040404040c0c0c0c000000000c0c00000c0c00000c000c000c000c000bfbfbf00bfbfbf00bf3faa00bf3faa00bf00bf00bf00bf00bf003f00bf003f00bf000000bf000000bbbbbb00bbbbbb00afafaf00afafaf00afaaafaaafaaafaaaf000000af000000aeaeaeaeaeaeaeaeaeaeae0caeaeae0caeaeae00aeaeae00ababab00ababab00ab000000ab000000aaaafefefefefefeaaaaeeeeeeeeeeeeaaaaeaeaeaeaeaeaaaaaaaaaffaaffaaaaaaaaaafafafafaaaaaaaaaeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa22222222 else (if page < 9 then 0xf000f000ff00ff00f000f000f0f0f0f0f000f000f000f000f0000000f0000000efefef00efefef00efeeefeeffeeffeeefeeefeeefeeefeeef000000ef000000eeeeffeeffeeffeeeeeefefefefefefeeeeeeeeeffffffeeeeeeeeeeffeeffeeeeeeeeeeffeeeeeeeeeeeeeefefefefeeeeeeeeefeeefeeeeeeeeeeeeeeeffeeeeeeeeeeeeeefefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00eeeeeeee00ee00eeeeeeeeee00000000eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeeeaaeeaaeeaaeeeeee88eeeeee88eeeeee22eeeeee22eeeeee0eeeeeee0eeeeeee00ffffff00eeeeee00eeeeeeeeeeeeee00eeeeee00eeeeee00ee00ee00eeee444444444444eeee00ee00ee00eeeeee0000eeee0000eeee000000000000eee0eee0eee0eee0eee0ee00eee0ee00eecceecceeeeeeeeeecccccceecccccceeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaee22ee22eeeeeeeeee222222ee222222ee0eee0eeeeeeeeeee0eee0eee0eee0eee0e0e0eee0e0e0eee00ff00ee00ff00ee00eeeeeeeeeeeeee00ee00ffffee00ee00ee00ff00ff00ee00ee00eeeeeeeeee00ee00eeeeee00ee00ee00eee0eee0ee00ee00ee00eeeeee00ee00ee00ee00ee00ee00ee000000ee000e00ee000e00ee000000ff000000ee000000eeeeeeeeee000000ee00ee00ee000000ee000000ee00000000000000ececececececececeaeaeaeaffeaffea else 0xfefefeeefefefeeefefefeaafefefeaafefefe00fefefe00fefefe00fe00fe00fefe0000fefe0000fefcfefcfefcfefcfef0f0f0fef0f0f0feeefeeefefefefefeeefeeefeeefeeefeeeeeeefeeeeeeefeaafeaafefefefefe00fe00fefefefefe00fe00fe00fe00fe000000fefefefefe000000fe000000fcfcfcfcfefefefefcfcfcfcfcfcfcfcfcfcfcfc54545454fcfcfcfc00000000fcfcfcf0fcfcfcf0fcfcfcccfcfcfcccfcfcfc00fcfcfc00fcfc0000fcfc0000fcccfcccfcfcfcfcfcccfcccfcccfcccfcccccccfcccccccfcc0c0c0fcc0c0c0fc00fc00fc00fc00fafafafafafafafafafafa00fafafa00fafaf0f0f0f0f0f0faf2f2f2faf2f2f2faf0faf0faf0faf0faf0f0f0faf0f0f0faaafaaafaaafaaafa0a0a0afa0a0a0afa000000fa000000f8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f888f888f888f888f800f800f800f800f7f0f7f0f7f0f7f0f700f700f700f700f6f6f6f6f6f6f6f6f500f500f500f500f4f4f4f4f4f4f4f4f3f3f300f3f3f300f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f1f1f100f1f1f100f0f0f0f0fff0fff0f0f0f0f0fff0f0f0f0f0f0f0fafafafaf0f0f0f0f8f8f8f8f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f00000f0f0f0f000000000f0f0f000f0f0f000f0f08080f0f08080f0f00000f0f00000f080f080f080f080f070f070f070f070)) else (if page < 12 then (if page < 11 then 0xff888888ff88ff88ff888888ff888888ff888888ff000000ff88888888888888ff80ff80ff80ff80ff808080ff808080ff77ff7700000000ff77ff00ff77ff00ff70ff70ff70ff70ff3fff3fff3f0000ff3fff00ff3fff00ff3faa2aff3faa2aff3f3f3fff000000ff3c3c3cff3c3c3cff2aff2aff2aff2aff2a2a2aff2a2a2aff0fff00ff0fff00ff0f8808ff0f8808ff0e0e0eff0e0e0eff0c0c0cff0c0c0cff0aff0aff0aff0aff0a0a0aff0a0a0aff08ff08ff88ff88ff08ff08ff08ff08ff080808ff080808ff03ff03ff030000ff03ff00ff03ff00ff030303ff000000ff020202ff020202ff00ffeeffeeffeeff00ff88ff88ff88ff00ff00ffffff00ff00ff00fff0fff0ff00ff00ffeeffeeff00ff00ff88ff88ff00ff00ff00ff00ff00ff00ff000000ff00ff00ee00ee00ff00ff0088008800ff00ff0000000000ff00f000ff00f000ff00ee00ffffeeeeff008800ffff8888ff008800ff008800ff007700ff007700ff003f00ff003f00ff003f003f003f00ff000f00ff000f00ff000300ff000300ff00030003000300ff000000ffeeeeeeff000000ff888888ff000000ff00ff00ff000000ff000000ff000000ee000000ff00000088000000ff0000003f000000ff00000003000000ff00000000000000fefefefefffefffefefefefefefefefefefefefe00000000fefefefafefefefafefefef0fefefef0 else 0xffffa0a0ffffa0a0ffff8888ffff8888ffff888888888888ffff888800000000ffff808080808080ffff0000ffff0000ffff000000000000fffefffefffefffefffeffeefffeffeefffefefefffefefefffcfffcfffcfffcfffafffafffafffafff8fff8fff8fff8fff0fff0fff0fff0fff0fff0fff0f0f0fff0ff00fff0ff00fff0f3f0fff0f3f0fff0f0f0fff0f0f0fff0f0f0f0f0f0f0ffeeffeeffffffeeffeeffeefffefffeffeeffeeffeeffeeffeeffeeffeeff00ffeeffeeffeeeeeeffeeffeeffee0000ffeeff00ffeeffeeffeeff00ffeeff00ffeeefeeffeeefeeffeeeeeeffeeffeeffeeeeeeffeeeeeeffeeeeeeff000000ffeeeeeeeeeeeeeeffeaffeaffeaffeaffeaffc0ffeaffc0ffeaffaaffeaffaaffeaeaeaffeaeaeaffccffccffccffccffccccccffccccccffc4c4c4ffc4c4c4ffc0ffc0ffc0ffc0ffc0ffc0ffc0c0c0ffc0d5c0ffc0d5c0ffc0c0c0ffc0c0c0ffc0c0c0c0c0c0c0ffbfffaaffbfffaaffaaffaaffeaffeaffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaffa8a8a8ffa8a8a8ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ff8fff88ff8fff88ff88ff88ffffff88ff88ff88fff8fff8ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff888888ff88ff88ff880000ff88ff08ff88ff08ff88ff00ff88ff88ff88ff00ff88ff00ff88f080ff88f080ff888f88ff888f88) else (if page < 13 then 0xffffffffffffff88ffffffffffffff00ffffffffffffeeeeffffffffffff8888ffffffffffff0000ffffffffffeeeeeeffffffffff888888ffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffff0f0f0f0fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffee00ee00ffffffffee000000ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaa000000ffffffffa0a0a0a0ffffffff88888888ffffffff88008800ffffffff88000000ffffffff80808080ffffffff80008000ffffffff3f003f00ffffffff03000300ffffffff00008888ffffffff00000000fffffffefffffffefffffff0fffffff0ffffffeeffffffeeffffffeeffffff00ffffffeeffeeffeeffffffeaffffffeaffffffaaffffffaaffffffa8ffffffa8ffffffa0ffffffa0ffffff88ffffff88ffffff88ffffff00ffffff88ff88ff88ffffff80ffffff80ffffff3fffffff00ffffff2affffff2affffff0effffff0effffff0affffff0affffff08ffffff08ffffff03ffffff00ffffff02ffffff02ffffff00ffffffeeffffff00ffffff88ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffff0f0fffff0f0fffff0f0f0f0f0f0ffffeeeeffffeeeeffffeeeeeeeeeeeeffffeeee00000000ffffc0c0ffffc0c0ffffc0c0c0c0c0c0ffffaaaaffffaaaa else 0xffffffffffffffee)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xcde7d5233b9f148 else 0
  | 3 => if page < 1 then 0xcef0a94d71cef0a9bd4dcef0aa0d48ceefba7283cef0a92181c8e8a9f548c8efa9f148 else 0
  | 4 => if page < 1 then 0x33bc2a6f5c4cfc8f0ca2a535c73bc2a488b971cdf0c922295c73bc2a488a171cef0a921cf5c723c328a9bd4dc8f0ca2a835233bc2a6f71148cef0a9bdc44073bbee9c9bdc4cdf0c921e56f73bc2a48795bcc8f0ca2a486073bc2a4879580cdefaa72535c737bea9c9bd4dcdefaa728352323bea535c488c8efa9bd4d22323bea8352088c8efaaea9ca0f37bea9c92181c8efaa727d52323bea9c52095c8efa9218122323bea9ca0c70 else 0
  | 5 => if page < 5 then (if page < 2 then (if page < 1 then 0xcdd08764442399a901e5be3d7a64cf5e9083d795c4e8f171393c5c4e3f2be38bc5c4e1f1dd36f98b8d7f22e32bc774b7e5df2d39774b4e5802d3c520b4e5012d39774b3e66f27bc5c495f22e237c98488ce4e22339ec889d80223643888cd082235cec863e611f3a9387cea7b1f2e4207cf22e1e7ca0c75f22e1d7c73c75f2511d7938875f22e1c7c9bc70e66f1bb99bc6de62e197c6045ef30b160f220585ef9048f00260ec00cddf003307c009f3700273dc009c9f001c3f80039fe000d9f80027fe00088dc002177000587c00061f else 0xcef0a0307002d5a0f9002d99bf9002d79bf9002d69bf9002d59bf9002d49bf9002ba9bf9002b29bf9002b09bf90026f99790026f7e79002ee7c79002d57c79002cc7c7900337979b00337939b0033bbecf0030ca2a70028a9f67003379cd70030c9c670030a6f36001e26e3c0030c607c0028a607c0026a603c00222603c00337601e001e1603c0022e5e7c002815c7c002805c7c0027f5c7c0027e5c7c0027d5c7c002785c7c002765c7c0024d5c7c002365c7c002315c7c002305c7c0022f5c7c0022e5c7c0022d5c7c002295c7c002275c7c002255c7c002235c7c002225c7c002215c7c002145c7c002125c7c001ce5c7c001cd5c7c001885c7c0022e5c3c0022e57bc0026a52390030c4ee70026f4ab900337439b001dd4379002cf423c) else (if page < 3 then 0xcde6f4399c328a43a3cdddd4399c328a4225b3e6f4078cde6f4059cef0a40478b9713df87b98e3d788b9483d788b9713bf4cef0a3887cdd71389c9117138b85c4f538b8afa6f33f8cef0a33c79b17133f89ad7133f89a97133f8cef0a3147cdf0c2d075c4cf2d38cef0a2cc7c29dd2cf19bddd2bb1ce30b2987cef0a2987cdf0c28479bddd27f8cef0a26878b971231cc066f22318b9b622349bd8022348b9802234a0d7122348b971223473d7122349457122319bd4822319bd0e22317750e22319bd0122315c4e22234cef0a204798ddf1f38a0ddd1f389bd011f38c2a2e1d74cef0a1d479bccf1d788b8881d7494d7117b89bd4d17b8a0d4817b8c328a1607cdf0c14c7cef0a14c7cdf0c1007cef0a1007cdf0c05c7cdf0c0587cef0a0447 else (if page < 4 then 0xc322e5c459933bc2a2e5c4400337b566f6400c328a97a30030ca2a4e8c00cf73bc2870033ccef0a1c00cef1ec2870033bc5f0a1c00ce30bba870033bc2aea1c00cdf0cb88700338c2ec81c00cef0ab20700337c32be1c00cef0aa0c70033bbe6731c00cef0a8b8700337c32221c00cef0a884700338c2e091c00cef0a824700337c32031c00cef0a7fc70030ca29bd9800cde2e6bdc0033bc29991c00bba6f6038003379bd807000cde2e601c0030ca29809800bba835c780030c94d71e000a2a535c7800337a0d7170009e62e5c78003378b9717000cce2e5c5c003308b971700091e2e5c780030a8a171d000c2a215c740033773d717000cde515c590033bc29711c00945b85c780026f69571e000cdf0c5a870033bc29691c00ce30b55870033bc29561c00cdf0c53c70030c9bd4de000a2a6f53780030ca0d48e000a2a835238003379bd486400cef0a52070026f6e148e000cdf0c49c70033bc29261c00ce30b45870033bc29161c00cdf0c4407 else 0xcef38c322e5c44cdf0ca2a2e5c44c328a9bd7133e0ceef98b97122040030cb568a9be100337c32ee98c30030ca2a2e6be40030ca2a6f60240030ca2a2e60240030ca2a835c6400338c2e2e5c4c0033bc2a2e5c4c00338a6e2e5c540030ca2a2e5c640030ca2a295c640030ca2a225c640030ca29cf5c640030ca2a515c610033bc2a6f5c450033bc2a2e5c4500337c31b85c460033bc29b75c460030ca2a6f52210030ca2a6f43a10030ca29dd43a10030ca2a6f406100337c318e3d430033bc298e3d030030ca297138a40033bc2a6f33c30033bc2a6333c30033bc298e33c6003379bd7133d80033bc297133c60030ca29dd2d210033b8b971230c002f98b971230c0026f5c4cf22300033bc2a2e1f060033bbe62e1d4c0030b8b97117a4))) else 0
  | 6 => if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x247e46fc8bf913f217e41fc81f8fff1f7e3dfc79f8eff1d7e39fc71f8dff1b7e35fc69f8cff197e31fc61f8bff177e2cfc57f8abf147e26fc49f88ff117e21fc41f87ff0f7e1dfc39f86bf0cfe17fc2df857f0a7e12fc23f843f07fe0efc1bf833f05fe0afc13f823f03fe06fc0bf813f01fe02fc03fef7e else 0xa8fe9ffa6fe97fa4fe8ffa2fe87fa0fe77f9cfe6ff99fe63f96fe57f94fe4bf8ffe37f8afe27f86fe0bf81fe03f7ffdfbf7cfdeff7afde3f77fdd7f73fdcbf71fdc3f6ffdb7f6cfdaff6afda7f68fd9ff65fd7bf5dfd73f5bfd6bf57fd53f53fd4bf51fd43f4ffd3bf4dfd2ff4afd27f) else (if page < 3 then 0x89ff12fe23fc43f87ff05fe09fc0ff817f01fe01fbfff7f7efdfdf7fbe7f7c7ef1fddbfbaff757ee8fdcdfb93f71fee1fdc1fb7ff6efedafdadfb57f69fed2fda3fb43f677ecdfd97fb2bf64fec8fd8ffb1bf62fec4fd87fb0bf60fec0fd7ffafbf5efebcfd75fadff5afeb4fd67fabff567eabfd55faa7f else 0xbbff75fee9fdcffb97f71fee1fdb7fb67f6bfed5fda7fb2ff64fec7fd8bfb0ff60febdfd77fadff5afeb3fd63fabff56feabfd53fa9ff52fea3fd43fa7ff4efe97fd27fa3ff46fe8bfd13fa1ff42fe83fcfff9f7f3cfe77fcabf947f27fe4dfc8ff90ff1efe3bfc73f8dff1afe33fc63f8bff16fe2bfc53f)) else (if page < 6 then (if page < 5 then 0x82bf827f823f81ff81bf817f813f80ff80bf803f7fff7fbf7f7f7f3f7eff7ebf7e7f7e3f7dbf7d7f7d3f763f75ff75bf757f753f74bf743f733f72ff72bf727f723f6f7f6e3f6c7f6bff6bbf6b3f6aff697f693f687f683f67bf677f673f66ff663f65ff65bf653f61ff61bf613f60bf5fff5fbf5f7f5f3f5eff5ebf5e7f5e3f else 0xaabfaa7faa3fa9ffa9bfa93fa8ffa8bfa87fa7bfa77fa5bfa57fa4bfa47fa3ffa3bfa37fa33fa2bfa27fa23fa1ffa1bfa13f9fff9fbf9f7f9e3f9dbf9d7f9d3f9c7f8eff8ebf8e3f8dff8dbf8d7f8d3f8cff8c7f8c3f8bff8bbf8b7f8a7f89bf897f893f88ff88bf887f86ff863f85bf857f853f84bf843f83ff837f833f82ff) else (if page < 7 then 0xc83fc7ffc7bfc77fc6ffc67fc63fc5ffc5bfc57fc53fc4ffc4bfc47fc43fc3ffc3bfc37fc33fbdffbdbfbb3fbaffbabfba7fba3fb9ffb9bfb97fb93fb8ffb8bfb87fb83fb7bfb77fb73fb4ffb4bfb3bfb2ffb2bfb27fb23fb1ffb1bfb17fb13fb0ffb0bfb07fb03fafffafbfaf7faf3faeffaebfadbfad3facffac3fabbfab7f else 0xb945edec217b7aec5edeb517b7a945edf03179fbf05e7e82179f9ec5ebe7317b78445edd8017be57c5edd3c17b747c5edd0e17bb4205ef4ad17b718c5e7c62179fce0587f0c161fa60587e8a161f22c587c87161f178587f0b14efcdc537f0914df244537c8814f7190537df711fe41847fa67103dc2c40bf37101fca8407f28101fc90407f09101fae4407dc1103e500407d3a101f36040f891101f22040dc64101fca0367d400d9fcdc177f37059f7080cf90c033db566fe6295c7c88971f1dd2d398b875f000d03f0033ffc00c8bf))) else (if page < 12 then (if page < 10 then (if page < 9 then 0xbf488deea2237b2088de8322378dc88de2e223787c88de1e223787488de0922377fc88dd9922375f888dd7122375a088dd67223759888dd56223752088dd25223749088dd16223740488dce2223733c88dcc522372c888dcb1223729888dc9a2237c2881dc8820772207fde831f3e8b87cfa201f3e8787cfa1d1f3e7fc7cf9011f3e3887cf8cf1f3e2e47cf8b81f3e2687cfa631dbe9bc75f62e1d7dc2875ddb41d7e3e875f8cf1d7e22075dc881cb72206fde6f1afb98c6bec881a778b866fa2b191f5b8647ef9185fbe45f7e4e17bb else 0x638efdd713bf7b20eedd363bb7b08ecde433b3b4dcecdcf33b3bb68e2f737389f910e2ecf538bb9bcd9fa63367e8b8d9f9dd367e638d9f971367eb20d4f98e34fe62cd3f97134fe638d2f98c34be5c4d2f98e343e634d0f971343eb3ccffacc33feaf8cffa6a33fb988cfef3733df910cfecf533fb638cef97133be648c8fb37315f910c5ee40317b4d4c5ecf5317b774b4ed712d3d370b4eccf2d3bc28b3de6f2bb7c30abdf0a29b7cdca67eee287bcdca17e6f27feb3c9afb37269f8b88efa2e231f5c48c7f052237c1088defe2237) else (if page < 11 then 0x6b171f9aa5c7e6a171f9a75c7e69571f9915c7e5fd71fb0a5a77c315cdf0a55b7b0956debb55b7a7556df37559fa6d56de9355b770956fb3753dfcdd487f27521f6e148f9ac523eaed42dd714f775213ddf0c4f375593cdd424f37c2926dddd4837c311dded147777651ddf0a45b7b4116df37459f79116f737441fc310eee8a43bbc3108f68a423d77507fad1413e5c504f948413eb3d01fb37405f78501f6633dfb8b8f7ed8e3dfb5c4f7ef1a3d7b7c8f5ed8e3d7b628f5ed483d7b4a4f5ed013d7b638f4ee423c3b98cefde2e3bf7 else 0xbe673de8a9cf79e62eee5e8bbbcde2e7f338b9fcc22e7f2d8b9fc2a21df0c83b7c2a09df37825fa6e09df3780dfcddff7e6f70fe8b9c3fb0c6f7ec65b8fac86e3e6f5b8fa6f697b98da5ee2e68fe6d59ffb37665f6e199fb0c603ea2980fa6f5c7d9b171f66b5c7d9a971f6685c7d99971f6505c7d8a971f6295c7d88971f61a5c7d86571f5ed5c7d7b171f5ea5c7d7a571f5e85c7d79d71f5e65c7d97971ee585c7bcdd717f335c5fcb5717f295c5fc9d717e475c7b74d71f5c35c7e6f571f9bb5c7e6e971f9b95c7e6e171f9b75c7e)) else (if page < 14 then (if page < 13 then 0xc328a14e78b97113bc9bddd11398b971113cce2981017c328a10278b9710ebc8b9710dbc9bd480db99bddd0c3998d8e0a7a8b9710a7c9bddd07798b97104fcceef9044f8b971047c9bddd03b98b97103bcceef9030f8b971033ccef0a8b87cde2e5c5ccef0a5c478b9712234002eea0fb002f198fb002ef98fb002ee98fb002ed98fb002d598fb002cc98fb002ac98fb002aa98fb0030297fb0028a97bb0026f97bb0026397bb00263973b002ee96fb002ee96bb00307967b0030c93bb0028a93bb0026392fb0033acddf00339cddf00337cc9f0033bcc5f00337cadf00334cadf0033bca9f00335ca9f00338ca1f0033bc99f0033bc95f00337ba9f00337b89f00337b21f00337af9f0029aa2b700299a2b700337a0df0033b9cf70030c9cf7 else 0x9117133fa9017133fa7857133fc5c53533fa5c50b33fc638f533fa5c4f533fa8b971323cc328a3167c328a2d27c31dd2d399bddd2d39ceef9298fc328a29a7c328a28679bddd2879c328a26a7cee2e230fbe62e230fced71230fbe571230fc1a6322338b971223c9bd7122358b97122359bccf223398ccf2233638cf22365c4cf2236ceef9204f8b971207cc1a631f3ac2a2e1f3698ddd1f3a9bddd1f398b9711f3c98cdc1f3a9bccf1f3a98ccf1f3a8b8881f368b87d1f3cbe62e1d7cceef91d4f8b9711d7c8b87c1d7c98c7c1afa8b971193cc2e2e17a79bd8017bc8b98017bca0d7117bc8b97117bc73d7117bc9457117b9c2d7117a79bd4817b99bd0e17b97750e17b99bd0117b95c4e217bcc322e16678b971167cc31711667ce29814d7) else (if page < 15 then 0xcef0a5c4fce29b5c57c328a5c679bdb85c7c8b9b85c7c8a9b85c7c785b85c7cc29b75c768b9a05c7c8b99c5c7c8b97a5c7cc328a5aa78b9715abc8b971587c8b97156bcceef9558fc328a55a7c328a53e78b97153fcc326f5239aee6f5239a2a6f5239c328a52278b97150bc9bd4850b98b9714f3c9bd484f39c328a49e79bddd49f99bddd4779ceef9458fc328a45a7c328a44279bddd4439c326f43b9a2a6f43b9c31dd43b9a29dd43b99bddd4139c326f4079a2a6f4079c328a406798d8e3d7a8b98e3d7a6e18e3d7a8b9713d7c7750b3d79c298e3d338b9713bbc98d8e3a7a8b9713a7cc328a38a7c317138bca297138bc9198e343ab3e6f33fab3e6333fab6a6f33f9cde6f33dbcde6333dbc328a33e7cdd8e33de9118e33facdd7133de else (if page < 16 then 0xc32e2a2a7c32c8a2a7c32bea2a7c328aa0e7ce30b8b8fcef0a8b8fce29b8b97c328a8ba7c328a88a7ceef9824fc328a8267c328a80e7c328a7fe7a2a2e6bfcc328a6667c326f603ca2a6f603cc322e603ca2a2e603cc32835c7ca2a835c7ccfa2e5c7cc862e5c7cc822e5c7cc722e5c7cc662e5c7cc322e5c7cc2a2e5c7cbc22e5c7cbba2e5c7cb8a2e5c7cb3e2e5c7cb0a2e5c7cafa2e5c7caee2e5c7ca822e5c7ca7e2e5c7ca762e5c7ca6e2e5c7ca4e2e5c7ca422e5c7ca2e2e5c7ca2a2e5c7ca162e5c7c9322e5c7c9122e5c7c9022e5c7c8fa2e5c7c8f22e5c7c8d22e5c7cc32295c7cc32225c7c8ba225c7c8ba0d5c7c8ba035c7cc31cf5c7ca29cf5c7c8b9c75c7cbba6f5c79c32515c79a2a515c79cde6f5c5dcde2e5c5dce30b5c4f else 0x30cbba8a98e3cef38c322e1f37c328a8b87cef388b971730ca2a2e5c6ccde8a8b971730ca2a6f5c65c328a8b971973bce30c5c47cdf0ca29711f0ca29b85c66c328a638f58f0ca2a6f33e3c328a98ccf8f0ca298e33e6c326f5c4cfe28a9bd7133f8c328a5c4cf9b3bbe62e2207be62e5c488d33bbe5712207ceef98b87c3b0c8b97117b4ce22e5c45e72988b97117b49bd7133c5ee22e5c490179c8b97121c5ed30ca2a2e5c64002eeb6a6fe400b568a9bf900337bba636c00ccb0ca2a70032bc328a9c00c830ca2a700319c328a9c00c32eaa2a7))))) else 0
  | 7 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x88bf873f84ff837f80ff7fff7ebf6c3f6b7f66bf657f617f60ff603f5ebf5e3f5abf593f587f56bf55bf53ff527f523f50bf4f3f49ff48bf45bf443f407f3f3f3c3f3b3f397f37bf33ff323f317f303f2eff2d3f2c3f287f25ff24ff207f1d7f17ff13bf10ff103f0ebf0dbf0c3f0b7f09ff097f08bf077f06ff047f033f603e else (if page < 2 then 0x98db0fac867f79919fde635dbe9bd71f6675c7d7ad71f7375c5f73d71f5b85c7e6a571f9a65c7e64d71f9805c7eb2156de63523b96948edd945b79bd01ee63407b77d01f571407e52101f98e3d7b9bcf2ed8e353e5c4d4f98033fe520cff93433fe4d0cfed2d33fe424cfee5a317b4d0c5ed7126be8b888dd7122378b87cfa4514dfcac477e6d11df158477f2b101f4e4407dcf5c7c9bd48e66f407900320fc00c67f002f8fc00b8bf002dffc00b47f002c8fc00afbf002bbfc00ac7f00294fc009dff00239fc008d3f00232fc008bbf else 0x96840fe45103f8f440fd8e103f5c440fd6e103f55840fd48103f4e440fd36103f4d040fcfa103f3d840fcec103f31440fc8b103f21c40fc83103f1d040fc5e103f15440fd710ebf1783afd710dbf52036fc470dbfcbc30fddd0c3f17830ff2f0b7f7742dfd010b7f11c2dfe630a7f8b829fd8e0a7f5c429ff3509ff8b827ff2c097f9bc25fe2e097f77425fd8e097f5c425ff3508bf5c422fe6f077f1781dfe6f06ff11c1bfe2e04ff5c413ff3b047f8b811fe6f03bf8b80efddd03bf5c40eff3b033f5c40cfeee98fb98e4fef378b9f)) else (if page < 5 then (if page < 4 then 0x5c459ff3814ffcd453ff0c14ffbc853fe9814ffa2853fe4514ff8f453fcf614ff3b053fc8b14ff21c53fc5e14ff8b84efc5e13bf7744cff3611ffcbc47ff2b11ffbd447fed811ffb2047fe8311ff9c047fe6f11ff9b847fe6d11ff99047fdff11ff77847fddd11ff77047fddb11ff76447fd9911ff52047fd2e11ff4b447fd2b11ff4a447fd1611ff40447fcdc11ff2d847fca611ff26847fc8411ff15847fe6f113f8b844fddd113f5c444fe6f10ff11c43ff38103fcd440ff2b103fc3040fef2103fb2040fe98103fa2840fe63103f else 0x4c0a6fd2f29bfa28a1fe6f287fc309afed126bfa289afd9f26bf5c49afd2f26bf9bc97fd9f25ff8b893fcec24ff8b888fd71223fbe481fe2e207f9bc7cfe2e1f3f7747cfd711f3fbe475fd711d7f8b864fd71193f9bc60fddd183fb205ffd7117ffcc85eff2b17bfc145efefe17bfba85efec817bfa0c5efe3417bf8b85efe2c17bf8ac5efe1e17bf8245efdff17bf6645efd7a17bf5c45efd6f17bf5b85efd6717bf5585efd4817bf4a45efd2517bf4585efd0117bf3885efccf17bf3145efcb617bf2c85efca617bf2685efe2e167f) else (if page < 6 then 0xa28e2fe3d38bf3b0e2fe2e37bf3b0defe2e353f638d4fd71353fc30cffedb33ffb60cffecd33ffb20cffe8a33ff804cffde033ff774cffd8933ff520cffd3433ff4c8cffd2d33ff428cffd0133ff9bcccfe2e333f774ccfd8e333f5c4ccfe45323f5c4c8ff0c317fbc8c5fec8317fa28c5fe5a317f8f4c5fd8e317f5c4c5fd56317f520c5fd36317f4d0c5fd01317f3e8c5fcec317f5c4c0fcec303f5c4bbfcec2effc30b4fe6f2d3fb44b0fe6f2c3fceca6ff0c29bfc00a6fef929bfb44a6fe8a29bf8b8a6fdb329bf67ca6fd7129bf else 0xc3101fedb407fb6101fed1407fac501fe8a407f9bd01fe2e407f7fd01fdf0407f78101fddf407f77501fdd9407f67d01fd71407f52101fd16407f774fcfd9f3f3f404fcfe633d7f8b8f5fd8e3d7f5c4f5fe6f3cbf774f2fec83c3f5c4f0fe2e3bbf5c4eeff053b3fbfcecfefe3b3fba8ecfecd3b3fb20ecfe833b3f968ecfe393b3f8b8ecfe1e3b3f824ecfdf33b3f7c8ecfd8e3b3f614ecfd713b3f59cecfd563b3f530ecfd483b3f4e0ecfd363b3f4d0ecfd013b3f98ce9fe2e3a7f638e9fd713a7f914e5fe2e397fc30e2fef238bf))) else (if page < 10 then (if page < 8 then 0x5c56afef2593f5c564fd71587f5c55cfd7156bfced56ff0c55bfc1d56fefe55bfbe556fef255bfb2156fe8a55bf98d56fe5a55bf90956fe3d55bf63956fd7155bf59d56fe8a53ff5c54ffddd52bf5c549ff0c523fb4548fec8523faed48fe8a523f8b948fdff523f67d48fd71523f55948fd9f50bf5c542fd4850bf5c53cfd484f3fc3127fddd49ffb4522fddd48bf7751dff3b45bfc3116ff0245bfc0116fef945bfb6116fed145bfa2916fdff45bf77516fdda45bf76516fdb345bf67d16fd4845bf49516fe8a443f77510fddd413f else (if page < 9 then 0xbd171fef35c7fbc971fef05c7fbb971fed15c7fb3d71fecd5c7fb2171fec25c7faf971febb5c7fae171feb75c7fabd71fea85c7fa8171fe9f5c7fa7571fe9b5c7fa5d71fe945c7fa4d71fe905c7fa2d71fe8a5c7fa1571fe635c7f97571fe5a5c7f96571fe575c7f95971fe555c7f95171fe4c5c7f92571fe445c7f90571fe405c7f8fd71fe3e5c7f8f571fe3c5c7f74571fdc75c7f71971fdb85c7f6c971fdb05c7f6a571fda65c7f68171fd9c5c7f66571fd935c7f63d71fd855c7f60d71fd805c7f5e971fd785c7f5d971ff0c5abf else 0x8e62efe348bbf8ca2eff0c88bf8ba22fef2873f8ba1cfe6385ff8ba13fe2e837fcee09ff0c827fc1e09fef9827fbca09fe8a827fa2a03fe2e80ffc31fffed87fffb45fffe8a7fff8b9d1fe6f71ff8b9c7fe63717f9bdb8fe2e6e3fb21b0fe636c3fb61adfe2e69bf9bda2fe6f683f8b9a0ff0867ffc099ffefe67ffbd59ffed867ffb219ffe8367ff9e99ffe6f67ff9a59ffe6467ff7fd9ffdfa67ff9bd9cfe2e673f9bd9aff0c667fb4599fe8a667f67d99fe6f657f67d95fe635dbfcf971ff215c7fc7171ff195c7fc3171ff0a5c7f)) else (if page < 12 then (if page < 11 then 0x9697133fa77d7133fc5c53433fa6390933fa5c50933fa5c4dc33fc8b971317c9bd7131798b97117bc9bddd11f98b971103c9bd7133f800320c33f00319c33f0033bbabf0030cbabf00308b47f002f8b47f002f5b47f002dfb47f0033bb23f00319b23f0030cb23f00307b23f00300b23f002feb23f002f3b23f002f2b23f002d1b23f002fea53f00332a2bf0032ba2bf002eaa2bf002e2a2bf002c8a2bf002bea2bf0030ca0ff002d1a0ff0028aa0ff0033e8bbf003218bbf003208bbf0031c8bbf0030c8bbf0030a8bbf002f88bbf002f48bbf002f28bbf002f08bbf002ee8bbf002e28bbf002cf8bbf002cd8bbf002c88bbf002af8bbf002a08bbf0029f8bbf0029b8bbf002978bbf002908bbf0028b8bbf0028a8bbf002858bbf002778bbf else 0xce22e179fa622e17b79bd7117bd8b97117bdc317117b7ce171179fa617117b79bccf17bb98ccf17bb638cf17be5c4cf17be8b890179f5c490179f8b88717b75c48717b79162e14dfcba6f11df9be6d11df9bddd11fb98ddd11fb929dd11fbcb9dd11df78ddd11fd9bdbf11fe775bf11fe9bd7111fdcad7111df6393311df9bd3111fe7753111fe9bd3111df7753111df7752c11fd9bcdc11fb774dc11fd5c4dc11fd9bccf11fb9bc5611df9bd71103d8b971103dcad71101f70171103e5c539101f5c4fa103e5c4cf103e5c4cf097ec328a8ba7c322e5c7cbca2e5c7cb222e5c7ca2a2e5c7c96a2e5c7c8f62e5c7cc328a5c678b97155bc8b971523c9bd7152399bddd45b99bddd40798b9713b3c9bd7133fc7b97133fc9bd7133fa98d7133fa) else (if page < 13 then 0xb466f33fba2a6f33fbc326333fbb6e6333fba2a6333fb98de033fb9bd9f33fbc318e33feb6d8e33feb358e33fea298e33fe8058e33fe7818e33fe6398933fec317133febc97133feb6d7133feb217133feaad7133fea297133fe9bd7133fe98d7133fe9697133fe9497133fe8f57133fe7b97133fe7817133fe77d7133fe7757133fe9697133fb6017133fe5c55633fe7754833fe6394833fe5c54833fe5c53633fe5c53433fe5c53433fb6393233fe9bd2f33fb6392d33fe98d0a33fb6390a33fe5c50a33fe6390933fb5c50933fe5c4ec33fe5c4dc33fd5c4cf333e9bd71317d8b971317d98d71317b96971317b64d71317e5c534317b5c509317b5c4fa317e5c4cf317e9697126be5c4cf26bebe62e2237be5712237be62e1f3ec322e17b7 else 0xbba8a98fbcef388b9fc328a8bafcde8a8b9fb6e636c3eb466f67feb466f67f79be6467f7c326f5c7dbca6f5c7db466f5c7db226f5c7da2a6f5c7d9be5a5c7d9be3d5c7d99e3d5c7dc322e5c7dbca2e5c7db222e5c7da2a2e5c7d96a2e5c7d8f62e5c7dcef385c5fc328a5c6fcde8a5c5fbca3d5c7bbca3d5c77c31b85c7e9bd9f5c7db219f5c779698e5c7b9bd7155bd8b97155bdb217155b79bd71523d8b971523d98d71523b96971523b9bddd45bb98ddd45bb781dd45b7775d945b79bddd407b98ddd407b77ddd407d77571407e77548407e5c548407ec318e3d7bb466f3cbb8b9ef3b3dbca2e3b3b8f62e3b378b9903b3e8b98e3b3e9bd713b3d8b9713b3dbc9713b3b8f5713b376398a353e91571353ec326f33fb)))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x9bd9ffe2e67ff9bd99ff0c5c7fbc971fed15c7fb2171fe8a5c7f98d71fe5a5c7f8f571fe2e5c7f67d71fd8e5c7f5c556fd71523f77516fddd407f98cecfe2e3b3f638ecfd713b3f8b8e2fe6f33ff98ccffe2e33ff774cffd8e33ff5c4cffd71317f9bca6fe6f26bf8b85efd7117bf8b853fe6f11ff8b847fddd11ff5c447fd71103f9bd71f62e5c7d9bccfee6333fb638cff97133fe8b971f000babf002c8fc00a0ff00209fc007fff00199fc0055bf00148fc0045bf00101fc0038bf000cffc00317f000a6fc0026bf00053fc00103f else 0xc322efef28bbfbaa2efed18bbfa2a2efe838bbf98e2efe2e827f) else 0
  | 9 => if page < 1 then 0xc33fb47fa2bf8bbf67ff5c7f3b3f33ff17bf11ff else 0
  | 10 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x3c else 0
  | 3 => if page < 1 then 0x50 else 0
  | 4 => if page < 1 then 0x64 else 0
  | 5 => if page < 1 then 0x711744912435 else 0
  | 6 => if page < 1 then 0x5d12449124490d4350d4350d4210842107c1f0741f else 0
  | 7 => if page < 1 then 0x12449124490d4350d4350d4350d4350d421 else 0
  | 8 => if page < 1 then 0xd435 else 0
  | 9 => if page < 1 then 0x21 else 0
  | 10 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 7
  | 4 => 27
  | 5 => 297
  | 6 => 1061
  | 7 => 894
  | 8 => 72
  | 9 => 10
  | 10 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 1024
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 10)

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
  | 2 => 1
  | 3 => 4
  | 4 => 15
  | 5 => 171
  | 6 => 536
  | 7 => 553
  | 8 => 66
  | 9 => 20
  | 10 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 4
  | 3 => 17
  | 4 => 53
  | 5 => 619
  | 6 => 1930
  | 7 => 1990
  | 8 => 238
  | 9 => 73
  | 10 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 7
  | 8 => 7
  | 9 => 4
  | 10 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 7
  | 3 => 9
  | 4 => 11
  | 5 => 15
  | 6 => 17
  | 7 => 16
  | 8 => 13
  | 9 => 10
  | 10 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0xf else 0
  | 4 => if page < 1 then 0x5001ca0f204020d001108 else 0
  | 5 => if page < 3 then (if page < 1 then 0x10042000af81830e245830010700000438000283813e0848000042821a00400140400a2000485041c0800200008020010008240072214204 else (if page < 2 then 0x48100120c02409049081a60012020009400d9c160000a0e30105080c00135069c9032a0000026606820a4c0002a98100022c093003cb82 else 0x5d7810c0869c0e2c40514001db3e5c2000010982023c202060c48b063c0020204203340c405)) else 0
  | 6 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x6010b00020d0007030001000b00170002001703060000190003030112000100040f0101001e020b1200000101140518080905001002003e000200000100 else 0x10200070008000102171c0a000400021209090002000000000d0905000b02010820032b0008070c0a070000150902010402030f0f09000d24000702010403) else (if page < 3 then 0x10102080101010c0000110000010001040d0b040d1812021e06030103040101000805060000080239050306070000240101000513280c030113020a030600 else 0x60900001300031207080b010c26090206000d220007030103120908000603021b0d0d0004180522020b01050405020806020814063101000400010a000502)) else (if page < 6 then (if page < 5 then 0x1040502040019081033040d00002d321a000a0317011b04000602150d0004010400050b01280b01002a033e1a003f010200060023070700030602001700010c else 0x100021104201b00011401040019000400080102000e040c18110008241200041803030108000a0309040209061700000c0e0605021f0002014402010a00060b) else (if page < 7 then 0x6220a04151413031503350f040600121f3a01070e010013001203191f01032600030e000000000001161f05064603170701170007020a0c00100b1600000000 else (if page < 8 then 0x3250200000200110e11012a23060a010a0003041e3f1d02003ea203052d1929170701244211203d00000401070e040000020007030f11140004670200100614 else 0x1033117042c090906004e0a05020301000c030002012302)))) else 0
  | 7 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x6044032a14119000458900000000c003802414000020cb8402241020c24006200588108000860244595022c0282e0401300240001605208 else 0x9100e30097224810004054800601a050018006040008300088000020402100018600000040a18602241008000300805a780840c2c386) else (if page < 3 then 0x140028410304801600400000800000080034c002011a2ce040400080100800004008010a2460a0800081083c000043010204108800000081 else 0x480820b020020d0a00003005800000007021e2800328088aa2688101000c00a00f409608cc1124e11080200018d000c68006202000000619)) else (if page < 6 then (if page < 5 then 0x4ac0030708c0224132861a202a10e30e81003c6010024009040460010245000454a8908341800e48710080060124ac01c1200600780810e else 0x61871d023c480161ce9d0430c0200081c47a7c00f0604680240c002081460106140a51620802482cb800c7029442140083418204081800a) else (if page < 7 then 0xc0c0162c004000602303785802400107000e1800300003124a3810f00086860e54a9964542410c2c0800a203000028285031c18d026002b else (if page < 8 then 0x28840b0095705100d480006a5fd0225d00146000a0a4808302146d50009280760e60728043050c0c01888c4082101c1163404b496450000 else 0x1b66004808e009830020c2e1608011126c3005e00000000409c12044090c05b02003c008)))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x2cc830e3c1400d082410068244332c4000e0000080000430157080192204013000060c028c61c24312830012480000890618000010600004 else 0x209) else 0
  | 9 => if page < 1 then 0x5404d00a522f47100321 else 0
  | 10 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x100044 else 0
  | 3 => if page < 1 then 0x404c40187436000000030060c000081a0c0000 else 0
  | 4 => if page < 1 then 0x358900000000c0480002c63800b000160003a0000221e83818d0201c4008753200180925301806033079030131e40720c003c0280c6080000001730e1880d00001406009190488c000 else 0
  | 5 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x690000014010a9b55866701ca9330021011e10000445258800f00000220005889f484a000001b00f00c629000089000c01da22240000054011e1a4800d1200000002298000082111a000000000b301f803580388c954800013807a00170d08231001fbc7d48dc19bc68c18e30240035128206d60c0004743 else 0x81002e0134117400e12d86136187c09080d1004e03ec63c18e1194eaa5c035008e02141c59e3300dc00c4013c06780f000000000082011f60000458c8738a10e40c18d807828b022e00dc00000000000010d2000063008c18000000000000000000000000000002b4000000001cc3420013183800ca01000) else (if page < 3 then 0x24310b4952000004c24930082042865400950d241bbc34d0122021c538400000744972194c0310cbf483e31e1228382b49dc199988324c348b403f83790090003a1ba0331bc000120ac08f000000017601b4000007f01da00000090815022e901cc6a98220c4c0214456001a6cb6012403800e001aa03e00 else (if page < 4 then 0x12012449cc005852800ba48b8c311672870300f8927c37700b4003c09d524a07070d40042c357b0390000028d21e0000001a30dc34b06aa5a360c59201804c7600007c3318c0001fc0434663984e19bac389834811f19d2000000000000000000000b811e0020248867f80e1604cc089e000000000003e40 else 0x87000002246000009860000000400403011a31940038300011b1800035cc5224000000037980001070186013c400007e48363110022a5250c14180005398c0487a900002f80ec00c4c191892000000b8027581680c749b00418c32b005014e039c00001150c00006c368b9091800023006e802505341b85e))) else (if page < 7 then (if page < 6 then 0x1a806800d0640830d0cb801b60bcc02ab0af18641bf522b00e848b201ed24b25030d72945838f804c015c0084087a4990e12c33407a80230e20928529181153150944c02e0c3a013262a80578673611c18ec606b0bd00281c24340002478cec414043811441ba331832bb007005e90a40698442487218000 else 0x808694485e600004d8000017a920c46986780228044006800153144a80007580b6600003c400f0013004c1b6c65f2516016a045048e007a480002e808a80d901780098602986f614c041803580b40c96000044088610136c0d1e7e809c6048325cc4687133234025c30d06c601381b0523b01124a16f3ecc) else (if page < 8 then 0x52a4150d22ac30008b023489cc1bcc91b0381622000403018000042181156480da021e02783658020023601340500600000001ac271b10d61ee0429800009e180000000918c7701301b7d849869d0c9c20f807704c5483a30f9e20a4b7623203ec04606304a4e004404ba43d02500000000001b000000000 else (if page < 9 then 0x586128043402cb0b50c0000000000000023c0800000000000c8049808e040000a402f8064008f00000414343080001ec00cdb0000724800000800802240d8e00000288047000002ac05100bc785003e8003430004f4b230c69800908d80128c8e02e401f6c0fc071002c0048c02405800190d36341cc else 0x1180096e06034d0c0810f293a800e0cc2488a036c06808bf0000047406a000000000000000005e00000000000001a01b6207036280000000000009280000164048588080ce000001bc0532a14480000041)))) else 0
  | 6 => if page < 31 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x2b2017d011c00964c28ae379012080000058c03f60d200079c44bc02370102a086c102e01290914a4d292144dc1901f5b07f4062c62360071867d0056ee80001b20c1d15562009e71df8695c0394019c50220625c081a226e0cb0a4ba0f15a037e01f28007c40000081592e004800760016c00c5080a92112034b306a00ac8066ac36a0d43b8db03 else (if page < 2 then 0x37a01c018e00049ab3fa0206080f054bcc1d0113e32124017e084c4d9800738051c309f743f2a00006860130560806f7400000000000001048042293f300872ed7950faa26829c836ba037780289602a00344075860e1105fa45805590020648662c928c000003904080001434d65a19007d0037c076c0230020d8061c008a12a35400001700 else 0x60603ff01d51876c100001d6020500c786000024e55ca30884073a920f000000f49833e210d14ef0000007c0032c0cb130569868c9000020d18165200002bf0c00007ec055800000087a4e0806e2900001dc8000000000000004d0ca74000000000178a400005ba61ee4911a503825ece385790e00cbd55a602eb002c00000069a32ac040b009b8f)) else (if page < 5 then (if page < 4 then 0x20061088259c6a603a549af80ab8005e03690c1eaa09c2448937d013ab07304782038e6000006582246929340773800003329021199c80944c7ac000000b70070000ee019601ee0452406aa181e01ab80fb006621938006b00eacc06e02fb05ae8071407d003f0603506d903302d8f20180860a00568000000f7bcb1d200000407933127742 else 0x7601f6018c80edc57a6020d25df00fec14de491549093aee0f70202ff0d6120fb1839604110dfe80a7c0410306b0dc78080452722126485280060000002001950acc444000000001b3860000000015d000000000000002ee019706c3c4418180001d200000049ab8000196860000000018f090b060000000000001d4000000000024b5166810540) else (if page < 6 then 0x37a0366797600e8556120b63000000fc406920ba73098a48ad20f4b10c0042a4b04c384008b65c900a6d5000014c100000180144ec30e641804b51e0f0900000b82c308028e8000000000784037220000106009400840100001220698c0000000001713c000064cc2bd40f180f4406e601684846300b12000006e016b80000000003eb01da000000 else 0x47e009d6d60a46c8039e0c18493f06d58368a90550c60807a446b633e10021000d022f420530d6280a7920bc19f0491d8093d520eda92019b98f6003b0207300048060801200a8529b824495e34602e500c1887fc058422df49492c03405e40111406380afcf51402100e00009f5c236000b012c804cd26ea60f771ff01020064c3363311aa4df8c))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x81a09bf0000000000000031001b00c3d58502d82f11040063003e83000000000d9c0382009200c9010192000011c016e180000000034848f9b026461ae005e000000fdc04f400f901908c270900003300daa060000000037600402457c00181896120f00ba5c23e921000c2aa25035a2c35c0d13866a8261c21b0009e800fd24449011080386a555 else 0x13d0d81849e004bec00e0c1f01074c1da1a9678bb80ef8276603c600f0006e0336e025d012324d5807bc02c904000016c500000650136b8f94653600f4010500c7c057c2a494a0b80d84065e0354002b0600001ea00050a1080fb5806603630dd024f09e00002d501c6001e44000000001088c8c405f4c2a811d080f88044a900001190085c0) else (if page < 10 then 0xacc0000017009903000037f000000981200002c001c0b107921be202008fa3032d200003d0159d00f9003ee0091054ea445963d20abb70d7804080446020948923c0000230b00000e680000000001a408a33a000000002300539c200000000000000000921500001940208800040000000000bc007a8018cb80000000000000000000004d8c0000 else 0x36d0c0000000000003b700000043403100000000000000000002021444b0000000000044856007ac400001e800071e00006ee0134480000ed4006c2bc4480000000062a300001a488ae035c8030b10fc80718c554aa8b0171000000000035e00a58000002980020152d8c00000000416600000dfcc26a03a501d900f54600002bd102980b400)) else (if page < 13 then (if page < 12 then 0x2e293ec18a000bbcc4d48a8e61768003435c60292102b86b9800241852102482bec42842afc000000c480630c37800cea43d4478e628660018011457204b9f48d000189718491e310220855c05b26000003aae00004641800003080000000002610000002ac1038b200021000478008cc3cb0088003a007f20800010618000000001bc4a0e00c301 else 0x6e6ac0a1473860d807c60114300000bc40034913c0136169ec04540368780200f2852e4b038006d08000042a3acd0472806f000c662d679f8a46cc034c00eb60b380995b6ec91ed01a4800d817dcc0aa6c9124fe01164900002079e874c0221ae131350a0e9879ec41760a49800008020000007fb0c28100000e0119500c20074690f8719018f0d2) else (if page < 14 then 0x3c0116f00da0303acbd000000032821b229f478750a654066692cb007880ac005ece8ba001302688074890000000005d8004022726dcd2459985c631030085b0fac624eb00001e1000000542b800005c2e91021c6118a0000000e4050c32da307000874000002df00bdaa05846a2004f000da4298010eb08e01a008551843aab25614bbc1f12 else 0xd008d2010980f14006ac10a006c087c8022e5416185738b240026014d120f18800c7f41bd2020180f3802fc11e4040000c58617890c54800005bd260000cf590580674201e1b8401fc00469660e0108610916f6435a2f143094e245cc51d4040d00000000000da001e05a60012c06c21b2470e22400003d609d1091a866d4068a0348003206d080)))) else (if page < 23 then (if page < 19 then (if page < 17 then (if page < 16 then 0x14ed9d410cd8102400141986010b9ed8804d2e0980daa80768072c03620d3b8099492b8c019010886dbc0228007214960a374073c92ab009b005d057849419609524ef060f690951500303ec0646c33c00030c44c04821a1b00a7b86e8043a7877490f80ec45552031e01cb2444935a4036e0d100022120000066159486ec405d8142461a20083c3 else 0x11a03fc012f8c9e4113c522f00010087806e892b600672454805183398496600bf8081803bf011e80f20c42201bb00220459002a60076016f18d0405ee1a1e55c98c4edc5d5118e09782486433904bd504783a30d581e010d4901068e012e4bc040182808600704c26c757781040084401e200c0008f8008a0b28000404ea4019a93a6000a888b13) else (if page < 18 then 0x1b801c23010c05c4626929cab0d64373692e41877b7090003ac3b80cca06544c83000ef0cba800000500dae701d2980000362213a118300eb1200000df0400003a404ce20b102120cd680000028f4800010104000000000b50000007be01d5104d0a2c853a27403110718da000b418fd000000354013e584415f3002ec053634120d1f86a652 else 0x256012149d52400005ea00e0080000c9464e800000033866f846b2300001ed00020016c91e0053b98000000003af011d040c808160036080000341200003854938c2ca0300000340400000000508300000642c26d86be780001cba4000045490000000000cc5000000000162c00000be0a340c6e08da86648c00000753a0000000007c000000a612)) else (if page < 21 then (if page < 20 then 0x48e0000000000aa83000027601fc80c50600c1b1700e780f001504d09301ba80b91837a19f148ac00539c81e1b5b3c0000834c3501033080000000000000c25141b038d939a22fb01918c6a0300001ac000000da120682bab49c18c000055e0139081202d60c250aae261eb0837800000109085180140070e041a002e8a858682e32556000000000 else 0x82c00bd4800000000000013804c680290500003c230ef80c9060de90000187801353290883108000070c343401a10000006ac072260b959e0988a03830f2d46000000000066183c45fa801c00698224c495f22000000001da100000ef81000000000000000004861bf349b2300000104b8000004a4000000000000079b8d60063630140184800000) else (if page < 22 then 0x8323365618db0cec4634e372480000f41820ac09c6c73002281000034c04c806f280368004a61108600000660a010c8780958025e9348318200bf40264000000bc8076444a803320ce3a4bf8240603f2195d1eae8362ac00001a80200005791a041123002bd828818c658e180000031c031c018b00750154e2ae36043247f8034e1bea01b28674c4 else 0x3b8016d0000009b620462800000000c54020c03db01ea0002803d800000000009fdb1ae2800000000874300000d3098404e200160c366480000110066e90b75591240000000024c0189805598622000001a90ceb80140e9d000000049d34b002c1006224c34100000690c0000a71440e195041dd801fd2000020e002c804018000035c017018da98))) else (if page < 27 then (if page < 25 then (if page < 24 then 0x1d7100000088042061aa01cc00850680a026001723ca2186140184557000480c2aa0000019f009f400329399007200e14056a01a501a680644027c0347489f867e80000034f605f2cf6403f0026079321eaddc01810000162086d84658023a010b8689830000000003880a692774033f00f0886b8054a0000005a2c0cc4000037b0138b60000 else 0xb400b6010f1e00003c8217f008caab640000038301530023c06d0639301089880c45ba035d548080000034612130c9c0815124800b8d00730491406200800016500305245003a749b3988e40540b270857324000064e000000b2a4000027c13e505938c244211e28b359512a00002f8029310d008fe4248a60bd12028cf3001fc03ac00ca042698) else (if page < 26 then 0x1ca1a94595524dac345a000001598026c075600550083928e836fa600001c1b0a9c400003f401a80882033a4e19561ea80d7c3572d80001ee0026401c4e3aa00fe003d844bac28819800486032d6028511e6985c1772e031661038c978653c019708f108b8de000008e0d5e3ae1805f2000000000050404a40000005080d35871603841852001f52 else 0x69cc0000000000000272011d31c4b6da4052090b1499ea489805a4611d01631818c0506313700cd05079e508033d0167800a5250c028c6020a4908059a22db005a80e0865e800db00000087836bc33f601d6804b9240ec242048bb8a4401ac18a900000000000ac338a000000c54c458942300000104cc5b0027c01858304c0580628d000000c740)) else (if page < 29 then (if page < 28 then 0x3a0a4b49190400003b6241d013a80cd0064ec000003600c1827ce006148c804ac8202a01930cee1822c06a0000000c580aa054b4025b01eb80aee255a0091007180cd92520000001d10009585acc000020602cc8000003bd041300f9032bcc36f48888815c06c01a9240240066000061b0d00a500bd0220802c3707e308f4380ac0440579808f00 else 0x9aa41843000039c497c00dd522d290b54981009a1c792034c18e6000000298c000003ca40000000032e011f0665180000000020f80b11044a98000137b6724374e022e00eb088a4300000bb4a0398b3803cc0b5a1902000cd845a1800010a8c2a1d4861304091a24000077a0262000000d68305a02220d4394df1e01800844876041603) else (if page < 30 then 0x6cc1872018a30cac3556902b580000a3c618002af0cad810380000023301551e0a12000037c600000c70600001a900040708417dec16361b28cf3c02fc01e5015304ec0325a923c0e010020c2548015101138cfa4008e28c95d02886780556626b742888a3c04ce82df78fab0ce00312202100000000007f62000000000000000002c1119b806b40 else 0x2700071255e620d015cc294d2587125f0133370500))))) else 0
  | 7 => if page < 32 then (if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x7c0d4806d42bc406f40bf0000003381ca0000009b1200000000d8000000dd40968e000070160000b70d0000000000832e80bd444f526d001c1e00000000261c00000000000000000000bc8002520000000000000bc09640710000004f92811e00000000cf180000000033137b467dc303c100000000cf92304000000000 else 0x1c407902c0c3ce06ad8083212e4151522444c6c08c026706d500764277d24200794287c222002c8172808dd8ca4c3c409b14d346598c63005b4cb9446ac0470079003d049f588ec05e5cbd052ddc2b9c6f80d044000001c4000094520802981bce8c42d2d1c000000000000066400000000000000000a380000017d88118a8cc) else (if page < 3 then 0x3101a2c634406d498a41598050cc7952be414fd5a94040d29f80c900290199cc5352da8061467b03649236d6c74cd74c631896d5924064403012dcd20f80ae0c7954c08306848e9868005a065c062fc0500c52d26208bd4c61c667c87f405a46bf8123409ad21b066206a80043016b405d061c00af18da186bc0 else 0xbd40478253c325400018a9cc3650cb0414523652a41bab1259c6c1cc88980000000000000480bf5e3b10180c00001e807683a143d4062b406e8056003a92abd25f98000079c400005d86d2cc05120000000000002a8258c0338019001d806e066dc0848c00002d5c13c03bd36845739500005b522e0000002c4454cc00005bc6)) else (if page < 6 then (if page < 5 then 0xb5c0d64cda40c50316c3a11c745468017840114383c038c24052c5028500a6c097019992c34c198a88805f4082802a0000004a83511485c5154051d5111800006fd2000011820201251c1b92dc5e53802f842cc4529298866f8217409b1534c002c02e8442021dcc764397d793d20000938000003184000076c28ac37981 else 0xde121d438062be81600000000000cc98250a0000d31210c0cb00b7c0d2807a80ae802844a1dac280648622022b424b83d68000007e02d2000000bfc19d858d40ddc0d01e27c0778018de31c40000168381806fc47295ac000000b48000002046b6c6280400000000aa81000025c639847903aac05b981bc0100072d200004800) else (if page < 7 then 0xc3c0b1805780da0c02560000000000000000000008120000000089005b1e260aa7804952d14c00009e120e0c2f41dacc0000bd424e520000000000000000d900084000005d5ec652000030c1c6989d0000008f800000000000002a1877c3d10000001ac6a882b5400000b7468e8c1b40c80300005bdeb7d27115abd3b400 else 0x6952c942db0c8c0000002ec400006782000070c0000000000000c18c44d2699276c06f830000000077d4000000000000cb4357823582b95000002d98cc44a2432ad86c0672929d02a9cd0000080353c077ccce921ede07987640b50c1e8c998cdd4c56c08e0649120000000000001183000077983480000054800000b55c595e))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x69c08e80b4c1bb80771200003cc1000000007e4300000257d38c00000000000000004dc0ba803c800a80430300000000891e1d8cb1404b036a4000000000c04f3506cbc02c40000057c026c000000000b04009c3429200000000ca40b5c4000008d24252b60c8c43b910620200006581b9c02740c5d203404dcc000071120000 else 0x5a585c1801122684b8968a82b9869b80d3d25e9c34003ac00000b74023d213004b55bf40000000005d18c880a54c134000000000000014406b8239000000b8d600000000929247407d8077cf78c267809cc300000000c74000007b80958000002d58000000006500638000000000d400d31e0000af5ec5001e58908100000000) else (if page < 11 then 0x1a066ec04a037edc61d8b71030c2ccd829c13e81759274001d1bbd865640c718dd80c6129b523e40aa025ec03a823580a4c3aa01bec08158adc043809e80c558d84087425e045783cd98b9d679437d00c442420556926f8925c0021693c1c80cd258ca807a046f007cc06d804ad55b1890cc72d48cdbc000cbc348055506a8c0 else 0xaa8055003a40cdd811c300003e1cc7860e52be8428006a9822437c82c9c36303cfd21fd81f1cdc40615859c0da1e7fc0b4c4a7c04953a741bf4c3392164f5583609c488150008c9879802e4052126a18334c1b46b800bfc403c01c9ea08189812d0c5952cbc2c2588a440281c340dd529003df4632cc5d98491350c017808d00)) else (if page < 14 then (if page < 13 then 0x93c084c05912d7001058af4000000cdb00006bcc705200005255689d6f42afcc4641084c2798b481cd46364c48c1568c0000dec233029a40d982a300000093560000c6d83a4c7d818e40c100d08a72943742a883264428405acc354068c0cf465082c4d8d358b78006000000b3405dc61f8c0000ac023500331278c36e81 else 0x5a8c7c0240000cdaa0c45f003240b440961218d8a40018d2a1429ec0de806ac278584cc0a58066c0dc4c208677c258440c9e1d4f72156bd255800b055ad24212cf581a8c0000640000009ddb44000000ca020000884000439e4097000000bb067c5298210000000000002718d7400912690089400000d140711444413600631b) else (if page < 15 then 0x625885c444808a19aa007d43b880a44c58843b56be1e5d52cd066f02c64cbd00c9cc96d2ba0497d60852648c47013dd8b2806f88c180d6c05b401b00b6006040c44c06c01ec0b300cb8c8ac289c498cc3fc01c18db00420102845ccc3d84ce40a980dc0053c238c06d46d940cb0146c03204620029c488cc11c25bd20000a9c0 else 0x8a837742b4cc8700238000000000000000008e9e77c00c189080d60000000000000029120000000071d2dc0c6e928f4024d09a12a64036d323006f86158078843b80290000002a80454067182f40bbc00000b20040925a92bcc08fccc043c30c81c45443d1cc2c804c801b803f44ac4330c02590a9000dd20c40918ac240)))) else (if page < 24 then (if page < 20 then (if page < 18 then (if page < 17 then 0x4d9276021e00a2801880cc026ec22f0c4d40580015c44304000000008b40000000000000bdc60000db4c51d41ac036c4c5cc45806309cb82c7de3b401ecc0e00d6cc8f03144c3100c4401e5e6fc147c0bd41418674d6059251120000c800cf9e32010000000000000000dcde185e84cccc0caa41db808cda8b981a40000022c0 else 0xb4c0b816d64022839d43b0c043c08918838c0ac3bdd8d2c07743dac000006dd238168b03189e0000699eb786cc0095121d216e002b992000695e3700788000000b80d240d5c0a0403c008dc0c480cc03610196d38c9a6b807200bb40a183399675d29c0065c0c3c200000b5b1950dc527c038200a981678136c1000036cd2801) else (if page < 19 then 0x6c826b42618060dca242484000000000b0804f1200002741000000000000000049c0ddd21fc6bbd6318036806c4300009e0c558239c0df58cec68540000064982744aa03b8566c00631a99c000007195cc8600009683291600009c024e92a7c200004680d586d54662c1b9167415d0c066005c86b8406f431643da00bd455598 else 0x78122dc06d48904122c327451ccc6ac3338277cebac09412b5804512a5019100d4865558db8c4fd45dd82d59d51296d421951ed86ec376c3cb836b12a5c01258ba00185873d56cc0610023034980ba968c4295ccb70c760326c1295636568e18c84072522215aa42d4c0afc0d8c04d007e008f83000000000c988480a20226c4)) else (if page < 22 then (if page < 21 then 0x938c87432957c40c9200c1c063081c067a4042038dc300000000a84000000000bfc0078600002bc16a861f80c7038bc262c072144300a34026c55c4600000a006b43128c6280ce185ea2de58858571520800c38068442917b980d0129f00bc1c9a4c64c00f5b7352acc0560200009797cb401944bf52794c20c0ced80552019c else 0xc1407846d980bb46c9c075526d4301440e801a86ac80411290c06181c38c0000c2c07edd214f2d80c8c0000009820000a119285600009a9277d5d7c0b8c0828c1c9873122098968f00006306ca0312d292d2dec03d40be807c4c9fc0b000b7d6824ccb80a54014c006c621cf6a066c92460047837401ba405b46ae403d41a3da) else (if page < 23 then 0xcd86ab924880c54683cc8603075cdb40824073d4cb4215d06b5235c0a1d8c3c3c700b24037c0199c100610801700300c00c0bec22d9936d03081a9c136d2a6003bd2289676008000b58c098000003ec0a70074d77ac034023ec118cc9140d18037400000038005c01f40bac6985298982a01c20c205800002841d78000008d83 else 0x834f000000000000d4460000855b87c376820204d78c00006fc082c50000840c8fc0000041c0d54024c43f846203000024404e00560304c0c14c21c387400000aa40c30048c08800544019d2ba46b640cc41a44000000a44990c0000d80c8d03dd009745af80000043020000ccc64bc3b2d8794e67832e04af582d822c0491c0))) else (if page < 28 then (if page < 26 then (if page < 25 then 0x890cd20c000000000000d09c000084001c0c00001a52dd5e148c54427041bd98000000002fc10000214315008e4c00008a1ca3db990018c020c3b6c06d40a30c00000000028009c2540029c07512b5000000cc4c3a000000b68000000000000055400000cdc62e42a018ad40138125841f0a79845195170c6c0c0983 else 0x86400000414055c0b1c0a2d8040332c0d8802a8112000f0521805c985fc09682018a6240815b87c06f52bb00d68cc4431a183dd9bf0c3340ce462a040000a4800000625b71947ac1b64c8d02c28c00002e013a801c805b5e8b9a6d83241294c074140000000000000d0014dcc7d2000000007c8067dbdd0c3140508330848c9b) else (if page < 27 then 0xdc8045c065d8919c5a00c9c2aac34b0fdbc0000063c063027d8253d8000000000000bf8414000000c61e0000c0027a41c94000001cc0000019de000054c0794f8d825cc0cd580000815a6740000000006c5200003840000000000000000000006e405e4a181277860000000004436d068f82d846831b6d826680cc406c420000 else 0x5c588f5b38804340c88c95c08f02a5c103046540bd43d5c6c7028343089276807b583280574009c0b3805e10df013a93a804ab5246445bc000003482b2c0330081d000006f032d404a8fd3800000b1ccda8cde467c00a6925040b1001a809bc071c0000000002f124ed22fc400000000be4453128458de006f1200007bc2b484)) else (if page < 30 then (if page < 29 then 0x5b58378098c0ad0048046c8079400000c586cd1812800cd867c99c830000c9431a4cdbcc6580d7cc3b045b86d4c6b3c0000000000000d18c00005c0c000000000000000058ccaec00646dc8c9101cac03ac29952749582d10000bcc5704000006c4036534a433bd68c0383809751d9c170c1cfde44447dc20d960d4015046e84 else 0xd9c48b4263c12d007f1b354186c0be40000080981c124780000088c0931294803e84d050bf801180da4c33c01142c980a7406cd28680001ec8025214c798b7c61758df04254607007b18709287987e85be12c71e2b00419800004204d4403a4d850162097201d3c0805c0fc05c12c69e3a4120c2845e9c407740430579553544) else (if page < 31 then 0x36c080c095401380625a6340161c36cc3f812c417f8028d2c6de06403f002484689c21037881cf063940095218980200d88c67da78c0950318c64c032706000024410000cb0c00000000820c94c1a742590cd580734000002a4021820ec000006b837d8300000000b7d3298057007bc300000000364d27864c439cc2c5987452 else 0xc200000011c00000ae006c83))))) else 0
  | 8 => if page < 4 then (if page < 2 then (if page < 1 then 0x3263731fa428010a8600c9a8546ec2b199860d47203b0868069224041317aae80746400168d0036a002491987832c04608480a404290349984cc04832b2599c7124c62b68f871000ac0001f04ad8680100c000f802e60354c011830a3450d38cb583622d25506e01 else 0x4090001424ac80003d480007c50003f559000006e32f51d8034328308516900043a01a58f011803602c00c805c00803a3db006503c21778abc6cd3e22e491000447821f0221e716780b231f066d05411b30506312020390c9b11c48e0c201a84b5a7ea1812218b02) else (if page < 3 then 0x1690006204f8c3a2410098c5181e01e062800000000000000e002463000f82adb00000016b640274716307866c150f00021800007419548684000887000000091800040080000000000000ba40413a0c40c0000001c027600000003c2a548000d438a10000000440 else 0x1180bd242a9a4cf04000761b108c82b030003e3800021286080000009803222a00000e04667bc000000004af310cf8460138980019982820003700800f8f8e0390a1881d26200f09d04000)) else 0
  | 9 => if page < 2 then (if page < 1 then 0x27a152304111555600db3180d80d9850cd82180c2004455004838c930a021004353c0090092004420021271000418162614c0480000241508009101330000832147020f461400018654a00369c1040c3 else 0x5380040000000c8) else 0
  | 10 => if page < 1 then 0x0 else 0
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
  (slot / 64,slot % 64)

def s45 : Switch := ⟨16,0xffff0000,0xffff00000000⟩
theorem s45_ok : s45.Valid := by unfold Switch.Valid; decide +kernel
def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s35 : Switch := ⟨24,0xff00ff00,0xff00ff00000000⟩
theorem s35_ok : s35.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s45]
  | 2 => [s34]
  | 3 => [s34, s35]
  | 4 => [s35, s34]
  | 5 => [s35]
  | 6 => [s12]
  | 7 => [s12, s45]
  | 8 => [s12, s34]
  | 9 => [s12, s34, s35]
  | 10 => [s12, s35, s34]
  | 11 => [s12, s35]
  | 12 => [s01]
  | 13 => [s01, s45]
  | 14 => [s01, s34]
  | 15 => [s01, s34, s35]
  | 16 => [s01, s35, s34]
  | 17 => [s01, s35]
  | 18 => [s01, s02]
  | 19 => [s01, s02, s45]
  | 20 => [s01, s02, s34]
  | 21 => [s01, s02, s34, s35]
  | 22 => [s01, s02, s35, s34]
  | 23 => [s01, s02, s35]
  | 24 => [s02, s01]
  | 25 => [s02, s01, s45]
  | 26 => [s02, s01, s34]
  | 27 => [s02, s01, s34, s35]
  | 28 => [s02, s01, s35, s34]
  | 29 => [s02, s01, s35]
  | 30 => [s02]
  | 31 => [s02, s45]
  | 32 => [s02, s34]
  | 33 => [s02, s34, s35]
  | 34 => [s02, s35, s34]
  | 35 => [s02, s35]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s45_ok, s34_ok, s35_ok, s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def goalColumns : Nat := 0xfefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000fefefe80fe808000
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0x1010101010101010 0xf34b24714304 3 4
    pinBase [0x0,0x1010101010101010,0x0,0x0,0x1010101010101010,0x1000100010001000,0x1010000010100000,0x1010101000000000,0x1010101010101010,0x1010101010101010,0x0,0x10001000100010,0x101000001010,0x10101010] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x1111111111111111 0x420c41461c824a2cc34e3c 4 5
    pinBase [0x0,0x1111111111111111,0x0,0x0,0x1010101010101010,0x1100110011001100,0x1111000011110000,0x1111111100000000,0x1111111111111111,0x1111111111111111,0x101010101010101,0x11001100110011,0x111100001111,0x11111111] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x505050505050505 0x220a41261a822a2ac32e3a 4 5
    pinBase [0x0,0x505050505050505,0x0,0x404040404040404,0x0,0x500050005000500,0x505000005050000,0x505050500000000,0x505050505050505,0x101010101010101,0x505050505050505,0x5000500050005,0x50500000505,0x5050505] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0x303030303030303 0x1209411619821a29c31e39 4 5
    pinBase [0x0,0x303030303030303,0x202020202020202,0x0,0x0,0x300030003000300,0x303000003030000,0x303030300000000,0x101010101010101,0x303030303030303,0x303030303030303,0x3000300030003,0x30300000303,0x3030303] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf000f000f000f0 0x1d79f71969b6155975114934 4 5
    pinBase [0x0,0xf000f000f000f0,0xa000a000a000a0,0xc000c000c000c0,0xf000f000f000f0,0x0,0xf0000000f00000,0xf000f000000000,0x50005000500050,0x30003000300030,0x0,0xf000f000f000f0,0xf0000000f0,0xf000f0] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf0f00000f0f0 0x1cf9ef18e9ae14d96d10c92c 4 5
    pinBase [0x0,0xf0f00000f0f0,0xa0a00000a0a0,0xc0c00000c0c0,0xf0f00000f0f0,0xf0000000f000,0x0,0xf0f000000000,0x505000005050,0x303000003030,0x0,0xf0000000f0,0xf0f00000f0f0,0xf0f0] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xcc00cc00cc00cc 0x1d79f71969b60d38f30928b2 4 5
    pinBase [0x0,0xcc00cc00cc00cc,0x88008800880088,0xcc00cc00cc00cc,0xc000c000c000c0,0x0,0xcc000000cc0000,0xcc00cc00000000,0x44004400440044,0x0,0xc000c000c000c,0xcc00cc00cc00cc,0xcc000000cc,0xcc00cc] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xcccc0000cccc 0x1cf9ef18e9ae0cb8eb08a8aa 4 5
    pinBase [0x0,0xcccc0000cccc,0x888800008888,0xcccc0000cccc,0xc0c00000c0c0,0xcc000000cc00,0x0,0xcccc00000000,0x444400004444,0x0,0xc0c00000c0c,0xcc000000cc,0xcccc0000cccc,0xcccc] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xcccccccc 0x1cf5df18e59e0cb4db08a49a 4 5
    pinBase [0x0,0xcccccccc,0x88888888,0xcccccccc,0xc0c0c0c0,0xcc00cc00,0xcccc0000,0x0,0x44444444,0x0,0xc0c0c0c,0xcc00cc,0xcccc,0xcccccccc] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xaa00aa00aa00aa 0x1d79f71559750d38f3051871 4 5
    pinBase [0x0,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0x88008800880088,0xa000a000a000a0,0x0,0xaa000000aa0000,0xaa00aa00000000,0x0,0x22002200220022,0xa000a000a000a,0xaa00aa00aa00aa,0xaa000000aa,0xaa00aa] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xaaaa0000aaaa 0x1cf9ef14d96d0cb8eb049869 4 5
    pinBase [0x0,0xaaaa0000aaaa,0xaaaa0000aaaa,0x888800008888,0xa0a00000a0a0,0xaa000000aa00,0x0,0xaaaa00000000,0x0,0x222200002222,0xa0a00000a0a,0xaa000000aa,0xaaaa0000aaaa,0xaaaa] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xff00ff00000000 0xc31cb3d35db78218a39259a7 4 6
    pinBase [0x0,0xff00ff00000000,0xaa00aa00000000,0xcc00cc00000000,0xf000f000000000,0x0,0xff000000000000,0xff00ff00000000,0x55005500000000,0x33003300000000,0xf000f00000000,0xff00ff00000000,0xff00000000,0x0] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut16 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xff000000ff0000 0xc31cb3d35db7411493515597 4 6
    pinBase [0x0,0xff000000ff0000,0xaa000000aa0000,0xcc000000cc0000,0xf0000000f00000,0x0,0xff000000ff0000,0xff000000000000,0x55000000550000,0x33000000330000,0xf0000000f0000,0xff000000ff0000,0x0,0xff0000] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut17 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xffff00000000 0xa29aabb2dbaf8218a39259a7 4 6
    pinBase [0x0,0xffff00000000,0xaaaa00000000,0xcccc00000000,0xf0f000000000,0xff0000000000,0x0,0xffff00000000,0x555500000000,0x333300000000,0xf0f00000000,0xff00000000,0xffff00000000,0x0] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut18 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xffff0000 0x61969b71d79f411493515597 4 6
    pinBase [0x0,0xffff0000,0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000,0xffff0000,0x0,0x55550000,0x33330000,0xf0f0000,0xff0000,0x0,0xffff0000] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut19 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xff000000ff00 0xa29aabb2dbaf20928b30d38f 4 6
    pinBase [0x0,0xff000000ff00,0xaa000000aa00,0xcc000000cc00,0xf0000000f000,0xff000000ff00,0x0,0xff0000000000,0x550000005500,0x330000003300,0xf0000000f00,0x0,0xff000000ff00,0xff00] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xff00ff00 0x61969b71d79f20928b30d38f 4 6
    pinBase [0x0,0xff00ff00,0xaa00aa00,0xcc00cc00,0xf000f000,0xff00ff00,0xff000000,0x0,0x55005500,0x33003300,0xf000f00,0x0,0xff00,0xff00ff00] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xc0c0c0c0c0c0c0c0 0xffedf6bee9e67de5d63ce1c6 4 7
    pinBase [0x0,0xc0c0c0c0c0c0c0c0,0x8080808080808080,0xc0c0c0c0c0c0c0c0,0xc0c0c0c0c0c0c0c0,0xc000c000c000c000,0xc0c00000c0c00000,0xc0c0c0c000000000,0x4040404040404040,0x0,0x0,0xc000c000c000c0,0xc0c00000c0c0,0xc0c0c0c0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut22 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xa0a0a0a0a0a0a0a0 0xffddf5bed9e57dd5d53cd1c5 4 7
    pinBase [0x0,0xa0a0a0a0a0a0a0a0,0xa0a0a0a0a0a0a0a0,0x8080808080808080,0xa0a0a0a0a0a0a0a0,0xa000a000a000a000,0xa0a00000a0a00000,0xa0a0a0a000000000,0x0,0x2020202020202020,0x0,0xa000a000a000a0,0xa0a00000a0a0,0xa0a0a0a0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut23 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x8888888888888888 0xffbdf3beb9e37db5d33cb1c3 4 7
    pinBase [0x0,0x8888888888888888,0x8888888888888888,0x8888888888888888,0x8080808080808080,0x8800880088008800,0x8888000088880000,0x8888888800000000,0x0,0x0,0x808080808080808,0x88008800880088,0x888800008888,0x88888888] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0x5555555555555555 0x220a41261a822a2ac32e3a10630e51671e926b2ed36f3e 5 6
    pinBase [0x0,0x5555555555555555,0x0,0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000,0x5555555555555555,0x1111111111111111,0x505050505050505,0x55005500550055,0x555500005555,0x55555555] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut25 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0x3333333333333333 0x1209411619821a29c31e3910530d51571d925b2dd35f3d 5 6
    pinBase [0x0,0x3333333333333333,0x2222222222222222,0x0,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000,0x1111111111111111,0x3333333333333333,0x303030303030303,0x33003300330033,0x333300003333,0x33333333] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut26 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0xf0f0f0f0f0f0f0f 0x1209411619821a29c31e3908328b49369b8a3aabcb3ebb 5 6
    pinBase [0x0,0xf0f0f0f0f0f0f0f,0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0x0,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000,0x505050505050505,0x303030303030303,0xf0f0f0f0f0f0f0f,0xf000f000f000f,0xf0f00000f0f,0xf0f0f0f] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut27 : CutCertificate target :=
  makeCutCertificate target Minor12.target 0x55555555aaaaaaaa 0x9aedbe1cf5df92cd3c14d55d8aacba0cb4db828c38049459 5 9
    pinBase [0x0,0x55555555aaaaaaaa,0xaaaaaaaa,0x4444444488888888,0x50505050a0a0a0a0,0x55005500aa00aa00,0x55550000aaaa0000,0x5555555500000000,0x5555555500000000,0x1111111122222222,0x50505050a0a0a0a,0x55005500aa00aa,0x55550000aaaa,0xaaaaaaaa] Minor12.raw Minor12.nonzero (@Minor12.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut30 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0x9999999999999999 0x310720b30f41351761b71f823927a2bb2fc33d37e3bf3f 5 9
    pinBase [0x0,0x9999999999999999,0x8888888888888888,0x8888888888888888,0x9090909090909090,0x9900990099009900,0x9999000099990000,0x9999999900000000,0x1111111111111111,0x1111111111111111,0x909090909090909,0x99009900990099,0x999900009999,0x99999999] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut31 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xa5a5a5a5a5a5a5a5 0x508720d28f41549761d69f8258a7a2daafc35cb7e3debf 5 9
    pinBase [0x0,0xa5a5a5a5a5a5a5a5,0xa0a0a0a0a0a0a0a0,0x8484848484848484,0xa0a0a0a0a0a0a0a0,0xa500a500a500a500,0xa5a50000a5a50000,0xa5a5a5a500000000,0x505050505050505,0x2121212121212121,0x505050505050505,0xa500a500a500a5,0xa5a50000a5a5,0xa5a5a5a5] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut34 : CutCertificate target :=
  makeCutCertificate target Minor12.target 0x5555aaaa5555aaaa 0x59edbe1cf9ef51cd3c14d96d49acba0cb8eb418c38049869 5 9
    pinBase [0x0,0x5555aaaa5555aaaa,0xaaaa0000aaaa,0x4444888844448888,0x5050a0a05050a0a0,0x5500aa005500aa00,0x5555000055550000,0x5555aaaa00000000,0x5555000055550000,0x1111222211112222,0x5050a0a05050a0a,0x5500aa005500aa,0xaaaa0000aaaa,0x5555aaaa] Minor12.raw Minor12.nonzero (@Minor12.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut37 : CutCertificate target :=
  makeCutCertificate target Minor12.target 0x55aa55aa55aa55aa 0x39ebbe1d79f731cb3c15597529aaba0d38f3218a38051871 5 9
    pinBase [0x0,0x55aa55aa55aa55aa,0xaa00aa00aa00aa,0x4488448844884488,0x50a050a050a050a0,0x5500550055005500,0x55aa000055aa0000,0x55aa55aa00000000,0x5500550055005500,0x1122112211221122,0x50a050a050a050a,0xaa00aa00aa00aa,0x55aa000055aa,0x55aa55aa] Minor12.raw Minor12.nonzero (@Minor12.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut38 : CutCertificate target :=
  makeCutCertificate target Minor12.target 0x33cc33cc33cc33cc 0x35db7d1d79f731cb3c1969b6259a790d38f3218a380928b2 5 9
    pinBase [0x0,0x33cc33cc33cc33cc,0x2288228822882288,0xcc00cc00cc00cc,0x30c030c030c030c0,0x3300330033003300,0x33cc000033cc0000,0x33cc33cc00000000,0x1144114411441144,0x3300330033003300,0x30c030c030c030c,0xcc00cc00cc00cc,0x33cc000033cc,0x33cc33cc] Minor12.raw Minor12.nonzero (@Minor12.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut40 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xff00ff00ff00ff 0x108300518710928b20d38f31149341559751969b61d79f7 5 9
    pinBase [0x0,0xff00ff00ff00ff,0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0x0,0xff000000ff0000,0xff00ff00000000,0x55005500550055,0x33003300330033,0xf000f000f000f,0xff00ff00ff00ff,0xff000000ff,0xff00ff] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut42 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xffffffff 0x841804945908a49a0cb4db10c51c14d55d18e59e1cf5df 5 9
    pinBase [0x0,0xffffffff,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0x0,0x55555555,0x33333333,0xf0f0f0f,0xff00ff,0xffff,0xffffffff] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut48 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0xaa55aa55aa55aa55 0xc39cbbd3ddbf8298ab92d9af41949b51d59f00908b10d18f 5 8
    pinBase [0x0,0xaa55aa55aa55aa55,0xaa00aa00aa00aa00,0x8844884488448844,0xa050a050a050a050,0xaa00aa00aa00aa00,0xaa550000aa550000,0xaa55aa5500000000,0x55005500550055,0x2211221122112211,0xa050a050a050a05,0x55005500550055,0xaa550000aa55,0xaa55aa55] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut49 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0xaaaa5555aaaa5555 0xa39abbb3dbbf8318b39359b721929b31d39f011093115197 5 8
    pinBase [0x0,0xaaaa5555aaaa5555,0xaaaa0000aaaa0000,0x8888444488884444,0xa0a05050a0a05050,0xaa005500aa005500,0xaaaa0000aaaa0000,0xaaaa555500000000,0x555500005555,0x2222111122221111,0xa0a05050a0a0505,0xaa005500aa0055,0x555500005555,0xaaaa5555] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut50 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0xaaaaaaaa55555555 0x6396bb73d7bf4314b35355b72292ab32d3af0210a31251a7 5 8
    pinBase [0x0,0xaaaaaaaa55555555,0xaaaaaaaa00000000,0x8888888844444444,0xa0a0a0a050505050,0xaa00aa0055005500,0xaaaa000055550000,0xaaaaaaaa00000000,0x55555555,0x2222222211111111,0xa0a0a0a05050505,0xaa00aa00550055,0xaaaa00005555,0x55555555] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut67 : CutCertificate target :=
  makeCutCertificate target Minor11.target 0xffffffff00000000 0x9e69648e2860beeb6caeaa68df6d74cf2c70ffef7cefae78 5 7
    pinBase [0x0,0xffffffff00000000,0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000,0xffffffff00000000,0x5555555500000000,0x3333333300000000,0xf0f0f0f00000000,0xff00ff00000000,0xffff00000000,0x0] Minor11.raw Minor11.nonzero (@Minor11.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut68 : CutCertificate target :=
  makeCutCertificate target Minor11.target 0xffff0000ffff0000 0x5d65544d24507de75c6da658df6d74cf2c70ffef7cefae78 5 7
    pinBase [0x0,0xffff0000ffff0000,0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff0000ffff0000,0xffff000000000000,0x5555000055550000,0x3333000033330000,0xf0f00000f0f0000,0xff000000ff0000,0x0,0xffff0000] Minor11.raw Minor11.nonzero (@Minor11.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut69 : CutCertificate target :=
  makeCutCertificate target Minor11.target 0xff00ff00ff00ff00 0x3ce34c2ca2487de75c6da658beeb6caeaa68ffef7cefae78 5 7
    pinBase [0x0,0xff00ff00ff00ff00,0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff00ff00ff00ff00,0xff000000ff000000,0xff00ff0000000000,0x5500550055005500,0x3300330033003300,0xf000f000f000f00,0x0,0xff000000ff00,0xff00ff00] Minor11.raw Minor11.nonzero (@Minor11.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut76 : CutCertificate target :=
  makeCutCertificate target Minor5.target 0xf0f0f0f0f0f0f0f0 0xf34b24714304f75b65755345fb6ba6796386ff7be77d73c7 5 8
    pinBase [0x0,0xf0f0f0f0f0f0f0f0,0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000,0x5050505050505050,0x3030303030303030,0x0,0xf000f000f000f0,0xf0f00000f0f0,0xf0f0f0f0] Minor5.raw Minor5.nonzero (@Minor5.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut77 : CutCertificate target :=
  makeCutCertificate target Minor5.target 0xcccccccccccccccc 0xeb2aa2692282ef3ae36d32c3fb6ba6796386ff7be77d73c7 5 8
    pinBase [0x0,0xcccccccccccccccc,0x8888888888888888,0xcccccccccccccccc,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000,0x4444444444444444,0x0,0xc0c0c0c0c0c0c0c,0xcc00cc00cc00cc,0xcccc0000cccc,0xcccccccc] Minor5.raw Minor5.nonzero (@Minor5.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut78 : CutCertificate target :=
  makeCutCertificate target Minor5.target 0xaaaaaaaaaaaaaaaa 0xe71a61651241ef3ae36d32c3f75b65755345ff7be77d73c7 5 8
    pinBase [0x0,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0x8888888888888888,0xa0a0a0a0a0a0a0a0,0xaa00aa00aa00aa00,0xaaaa0000aaaa0000,0xaaaaaaaa00000000,0x0,0x2222222222222222,0xa0a0a0a0a0a0a0a,0xaa00aa00aa00aa,0xaaaa0000aaaa,0xaaaaaaaa] Minor5.raw Minor5.nonzero (@Minor5.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 7 => cut6
  | 8 => cut7
  | 10 => cut9
  | 11 => cut10
  | 12 => cut11
  | 13 => cut12
  | 14 => cut13
  | 16 => cut15
  | 17 => cut16
  | 18 => cut17
  | 19 => cut18
  | 20 => cut19
  | 21 => cut20
  | 22 => cut21
  | 23 => cut22
  | 24 => cut23
  | 25 => cut24
  | 26 => cut25
  | 27 => cut26
  | 28 => cut27
  | 31 => cut30
  | 32 => cut31
  | 35 => cut34
  | 38 => cut37
  | 39 => cut38
  | 41 => cut40
  | 43 => cut42
  | 49 => cut48
  | 50 => cut49
  | 51 => cut50
  | 68 => cut67
  | 69 => cut68
  | 70 => cut69
  | 77 => cut76
  | 78 => cut77
  | 79 => cut78
  | _ => cut0

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x0 else 0
  | 4 => if page < 1 then 0xb1a387000000000142c00b000000000000000004001 else 0
  | 5 => if page < 5 then (if page < 2 then (if page < 1 then 0x14143070e58204082820708103870e28b160e105040e1c38a0e2840408202040810204081020608100070e20207082038708102040e1c387 else 0x201c387081c3800e0030414286870e003870e1c58400003041410504081430a0a140050a2828408102040810204081020008103072c1c30a) else (if page < 3 then 0xe1c38a2e000160e582881414b181010286101cb0810183880e1040b102850a142868d001c380142c204082c58416000000e28590182880b else (if page < 4 then 0x142c3870e2c80b282858a1450508102c50b0e2c38e142840a142850a000050414142051c2c68d1610200001c80700000000000200001c807 else 0x14005870e2850a142858a143450d1a2c5800000387001c40a1020400001c58b002c58a))) else 0
  | 6 => if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x2040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040811 else 0x204081020408102054a992c408162040019285001100408002400c91266481032648162c58b102c00c902040810204081020408102040810) else (if page < 3 then 0x204081020549953258b10204081620548102000a800058810206ca9b2a64d992c408192a64c992c58810204081620408162658b162040810 else 0x3054c182c58c992664c992a58c993264c902040810204081020408102040a963240810204080022408162658b152c4081020408102040810)) else (if page < 6 then (if page < 5 then 0x204081020408102054b162e00b162c408902000a1020400100040b972e448932c54a1932648102040815324081000548903250c122654c18 else 0x50a00284c01428408102040810204081020408102a58b802c588102000a9028589952c58b162c00b9a004c000000081a34000002040810) else (if page < 7 then 0x2244a1122448942244891224489120408142c4ca142858a122458a962658a142c50817284ca142860a142448a182a609982800a142600880 else 0x2448a122444893244080020408000040810204081020408102040810204091020408102040c903248910204081920408102c5c0163240811))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x50a002800a1224400002800a1224400122440000000091220000002000c99244801900649123264d190064c9900408162c40c932640800 else 0x3600a9028448112c000163664c9b3264a992a64c993264c992e5cc000000d962c58c800064c962c58b16000081020408002e00c800044011) else (if page < 11 then 0x3264c993264c802040c99204081020400193264c9932408100068810204089020400000000d153264b803458b162c44b1626589962c50d80 else 0x2040b1600000190040810204000032448942200c992200c800058b160058b002c5c0162c58b162c58b162c580003264c800064b193264c99)) else (if page < 14 then (if page < 13 then 0x20000192040c993458b162c00800006481900000002c58b162c58b8000448162c00816220001620408102040810204081400500102000810 else 0x640192c58b1900000162040816000000000000000000000000000000000190000c80000001932640000000000000000000000000000010) else (if page < 15 then 0x32640003264c003264c902040c8034000193464d002c6881020580000000d000000b160058b000058b000000d972e580000000d80 else (if page < 16 then 0x5000000000000040810000000000000000000b162e600000058b173260c80006401900000002c00c8000580000000000005cb000000000 else 0x2c000102044894))))) else 0
  | 7 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x58b005258b162c5cb963058c180058000308cb164c98b162c58b162c58b162c00b162c58b162c5800030a4b984cccb162c58b162d11916 else (if page < 2 then 0x2c60b962c58b002c00c172c58c162c58b162c58b162c5cb962c58b162c58b160000016305cb983058b162c60b162c5cc186258c162c58b16 else 0x31100183060c183060c188800c440000c44880148000ccb165258b166658b162c58b172c58b162c58b165258b80011000000000440058b00)) else (if page < 5 then (if page < 4 then 0x110b002d100162c58b4401100292c5e2182e00c172e5cb972e5c01700ac0172e5cb975600b972e5cb972e00000005cbc488600003110018 else 0x2e5d496005c0172c5cb172c58000000000000000000000b973062244000234600000005601480000000056014805601480000002b00a4000) else (if page < 6 then 0x58b162c5cb970058b173000b162c5cb162e58b162c58b162c000002c600162c58b182c60b162c58b162c580162e580292e00ba92c5cb96 else 0x58b172c00b162c58b162c58b962c58b262c58b162c58b182c000162e00b178c58b162c58b162c58b1600a4b1600a4b162c58b162c58016))) else (if page < 10 then (if page < 8 then 0x58b003000029006002930a4c1800a4c1830a40162c00b980000b162e58c2600000000058b9600014960000b295258b162c014962ca4b00 else (if page < 9 then 0x2c58b002c5cb973000c003060b1600000002c6000000000162e58b182c58b162c00c002c00b002c5cb802c58c170000b162c58c163060b00 else 0x2c58b000058b172c000292c00b2952000162e00b172e5c0003058b172e000170060bc6305cb972e5cb800000b802e00b972e580162e60000)) else (if page < 12 then (if page < 11 then 0x2c58b162c58b16005cc168b140462e5cb9700623003060c4630600008c02300005c0002c58b800058b160058b172e60b000000b000000016 else 0x162e5cb972e5cc172e5cc172e5cb972e5cb972e5cc183060c1830580002c600162c00c162c58b162c58b16) else (if page < 13 then 0x2e000160058b802c5c0162c5c0162c60b002c58b162c58b162c58b182c58b182c58b972c58b162c58b162c58b162c58b162c58b160000000 else 0xb172e5c0162e600162c580163000b1600000162c00b982c60c182c58b162c58b162c58b162c580172c58b162c58b162c5cb80)))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x13e680013c0009e0001f9f3c00000026809a0274d413e6a09e026cd00027009e027809c7e6a04000fa6013549f3e980270135020527ce33 else 0x274f013a7ce) else 0
  | 9 => if page < 1 then 0x14a6520130052814ab else 0
  | 10 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 7 i

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

theorem root : pool 10 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 7 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 27 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 27 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x224 : span (checked 5) 73 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 297 0 = true :=
  (@span_join (checked 5) 112 0 185 chunk5x0 (@span_join (checked 5) 112 112 73 chunk5x112 chunk5x224))

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
theorem chunk6x448 : span (checked 6) 112 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x560 : span (checked 6) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x672 : span (checked 6) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x784 : span (checked 6) 112 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x896 : span (checked 6) 112 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1008 : span (checked 6) 53 1008 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1061 0 = true :=
  (@span_join (checked 6) 560 0 501 (@span_join (checked 6) 224 0 336 (@span_join (checked 6) 112 0 112 chunk6x0 chunk6x112) (@span_join (checked 6) 112 224 224 chunk6x224 (@span_join (checked 6) 112 336 112 chunk6x336 chunk6x448))) (@span_join (checked 6) 224 560 277 (@span_join (checked 6) 112 560 112 chunk6x560 chunk6x672) (@span_join (checked 6) 112 784 165 chunk6x784 (@span_join (checked 6) 112 896 53 chunk6x896 chunk6x1008))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x112 : span (checked 7) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x224 : span (checked 7) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x336 : span (checked 7) 112 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x448 : span (checked 7) 112 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x560 : span (checked 7) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x672 : span (checked 7) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x784 : span (checked 7) 110 784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 894 0 = true :=
  (@span_join (checked 7) 448 0 446 (@span_join (checked 7) 224 0 224 (@span_join (checked 7) 112 0 112 chunk7x0 chunk7x112) (@span_join (checked 7) 112 224 112 chunk7x224 chunk7x336)) (@span_join (checked 7) 224 448 222 (@span_join (checked 7) 112 448 112 chunk7x448 chunk7x560) (@span_join (checked 7) 112 672 110 chunk7x672 chunk7x784)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 72 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 72 0 = true :=
  chunk8x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x0 : span (checked 9) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer9 : span (checked 9) 10 0 = true :=
  chunk9x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk10x0 : span (checked 10) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer10 : span (checked 10) 1 0 = true :=
  chunk10x0
theorem verified : ∀ k ≤ 10, ∀ i < counts k, checked k i = true := by
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
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer10 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 11 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 10
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    10 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full



namespace SignedFrontier.CliqueLink
def target := SmallCert.Full.target
def raw := SmallCert.Full.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 11 ≤ p.length := by
  have inside : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial target 0 {target} Cone.done inside
  have start : available initial = insert 0 SmallCert.Full.raw.toFinset := by decide +kernel
  rw [start] at access
  have bounded := SmallCert.Full.lower run access
  omega
end SignedFrontier.CliqueLink

namespace TableLink
open SignedFrontier

def assignment (r : Fin 64) (v : Fin 6) : Bool := r.val.testBit v.val

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
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 11 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 11 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12360_aux

open PEqualNP.Outside.L_meta_12360_aux

theorem PEqualNP.Outside.L_meta_12360 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124160 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124160 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
