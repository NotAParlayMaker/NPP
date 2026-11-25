import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12244_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4269834240 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [0,1]⟩,
  ⟨.and, [2,6]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.or, [2,8]⟩,
  ⟨.and, [3,4]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.and, [5,11]⟩,
  ⟨.or, [10,12]⟩,
  ⟨.and, [5,10]⟩,
  ⟨.and, [7,13]⟩,
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

namespace SignedFrontier.Packed

-- These packed integers only propose a negative input row. Every proposed
-- obstruction is tested on the original signals before a successor is skipped.
structure Columns where
  w : W
  pos : Nat
  neg : Nat

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 54) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 54) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 3456 := by omega
  have val : fullLanes = 2^3456-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 54) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 54) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 54) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 54) (xs : List Columns)
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
    (length : rows.length = 54) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 54) (bounds : ∀ r ∈ rows, r < 64)
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

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x8eee8eee8eee8eee
def negative : List Nat := [0, 4, 8, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨9,13,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨5,13,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

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

end SignedFrontier.SmallCert.Minor0

namespace SignedFrontier.SmallCert.Minor1

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfee8fee8fee8fee8
def negative : List Nat := [0, 1, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

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

end SignedFrontier.SmallCert.Minor1

namespace SignedFrontier.SmallCert.Minor2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x80fe80fe80fe80fe
def negative : List Nat := [0, 8, 9, 10, 11, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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

end SignedFrontier.SmallCert.Minor2

namespace SignedFrontier.SmallCert.Minor3

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xe8fefefee8fefefe
def negative : List Nat := [0, 8, 16, 24, 25, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨17,25,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨9,25,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 4 then (if page < 2 then (if page < 1 then 0x5f0000005f00000055aaaaaa55aaaaaa55550000555500005500550055005500550000005500000050505050505050503f3f00003f3f00003f00ff003f00ff003f003f003f003f003f000f003f000f003f0000003f0000003c3c3c3c3c3c3c3c330033003300330033000000330000002aaaaaaa2aaaaaaa2a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a2a0a2a0a2a0a2a0a2a0a0a0a2a0a0a0a22222222222222221f001f001f001f001f0000001f0000000ff0f0f00ff0f0f00f0ff0f00f0ff0f00f0f0f000f0f0f000f0f00000f0f00000f0a0f0a0f0a0f0a0f0a0a0a0f0a0a0a0f00ff000f00ff000f000f000f000f000f0000000f0000000e0e0e0e0e0e0e0e0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a000a000a000a000a0000000a000000080808080808080803000300030003000300000003000000020202020202020200ffff0000ffff0000ff000000ff000000fefefe00fefefe00eeeeee00eeeeee00aaffaa00aaffaa00aaaaaa00aaaaaa0088888800888888000a0a0a000a0a0a0000ffee0000ffee0000ffaa0000ffaa0000ff880000ff880000ff0a0000ff0a0000ff000000ff000000fefe0000fefe0000eeee0000eeee0000aaaa0000aaaa0000aa000000aa00000088880000888800003f0000003f0000000f0000000f0000000a0a00000a0a000000aa000000aa0000000000000000 else 0xeaaaaaaaeaaaaaaaccfefefeccfefefeccfcfcfcccfcfcfcccfcccfcccfcccfccceeeeeecceeeeeeccdcdcdcccdcdcdcccccfcfcccccfcfcccccfcccccccfccccccceeeecccceeeecccccccccccccccccccc4444cccc4444cc444444cc444444cc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0cc0c0c0c0c0c0c0c0bf00bf00bf00bf00bf000000bf000000afaaafaaafaaafaaafaaaaaaafaaaaaaaf00af00af00af00af000000af000000aeaeaeaeaeaeaeaeaafafafaaafafafaaaeeeeeeaaeeeeeeaaaaffaaaaaaffaaaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000aaaa0000aa8aaa8aaa8aaa8aaa8a8a8aaa8a8a8aaa88aa88aa88aa88aa888888aa888888aa2aaa2aaa2aaa2aaa2a2a2aaa2a2a2aaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa02aa02aa02aa02aa020202aa020202aa00ff00aa00ff00aa00aaaaaa00aaaaaa00aa00aa00aa00aa000000aa000000a8aaaaaaa8aaaaaaa8a8a8a8a8a8a8a8a0f0f0f0a0f0f0f0a0a0a0a0a0a0a0a08a8a8a8a8a8a8a8a88aaaaaa88aaaaaa8888ff888888ff888888aaaa8888aaaa88888888888888888800ff008800ff008800880088008800880000008800000080808080808080807f007f007f007f007f0000007f0000005f005f005f005f00) else (if page < 3 then 0xff88ff88ff88ff88ff888888ff888888ff808080ff808080ff0fff00ff0fff00ff0f0000ff0f0000ff0aff0aff0aff0aff0a0a0aff0a0a0aff080808ff080808ff00ffaaff00ffaaff00ff00ff00ff00ff00ee00ff00ee00ff00c000ff00c000ff00af00ff00af00ff00aaaaff00aaaaff00aa00ff00aa00ff00a800ff00a800ff008888ff008888ff008800ff008800ff008000ff008000ff005500ff005500ff003f00ff003f00ff000f00ff000f00ff000a00ff000a00ff000800ff000800ff000300ff000300ff000100ff000100ff000000ff000000fefefefefefefefefe00fe00fe00fe00fe000000fe000000fcfcfcfcfcfcfcfcfafafafafafafafaf8fafafaf8fafafaf8f8fafaf8f8fafaf8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f1f0f0f0f1f0f0f0f0fefefef0fefefef0fafafaf0fafafaf0faf0faf0faf0faf0f8f8f8f0f8f8f8f0f2f2f2f0f2f2f2f0f0fff0f0f0fff0f0f0fefef0f0fefef0f0fafaf0f0fafaf0f0faf0f0f0faf0f0f0f8f8f0f0f8f8f0f0f2f2f0f0f2f2f0f0f0faf0f0f0faf0f0f0f0f0f0f0f0f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeeeeeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaee00ee00ee00ee00ee000000ee000000ecfcfcfcecfcfcfcececececececececeaeeeeeeeaeeeeeeeaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaa else 0xffffffaaffffffaaffffff00ffffff00fffff0f0fffff0f0ffffccccffffccccffffc0c0ffffc0c0ffffaaaaffffaaaaffffa8a8ffffa8a8ffff88aaffff88aaffff8888ffff8888ffff8800ffff8800ffff8080ffff8080ffff0808ffff0808ffff00f0ffff00f0ffff00eeffff00eeffff00aaffff00aaffff0088ffff0088ffff000affff000affff0000ffff0000fff0fff0fff0fff0fff0f0f0fff0f0f0ffeeffeeffeeffeeffeeeeeeffeeeeeeffccccccffccccccffc0c0c0ffc0c0c0ffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa8a8a8ffa8a8a8)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xa5a183a5a182c5a181b4a181a5a181a5a180a5a17fa18135a1352f7d69217d5621a16f65a16535a1652a8565217e65217d65217a6521 else 0
  | 3 => if page < 3 then (if page < 1 then 0xa58e1d0b8469590d4abc6a55d352ad1a9564d4ab06a557352ab1a9554d4aa86a54f34524b22919942711a1378d09b4604d4d426a9a1351d29a0e94c4d4a606c52f35a179a94bcc6a5e6a52e352969a84ae34a5237d228be90a5f484ad24234d21194908cfc74c642653c1231f0898ec44c761e6a1350be90840300e017c700bd3805c1c02c0e015e700ae380569c02a0e014c700a5380511c01bce008270035380151c00a4e00287 else (if page < 2 then 0xa57c57252b9ab9295f55894ae4ac4a59851152cba88a96614054b409c2a58a4a252c52412fa291c95d148e4a58a47252c52292962910943026f0d8a1370d2d09b8684e4dc34b426a1a171350d09b9a869684d034ae2681a1372f852be910695f48434264421a5841d252c50d1260ec444e876224a1810a4509b8505f088283426e081a5a18100050c160028607001430180094794804a3c2402967c6014b3c300be9d180574e8c0296746014b38300a59b18052cd0c0296646018530300a59818052cb0c0296546015528300a59318059490c02c6486014b24300b19118052c88c0296406014b1e3 else 0xa5a1a08aa59d8a47a5a1712fd8b6a181b6a5a181a5a08465a5a18165a5987b65a5927765)) else 0
  | 4 => if page < 5 then (if page < 2 then (if page < 1 then 0x92dc8ee4371fb8edeb3f55fa8fd37e93f45f9efce7e6bf31f7cfb5bd9decaf637aebd73eaef557a9bd3de95f47770bb2797bcb5e58f2bf95bcabe497a33d0ae71737b9b5cd5e69b30f17f8bbc57728d943c59e24f0e786bc31e16f0a784bc11f7c7ae3d29cd4e01f else 0x401db528e1e946cf1435ca51a3d28c9e9460f4a2e7db163d28b1e944cf88247a5123e1089e9444e782363b1171d889e9440f4a1e7b70d3d2869efc30f3a14b970a5c9052e442977e147b10a3d5051e9428ec414e610a72b8538dc28e5e14ea5083b383bac81cf620e7a5073b3833ac418f4a0c7a50539b821ea80cf4a067a5023d2809e860714b3a3a5981d2c90e955cd4aac6a1378d29798ec44c013db009dd804e6c026360127b) else (if page < 3 then 0xa55b3be2bf3415dd76aeea557b52abb9cd5f94aae7a556752ab1e954cf4aa479751d60a89e9544f84a07a5503d0276a9538f4a967a54a3c524729520f148fcbe473d7239e951cf148bca5453d2a21e950cf026f6a137cd09bcf60dcf4a6e739373d29a9dc4d4e6e6a7a134cb89a6760bdd4a5eea52f39b97da949cf4a4a7a5243d2919df08b2f8455c1223dd911e9488f84427a5213c5909cc884f4a407a51f3d28f1e107794a3a7 else (if page < 4 then 0xa53b1d3529d0e8e94b074d4b30223a574112d2a8889a954044d4a78226a53b1134523853296481c74aea0e5a55f0731e8a839a96291c8014109900a181c80493be40352756014b3ab00a5985805bc94c035e496015925300a59298052c92c031b08e01a97e700d9b13806a571c036aa8e01b94a700dba538064529c031e94e01894a700c3a538061529c02fe94e017d4a700bca53805d529c02e694e016f4a700b2a538058d29c02aa94e014b48700a58a38052c49c029620e014b0e700a58638052c09c0295b8e014ada700a56c38052b59c0295a8e014ad0700a56738052b31c02958ce014ab87 else 0x286822b14b43403c2a551352c5289b0a9540d4b14a069d8a47c6a4523b296291d94b148e5a59d471d0b89bc685c4bf14ae25e6caa5221e4d2910e96808874266451c9a5211d2d0108e962874d4b403a3a5511d352a80e9a953074d4a783a6))) else 0
  | 5 => if page < 3 then (if page < 1 then 0xb7fd8feabf4bfa4fc57e27f0ff81fb77db3ed5f67fb37d8feb9f57fa9fd4bea3f50fa77d2fe91f47fa2fd0fe6ff2ff93fc97e47f22f90fc83e3df1df8e7c6be33f17f88fc37e15f08f83fc1be0bf03f817c07f3bb92dea3f39f637aabd2bd5fc6f72ff06bc29f4a7 else (if page < 2 then 0x3322bd290be2877d403bba51d7a88ef93077c783be3a1dd960efa9445f881afdb0a7eb853f1029f4a157a50a7c5053d9c29ec014f5f0a7a8853d1c29e4c14f220a78e853c5429f240fbb707beb83beb01ef4a0f7a5077ba83f57c1fc7a0fe3d0778a83dc281de140cf0a037edd29f1294f854a7a58a3d2a89e9540f148fca5473d2911e9484f4a3a7a5113d2851e941ce01b9f00dbf80647c0313e0187f00c2f805ffc02f3e0175f else 0x286837b3aefd7b1bedd2bf5e95f894afc2a57d2c53f1147d14a3ec451bd2a8de9545f4aa0f8a47ecea3ef511df4a8ef7137bb897fb288b74045bc422bd2915e9489f18457)) else 0
  | 6 => if page < 1 then 0x1b7fc4fd2fe2bea3f47f917c77e15f07fd2bc29f4a7 else 0
  | 7 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x30 else 0
  | 3 => if page < 1 then 0x400ec2b else 0
  | 4 => if page < 1 then 0x3b0ec2b0ac1b else 0
  | 5 => if page < 1 then 0x2b0ac1b else 0
  | 6 => if page < 1 then 0x1b else 0
  | 7 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 18
  | 3 => 137
  | 4 => 282
  | 5 => 154
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
  | 2 => 13
  | 3 => 88
  | 4 => 189
  | 5 => 126
  | 6 => 15
  | 7 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 46
  | 3 => 316
  | 4 => 682
  | 5 => 461
  | 6 => 54
  | 7 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 4
  | 7 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 9
  | 3 => 12
  | 4 => 13
  | 5 => 12
  | 6 => 8
  | 7 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x305081308e539847 else 0
  | 3 => if page < 2 then (if page < 1 then 0x4e901200405f0d358014d1440410c244b0400190c645d0401465452c31c31c038000610e0c710510524c2c0005046085 else 0x3880432040c00600c1182682240140116181) else 0
  | 4 => if page < 3 then (if page < 1 then 0xa00005081000508040860631104060470008040000834002100c00914180020600017000018200040071000903021400010002811024080 else (if page < 2 then 0x84016020248112393010004403003c09306341151c0820e1a68003040c0810e080211e0c004040c0802461a080068507000c7801400280 else 0x13018a02040420b36007000afdf0500384c728282911c5c301100ca1a1e08086c63410000600800c00f0906002061c049021010085)) else 0
  | 5 => if page < 2 then (if page < 1 then 0x621c0071a14002304449010645080e0419d00040030c08682002000b1410100120418000080001400286020040d000038006445040020003 else 0x8202087000008b005400880081c5852200b00320c1261435db10fa01810470294000840042200800c1068808a528002005020c14003) else 0
  | 6 => if page < 1 then 0xf89506170fc2602 else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x24006b2d800880d1c02028531e070c0113d830440400080e00a15060d000240000063028ac1628199cd0000459a9063000090a0 else 0
  | 3 => if page < 5 then (if page < 2 then (if page < 1 then 0x6588410b822a7f04413505c01280400502a40003000001a86802b61b60000001c82d07201da3800007800001ca0003c90000700000005db0303730b15184a056a76357888071037b8407f92084b209023b2f05864625f04f0100700280170866 else 0x1760001b80002e06904880003e64008702f43894400c10000007b07065403202870006101845960200804c01426000000005d00000000c00006687848563d86302b08383811e83b88328600d03622c11c22968577d81943574803f2792644) else (if page < 3 then 0x6203105680007b219057a3700007321568261100000000002560000005123462766b67075e012a7600004b01825f12661b45d93688001364d066a4603795900001717507c865a7304322f62192a60006f07404501407a16f60a01608202f7000 else (if page < 4 then 0x2186968302c61806e614a6868100000006025a64703a05b05d83717e92140000282b20000000000000566b00000002a00183190006e00002406c67a04025004e80e06383e73e06706a01f87704222ea55027025038b6403da6321d81f94925b6 else 0x7723967a37e05e60b078210845251043061244836a6714b83600003c01fa2d64205940003f00363d07908462545304422c02303303070004c22100005201960600001505f60006d00000000000003a71300001ea6c00f0260410))) else 0
  | 4 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0xd4bbc188800023ba5980004f080838c9f0c4328304191e20c701f92d59e4efd021c2bd8bd6ea058b07e56f45402581540b6200011ba51830e3f800018c0c20b897a12461a309d600040c80000008094440000c504a81ac00000002eb0fc1b8c7140603fc0e2cb21 else 0x2e32bd0100d3022b1f492ac6d209015dcb20c6a14424400006f020819c52ec0000002ae00000007a81e98000ea20000ba81430622702b40bf0c108c835806c2a224fb22489e492084c22861602410000000000ba90003a488c000036118d9fd40007843b016d0266) else (if page < 3 then 0x50800000000000000a800000008423ec900433000000019a80006901a81c806735902a019cd16410cc50986cca67a901800003700002c4000030040341c0f2022a1c0a781b40b4107cbf0000052038300019acb6a3a821e2080c9452020a526c5445c04480a20000 else (if page < 4 then 0x40900022427a00002141ec20001c4ade0ee10e024cc6080000007480b444a22c01b01c021500000000001dc0bcb06804de030000000232600c0301d905d92241460d81f40000ac800035c1772a60000202800031100019480009e27814500d000003c01828000bf4 else 0x8423c936015624546221cce806b8a9042d50f00003cc400000000007a4a8c00000022c11045e0474a2400000004391fc19403f15410000000bb011b41502124664658b182a20007c816c1b8300a57130c000000071a0000fe8eb28000000000000873800218c5c1))) else (if page < 8 then (if page < 6 then 0x81100004a0ac0160c12168e4707411b28bf4c9022820ad2a28d95ecc511b800000000000fc0fa045480008ec0000ed4541800bab2ba80597169413fb14c80000001e13bd8ca0190888871c8001263d827c17ec00008db0815640002600000f480001c88001520f76 else (if page < 7 then 0x2e81240bd30b80920e805a06916124359162d400203d00a6278660203e184c8db6e924c11d050841c1b013ced501e82e654a510029833c9740cf81f13b41c20900478054180c00053807edf605020f19e596810206d822621a04f100010c1868fc24200bc5c30620 else 0x64212c8c224d633120e90400e852c2500c10be90482b5a2c490255011020d11307393cc032289121042410104f95dda010000a3203805116a00007fb2880000380490a799bc47942b88000a00000459c2500000007020d061007303681f50e02e703589981be08e0)) else (if page < 9 then 0x6d236403d60c16702cc5ee01d873027dc8240004e00a0510000060b26593a024011409c50e0a0768003a50a83e0190b11934c6f64c81680742af02731f020a0868768c581b4c8840f0081d5c8a99198ac00d02d103903fe89100617291b81980e203880ec0937104 else (if page < 10 then 0x3732f258a80003b02000000a0063d3504000dd03641f8a1406400582d5d6660000000001900ec1144b601b621775280001c0000002801c538c0007f02040b804a02b82601c0c6a17c01390b00628000281a300b1472832c1460000549b8c0500f608490002060de0 else 0x1546eb040c000168ab118b813ec562c1400033c0e808607900040ac02960000d4000104200037109440a00b833920f07e40000001cc50c02f89fc40400565702f6c000351)))) else 0
  | 5 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x9212d57e85c79050007c82fb9300000006424a02606505145165806f10e28181141020001861764b40006908f08e78210591a07b03e14b60f80004970002104900009838106406d48806057927601840000105264d01a45904d22c1 else 0x1e20007e00003d84610002830008d45f47a29460000008667219600005b74c40110000009286620207d40007e28005729714800006921f800087708100032478105b1300000000004a10000360000004f01d00000000006640004000008b0000) else (if page < 3 then 0x6c68c62986101660d40000001405b05249343762126613967a18580000006685000006818901a16f02508e57542c65863a20911e05f03604566a47866d08d01807704702d14d80004e878a00000035b0004600005465408d69223047c24c2829 else 0x3141901877808488a08828814917101418227268500003363260c05f64205d16202475e07010005c07208441017d02e70e13645f70f98434845a195552077a8c00613063342b62281648b42090001102220000000009406880006e1000)) else (if page < 6 then (if page < 5 then 0x68066a6b66666c49365d06e08881e84219810475a58284e27316708424362894301b21c90f26b15780d65e23f07c051054492023659635a5507b14c85548209102727b46217b60b05f51a27b27246b06722f91cb8e10b28403817140004b07ba else 0x6010002a61000000000464629579611708306303808340000000a00006911167986983108e43c08237404c60006784c01b88919980004f20005301316514e04ca0004953307a08320000e07b89008085840a11500d08493445a0441660) else (if page < 7 then 0x7905a75560000009549028124869924113164340605606002d76a68c40005389040eb9016e20006a01604515f10e90009440006820f07169566c07007f01212615947566d68767303948e66070006e87509504f83b00008e0220000000000246 else 0x2b49510000787f42625322b00006b4570000401))) else 0
  | 6 => if page < 1 then 0x313730008041b60000840058708190728500215256b700c000b592003669638700116286a0b1b035986068344010b4205a7861505400 else 0
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
theorem chunk2x0 : span (checked 2) 18 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 18 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x48 : span (checked 3) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x96 : span (checked 3) 41 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 137 0 = true :=
  (@span_join (checked 3) 48 0 89 chunk3x0 (@span_join (checked 3) 48 48 41 chunk3x48 chunk3x96))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x48 : span (checked 4) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x96 : span (checked 4) 48 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x144 : span (checked 4) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x192 : span (checked 4) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x240 : span (checked 4) 42 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 282 0 = true :=
  (@span_join (checked 4) 144 0 138 (@span_join (checked 4) 48 0 96 chunk4x0 (@span_join (checked 4) 48 48 48 chunk4x48 chunk4x96)) (@span_join (checked 4) 48 144 90 chunk4x144 (@span_join (checked 4) 48 192 42 chunk4x192 chunk4x240)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x48 : span (checked 5) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x96 : span (checked 5) 48 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x144 : span (checked 5) 10 144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 154 0 = true :=
  (@span_join (checked 5) 96 0 58 (@span_join (checked 5) 48 0 48 chunk5x0 chunk5x48) (@span_join (checked 5) 48 96 10 chunk5x96 chunk5x144))

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

end SignedFrontier.SmallCert.Minor3

namespace SignedFrontier.SmallCert.Minor4

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeaaafffeeaaafffe
def negative : List Nat := [0, 16, 18, 20, 22, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨0,8,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,18,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffffccccffffccccffffaaaaffffaaaaffff8888ffff8888ffff00aaffff00aaffff0000ffff0000ffaaffaaffaaffaaffaaff00ffaaff00ff88ff88ff88ff88ff0fff00ff0fff00ff0cff0cff0cff0cff0aff0aff0aff0aff00ffccff00ffccff00ffaaff00ffaaff00ff00ff00ff00fcfcfcfcfcfcfcfcfafafafafafafafaf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeedddd0000dddd0000cccccccccccccccccccc4444cccc4444cccc00cccccc00cccccc0000cccc0000c4c4c4c4c4c4c4c4c0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0aaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaaa0000aaaa0000888888888888888855ff000055ff00005555000055550000505050505050505044cc44cc44cc44cc4444cccc4444cccc444444444444444400ff000000ff000000cc00cc00cc00cc00aa00aa00aa00aa0000cccc0000cccc0000aaaa0000aaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x4ce35099c285314310098a3010946 else 0
  | 4 => if page < 1 then 0x4ce4ea98eea3998db4c55aa29cd14e98a3b437261ab50cd286692364a0dd3146010f0135c096e0497023b8115c086e041701fb8153c0a5e050f019780bf405ba029d013e8097403bc016f00a78047401fa00dd else 0
  | 5 => if page < 1 then 0x15feafbbf6beafd1f9bf33e57c6f8bf13e1fc2f83f9af53ca78dd else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x2f else 0
  | 4 => if page < 1 then 0x23 else 0
  | 5 => if page < 1 then 0x17 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 5
  | 4 => 39
  | 5 => 19
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 3 => 4
  | 4 => 27
  | 5 => 16
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 15
  | 4 => 96
  | 5 => 61
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 6
  | 4 => 9
  | 5 => 8
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xa00 else 0
  | 4 => if page < 1 then 0x69a8c50ac06037820016c60030050c05c000003f else 0
  | 5 => if page < 1 then 0x8026c0038201d4040101 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1a058810008440240480304 else 0
  | 4 => if page < 2 then (if page < 1 then 0x29ad000e064a802b183000001198102de62c6d47000db18ba8f33064421703c74821a0004e206411105090b6cc541a0008c00201583400001f2998a4c8a414001e1d04c803c122e3 else 0x8830430413e00e584454800000050ca1f0fc94b8960000014180d844b44e0002680206c4) else 0
  | 5 => if page < 1 then 0x194a20311c6093083c7a844b3480480000883a000000006c2b4100007b000002783903006830582a5b008100901838731050404470283b5a3d72699200 else 0
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
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 5 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 39 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 39 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 19 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 19 0 = true :=
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

end SignedFrontier.SmallCert.Minor4

namespace SignedFrontier.SmallCert.Minor5

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeafefefeeafefefe
def negative : List Nat := [0, 8, 16, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨18,26,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨10,26,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

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

end SignedFrontier.SmallCert.Minor5

namespace SignedFrontier.SmallCert.Sub6x0

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0]
def target : W := 0xe8e8e8e8e8e8e8e8
def negative : List Nat := [0, 1, 2, 4]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl <;> first | contradiction | decide +kernel

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

end SignedFrontier.SmallCert.Sub6x0

namespace SignedFrontier.SmallCert.Sub6x1

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfeeafeeafeeafeea
def negative : List Nat := [0, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨0,1,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨4,6,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,6,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

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

end SignedFrontier.SmallCert.Sub6x1

namespace SignedFrontier.SmallCert.Minor6

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
  makeCutCertificate target Sub6x0.target 0xf000f 0x4d24500c2040 3 4
    pinBase [0x0,0xf000f,0xa000a,0xc000c,0x0,0x0,0xf0000,0x50005,0x30003,0xf000f,0xf000f,0xf] Sub6x0.raw Sub6x0.nonzero (@Sub6x0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Sub6x0.target 0xf0f 0x2ca2480c2040 3 4
    pinBase [0x0,0xf0f,0xa0a,0xc0c,0x0,0xf00,0x0,0x505,0x303,0xf0f,0xf,0xf0f] Sub6x0.raw Sub6x0.nonzero (@Sub6x0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 : CutCertificate target :=
  makeCutCertificate target Sub6x0.target 0xff 0x1c61440c2040 3 4
    pinBase [0x0,0xff,0xaa,0xcc,0xf0,0x0,0x0,0x55,0x33,0xf,0xff,0xff] Sub6x0.raw Sub6x0.nonzero (@Sub6x0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x55555555 0x71851030810079a59238a182 4 6
    pinBase [0x0,0x55555555,0x0,0x44444444,0x50505050,0x55005500,0x55550000,0x55555555,0x11111111,0x5050505,0x550055,0x5555] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x33333333 0x718510308100759551349141 4 6
    pinBase [0x0,0x33333333,0x22222222,0x0,0x30303030,0x33003300,0x33330000,0x11111111,0x33333333,0x3030303,0x330033,0x3333] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Sub6x1.target 0x5555aaaa 0x3cd2c91c50c179c698594490 4 5
    pinBase [0x0,0x5555aaaa,0xaaaa,0x44448888,0x5050a0a0,0x5500aa00,0x55550000,0x55550000,0x11112222,0x5050a0a,0x5500aa,0xaaaa] Sub6x1.raw Sub6x1.nonzero (@Sub6x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 : CutCertificate target :=
  makeCutCertificate target Sub6x1.target 0x3333cccc 0x3ce2ca1c60c275c658554450 4 5
    pinBase [0x0,0x3333cccc,0x22228888,0xcccc,0x3030c0c0,0x3300cc00,0x33330000,0x11114444,0x33330000,0x3030c0c,0x3300cc,0xcccc] Sub6x1.raw Sub6x1.nonzero (@Sub6x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0f0f0f 0xc20402ca2484d24506da658 4 5
    pinBase [0x0,0xf0f0f0f,0xa0a0a0a,0xc0c0c0c,0x0,0xf000f00,0xf0f0000,0x5050505,0x3030303,0xf0f0f0f,0xf000f,0xf0f] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xff00ff 0xc20401c61444d24505d6554 4 5
    pinBase [0x0,0xff00ff,0xaa00aa,0xcc00cc,0xf000f0,0x0,0xff0000,0x550055,0x330033,0xf000f,0xff00ff,0xff] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xffff 0xc20401c61442ca2483ce34c 4 5
    pinBase [0x0,0xffff,0xaaaa,0xcccc,0xf0f0,0xff00,0x0,0x5555,0x3333,0xf0f,0xff,0xffff] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Sub6x1.target 0x55aa55aa 0x5d54d179c6981c50c138c288 4 5
    pinBase [0x0,0x55aa55aa,0xaa00aa,0x44884488,0x50a050a0,0x55005500,0x55aa0000,0x55005500,0x11221122,0x50a050a,0xaa00aa,0x55aa] Sub6x1.raw Sub6x1.nonzero (@Sub6x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 : CutCertificate target :=
  makeCutCertificate target Sub6x1.target 0x33cc33cc 0x5d64d275c6581c60c234c248 4 5
    pinBase [0x0,0x33cc33cc,0x22882288,0xcc00cc,0x30c030c0,0x33003300,0x33cc0000,0x11441144,0x33003300,0x30c030c,0xcc00cc,0x33cc] Sub6x1.raw Sub6x1.nonzero (@Sub6x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Sub6x1.target 0x5a5a5a5a 0x6d979c4d15942c938c0c1184 4 5
    pinBase [0x0,0x5a5a5a5a,0xa0a0a0a,0x48484848,0x50505050,0x5a005a00,0x5a5a0000,0x50505050,0x12121212,0xa0a0a0a,0x5a005a,0x5a5a] Sub6x1.raw Sub6x1.nonzero (@Sub6x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 : CutCertificate target :=
  makeCutCertificate target Sub6x1.target 0x3c3c3c3c 0x6da75c4d25542ca34c0c2144 4 5
    pinBase [0x0,0x3c3c3c3c,0x28282828,0xc0c0c0c,0x30303030,0x3c003c00,0x3c3c0000,0x14141414,0x30303030,0xc0c0c0c,0x3c003c,0x3c3c] Sub6x1.raw Sub6x1.nonzero (@Sub6x1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf00ff00f 0x7de75c4d24503ce34c0c2040 4 7
    pinBase [0x0,0xf00ff00f,0xa00aa00a,0xc00cc00c,0xf000f000,0xf000f000,0xf00f0000,0x50055005,0x30033003,0xf000f,0xf000f,0xf00f] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xf0f00f0f 0x7de75c2ca2485d65540c2040 4 7
    pinBase [0x0,0xf0f00f0f,0xa0a00a0a,0xc0c00c0c,0xf0f00000,0xf0000f00,0xf0f00000,0x50500505,0x30300303,0xf0f,0xf0000f,0xf0f] Minor1.raw Minor1.nonzero (@Minor1.lower)
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

end SignedFrontier.SmallCert.Minor6


namespace SignedFrontier.SmallCert.Minor7

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
  | 0 => if page < 1 then 0xffff0000ffff0000ff00ff00ff00ff00f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaa88888888888888880000aaaa0000aaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0xbf5f3f else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0x11 else 0
  | 8 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 7 => 3
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
  | 7 => 9
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0x22180791003e31c0b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0xe086661f3308d7ab0169a27a1e008880000804ca121284225100034c196618104c179400c980580400219002a590000000004f18000 else 0
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


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0x55555555 0x79c69859449038c288184080 4 7
    pinBase [0x0,0x55555555,0x0,0x44444444,0x50505050,0x55005500,0x55550000,0x55555555,0x11111111,0x5050505,0x550055,0x5555] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target

  | _ => cut10

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0xbbb else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 4 i

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

end SignedFrontier.SmallCert.Minor7


namespace SignedFrontier.SmallCert.Minor8

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfffefeeefffefeee
def negative : List Nat := [0, 4, 8, 16]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨8,12,by decide +kernel,?_⟩
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
  | 0 => if page < 1 then 0xffffeeeeffffeeeeffffccccffffccccffffaaaaffffaaaaffff0000ffff0000ffeeffeeffeeffeeffccffccffccffccff00ff00ff00ff00f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaa3030303030303030222222222222222210101010101010100000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xea7 else 0
  | 3 => if page < 1 then 0x39998ccd92b1e18700dc else 0
  | 4 => if page < 1 then 0xddc79ecbcdc else 0
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
  | 2 => 1
  | 3 => 6
  | 4 => 5
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
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 3
  | 3 => 20
  | 4 => 21
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 7
  | 4 => 7
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x25018 else 0
  | 4 => if page < 1 then 0xf50043 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x8 else 0
  | 3 => if page < 1 then 0xe08208049b54a1449c101114260001480 else 0
  | 4 => if page < 1 then 0x8c59ba36ca1134600004000c5d2020014a6 else 0
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
theorem chunk3x0 : span (checked 3) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 6 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 5 0 = true :=
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

end SignedFrontier.SmallCert.Minor8



namespace SignedFrontier

-- Supplying intermediate wires costs at most the number of gates used to
-- compute them. This permits a projected branch to retain non-input wires.
theorem signedLower_after_prefix (g : W) (raw init supplied : List W) (n : Nat)
    (low : signedLower g raw n) (start : available init ⊆ insert 0 raw.toFinset)
    (p : List (Nat × Nat)) (stock : insert 0 supplied.toFinset ⊆ available (p.foldl add init)) :
    signedLower g supplied (n - p.length) := by
  intro k s run hs
  obtain ⟨m,t,hm,ht,exec⟩ := extract p init g k s run (hs.trans stock)
  have lb := low exec (ht.trans start)
  omega

theorem rowMap_zero (f : Fin 64 → Fin 64) : rowMap f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (rowMap_read f 0 ⟨i,hi⟩).trans (by simp)

theorem rowMap_not (f : Fin 64 → Fin 64) (a : W) : rowMap f (~~~a) = ~~~(rowMap f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun w => rowMap_read f w ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_not,hi,(f ⟨i,hi⟩).isLt,decide_true,Bool.true_and]

theorem rowMap_and (f : Fin 64 → Fin 64) (a b : W) :
    rowMap f (a &&& b) = rowMap f a &&& rowMap f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun w => rowMap_read f w ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_and]

theorem rowMap_getD (f : Fin 64 → Fin 64) (ws : List W) (j : Nat) :
    rowMap f (ws.getD j 0) = (ws.map (rowMap f)).getD j 0 := by
  by_cases h : j < ws.length
  · rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]
    exact rowMap_zero f

theorem rowMap_add (f : Fin 64 → Fin 64) (ws : List W) (gate : Nat × Nat) :
    (add ws gate).map (rowMap f) = add (ws.map (rowMap f)) gate := by
  simp only [add,List.map_append,List.map_cons,List.map_nil,rowMap_not,rowMap_and,rowMap_getD]

theorem rowMap_prefix (f : Fin 64 → Fin 64) (ws : List W) (p : List (Nat × Nat)) :
    (p.foldl add ws).map (rowMap f) = p.foldl add (ws.map (rowMap f)) := by
  induction p generalizing ws with
  | nil => rfl
  | cons gate p ih => simp only [List.foldl_cons,ih,rowMap_add]

-- The concrete prefix executes on the original physical inputs. Its wires
-- restrict to the same program on the projected inputs, even with high pins.
def prefixCutCertificate (g goal mask : W) (f : Fin 64 → Fin 64) (base raw : List W)
    (n : Nat) (low : signedLower goal raw n) (nz : goal ≠ 0)
    (cover : ∀ i, mask.getLsbD (f i).val = true) (goalEq : signedMap f g = goal)
    (start : available (base.map (rowMap f)) ⊆ insert 0 raw.toFinset)
    (p : List (Nat × Nat)) : CutCertificate g :=
  let ws := p.foldl add base
  let supplied := ws.map (signedMap f)
  { mask := mask
    patterns := ws.map (· &&& mask)
    bound := n - p.length
    sound := by
      intro budget s k le run
      apply maskedCut_sound f mask _ ws supplied g _ budget s cover rfl _ _ _ le run
      · intro w hw
        exact Or.inr (List.mem_map_of_mem hw)
      · rw [goalEq]
        exact nz
      · rw [goalEq]
        apply signedLower_after_prefix goal raw _ supplied n (@low) start p
        rw [←rowMap_prefix]
        simp only [available,List.map_map]
        rfl }

end SignedFrontier

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfe80800080000000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨30,31,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨29,31,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨27,31,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨23,31,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨15,31,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨15,47,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 3 then (if page < 1 then 0x8f8f8f008f8f8f008f008f008f008f008f0000008f0000008e8e8e8e8e8e8e8e8a8a8a8a8a8a8a8a8888888888888888880088008800880080808080ff80ff8080808080aaaaaaaa8080808088888888808080808080808080808080000000008080800080808000808000008080000080008000ff00ff008000800080808080800080008000800080000000800000007f7f7f7f808080807f7f7f7f000000007f7f7f007f7f7f007f7f00007f7f00007f007f00ff00ff007f007f007f007f007f0000007f00000070707070707070704c4c4c4c4c4c4c4c3f003f003f003f002a2a2a2aff2aff2a2a2a2a2aaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a002a2a2a002a002a002a2a2a2a2a002a002a002a002a0000002a0000000f0f0f000f0f0f000f000f000f000f000f0000000f0000000e0e0e0e0e0e0e0e0a0a0a0a0a0a0a0a080808088888888808080808080808080800080008000800070007000700070003000300030003000202020202020202000080808080808000002a2a2a2a2a2a00000000ffffff0000000000ff80ff8000000000ff00ff0000000000eeeeeeee00000000eaeaeaea00000000aaaaaaaa000000008f008f00000000008888888800000000808080800000000080008000000000007f007f00000000002a2a2a2a000000002a002a0000000000000080800000000000002a2a0000000000000000 else (if page < 2 then 0xffffffff00000000ffffff80ffffff80ffffff2affffff2affffff00ffffff00ffffff0000000000ffff2a2affff2a2affff0000ffff0000ffff000000000000fff8fff8fff8fff8fff0fff0fff0fff0ffeeffeeffeeffeeffccffccffccffccffc0ffc0ffc0ffc0ffaaffaaffaaffaaff88ff88ff88ff88ff80ff80ff80ff80ff80ff00ff80ff00ff808080ff808080ff800000ff800000ff7fff00ff7fff00ff70ff70ff70ff70ff2aff2aff2aff2aff2a2a2aff2a2a2aff00ff00ff00ff00ff00ff00ff000000ff00ff0080008000ff00ff0000000000ff008000ff008000ff000000ff000000fefefefefefefefefcfcfcfcfcfcfcfcfc00fc00fc00fc00fafafafafafafafaf8f8f8f8f8f8f8f8f800f800f800f800f0f0f0f0fff0fff0f0f0f0f0f0f0f0f0f000f000f000f000eeeeeeeeeeeeeeeeee00ee00ee00ee00ececececececececeaeaeaeaeaeaeaead500d500d500d500cccccccccccccccccccccccc00000000cccccc00cccccc00cc00cc00cccccccccc00cc00cc00cc00cc000000cc000000c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0c000c000c000c000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaa00aaaaaa00aaaa0000aaaa0000aa80aa80aa80aa80aa2aaa2aaa2aaa2aaa00aa00aaaaaaaaaa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a08f8f8f8f00000000 else 0xffffffff80808080ffffffff2a2a2a2a)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x7b636135076b0a21ac1ed8d8484100f6c676300676235c0032311ae001b580d6100c6c2670806d612f840311a87b00188d43980000ce79a00006233e00003115f00000f03dc else 0
  | 5 => if page < 1 then 0xf8c6c26b0fc6361218403e319dcc019d84d7100c8c26b8807b63351c031a49acc01b510d6600e0c25f88063482f98033b090e201ed8c84700c6a443280634921980309a87b20184843d900c26a1cc80007d639c00037b1ce00018cfe70000ce77b00006133e40003199ce0001b4be70000c257c80003b0f780003303ae0001e008f000000c9b8000002d7c000000e7600000039f else 0
  | 6 => if page < 2 then (if page < 1 then 0x351cec9873b211ced046fb351becc86fb2a1becd46bb211aecd43df210f7cd439f800d7d0035f3b0df8d035f2c0a7cb021f81077d941df2c077c341df007efc01f7f0072fc01c7f0070fc01bff006efc01b3f0069fc00fff003dfc00e3f0037fc00dbf0033fc00c7f0030fc00bff002efc00aff0029fc00a3f0027fc0093f0023fc008bf0020fc007ff001efc0077f001bfc005ff0015fc0047f0010fc0027f0007fc001bf0005fc000ff0002fc0007f else 0x7c6135e78309af38d84d79f8c66b3f04435db1a21aed64e8bfcc26a5fcd93a28f221d146d84d4a39886a51b7c6121e71b090f3f18c867c6a043ae1350de651a86bd8484379a6421aee13507e403d31de018cfb700f877f00633bf802e1af6019cd7700c86bb804935f80239afc0118d7e008a6bf004335f803817ee018cbf700905ff004828f8022146e00e4a37005e51b803a22f801a917c00d08be00b843d806721dc02910fa014487d009e43e804921f801d0f7c00d47be) else 0
  | 7 => if page < 3 then (if page < 1 then 0x9a31fb518fd30c7e9463f4231fde16fe08b7ee85bf6a2dfa616fd08b7ee853f7425fb50dfd086ff342ff6a15fa50afd0857f7823f6a11fa608fdd03fed41ff9a09fa104ff09d7aecebebe6bdde35ee21afd8487bbe43dd021f6710fae887e6a43f351bed08df6d463e4c31f2618ed28c7d785bb4c2ddba12fb09af38487900e1f806afc02cfe015bf007df803bfc01afe00bff0051f8021fc00f7e0063f002df8007fc0027e00efe else (if page < 2 then 0x746a31f3a2618f9d130c77049463ebc742ddba2616eef1d097d7964ebcb2746be613a35e70a690f378e863a744c31d007356fc03b9d7e01c0ebf00d675f805f3afc02f1d7e0174ebf008475f803e3afc01d9d7e0178e7f00f86bf807235fc0389afe01c0d7f00c66bf805935fc02b1afe0110d7f00746bf803935fc01d17fe00d4bff007451f803528fc02b127e00d493f00f843f807421fc03990fe01c887f00d443f806321fc03090fe016487f00ac43f805521fc02810fe013887f009a43f804c21fc02210fe00e887f006a43f802421fc0268f7e00847bf006a37f80261bfc0108dfe015c63f else 0x30af1d7b7964ebdbc8875f5e413aef09d1afb64e8d7dbe746bdde3a35eed1d1af710e8d7ec29a43ddf4d21ee82690fb393487d9a7443f4d3521f9d1a90fd5d046fb826a37dba351bee6908df75d0463ebc7431f5e3a18ee69a8c7d04d463e)) else 0
  | 8 => if page < 2 then (if page < 1 then 0xc285ffc3affb1d7fc8ebfe275fe33afef9d7f78ebfb475fd93afe21d7f04ebf7473fba35fe6927f3487fbe37fd91bfe08dfee86ffb233fe118fef8c7f6463f9a31fc118fdd0c7ee85bfc227fe112fec86fee837fb219fe10afec857f342bf7415fba08ff09d7b64ebd8875f411bef08c777c63b8231f3a18fac9d7801d7f00e3f8062fc02c7e015bf0085f8039fc01afe0093f0043f8019fc00c7e005bf0027f8012fc0067e0023f else 0x3e2cffd967feab3ff259ff1acff8967fbeb3fd958ff0a27f6513f) else 0
  | 9 => if page < 1 then 0x3e7fcbfc7fd9fe27eebf37f98fc6fe2bf else 0
  | 10 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x4b else 0
  | 5 => if page < 1 then 0x4b else 0
  | 6 => if page < 1 then 0xec2d else 0
  | 7 => if page < 1 then 0x3b0ec2b else 0
  | 8 => if page < 1 then 0xac2b else 0
  | 9 => if page < 1 then 0x1b else 0
  | 10 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 4 => 15
  | 5 => 32
  | 6 => 115
  | 7 => 154
  | 8 => 74
  | 9 => 10
  | 10 => 1
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 6)

def bucketCount : ℕ → ℕ
  | 4 => 9
  | 5 => 22
  | 6 => 79
  | 7 => 155
  | 8 => 70
  | 9 => 20
  | 10 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 4 => 38
  | 5 => 80
  | 6 => 290
  | 7 => 556
  | 8 => 254
  | 9 => 73
  | 10 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 4 => 3
  | 5 => 5
  | 6 => 7
  | 7 => 7
  | 8 => 7
  | 9 => 4
  | 10 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 4 => 10
  | 5 => 11
  | 6 => 13
  | 7 => 14
  | 8 => 13
  | 9 => 10
  | 10 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x4088743 else 0
  | 5 => if page < 1 then 0x111c380c808011087009890bde3 else 0
  | 6 => if page < 2 then (if page < 1 then 0xe2c20264080804a20b26060408a0a2000004108180a0438012301073c0818600140020020006000018004002021014181023c0911004080 else 0x1018130002928080a121400080) else 0
  | 7 => if page < 3 then (if page < 1 then 0x240a8a02d43a5001009b040000326004801600001060050406941000214080160001526540360c7888204600011218b020e340800e00c99 else (if page < 2 then 0x1e140001e040046214101186820200242000052883007001c006cb12328e086000048002318820030100040000a003800408040050410285 else 0x3019d2488f8600000804a2c00008141020600599109121f)) else 0
  | 8 => if page < 2 then (if page < 1 then 0x33800cc00380002098f0e0004603041810a4e28a22020828c0004a800000102000140014000895a1010c001878a180010f022c500001c200 else 0x16833428cb8) else 0
  | 9 => if page < 1 then 0x5404d00a522f47100321 else 0
  | 10 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0xc11cc0000000000101807480050000e12800038cc0100d0800b79c0e48809018c8098206000d02d8648003638000000 else 0
  | 5 => if page < 2 then (if page < 1 then 0x10000046000809e92ded00212823ccc98000603c0a0174800000480e00cc080eb1b4a29580f80003e96c0524002206ccb8130000000ca583ac95ccb18b618c1c0c8074a264c6e2580a40103c28a3200141f99a13c0000 else 0x8040070c5000002c700ebc002a000033c801a11cc) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0xac04f01381a40220240c1819d29604000a8b392a879c124893cd9e6124b7249026e31706d3c9ccae1396f424000806535e800980000000000134c9084c00000c982e013063818c00006d5382475668000000011830001916aa5c803a8000238c000e2610100002c6 else 0x8094d00b008183003a0a520e837605c698bcfc018064030008820007248000000d063e60001b8cc20451a5095c376328026a5492a8ad40e080e88580ee017ad7c05a23702216000c614811a81c0c78c0406f01a805203f18d0958c00003042019400005344f01ac0) else (if page < 3 then 0x5626731c0c08000030100000009c00b600000004205e4928000000000027a57406005900000000e46070d680bc4d696322c06e9bb4c500870ae180006d0a099256cc0180f6a435272d4858000a801e04e4f0a40009c60b0311954c20b7103124f469c6c302dbc410 else (if page < 4 then 0x7ec1d116094800a239200876d89e99f6280374276c2f42c8c000ac9680309978c7000001b000000000003499c5200000000000002606b32280000aa00900508203d806d3a18c00062c0003800000b8c4414a886c0000000298a0000003c183310809e0ba27380d01 else 0x1c87250de02b013a4b84da65f18a00e427a01a16919381602b9240008834606d01d34000c40631acb00001a0000c0000001a60002880cc0))) else 0
  | 7 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x846048c8d08e805408000886cc1234099922f5a1c860500001900000953168264000005f01f5e33017820000c450600000020400056017403d78c43562485498018c05019f9e2108b925300fc60000000650c0001201b0236615c11831615000000000000007a60fd266521405952218 else 0x1060000f0c136214617795432e587c00001e4069614808824000000059e0001e0000012427379880700e5cf021120c72480008d20c166d61c422f4db8041180002800c4297313422f0400003181c261481c07c309c08600bd0000000000016125e00606430c6486b3189822024c0) else (if page < 3 then 0x7101f586a68fde7f3240e9600000890070c900a1c615308d845018c1321000000007824324040603e5c056206460000d462a600005b0205e60560c000010c260310d83b188cc14011430001e4c1a0c8557631a5e490d9023e61c948868000893000000024033204e006e617021a619c4 else 0x5b08b413e484527401bda1a24c135954682410c91e920084f436d8c40808000234a386460c84c0a61440820158647483400c013c040193408f00203020098088201c3910a2c05c0d6838d2494c2f34a412e4198e4801a0300003c266009182c00c808f183c02b10ac14d207880000000)) else (if page < 6 then (if page < 5 then 0x21010426a6c4404d261425948f808d0e3001e2464395010988761a020b68000680000018600001c023400001d402a64c41436981200009c11a6c000440c00000017000001983291258c23180000501bdb4c01f98050d0c8540e306993095e80195404508b93850cbc45001c955710000 else 0x16600004060000806019282321db4f480180509582970dc0053090c02e353067360b040e0a50c6e789c42f30bc031024cc6701c022149c4347306d260014810000fc0640c800460001e940029e1848c444a0000041263464d0d6145f1998f44017d87b025c24e08000910e1493d62183) else (if page < 7 then 0x320c0448a0199519252d21a00b0125019c14e0cb446c0d4843214d004d18ccc1a2038341220cc6630740290240f080240c3e79a9862197431908bd26500f128a491825d0a5ce7c487834408000426c2db0001d800001500000040018016c317608061e022c61a6a10600012820001b8c else (if page < 8 then 0x852000003008c02604000000168000000000000000983178311318020000f8c4b012400000000000018c8e0095890015c043187063b00984320980e0f0dfc001040000000dc00000000881a1c90400e4c28040004a0d4c31f1a440560d5421d1a1824269942340ddc06609bd82a71b00 else 0x1a1a1da0000e52470084e0d183804e02640000000000000003500f861b000000000000187800000000002e300000b60000481884328118036b008de2d00ac074302401e1a0521b310401548000)))) else 0
  | 8 => if page < 4 then (if page < 2 then (if page < 1 then 0x10000000000000000055246a084a31e6c400000000000d58000000000b495a34709084d002e62800088ac050641551a500f8a0970de1d1c082927480025cf8419d011252006a1900d7b0000306193220084072c3e100010027421e59c808451a18002301183 else 0x1e01709e84f801a10a008045883e20518700f433a6bc31d86f036092532482a9e400941a2804404801d400006405e42e082b00003a601058a81d25edc030e82cc20000f0c0002d28e18000e24bda5c18100000dc2422000000000000000010860006a7433130d080) else (if page < 3 then 0x2af2c01b000007260000000215000391978cf020002f24b800003291f04b0c00032f4511c00d404cc3a0631cf0f7611e4cb9ccc07801f002008027a02a4a488d422400851280d4f2cc3b0098c8d56e1b700504c555ac4300d005893000248d807164002015a18b80 else 0x52c00006806cd000330ca300005a40000e268413664901900f818c648080006d00001a041a91827401e48d08b021891b05fa520382a31487842404ef200c50659b2cd06016b6d4c4020348800744841000148d00e5ad400c0004d82462c0c000000)) else 0
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


def goalColumns : Nat := 0xfe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000fe80800080000000
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xc0c0c0c0c0c0c0c0
    (fun r => ⟨(0x18738f59779f9a7bafdb7fbf >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xa0a0a0a0a0a0a0a0
    (fun r => ⟨(0x14734f55775f967b6fd77f7f >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0x8888888888888888
    (fun r => ⟨(0xc72cf4d76df8e7aefcf7eff >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor0.target 0xf0f0f0f000000000
    (fun r => ⟨(0x9efdff9aedbe96dd7d92cd3c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor0.target 0xf0f00000f0f00000
    (fun r => ⟨(0x5dfdff59edbe55dd7d51cd3c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor0.target 0xf000f000f000f000
    (fun r => ⟨(0x3dfbff39ebbe35db7d31cb3c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor0.target 0xcccccccc00000000
    (fun r => ⟨(0x9efdff9aedbe8ebcfb8aacba >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor0.target 0xcccc0000cccc0000
    (fun r => ⟨(0x5dfdff59edbe4dbcfb49acba >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor2.target 0xffff000000000000
    (fun r => ⟨(0xe39ebbf3dfbfc31cb3d35db7 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 6 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor2.target 0xff00ff0000000000
    (fun r => ⟨(0xe39ebbf3dfbfa29aabb2dbaf >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 6 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor2.target 0xff000000ff000000
    (fun r => ⟨(0xe39ebbf3dfbf61969b71d79f >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 6 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut18 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor8.target 0xff00ff00ff00ff0
    (fun r => ⟨(0x1149341559751969b61d79f7218a38259a7929aaba2dbafb >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor8.raw 6 (@Minor8.lower) Minor8.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor8.target 0xf0f0f0ff0f0f0f0
    (fun r => ⟨(0x10c51c14d55d18e59e1cf5df828c38869c798aacba8ebcfb >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor8.raw 6 (@Minor8.lower) Minor8.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor8.target 0x33cc33cc33cc33cc
    (fun r => ⟨(0x928b20d38f3218a38259a791969b61d79f731cb3c35db7d >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor8.raw 6 (@Minor8.lower) Minor8.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut30 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor8.target 0x55aa55aa55aa55aa
    (fun r => ⟨(0x51871218a380d38f329aaba15597531cb3c1d79f739ebbe >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor8.raw 6 (@Minor8.lower) Minor8.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut45 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor7.target 0x9999999999999999
    (fun r => ⟨(0x310720b30f41351761b71f823927a2bb2fc33d37e3bf3f >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor7.raw 9 (@Minor7.lower) Minor7.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut46 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor7.target 0xa5a5a5a5a5a5a5a5
    (fun r => ⟨(0x508720d28f41549761d69f8258a7a2daafc35cb7e3debf >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor7.raw 9 (@Minor7.lower) Minor7.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut60 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor3.target 0xf0f0f0f0f0f0f0f0
    (fun r => ⟨(0x1cf5df9efdff18e59e9aedbe14d55d96dd7d10c51c92cd3c >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor3.raw 8 (@Minor3.lower) Minor3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut61 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor3.target 0xcccccccccccccccc
    (fun r => ⟨(0x1cf5df9efdff18e59e9aedbe0cb4db8ebcfb08a49a8aacba >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor3.raw 8 (@Minor3.lower) Minor3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut62 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor3.target 0xaaaaaaaaaaaaaaaa
    (fun r => ⟨(0x1cf5df9efdff14d55d96dd7d0cb4db8ebcfb049459869c79 >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor3.raw 8 (@Minor3.lower) Minor3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut67 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor6.target 0xffffffff00000000
    (fun r => ⟨(0x828c38869c798aacba8ebcfb92cd3c96dd7d9aedbe9efdff >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor6.raw 9 (@Minor6.lower) Minor6.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut68 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor6.target 0xffff0000ffff0000
    (fun r => ⟨(0x418c38459c7949acba4dbcfb51cd3c55dd7d59edbe5dfdff >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor6.raw 9 (@Minor6.lower) Minor6.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut69 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor6.target 0xff00ff00ff00ff00
    (fun r => ⟨(0x218a38259a7929aaba2dbafb31cb3c35db7d39ebbe3dfbff >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor6.raw 9 (@Minor6.lower) Minor6.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p
def cutFor : Nat → List (Nat × Nat) → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 7 => cut6
  | 8 => cut7
  | 13 => cut12
  | 14 => cut13
  | 15 => cut14
  | 19 => cut18
  | 21 => cut20
  | 25 => cut24
  | 31 => cut30
  | 46 => cut45
  | 47 => cut46
  | 61 => cut60
  | 62 => cut61
  | 63 => cut62
  | 68 => cut67
  | 69 => cut68
  | 70 => cut69
  | _ => cut0

def suppliedPrefix : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | j+1, z => if z=0 then [] else ((z%256)/16,z%16) :: suppliedPrefix j (z/256)
def selectCut (code : Nat) := cutFor (code%128) (suppliedPrefix 2 (code/128))
def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x4614008c3001485000010004610008c280118600230a004618008c2001184002308004614008c2801184 else 0
  | 5 => if page < 1 then 0xbc560378ac0400004000000000000000002f15810000008b2502ac6a0800000000000bc560378ac0800000000000000000000014000035e2b0300000e0000000000000000000000000001c0000200000400000a00000000000800004 else 0
  | 6 => if page < 2 then (if page < 1 then 0x200000400000800001000002004c0401a008000010000020000000000000000000001a00ba0c0174080000000790400f40c0000680000d0000000000340000680000d00000400000c0000700000e00001e00003800007805e03005606000000000008000010000000000000000000001300002600000000000002c010000000000040174080168100000200000400000800001000002005a040000080000d0000020000340000680000d00001a00000400006800001 else 0x17804022c0802b010000000136080158100128100250200b00401641002c010059040178040158080000000560200ba0401741002e81005d02005a0400006802b0300bc0200ac040000080000000000001780800000801281007b0400ac080000000000000350400b2080000f800019000026005a0400b4080001500000200000002f00803d8100560201780800000800001) else 0
  | 7 => if page < 3 then (if page < 1 then 0x2000004000008000010000020000040000080000100000200000400000800001000002000000000000000010000040000080000100000300000600000c008e200000000000200000400000800001000002000004000010000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100008c00000400000800001000006000004000008000000000000000040000080000100000200011000000800001 else (if page < 2 then 0x2000004000008000010000020000040000080000100000200000400000800001000002000004000008011c60000060000040000080000100000200000c00000800003000000000008000018000000000000000040000080000200000200000c0000000000000000000000000000800001000000000004000008000020000020000000000080000100000200000400000800001000002000004000010000010000020000040000080000100000200000400000800001 else 0x800001000004000004000008000010000020000040000080000200000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001)) else 0
  | 8 => if page < 2 then (if page < 1 then 0x7a004714008e300003f00238c0047140001f80000000238c0000b80001f80003f00238c00000000d2300000000007a0113180001e8011c600007c0000f40001780003f00007a0000bc0001f8011af00007a0000f4022620011c400007c0135100001f801a4400007e0047100001f00002e00238c0000f40001e80002f00005e0046bc0001700003e00008c0000f40001f00002e00005c00471800000001a460000000000f40001780002f00007a0000b80001f000044 else 0x22628044c600007c0000fc0226280003e00007e0000f8026a300003f) else 0
  | 9 => if page < 1 then 0x2280004600008a0000000002300000000008c0000bc00022000044 else 0
  | 10 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 23 i

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
theorem chunk4x0 : span (checked 4) 15 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 15 0 = true :=
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
theorem chunk6x0 : span (checked 6) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 3 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 115 0 = true :=
  (@span_join (checked 6) 112 0 3 chunk6x0 chunk6x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x112 : span (checked 7) 42 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 154 0 = true :=
  (@span_join (checked 7) 112 0 42 chunk7x0 chunk7x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 74 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 74 0 = true :=
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
  · simp [counts]
  · simp [counts]
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

end PEqualNP.Outside.L_meta_12244_aux

open PEqualNP.Outside.L_meta_12244_aux

theorem PEqualNP.Outside.L_meta_12244 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
