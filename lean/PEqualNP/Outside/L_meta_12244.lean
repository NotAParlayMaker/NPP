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
  | 0 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0xfffe0000fffe0000fffa0000fffa0000fff00000fff00000ff000000ff000000fefe0000fefe0000feee0000feee0000fcfc0000fcfc0000fafe0000fafe0000fafa0000fafa0000faf00000faf00000faaa0000faaa0000f8f80000f8f80000f6f60000f6f60000f3f00000f3f00000f2f20000f2f20000f0fe0000f0fe0000f0fa0000f0fa0000f0f00000f0f00000f0a00000f0a00000f0300000f0300000f0000000f0000000eeee0000eeee0000eaea0000eaea0000e0e00000e0e00000cccc0000cccc0000baba0000baba0000b0b00000b0b00000aafa0000aafa0000aaee0000aaee0000aaaa0000aaaa0000aaa00000aaa00000a8a80000a8a80000a2a20000a2a20000a0f00000a0f00000a0aa0000a0aa0000a0a00000a0a00000a0000000a000000088aa000088aa0000888800008888000080800000808000007676000076760000707000007070000066660000666600003330000033300000323200003232000030f0000030f000003030000030300000300000003000000022aa000022aa00002222000022220000202000002020000010100000101000000ff000000ff000000aaa00000aaa000000fa000000fa000000f0000000f0000000ee000000ee000000aa000000aa000000a0000000a00000008800000088000000300000003000000022000000220000000a0000000a0000000000000000 else (if page < 2 then 0x1010f8f81010f8f81010f0f01010f0f010107070101070701010303010103030101010f0101010f010101010101010101000f0f01000f0f010001000100010000ffffff00ffffff00fff0f000fff0f000fff00000fff00000ff0fff00ff0fff00ff0f0f00ff0f0f00f0ff0f00f0ff0f00f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0a0f0a0f0a0f0a0f00fff00f00fff00f00ff000f00ff000f000f000f000f000ccccccc0ccccccc0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa02aaaaaa02aaaaaa0222aaaa0222aaaa00fffff000fffff000ffffaa00ffffaa00ffff0000ffff0000fff0f000fff0f000ff00f000ff00f000ff000000ff000000fe00fe00fe00fe00fafafa00fafafa00f0fff000f0fff000f0ff0000f0ff0000f0f0f000f0f0f000f0f00000f0f00000f000f000f000f000eeeeee00eeeeee00cc00cc00cc00cc00aaffaa00aaffaa00aaf0fa00aaf0fa00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa00a0f0f000a0f0f000a0aaaa00a0aaaa00a0a0a000a0a0a00088aaaa0088aaaa00888888008888880033ffcc0033ffcc0033ff000033ff0000333300003333000030fff00030fff00030ff300030ff300030f0f00030f0f000303030003030300022aaaa0022aaaa0022222200222222000ffff0000ffff0000ff0f0000ff0f0000aaaaa000aaaaa else 0x3030f0703030f0703030f0303030f0303030baba3030baba3030b0f03030b0f03030b0b03030b0b0303070f0303070f0303070703030707030303c3c30303c3c30303330303033303030323230303232303030f0303030f030303070303030703030303030303030303030003030300030300000303000003020f0f03020f0f030203020302030203010f0f03010f0f030103010301030103000fff03000fff03000ff003000ff003000f0f03000f0f03000f0003000f000300030f0300030f030003030300030303000300030003000300000f0300000f030000000300000002aaaaaaa2aaaaaaa2a2a2a2a2a2a2a2a22aaeeaa22aaeeaa22aaaaaa22aaaaaa22aa22aa22aa22aa22a2aaaa22a2aaaa222aaaaa222aaaaa2222f2f22222f2f22222eeee2222eeee2222eaea2222eaea2222aaaa2222aaaa2222a2aa2222a2aa2222a2a22222a2a22222666622226666222232322222323222222aaa22222aaa222222aa222222aa2222222a2222222a2222222222222222222200002222000022202220222022202020f0f02020f0f02020aaaa2020aaaa2020a0a02020a0a020203030202030302020222220202222202020202020202020002000200020001111eeee1111eeee1111aaaa1111aaaa111100001111000011101110111011101100ff001100ff0010f0f0f010f0f0f01030f0f01030f0f0103050f0103050f0)) else (if page < 5 then (if page < 4 then 0x5555aaaa5555aaaa555555005555550055555050555550505555444455554444555500005555000055505550555055505500ff005500ff0055005500550055005500000055000000545454545454545450f050f050f050f05050f0f05050f0f050505050505050504c4c4c4c4c4c4c4c44cc44cc44cc44cc4444cccc4444cccc44444444444444443f3f00003f3f00003f00ff003f00ff003f003f003f003f003c3c3c3c3c3c3c3c33ffff0033ffff0033ff000033ff000033ccff0033ccff0033cccccc33cccccc3333f0f03333f0f03333cccc3333cccc3333aaaa3333aaaa33336666333366663333444433334444333333cc333333cc33333332333333323333333033333330333300003333000033323332333233323330fff03330fff0333033303330333033303030333030303300ff003300ff00330077003300770033003300330033003232fafa3232fafa3232f0f03232f0f032323232323232323230faf03230faf032303230323032303222322232223222313031303130313030ff303030ff303030ff000030ff000030f0fff030f0fff030f0fcf030f0fcf030f0f0f030f0f0f030f030f030f030f030b0f0f030b0f0f03070f0f03070f0f030707070307070703033f0f03033f0f03030fff03030fff03030ff303030ff303030fcfc3030fcfc3030fcf03030fcf03030f8f83030f8f83030f0f03030f0f0 else 0xa0a0a0a0a0a0a0a0a0a0a000a0a0a000a080a080a080a080a020a020a020a020a000f0f0a000f0f0a000f000a000f000a000aaaaa000aaaaa000a0a0a000a0a0a000a000a000a000a0000000a00000009999aaaa9999aaaa9898f8f89898f8f898989898989898988f008f008f008f008c8c8c8c8c8c8c8c8aaaaaaa8aaaaaaa8a8a8a8a8a8a8a8a8a8a0a0a8a8a0a0a88aaaaaa88aaaaaa8888f8f88888f8f88888aaaa8888aaaa8888a8a88888a8a8888888aa888888aa88888888888888888888000088880000888088808880888088008800880088008080f0f08080f0f08080aaaa8080aaaa8080a0a08080a0a08080888880808888808080808080808080008000800080007f007f007f007f007777888877778888777700007777000077707770777077707700ff007700ff007700770077007700767676767676767673507350735073507272f0f07272f0f07272727272727272727072707270727070f0f0f070f0f0f07070ff707070ff707070f8f87070f8f87070f0f07070f0f07070f0707070f0707070777070707770707070f0707070f070707070707070707030f0f07030f0f0703070707030707070307030703070307000f0f07000f0f0700070707000707070007000700070006666eeee6666eeee6666aaaa6666aaaa66666666666666665f5f00005f5f00005f005f005f005f0055ff000055ff0000) else (if page < 6 then 0xaaaafefeaaaafefeaaaafcfcaaaafcfcaaaafafaaaaafafaaaaafaaaaaaafaaaaaaaf0f0aaaaf0f0aaaaeeeeaaaaeeeeaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaababaaaaababaaaaaaafaaaaaaafaaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa2a2aaaaa2a2aaaaa2222aaaa2222aaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000aaaa0000aaa8aaa8aaa8aaa8aaa2aaaaaaa2aaaaaaa2aaa2aaa2aaa2aaa0fff0aaa0fff0aaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aa22aaaaaa22aaaaaa0aaa0aaa0aaa0aaa00aa00aa00aa00aa000000aa000000a8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a8a0a8a0a8a0a8a0a888a888a888a888a6a6a6a6a6a6a6a6a5a5f0f0a5a5f0f0a5a5aaaaa5a5aaaaa2aaaaaaa2aaaaaaa2a2aaaaa2a2aaaaa2a2a2aaa2a2a2aaa2a2a2a2a2a2a2a2a2a0a2a0a2a0a2a0a222aaaaa222aaaaa222a222a222a222a0f0fff0a0f0fff0a0f0f0f0a0f0f0f0a0aaf0f0a0aaf0f0a0aaaaaaa0aaaaaaa0a0ffa0a0a0ffa0a0a0f0f0a0a0f0f0a0a0f0a0a0a0f0a0a0a0ececa0a0ececa0a0e0e0a0a0e0e0a0a0b0b0a0a0b0b0a0a0aaaaa0a0aaaaa0a0aaa0a0a0aaa0a0a0a8a8a0a0a8a8a0a0a2a2a0a0a2a2a0a0a0f0a0a0a0f0a0a0a0aaa0a0a0aa else 0xcccceeeccccceeecccccececccccececcccceccccccceccccccccceccccccceccccccccccccccccccccccc00cccccc00cccc8888cccc8888cccc4c4ccccc4c4ccccc44cccccc44cccccc4444cccc4444cccc0c0ccccc0c0ccccc0000cccc0000ccc0ccc0ccc0ccc0cc4ccc4ccc4ccc4ccc0ccc0ccc0ccc0ccc00cc00cc00cc00cc000000cc000000cacacacacacacacac8c8c8c8c8c8c8c8c4c4c4c4c4c4c4c4c0f0c0f0c0f0c0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0c0c00000c0c00000bf00bf00bf00bf00bbbbccccbbbbccccbbbabbbabbbabbbabbb0bbb0bbb0bbb0bb00ff00bb00ff00babafafababafafababaf0f0babaf0f0bababababababababaaabaaabaaabaaab8b8f8f8b8b8f8f8b8b8f0f0b8b8f0f0b8b8b8b8b8b8b8b8b4b4b4b4b4b4b4b4b3a0ffa0b3a0ffa0b3a0b3a0b3a0b3a0b0f0f0f0b0f0f0f0b0b0f0f0b0b0f0f0b0b0b0f0b0b0b0f0b0b0b0b0b0b0b0b0b0a0f0f0b0a0f0f0b0a0b0a0b0a0b0a0b030f0f0b030f0f0b030b030b030b030b000f0f0b000f0f0b000b000b000b000afafaaaaafafaaaaafaf0000afaf0000afaaafaaafaaafaaaf00af00af00af00aeaeaeaeaeaeaeaeaeaeaaaaaeaeaaaaaaffffaaaaffffaaaaffff00aaffff00aaff0000aaff0000aafafafaaafafafaaaf0fff0aaf0fff0aaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaaafffaaaaafffa))) else (if page < 10 then (if page < 8 then 0xeeeeececeeeeececeeeecccceeeecccceeeeaaaaeeeeaaaaeeee6666eeee6666eeee4444eeee4444eeee0000eeee0000eeeceeeceeeceeeceeecececeeecececeeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceecccccceecccccceeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaececeeecececeeececececececececececececccecececccecccecececccecececcceccceccceccceccccccceccccccceaeafafaeaeafafaeaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaeaaaaaeaeaaaaaeac0eac0eac0eac0eaaaeaaaeaaaeaaae8e8e8e8e8e8e8e8e6e6e6e6e6e6e6e6e4e4ecece4e4ecece4cce4cce4cce4cce2e2e2e2e2e2e2e2e0e0f0f0e0e0f0f0e0e0eeeee0e0eeeee0e0e0e0e0e0e0e0e0c0e0c0e0c0e0c0e0a0e0a0e0a0e0a0e000e000e000e000dfdf0000dfdf0000df00df00df00df00df005f00df005f00ddff0000ddff0000ddddccccddddccccdddd0000dddd0000dcdcdcdcdcdcdcdcdcccccccdcccccccdadadadadadadadad8d8d8d8d8d8d8d8d0f050f0d0f050f0d0d0f0f0d0d0f0f0d0d0d0d0d0d0d0d0d0d05050d0d05050cff0cff0cff0cff0cfcff0f0cfcff0f0cfcf0000cfcf0000cfc0cfc0cfc0cfc0cf00cf00cf00cf00cf000f00cf000f00cececececececececececccccececcccccffff00ccffff00ccff0000ccff0000ccecececccecececccccfcfcccccfcfccccceeeecccceeee else (if page < 9 then 0xf0f00000f0f00000f0eef0eef0eef0eef0e0ffe0f0e0ffe0f0e0f0f0f0e0f0f0f0e0f0e0f0e0f0e0f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0b0f0f0f0b0f0f0f0b0f0b0f0b0f0b0f0aaf0f0f0aaf0f0f0aaf0aaf0aaf0aaf0a0fff0f0a0fff0f0a0ffaaf0a0ffaaf0a0ffa0f0a0ffa0f0a0ff00f0a0ff00f0a0f0f0f0a0f0f0f0a0f0e0f0a0f0e0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0a0f0f0a0a0f0f0a0a0a0f0a0a0a0f080ff88f080ff88f080f0f0f080f0f0f080f080f080f080f070f0f0f070f0f0f070f070f070f070f0707070f0707070f050f050f050f050f03cf03cf03cf03cf033f0f0f033f0f0f030f0f0f030f0f0f030f070f030f070f030f030f030f030f030f000f030f000f0303030f0303030f020f0f0f020f0f0f020f020f020f020f010f0f0f010f0f0f010f010f010f010f00ff0f0f00ff0f0f00ff000f00ff000f00af00af00af00af000fff0f000fff0f000ff00f000ff00f000faaaf000faaaf000f0f0f000f0f0f000f0e0f000f0e0f000f0a0f000f0a0f000f070f000f070f000f030f000f030f000f000f000f000f000a0f0f000a0f0f000a000f000a000f0003000f0003000f0000f00f0000f00f00000f0f00000f0f0000000f0000000eeeefefeeeeefefeeeeef0f0eeeef0f0eeeeeeeeeeeeeeeeeeeeeeeceeeeeeeceeeeeeeaeeeeeeeaeeeeeecceeeeeecceeeeeeaaeeeeeeaa else 0xfa00ff00fa00ff00fa00fa00fa00fa00f8f8fafaf8f8fafaf8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f888ff88f888ff88f888f888f888f888f7f0f7f0f7f0f7f0f7a0f7a0f7a0f7a0f780f780f780f780f700f700f700f700f6f6f6f6f6f6f6f6f5f50000f5f50000f5f0f5f0f5f0f5f0f4f4f4f4f4f4f4f4f3f3f3f0f3f3f3f0f3f3f300f3f3f300f3f2f3f2f3f2f3f2f3f0fff0f3f0fff0f3f0f3f0f3f0f3f0f3f0f0f0f3f0f0f0f3ccf3ccf3ccf3ccf3c0ffc0f3c0ffc0f3c0ff00f3c0ff00f3c0f3c0f3c0f3c0f3a2f3a2f3a2f3a2f333f000f333f000f300ff00f300ff00f2f2fafaf2f2fafaf2f2f2f2f2f2f2f2f2f0f2f0f2f0f2f0f222f222f222f222f1f0f1f0f1f0f1f0f0fffff0f0fffff0f0fff0f0f0fff0f0f0fff000f0fff000f0ff0000f0ff0000f0fafafaf0fafafaf0faf0faf0faf0faf0f0fffaf0f0fffaf0f0fff0f0f0fff0f0f0ff00f0f0ff00f0f0fefef0f0fefef0f0fcfcf0f0fcfcf0f0fafaf0f0fafaf0f0faf0f0f0faf0f0f0f8f8f0f0f8f8f0f0f3f0f0f0f3f0f0f0f2f2f0f0f2f2f0f0f0faf0f0f0faf0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0f0a0f0f0f0a0f0f0f070f0f0f070f0f0f030f0f0f030f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f07070f0f07070f0f050f0f0f050f0f0f05050f0f05050f0f03030f0f03030f0f000f0f0f000f0)) else (if page < 12 then (if page < 11 then 0xff00ffa0ff00ffa0ff00ff88ff00ff88ff00ff70ff00ff70ff00ff30ff00ff30ff00ff00ff00ff00ff00cf00ff00cf00ff00af00ff00af00ff008f00ff008f00ff007700ff007700ff005f00ff005f00ff005500ff005500ff003f00ff003f00ff000f00ff000f00ff000000ff000000fefefefefefefefefefef0f0fefef0f0fefe0000fefe0000fefafefafefafefafef0fef0fef0fef0feeefeeefeeefeeefecceeccfecceeccfeccccccfeccccccfe88fe88fe88fe88fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcf0fcfcfcf0fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcecececfcecececfcccfcccfcccfcccfcccecccfcccecccfcccccccfcccccccfbfafbfafbfafbfafbf0fbf0fbf0fbf0fafff0f0fafff0f0faff0000faff0000fafafffafafafffafafafefefafafefefafafafafafafafafafafaf0fafafaf0fafafaaafafafaaafafafa00fafafa00fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0a0afafa0a0afafa0000fafa0000faf8faf8faf8faf8faf2faf2faf2faf2faf0fff0faf0fff0faf0fafafaf0fafafaf0faf0faf0faf0faf0f0f0faf0f0f0faeafaeafaeafaeafaccfaccfaccfaccfac8fac8fac8fac8fabafabafabafabafaaaff00faaaff00faaafafafaaafafafaaafaaafaaafaaafaaaf000faaaf000faaaaaaafaaaaaaa else 0xffeeff00ffeeff00ffeeeeeeffeeeeeeffeeee00ffeeee00ffee0000ffee0000ffecffecffecffecffe0ffe0ffe0ffe0ffcfff00ffcfff00ffcf0000ffcf0000ffccffccffccffccffccff88ffccff88ffccff00ffccff00ffccccccffccccccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffafff00ffafff00ffafaf00ffafaf00ffafaaaaffafaaaaffaaffaaffaaffaaffaaffa0ffaaffa0ffaaff88ffaaff88ffaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaafaaffaaafaaffaaaaaaffaaaaaaffaaaa00ffaaaa00ffa8ffa8ffa8ffa8ffa0fff0ffa0fff0ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ffa0a0a0ffa0a0a0ff88ff88ff88ff88ff88ff00ff88ff00ff888888ff888888ff80ff80ff80ff80ff770000ff770000ff70ff70ff70ff70ff55ff00ff55ff00ff50ff50ff50ff50ff44ff00ff44ff00ff33ff00ff33ff00ff30fff0ff30fff0ff30ff30ff30ff30ff22ff22ff22ff22ff22ff00ff22ff00ff222222ff222222ff20ffa0ff20ffa0ff20ff20ff20ff20ff0ffff0ff0ffff0ff0fff08ff0fff08ff0fff00ff0fff00ff0f0f00ff0f0f00ff0f0000ff0f0000ff0cff0cff0cff0cff0cff00ff0cff00ff0aff0aff0aff0aff0aff00ff0aff00ff08ff08ff08ff08ff05ff00ff05ff00ff03ff00ff03ff00ff00fff0ff00fff0ff00ffc0ff00ffc0ff00ffaaff00ffaa) else (if page < 13 then 0xffffa020ffffa020ffffa000ffffa000ffff8f00ffff8f00ffff88f8ffff88f8ffff88a8ffff88a8ffff8888ffff8888ffff8880ffff8880ffff8800ffff8800ffff80f0ffff80f0ffff80a0ffff80a0ffff8088ffff8088ffff8080ffff8080ffff8000ffff8000ffff4040ffff4040ffff3300ffff3300ffff3030ffff3030ffff2222ffff2222ffff2220ffff2220ffff20f0ffff20f0ffff20a0ffff20a0ffff2030ffff2030ffff2020ffff2020ffff2000ffff2000ffff0ff0ffff0ff0ffff0f50ffff0f50ffff0f00ffff0f00ffff0a0affff0a0affff0888ffff0888ffff0808ffff0808ffff0500ffff0500ffff00f8ffff00f8ffff00f0ffff00f0ffff00e0ffff00e0ffff00c0ffff00c0ffff00b0ffff00b0ffff00aaffff00aaffff00a8ffff00a8ffff00a0ffff00a0ffff0088ffff0088ffff0080ffff0080ffff0070ffff0070ffff0050ffff0050ffff0030ffff0030ffff0020ffff0020ffff0010ffff0010ffff0008ffff0008ffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffafffafffafffafffafff0fffafff0fffafafafffafafafff8fff8fff8fff8fff3fff0fff3fff0fff2fff2fff2fff2fff0fffafff0fffafff0fff0fff0fff0fff0ff00fff0ff00fff0faf0fff0faf0fff0f3f0fff0f3f0fff0f0f0fff0f0f0fff00ff0fff00ff0fff00000fff00000ffeeffeeffeeffee else 0xfffffffafffffffafffffff0fffffff0ffffffa0ffffffa0ffffff00ffffff00fffffcfcfffffcfcfffffafafffffafafffff8f8fffff8f8fffff0f0fffff0f0fffff000fffff000ffffeeeeffffeeeeffffeee0ffffeee0ffffee88ffffee88ffffee00ffffee00ffffececffffececffffec00ffffec00ffffeac0ffffeac0ffffe8e8ffffe8e8ffffe0f0ffffe0f0ffffe0e0ffffe0e0ffffe0a0ffffe0a0ffffe000ffffe000ffffcff0ffffcff0ffffcfc0ffffcfc0ffffcf00ffffcf00ffffccccffffccccffffccc0ffffccc0ffffcc80ffffcc80ffffcc00ffffcc00ffffc8c8ffffc8c8ffffc0f0ffffc0f0ffffc0c0ffffc0c0ffffc000ffffc000ffffaff0ffffaff0ffffaf00ffffaf00ffffaafaffffaafaffffaaf0ffffaaf0ffffaaaaffffaaaaffffaaa8ffffaaa8ffffaaa0ffffaaa0ffffaa88ffffaa88ffffaa00ffffaa00ffffa8a8ffffa8a8ffffa8a0ffffa8a0ffffa888ffffa888ffffa2a0ffffa2a0ffffa0f0ffffa0f0ffffa0e0ffffa0e0ffffa0b0ffffa0b0ffffa0a8ffffa0a8ffffa0a0ffffa0a0ffffa080ffffa080)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xdc69da0371a7468dc6a05d368a7d74d769f5d371a7974dc69d5d37174d74 else 0
  | 3 => if page < 3 then (if page < 1 then 0xcd604664902332181198dc08cc660466250232a981293d40948aa04a6b501320467b1b7d565dbeaa2edf50176fa78bb8d3a5dbe9d2d994e969f7da3b7ba65bd1c42ee3400f668ec7934763dbe3a1e4d180f278b87b7c583dc62b1ecd090f518487934243da20d1ea5068f288347b7c183dc60b1edf040f7181c702269881111c40860e3262a87ae94c3dbca51ee2520e041ff1b88ee3c1c771c1a3b8e071dc74e8e91a745c8d3a1ec6040cd90202ecdc69d08017e9c00bbce0047b30023498010acc002b26000ee7 else (if page < 2 then 0xd2edf8109a55bf021341b7e0426756fc084ceade8109b7dbb02133ab7204267566c084ceacc81099d58b021323b16042675614084ceabe81099d57b0212df8ee0486751dc088b7e29812185c510242df89a048675134088c662681116fc2502433a84a04467507c088c2e0d81217bd4efbc307a7df786b57bd4c1dc75aa7c3ace0f4f8771c1e9d0ed783d3a1dbf03a743b7d3b090771a760d0ee34ec0e1b7e0444219d40888233a8110c4633022188b7e0430219d4086022f6810b98675021728d5a042cd16fc083f433a8107e4675020fa8dbe9d1a09b8c0e340b6fa745a0cf9020768b7e040ec9b7d3a170726a742e0edf4e81010036281180069b023000d26046001a3c08c00342811800679023000cee0460019d408c else 0xceadf9f204ceb0783604ceadf8110ccea044650cdbe9da024ddbee893604d26e493604d9edf93604d9adf93604d82df93604)) else 0
  | 4 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x3376666ccbd993b323663ecc6d98bb30b660ecc0d97fb2f365d6cb9d971b2d765a6cb0d95db2ab6546ca3f143e283c4f789df135e267c4c7896f129e24fc497887790de20b640ec80d8fdb1ef63cec74b8e7b1a3c337865f0c8f189e2e5c5bb896f12ae245c47b884f105e1fbc3b7874f0e1e183e159801f else 0x87370d6e18dc2b784b708ee0fdc11b815ed375a67b43b67b6ceed9bdb3576636cbed96db29b64b6c86d877b0975f9eb9f968f2b3e5636abf956f2abe553ca8f94fba6be4c3c8ebd16da29b44f6896d11da21b43f6876d0dda19b42f6856d08da0fb413c81f4e8b9cfd397a72bce3e9c4f387a7074d5d9a7b) else (if page < 3 then 0xd09fa0bf407e7efcf9f9e3f3b7e74fce5f9bbf367e6afcd1f99bf2e7e5afcb1f95bf2a7e52fca1f923f217e40fc7df8ebf1b7e34fc65f8c3f177e2afc51f89bf127d0f7a12f3d5e77bced79aaf34de68bc99b92b71f5e3cdc77b8eb71c6e36dc6578c6f186e2fdc5578a7713ee26dc4bb88f7116e21dc41b else 0x1d82e3d98159e470a9720054b7fc22e3fc1171fc08b902041c81019e3f80cf20405792e822bbe4113d98089e0d02e70a0113ac8073c020372040139a4c08ccea04663302336fa74b934243ca20d1edf040f7181c600541d0029ee8014ef40080fa003f3d001f8e800f8f4007c3a003dfd001eee800f6f4007b3a003c9d001e3e800f1740074fa00385d001bfe800df74006f7a00379d003687801b1bc00d85e006c0f0035f7801af3c00d3de0069af0034c7801a4bc00d21e0068ef003467801a2bc00d11e00686f)) else (if page < 6 then (if page < 5 then 0xa745accae2d4f71168fb78b47b305a3d962d1e1416a7b78b277d452e3e829728a14b5448a5a8104ce6de251ef3128fb78927dbc463ede229df511392e882b8fc415d041ececc0f4f6507a78b83d9c2a1ece120f670687b381c3d994c1ecc750f663a87a7aa03b38bc1d9dfd0ddd5286eb974375dea1b9ecc0dcf6206e781034e53a1766b00b975785cbaa02e9d34172e990b973f85d39742e5cb8172e5b0b977f85c7bc02e3d9c171ecc0b8f6585c78542e9c28174e090ba66785cb3382e5956174c760ba63b05cb else 0x4009971ea4ce8f4267474932e39499e1ca4cb8cb267465133a30099d64c4c3a0425b8dc92dca9893d6ae49bb4a24dc5a927ad5891769248bb3a245d8c922e74891d3ea40e5fe1fb2f80fd9bfc7e99063f4f601e97900f4bc1c789e0e3a4e3f1d27068e9381c749d3a3472121a34348d1cdc4643ede321f07190f590c87dbc633cbc312e5718a72b8c4bdbc623d64311e1218a7090c4b820625ede2e9e9617272b8b93dc45c3ede2e1f6b170f900b87b285c3c802e4e3f1727068b9381c5c99662e4f6f16cf650b67) else (if page < 7 then 0xd14b35e6459af202cd78f166bc58b35b9659af072be7b79553c1caa9d84554dc72aa6761553364aa9e0e54ce6d2a67b79513c1ca79d8453cf7129a78394d395ca69eb6531f26298ee614d3dbca43d44506aa12835ab940e364a0b1965068c028356513ce7f899e3e04cf2f5266d791336bc499b5d44cdae2266d6f9336b7899b5ae4cdad2266d681336b3099b5904cdac2266d5f1336d509976824cbb3a265d90132e96c9974884cea40267510933a84899d3ae4cb9d02674e7933a6dc99e32e4ce910267486133a else (if page < 8 then 0xbe4c09dea604ef23027789813ba8c09dc4604edf30276f1813b5cc09da0604ecc3027641813b08c09d82604f573017aa180bd28c05e82602f3a301793180bc80c05df0602eb43027599813990c09cb6602e143026ed180b760c09b706065a33026b7181a588c0d2aa60691c30168d1813464c09a04602d0030167c98133b4c099d2602ce5303272980b364c09e405f2f4a2e96fe973abd8b99e825caf3a2e566c1733800b5d6ae5aadf72cf4f4967a748b3d2f259eb602cd7ae166bd64b35eac59af552cd7aa166b else 0x81121e41a8dce044638ff2219ba9109dbe884ede44279d220b469109bea8665f04333a5218bd050c5e7a862f3a43179c218bcd10c5e54862f26431791a18bc810c5e32862f1743175c2193add0c9d66864e7543270a219369d0c9a3c864d1a43268ca193465089e0e834e7841a69420bc81103e67481b52840f8862079ac8ea3bfa72f1fd395d7a9cb5bd4e53c1a6e4f203517839a337cccbd3e465eb5732d75999737f4c0d3e66069f23034f4981a7a0c0d3126069813034bc981aa90c0cbfc6065f53032f81819)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x95e0d9ecd069f51834f9441a7c9a0d3c2b06cf0782e7b7c167c1e0a9edf042f6f820fb8c0e7dbe073d99039e0d7da7543bd3851de9e40d02f0767e77ab2f3b5d979b46cbcf5465579932abc81955e0ec9cf0763e7b7b107dbd873d64c39f6f614f2eafabb317d3e9cb93a045a7906acd38115ce38cae720456b952aababd555b598aadac8556d322ab685155b4f8a9eb3a54dd91aa6edbd4e3cbaa6ae7f52a72ea94b96d4a5d98a51e1452a6ff28bc71545e408a1f2044cf902259c7f92be4089572044a38f2251c else 0xc9a2e3e1b16cf078b67b5c56bdbe2b3dbf14cf0b8a2783c513b7e269e75132f1989976dc4cbbd6219d8510cef287e76143f3d521f5e410faf1e87d783c373c1e179e0f0b4f0785672bc2b3c1e139ee3094f6f84a7934253c1e129e0d094eea84a7714253b7e129dad094ed484a7664253b0a129d7f094ebc84a7a5424bd06125e75092f26849790424b96e125caf094f26848f0ac253852129e0f084f3a83d783c1d3d520e5ee306cf28836786c1b3c2e0d9e1506cf0783678141b3ab60d9d1906ce78836736c1b3) else (if page < 12 then 0xceadc3e696e1f4ab4cfa75a47cbed23edf689f41b3cf9559e7ceacd3ed3661f4eb30fa55987d06cc3e75661f2fb30f935987bbacc3dcd661f4ab1cf9358e7d3ac63e4b631f3ab14f91d8a7d3ac33e99611f4ab08fa0d847ceac23e4d611f4ab00f935807d06bf3e755f1f3aaf4faa5787c9a823edf401f209217b7c773c1e3b9df51dcee28ee77e476bc1e359e4d1a9f078ce72bc653dbe309e0f184eea8c2771c613b8a309db3184ec28c27b8c5d3c1e2e9de5174ed88ba76145d3d522e5e41172f168b972bc5d3 else 0xcd1f06e54f837267c1b903e0dc69f06d6cf856b37c2b1dbe198e5f0cc48f866147c2b093e19849eecdc4f6d7417b5b9f3dad7f9cfcbe0e76754705b6fb815af9c0ae74e036966fb329b7d9b89bead84df56bf6faba0b7cdad9bead66df56426fb3b4dfe7dbefe3ec17d1f66bb4faddda7d46ed3e9d761f4ebacfabdd47d3aea3e95751f6fba4fb7dd07dbee73ee3731f6fb98fb7dca7d26e43eb1711f57b88faa5c47d32e23e95711f41b88fa0dc27dbee03e976f9f4ab7cfa0dbe7ceadf3e756f1f6fb74fa0db87)) else (if page < 15 then (if page < 14 then 0x8103908996fc080cd2be81019a67502032c912040671022180ce33a8101666750202acd3a0403999d40807334e7f80e66df038103ceadf81099d408862000a7680e00185c09c0028e81380050d0270009f204e0013cc09c002748138004a3027000c3df7e00153befc002a77a780053ef4f0007d5e9e000f83d3c0029f79b800408f2f000811e4e000f8341c002046738003e0bef00070579e001aa53ed00353a7da006d74eb400daa9d68014ec25900356811a00693023400cea0468018cc08d002ed7e6a005c4fcd400d31f968012bbe39002a27c320052cf86400a29f0c8013e3e19002627c32004aef8640094df0c801b23e0d003607c1a006aef83400d51f06801a53e0d003497c1a00682f83400cf9f068019d3e0d else 0xceadf244da75a4489b4eb3091367486122a811281fb153d2c3d627c8107ac675020f4ca9de91eb183c1a344b6f81c6836df2f0c43aca5e1887b7c10310eb2820621edf4b0b43dbe481687b7c1a2d0f6f81c5a1ede598b43dc60d0f47b5c1a1e8f6a8343d1e0e3a87a3834750f47022501db2a781037c4f90206989f2040bb16fc0817533a8102e65674e85d1dbe820b87b7cfc170ec29742e1d672e85c3b0a5b0b8759cb6170ecc8fc2e1edf1705c3dae140b87b8c24170f6f8482e1ee30685c3dbe0d0b879341a170f6f81c2e1e4d0385c3be4b30b87b794c170f6f1d82e1c1a3b05c3dc60d0ac76fc0815533a8102a65bf020454afa0408a99d40811332f8102265d4ff0454d39fe089975524114b07a082293fc7a0458) else (if page < 16 then 0xc66044a191dc0894622681128c4250225189f20448319d4089032044a110c5bf0221989f20443319d40886333a8110c4e756fa183dbeb243070225086633a4650c1a388ca183cea0440d99d25081b20443103c250862078c1e9f36e3b7d64658f5a7f4c0c5eafe9812d69fd3015ad5ea600f6fac8c01c089418187f4d93025023725ce36fac8b51cf9021678cea042cd94b3e059e2a77a4b3c52cea1678d51e92cd50235a59e354a9cb34e41539669c1e9f2ce36138259c76b704b34ea9791663daeba2cc7b5d66598f71ac8b31bd2761672d50ec2cc783d3e53476fac8a035eb529332d6af5264db5c7e4cab078349995ea6f1326bd4c026646c9804ccb6fac893367502122ca59f02471a738048b34eba89136df731226 else (if page < 17 then 0xcea9681199d4f90232df8a204a5bf06c094cea0d811983deefbd2a7a59e9c6a953bd2ca9e047a713e408f2e27c811dec675023bcca9e045f71b7de9539754bcaa72edfad53e5c1e9d8363b7d3b06976fa76072ecd7bc085d6af5810bb7de902173ab7e042eb5664085c1e0d7e63a0d2cf82741b89f02edf593e05c1e0d7c2383c1af6c74abb68a1e756fcf83dbf4e8487b8e9d068f71c820d1edf9041a3d33078347a0e0f068f3ec1e0d1e7583c1a3ca30783479060f068f71c060d1e0f2dc1a3dbe408347b8c7f068f6faca081ee383c0e3daf0781c7b7e07038f6f84a071ee306c0e3bb696592583d04b24a7c8115cc693022b8cdbe0d52873e4089fe33a8113f66c102250cd06044a199d40894333481128664102250c else 0x6dfad5db02133ab7e044a0983c1b022510cea044a10c440894232864000dbb4e8118006b5a7408c0036ccea046001b5e75023000da73a81180069d9d408c0035ac720460019d60f023000ceab18118006ad4b408c))))) else 0
  | 5 => if page < 23 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x5be0a7c13f825f047e087c0ff81df037e067c0af813f023e03fc06f80bf013e01fc02f803fa77afcf5f0ebdbd6fbbb03f4c7e92fd15fa0bf3e7e74fcd1f953f207e34fc65f8abe3bdc61b89b710ee12db2fb557c886d0cda07d397a72bccbd981b2e765aecaad941e267c49f87ed8d1e189e2e5c3b7801f else 0x8efc6fe33f17f8afc4fe23f09f7efbe7debef1f68fb17d77eb9f5afabfd57ea9f53fa97d43e9ff4efa6fd33e8df45fa27d0fe81f3ef9efcefe6ff36f9afcd3e65f31f97fcbbe5bf2cf95fcabe53f28f937c97e49f23f917c87e41f1ff8f7c77e39f1bf8d7c67e31f) else (if page < 3 then 0x9b7e5bf967e57f957e53f947e4df927e47f917e43f907e3ff8dfe2ff8afe21f867e13f837e07f737dcbf727dbff6efdb9f6dfdb5f6b7da9f697da3f687d97f627d87f607d7df5efd77f5cfd6ff5b7d6bf59fd65f57fd5bf557d53f53fd4df527d41f4e7d37f4cfd2ff4afd27f48fd1ff else (if page < 4 then 0xd2ff49fd17f41fcfff39fccff2ffcaff27fc8ff1ffc2ff07fc07efffbefef9fbdfef5fbcfef1fbbfeedfbafee5fb4fecffb37ecbfb27ec7faf7ebbfae7eb7fad7eabfa9fea5fa87e9dfa67e97fa57e93fa47e8ffa37e8bfa27e87fa17e83fa07e7ff9f7e7bf9e7e77f9d7e73f9c7e6ff else 0x9b7f367e6bfccff99bf32fe63fcc5f987f307e5ffcb5f963f2bfe56fcabf94ff297e51fca1f93ff277e4bfc93f923f1dfe37fc6bf8cff187e2efc5bf8aff147e26fc43f87ff0f7e1dfc37f867f09fe12fc21f83bf06fe0bfc15f81ff037e04fbeff7dbef5fdeafbd3f79fef37de1fbc1f77feef7ddcfbb7f))) else (if page < 8 then (if page < 6 then 0xd50b35e4059af0729a77a933630099d67448bb6f188f590c47dbc5a3c1a1ece5d0b972d85cbb302e3c28174dfe08b902033ccea046001b97c00dc7e00621f0030ef80186fc00c33e00617f0030af80184fc00c23e0060ff00305f801827c00c0fe00563f002aef80156fc00ab3e00539f0029bf8014c7c00a5fe0052df00295f8014a7c00a4fe0051df0028df801467c00a2fe00515f00289f801447c00a1be0050bf00283f801417c00a07e00501f0027df8013e7c009efe004f3f00278f801387c009bfe004ddf else (if page < 7 then 0x1c011d8dc08bc5f045fab81ef27c0ff4080775fe03bae001ddd380e7e74073f2f039eea81cf6d80eeade0778fc03bc7d81cf3bc0eed2c046f20021f59811792008dc24046e0d023659811b1c408d8d4046e0401bda700cfd28067e38033eb501aeb880de3f806f1f0035c9101bd3e409ca9de9e6750236967c33a0be0dd3aea3edf731f41b88f9d5be7d3acc3e0f174f6f84a783c253b0a129ee306cf0783672bc1b3c9a0d3edf039e04573902251cce90c5a32864e0440f894207c7f4c0d5ea604cd93026f4967a else 0x3ec2279ea116cf408b678845d3c022e9d2113cca08b660045b27c22f13211789108bc48045e21422f0ce117839089f9303af5f41cf3e00e75be073b4b039b94c1cddc40e5ec2072f5f8397d041c7d6c0e5eb3072f21039b6e01cead80e7902071e8083973d01cd9e60e6cf2073b02033d70019edbe0cdebe066f9d032f91019dada0cf91c065e86033b26419f1220cfb3a059e8602dbd5c127994096dc1047b4b023bb0811bd7808df6f045fb5822fd50117e6008beba046f59823791811db9408bdb5047a79823b)) else (if page < 9 then 0x9002bd8ea15bc5f0adfb4854fd382a7c7e153cde0a9e42854f0b82a7bd214fa8208bd02045e7f822f3fa1179fb08bcfd045e7a422f3ac1179d508bcc1045e5f422f2f41179fe08baf8045d6f822edea115ef208af750457b8822bdbe115ecc08af610457afc22bd7c115f54089fa7044fd04227e74113f2f089f90044fc70227d46113e73089f2d844f91022dc86116e4008b709045b754227b6e11757008bcb7845e5b422f2d611796a08bca9845e470227a18116d00089e7f845e3fc2279fa1178fc08bc7d845e else (if page < 10 then 0xb302e7d94173eb90baf5a05d7acc2ebcba173e5b0b9f2405db9142edc82176e400bb71f85db8b82edc3e176e140bb70a05d78482edc1a176e070bb6fd05cf6802edb2a176d8e0bb6c685db6342e7b18176d8b0bb6c305cf5b82ef238173d190bae8605db3b82e79d8175ce90b9e6c85d73502ed994176cc00bb65985db2c42ed94c176ca20bbc4f85de2642ef0f4176c750bb63a85cf1c82ed8e4173c710bb63885cf1bc2ed8dc173c6d0bb63605db1ac2ed8c2173c600b9e2f85cfb082bbed615bf6a0adf90056f else 0x3e052f1ee29789114bd6509efbb43dbd841edf710f5fb587af8fc3ddc1a1edcb30f7758876fa583b7c081dbe040dfd5386fbdbc377eda1bbf6b0ddfa706ef6d03779f61bbcb30df64886fea2836dcf81a6dfe0bbafa85dd7c02eeb7c1776b10bb74b05dba482edd22176e900bb74785dba282edd04176e7e0bb73e05db9882edcba176e5b0bb72c85db95c2edca6176eea0baf7105d7b7c2ebd98175ec20baf5f85d7af02ebee2173f6f0b9fb585cfda82e7e94173f410b9f9d05cfcc42e7e60173f260b9f9005cf)))) else (if page < 17 then (if page < 14 then (if page < 12 then 0xd04917e7448bf2a245f90122f84891db9e48edac247aae123e51491f25648f928247c86123b40c91f20648f4f6247c7a123b3c091e9de48f4c024764c923e3008cd932467a96227cd0113e7c089ed2c44ee622277a0912fca8897bb244ddce227697913e43089da0244dcf3227679113d28889f4083f6dfa1fb6ff0f9d3d07cdd4e3d75f01ebaea0f5dc1c7adbbc3d6d2f1ebd068d1e81c68f6de313eb2189f838b97ac85cbd2c2d6f6f169fb58b4facc5abc1a2d6e0716b6598b5ba5852f40829796014bcaf8a5e else (if page < 13 then 0x3acb3e9d659ecd92cee60167b70caad9ae556cc02a770914fba7ca6eede535f0729af6a14d76aca6d994536eb2283cd8141e6bca0f6d64cfb5a267da7133ec1c99f54e4cfaa5267d4b133e98c99f47e4cfa0d267d02133e7f499f3aa4cf9cd267cdb133e6d099f3524cf9a8267d7a93375a899f27e4cf928267c93933e3ec99f1e64cf8de267c60133e30099d9664cfb6f24fcdd127ec3891f52c48fa82247d3e123e9c491f4a648f9e9247ce8923e6b491f35848f9a0247cbe923e81091ebe048f5c0247baa122f else 0xa9cb3ed3e59f5f52cfaf8167d750b3eb8259f7712cf787167bc1cb3de0659eef22cf76c167bb24b3dd8459eea22cf74b167ba28b3dcf859ee722cf736167b988b3dcae59ee532cf7ad966fd5cb37ea859bf4a2cdfa0966fce8b37e5459bf262cdf90166fc54b37d7459deb32cef1c967b890b3dc2859de122cf6f4967b778b3dbb259ddce2cf6e4967b6ccb3db6259f5b12cf6d7167b6b4b3db5459eda92cf6c5167b5f4b3da9459ed312cfa98967b464b3ba1859ed012cee7d167b3e4b3b9e859ecf32cf6761677)) else (if page < 15 then 0x4a10cda4a866d2043368ca19743106dc0881f52840fbad1cbdd68e57b6872f5b4395f879b7da9cdbedda6ddeb1353b539a9d810d4ee0e6a6e8a34b759197b6c0cbdb5e65edfd303db7981bdacc0deb4606f4e303783981bbdcc0ddea606eed30376a981bac8c0dd4e606ea530374b181bbd4c0bc7e606e0d303702181b7f4c0db94606dc73036da981b6d0c0db60606daf3036d4981b6a0c0db44606d6a3036b0181b4fcc0da5c606d28303693981b364c0be9c5cedb92e772b96fbdbcb5db745aedf32cfcf4967e else (if page < 16 then 0xd513f7e949fbf414fdf9f27efce93f7e689fbf2a4fdf9327efc813f7e349fbeb64fef59a7f78e53fdc489fee144fef0927fb7653fbb9c9fedb24ffab0a7fe84938dd049bf9f04dfaf6a6fdb8937be829bbf3e4ddf02257ed392b7ad495fa044a3af8251d70128ee82943f3a4a1f9a250fc81287e32943e264a3709251b54d28f3e090767c4837a0a40fce9207e68903d6a443694221b49d10dede866f07433776a19bb7d0cddb4866eb243374b219b9f10cde74863e0d433702219b5810cda7e866d32433697a19b else 0x835dedd4ed07707683753b39da9d95ee0ecaee96657753afbbb097dbedebebf6b5f5f59afb7dad7b7eb4bd3f5a5e1f872c9ea5964f3f2b276ed592f712c97d31647d62ae7a96573d022b9e8115cebe0ae769657373e2b9bd255c7d44adeeed54fd4b2a7e81153ed4ea56e9652b771a957dbd4a7ed6a53e3f52b706a95ba5945f408a2facc516fa728af85145bcaea26e964ffd4127fe7cd3ff3d29ff9a04ffcbea7fe7d53febe09ff5ed4ffadf27fda893fdd2c9fee8a4ff73e27fb9893fdcae9fee534ff7aba7ef))) else (if page < 20 then (if page < 18 then 0xdc648de0f246f008ef776c77bbb635bddb186f6b8bb78745dbc1e2edd2d176f6f8baf83c5d7b8a2ebdd516dedf8a2fb5c3fbc1e1fdd2d0fef6f84b7b5c25bd3a12de0f096eed84b761425ba5a12dd07096e5d84b7b7c257c1e12bd85095f71836fb7c1b7c9a0dbe0f06df06836f7541b7b8a0dbdbf06ded6836f6a41b7b320dbd8506df41835f9f41afcea0d7e4106be5b835f2bc1b79020ddc2506ef6b81dfb540ef84a07dec1023f41811f9d408fc82047c77026e12813753bd3bd51e97d62ef6e9677b7b03bcf else (if page < 19 then 0xac9f0ed4ef876967c3b06be1d811f0ec1af6f6a77a7b023c3da9ddeebe0ef75f5777b023a9dd69c1ec08e0f75a703b53b81ddaf697ee3a73f6ed39fb5e9cfdab4e7eb5a73f70d05fb7e82fdaf417ecba0bf5ad05fa7682fdb33a7ed79d3f4ece9fad660fd3b307ed797bf5acbdfb8e40fdbf207ed7903f50c81fa7640fdbf1c7ed78e3f5ac71fa660efd07077e7583bf20c1dfabd2cfd5a967ea94b3f4aa59fa0d2cfcea967e4d4b3f22a59f9052cfbb68abe95453f6fa0af83d057cea7c7ddb365eed95efa74a6f else 0xdbc5f0b8f838be171ec217c2e3d662f85c78fc5f0b97090be172e0d17c2e59662f85cb1a85f0b8fb78b0171e0d0f02e9e0f068573dbe0d0acfad4081536044a02ae6b502045ca9e0408b9a7408113b6b8fc225e0f0684537f96a08b9752d4115b4e5a822740894045cd38fb089cb51f611396a3d022d2d478045c8109108b8e012211734e24422765e48844e75491089cdb12211720415822e40813845c811280679020440cf36b2cc115e9c4881ce8102203b9b7d64041f6f834089edf5900c7d6b4e81199d4089432044a10cc6df0685c30035aa7fa0053b06f400a7607e80187c09d002a7813a0053f0274009f204e80131409d00254813a0060efcf400dbdf0e80183be1d002fb7c3a005eef87400bb5f0e801713e1d)) else (if page < 21 then 0xce928245c9421848ea043bc91e25077923ca58b324754b16644ea9624489d408940f5ca58b31eb5b7d64311f6fac85a3edf590a47c1e0d0f67b5d2c1baea78102ecd854b05d3dbe960b97b5d2c172eb3a582e9edf7685c7dc6c20b8fb7d84171f6bb082e3edf5985c7daeb30b8f93566171f6fac82e3edf2405cbb0a3f0ba7b7c7e172f6b8fc2e5d671f85d3b0a120ba7b7c1a174f078342e9d850685d3dbe0d0b97b5c1a172f6a8342e5d670685d3dbe0d0b8f59c0e174e044a02ee6de6b85c7a9cb30bb2e09661766c22cc2e9ede5985cbdacb30b9798166172eb32cc2e9b945985cb6d4b30bb34b122176a0d1d42e5ede3885cbdac6e0b97660dc171ec21b82e3c7e3705cb8506e0ba70a0dc171e9617c2e5cba2f85cb else (if page < 22 then 0xa59f04ff3a0be09fb741a593f5e837127e7dbeb24fcf83c1a9fcf07835379e0f02251cac6044a394b40894727c81128e41b02251c811de4a399d40894373ab7d283e0f06a5138113f4a39022509072044a10ce408942199ce928431694232864e044a103e60f7b9b75c1e0d36e74b4086a72a7a58d4cbfada181ad69b430337ab68604f5a6d0c05b686c9813a5a042cf4f4b5259eb07a9cb3cd4f4b1679daf5a2cd7b5e9c59af6bac8b35edf591667c1e0d2ce753b5259e7546a4b35d2c9f967a811282cf9839f059cea73ccb3cba87996794bcf32cf4d49d859cf0735cb39e0f0694d3c1cb329a7ad3684cf2f56d099b6b4da132e6d0de265cda1804cea9681091e6d7a7122ed6b4e245d83c1a48ce964fc91d40894123c else 0xbde96813953d2d02736bd6a046eb5a7408da9e0477b3b7eb5769f6fd3aed3e0f76c5d3dc76b8367b7ed706cf71c1e0d9ed783c1b3dab078367a760f06cf0ec1e0d9e0f80c1b3c1e96836783d0506cf6fd3a0d3ed71fc1abdbe3f834f83c1b03cf6f836073e0f06c093c1eed592d83c1ab24ea78115ce54f4b2b9aa59f04ff953d2c9feb41a593f752d0227fa))))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0xac7f4b7e8afd05f9f3f367e62fcaff94ff247e2efc3ff84bf06fe07fc09f7a7eef7da0fb2bf5f7ebd7d64fab9f54fea57d45fa7ff4dfe95fd28fa41f433e6dfcd4f981f2cfe537c99f923f227e3d7c5af8a5f0f7e1bfc2ef857f0abe117c1cf833f047e077c08f80df7c3ba0bf3a7e40f84b6866cc0d933e else 0x15822f8a2117c2e08be13845f4fc1cf85c0e7c22073e94033f08819feb408fcb3047e17023fd680ef922077c2203bfb7811f0b808fede037c2201bf53c09ddaf4e7eb5a73f6f836f83c1b7a593ff3e09ff6964ff7a0a7ef81128ee74943d284336da181ba9cb3ee0e59ee962cf6d4967b3ccb3db684cfa96247d02123d4a091f1de48f6960bb76105d7dbc2e7ed6173eb30baf1f85db8342ed966176c6e0b9e2f85cf81022f69c113d6a08bc7d845e3ec227922117b07836702251c00371f801877c00c1fe00607f) else (if page < 3 then 0x4fc89f96644fc91227f020f5f2cc7afd642d7eb214bf8387bfa5837fede177f6b0bbfa705dfc1c2efdda177ec20bbf5985dfac82efd2c177e3f0bbf0685df8102efafa177d6c0bbeb505df5802efa7e177d280bbe6f05df35c2ef966177c910bbe3705df17c2ef8b0177c3c0bbf06857f0b82bfc08157f6b08bfad045fd3822fe0e117ea708bf4b045f94c22fc84117e3f08bf06845f81022fb80117db608beda045f6a422fad4117d3f08be94045f3ec22f9e6117cef08be6f045f2cc22f922117c5f08be2c045f else (if page < 4 then 0xc1d3ffdee9ffeed4fff7127ffac93ffd4e9ffe964fff06a7ff8113ffbe09ffdb04ffed4a7ff5813ffc1a9bfd3f4dff83a51fa5928fcf8947e0d4a3f02251f4fd28fa7e907d28483e94219fc1cdbfd2c6a7db4303fb7967fc1cb3fdee59feed2cff6a167fac8b3fd4e59fe962cff06967f810b3fb9059fdb02cfed4967f680b3fac059fd3f2cfe97967f4a0b3f9f059fcf32cfe6b967f834a6f966537db4267f83923fa9c91fd2c48fe62247f06923f81091fb9c48fda9247e9f923f4a091f9e648fcef247e59923f else 0xdc707fed783ff0ec1ffb7d2dfc3a96fe0f4b7ef7a5bf76d2dfac696fd4f4b7f6f923f76c5dfdae0dfed506ff4e837f83c1bfa5a0dfd0506fe3f837f06c0ffc1e04fd63027e96813f06c09f811defe0eb27ea7573fb7a7ff))) else 0
  | 7 => if page < 1 then 0x307fd2df837f027d3ffa51f2cfe48fc2ef845f else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x3c else 0
  | 3 => if page < 1 then 0x5011c33 else 0
  | 4 => if page < 1 then 0x16c4711c4711c330cc330cc330cc330cc330cc1f07c1f else 0
  | 5 => if page < 1 then 0x4711c4711c330cc330cc330cc330cc330cc330cc330cc1f0741d06c1f else 0
  | 6 => if page < 1 then 0x330cc330cc1f else 0
  | 7 => if page < 1 then 0x1f else 0
  | 8 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 8
  | 3 => 138
  | 4 => 1103
  | 5 => 1440
  | 6 => 284
  | 7 => 10
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
  | 2 => 5
  | 3 => 102
  | 4 => 753
  | 5 => 1063
  | 6 => 232
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 21
  | 3 => 366
  | 4 => 2712
  | 5 => 3835
  | 6 => 835
  | 7 => 48
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 8
  | 6 => 8
  | 7 => 5
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 7
  | 3 => 12
  | 4 => 15
  | 5 => 15
  | 6 => 13
  | 7 => 8
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x10e20 else 0
  | 3 => if page < 2 then (if page < 1 then 0xc011a06110b220e010f132309101f020a010403011c08000615000704021815090000100300010000070706040e000100000c1407000b001a02010509000002 else 0x2b1d230c17200b000f0e0800010024042b00060013000b089500320800000000381a00001d05) else 0
  | 4 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x1c000010e00080040459a0c480850604207007c2000400001001df0a00002800c483030c40004000830b2238006000000000050001404381 else (if page < 2 then 0x420080022400002000830010400001800a080009608041960a2408800044120029091162008d040000000001130218406000c1820418400 else 0xa040251600202000000c0a58488080008a4e0010202000014e2c28048741800800080020ca8202000821400080461000300380840008085)) else (if page < 4 then 0x1818d2c00205000048402041006800080062c280080818200089070d40006088c18308100040230001080028b020408500001020200480 else (if page < 5 then 0xc0089b0c4c20208085850614284022c08d0e00a01047c7810020008421460100106820800004060018900000070008206000c0850428000 else 0x201000112240000400002003400f0428000424038b181c4230004ca60a0078128195811c0860402001000c10788180028118801810a18706))) else (if page < 9 then (if page < 7 then 0x1820002442840a11481040890006200850400121001c0013c044810008311144de001421a8e0244180122cc010ee800400003020a2090a else (if page < 8 then 0x960c38a0c0418010000040014f0c22080803e0008006b81802034a800a0898a004012a2a04804560c90c1e0038006180033e300840400187 else 0x400c224c68200044842e30001001c18670004803624801020c003040c00a221820c02d8092923c0080c70a13183e6000a0c5822008000)) else (if page < 10 then 0x14384000e0080311203080000c000410181a0100331800700862c4aa04147063a5900a2a62a8102040080618380141430510006822c000ad else (if page < 11 then 0x2638792027c200360820730243220324d3022065ad083002be62c2800c80015080400b0440190680010414080007c7c00026000000e042c1 else 0xd0408027062c3004c10202120c0001648c2b1c1888a1015280100021eb04002e3c90801551405b0030c82)))) else 0
  | 5 => if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x10600001300080500020f0d050003000009000d000003010106040f0104010502021002030c0201000034010c080000010f0116090701000102000000010000 else 0x10000004010f0101040004030200000a010c050024001300140403040d040f070017020a00050309060d0304120301021b000f000517050004010e011c161b01) else (if page < 3 then 0x7041604020001000f000e07010106000000061b00010d010f0308000301070708020703030116000001000519030109000700000309030301000302060000 else 0x200070201000f0201060900010101040e040000000100031300010106030209161800170c02000a051a15000001020105000004012b02000201020001000502)) else (if page < 6 then (if page < 5 then 0x50c080d0010051002060210020c05001b0817080f060d13010006000b11060e04060506000b08310902052400030e000a00000500020000010112070201 else 0x30a040223021a010108010801010010070d01040d040203021201000b1a1e020104030011080e000c000000030123003b000109040905021700020a001b0405) else (if page < 7 then 0x2401060f0000052402010c1e05000301030829010100010d0401040203070101012501010007054e210002000e0101041808140002060a0702210e01060500 else 0x1800021802042d0413250d091d04080d1504130409270101020000180300001d0726070003070001023700070612070803020600140b00010504060602010900))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x7000302000105000b01030000040e12000d040b000007010006060100020005000115010000001505011000000005080702040200000100001300000002010d else 0x305001a0a1515002c000700040c000004010e05090006150b0026030002000221010508271c04002404002800051f0100110813070605001818030b02000203) else (if page < 11 then 0xd000804046634113b152e1917020000320704110b0023180c0431110a17053701020001040000160a0325010500020100010012000b1d1213000f0a0043070e else 0x210000018000e0f14150013af0000040c2d0305030823080f00090001090c021735030602000f0f150c04132c00050007091900000000021206040000110214)) else (if page < 14 then (if page < 13 then 0x100030000020f010b002a01000403000a1237000006000001000207052a04173602010402440600041324063b070604052e090c120c00000914182a0c0a1c01 else 0x2b0327020f0306500504020f110e021406124602090a053c8d060b1d0e06020325023c03124600174513150204152405091f02000202121e042c001603016300) else (if page < 15 then 0x100a19030c0400060300030e140b1f080904060b01052901010001000a0a0310111000000a000d06030500000014031102040417000c01120c04510100130014 else (if page < 16 then 0x12237e02500000000500004b0f000d00046b1c0340040003070918061c13121f010409020e070000110e040200001407202a00031d01190003002709013c0603 else 0x3f0000114b1d00003a2715130b000903080c24280a010819001400133e01042d050451000d0014))))) else 0
  | 6 => if page < 4 then (if page < 2 then (if page < 1 then 0x300010300030107050712011403001c00070004001a001517040f0302050301011d050001000001041200050004050300050005120014000101070100010a11 else 0x21106000006000101000f001402020b0d0d010007010c03060003080d000900000a0207062b02001500040d0a06040900100700290905010000000e0a230301) else (if page < 3 then 0xb00020a04070102092b0200033623090002000006001b000a0b1a0201100002010802021609080407060a15223c00020400050d0b0b110425041a0a07080500 else 0x1c2f320f04090f20061f0200000601359e0a0f0801031103030b0105000f0a1c0000051e05002204)) else 0
  | 7 => if page < 1 then 0x22180791003e31c0b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x602c00000a49200068c237000d90060002810 else 0
  | 3 => if page < 6 then (if page < 3 then (if page < 1 then 0x2012636308223e45927f21534800805f03c15b06b14b06d10106d02b30008400000c00000007630006561003913330423a42d65945e60001704f21508017605057117e34c51152c236a1e46d44a02d46a000000045b000000000000000890714 else (if page < 2 then 0x4201808504102038803926e14547d03421360000f00564567f055a6902f20905a04c03c07103d06941b15905e07807f36a44405814303064501a26f07c00000006267320000002f84d3000000000000000205636593000120024160510063366 else 0x4000700007300004717e25a50e070016b0b56c03b454a3502707315152c08534010a66163802d07700300f40205502f649630037028103b7c24315805312a07758231d17406482914700c47411c74f06346e04517530760910b60a406000015a)) else (if page < 4 then 0x8607a00007853b16067e01b03201d40002132e600000000000057054b7640000006660005f37a32f90406841756b06145c601a4116492f02a63123f12c34900000000440006108004f300356b7913b23e06f40a04041a37745400b05d6053000 else (if page < 5 then 0x4e63a04d000051463a57a5240000000000002e00000000006003670002f30004c32300000025a40005d00005c000021400000087067029256a0352027902460000002241264a48437b45362b67027b52834608125044574a10000814e04d6032 else 0xd07202e51404211d02005e41f07503751908525f60c64867b02226c10458304b12043b026a0001a02c67d15915605203f03103823d181368034303a5b44a625b530000))) else 0
  | 4 => if page < 43 then (if page < 21 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x500084e80000a417500000194800000000f86400011a17c00aa40cb9397226c624841eb42f66700df108e82e400bd410da0a824eb87a8f600d7b41d06dc0bcc5fa89b6082630848ae03e400f28f9e9380354113e2d9499020b4100005851fc0a1c43b002b587030f7100001ed52552c7149b6cb01e79a884 else 0x62870aec7a8195551480c699d88eb079e0dbc042a000060e600020292eb4470865d10d21deb00a861155420f46000000019980f9031450b4982022012a60bb0c1b5800035c281c00b98000116af96c5030000000077689102a600000fbc4f83afe08888000167d3d997e46ed99e230000166acc400003c80) else (if page < 3 then 0x78000fa12f23d234a06524e1d43b800000774162080007200ff80381449246c067289283c820000000000034a00000000215b00000000a505e5800000000a048a51b3b085860000c3d0000000112104e4af906d44afc60b09ac62480b640e8d973986f26fc50a03df85040af05ad2b429376c7e01288a183 else (if page < 4 then 0x1da4e354f8500007860040d7920000000031e8cc136d31860844dad12f555b007f89aa89dc042844588858260449f29c848428185272ab5c00000d56060ca4500623fb075a0f8ae19838a400e8ee80000145460c61a500002c0273c08e806f800f3043400c46c3053431661268cb53cea36147a58e582e75 else 0x1220000373b67933b4e20078083167eac8c51682081076a61f008b82a33454229099592a4414424ed40001af0052cc5640003d200000140df0832a054aad3987e9035a42082ed10153a0681604d0dce038a17560684521a35c652e02e113c89f5a7ee08281bba17e277e4b5802e22d23))) else (if page < 7 then (if page < 6 then 0x25e00001cd827b000000001b2827011ba408add7000000000c360970130000010e4c302838b29404e48f2da7435174000015416c02d2a1925f78000000000000b80198400003b01b6009727102000000043f25bc400000000d1087606a4182080ab778ce481b5908f30000228151a28c0390cdd00e1c0f02 else 0x859108006e00a914af600009e124a50e60c04d1588d20700c45114a99e306966a611e94b8504b6d0d8d09841804a20f341ad311f21a810005d18388402c864e88c5828841741d5978a29b40000e0800001d7022ca8e15639b3a02902d30068001ab612050c07d844105ea20000e0015f46bc0e10815236f3) else (if page < 8 then 0x1074a281aab0e930000338172b258b7f0494a494a8a4087e24e4c5d08d8330a4fa0107000b51a607259ddaad6170210680c0b179222a0db4000023111462a60946a43068180c54c8328c710000229c000190074b20001ef89ad0000000013439ad15a6254512c8273276c02688918000039e01f50315bec3 else (if page < 9 then 0x7c94338977492e628c44c0c0003250000079540004390718a7f5c530ab806960f98149a2be0810067405422bd466c022aca28a23773c44cc0dd0144000000001ac0203044aa9081170a8e080208bc0498373242647cc080aa1a147a10090e6d425041203cc17c02d1035ccf7420f827c434e01ae94380962 else 0x1048fe849e827b52c80126d0900000420093c000010f41e9000005409faa43c0704400043c300000f656700000000056506d5000058ae64400002a510000e7d89f9bf805e8a2cd00003dd60108e180940b872176200513901a5928c200000002e9400000001c98a394356d0a14235000055ee00005008000)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0x2e31685600009c194057ec2000032d0b810f8a0001f5d0f478920e0c1f4d11631b0111900003bf06aec000177aa0f9872c0000000019000000000a5100000000dfd8d301980862cef4215d00000000b5c585800002bc076686d000000000b3c0000249b0000c6cd0a511324f201801fb98000 else 0x35c0000000027b224090a28a6ac4b10000c5e01d485f983eca715e59261605b480420d816f081e00001201bff1860420680002d5100000000ea90b3000002b4400011210dd64ecd6381801614000000000fe284c22d44b001a926f409900760b7104d2e0000c3127d3372502d14fa000042b4000008d0513) else (if page < 13 then 0x12eed759f722f644cac0000f6187b00000c3a17e2800034e43d0529da7b36802cf04d7a2b702f223045b4b0be62006a50000043736da4eb00de38a080c4a5fe900518f00000be460fa2c81000090c1fa82ff057488cc56d9800033343c41ef826960f00655000040f317a09f48869a30252487198e183701 else (if page < 14 then 0x33f50551613bd0100006a8000019a463a4fe0e0a1bbd56226564c0003792346059d000002bb0001018080818fa74a60000c151b2067e0f581f58277138a08169d0ab2f5726505d015a25131324890800030007cf60000b382e230c7604081553a20378c0001baa11140000000000000000000fe89d482860 else 0x6ce6e800000023662c6e100d713340000007e4c03c02100000000ff037303d740000708367078e0054c000345060e00000118ba2151c21d0000041d139a03dc1e2201b30000000160900003e94bb4c00000007c9616c0210000088744d4db3333e13bb67084e5c876404748b0cda18000000000006120bb0))) else (if page < 18 then (if page < 16 then 0x3bd42b5037c80000000c68409834100000538c658155283843980b52ade100000cecb6b106008ac7819aa200000000000133100001580d54000007a221e0fcc000034572122e300d4cae123204a7405f5112004d66de8000000000000000b2880007428e45109533558102de89720a90200008e00cc80000 else (if page < 17 then 0x2fe4d3c0d49b4e37f807c6c8319e1b7508c400d6005953802389944a00213f20186565d3844000021458ba91660e2c00020b03d033ae40001e481b302d664408dc898a02ed68b4c00007b24908edd8bf38ef385a612181250000000112c01a882733a844280b08a606736664ac0000aa42482fd482919161 else 0x17d6589054101d454a04605ad004c469451141de0809506ae5b044e3a8402e40dac12b28f2662e8fd89d083e5000e22609f502686684219d98b8ab1772eaa0c9189a21171e24769518357709d43828d28202b06b6b80c2231e407c60a812230b17071cc1351498013661e03a81ed8c1c05f460000610b5f6)) else (if page < 19 then 0x29204f016202a547a8d0bc16db2ac035009e0d58384fa01e40c221180d2400000001308177245c06f40d7d08aa50a80d48000270262727c01902b35062400bc08f002f66f648d016d1ac002dec6fc01e599d274809aa8a780be56ac09dd8cd11c8305f20001c580a0256c09414f6d02b74a46692400040d0 else (if page < 20 then 0x5e0641558590cc0083669d9f6844b268ec6d4104500007068a4880f843f084c01a0400034e91780fb85ffa00004620a85063a281044c67d2de6ca3b04c528bc530000008062000000040200656c6509429380478082ec7c3021608f48a01c0018744fe2e9c053889437b130d40d95216089c6df919300289 else 0x1722c4a560b800035440fc886a3e90000113000003fd12faca5d00000d263720ad058682ee34ce2bdd5918000062e68cc0000000001c40000000000058450a987d0178100009bd4e750de005f048511d23b0080a23a58000031b762000010d03e0634645f09a9024ca7b022d8504393f27328fc419e83a45))))) else (if page < 32 then (if page < 26 then (if page < 23 then (if page < 22 then 0x4e6615880000c807f40d1c22100000164000006202d91634913800001aa976ac6edc00000000b2800007e808c200000001bbb08925dcb0e1e1bb0b0112f309c05f1000076a07e810b5143500004f9616b11cb2a449b8212023b4000092152fa8000102499da225000000007b420a029c40000e9d1e133c41 else 0x206c4644000000000001541cb03be55ba00000f10142000002e007780a342886c7254d00be12842000000011b57ec0ae047e100000000000000000002a24000000018d000001d680000f4001ca4a980001f0672800000e85800000000000000000013a80001e102c2100005b5000000007a0067a8e4c0000) else (if page < 24 then 0x8200f1817b03ce678071260f602c6667c04ccc000000000010b99a2b41c100000000c7024406280894c5f006d90000fb49a20000042a04d4005dbe9b03ccbc949e982340000d3e12d800107266324800014d06144ec816602fc465c0ab841bd9c093b4053451890e840000000000002ca436000000002a31 else (if page < 25 then 0x2a46df8400028ca79406040e8000006ac24d80415000023e0390000000007340d0000000000000017480000855000111943e2000082088fd400033f13aa01f90000000046840000305983200000001c0137707b8074c076800000000b80969990620000728103d109050a06f9df703760325400020202b91 else 0x4156000149980005e2ab24405a43d120c2da807184070000110480002e7482403ad11091f8a2b06d0821a0800000008f80bd8375078800ac8ca044960000f9c0000226081c678686300e837448806c00028515362ff109b98d905760c0918f00000000020dc9fb1aca3b73024cd890000586cd440a3899f4))) else (if page < 29 then (if page < 27 then 0x6de45054028132b000079a86e999a0782a35d800018c10d243c0000037802188add1dc8291300007ee9cc80ee062f500461611a1024209e817aa255b22c0c6c8cf81a9640d66881660bdc634d30c8ce38203159547201b102a521f486e840000c9179c0e601c0a2e0014644554d20203a632ae4448d018ca else (if page < 28 then 0x380e3fd43650f540000d65a0181fca25830290638090132f41dc0c6d0000238039d07e8aa7038810a182b9afb52762f040f659a7373a027840003e2a00010f848003a6100010f407c0b43014088444de91ef044403f8000038947bcc9fd40203a5500000000000000017c6000000039a3692000000001e80 else 0x181900002f880001dfb25f000c00001a7039f01ac652cca99072b6d663ed0d6b3da60f689ae838c9b8a892e5b44b4a0db07acc00010bca83041d200019b08000000077ee14b38a26fe049815f992fb48ea0000c49000000010748633a7403d626228000000004e0df8968a8000000000000001ff0)) else (if page < 30 then 0x2180dc0091338f085467501d818f80870c2cc4c2200000000af0154a3cca556833c1de000004560fb4e23905000000c14c0004342000073ea00000003dc06000ee412d57f202ee843a0852458af5d8f9d80e115a05904b3042923fa09b40fcd0f744e4a4a9060080001d420000cd513e255ae9140f7543c2 else (if page < 31 then 0x54c89fc0790169605603a405f3ba6069a4e96c06a890200005508d59354051e8fccda8000510000eed13650faa22a2d69062833906a8c709852200007b20670094a000005d24c182a2000070c8cb4222a21d2185629453b803825e6a5e80d58000059d488020480f213374c7c00001ac12260dc84879c430 else 0x18c28884a580310292a11d8f9d428428825a415952ff114010b400e032b021c67d813f909b51ec08d40a2820b02168eb194c825a37cd4ac597e99630061441001ab1d2a6fa043d4efd353236641c811c8276034620000be818ea5b80221440d86aa00002288a3809522eb44495bc83df606948324b631edb)))) else (if page < 37 then (if page < 34 then (if page < 33 then 0x62245b10fd835a34f00b0c974196d00000bbec6eb3b06091262687a8bf4026368f103b52df163e6530624894c24de48dc02a00be4150008c1ef01c5620eae3400f9a4ba210104c1e1b3b526c6cc9c0f31ade057c84250f3d8eb172a0a6c061034825448f880668a5f652a90141a3443e063a6ebcc4751c51 else 0x6862b9496d00c28660006104ad800009809701f90080a3f8e1a2db002b5163b0000000000006e40000000008170000e65400000004b141408ad9acda7702000106c8bf183c00000ab0000000001ec46ecbbe42e60000126209237784bd940000af15be0a7c19201c3689a48b49c4101040000d4c0c012020) else (if page < 35 then 0x1dc68c814b2149104141515ff101956c803ec5e4d22a01ba00c5c8700ab400009ec59e000006fc038800002e306d10f824df321807f280000cf013a021c20000a1305a069a000012bd3aa02942000000042e03ae697822500ed33b20a2017a1c3290c74b1dddb80c6b5d4a4a80e6d85a47aa0b3d000027a4 else (if page < 36 then 0x46003fc0588039b47e10a40e4811643d161554662a7222e94d6d89f828026584c840bc11ffb5b086b1d6a0114088c03a48a6b01d0878009e588180cb4b949425f5496e03fb40000db8236244a4f44dc5025b354c265ad9903da000000001d9804ba448a538021cb11078282350c158f1458ce9fcd0f99504 else 0x3883a916d32b6101a307984c280000000119a23830010000fbd0a3abf005c20635000000008440240ddea1f1070e00002208a8647220a88584cac56446c94d538800003174d84de6010d04e465f492b5a9e400008340fbd1c06150a072975a8000604aba4ddd19b8007d3110181811b410a00d522033370))) else (if page < 40 then (if page < 38 then 0x5044b2017da2e6212282190e0b0a307a2094800c040d40286a8002502b3a70741dd13c12960204c682d91022918680a750820a6500ecc21014509c2040ee0969af83f2202a2540a1f10ab160a407c800026395c409cc080a3d3000010cd996b1ca10f66d48920831191180e941cc8bae22232826cf50a3c5 else (if page < 39 then 0x20e049c015d035041e0ff41c982da285c440d00000d671740d3c99e99fea1e62000046d07547462f2115e1b1c8246800003e11970768099817a9aae78928fb00225134071c05c85d7835902ba08608bb840a07b6c0f40deb1bd12aa83281899a54b0b06330586016f172469465b9124605b60cd107004101 else 0x7763bc9dc11812000112018c2aaf622165ac104006ea6f42fa280001f5568845758a6044d02db49d40b2811716b431119c4813c370481fe92f097296ab40001840c3706fa480ddb3b12b108b4d5521930e5000010e98a2ab7c07f2aee4ce85000026e0888ced8198a6b0c5c6d8313d195288eb4d7ad3d40)) else (if page < 41 then 0x82891388000000078b2b941bd8000065009b8400000000f04a6cc6ec000074860e000000a112a40ff8d00020460000d180662000015c2f141cb82a4300000001ecb120079547f00e602b008221128434c90f18264000124aa4b370a800020c82aa445840000000000068e2102c000312320a023157e90000 else (if page < 42 then 0x7fe0369932300004f02eec07e0c07a298a66c08029d6439528640f7d80000000ae4197a2b716d0cb2113f10000880f0aa4a99bfd400006468000000055820000000000046c689cc92a443400000001eab00000ccc0001ec8800000010e64f933cba7ae0319033d157307b004a55e83db088006f651380900 else 0x2044bd40eb019350000568c2a0c0414ba046543701feb000006040003ec25a602dc000016842dc2f6180004300)))))) else 0
  | 5 => if page < 60 then (if page < 30 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x95c0cfe48b0000000013bc162356f397611b82308b28a8c26aaa9a9c1d40000001e86910ce56420fc558ca000073f61ec12a215f26ca0011800028e0512a6c2a7b01a20968c9d845a936e6ab80d3400002fe0826a000063326d35b92f9824f89d26122073868aab6a0456023844982ab0191000001dd0639 else (if page < 2 then 0x32001681582458e7b84e4200000000dcec00000002624b200000000052e20000bf800000000ae06b7007911d940000d10800038c268919183cc642c00002059838167209111ba452214d60ddca0c585618aeafd8544845c51280080496145e0000006c602800ca44c1579952a86196f414fc49e4b361 else 0x3e74cb801da0000350cc3195f4bbb16fd000015db0b569320f38191d395033a4c258391a22a4ae161c13f080004cac6dd08aa44d10eea0002562253092220ec64b0d2e17fc0f500880c2309a816746cd21dd91874000000030b90001008070b32ba6f275041308000095e9120000000002fe200000002f70)) else (if page < 5 then (if page < 4 then 0xac8405dbac90000a54e5e81c508b867dcac002c9338407981452a2a60f95526a0b0000000000e98a11815184630ce921027a04f6709423401d209940000028821701f8d518000025e3000063847122960125228800003c703c36000000000002e60e32c2a880008d682f127821cb046cf490058145d2 else 0x9e00054098a96b622a4580cfa23bc006a10b0006000005a803aa9208500081c08ce8000032074612b5a30123479e40df98000457393a870422319c4605cc5d55f619de03a826948000000040611ece8c042a651e2000000032f93b4400023781681ac540002ac4b4210d1600005a2d8100b8000009813ef1) else (if page < 6 then 0x6b4b58017f300003ce94580f4b0000000000004d304149f212b9882814c04aad50d044b23004bcd019a7f200005c62dd80ac3421050245bc6560800068b2000000008ba4926d9e1438393b1cac7f403d1005593809b8245855939314d7652283d841fa07719609849619a02b4c110912194a2d000ac190b0 else 0x9e4cb9007a350d01c74ac0ccf4840007d505c1e2839aa2f845a9210cc296b208ad061d084459464d0402e88f1096a693140000e0689a000014408000af002b1d8849c81a42866400c545f39c6228c0fdb326a89ab1b121b30b325406c202ce028f08314b4197cb3f04a1820002b180ea659c60001f0030c0))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x86ecfec91f83f5069924445ae32de957295f849684e6a9b008029488193443a130c1f784200992cd5d8a5806a00c207e8967b279442a53dc16b028a260e06d81a3928653b480b4a26003607b60acc50e225d418002941831aaa018ecc789ee844372ac09355033a2da4a0144190001bda3a4261819050c10 else 0x380200018d518e072d6000117037464615524288b12e200015d4c9b04ea0237517415a900002a06e96d9002fa56642f282b6919001620ad80bc9b140a86c6e50130ab167572b0cdf60b22a374304edc082112b281039a620033337c013407bc0b3344a124828e80c2aa7041c053a842605ec06685b718354) else (if page < 10 then 0x256478968a3464457640002b61a4833ac91282ac880002d82f6441facc6068c000000003a70b2e4c24236044f04640ab92b412bc5296c8e89bd80c0103c2fdd9c5d5733000164c000029922646c70a54080002fac8a013780d424b2000000000fa0000000005984741972118065801e097ae65a580000521 else 0x95740002104800063f52ed8809ac910d3691c011014a02d4349800001de68b613e81f1236d80000000045836c030e232247834e10580600004b5c4000000e46c7b120204eec000000039901168000000045d3000146880f0000000008680d78800037d65c100001ad1aca60000b5893534acd06c00002ac4)) else (if page < 13 then (if page < 12 then 0x4e80000000000002ce200000004cc0000146802f2000000003bc10b89cc0000134800004ea4151495d860b3c2070e103cc2a911d12560d6d8b6810004528fec5c589a1072741dad5680021b3a87a802d837190ae2e76ea40398b82ea8e109c4843095b02f1a5d0064b2ec0f3025981b101d20a28468b2ea0 else 0xb101c902bf99d20000000000000cecbdd40002ae1604c00017e0800000000900000000090ac88900002130068082023852ec0272082c0d4820d288c400021d40c536dc0495d6b3039b9960e22e56037067220f001300af4276013b812eb4af037cb4b597d2575290e544da7ca053a52a8000276345e3) else (if page < 14 then 0x8c0127d1472c1801976f109b00baa948a27e488d907d24b8c80403a0d5906c708a04e3218c24ecd1fc0e5041400000ddcc5e556662ee0a4503d3574480f0d906169000094e817050d54fb08ba29455a7817a157602a825882b4000007f580004870000060025b826639d0200000000000000025a97283f18 else 0x790d29043fdbf006f6c732800038b0700c57092d84a60000064800000000444263441f3000009e2c3c177335e09560c90274a3bc182cb01da42028e429e60000a800000414905549c03cc16594955400034f661ccef0c0003799aa6c03a86db0d6992e0acc1071024197e139483d044716e1284194a09550)))) else (if page < 22 then (if page < 18 then (if page < 16 then 0x94083cc1b0349a20000000017853f6370d111a50a2fe1a740918062baf040714cd48d31b8a061c0d6008f10b5494e09cc1df0347384a74b1a65c47c2b04c000000008548ae800026c828508fa5134ca01b521b0807c5aa7849717fa282d11e91d544a8d5318ef393200f6aa6052529fca6360cd00d401262 else (if page < 17 then 0x241010440000f7c09430ad2ada000000001bb400015ac017003709280725abf81322932c5f00b5a252198012681400b89b99661646788abe097121eee6632c8300001c4e168000000005f856502a8000000001452166100000001f0300005decc4858ed076a606cd8d800000000000000097a8000 else 0x1d6d214936a9d24734049c0000318a14f513c5ae04a1a0000e4a473b386b6f2cca02ab30000000000006803be192c816400aa1751996d0ed82404481000029286acd2c406c2e62acd180009b600000bfb000020460000000000055a3220400007da042000008d1bcc206e30fc00000000000156640003132)) else (if page < 20 then (if page < 19 then 0xbe0a248ec055f63922854c00017431e82000014cc8e7a84104025000e4a078c240d3a08000382c00008cb0c146c40e36c6f2a8a000005f9800018f077a00e817900000000072d84cdaca65388ac41c4509199840000000018a053202b94000000015344fa68e04b7637f6f2ccec2561030a0a6810da38e0 else 0x3e684b48b284123aba200011da36133d81314292ace404e410459e1bc7936ae15d40ffd47145f000001f980000ae2503002124d6077e522e29f83c036320cdc01003e30a4214180258aed05f601cc1448bdb1a12b0fc929b1b5089cb675e8805130000100221a80000498083e9e6389068d48fc85aa824d0) else (if page < 21 then 0xa180864279820d0024a58cd8f39f50aee5630000057b39b630c999b180004d435149f7048b17f20d4c051300000000155233032b07ce10b820d50cfb6f30a24c7e01f3000006b9800049a1634418c0000000083d454c9368800045e01ea601128041334518a870ac701af46a45dd0114202a40002c4002b0 else 0x60d5c9a92093c24fca8fc64f29910018f3b6aa1323f2a3c0ccc1fa1b8d0464945c1a3c378083214e028a0183b8720c55069d4cf663c092c26e02e035b4ab7412c0a715850165818e810836ea14f40eb829701eae5842a3a3980602d18853092b564beb3200c59bfd03843444222811d479a4dc5a2203e80))) else (if page < 26 then (if page < 24 then (if page < 23 then 0xaa0bed954859f346804442a22984082b764009d21f608a80f7440000000a8a000020a2ae0018c0e26993945e22b411b9ded096410fd621c2333220053814bc060915d01932b402908cb36960d41c00002f435b2a8189ea0c9b4000138118cd4de0b220a4c1c24a7f06e0052000000000002285d13d82f36 else 0xab4313514204a212de000020300d934880564ab302cf045e2f6513a28ce010d4dd60a3929e0080200009a00ca93ca000000004d12000000000000479000088496f8000089e53f02ae4b9307400d4015ac013b41200000342a9d03ea86080565359400000001aa058f024e46c69e032df650c1560178324b5) else (if page < 25 then 0x87400001f1a19146cc08d12aa827809b230b0856813e31c28dd457e8c4a18520df1853326c0214d018c0005732b3005c4297b26467336000133a851139829c0018947aa3dc0a845af884020d626b407730d907becc6ea15043968ce000005a0195005a6f10c000000003e0a81400016139aa2e9e9f504bc0 else 0x444eef0a548000050e8b1c400000004440570e2fa9fe20000000000034a1000155451824b266ef211adb38000000013381dc800003f051004a2952c0000000017f854922f060000fa88c52a9c21741020534999cccf44ce109f00000d8c88f9800036ed5c02878a5624620d00620b1f748fc2460e29838da)) else (if page < 28 then (if page < 27 then 0x1e7a4c9200000000000000095a8e52c000351905d3090c0002c00000165c618d000000000001be04cd6a50123d800019a06b0c00017e000008fc54f02a984adaa028000000025a66e213981ec0000000001299c4805a000014c180002db3b2480000ce980000000c5893098c3095cf5b082232b82 else 0x33c8094144a4674448010da718011099a13f81261b630768c62cabd334997e80f30d5d00fa67f710f450993262aec460e91954fa46a226c91ff8a0b69a432a90fb8b22022a32141d2046a02bc48a82cc9ae417f80239c4add3e028e0371811596932d2100c0cbaa3418920a0c1148561b54cb5cc00000000) else (if page < 29 then 0x44347c41248258600013dd1bf037f930e0aae8ed819402540ecdab634d506f0355586ccb9a753ea2d94cdb0dd609a35a809b92d849d80e0e42a048f722a1065dd9103d01320fc193e3151262c0e4022384b6045d50ac206817a64720e3c26081ea133f350180080ef67b82a594d29b60068f2ac0131b1c90 else 0x6e40000fc046033d0098915b14d3000010926aa028800dc6fec1bc80bc019f4abc40002100000162c0000572112b53c409dcbcb006c8000000003226e8099a4db8000034800000453576013ac1d4000000001da122ca8a892170776eb4c9e9894616a0c729df99a591cc0000123900000000c0180005770))))) else (if page < 45 then (if page < 37 then (if page < 33 then (if page < 31 then 0x368d2e51d8d3b5000000000000354c000000061415b4dba3b4aaa0815dcdccd26950000a345d9908a7959478c234a4513070c000000017e06520d1000005843088ed2c016c8000000008127c3000091800cc192d2fc62dcd2059e71aa319ba4c61047823e4b1a08b1000048739c68d30c37953f4 else (if page < 32 then 0x97c14215c83bcd14582de4acd803da1a6134d0fd226009b68851014032a208e0f690000000003a260c000000000000afc40000000ac960001410042512e01186b3b1c76283274c000054e069c33046440000000000000000000000000000a19b7f60e4400003e8000076405b820f81d427a2a00008400481 else 0xc198cba00690000e35000055065088cd58d5854a00000b8400000000a914000000000009420000000026e30ea6f1ccad9ab50102046dc000000070e4b8c164800000000000263b00007bc15bc800021c05bac8311038000057233ba9be856b18c60a78400026e26aad4ac23080bd0946000003e00323)) else (if page < 35 then (if page < 34 then 0xaca00fc10ed211191327e440000000502a00caabb47c376f4fa413692f93926015099d1d3119a86f4ca18013738ea961265a9533000010c81e5900009a2623a9f689fd252414c801f88000916ce768260b2e28fa6000024836f009ac994df28561a0f20c84a4d88000468c89c257234898fe611119b040b2 else 0x12a8f584d70739400014c00000944b3fd2108cc90b38800010f112109d0003d9ffb08504314d3584804c013b40fcda1781d90922000022c158d600014ec2a903c6170b55f02641bf823e811451cf80555ad00bc407bb2422adc6fe808680e006d016649cb800002cc095d11982da49a922800ab30443) else (if page < 36 then 0x95c2fa44d302242abe0478d1682066024864e99493486850c460a28037223b8211061c0290053e20edd041120375ec23cc0002bd386ac75c90d83d60786c744000000000000d658000000000012baa85b00fa27c45bd022537205b292c80000582019065c500000000560accc85900000684c0000f081020 else 0xee821982288a86570942861e30bb6b36c9f5800000007000110aaf0478200005ac000028d00c6c0e51ba093f27a60e9290c04a44404e416471519694cecb4c4b5ba43083b516894b097258380205963026864a4143da078085aabb2bc14ad303e00e6d1d88de44842a980550c0ba30106ac2000173012f3))) else (if page < 41 then (if page < 39 then (if page < 38 then 0x5a2150c008013253762a7983e5d10172f50ec27e8564a96ccc940f4825719d087f1eca0d5d06244e10ec180f6361449d4a9001212a2a41380a684a1686806341611b690a64a560176a2644815230915b836a23300e3de2b057d190624cc9ce8586089a470c1a28a9a678a52e58b3a498424e65008b0019a4 else 0xa287004110a00003146c74a3920000688c00008d83f26a9600000000000000000001d1db81858a15a859c348126fe057ccad14696760c2a40d208000000057026130eda0d820ed9a7345e194a91d002430d025f069380c60224455822ac1a6c9e205484ec58da03cf51ccd570c89d553806ca94515dc2712) else (if page < 40 then 0x17732ea00001368347000000e000549bd609b61385ab037a601cca98e37b86a9000000005f180000620a1d4602382993c946c85c817220c563be80000b749da0c0c000056904f03068000059c636a877d800055600e068e90fd84f5000e8000263c39ba00013bc47600000 else 0x75423b9366641e00001d7846348b4069cd73800002f64a942812c9a447c151112883d7907a277410f816407943464800052a09b081b4dd400c8274d720400000000070917100f8bc515d0015c135040409fe08508000000061c48e58d2101d2624046eeb43d5b18da00001b0c26c40000cfa5118a02a)) else (if page < 43 then (if page < 42 then 0x6340bd0000039600000ca091ca3f717a4163983a9234a9e812f9800056205de9448204826b178640e4800059f09d60d1224c08c07342551c20134c274034044cf000b758b2657e06e837712a66bb80a910c7049414f8c590bae1a0089e84909d2f117e09a992c04f735ec940d5100809a366041984180000 else 0x7f6c9dc000000000080518ebe81b0062f4f9100004ab47a0a00024aa00008f2057d8e8087405e2c67840000ceb094062889c917a4a2a746c07c500004da93e000000c8683f2d39000059da000119513a2124310529e4d585800041a8472a40000005aece8800d0aaf09be9066aa804620000000001380000) else (if page < 44 then 0xa5a142515080000000000000003b10432800015c818800000ed00dea2c610c14f1000003e40751611caa20b92b8c294a428102625af2d2d023412c5334647648dc036316782f5c0000003334000000e80000068a1330400045a3000000000001aa0a6874d4207908ca4a82c38d521c7e090c4c92884b0000 else 0x94829c092d25968c80c981cf523c42d0156d97f238190368000265cd51000008cd140817b08a420fd0000490856407f9c05d0000422e834400058a0958b1f8d9553c620520a8006319ba646e0f0c5d983e200000d6899e9000089c000004f00000000154e4000000095ea000000031a1000000017581a92)))) else (if page < 52 then (if page < 48 then (if page < 46 then 0x8e009880931989005801e8d5e836e9a9a0360015b32a040a53940e4323a1a02122a051b1f2089607fc19bb33665109044c50d2d323e053cc97a353537b8056ca9280000132e0001502000014c014c2bc23fdb0000861103d4eb400003c99d9089b23406eb8e70a0ff09146a0d43099b20753600019604110 else (if page < 47 then 0x5640d8233c0054013c000025059dc93bc9cd83c80000000028c856b222aab1cc000448411e4a2c1d352a0637401d866d000007c20a8800001dc475352c216148d3700004e0a8aa2845348800000003b6a9500074000000003930c542411b2da692040d4c9080005fe2a68aab843d0123116540003d14 else 0xa6c600024e848328e600000189800040b4178000000000000da987bc8c732249619a80b352900000bcd5d8800007835e81dd8443657440002bf02c20109600028930000418060400003d500000514c00019c3000126c152a597400009a6d89844e400006e902508000004af24c00033376b20ab51bbb1440)) else (if page < 50 then (if page < 49 then 0x89226780e2020a234c279001792a300000df61690008900000002c490000af02fe0de083a5a77c40002b90000035e000000003a10630079c40000fb08d2109c2618d0f02e890b464012cc53da0ac5cb090319a2a14892b1d84b48da8b0444602f56a9c73e100c985c46b82852a9c828f402e2848848b0000 else 0x5c43514d27ab2d0a4400555e184ad203830d81a38800053e0312800000006ef00001c855516962c9685584a751992705ac822835a0000b18c00000006368b28c0004f141d015d000004c413de0cba8e8903b0000104a6723000061e2000185b24d363d400027da000035e8c340920d1f0a120efc00002cd3) else (if page < 51 then 0x41020890e6815e30600af2cc033c26ac806184cb185802e680001342c3f100015ec2653045578221fea460a257b1822282c8b3fa1b24161c40002c62ae213a8aa2038fa6e500000a83c5506ca4c7c0000000060ece7008ba280000012804a813431000041ca1c349e179a0900173b50e008b62fd98200000 else 0x27c000016292060440eae86ac199d0000038412118000200226a90f052e029ccf751b109e568d610b06918000086e0bd41e19b61237a011492992a8100007f080ea0500000000022902932000055cc0000f8b11201042302cad7245563d80000524292879c023347501926d6c40002c306940a28d6f0afd0))) else (if page < 56 then (if page < 54 then (if page < 53 then 0x47802001ae9b4039ba091511d0000000000000000000034e023998e03ff00000f78400020940000000000054f63acc3a198b3c0f825e0b2d5e58b2700000e30c000000000000001e3000001dc12b4233b005400016759cf03d3135c02e0000026e1116c0002040000000000001131000000000002b383a50 else 0x305489aa538bf88ade0052d393c04618a14b9891ac1d015e10d19f582ea2848101497622ac07f229b1560840000000b882cf900006ecc64d4558a85427060001d1580007e24e16c13038c0000069416c2d9d51eb48d99c6a8cc67c2d320a68811060ca08ec230902c6000000011604df0af21420e5123640) else (if page < 55 then 0x7fee19c1becb8808c0858093f9a2223c8e1045d0d9c37a0cb0280b118ae43ac018129883b8a8e6200000000000a8ad234a86b41bb052c3d0103a1460380e1bc2c6954aa53c8cd40acb47116774a30169833192d8158e93f00ba3548019961149afa80e011ed0b503cb2f95358c843117154e71e4a7922380 else 0x2e00fdc000036c235800001118000039ac00020f01c006e060002b602473131400016a846151142a40654248a253612b1dca019041392dce4a4331191a7749c00000a06000000000002d46000164980003a9061701d9a4180000618600015c000000000032d2d8800026a400000001cf8ab8d41402388000)) else (if page < 58 then (if page < 57 then 0xe5ee8400000ab411040d6a3c902fa1040abb18000b2a01f462102dc000011d81d25b49600000000e402414acb20001bab00008b2942812a9a0618d6c431ac703a6004634d00eedc5b20000a04ced08000b3c052980004e702526db42aeb01920a0342c02904d240001395abdcc58084b31e007c92771 else 0x6a6c65080000440476caa450d205e1ae8200006314e7aa7065e800000f169480244a5e0839166c4f485a331c0647a0044a383d3e6180c0528c78d8907a087b0570b2ed5202444812b03380a7c41a8c0001be63e1000018003f49066450ca4112de019ac05a97480514000000022b128246f0467880005370) else (if page < 59 then 0x85e4d6a0aa1343856e8db5904492f21b5613c87f3540066122226b9230501bf4adca7103be320456590e30450242b52bc58b82a01b30332ca1f02fb43380c004c720653b022ed6a47327022600c309c3504da4b847c9006c87c108446604a521dc000008f5298b1b6633e00002b712c81a600d2000384d00 else 0x2c39445492e81bce058484600006fc1382bee60000108479b47706ba03dc0000000000008dc98a13661a26297d8870000000005c06c282504910cff88000000057e12a80cd3000011b41e021d31b4475c043c194d4e0055c0ddc0c393eb6a8c414dc6e9a35000000001b583020)))))) else 0
  | 6 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x2a80f4def2fd15ccc1d23600001a992e89c0000858a48000099152aa65dec0b46530370414824680b0000962020798c50000000028035c0000e9370836640007f00003cc0a486c03b59ae8fc04946dc3e00000f7674000011083b33c000021ac2967a81ad14a2c40 else (if page < 2 then 0x201d56491011802d900272116486d90f425500017d9284b930000000000cf0700b6847e0b4402800007043633d82c8c00000052213104b7120780b78122200076a148122e0002ab28cc000d6301a05cdb6c0008300001ba045042ba084d625c60000000082593 else 0x47a2d8ca08d900623661c600ba550458056c12036320099028f6171b1da16400082c2040600ca202a26c000106300002c00c303388115821e200000000010606c80300cd0000ee000015c00009327580001ac45331d11600d040c139d458800098a000270054cef9)) else (if page < 5 then (if page < 4 then 0x4b00068000d6125804c15a8e295d1ab40de0ab1101bd4632c19a5b8bf041c8af38532851960bc085842d97a407069089a818099a50987c20000a06b0328110e3d25901701fd01116e00002120c004a009e5102b543f900009e0170000459830cab51f9b501e80950 else 0x2101b48842cc043800000000000003b4400062144900001e06417fc1901c2690077900000005768a082014e4a2079300015c000064900000000004100001a030e04593c400009f4838ab99340fd348d0000c60e114f824c0d000002d80581fa40001642169b0c000) else (if page < 6 then 0x2f32101a40a10598310e040a851a537e54ecc237712951f80cda6303bd94c2e763303849fc0c421d83a0d4a64c036491918acbf07c41045de100364000012e08a06802068000e493e839801a40936983fc80010597b822d98a400000015980001e0044c1121801ca else 0x78013980006365a03644000e40000324c9408f100017a1be600021846009140007140001d20a704402685806000000000150060a000440cbc461252305248e08f70002292140fa63c83240ce0f8286817c21007a637193855804a47d9b90d1145516c0328e3061cb))) else (if page < 10 then (if page < 8 then 0xea099200034e4000b220003b40000ff605db8e14640008208001d650526e13008000fe105880000006c274138002002b072d22c0c265353d033d98606b57d8218a04c4b60000284bc313075c2901bcc1a000020c81e2e320d0bfa4000d101a3bfc4036143 else (if page < 9 then 0x45bb6822267240b90f983e6844819238168ae365e98fc9442cc41704024000a454ab058da664d565b11850c0c508a802400a23725599940014e206133720a02bc343340c20c4db04600c860a076a8d13bcd844b7000029414600005f03acc0000001431a405a0e5b else 0xe494240004d20000000b1000041c0d862364783c8150c8502018088d247c01a905892a452105534c956826b5b01440462dc6599318d760c531d1b0800010f27490000000a361d9415952c2e2305bee52e84265e113c82a67d21e323e82286b757095014cc891)) else (if page < 12 then (if page < 11 then 0x2981c80242a113a03e19e0859050abdcdc426950f9060190cf818b896a9820db94b3215920c81211227422e09945802d95964eb625a458608037000031c198c0233a32000c200f486a3f41a70f785e838c4b0c7e20000800e2059206880011a0a906f845a1584a26 else 0x3c0800102847a788c6811950f40001100d48fa05001b400003c08a88a400001e600027800000001f1b6cd224a8485c26405ecb2648a1f59f2082431034d942c3101c83ae448608216329cd7005d006b414d5a2aa67b91dc1aa0af55a892dd560c62) else (if page < 13 then 0x5a800000004d00002bc0000000659a55c0009220e81780000c361010001b647840d31200f62ef87f8338510c0002480000d26cc18783a821240838c48001d807030001891dc6ce00002504000c844480000000e7006800023206e923000013003934339e49062a52 else 0x840ea2000)))) else 0
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


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 8 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x48 : span (checked 3) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x96 : span (checked 3) 42 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 138 0 = true :=
  (@span_join (checked 3) 48 0 90 chunk3x0 (@span_join (checked 3) 48 48 42 chunk3x48 chunk3x96))

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
theorem chunk4x240 : span (checked 4) 48 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x288 : span (checked 4) 48 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x336 : span (checked 4) 48 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x384 : span (checked 4) 48 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x432 : span (checked 4) 48 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x480 : span (checked 4) 48 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x528 : span (checked 4) 48 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x576 : span (checked 4) 48 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x624 : span (checked 4) 48 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x672 : span (checked 4) 48 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x720 : span (checked 4) 48 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x768 : span (checked 4) 48 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x816 : span (checked 4) 48 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x864 : span (checked 4) 48 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x912 : span (checked 4) 48 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x960 : span (checked 4) 48 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1008 : span (checked 4) 48 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1056 : span (checked 4) 47 1056 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1103 0 = true :=
  (@span_join (checked 4) 528 0 575 (@span_join (checked 4) 240 0 288 (@span_join (checked 4) 96 0 144 (@span_join (checked 4) 48 0 48 chunk4x0 chunk4x48) (@span_join (checked 4) 48 96 96 chunk4x96 (@span_join (checked 4) 48 144 48 chunk4x144 chunk4x192))) (@span_join (checked 4) 144 240 144 (@span_join (checked 4) 48 240 96 chunk4x240 (@span_join (checked 4) 48 288 48 chunk4x288 chunk4x336)) (@span_join (checked 4) 48 384 96 chunk4x384 (@span_join (checked 4) 48 432 48 chunk4x432 chunk4x480)))) (@span_join (checked 4) 288 528 287 (@span_join (checked 4) 144 528 144 (@span_join (checked 4) 48 528 96 chunk4x528 (@span_join (checked 4) 48 576 48 chunk4x576 chunk4x624)) (@span_join (checked 4) 48 672 96 chunk4x672 (@span_join (checked 4) 48 720 48 chunk4x720 chunk4x768))) (@span_join (checked 4) 144 816 143 (@span_join (checked 4) 48 816 96 chunk4x816 (@span_join (checked 4) 48 864 48 chunk4x864 chunk4x912)) (@span_join (checked 4) 48 960 95 chunk4x960 (@span_join (checked 4) 48 1008 47 chunk4x1008 chunk4x1056)))))

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
theorem chunk5x144 : span (checked 5) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x192 : span (checked 5) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x240 : span (checked 5) 48 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x288 : span (checked 5) 48 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x336 : span (checked 5) 48 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x384 : span (checked 5) 48 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x432 : span (checked 5) 48 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x480 : span (checked 5) 48 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x528 : span (checked 5) 48 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x576 : span (checked 5) 48 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x624 : span (checked 5) 48 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 48 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x720 : span (checked 5) 48 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x768 : span (checked 5) 48 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x816 : span (checked 5) 48 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x864 : span (checked 5) 48 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x912 : span (checked 5) 48 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x960 : span (checked 5) 48 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1008 : span (checked 5) 48 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1056 : span (checked 5) 48 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1104 : span (checked 5) 48 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1152 : span (checked 5) 48 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1200 : span (checked 5) 48 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1248 : span (checked 5) 48 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1296 : span (checked 5) 48 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1344 : span (checked 5) 48 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1392 : span (checked 5) 48 1392 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1440 0 = true :=
  (@span_join (checked 5) 720 0 720 (@span_join (checked 5) 336 0 384 (@span_join (checked 5) 144 0 192 (@span_join (checked 5) 48 0 96 chunk5x0 (@span_join (checked 5) 48 48 48 chunk5x48 chunk5x96)) (@span_join (checked 5) 96 144 96 (@span_join (checked 5) 48 144 48 chunk5x144 chunk5x192) (@span_join (checked 5) 48 240 48 chunk5x240 chunk5x288))) (@span_join (checked 5) 192 336 192 (@span_join (checked 5) 96 336 96 (@span_join (checked 5) 48 336 48 chunk5x336 chunk5x384) (@span_join (checked 5) 48 432 48 chunk5x432 chunk5x480)) (@span_join (checked 5) 96 528 96 (@span_join (checked 5) 48 528 48 chunk5x528 chunk5x576) (@span_join (checked 5) 48 624 48 chunk5x624 chunk5x672)))) (@span_join (checked 5) 336 720 384 (@span_join (checked 5) 144 720 192 (@span_join (checked 5) 48 720 96 chunk5x720 (@span_join (checked 5) 48 768 48 chunk5x768 chunk5x816)) (@span_join (checked 5) 96 864 96 (@span_join (checked 5) 48 864 48 chunk5x864 chunk5x912) (@span_join (checked 5) 48 960 48 chunk5x960 chunk5x1008))) (@span_join (checked 5) 192 1056 192 (@span_join (checked 5) 96 1056 96 (@span_join (checked 5) 48 1056 48 chunk5x1056 chunk5x1104) (@span_join (checked 5) 48 1152 48 chunk5x1152 chunk5x1200)) (@span_join (checked 5) 96 1248 96 (@span_join (checked 5) 48 1248 48 chunk5x1248 chunk5x1296) (@span_join (checked 5) 48 1344 48 chunk5x1344 chunk5x1392)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x48 : span (checked 6) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x96 : span (checked 6) 48 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x144 : span (checked 6) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x192 : span (checked 6) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x240 : span (checked 6) 44 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 284 0 = true :=
  (@span_join (checked 6) 144 0 140 (@span_join (checked 6) 48 0 96 chunk6x0 (@span_join (checked 6) 48 48 48 chunk6x48 chunk6x96)) (@span_join (checked 6) 48 144 92 chunk6x144 (@span_join (checked 6) 48 192 44 chunk6x192 chunk6x240)))

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
  | 0 => if page < 5 then (if page < 2 then (if page < 1 then 0x4444cccc4444cccc3f003f003f003f002aaaaaaa2aaaaaaa2222aaaa2222aaaa22222222222222220fff00000fff00000ff0fff00ff0fff00ff0f0f00ff0f0f00f00ff000f00ff000ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0aaafaaa0aaafaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a08aaaaaa08aaaaaa02aaaaaa02aaaaaa00ffffaa00ffffaa00ffff0000ffff0000ff000000ff000000f0f0f000f0f0f000eeeeee00eeeeee00ee00ee00ee00ee00eaeaea00eaeaea00cccccc00cccccc00cc00cc00cc00cc00aaffaa00aaffaa00aaeeaa00aaeeaa00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa008aaaaa008aaaaa0088aaaa0088aaaa0088888800888888003cfcfc003cfcfc002aaaaa002aaaaa002a2a2a002a2a2a000ffff0000ffff0000ff0f0000ff0f0000ccccc000ccccc000afaaa000afaaa000aaaaa000aaaaa000a222a000a222a000a0aaa000a0aaa0002aaaa0002aaaa0000fffe0000fffe0000fefe0000fefe0000eeee0000eeee0000eaea0000eaea0000cccc0000cccc0000aaee0000aaee0000aaaa0000aaaa0000a8a80000a8a8000088aa000088aa0000888800008888000080800000808000000ff000000ff000000aaa00000aaa000000ee000000ee000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xcc000000cc000000cacacacacacacacac0f0f0f0c0f0f0f0c0ccccccc0ccccccc0c0c0c0c0c0c0c0aaffffaaaaffffaaaaffff00aaffff00aaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaacceeccaacceeccaaccccccaaccccccaaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaa00aaaaaa00aaaa8888aaaa8888aaaa2222aaaa2222aaaa00aaaaaa00aaaaaa0000aaaa0000aaa8aaa8aaa8aaa8aa00aa00aa00aa00aa000000aa000000a8aaaaaaa8aaaaaaa8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a888a888a888a888a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a09999aaaa9999aaaa9898f8f89898f8f898989898989898988aaaaaaa8aaaaaaa88f8f8f888f8f8f888cccccc88cccccc88aaaaaa88aaaaaa88aa88aa88aa88aa888aaaaa888aaaaa8888f8f88888f8f88888aaaa8888aaaa8888a8a88888a8a8888888aa888888aa8888888888888888888088808880888080aaaaaa80aaaaaa8080aaaa8080aaaa808088888080888880808080808080808000800080008000777700007777000070707070707070705f005f005f005f0055ff000055ff00005555aaaa5555aaaa555555005555550055554444555544445555000055550000550055005500550044cccccc44cccccc44cc44cc44cc44cc) else (if page < 3 then 0xfcccfcccfcccfcccfcccf000fcccf000fcccccccfcccccccfbf0faf0fbf0faf0fbf0f0f0fbf0f0f0fafafafafafafafafafafaf0fafafaf0fafaf0f0fafaf0f0faf0faf0faf0faf0faf0f0f0faf0f0f0faaafaaafaaafaaaf8f8f8f8f8f8f8f8f7f0f7f0f7f0f7f0f7f0f0f0f7f0f0f0f5f0f0f0f5f0f0f0f3f0fff0f3f0fff0f3f0ff00f3f0ff00f3f0f3f0f3f0f3f0f3f0f2f0f3f0f2f0f3f0f0f0f3f0f0f0f2f2f2f2f2f2f2f2f1f0f0f0f1f0f0f0f0f8f8f8f0f8f8f8f0f0faf0f0f0faf0f0f0f0f0f0f0f0f0f0f07070f0f07070f070f070f070f070f000f000f000f000f0000000f0000000eeeefefeeeeefefeeeeeeeeeeeeeeeeeeeeecccceeeecccceeeeaaaaeeeeaaaaeeee6666eeee6666eeee4444eeee4444eeee0000eeee0000eeeceeeceeeceeeceeecececeeecececeeeaeeeaeeeaeeeaeeeaeaeaeeeaeaeaeee0eee0eee0eee0ecececececececececcceccceccceccceaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeac0eac0eac0eac0eaaaeaaaeaaaeaaae6e6e6e6e6e6e6e6e0e0e0e0e0e0e0e0ddddccccddddccccdddd0000dddd0000dcccdcccdcccdccccceeeeeecceeeeeecceecceecceecceeccccfcccccccfccccccceeeecccceeeecccccccccccccccccccc44cccccc44cccccc4444cccc4444cccc0000cccc0000cc4c4c4ccc4c4c4ccc44cccccc44cccccc444444cc444444cc00cc00cc00cc00 else (if page < 4 then 0xffff0a0affff0a0affff0888ffff0888ffff0808ffff0808ffff00aaffff00aaffff00a8ffff00a8ffff0088ffff0088ffff0080ffff0080ffff0008ffff0008ffff0000ffff0000fffefffefffefffefffcff00fffcff00fffcfcfcfffcfcfcfffcfcccfffcfcccfffcccccfffcccccfffafafafffafafafffaf0f0fffaf0f0fff0fff0fff0fff0fff0ff00fff0ff00fff0fef0fff0fef0fff0faf0fff0faf0fff0f8f0fff0f8f0fff0f2f0fff0f2f0fff0f0f0fff0f0f0fff0f000fff0f000fff00000fff00000ffeeff00ffeeff00ffeeeeeeffeeeeeeffccffccffccffccffccff00ffccff00ffccccccffccccccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff88ffaaff88ffaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaaaaaffaaaaaaffaaaa00ffaaaa00ffaa55aaffaa55aaffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff88ff00ff88ff00ff888888ff888888ff80ff80ff80ff80ff77ff00ff77ff00ff22ff00ff22ff00ff0aff0aff0aff0aff0aff00ff0aff00ff08ff08ff08ff08ff00ffaaff00ffaaff00ff88ff00ff88ff00ff00ff00ff00ff005f00ff005f00ff005500ff005500ff000000ff000000fefefefefefefefefeeefeeefeeefeeefcfcfcfcfcfcfcfcfcfcfc00fcfcfc00fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcecfcecfcecfcec else 0xfffffff0fffffff0ffffffc0ffffffc0ffffffaaffffffaaffffffa0ffffffa0ffffff88ffffff88ffffff00ffffff00fffffcfcfffffcfcfffffcc0fffffcc0fffffc00fffffc00fffffac8fffffac8fffffaa0fffffaa0fffffa00fffffa00fffff8f8fffff8f8fffff888fffff888fffff0f0fffff0f0fffff0c0fffff0c0fffff0a0fffff0a0fffff080fffff080fffff000fffff000ffffeeeeffffeeeeffffeee0ffffeee0ffffee00ffffee00ffffeac0ffffeac0ffffe0e0ffffe0e0ffffccccffffccccffffccc0ffffccc0ffffcc00ffffcc00ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaa8ffffaaa8ffffaa88ffffaa88ffffaa00ffffaa00ffffa8a8ffffa8a8ffffa888ffffa888ffffa0a0ffffa0a0ffff88a8ffff88a8ffff8888ffff8888ffff8880ffff8880ffff8088ffff8088ffff8080ffff8080ffff8000ffff8000ffff5000ffff5000))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x12077a8638ef50c91e89891bd527247a24e50f437ca5e66f else 0
  | 3 => if page < 2 then (if page < 1 then 0x923a57a18bbbd361923a53418dbb92c1923a52c18bbbd2a18bbbd181803bd1818bbbd12187318c4877b14c3092388b04923a4b02922b0b028b398a2492394a2492388644923a464274b885818731042877afc4308dbb8422923a4422922b042270b1037077afc2b0923c82a48bbbc2a2923a42a2923a4262923c016200481de30047dde300471de300491da300491d8300495d6300491d6300491d4300499d2300495d2300491d23004a5d0300491783004917630045d66300491643003456430045d6030046d5e3004855c3004915a3004915830049154300284bb800284b58002fc731003bc672002d05380041452c003104f80039047400384391003bc2d2 else 0x873858893923a54251923a5c421923a44c218db91866f8cbbd806f913bd7e6f8d3bd7e6f8bbbd7e6f883bd7e6f923a57e6f88bbd7c6f) else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x6b056c170af1880ecb981766f82ecde05d9b20bb3381765d02b4a104713c08e3bc0d35c80f4a1017248ec1c91d23922b06008abc0113780218f00425e00843c010678020af00411e0081bc0102780202f003f9e007dbc00fa7801f2f003e1e003cbc0076e800ebd001bbc0032f8005ef000b7e0016b6002c780056f0009fe000f7c001c6c0033f00065e000bfc001778002c78004fe0008fc0010f8001ff00037e0006bc000cbc0018d8002be00053c0009780011780001f else 0x5d18b4ab31698a61e284c3c509738e22c71d258d2b0b1a3e9634a12af14054e378a9668152ca129f17453d314a3c5094789028f0f051e2849bc520e66bf19717a32e45c64e1b0cb924169dd22c5c90587638b0e5114f1d221d30843a608874b710e96c21d2d043a588874ac10e95221d2a043a87885d0e10ba1421741442e64886c8310f10421e1f043c2c88784810d88221e0f84361b886c3610f06821e0b042e130878a10ef0f01de3843768d8616e70c2de415e3b82b6) else (if page < 3 then 0x723801f46aa841f482a841ec6224c1d86f2e0172702dc17277ad4172702a0172853801667e38016686b781669236c1669236016677afc1718bbbc163923a41636f0fc1746aa8411465a8411482a8410c53284118509241188bbbc0c38bbbc0a386b8006686b780669236c066923a40638bbbd7e1923a442200459cc700491ca700451c0700435be70043dbc700435bc700429bc700491ba700491b8700491b6700491b4700425ae700461aa70045daa70042daa700429aa70041daa700415aa700415a8700491a6700415a4700409a47004299e7004359c7003fd9c7004159a7003f59a7004299870041596700310fd900490f4700490f2700310e5900380d16 else 0x9246dc8c40c15aaa12891dea45094612474b1c4229231c4c2120024f1b778c01248dbbc60094c91d230049e48e9180248f1748c012477ba4600923a5d0300479deba180236ee5d0c012474ae8600853816e30045ddeb518020ad55a0c01248dab8600923a5423002e92c62c0018893316001095d18940087310c49003bd7e6188022ea128b001125094580083a84a2c004154251600204a128b000fa5094580052a84a38003112651c0018c8f28e0011171944a0092388a2500491d251180188932660010e6213120077a9065200491d22c1801d2c7160c00e971087000923a442a00491c421300248db1098012463884c007220043400310f621c00248e9108c012416084c00638b0426003a44c21c000542610e0012473854c0077a902b2)) else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0x62fd45f50fd33f4bfd29f49fd25f48fcf1f3a7ce7f397ce3f387cd1f327cc7f317cc3f2c7cabf2a7ca7f297ca3f287c9df26fc99f25fc65f167c53f127c45f10fc3df0efc2bf087c1ff077c19f05fc15f04fc11f03fc0bf027c07f017c03f84be0af813df4f2c7865e163c43e0af801f else 0x7082eede05ddaa0bbb2c1778702df0d05be0a0b7bf016f4682de8605f4d80bf1a817e3482fc5705f88e0b791817e2302de4405f8860b790017d1f82fa3a05bc6a0be8c417e1402fc2605f4420bf08017e50823a880475aa08bb2c11782821ea6046cd608f12810f2482363c04787608f45c0af18817ca101fa1a037c2806f7e00dec801dcda03f11407e2100ee3001fa1ade3c91b6782b54eba31694251e490587638b0ee910e84c21e37817650823924748c00f6f8018df) else (if page < 3 then 0x5d18b6b4316e12627afcc3d5d153ca12a7a1a547afca3d50947a9628f51051ec5ca2f83945f0528be04517be8a2f5294766028f9684cdc1498f81131ea419794632f49058f638b1f2410f9c821f38843e70087cdb10f99021f31c43e62087ca110f91621f20443e40087c7f10f8f621f3a443b33887c6610f8a221f09843d10877cef0af9ce15f3101fd8b03df0d07bd260ef31817e5082fca005f93e0bf27417e4e02fc9305f91c0bf23417e4502fc7705f8e60bf38c177 else 0x92445c0792435c07622e8c5a77a84a3c63284a3c5d284a3c5a284a3c50a3ca3c82a84a2d82b54a2777a90a335d17ca3a5094499c9231c58774b1c43a9231c42e9231c4276389843c88a841ed509441fc923801767238017686a8416e88a1016d621ec1796f1a4176869a416e5094417c8690c16e3490c16e348fc17c5089417c8688016e7e08016e640801765083417c5094411c5082c11c9231c0677002c0769246dde382a84a2c9231c4260048e1af004461af004760af0046e0af004360af00491f8f00445f8f0045d42f0044942f0041d42f0041542f0031127b0043926f00310e7d00444e6f00444e2f00318c5e00284c5e)) else 0
  | 6 => if page < 1 then 0x3bd43f63287eba50fd8862fbbca3f5d147eb428fd4851fa84a3f2f947e51267d8e21fa841ff8882ff0d05fd880bfa8417f4402fe8505fd080bf9ec17f3482fe5105fc860bf8ac17f1282fe2005fc1a0bf94411f05823f2401fc1603fc461af50947b0528bd8e21f28417e8682de6905f8860b788017e50947800637c00a1f80127f001cfe00317c0054f800a3f00133e0010fc000ff80017f00023e0001fc0105780043e else 0
  | 7 => if page < 1 then 0x50fd47e17f else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x36 else 0
  | 3 => if page < 1 then 0x12041 else 0
  | 4 => if page < 1 then 0x14c410bc2f else 0
  | 5 => if page < 1 then 0x1042f0bc1d else 0
  | 6 => if page < 1 then 0x2f else 0
  | 7 => if page < 1 then 0x1b else 0
  | 8 => if page < 1 then 0xb else 0
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
  | 2 => 8
  | 3 => 81
  | 4 => 240
  | 5 => 292
  | 6 => 77
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 29
  | 3 => 297
  | 4 => 866
  | 5 => 1053
  | 6 => 275
  | 7 => 48
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 3
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 7
  | 7 => 5
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 10
  | 3 => 14
  | 4 => 15
  | 5 => 15
  | 6 => 13
  | 7 => 9
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xe78202 else 0
  | 3 => if page < 2 then (if page < 1 then 0x7cf2062d00002000041000c02c40011832000400113010d408618220f1150460031002802401c0002005040180052043 else 0x704930138350584c1006864c0) else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x860a042040000082002401142006800e082800408c000a108830418003009c380003860002110020004403002410406001800e04186 else 0x2610481001c2051844102021460000101938e2c0061a14881365c001161c68a0204e000a0050018358830214006081838a0c000093a1c081) else (if page < 3 then 0xcc4483004898700000035420024600429d0e04a840e3828804082840828000001001d8200004181c20d021c30102981090c000030200009 else 0x25d691180c0a9300800c361c484014c0003088002120c88e0c041000cf85010000600021cd8a0a08013)) else 0
  | 5 => if page < 5 then (if page < 2 then (if page < 1 then 0x12041014c04985547418504041800c481032a301000010209180400d141010202180012204400020408006381003a1008036000020840015 else 0x2282001a10b89026c100000100e001089b0000f91020040402040830634283003998f000480102140050c008110620281340c0001a10004) else (if page < 3 then 0x2340012800000021818014000081a9c10208040000008014002128a0a002030a0013f2c0008102002801e24101082410c0c04b050401180 else (if page < 4 then 0x281010012380182e20408000cc02000400c06040828c081084ae411d0e98700040040516200850024080014c20a46142110000380100ca18 else 0x4c0c2086e5c301062401402840040a1885c0e0000302241031c1052343487bb))) else 0
  | 6 => if page < 2 then (if page < 1 then 0x20a08021040146f4002060461c4c6808000503840a54006000158200000000028b0a001c811008c0010c100000e0000800581802a04300 else 0x114280041a871260804d85) else 0
  | 7 => if page < 1 then 0x22180791003e31c0b else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x118478000003cb8ca156a8000018d899ec02840009e000000ce2100009969e9860407d498 else 0
  | 3 => if page < 5 then (if page < 2 then (if page < 1 then 0x3ef000000024803c111186ef400086725000000a4d8e900001768ec900000001ef40000e60b838b8020168009db000000078d04bc4c020c070fc000541c4302930b49380dc3c49c5e0600012825e0cb5e600c000940e0de84f87d400000f50001586656c85e00001009569d3d57c8000 else 0x5a605d8276a3807779bbe516c40042322922cce02a0001a5b39300000978b302d00e4b37686d55c0c1da52188da5b68eda00024003954b4b21da33c5f000003e4800000020c10b792801f2d90040c8b5a4391fda0000b58676a1bc6210f88836c000761800017214801b30e60000165a) else (if page < 3 then 0x72fde89156955f2d205cb4609edb6c410e00001fde000160138c1b1e2500e37000118000019db848140042014903e100001d54000336c6d0000055e3034e02790df3d0000b542d6d03019318002c0d08601c5a5e3cf08de4fd5a5a6a494b06216238166ccda31792005d00a800dc5004 else (if page < 4 then 0x49c1fc08e086d162016005578d834bc22391cf4c0680b45c0302659e5a0000086f9d0853710060cf14da74f1b1f256137000005de00021b12c18f30312017600011f000024da3920e5a6ef14dd2ac1b003934b024020e0c2f6800000000000a014c82e003007300e07060145a2c006cd else 0x3f035680000000000660223c3b3110000000000000ac01600f0847c5a808484380176d74172f0c5b392633200000000000200000185a000000019345ce776c7bc1969fc14e01f08))) else 0
  | 4 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x2305566168cc9bb8a615aef800ec0000000003cda000000000006b9846000000000290600000002b823ebd0000518cc015680aa05b2021406200000106600005500d5380000949000074260002d748000c8010678dcf4d0d7f2000000005c0ee7793800e09bae328249a0322e8000c60d74105780000 else (if page < 2 then 0x8a2d9e19c807a5a4fbb06013000000000009c004063dd319b260a101e7803c05b210e301b80e9b600000001600713db801bc0758800002c02ff62e861f093234000198000016603a241b090001c61ab800000e961bf812c33789b0c120007aebe3d22035071c401a04ac0984000006b004530dc0df88bfa1 else 0xbef708600015c0800048020000d50000000000000000000000000000c720000740c16b60000c01a70600006e190fb00004cb500080007b0025000000000655d0000000332e6f80bce58d70bed5b00cc03cef80007080742b99680000000eb64461382600000000760bd2e1858df24ea48e891301)) else (if page < 5 then (if page < 4 then 0xb4d160385af0000da02764b3d806c8a74346f16eedfedf160bd327829481f205dc022894496ef0022f3a985400000000000005782e9bcd8000000370a2b97f184002ddccbbb1c417404fc9a2b431020062d5abbc0d103c99000098bb354964027df0000000000079003fe60001000000005d800019005582 else 0x921a5005a801d809f9c81c400078bc0000e0f000057800a188d69cca83600753800142e940a742542121c1c600910067695481081e81caf7186e855a98b4c56a6a9e21ef604ab6b501e983ceb43d83600884128d8000182e75347f018a000000000f278946d7ad32dab42d6030af04e1085026d8e000ce01) else (if page < 6 then 0x7b8000032c3378805ed8e00a18bb000001ce20000241e880946fb4208503b0cddb68f482587f060cd68dc0855cac01b81cacf9680c0806c229003606000000000005fc30000000000000005e00fc4336d415d0000c40322e0475c1e374329c66800ed06b03a9031414a00d332780fc4037f0cd000671a986 else 0xb9253642486711e2b2567917ee14047d00d203ca46d000bbb6a488702eda9400ea56f004282e03d260ef806080362b6c055401400a6007fdb6c0c9023901ea036007543d903639827b4e6998b8da0290c23863ad2c2c152e725a5e0c820172e241854039370e0b2e5a07015e8726d01691ab400013506a9d))) else (if page < 10 then (if page < 8 then 0xe96c6c10000020428c0000398000000000d702800591251245400c2dc703c430fe615007980860170333ed5908162334400001408de018105d985e5a9cc836869400809dc0de61bb4242330eba5f6f96d6e81ae03d729788718036e1e437b403c5b8d03761952d5d92be8d760350d9700e1022d3558089a1 else (if page < 9 then 0x1cbe0002d0610018d0000000007718a7407580ac2380000019770d302894d808000000000000000c768000054ccab50000d095f0216bea16800075428b1a00017c015800a31b6124c6269e00007612aa3635a00004a130c00548ace066435c006da7267c80d70076de7f37438204f6a1e97014e01e6d9c12 else 0x65001575ead79187f7221039deaddf44ea20cee44298716314f20d894e939c271d2470c185ead04640fb641d003d01dbc11c01b0077b73202ff81d0ced0b3333bede6802b4461693ee57a02400b031fc1ab808a2796000000000c10485dae8900008f0a7590cc31a80c1e102816adcc90d3011e10e812b00)) else (if page < 12 then (if page < 11 then 0x4e0e798344f80000001394186d00000000e65cf330000212400033980cf00cbb62208425f82e5aac218d1e7798a0076d8354c0000843600000006a9ea0b406b62c815f57e1220f4000308031982578c000000000000001038000ea6d2162dc679034d43743a04032863c00000380868a0cc0c00000004e60 else 0x4005385bb6033809d2c4323a6d4a029f919c19038325a4c03ee7bd0318486f80e78ed464c1064915e182807a00ce007a5b79e07dee32009c534300000a2008574201f0028e1e17a8800bb098006c0497914095519dd6b50c18dab9096a0a580629ebd0128f186e3441db000b82249a506ed04505474c77da) else (if page < 13 then 0x630072300002bdd8ac0921d7661281d661c800131e600c901a47bb40e5000001ba009c0000014b4256b6f80000db120002a0225cf97b460c00005be49578420344f64c81e90da62c70539e00000002f7825c9b5c1384800024003201560388830000000f56c00075cb69813121d31d10600016a01958026d else 0x1748000032054c05eaf4f1241e056066265484c6014a7afe1791bb2c00000000430cf2346e0afb836617c01cb028708000000000000004f0400016632aa00000)))) else 0
  | 5 => if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x4dc0d622b012b06000166222c43319b202ab83b40800079cce52c2092300000000022cc2b5a208126018004e800c98ca061f32a8c95013402d4c370055024f795496684aa820722b8de6aa42b55302134cd8629c6ee262f00000d15b040700f505aad0123c4aedafe0343c2799fd14784b87916183b85f86 else 0xe603f249100b3601c4894464b13d0d82796e30000e6258883e40331eca792061f01065a00010600306330e8c0049caf403be9c3308d691402b1b96202663b6e8ddc00000000aef03010000ea2188050dde6009c195245f9b9ba516b66ae16803743377448f0000cf01a00296e69800001a057d804e00) else (if page < 3 then 0x6705660220000000001c202404be80e2c1c8806bb0c866c187a265805b89dd00940c84016903d10f5803413a923430b8025a626965607d048b10fe10db00c20942ee30618e37e03cc04580d14468840000000eac715837004c0680cc800fbad66003f120e02e71eb001003c4000005f030f05a403973215b else 0x1700e3a6b0064060000000148040688c33ca0098480f18a1123c0c4f42ad541970f82846f2140017601e307d065e001809ab04c5c4e214a0351e452acec3660628375156401db72f1ee760a6b9860000067825878000194014206b0c000020243800b0c000016f35a1cd38000204045924fba00000004119)) else (if page < 6 then (if page < 5 then 0x2d421c11a5568e0f902197790ff38400013a180000b047c017c6c6380901cd01f835040c5e6a10274800005b1ebe0d8c862ccca1e000170840002e802311a188000000095b82018cb4db802d410bbfb831e800b010f8264066980c207884c1008f3da19f00f78057849ba600000006e0105b6d422aa06c01 else 0x7f01f402180800046b91c100005e8139427cc064000000298f6006b9ef20f1124c023895703663e499282e68a3ce08dda78000e0183026c6230fb49c374136060ccd4c1c63cea13a304b905a1200016400000f7042012e000981e71da5746c0280000019020d002582e4461200e486984e90356073704792) else (if page < 7 then 0x6dd31684500b62c4cb800000001e20b365ee1b5ae8b12080177b56e000009537dd71e000000353c000122d4a861906000000021804100c008e062703761c88300002792b63000030d000009fbbf2f25ed4098f28066806e634120001d9680000000c7000000000000000000003d412692e30130000007886 else 0x1eb40e05a0445127d334b7598647e0c4052a0d74c7b03a20108218400780b20058804800000f604b9c16c014983f1000005c0f90000000002fc180000000d838000088172021503a800000b73003c1f40ee82b47888084092c3e1f918c036022c8be1020002cb80000d029be01349f600000140022f48000))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x48268833008000841304127c03404a10027a714f4300db026a82d801186906b7081cf4b9e0e43deac2c409a6939311d813c02b5c450d1c02ef1ac898b0828104f02980630200000005f0008029e1000047180000e8300ad6e127a008f6800078808f01b83047b2a801300884836d4d5d8a381dc7b807084 else 0x8338000000000007a2437766835b069035ae01130000000012860000000000002c006c80541b00253c7c017888721dd60300340027bd20000000000000017060240fe4ef431f848000461e0000000128de89a6418a2020806d016c44ce00000265ad100f3822ce0000000000000004800000018000007304) else (if page < 11 then 0x11a86274815dea3080439c611031603b8096446592a6ba0000341fe5056013770ccf7a803901c7825c03c01b9005078a76a9e000001e0594672e97ec16202f20133300009600740ad08c865328714ff3991012d602d406981a2b588780001d80292a5dcbd023c80363c00000000000c709c8848408000 else 0x20150dda23c3760a8ae8000c0015169840a89070d2223bb2e9480fb910001f8634881db400020c3b5660000141ba40505d260c00019cce7010001180bf260000cdcc264ac8237807bd0b2542c1800099bbbc227ad00000000aa0a94325060000be1344f8000d1058200000695a0000000032e0cda)) else (if page < 14 then (if page < 13 then 0x521958044007382f007381bf0a6b5a74912d69f8173810000000292e800002b800039742700102bee000000a816703200838468607d38d6834743f9fcb09e002bc0800003b5a04828000005b050bc400000000000c6002c1497100004a018c23f0000018c810c0f65c892409000002f0264040002256c80b else 0x5591c60b258402c77114768f834986890000000004f060001281a94089844f0272809ede898000053c00887982bac76618f842500de0d7403ec86407e3188c199c27b832ec89c3100138e80000ae48c4c68630000fc4800046a36d000002b84e200a7b5ad704907112d1d36e847ed0000c03000010af3318) else (if page < 15 then 0x5f00ec3000019180000c2136807d1bd900000000000006330000110008848a00ce734ae0304a4b8000000036230000218cc10800000002d80b4c5287e65aba562423a808b1328000007c840000e64b2f17c00d124a60662d520015010619d0951815604e231b16e660a40d97836c924897d054603d004bcc else (if page < 16 then 0x2513c803b6d63818c30dcb62c088600000997730955804309d61a6c380007d0800029ad7a831011da027807306f403d21354624802d3c727a5c0b9044e1a19231505804c33d68000004f5cd8009f4630090411196440930827025325f0080000000d159661f540483300014c00a98616985d21a0000077da else 0x1fbce3252b68e8f000008e13603218739c0001f6300801110fa06000391117e992e000039b4ab84f27a0000000740c0001e4f164c7308))))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x1482559a014804202f0599a0ae8003706409d1ee8f1e000800000a12ac000090f8206232000910ec084c0e01e023602f372e9880be21f1800002e6625e04703bcc3620706c809804a21ab4a011ad2649c0080cd81e211d0d38030f56b68003829c3244a555222 else 0x7024ba2db9780d20000293f1920000002238e8856d0601731404d8c5b75b0c0000006409609b1b000281a94600050c0003540a0800004009c6f8e2cc00000017000000002501586a415063600000910062221059eb0200000000000004000000d5d0003e02400000) else (if page < 3 then 0xcd9947a0198811c00d7430d6dadc02c053c0d5cb815402942000c804782833a04bc1d7a7400000609660a0cc280140b20800148c9c40002803202ad500015bb983956c1a0a439b06463c30e00a000c085729448804010001f05100973000000110660acc22f3549e else (if page < 4 then 0xc00544930141c38128100baf860000000001104ccdd01a447998740000330c780000040800000058000006b94a010930511d210c0424a180b44f088c0612811601c81b1824189600ad6602301060c402864c41306ac416818c55ac56e318f542800e00ec6ac01703 else 0x2e02bcd580a402873704000cd97002004000d4f000243d9883449886bd04ed))) else 0
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
theorem chunk3x0 : span (checked 3) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x48 : span (checked 3) 28 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 76 0 = true :=
  (@span_join (checked 3) 48 0 28 chunk3x0 chunk3x48)

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
theorem chunk4x240 : span (checked 4) 8 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 248 0 = true :=
  (@span_join (checked 4) 144 0 104 (@span_join (checked 4) 48 0 96 chunk4x0 (@span_join (checked 4) 48 48 48 chunk4x48 chunk4x96)) (@span_join (checked 4) 48 144 56 chunk4x144 (@span_join (checked 4) 48 192 8 chunk4x192 chunk4x240)))

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
theorem chunk5x144 : span (checked 5) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x192 : span (checked 5) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x240 : span (checked 5) 13 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 253 0 = true :=
  (@span_join (checked 5) 144 0 109 (@span_join (checked 5) 48 0 96 chunk5x0 (@span_join (checked 5) 48 48 48 chunk5x48 chunk5x96)) (@span_join (checked 5) 48 144 61 chunk5x144 (@span_join (checked 5) 48 192 13 chunk5x192 chunk5x240)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x48 : span (checked 6) 9 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 57 0 = true :=
  (@span_join (checked 6) 48 0 9 chunk6x0 chunk6x48)

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
  | 0 => if page < 23 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x88088808000000008800ff00000000008800888800000000880088000000000088000000000000008080aaaa000000008080888800000000808080800000000080008000000000007f007f00000000003f3f3f00000000003f2a3f2a000000003f00ff00000000003f003f00000000003f000000000000002a2aaaaa000000002a2a2a2a000000002a002a00000000001f001f00000000000f080f08000000000f000f00000000000e0eeeee000000000e0e0e0e000000000e000e00000000000a0afafa000000000a0aaaaa000000000a0a0a0a000000000a000a0000000000080888880000000008080808000000000800080000000000070007000000000003030300000000000300ff0000000000030003000000000003000000000000000202aaaa0000000002020202000000000200020000000000010001000000000000eeeeee0000000000888888000000000000ffee000000000000ff88000000000000ff00000000000000fefe000000000000eeee000000000000ee00000000000000eaea000000000000aaaa000000000000a8a80000000000008888000000000000880000000000000080800000000000003f000000000000002a2a0000000000000e0e0000000000000a0a00000000000008080000000000000300000000000000020200000000000000ee00000000000000880000000000000000 else 0x3f003f003f0000002a2a2a2a2a2a00000e0e0e0e0e0e00000a0a0a0a0a0a000008080808080800000300030003000000020202020202000000fefefefefe000000eeeeeeeeee000000888888888800000000ffffff0000000000ffffeeee00000000ffff888800000000ffff000000000000fff0fff000000000ffeeffee00000000ffeeff0000000000ffeeeeee00000000ffc0ffc000000000ffaaffaa00000000ffaaff0000000000ff88ff8800000000ff88ff0000000000ff88888800000000ff80ff8000000000ff00ff0000000000ff00ee0000000000ff00880000000000ff003f0000000000ff00030000000000ff00000000000000fefefefe00000000fefefeee00000000fefefe0000000000feeefeee00000000fe00fe0000000000fcfcfcfc00000000fc00fc0000000000f0f0f0f000000000ef00ef0000000000eeeeeeee00000000eeeeee0000000000ee0eee0e00000000ee00ff0000000000ee00eeee00000000ee00ee0000000000ee00000000000000eaeaeaea00000000ea00ea0000000000cccccccc00000000c0c0c0c000000000bf00bf0000000000af00af0000000000ab00ab0000000000aaaaaaaa00000000aa80aa8000000000aa2aaa2a00000000aa00aa0000000000a8a8a8a800000000a800a800000000008f008f00000000008888888800000000888888000000000088808880) else (if page < 3 then 0x30001000300010003000000ff000000030000000f00000003000000030003000300000003000000030000000000000002aaaaaaaaaaaaaa0202aaaaaaaaaaaa02020202ff02ff0202020202aaaaaaaa02020202aa02aa02020202020202aaaa0202020202020202020202000202020002000200020202020200020002000200020000000200000001010100ffffff00010101000101010001000100ff80ff8001000100030003000100010001000100010000000100000000ff00ff00ff000000ff00ff0000000000ff00ee00ff00ee00ff008800ff008800eeeeeeeeeeeeee00aaaaaaaaaaaaaa00888888888888880000ffffffff00000000ffff0000ff000000ffff000000000000fff00000fff00000ffeeffeeffee0000ffc00000ffc00000ff88ff88ff880000ff00ff00ff000000ff000000ff000000fefefefefefe0000fcfcfcfcfcfc0000fcfc0000fcfc0000f0f0f0f0f0f00000f0f00000f0f00000eeeeff00ffee0000eeeeeeeeeeee0000eeeeeeee00000000eeee0000eeee0000ee00eeeeeeee0000ee00ee00ee000000eaeaeaeaeaea0000aaaaaaaaaaaa0000aaaa0000aaaa0000a8a8fcfcfcfc0000a8a8a8a8a8a800008888ff00ff8800008888f0f0f8f80000888888888888000088888888000000008888000088880000880088888888000088008800880000008080888888880000808080808080 else (if page < 4 then 0xa0afafafafafafa0a0aaaaaaaaaaaaa0a0a0a0aff0aff0a0a0a0a0afafafafa0a0a0a0afa0afa0a0a0a0a0aaaaaaaaa0a0a0a0aaa0aaa0a0a0a0a0a8a8a8a8a0a0a0a0a0a0afafa0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a000a00aa00aa000a000a000a0a0a0a0a000a000a000a000a0000000a0000000909090009090900080888888888888808080808ff08ff08080808088888888808080808880888080808080808088888080808080808080808080800080808000800080088008800080008000f000f0008000800080808080800080008000800080000000800000007070700070707000700070077007700070007000f000f000700070007000700070000000700000003ff03ff000000000303ffffffff000003030303ff00ff00030303030f000f000303030303030300030303030000000003030300ffffff00030303000f0f0f000303030003030300030303000300030003030000ffff00000303000003030000030203020302030203020300030203000300ff00ff00ff0003000f003300ff0003000f000f000f0003000300ffff030003000300ff00ff0003000300ff00030003000300cf00cf00030003000f0f0300030003000f000f00030003000f00030003000300030303000300030003020302030003000300ff000300030003000f0003000300030003000300030003000000 else 0x2a0000002a00000022222222222222221f1f1f001f1f1f001f0000001f00000011001100000000000fff0fff000000000f0fffffffff00000f0f0f0fff00ff000f0f0f0f3f003f000f0f0f0f0f0f0f000f0f0f0f0f0f00000f0f0f0f000000000f0f0f00ffffff000f0f0f003f3f3f000f0f0f000f0f0f000f0f0f000f000f000f0f0e0e0f0f0e0e0f0f0a0a0f0f0a0a0f0f08080f0f08080f0f0000ffff00000f0f00000f0f00000f0e0f0e0f0e0f0e0f0e0e0e0f0e0e0e0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0a0a0f0a0a0a0f080f08ff88ff880f080f080f080f080f080f000f080f000f0808080f0808080f00ff00ff00ff000f000f00ffff0f000f000f00ff00ff000f000f00ff000f000f000f008f888f880f000f003f003f000f000f000f0f0f000f000f000f0a0f0a0f000f000f00ff000f000f000f000f000f000f000f0000000f0008000f0008000f0007000f0007000f0003000f0003000f000000ff0000000f0000000f000f000f0000000f0000000f000000000000000e0eeeeeeeeeeeee0e0e0e0eff0eff0e0e0e0e0eeeeeeeee0e0e0e0eee0eee0e0e0e0e0e8e8e8e8e0e0e0e0e0e0eeeee0e0e0e0e0e0e0e0e0e0e0e000e0e0e000e000e00ee00ee000e000e000e0e0e0e0e000e000e000e000e0000000e0000000c0c0c0c0c0c0c0c0b0b0b000b0b0b000b000b00bb00bb000b0000000b000000))) else (if page < 8 then (if page < 6 then 0x3f3f0000000000003f2a3f2affaaffaa3f2a3f2a3f2a3f2a3f2a3f003f2a3f003f0c3f003f0c3f003f00ff00ff00ff003f003f00ffff3f003f003f00ff00ff003f003f00ff003f003f003f00bfaabfaa3f003f00bf00bf003f003f003f3f3f003f003f003f2a3f2a3f003f003f00ff003f003f003f003f003f003f003f0000003f002a003f002a003f0015003f0015003f000000ff0000003f0000003f003f003f0000003f0000003f000000000000003c3cfcfcfcfcfcfc3c3c3c3cff3cff3c3c3c3c3cfcfcfcfc3c3c3c3cfc3cfc3c3c3c3c3cbcbcbcbc3c3c3c3c3c3cfcfc3c3c3c3c3c3c3c3c3c3c3c0c3c3c3c0c3c3c3c003c3c3c003c003c00fc00fc003c003c003c3c3c3c3c0000003c00000033ff000033ff000033333333333300003333333300000000333333003333330033330000ffff000033330000333300003333000000000000333033303330333033003300ff00ff003300330033003300330000003300000030303030303030302f2f2f2fa0a0a0a02f2f2f002f2f2f002e2e2e2e2e2eeeee2e2e2e2e2e2e2e2e2e2e2e0c2e2e2e0c2e2e2e002e2e2e002b2b2b002b2b2b002a2aaaaaaaaaaaaa2a2a2a2aff2aff2a2a2a2a2aaaaaaaaa2a2a2a2aaa2aaa2a2a2a2a2a2a2aaaaa2a2a2a2a2a2a2a2a2a2a2a002a2a2a002a002a00aa00aa002a002a003f003f002a002a002a2a2a2a2a002a002a002a00 else (if page < 7 then 0x8080800080808000808000008080000080008000ff00ff0080008000aaaaaaaa80008000aa00aa00800080008888888880008000880088008000800080808080800080008000800080000000800000007f7f7f7f808080807f7f7f7f000000007f7f7f007f7f7f007f7f00007f7f00007f0f77007f0f77007f007f00ff00ff007f007f007f007f007f0000007f0000007e7e7e7efefefefe7e007e007e007e0077ff77ff000000007777ffff0000000077777777000000007777770077777700777700007777000077007700770077007700770000000000727272727272727270f070f070f070f070707070f0f0f0f0707070707070707070707070000000006f6f6f006f6f6f006e6e6e6eeeeeeeee6e006e006e006e0066666666666666665f5fffff000000005f5f5f5f000000005f5f5f005f5f5f005f005f005f005f005f005f000000000055555555555500005555555500000000555555005555550055550000555500005540554055405540550055005500550054545454545454544c4c4c4ccccccccc4c4c4c4c4c4c4c4c444444444444444440404040404040403fff3fff000000003f3fffffffff00003f3f3f3fff00ff003f3f3f3faaaaaaaa3f3f3f3f3f3f3f003f3f3f3f3f3f00003f3f3f3f000000003f3f3f00ffffff003f3f3f003f3f3f003f3f3f003f003f003f3f0000ffff00003f3f00003f3f0000 else 0x88888888ff88ff8888888888ff88888888888888ff00ff0088888888f8f8f8f888888888f888f88888888888f0f0f0f088888888aaaaaaaa88888888aa88aa88888888888888ff88888888888888f8f8888888888888eeee888888888888aaaa88888888888888888888888888888800888888888800880088888888080808088888888800880088888888880000888888888888000000888888888800000000888888088888880888888800ffffff008888880088888888888888008888880088888800880088008888000088880000888800000000000088808880fff0fff088808880888088808880880088808800880888088888888888088808880888088808080888080808880088888888888888008800ffff880088008800ff00ff0088008800f8f0f8f088008800aaaaaaaa88008800888888888800880088888800880088008880888088008800880088888800880088008800880088008800000088008000880080008800080088000800880000888800008888000000ff00ff0088000000ff00000088000000888888888800000088008800880000008800000088000000000000008282828282828282828282008282820080f080f080f080f080aa80aa80aa80aa808880888088808880808080ff80ff8080808080f0f0f0f080808080aaaaaaaa808080808888888880808080808080808080808000000000)) else (if page < 9 then 0xa800a800fcfcfcfca800a800a8a8a8a8a800a800a800a800a8000000a8000000a2aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a2a2a2a222222222a222a222a222a222a0aaa0aaa0aaa0aaa0a0a0a0ffffa0a0a0a0a0a0ffa0ffa0a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a020202020a0a0a0a000a000a0a0a0a0a000000000a0a0a000a0a0a000a0a02020a0a02020a0a000a0a0a000a0a0a00000a0a0a0a0a0a00000a0a00000a0a0000000000000a000a000a000a00099999999000000009999990099999900990099009900990099000000990000008f8f8f8f000000008f8f8f008f8f8f008f888f88ff88ff888f888f888f888f888f0f88008f0f88008f008f008f008f008f000f008f000f008f0000008f0000008e8e8e8e8e8eeeee8e8e8e8e8e8e8e8e8e8e8e0e8e8e8e0e8e8e8e008e8e8e008e8a8c008e8a8c008e0e8e0e8e0e8e0e8c8c8c8c8c8c8c8c8b8b8b008b8b8b008a8aaaaaaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8aaa8aaa8a8a8a8a8a8a8aaaaa8a8a8a8a8a8a8a8a8a8a8a0a8a8a8a0a8a8a8a028a8a8a028a8a8a008a8a8a008a888a88aa88aa888a0a8a0a8a0a8a0a88ff88ff0000000088ff888888ff888888ff880088ff88008888ffffffff00008888ffff000000008888ff88ff88ff888888f8f8f8f8f8f88888aaaaaaaaaaaa888888aa888888aa88888888ffffff88 else (if page < 10 then 0xaa8aaa0aaa8aaa0aaa8a8a8aaa8a8a8aaa88aaaaaaaaaaaaaa88aa88aaaaaaaaaa88aa88aaaaaa88aa88aa88aaa8aaa8aa88aa88aa88aaaaaa88aa88aa88aa88aa88aa88aa88aa00aa88aa88aa888888aa88aa88aa00aa00aa88aa08aa88aa08aa88aa00aaaaaaaaaa88aa00aa88aa88aa88aa00aa88aa00aa88aa00aa00aa00aa888a88aa888a88aa888888aaaaaaaaaa888888aa88aa88aa888888aa888888aa888888aa000000aa88888888888888aa888800aa888800aa80aa80ffc0ffc0aa80aa80aaaaaaaaaa80aa80aa80aa80aa80aa00aa80aa00aa808080aa808080aa2aaa2aaa2aaa2aaa2a2a2aaa2a2a2aaa22aa22aaaaaaaaaa22aa22aa22aa22aa222222aa222222aa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa020202aa020202aa00aaaaaaaaaaaaaa00aa00ffffaa00aa00aa00ff00ff00aa00aa00eac0eac0aa00aa00aaaaaaaaaa00aa00aaaaaa00aa00aa00aaa0aaa0aa00aa00aa88aa88aa00aa00aa00aaaaaa00aa00aa00aa00aa00aa00aa000000aa008000aa008000aa002a00aa002a00aa002200aa002200aa000a00aa000a00aa0000aaaa0000aaaa000000ff00ff00aa000000ff000000aa000000aaaaaaaaaa000000aa00aa00aa000000aa000000aa00000000000000a8a8a8a8ffa8ffa8a8a8a8a8fcfcfcfca8a8a8a8a8a8a8a8a8a8a8a800000000a8a8a800a8a8a800 else 0xaaaaeeeeeeeeeeeeaaaaeaeaeaeaeaeaaaaaaaaaffffaaaaaaaaaaaaffaaffaaaaaaaaaafafafafaaaaaaaaaeeeeeeeeaaaaaaaaeaeaeaeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa88aa88aaaaaaaaaa888888aaaaaaaaaa88888888aaaaaaaa88008800aaaaaaaa22222222aaaaaaaa0a0a0a0aaaaaaaaa00aa00aaaaaaaaaa0000aaaaaaaaaaaa000000aaaaaaaaaa00000000aaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa8aaaaaaa8aaaaaaa88aaaaaaaaaaaaaa88aaaaaa88aaaaaa88aaaaaa00aaaaaa88aa88aa88aaaaaa80aaaaaa80aaaaaa2aaaaaaa2aaaaaaa22aaaaaa22aaaaaa0aaaaaaa0aaaaaaa08aaaaaa08aaaaaa02aaaaaa02aaaaaa00ffffff00aaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aa00aa00aaaaa8a8aaaaa8a8aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa8800aaaa8800aaaa8080aaaa8080aaaa2a2aaaaa2a2aaaaa22aaaaaa22aaaaaa2222aaaa2222aaaa222222222222aaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000ffff0000aaaa0000aaaaaaaaaaaa0000aaaa0000aaaa000000000000aaa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa8aa00aaa8aa00aaa8a8a8aaa8a8a8aaa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0aa00aaa0aa00aaa0a0a0aaa0a0a0aa8aaa8aaaaaaaaa)))) else (if page < 17 then (if page < 14 then (if page < 12 then 0xcc00cc00cc00cc00cc000000cc000000c4c4c4c4c4c4c4c4c0ff0000c0ff0000c0ccc0ccc0ccc0ccc0c0c0ccc0c0c0ccc0c0c0c0eaeaeaeac0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c040404040c0c0c0c000000000c0c0c000c0c0c000c0c00000c0c00000c000c000c000c000c000c00000000000bfbfbfbf00000000bfbfbf00bfbfbf00bfbfaaaabfbfaaaabfbf0000bfbf0000bfaabfaaffaaffaabfaabfaabfaabfaabf3faa00bf3faa00bf00bf00bf00bf00bf003f00bf003f00bf000000bf000000bebebebebebebebebbbbbbbb00000000bbbbbb00bbbbbb00bbbb0000bbbb0000bbaabbaaffaaffaabb88bb88ff88ff88bb00bb00bb00bb00bb000000bb000000afafafaf00000000afafaf00afafaf00afaf0000afaf0000afaaafaaafaaafaaaf0f0f0fa0000000af00af00af00af00af000000af000000aeaeeeeeeeeeeeeeaeaeaeaeffaeffaeaeaeaeaeeeaeeeaeaeaeaeaeaeaeeeeeaeaeaeaeaeaeaeaeaeaeaeae0c0c0c0caeaeaeae00000000aeaeae0caeaeae0caeaeae00aeaeae00aeaaaeaaeeaaeeaaae0cae0caeaeaeaeae0cae0cae0cae0cae0c0c0cae0c0c0cae00ae00aeaeaeaeae00ae00ae00ae00ae000000ae000000abababab00000000ababab00ababab00abab0000abab0000ab00ab00ab00ab00ab000000ab000000aaffaaaaaaffaaaaaaffaa00aaffaa00aaaafefefefefefe else (if page < 13 then 0xeac0eac0eaeaeaeaeac0eac0eac0eac0eac0c0c0eac0c0c0eaaaeaaaeaeaeaeaeaaaeaaaeaaaeaaaeaaac000eaaac000eaaaaaaaeaaaaaaaea00ea00eaeaeaeaea00ea00ea00ea00ea000000ea000000e666e666e666e666e0eee0eee0eee0eee0e0e0e0e0e0e0e0dcdcdcdcdcdcdcdcd500d500d500d500cfcccfcccfcccfcccececececececececcffccffccccccccccffccff00000000ccffccccccffccccccff0000ccff0000ccccffffffff0000ccccffff00000000ccccffccffccffccccccfcfcfcfcfcfccccceeeeeeeeeeeeccccccccffffffccccccccccffffccccccccccccffccffccccccccccffccccccccccccccff00ff00ccccccccfcfcfcfcccccccccfcccfccccccccccceecceeccccccccccccccffccccccccccccccfcfccccccccccccceeeecccccccccccccccccccccccccccc0000cccccccc88cc88cccccccccc88888888cccccccc44444444cccccccc00cc00cccccccccc00000000ccccccc0ccccccc0cccccc88cccccc88cccccc00cccccc00ccccc0c0ccccc0c0cccc8888cccc8888cccc8800cccc8800cccc44cccccc44cccccc4444cccc4444cccc0c0ccccc0c0ccccc00cccccc00cccccc0000ffff0000cccc0000cccccccccccc0000cccc0000cccc000000000000ccc0ccc0ccc0ccc0cc88cc88cccccccccc88cc88cc88cc88cc888888cc888888cc4ccc4ccc4ccc4ccc00cc00cccccccc else 0xeeaaeeaaeeaa0000eeaaeeaacc00cc00eeaaeeaa00000000eeaaee22eeaaee22eeaaee00eeaaee00eeaace0aeeaace0aeeaaccaaeeaaccaaeeaacc00ffaaff00eeaacc00eeaaeeaaeeaacc00eeaacc00eeaaaeaaeeaaaeaaeeaaaaaaffaaffaaeeaaaaaaffaaaaaaeeaaaaaaeeeeeeeeeeaaaaaaeeaaeeaaeeaaaaaaeeaaaaaaeeaaaaaacc000000eeaaaaaaaaaaaaaaeeaaaa00eeaaaa00ee88ee88eeeeeeeeee88ee00ee88ee00ee888888ee888888ee80ee80ee80ee80ee6eee6eee6eee6eee66ee66eeeeeeeeee66ee66ee66ee66ee666666ee666666ee22ee22eeeeeeeeee22ee22ee22ee22ee22aaaaee22aaaaee222222ee222222ee0eee0eeeeeeeeeee0eee0eee0eee0eee0e0e0eee0e0e0eee00eeeeeeeeeeeeee00ee00ffffee00ee00ee00ff00ff00ee00ee00eeeeeeeeee00ee00eeeeee00ee00ee00eee0eee0ee00ee00eeaaeeaaee00ee00ee88ee88ee00ee00ee00eeeeee00ee00ee00ee00ee00ee00ee000000ee00aaaaee00aaaaee00aa00eeeeaaaaee00aa00ee00aa00ee006600ee006600ee000e00ee000e00ee0000eeee0000eeee000000ff000000ee000000eeeeeeeeee000000ee00ee00ee000000ee000000ee000000aa000000ee00000000000000ececececececececeaeaeaeaffeaffeaeaeaeaeaeaeaeaeaeaeaeaea00000000eaeaeac0eaeaeac0eaeaeaaaeaeaeaaaeaeaea00eaeaea00)) else (if page < 15 then 0xeeeeeeeeffeeffeeeeeeeeeeffeeeeeeeeeeeeeeffaaffaaeeeeeeeeff00ff00eeeeeeeefefefefeeeeeeeeefeeefeeeeeeeeeeeeeeeffeeeeeeeeeeeeeefefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaeeeeeeeeeeeeee00eeeeeeeeeeee0000eeeeeeeeee00ee00eeeeeeeecccccccceeeeeeeeaaeeaaeeeeeeeeeeaaaaaaeeeeeeeeeeaaaaaaaaeeeeeeee66666666eeeeeeee22222222eeeeeeee0e0e0e0eeeeeeeee00ee00eeeeeeeeee0000eeeeeeeeeeee000000eeeeeeeeee00000000eeeeeecceeeeeecceeeeeeaeeeeeeeaeeeeeeeaaffffffaaeeeeeeaaeeeeeeeeeeeeeeaaeeeeeeaaeeeeeeaaeeaaeeaaeeeeee88eeeeee88eeeeee66eeeeee66eeeeee22eeeeee22eeeeee0eeeeeee0eeeeeee00ffffff00eeeeee00eeeeeeeeeeeeee00eeeeee00eeeeee00ee00ee00eeeecccceeeecccceeeeaaaaeeeeaaaaeeeeaaaa00000000eeee0000eeee0000eeee000000000000eeeaeeaaeeeaeeaaeee0eee0eee0eee0eee0ee00eee0ee00eecceecceeeeeeeeeecceecceecceecceecccccceecccccceeccaa00eeccaa00eecc0000eecc0000eeaeeeaeeeeeeeeeeeaeaeaeeeaeaeaeeeaaeeeeeeeeeeeeeeaaeeaaffffeeaaeeaaeeaaffaaffaaeeaaeeaaff00ff00eeaaeeaaeeeeeeeeeeaaeeaaeeeeeeaaeeaaeeaaeeeaeeeaeeaaeeaaeeaaeeeeeeaaeeaaeeaaeeaaeeaaeeaaeeaacc00eeaaeeaaeeaaaaaa else (if page < 16 then 0xf2f2f2f0f2f2f2f0f2f2f232f2f2f232f2f2f222f2f2f222f2f2f202f2f2f202f2f2f200f2f2f200f1f1f1f100000000f1f1f100f1f1f100f1f10000f1f10000f100f100f100f100f1000000f1000000f0f0f0fcf0f0f0fcf0f0f0faf0f0f0faf0f0f0f0fffff0f0f0f0f0f0fff0fff0f0f0f0f0fafafafaf0f0f0f0f8f8f8f8f0f0f0f0f0f0fff0f0f0f0f0f0f0fefef0f0f0f0f0f0fafaf0f0f0f0f0f0f8f8f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f000f000f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f070f0f0f070f0f0f030f0f0f030f0f0f010f0f0f010f0f0f000f0f0f0f0f0f0f000f0f0f000f0f0f000f000f000f0f0c000f0f0c000f0f0a000f0f0a000f0f08080f0f08080f0f08000f0f08000f0f07070f0f07070f0f00000f0f00000f0f0000000000000f0a0f000f0a0f000f080f080f080f080f080f000f080f000f070f070f070f070f000f000ff00ff00f000f000f0f0f0f0f000f000f000f000f000f00000000000f0000000f0000000efefefef00000000efefef00efefef00efeeefeeffeeffeeefeeefeeefeeefeeef00ef00ef00ef00ef000000ef000000eeffeeff00000000eeffeeeeeeffeeeeeeffee00eeffee00eeeeffffffff0000eeeeffff00000000eeeeffeeffeeffeeeeeefefefefefefeeeeeeeeeffffffee else 0xfcfcfcfcfcfc0000fcfcfcfcccccccccfcfcfcfc54545454fcfcfcfc0000fcfcfcfcfcfc00000000fcfcfcf0fcfcfcf0fcfcfcccfcfcfcccfcfcfc00fcfcfc00fcfc0000fcfc0000fcf0fcf0fcfcfcfcfcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcf0f0f0f0f0f0f0fcccfcccfcfcfcfcfcccfcccfcccfcccfcccf000fcccf000fcccccccfcccccccfcc0c0c0c0c0c0c0fc80fc80fc80fc80fc7cfc7cfc7cfc7cfc00fc00fcfcfcfcfc00fc00fc00fc00fc00fc0000000000fc000000fc000000fafafafafffafffafafafafafafafafafafafafaaaaaaaaafafafafa00000000fafafa00fafafa00faf0faf0faf0faf0faf0f0f0f0f0f0f0faaafaaafaaafaaafa0a0a0a0a0a0a0afa00fa00fafafafafa00fa00fa00fa00fa00fa00aa00aa00fa000000fa000000f8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f888f888f888f888f800f800f800f800f7f7f0f0f7f7f0f0f7f0f7f0f7f0f7f0f700f700f700f700f6f6f6f6f6f6f6f6f6f6f600f6f6f600f500f500f500f500f500f50055005500f4f4f4fef4f4f4fef4f4f4fcf4f4f4fcf4f4f4f4f4f4fcfcf4f4f4f4f4f4f4f4f4f4f444f4f4f444f4f4f400f4f4f400f3f3f3f300000000f3f3f300f3f3f300f3f30000f3f30000f3f0f3f0fff0fff0f3f0f3f0f3f0f3f0f300f300f300f300f3000000f3000000f2f2f2f2f2f2fefef2f2f2f2f2f2fafaf2f2f2f2f2f2f2f2))) else (if page < 20 then (if page < 18 then 0xff008000ff008000ff007700ff007700ff005500ff005500ff003f00ff003f00ff003f003f003f00ff000f00ff000f00ff000300ff000300ff00030003000300ff000000ffff0000ff000000ffeeeeeeff000000ff888888ff000000ff00ff00ff000000ff000000ff000000ee000000ff00000088000000ff0000003f000000ff00000003000000ff00000000000000fefefefefffefffefefefefefefefefefefefefe00000000fefefefcfefefefcfefefefc00000000fefefefafefefefafefefef0fefefef0fefefeeefefefeeefefefeee00000000fefefeaafefefeaafefefe00fefefe00fefe0000fefe0000fefcfefcfefcfefcfefafefafefefefefefafafafefafafafef0fef0fefefefefef0f0f0fef0f0f0fef0f0f0f0f0f0f0feeefeeefefefefefeeefeeefeeefeeefeeef000feeef000feeeeeeefeeeeeeefeaafeaafefefefefeaafeaafeaafeaafeaafc00feaafc00feaaaaaafeaaaaaafe80fe80fe80fe80fe800000fe800000fe7efe7efe7efe7efe00fe00ff00ff00fe00fe00fefefefefe00fe00fe7efe7efe00fe00fe00fefefe00fe00fe00fe00fe00fe00fe000000fe00fa00fe00fa00fe00f000fe00f000fe00ee00fe00ee00fe00aa00fe00aa00fe00aa00fc000000fe008000fe008000fe000000fe000000fcfcfcfcfffcfffcfcfcfcfcfefefefefcfcfcfcfcfcfcfcfcfcfcfcfcfccccc else (if page < 19 then 0xff2a2a2aff2a2a2aff0fff0f00000000ff0fff00ff0fff00ff0f8808ff0f8808ff0f0000ff0f0000ff0e0e0eff0e0e0eff0aff0aff0aff0aff0a0a0aff0a0a0aff08ff08ff88ff88ff08ff08ff08ff08ff080808ff080808ff03ff03ff030000ff030303ff000000ff020202ff020202ff00ffff00000000ff00ffeeffeeffeeff00ff88ff88ff88ff00ff00ffffff00ff00ff00fff0fff0ff00ff00ffeeffeeff00ff00ffc0ffc0ff00ff00ff88ff88ff00ff00ff00ff00ff00ff00ff00ee00ff00ff00ff008800ff00ff00ff007700ff00ff00ff003f00ff00ff00ff003300ff00ff00ff001100ff00ff00ff000f00ff00ff00ff000300ff00ff00ff000000ff00ff00ee00ee00ff00ff0088008800ff00ff0088000000ff00ff0080008000ff00ff003f003f00ff00ff000f000f00ff00ff0003000300ff00ff000000ff00ff00ff0000000000ff00fe00ff00fe00ff00f000ff00f000ff00f000ff000000ff00ef00ff00ef00ff00ee00ffffeeeeff00ee00ff00ff00ff00ee00ff00ee00ff00ee00ff000000ff00ee00ee00ee00ff00ea00ff00ea00ff00cc00ff00cc00ff00c000ff00c000ff00bf00ff00bf00ff00af00ff00af00ff00ab00ff00ab00ff00aa00ff00aa00ff00a800ff00a800ff008f00ff008f00ff008800ffff8888ff008800ff00ff00ff008800ff008800ff008800ff000000ff00880088008800 else 0xffc0ffc000000000ffc0c0c0ffc0c0c0ffc0c0c0c0c0c0c0ffbfffaaffbfffaaffbfff00ffbfff00ffafff00ffafff00ffabff00ffabff00ffaaffaaffeaffeaffaaffaaffaaffaaffaaff00ffaaff00ffaaff0000000000ffaaaaaaffaaaaaaffaa0000ffaa0000ffa8ff00ffa8ff00ffa8a8a8ffa8a8a8ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ffa0a0a0ffa0a0a0ffa00000ffa00000ff8fff88ff8fff88ff8fff00ff8fff00ff88ff88ffffff88ff88ff88fff8fff8ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff888888ff88ff88ff880000ff88ff88ff00ff00ff88ff8888888888ff88ff08ff88ff08ff88ff00ffffff00ff88ff00ff88ff88ff88ff00ff88ff00ff88ff00ff00ff00ff88ff0088880000ff88ff0000000000ff88f080ff88f080ff888f88ff888f88ff888888ff88ff88ff888888ff888888ff888888ff000000ff88888888888888ff88888800000000ff888800ff888800ff880000ff880000ff880000ff000000ff80ff80ffaaffaaff80ff80ff80ff80ff80ff8000000000ff80ff00ff80ff00ff808080ff808080ff800000ff800000ff7fff00ff7fff00ff77ff7700000000ff77ff00ff77ff00ff70ff70ff70ff70ff3fff3fff3f0000ff3fff3f00000000ff3fff00ffffff00ff3fff00ff3fff00ff3faa2aff3faa2aff3f3f3fff000000ff2aff2affaaffaaff2aff2aff2aff2a)) else (if page < 21 then 0xffff0303ffff0000ffff030300000000ffff0300ffff0300ffff0202ffff0202ffff0000ffffeeeeffff0000ffff8888ffff0000ffff0000ffff0000ff000000ffff0000f0f00000ffff0000cc000000ffff0000c0c00000ffff0000aaaa0000ffff0000aa000000ffff000088880000ffff000088000000ffff000080800000ffff000000000000fffefffefffefffefffeffeefffeffeefffeff00fffeff00fffefefefffefefefffcfffcfffcfffcfffcfcfcfffcfcfcfffafffafffafffafff8fff8fff8fff8fff0fff0fff0fff0fff0fff000000000fff0ff00fff0ff00fff0ff0000000000fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff00000fff00000ffefff00ffefff00ffeeffeeffffffeeffeeffeefffefffeffeeffeeffeeffeeffeeffeeffeeff00ffeeffeeffeeeeeeffeeffeeffee0000ffeeffeeff00ff00ffeeffeeeeeeeeeeffeeff22ffeeff22ffeeff0effeeff0effeeff00ffffff00ffeeff00ffeeffeeffeeff00ffeeff00ffeeff00ff00ff00ffeeff00eeee0000ffeeff0000000000ffeeefeeffeeefeeffeeeeeeffeeffeeffeeeeeeffeeeeeeffeeeeeeff000000ffeeeeeeeeeeeeeeffeeeeee00000000ffeeee00ffeeee00ffee0000ffee0000ffeaffeaffeaffeaffeaffc0ffeaffc0ffeaffaaffeaffaaffeaff00ffeaff00ffeaeaeaffeaeaeaffccffccffccffccffc0ffc0ffc0ffc0 else (if page < 22 then 0xffffffff000000eeffffffff000000aaffffffff00000088ffffffff00000000fffffffefffffffefffffffcfffffffcfffffffafffffffafffffff0fffffff0ffffffeeffffffeeffffffeeffffff00ffffffeeffeeffeeffffffeeeeeeeeeeffffffeaffffffeaffffffc0ffffffc0ffffffaaffffffaaffffffa8ffffffa8ffffffa0ffffffa0ffffff88ffffff88ffffff88ffffff00ffffff88ff88ff88ffffff8888888888ffffff80ffffff80ffffff7700000000ffffff3fffffff00ffffff3f00000000ffffff3300000000ffffff2affffff2affffff1100000000ffffff0f00000000ffffff0effffff0effffff0affffff0affffff08ffffff08ffffff03ffffff00ffffff02ffffff02ffffff00ffffffeeffffff00ffffff88ffffff00ffffff00ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffff0f0fffff0f0ffffeeeeffffeeeeffffeeee00000000ffffee00ffffee00ffffee0000000000ffffccccffffccccffffcc00ffffcc00ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaa00ffffaa00ffffaa0000000000ffffa0a0ffffa0a0ffff8888ffff8888ffff888800000000ffff8800ffff8800ffff880000000000ffff8080ffff8080ffff3f3fffff0000ffff3f3f00000000ffff3f00ffff3f00ffff2a2affff2a2affff0e0effff0e0effff0a0affff0a0affff0808ffff0808 else 0xffffffffffffffeeffffffffffffff88ffffffffffffff00ffffffffffffeeeeffffffffffff8888ffffffffffff0000ffffffffff00ff00fffffffffcfcfcfcfffffffffafafafafffffffff0f0f0f0ffffffffeeeeeeeeffffffffee00ee00ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffa0a0a0a0ffffffff88888888ffffffff88008800ffffffff80808080ffffffff3f3f0000ffffffff3f003f00ffffffff2a2a2a2affffffff0e0e0e0effffffff0a0a0a0affffffff08080808ffffffff03030000ffffffff03000300ffffffff02020202ffffffff0000ff00ffffffff0000f0f0ffffffff0000eeeeffffffff0000c0c0ffffffff00008888ffffffff000000f0))))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xa5f12ce0d2f88c706acc443831ce359bf8e7194dfccf8c46debe44437f5f2291b7 else 0
  | 3 => if page < 1 then 0xab31ce099f3ab31ce209caab31ce361c1b374be261c1a5f2a5f4a1bab31cdf5a1aaf91cdefa1aaf91ce091f3af91ce099e8af91ce1c1caaf91ce209c9af91ce319c1af91ce2a9c1af94e2261c1af94c2261c1af9332261c1af956e221c1af91ce361bfaf91ce331bfaf9332361b7af9342311b7a73130e0875953188e0867a73130e0867af91cdf5a19af91cdf5a18af91cdf5a17af94e6281c1af94e6271c1af94e6269c1af94e6261c1af94e6259c1af94e6241c1af94e6239c1af94e6229c1a732a6359bfa732a6329bfaf94e6261bfaf94e6299b7a732a6359b3af94e6261b3a732a4e08aea732a4e08ac else 0
  | 4 => if page < 3 then (if page < 1 then 0xa1f1cc79b91cc78e6a8668e6a7e68e6a1a68e69fe68e69d268e69ce68e69ca68e69c668e69c2692e9ad68e69a668e6996699894667d286f894086b47be86b88e683a68e683268b87cf88267cf88247cf88947cf48927cf48907cf488e7cf48267a3887072b888272788da70788d870788cc70788c870788c670788b670788b070788ae70788ac70788a870788a670788a2707889e707888870788d86ff88cc6ff88d86cf83826b783826b3876e67f85cc60f84344c783e63bf839435783822b783822af83822ab83822a784341d5c0010bb900086bc000867c000863c00052f9 else (if page < 2 then 0x8e6c4507c9282099f3c239c593e724738aa7ce492ee1cf9a91cdbe1f39239b7a3e724736f07ce48e6ddcf9c91cdbb1f3924bb6f3e6a4736da7ce48e6dacf9c934daa1f39239ad03e7247376e7a248e6ebcf4491cdb81e89239ad33d124a088272b09411b0e0e11fe361c1c2cdc4c383855b8987070a8f130e0e14be261c1c26844c383847389870708e70e0e0c31ce181c1866642a3830c2a4cc7070854958e0e10b5289c1c215a5138384284a27070854918e0e11ce209bf8639c3937f0cd08d86df0999104dbc3188e09b7a2261c136f84623826be8898704d7e0f40e099dc297c4128c4c7387051618e70c0a2c30a8e0940c1d41c123ec4735044622a5ebe0671304cf987562209ca0eac46c3821d588d870433b11ace086662311c10cd444c38219b08d67041c31130e0838c0004fd8558800acf1cc7 else 0x156639c413e63d6be55b8e704cf9d7c8e709a041f3af91cdfc3d03e756639beb76e7cebe4737beedcf9d2f940fadc11f3a5f2a5f4b823e74be503eb7007ceacc737d6dc0f9d7c8e6f7db81f3a5f25df5b493e75f1ec3d06927ce97ca97d2b50f9d598e6fad699f3af91cdefad33e71b9f5b14516756be55b8e7104e557cab71ce361c1ab31ce20ab83835f239c41534706be4cc882944e0d7c8e70dd289c1af91ce20a9a37f56639c41570516be473882a68a2d7c8e71054d144a7325de81f321b4be54c413e63da97ca98807cc7b57c8e70e0f98f5af91ce181f31eb5f239c413d03d6be4738827a07a52f940fad8d278a5f2a5f4b1a4f14be54beb6329e297ca07d6c693b5598e6fad8d26caf91cdefb1a4d95f239beb6229b2be4d37d6bfd28d7c8e6faddba22af956e39beb4354be54be9634842acc737d6c6907d7c8e6f7d8d20f)) else 0
  | 5 => if page < 24 then (if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xa67ea27ea1fea17ea03e9ffe9fbe9f7e9f3e9efe9ebe9e7e9e3e9dfe9dbe9d3e9cfe9cbe9c7e9c3e9bfe9bbe9b7e9b3e9afe9abe99fe997e993e89bd853d84fe847e843e83fe83be837e833e82fe6d5f593b587b547b543b53fd533d4dfb4cbb4c7b4a3b49fb48fb40bb2e7e2b9f1e1f1d5f1bdf1b1f1a5f19df181f179f003f else (if page < 2 then 0xa5e038fa5e034fa5e030fa5e02cfa5e028f8e6a6a68e69c66001173b001087b00107fb00100bb001007b001003b000ffbb000ff7b000ff3b000fefb000fb7b0015fdf0015f5f0012a3700129f700129770012877001283700125b700124f70012477001243700123f700123b7001237700122b70012277001223700121b7001217700120f700120b7001207700120370011ff700114370011377001133700112f7001123700111f7000b6bb000adfe000adbe000aa7e000a9fe000a9be000a97e000a93e000a8fe000a8be000a87e000a7fe000a7be000a77e000a6fe000a6be else 0x5f02f795f02f395fa2ef95f02ef941e2efc3822ef928a2ef95f02eb9a5e2d0f3e62b7c5f02af93e62afc3e62a7c76e28bcb36260fa5e244fa5e214f8e61de78e61da78001d5b7e81d5b8981d575641d5e5621d5e54a1d5e5341d5e4f01d5e41e1d5e2c61d5b29c1d5d2621d5b52c1ade568199e560199e4ea199e43419bc9401817568181e534181e140180f7be17db7d0175b93e15d793c125793c109793a10979381097a620f0f9380e175540d9ea5e0ccfa5e0c0fa5e0a8fa5e09cfa5e098fa5e08cfa5e078fa5e06cf92e05d792e0597a5e048fa5e044fa5e040fa5e03cf)) else (if page < 4 then 0x474447a29c44793e643fc3e643bc3e6433c3e642fca5e428f3e642bc3d0427c350427c3e6423c3e641fc3e641bc3e6413c5f040b93e640b95f040795f04039a5e3dcfa5e3d8fa5e3a8fa5e370f5f036f95f036b95f036795f035f95f035b95fa35795f435795f035795e8357941e357c382357930635792c6357928a35795f035395f034395f033f95f033b95f033795f033395f032f95f032b95f032795f032395f031f938231f928a31f95f031b95f031795f03139a5e30cf5f030f95f030b95f030795ee30795e83079382307930c307930630795f030395f02ff95f02fb9 else (if page < 5 then 0x5f05a795f05a395f059b95f05979882593963259395f059395ee593987058f994058f362258f95e858f953458fa30658f97be58b9882587987058795f058795f058395f057f95f057b9882543976e54397d253f97e453b994053b57be53b97a253b979c53b953453bc534537c42a523c88251b9a5e518f8865179882517987251798705179864517985e51798565179850517988251396644c7965e4c79ab24c5b8d64c5b8984c735504c7a54a4c7a5344c7a4744c7a41e4c7a3484c7a3384c792c64c792b44c7929c4c7947447fa29c47f99da462b508463a502463a502447a else 0x76e7afc8e67ae78e67aa776e7a7c8e67a678d87a3c8d07a3c76e7a3c75e7a3c7507a3c7467a3c7367a3c7047a3c6a87a3c5a67a3c81c7a398187a398e67a2776e79fc8e679e776e78fc76e78bc8e678a79a675679a475679987567a5e750f8e67467a90730f76e70bc8867079882707987270798707079864707985e707985a70798587079856707985070798826ff98726ff98e66fe79986de78826cf93e667bc38267bc3e6677c382677ca5e628f88261f95a660fc8d860f988260f987c60f987660f987260f987060f986260f985460f966460f988260b98825f39a5e5c8f))) else (if page < 9 then (if page < 7 then 0x6ea7cfc6e87cfc6e67cfc6e47cfc6e27cfc6e07cfc6de7cfc6dc7cfc6d87cfc6d67cfc6d47cfc6d27cfc6d07cfc6ce7cfc6ca7cfc6c87cfc6c47cfc6c27cfc6c07cfc6bc7cfc6ba7cfc6b87cfc6b67cfc6b47cfc6b27cfc6b07cfc6ae7cfc6ac7cfc6aa7cfc6a87cfc6a67cfc6a47cfc6a27cfc6a07cfc69e7cfc69c7cfc6987cfc6967cfc6947cfc6927cfc6907cfc68e7cfc66a7cfc5ae7cfc5ac7cfc5aa7cfc5a87cfc5a67cfc5a07cfc59e7cfc59c7cfc59a7cfc5967cfc5947cfc5907cfc8667cf981a7cf98187cf98167cf98147cf944c7cfc4487cfc42c7cfc76e7cbc else (if page < 8 then 0x8da7cfc8d87cfc8d07cfc8ce7cfc8cc7cfc8c87cfc8c67cfc8c07cfc8be7cfc8bc7cfc8ba7cfc8b67cfc8b07cfc8ae7cfc8a87cfc89e7cfc8887cfc7f27cfc7ec7cfc7847cfc7827cfc7807cfc77e7cfc77c7cfc77a7cfc7787cfc7747cfc7727cfc7707cfc76e7cfc76c7cfc76a7cfc74c7cfc74a7cfc7487cfc7467cfc7447cfc7427cfc7407cfc73e7cfc73c7cfc73a7cfc7387cfc7367cfc7347cfc7287cfc7247cfc7187cfc7167cfc7147cfc7127cfc7107cfc70c7cfc70a7cfc7087cfc7067cfc7047cfc7027cfc7007cfc6fe7cfc6f67cfc6f27cfc6ee7cfc6ec7cfc else 0x8e6a6a765c9f3ca709e2ea669e2e9409e367d29e3a7be9e3a6329e3c6229e3c9409db68e69c768e69c6e6209c7c61e9c7c8e69c679a098f660895bc60695bc9a294769a0947699c947699a94769a6946e608947c604947c9a6946760491bc8e6902776e89bc76e88bc8e688a7ab686bc8e686bc87e843c7d2843a88683fc87083fc85683fc85083fc77e83fc73683fc6b483fc69283fc64683fc94083f67be83fa62283fc60283fc60083fc5fc83fc88283bc76e83bc62283bc882837c622837c882833c76e833ca5e818f92e7f5776e7dfc76e7dbc76e7d7c76e7d3c7687d3c)) else (if page < 10 then 0xa591ce7a3f1ce7a2d1ce7a2b1ce7a291ce7a271ce7a251ce7a231ce7a211ce7a111ce7a071ce79f71ce79f51ce79f31ce79e51ce79d71ce79c51ce79c31ce79c11ce79bf1ce79bd1ce79bb1ce79a91ce799d1ce78e718e78e71567a711327ab711278e6f327a5ef10f92eef178e6e7e78e6e7a78e6e7678e6e7278e6e6e78e6e6a78e6e4a78e6dee7a0ed5279e6d527a5ed4cf8e6d3678e6d0278e6cea78e6bbe78e6b7678e6b1a7ab2a95e81ea6ba81ca6ba818a6ba800a6ba7fea6ba7eaa6ba7e8a6baab2a69e8e6a6ae8d6a69e8d2a69e898a6b6626a6bc624a6bc622a6bc else (if page < 11 then 0x6fc7cc3338df4f986671ad1f30cce2d23e6199c5a27cc333889cf986671db9f10cce44139419b88d870433710ece0866657c1670cccbe429c199987651433327cc86866717c0dd0cccaf81a619997507cc30b956e398601e9c4970ae3d598e615c792efa02ba71cdef8578e4bab40aeb47353415e6878be024b30a57c049661daf808ccd3892e1087ab31cc210f25df40424e39bdf0851c975681096a5eab0211d1cd4d0429a4baaa078b46c3820e387ccc501932f918a032661daf8064cd2f9400447a5efa408974bd5a8113a9795c0226d2f26a044ba5e2a0088f4be5000c1e97be90185d2f56a030ea5e4d406174bc5400c1e39b9b3e724736ec7ce48e6edcf4480027ec41e4004a08019800940fb730015a239ce002b2c739c005628e73800ac31ce700158239ce002afc739c0055e8e73800ab71ce7 else 0xa5f280430f25e398861e97be910c5d2f56a218eab31cc3b8f566398761e39b9b0ea3c4141e1d5c76e83c3ab8edd0087572361f30eae3c03e61d5c76e7cc3ab8ec0f987571d79f30eae3a93e61d5c7507cc3ab8e8cf987571cd9f30eae3823e61d5c6a87cc3ab8b4cf987572061f30eacbb73d01d5c8e67a03a8f104e087566209830eacc412c61d595f058c3ab3104a287564f99090eae2f81b01d595f03543ab2be06087565db9f30e0e4415f01b1976e7cc36391057c06b65cc9f30d6e3b73e61a9c76e7cc34b8edcf986772209c10cecb18554199c62eaa833390ed0786671d420f0cce31441e199c8267cc33711acf986672311f30cd644c3e619b47f47cc3338f1cf986671e19f30cce3bc3e6199c7667cc3338eb8f986671d69f30cce3ac3e6199c7547cc3338ea0f986671cb9f30cce3953e6199c)))) else (if page < 18 then (if page < 15 then (if page < 13 then 0x8707cc7af10d8f98f5e21a1f31ebc4323e63d7885e7cc7af10acf98f5e2141f31ebc4413d03d788e67a07acd104d40f5e239c231e91c735343d268827cc7a71104f40f4e24ba2f1e6b4977a03b13a5efa47517566398e91e39bdf1d31c735343a66ab31cc6a8f1cd888d596acaf81aacc7353435665f0a686af0be0ca0d5e0f98f51abc52f5f032d992ebe065e30a57c0cbc51993e18fc1f31ea31f8a5f280608f566398c11e97b191826c736223065a70be060d32817c0c1c697ab518272f856a30788e6a6860ccbe14d0c1e17c196183c2f83283078a5f280600f2817c0c0c6acc731763c736222ee5854be05de31cd4d0bb98f98f5177c5598e62cc78e6c4459cb1cd4d0b39a39a9a16533b73e6285c72c7cc4d58aa8f309a3a97ca01243c978e62487a5efa44916f91ec0922e97ab512474375f02329 else (if page < 14 then 0x76e6a098f0edcd0931e1db99c263c1f33384c7876e7cc9870e64f9927e1db9f3247c32f46647f88388cc8fe50451991fca0823323f93a846647daa5e8a88f96ea0f991f71db9c123fc52f466464b9df1cc8c474bd191182e39a2e2311bb7382463865e8cc88f107519911ca08a33223947345c446376e70488f125de810d4e4b9f321ae52f7d2428b7d27cc8571566399091e39bdf2131c7353442667e47cc84f1280f9909d1ef9f3213c3d33e642787a27cc84f0f38f9909e0f99a2213c1f326242783e647c84f07cc88909e24bbd01f89c977a03e93a5f0987b974bdf48f72e97c411ec5d2f84c3d8ba5e8cc7b1d4bd190f63a209f31edc4403e63db8a5e7cc7b1d1ce1c0f58e39c231eb1d598e63d478e6f7c7ac71cd888f59639a9a1eb347345c3d668867cc7af1104f98f5e21d1f31ebc4393e63d78 else 0x854704d7e35662098366acc733063c7362260e5882a68c1f11cd4d1839a97b072f06c2a5f05e31a5f280b88f566399711e97b192e26c736225c65a5ead4b89d1cd4d1719a79a512e333034a25c74a5f280b80f5663996b1e39b112d72b075fe5ae5854be0b5e2c1d7916b9639a9a2d734975f059d9941104b1e356e399638e502f82c78c4153458f85f0a68b1f156e3994e9639bd029d8c975fe5215882704a47128220945c639c2a28b8d598e651478e6c44a2cb1054d145e239a9a28b344153451388e6a68a24d104e0940e297a332725bb73e64db8ab71cc98c71ce119318e39b9b2631b2f4664c788e68b898c710507931e1dba0f263c3b74024c788d87cc98f0edcf9931e1d79f3263c3a83e64c787467cc98f0e6cf9931e1c11f3263c3543e64c785a67cc98f0edcf4131e2399e82631bb73824c78)) else (if page < 16 then 0x7beedcf4711ce209e89639bb73d12d598e67a078e6f7cf4471cd551e89a39a9a3d134734a27a268e6918f44d1cd459e09a39a8b3b9347351676669a0edceae94be501d51eacc733aa3d488e67547a5efa4ea971cdef9d58e39bda3ab1d2f56a754e8e6a68eacd1cd4a9d59a39a913ab347351e75668e6a34eacd1cd461d59aa428b3aa748251675668eea2ceacd1d1459d59a39a8b3ab346e51675668e6a28eacd4be501d41e97c973983d598e673078e6f7ce64725d551cc5a39a9a399355b88272b88e7104e57156e361c1e26846c383c4738d87078882af0e0f1282209c1c63fc413838cd085470718e70a8e0e3566399c11e20a9a383c4735347066882998e0f1105319c1e220a56383c4cc4a27066882918e0f11054d1bfe239a9a37f34d08826df18e6a2cdbcd1b0e09b7e1aa1f335fa46c3826bf8 else (if page < 17 then 0x78cd50f9e8f15aa1f3d2503533e7a4976a07cf48e6d40f9e925da49f3d1e83493e7a3e95a87cf8940b4cf9e8f7d699f3e239acc3e7a4735927cf4818af0f9f0ea15e1f37172abc3e6e4a08187cf18e70e0f9cb1ce181f39639c083e72c737367ce58e6dd8f9cb4bd951f3364bb213e6ad698e67cc7acd1ccf98f58e399f31eacc733e63d238e67cc79eb1ccf98f372399f31e39be33e71c737c47ce38e6f80f9c71cdef9f38e39bde3e71c737ac7ce38e6f50f9c7331e81f38e39ae43e72c735407ce68e6a7cf9cd1cd4e1f39a39a9b3e7340e5347cf8818a68f9f11cd4d1f39a39a993e734735047ce68e69c4f9cd0312b1f3e2152563e7a42b4a27cf4850944f9e934d289f39a692513e734cc4a27ce6a5e940f99d1cd259f39a062463e7c42a48c7cf48e6894f9e8ea0ff9f372acbb73d0e47376e7a2c else 0xafaedcf9b9299db9f3d2523b73e7a4a376e7cf4944edcf9e9281db9f3d24abb73e7a49476e7cf4920edcf9e921ddb9f3d2413b73e7a48176e7cf48feedcf9e8fa9db9f3e1f1bb73e7c3e276e7cf87c2edcf9f0f81db9f3e1efbb73e7c3de76e7cf87aaedcf9f0f51db9f3e2acba33e6e3df7467cf8ab2e6cf9b91cdcd9f3b1efb9b3e7c5387047ceca6ce08f9d9281c11f3d2463823e7a3e97047cf87bee08f9f0f75c11f3e2503803e7a4736ec7cec8e6d98f9e91cdb19f3d239b5f3e7a4976b67cf48e6d6cf9e925dad1f37239b5a3e7a3d06b47cf49bed50f9e9361aa1f3d2683543e7a4bb6a87cf495cd50f9e92b5aa1f3d2553543e7a5386a87cec940d50f9e9241aa1f3d23f3543e7a47a6a87cf48eed50f9e91d1aa1f3d239b543e7a46e6a87cf47d2d50f9f0f7daa1f3e1e8b543e7a3ce6a87cf4))) else (if page < 21 then (if page < 19 then 0x8e6d254d4d1cda329a9a39b445353473684a6a68e6a954d4d1ce20a999a39bb75333473882a1a68e70dd434d66e97a783aadc734f1354e8e69e268e710538cd1ce132719a39bb74e3355b8e69b269a71cd28cd1cd81a51d239b024a3a4e860094749b0bfd28e91cd76a519a39adc4a3347358a94668e6a2d28cd0a145a519a39a714a334d85fe91b4ab31cd210f1cd88a429639a9a485347353490268e6a2d1ecd1cd45a1e9a20be9421c3e976e843894110507e91ce1520fd220bdf41fc4a076e83f47beedd07f11cdaa20fd2adc7341f34735fe83f4940edcfa68fa5db9f4e2adc133e7c4738267cf884d020f9f1282361f3d2cdc4c3e7a55b8987cf4a5f130f9e91ce261f3d239bf73e7a46c7be7cf88ccf7cf9f0fbddb9f3e1f73b73e7c3ed76e7cf87d8edcf9f1601db9f372bfbb73e6e57e76e7cdc else (if page < 20 then 0xab71ce004766e97bed2ecb5598e63d91ab31cc7aef566398f5d2acc731eb75598e63d6bab31cc7ab3472398f566864731eacce88e63d599b11cc7ab31ce360f66e97c4c1eb347376e3d648e6edc7ac71cddb8f56639bb71e91c7376e3d0f8e6edc79eb1cddb8f56639b9b1e97ca06a83d598e6d507aa71cdaa0f4be503531e97c976923d598e6d247ab31cda20f56e39aa59a39c4153f347384ca7e68e6edd4fcd1ce20a9d9a39c41537347376ea6e6b331cd4d4d65a39a9a9aca47353535918e6a6a6af51cd4d4d5de39a9a9ab9473535356e8e6a6a6ab71cd4d4d4aa39a9a9a94c73535351c8e6a6a6a191cd4d4d40239a9a9a7f47353534e88e6a6a69b11cd4d4d1ce3629a9a39c6a5353473882a6a68e70ed4d4d1ce1c29a9a39c2a5353473850a6a68e6edd4d4d1cdd429a9a39b9b53534736a8a6a6 else 0x8e6a69199118aadc733e642648e6f40f9909c24bbd04663e9292ef41178fa4a4bbd03e63e9292ebfcf98fa524ba3323e3e92a5efa5198f62a97be93e63d8aab31ce208f50eacc7384c3d438e7105888f58639c266223d618e71054d0f58a39c265343d62ab31cd198f51a39bdf4663d628e6c45198f592504413e63d708e70a8f98f5c2acc733e63d468e6f7cf98f58a39b113e63d648e71054d0f48a39c265343d2292ef91198f34aadc735f0356192f0ed7c0cb46cdd2f5f03049ab71cd7c0c186adc735f02ee1b36edcf98a13297bb73e6284c628a2cf989a3297b14516218c8e71054d0751a39bb75341d467beedcf98756239bdf3e61d438e6a68f987519db9f32621d588827cc7a875629c3b73e6198c7d0edcf9866624bba83e61994a5ee58f986632062aa3e61998882aa8e086661f21f321219988767cc7a866624bb543e615d492f0a97c049464bb543e6125492ed50f98425297bb73e604cca5eedcf98113297c415f00389a5eedcf980e3297bb73e6030cab31cddb9f31239bdf76e7ce00011ce20c088c0047384d0223)) else (if page < 22 then 0x8e6c45289f39239b0e4a27ce48e6c31289f39239b0b4a27ce48e6c25289f39239b084a27ce49b0c1d289f3923a3074a27ce48e6c1d289f392373074a27ce492ec01289f35239ae34a27ce4a5f281281f31a97c9748c7cc6ab31cd231f31a39bdf48c7ce292ec51231f35239b1148c7ce4ab71cddb9e89239c415347a248e6edd4d1e89239bb73e67a24a5f25d459d51a97b14516754c8e6c51459d59239b0751675648e6e58f99d59239bb73cc7564ab71ce209c186684414a270708e7105289c1c239b074a27064882944e09afc2adc7388260e1a5ef918397125ec2ff5f05ae1ab71ce2096386adc735f058e1ab71ce209458639bd85fe5161ab31ce131310eacc7376e4c438e71054d1318a39c265344c628e6edd4d1318aacc734664c438e6c45199318639a9a4664c62ab2edcf993162acc733e64c438e6a68f99318a4baaa46647d2a5ea2d1991f2a97ca04664603ab31cd199180e97b1946646098e6c45199188697ab5466460a8e6a69199188a97aaa454460a8e6945151188a97ca046645c3ab31cd199110e39b114664461 else (if page < 23 then 0xab31ce20a9a1aacc7376ea6868e709988a9a9239bb7622a6a49b11cd83a5192adc7388283e4ab71cddba0f92cdd2f76e7d0cab71ce361f392adc7376e7ce4ab51cddb9f392acc7376e7ce4a491cddb9f3928947376e7ce49ed1cddb9f3926fc7376e7ce4ab31cddb9f332acbdf76e7cd88e6f7ddb9f3a239bdf76e7ce49a0f41db9f3c2adc737467ce4ab71cdcd9f39239bb77367ce4b374bdc11f332adc737047ce4aa31cdc11f392adc736e07ce4b374bdaa1f332adc736a87ce4aa91cdaa1f39297c736a87ce48e6f61aa1f39239b966a87ce4ab71cda49f392adc735a67ce4ab71ce061f386acc738827cc58e7105ef9f38639c397be7ce18e701de81f386acc7376e7cc58e6f7ddb9f386acc737be7cc38e71054d1f39239bb75347ce48e6e9d4d1f392acc735347cc68e6f7d4d1f38a39b115347ce48e7031289f3c239c374a27ce48e701d289f39239b964a27ce48e6e39289f39239b8d4a27ce48e6cad289f39297ca04a27cc6ab31cd289f31aa6c734a27cc6a5efa5289f32a39bdf4a27ce28e6f71289f38a97b194a27ccc else 0x156eacc7376e7cc4a5f25e39bb73e6255b8e6f7ddb9f38239bd87a0edcf9c14be4bb074a27cc4ab71cddb9f3263055b8e7104f98f58239bd85fe7cc7ac156e39bb73e61d44))))) else 0
  | 6 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x87f842fc20fe103f07ff83efc1efe0f3f077f83afc1cfe0e3f06ff836fc1afe0d3f067f832fc18fe0c3f05df82dfc167e0abf051f824fc11fe08bf043f820fc0ffe07bf03bf81cfc0cfe063f02ff816fc0afe053f025f811fc087e03ff01df80dfc067e02ff015f809fc047e01ff00df805fc027e00ff005f801fe486f20b754bf29af93e7c9b3e else 0xbbfeebfb8fedffb5fed3fb2fec7faffeb7fabfea7fa4fe8bf9dfe6ff98fe4ff92fe3ff8efe37f8cfe2bf89fe23f87fe1bf83fe0bf81fe03f7ffdfbf7dfdf3f7bfdebf79fddff76fd9bf65fd93f63fd8bf5cfd63f57fd5bf55fd53f53fd4bf51fd3ff4cfd2ff4afd27f48fd1ff46fd13f) else (if page < 3 then 0x9fff3dfe79fc97f8eff18fe2dfc57f87ff0efe19fc2bf847f07fe0dfc13f7ffefefdfbfbeff7cfef8fdeffbdbf7afef4fde7fbcbf787eeefddbfbb3f75feeafdd3fba3f73fee6fdcbfb93f71fee2fdc3fb83f6ffedefdb7fb67f6bfed5fda9fb43f67feccfd97fb2bf62fec4fd87fb07f607ebffd7dfaf3f else 0xeb7fd5ffa9ff4ffe97fd0ff9fff3bfe6ffccff97ff17fe1ffc2ff7ffef7fde7fbbff75fee7fdc7fb7ff6dfecffd8ffb0ff5ffebbfc4ff88ff0ffe13fc1ff82fefdfdf3fbd7f79fef1fddffbb7f75fee9fdcffb97f71fee1fdbffb77f6dfed9fdaffb57f4afe93fd23fa3ff46fe8bfd13fa1ff42fe83fd03f)) else (if page < 6 then (if page < 5 then 0xb03fafffafbfa97fa6bf9f3f9b3f9a3f98ff98bf973f96ff95ff95bf93ff93bf91bf913f903f8fff8fbf8f3f88bf887f87ff87bf877f873f82bf813f80ff80bf803f7fff7fbf7f7f7f3f7eff7ebf7e3f7dff7dbf7d3f7cff7cbf7aff7abf7a7f7a3f79ff793f78ff78bf787f783f77ff77bf777f773f76ff76bf767f763f75ff else 0xf07ff03fefffefbfef3feebfee7fee3fedffed7fe8ffe7ffe7bfe77fe73fe6ffe6bfe4bfe1bfdc3fd93fd87fd83fd7bfd77fd73fd6ffd6bfd67fd63fd57fd53fd4ffd3bfd33fd2ffd2bfd27fd1ffd17fd13fd0bfd07fd03fcfffcfbfcf7fcf3fceffcebfce7fce3fcdffcdbfbbffbb3fbabfba7fba3fb9ffb77fb63fb1bfb0ff) else (if page < 7 then 0x9cdfce5fe717f383f9bffcdefe6dff36bf9b3fcd8fe6bff35bf9a1fccefe66ff32ff98ffcc5fe61ff30bf983fcbffe5e7f2ebf971fcb7fe5b7f2d7f969fcb3fe597f2c3f95ffcacfe557f24bf921fc84fe417f1f3f8f7fc79fe3c7f1dbf8ebfc73fe397f1c7f8e1fc6ffe36ff19bf8c9fc63fe2dff163f8affc54fe27ff113f799fbcbfde47ef0bf else 0x7467cfc7367cfc70c7cfc6e07cfc6b47cfc6927cfc76e7a3c8e67a2788260f95f035795f031f95f02ef9a5e044fa5e030f001683f00167ff0015eff0015dff0015dbf0015d7f0015cff0015c3f0015bbf0015b7f0015b3f0015abf0015a3f001597f00158bf001587f001583f00157ff00157bf001577f001573f00156ff0014b7f0014aff00147bf001477f001473f00146ff00146bf001467f00144ff00144bf001447f00143bf001437f001433f00142ff00142bf001417f001413f00140bf0013f3f0013e3f0013dff0013c7f0013b3f0013abf0013a7f0013a3f00139ff))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x50610be3fe109f368109f354109f34a109f2b410bd2ac10bd26210bb14010af13c10af134109f0ea109f0e2109f0cc109f0c2109f0ea105f6460f3db200f1fa5e0f1f92e0f3755a0f3e5540f3e3560f1f2b60f3d14e0f370e40f1fb1e0e1f92e0e1f5540e3e3680e1f0cc0e1f0ea0d5f7e40cbb62a0cbd6280cbd6280c9f5ea0c9f2680cbb09c0c9f09a0c9f8480adf0ea07df876075f0b6075fa5e045f94004777d2047b56a047e2b8047d26a047b15004770e4045fa5e031f94003377d2033b56a033e2b8033d26a033b15003370e4031fa251ce79bf1ce78e6e6e777e7cfc else 0x2b415fd27615df26215fb23e15df14015ef13415df12a15df0ea15df0cc15df0c215df0ea159fa5e149f92e14b77c8149f14e14b70e4149f92e141f0cc141fb04125f9fe125f9c6125f98c125f92e125f9161277878125f852125f60a127d4cc127e3fe125f368125f336125f32e125f324127e138126f12e125f0da125f0cc125f0b4125f876119f4f011be0b6119f92e115f0cc115fb20109fb1e109fb0a109fb08109fb02109fab2109fa4a109f9c6109f994109f97c109f962109f94010b7930109f92e109f92a10b78dc109f7d010bb7be10bb56810be55810be53410be) else (if page < 11 then 0x4f019be482199f446199f41e19be412199f40a199f3fa199f3e2199f3e0199f3dc199f3d8199f3ca199f3b2199f380199f316199f302199f2c619bb29c19bd290199f25e19bb25c19bb25a19bb21a199f1f8199f1f4199f1d8199f1ba199f1a6199f16c199f14c19b714a19b7124199f10c199f0e8199f0e6199f0e0199f0d4199f750185f3d8185fb34181fab6181f92e181f8e6181f13e181f132181f0cc181fb0a15dfb0815dfab215dfa2e15df97c15df96215df94015f793415df93015df92e15df8dc15df7d015fb7ca15df7be15fb79e15df77e15df56815fe53415fe else 0x3001b1f2e21b1f8821adf5f01adfb361a9fb2e1a9faae1a9fa5e1a9f7c81a9f7b01a9f3e61a9f2681a9f2561a9f3e61a5f3cc1a5f8e61a1f3e619df38219df80019bbb2a199fb20199fb1c199fb1a199fb18199fb16199fb14199fb12199fb10199fb0e199fb0c199fb06199fb02199faaa199fa94199fa8a199fa7c199fa30199f9c8199f92019b790419b78d6199f8c419af89819b779a199f78e199f786199f778199f766199f75a199f758199f754199f750199f72a199f6b4199f686199f5e0199f5bc199f58e199f56619be56219be554199f53019be52c19be52819be)) else (if page < 14 then (if page < 13 then 0x5342cbe76e28fe76e285f3e6285f72c26af3cc26af8e624af7b024af86e232f8e621af52021be51621be51421be2b021bd2ae21bdab21ddfab21d9fb2c1d5fb221d5faee1d5fadc1d5fa381d5f9d01d5f8d81d5f7801d5f76e1d5f7521d5f7501d5f7361d5f6a81d5f6881d5f4841d5f4001d5f3e61d5f3da1d5f3d81d5f3d01d5f3aa1d5f3821d5f30a1d5f3061d5f2e21d5f28a1d5f2121d5f1ea1d5f1d21d5f1b01d5f1aa1d5f1821d5f1661d5fb361c1fa5e1c1f76e1c1f8e61b9fb281b1faa01b1f8821b1f76e1b1f5f01b1f5ea1b1f5e61b1f5e41b1f3e61b1f30a1b1f else 0x3e63cbe4663c3e3e63c3e92e3b1f7a03b3b5543b3e4723b3e2b63b3d2303b3b7d23abb7e43a7b9403a777be3a7b7a63a7b7a23a7b7a03a7b79c3a7b5343a7e3443a7b2b43a7d2623a7b23e3a7b2223a7b832393b7b0393b346393b256393bab2355f622357d5f0357b534357e3e6357d328357e262357b206357b1ea357ba5e32df92e32f785232f75f031fd46631fb3e631fda70306f9403077632307d622307d56a307e534307e32c307e328307e26a307b262307b94030378542ef75f02efb3e62efd2062efb1ea2efb92e2d9f9402cf76222cfd5342cfe3282cfe2622cfb) else (if page < 15 then 0x262427b23e427b222427b4663fbe4543fbe4523fbe3e63fbe4663f7e3e63f7e92e3f1f92e3e9f3d83ebe3803ebe3523ebe3403ebe31e3ebe4663e7e4603e7e3e63e7e4663e3e4623e3e3e63e3e84c3dfb7d23dfb8823dbb84c3dbb4663dbe4643dbe3e63dbe8863d7b8703d7b8563d7b8503d7b84e3d7b8463d7b83c3d7b8363d7b7e43d7b9403d777be3d7b7a23d7b79c3d7b6223d7d5343d7e45c3d7e3d03d7e3503d7e3443d7b3323d7e3283d7e2b43d7d2623d7b23e3d7b2223d7b8823d3b84c3d3b8463d3b5343d3e4663d3e3e63d3e4663cfe45e3cfe3e63cfe4663cbe else (if page < 16 then 0x38247fb30047fb28a47fb46647bb7c8473b5f0473b46646fb5f046bb466467b9dc463b832463b82c463b82a463b7e0463ba64462f90446377b6463b7b2463b52c463e46c463b46a463b466463b464463b45c463b45a463b458463b456463b454463b452463b3c0463b390463b388463b382463b37c463b364463b346463b30c463b306463b302463b2fe463b290463b25a463b46645fb466453b46644fb46644bb9dc447b83a4477666447b466447b45e447b382447b30a447b28a447b466443b92e435f7d242bb7e4427b94042777be427b7a2427b79c427b534427e2b4427d else 0xade4c7badc4c7bab64c7b8d84c7b84c4c7b8484c7b8464c7b83a4c7b8344c7b76e4c7b7504c7b7364c7b6a84c7b6884c7b6664c7b4844c7b4664c7b45e4c7b45c4c7b4504c7b3e64c7b3d84c7b3d04c7b3aa4c7b3824c7b3524c7b3504c7b34c4c7b3424c7b30a4c7b3064c7b2e24c7b28a4c7b84c4c3b76e4c3b4664c3b3e64c3bb364abba5e4abb8e64a7bb364a3baa04a3ba5e4a3b5e64a3b5e44a3b3004a3b2e24a3b88249fb5f049fb8e649bbb36493baae493ba5e493b7b0493b3e648fb3cc48fb8e648bb466487b466483b7ce47fb75047df66647fb46647fb45447fb))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0x53460fe60e5efda5e5e1f92e5e3760e5e3d5fe5e375e45e375e25e378445c7b7e65c7b7e45c7b7e25c7ba705c6fa685c6f9e65c6f9405c7790e5c776325c7d6225c7d61e5c7d6185c7d6145c7d6105c7d60c5c7d6065c7d56a5c7e5345c7e9405c376285afd5fe5af75e45af7ab658fb8e658fbab653bd8e653bd92e521f5fe523d554523e3e6523e3d8523e382523e380523e7e4517b9405177622517d600517d5fc517d534517e534513e844503b3e6503e382503e4664e3b84c4dbb76e4dbb4664dbb3e64dbb4664cfbb304c7bb2c4c7bb244c7bb224c7baf24c7baee4c7b else 0x9a0757795c757795a75779547577a70756fa6e756fa62756fa40756f940757792a757790475778fc75778f475778ee75778e875778e675778dc757782875777d2757b7be757b7b4757b56a757e534757e52e757e52a757e524757e51e757e51c757e518757e514757e506757e476757e410757740e75779407537a92732f92e7337554733e55470fe4a270fe7e4707b94070778fe7077534707e4cc707e4c6707e4ac707e48c707e5346ffe8446dfb8326dfb9a06df78e66df75166dfe5166bfe4a26bf73aa6bf736e6bf788260fb84c60fbab260df62860fd62260fd5fe60fd) else (if page < 20 then 0x5c47cfd5c27cfd5be7cfd56c7cfe54a7cfe5407cfe53e7cfe5387cfe5367cfe5347cfe5327cfe5047cfe4f87cfe4e27cfe4d87cfe4cc7cfe4c67cfe4c27cfe4be7cfe4bc7cfe4b87cfe4b47cfe4b27cfe4b07cfe4ac7cfe4aa7cfe4a87cfe4a67cfe4a47cfe4a27cfe4a07cfe49a7cfe4987cfe4947cfe4927cfe4907cfe48e7cfe48c7cfe48a7cfe4707cfe4147cfe8827a3d76e7a3dab27a1f8e67a2f7be7a3b5547a3e5347a3e4a27a3e8e678377a0783b516783e92e77378e6773792e765f8e67677554767e516767e862757d648757d646757d640757d9be75779b07577 else 0x5167ffe4a27ffe4a27e3e8867cfd8827cfd8747cfd8727cfd8707cfd86c7cfd8687cfd8647cfd85e7cfd8567cfd8507cfd8107cfd80c7cfd8067cfd77e7cfd74e7cfd7467cfd7367cfd7227cfd71e7cfd70c7cfd6e07cfd6b47cfd6927cfd6507cfd64e7cfd64c7cfd64a7cfd6467cfd6447cfd6427cfd63e7cfd63c7cfd63a7cfd6387cfd6367cfd7de7cfb7da7cfb7d87cfbb007cdfafc7cdfafa7cdf94c7cf79487cf79447cf79407cf792a7cf79287cf790e7cf79047cf79027cf78fe7cf77d47cfb7c67cfb7c47cfb7c07cfb7be7cfb7bc7cfb7aa7cfb7a87cfb5c87cfd)) else (if page < 23 then (if page < 22 then 0x750a6be736a6be6a8a6be68ca6be688a6be684a6be54aa6be882a67e76ea67eb36a23ea5ea23e8e6a17eb369e3eab69e3eaae9e3ea9c9e3ea989e3ea5e9e3e8e69e3e84c9c7e8e69b3eb3699bea9e99bea5e99be8e6993e9d095be85495b74f895be9b0947e676947e5dc947e5d6947e572947e9b094779569477a6a946f91694778f894778e6947785694778509477620947d528947e526947e4d8947e4cc947e9b091be85491b74f091be4d891be57890be94090b762290bd53490be4ac90be48c90be534903e8e68f778e687b77a087b77c884beab683fe8e683fe5547fdf else 0x92aedf7928edf7920edf790eedf7ab2e6df8e6e6ef8e6d8f78e6d7f792ed6f78e6d6f792ed69f8e6d6b7a18d5379e8d537976d53795cd53795ad537a70d52f940d537920d5378f4d5378eed5378e8d5378e6d5378dcd53778cd53778ad537940d4f792ed277940d1378e6cdf78e6ba778e6b6778e6b137750af1f882adbe76eadbeab6a97e882a7fe84ca7fe76ea7fe882a77e882a6fe76ea6feb32a6beb2ca6beb28a6beb22a6beaf4a6beaeea6beae4a6beadca6beab6a6bea54a6bea38a6bea00a6be9d0a6be8d8a6be8d4a6be882a6be876a6be870a6be854a6be76ea6be) else (if page < 24 then 0xedcf987573a83e6199c00290c26ec00883023b00213408ec00ab7003b00239c00ec0084cfbfb002cdbedec00882fb7b002133edec00b3b2837002ce4a0dc00aad2837002a5ca0dc00a3928370028d4a0dc009d12837002734a0dc00b352437002ca487dc00a0121f7002cd482dc00b2f20b700293482dc00aa91cef002a4c73bc00a8d1cef002a2473bc00a871cef002a1473bc00a831cef002a0473bc00a7f1cef0029ec73bc00a791cef0029dc73bc00a751cef00289473bc00a131cdf0026fc73bc009ab1cdf0024fc73dc0093d1cf70024dc73dc009331cf700248473dc009051cf70025046cdc00b371337002adc4cdc00a5f133700239c4cdc008e6f277001f7bb7ec007dcedfb001f6bb7ec00b00eddf002bfbb77c00afceddf002523b7dc00946edf7002513b7dc00940edf7 else (if page < 25 then 0xa5e2642b9f4bc480573e4b8660aebbb73e614bc92f0a824af25daa0495e4baf2092bc973aa1257a5e258249f4bc480493e20af808dcbb73e611bc7207cc237966a4b8425eadc730853c978e6109792ef40212f25d550427a4ba51084bc973aa1097a5e264211f4bc4a0423e9788b0847d2f108108f646198213b25c330425d56866084f2aa0cc109e76e7cc1e78aa83303c79db9f3071e4413820e39882be01972c517c032758a066064ec264660afa76e7cc15f91057c01de697bb70267bb73e604fca5e7cc099f66e978113e97bb70227bb73e6047ca5f104071f4bddb80e3e20af801dcd2f5f0038f76e7cc07794bcf980e3ecdd2f0187bb73e6033ca5e7cc061f56639bb71e39c41535347376ea6a6940edcf9e8f7ddb9f3e239b543e7a5598e67cc78e6f7cf9c71cd4d1f39a39a8b3ab33b73e64c78 else 0x7627cc3378ebcf9866f1d59f30cde3a83e619bc7307cc3378e58f9866f1c11f30cde3543e619bc5a67cc3379030f9866e61d9f30ccec093e6199d7507cc333acb4f986675949f30cceb213e6199da707cc331efa0f98666d729f30cceab43e6199e55e7cc333cab8f986679561f30ccf2aa3e6199e5147cc333c958f98667a4b9ec0ccba8b3d8199e4a27b0333d4bcf30663d551e60ccf2aa3aa199e8827043372aa8e0866798a1800cceb142e2199d88258c3372be0b1866e6209450cdcb1428a199d4664e833368cc960666d1792b0ccda2f230199b7c842433367cc84866f1198fa0ccf22f1f4199e3e63e8333d0ec7a8666e120f50ccdbe41ea199b7c83a43336be06c066e57c0d20cdcaf818219b976e7cc30f8aa8f98617acd4970aebd5b8e615e792f1cc2baf25de80575e4bb540aebc974a215d7)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0xab71cc6acf56d7c0d5e620af81abcc9787632d7628be063f2be0aa8c7e6cdd2f1827d5b8e63067b36be060f356d7c0c1e697af8183cc735f03079ab71cc5dcf1cd7c0bbe620af8177cd5b8e62ce7b36edc509f4bddb8a13ecd9f31427d2f3e6284f76e7cc4d78a2cf989abacdd2f1247bb73e624bc882be04672edcf988cf2cdd2f10c7d2f51621ae76e7cc43791054d07579dba9a0eaf3b73e61d7c8827cc3abaedcf987575929f30eaebdf3e61d5b5567cc3abcaa8f9875794d1f30eaf2513e61d5e4664d03ab7098988756ddb9310eada332621d5b3e64c43ab68cc8c0756e208f50eadc261ea1d5b4663d43abc7cc7a87579459f30d6f53876e198f92eea0332f4bdcb0663e20ab40ccf3b7568199eb22aa8333cac55506679552420ccf44141e19bc76e83c33791b0f9866f1df9f30cde3b73e619bc else 0x5f055088f2be0a9911e6adc732133c737a04273ab67cc84f91ccf9909f1ec2331fdd3d74663fba92e8cc7d3cf3d198faea4ba2f1f4f4973e63e9e46647c7d74f99198f9e9f4a331edd3e93e63dba9411047ae71ce150f5ce504261eb9c7383a3d73ab71cc7acf1cde80f5ce20b111ebcc266223d79882a687af50994d0f5e9f92331ebd4a04663d767be8cc7af4f45198f5e9e72331ebd3114663d7c6467cc7af8fc8f98f5ea501f31ebb3df3e63d7a7a67cc7af4f44f98f5e9e71f31ebd3113e63d7c6007cc7af8bf8f98f5f0f99a21ebd4413283d7a84c6507af5104ad0f5e61315a1ebca332b43d7c3e65687af87ccaa8f5f0f99531ebe2332623d7a3e64c47af48cc8f8f5e8f991f1ebd2332223d7a3e64447af51054d0f4ea1329a1e9d3e44663cfa46647c79f4edcf98ecf2adc731d33c737a03a73) else (if page < 29 then 0x84ca6898f4edd4d131ea13233263d3b74664c7aab28cc98b6c4519931e555233263d29a4664c7a4a28cc98f4edcf9931f2209f3263cbb73e64c79ab27cc98b6aa8f9931e94d1f3263d2513e64c7a88256898f2edcad131e57c15a263c9f32b44c795168cc93f4a2cf9927ea12a3323fd3b746647faa5e8cc8fb725d1991fcde823323f9bcf46647f35548cc8ff4a2d1991fe928a3323fd3b73e647fc5848cc8c74af519918e95e233231d538466462b9408cc8c66c6519918e588a33231cab5466463a5348cc8c74a3919918e946233231d28a466463a4ac8cc8c7491919918ea97a2a2315c73454462b5f05748c72be0ae118e51995c231caf82b446394665688c72be0ac918e57c155231cca046645f384c8cc88f4edd19911e9e82332239aaa466447a4a28cc88f491919911e9db9f3223e2f82b64479 else 0x5fc918f9f8edcff9f3f1551ff3e6f55b76e7a3cab71ccf44f1054d1e8f1dba9a3d1e3b73e67a3c8e67ccf44eedcf99e0f1db9f33b3e59ba5e754fab71cceacf526399d59e97c733ab3c737b07567a92a2ceadd4bd459d5ba4ba8b3abb47351675768e6a2ceadd1cd459d59e399e63ab3d5b8e6732776e7cce67956e209c1e668441383cc738827079ab71cce0cf341289c1da39a51383b3b73e66dfc882704dbf2edcf99aff1289f335fb4413826bf94a2704d7ed56e20983e6adc733073c415f060f9882be0bc72bfd7c178d64baf52f0baff5ea5e35b374bcb89f56e399719e97b072e36c7360e5c6d9ee944b8ed56e3996b9e20af82d7caff5f05af5ab7104b1f31ce20963e6adaf82c7cc735f058f9882be0a47356e20945e639c4128bcd5b8e651678e6bfca2eb566131316eacbb7262dc415344c7a)) else (if page < 32 then (if page < 31 then 0x8e6f7cf9cf341e81f3ce39ae03e7ac415347cfc76ea68f9f8e9d4d1f3f2aca9a3e6f4735347cee7bea68f9f4c454d1f3f239a9a3e73c734c07cf68e6974f9ed25d2c1f3da39a583e7b4414ac7cfc76e958f9f8e452b1f3f1972563e7e4974ac7cde8e6958f9ecc012b1f3f1c7a513e7e32c4a27cfc648944f9f8c8d289f3f18f2513e7e4df4a27cf69b0944f9ed341289f3da572513e7b4ad4a27cf6954944f9ed4e1289f3ba99a513e774a04a27cf690e944f9ed1f9289f3da3ea513e7b47a4a27cf68ee944f9ed1d1289f3da39a513e7b46e4a27cf67d2944f9f4f7d289f3e9ee2513e7d3194a27cfc622944f9f8c39289f3f186a513e7e30a4a27cfc610944f9f8c01289f3f1612513e7b2c14a27cf6940940f9ed105231f3f1dba463e7e39048c7cfc71e918f9f925d231f3d98a2463e7e2ff48c7cfc else 0xab6edcf9f9569db9f3f2923b73e7e52276e7cfca18edcf9f93d1db9f3f26fbb73e7e4d876e7cfc9a0edcf9f92b9db9f3f256bb73e7e4aa76e7cfc940edcf9f91f9db9f3f23d3b73e7e47476e7cfc8e6edcf9f91b9db9f3f1f93b73e7e3df76e7cfc7a6edcf9f8f45db9f3f1e73b73e7e3bf76e7cfcab6e8cf9f956dcd9f3f1dbb9b3e7e59b7047cfcab6e08f9f9545c11f3f297b823e7e4737047cfc8e6dc0f9f8eddad1f3f2cdb543e7e55b6a87cfca5ed50f9f91cdaa1f3f239b493e7e3b76927cfcab6b4cf9f91cd699f3f220abc3e7e3b75787cfc646af0f9f956e061f3e639c0c3e7cca08827cf58e70a8f9eb1ce021f3d620bdf3e7cc397be7cf9940edcf9eaf7ddb9f3e639b543e7ad5b8e67ce7ab51ccf9cf566399f39e924733e73cf68e67ce79bf1ccf9cf566399f33eacbdf3e6dc737be7ceb) else (if page < 33 then 0x92f1057c049664baff5f0125592eedcf9849724baff3e6125592e944f98495a20af80cc125976e7cc33049724bbb73e6109c92e944f984259db9f30cc109cab71cddb9f39239b074a27ce400165aadc739c00591ab71ce70015deadc739c0056eab71ce700156e8e4739c0055ba191ce700156e744739c0055b9b11ce700156e39c6c9c0055b8e6ede700156a39bb79c005598e6ede700149239bb79c005128e6ede70013da39bb79c005598e6edcf00156e39b9b9c0047376ee6e700166e97b543c0055b8e6d52700155239b549c0052f8e6d5270011cdcb3549c0055b8e6d26700156e39b449c00559882a69e0011ce20a9ab80055976ea69e0011cddba9ab800426622a6bc000edd88a9af000473882a6a70011cddba9a9c004e88e6947600136239a51d80047386e94670011cdcb2519c004734f0947600156e39a429c004734a290b600156e20a0ff00047388283fc00156ddba0ff00047376e83fc00166ddb9f4f00055b8d87cfc0011ce361f3f00059e76e7cfc0015e1db9f3f00057776e7cfc0015c5db9f3f00056e76e7cfc else (if page < 34 then 0x8e6f61289f39a4bb074a27cf48e6c1d289f3b239aff4a27cf48e6c1d289f39639a8b4a27ce6ab71cd231f39a39aff48c7cf48e6edcf99d5d239a8b3e67566ab71ce131318eadc7376e4c63ab71cd199318eadbb73e64c78ab71ccf99318e4bbe446647d3b374bd199182eadc734664623a5ea2d19918aa39a8b466462a8e694519918caadc7346644638e694519911ca4bbe44663e9aab71ce208f58eadc7384c3d63ab71cd198f59a39bd04663d72ab7104f98f5e239c413e63d78ab71ccf98f59a39bd03e63d728e6bfcf98f5d2adc7376e1d47ab6edcf987572adc733e61d47b34edcf98667297bb73e6199c92eedcf9866d1f23b73e6199c76eea0f98667220aaa3e6199c76eaa8f986671d92aa3e6199c646aa8f9866724baaa3e6199662aaa8f9866718a2aa3e6199ca5ea2cf9866398a28b3e6199c628944f986671db9f33d8199c5548cc9a0666955233256199a5548cc8c06669f22331f4199a7c88cc7a8666a209f31ea19b87c87cc7a866698a1f31ea199c76e7cc5386671db9f30e4199c92eedcf985771db9f30cc15dc else 0xab756639bb71e97c978e6edc7ab71ce20a9a9aadc7376ea6a68e710545a519a39bb75169466b37281db9f3d2adc7376e7cec92f1cddb9f3d2adbdf76e7cf88e6f41db9f3d239bb76a87cf4ab71ce209f396adc7376e7ce5ab7566399f31e97c978e67cc7ab71cdef9f38e39bd87a07ce3ab71cd4d1f39a39c414a27cf48e6edd289f3d239b904a27cf4b374bd289f33aadc734a27ce6a9d1cd289f39a97c734a27ce6)))))) else 0
  | 7 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0xd13fcfbfceffbaff90ff8f7f883f87bf83ff7fff7f3f7e7f7a3f78ff783f773f767f757f733f70ff70bf707f6dff6bff60ff5f7f5e3f5c7f5aff523f517f503f463f437f417f3ebf3d7f3c7f3b3f3a7f393f37ff357f347f2eff2c3f2abf24bf21bf14bf117f10bf0f3f0e3f0cbf0bff0a7f08bf077f06bf047f033f9e3e83fe else 0x7a0427b230427b4663ebe45e3ebe3e63ebe7a03d7b41e3d7e3823d7e3423d7e3423d7b31c3d7e2a43d7b4663c7e3e63c7e8343a7b7a03a7b3423a7b2303a7b3e6307d3e62cfe76e1d5f3e61d5f8821b1f5f01b1f3e61a9f750199f3d8199f92e15df7c815df0cc15df876125f334125f0b6125fb22109f92e109f55410be352109f0cc109f7047cfc5a67cfc882707988251790015dff0015bbf0014bbf001433f00141bf0013dff0013a3f00137ff001363f001343f001313f001303f00116bf000f2bf000efff000eeff000edff000e6ff000e4ff000d7ff000d6bf000d27f) else (if page < 3 then 0x84d017b940edf792aedf78e6d537882a6be76ea6be84c9e3e9d0947e85494774f0947e4a290be84c7e7e8827cfd86a7cfd8627cfd8087cfd7047cfd6467cfd6407cfd9407cf792a7cf79047cf77be7cfb7aa7cfb5a67cfd5347cfe5067cfe4f07cfe4c07cfe4ba7cfe4ac7cfe48c7cfe4747cfe41e7cfe9d075778e67577516757e84c707b834707b4a2707e60e5c7d5fe5c775e45c77882517b84c517b5fe517d5fa517d3e6517e382517e84c4c7b76e4c7b4664c7b3e64c7b8824a3b5f04a3b3e6493b46647fb666463b466463b454463b382463b300463b28a463b466447b else 0x9d010bf92e10bf8e610bf84c10bf83410bf7c810bf7a010bf46610bf3e610bf3d810bf3aa10bf38210bf35210bf34c10bf34210bf27c10bf26810bf23010bf1d210bf13e10bf13210bf12810bf10810bf0cc10bf0b210bf3e60f3f3aa0f3f0cc0f3f3e60e3f3820e3f0920e3f5f00cbf2e20cbf0cc0cbf5f00bff28a0bff0920bff84c0aff76e0aff4660aff3e60affb2e0a7f76e0a7f882097f76e097f5f0097f466097f3e6097fb2e08bf3e608bf882077f0cc077f88206bf09206bf76e04ff3e604ffb36047f76e047f88203bf76e03bf5f003bf3e603bfb36033f3e6033f)) else (if page < 6 then (if page < 5 then 0x16619bf76e187f3e6187fb3415ffb2e15ffab615ffa4c15ff92e15ff8e615ff7c815ff7a015ff26815ff23015ff13e15ff13215ff0cc15ff76e14bf0cc14bf5f0143fb32127fb28127fa54127fa00127f8d8127f884127f882127f87a127f876127f854127f688127f5f2127f5f0127f5ec127f5ea127f5e4127f484127f3d8127f3aa127f382127f334127f330127f320127f31c127f318127f30a127f2e2127f28a127f206127f1b0127f182127f166127f12c127f0b6127f88211bf76e11bf5f011bf3e611bf882117f092117fb3410bfb2e10bfb2210bfab610bfa4c10bf else 0x516307f4a2307f3e6307f326307f322307f8e62eff8822effab62cff9ee2cff8e62cff4a22cff3e62cff3222cff8822c3f4a22c3f76e2abf2302abf76e26bf3e626bfa5e24bf76e24bf882233f76e233f5f0233f3e6233fa5e21bf3e621bf76e1d7f3e61d7f8821b3f5f01b3f3e61abfb2c19bfb2219bfaac19bfa9619bfa3819bf9d019bf8d819bf77e19bf76e19bf75619bf75019bf72c19bf6a819bf68819bf48419bf3fe19bf3e619bf3de19bf3d819bf3cc19bf3aa19bf38219bf30a19bf30019bf2e219bf28a19bf21219bf1ea19bf1d219bf1b019bf1a419bf18219bf) else (if page < 7 then 0x76e417f230417f76e3ebf4663ebf45e3ebf3e63ebfab63d7fa023d7f9e03d7f8e63d7f68c3d7f5fe3d7f5f03d7f5e43d7f4503d7f3aa3d7f3823d7f34c3d7f3423d7f3303d7f31c3d7f2e23d7f2a83d7f28a3d7f8823c7f76e3c7f5f03c7f4663c7f3e63c7f3303c7f7c83b3f3e63b3fab63a7fa4c3a7f9d03a7f8e63a7f8343a7f7a03a7f4663a7f3e63a7f3aa3a7f3823a7f34c3a7f3423a7f28a3a7f27c3a7f2303a7f3e6393f3aa393f230393f3e637ff34c37ff23037ffab6357f882357f9ee347f882347fb36307fab6307fa9e307fa5e307f9ee307f8e6307f76e307f else (if page < 8 then 0x8e6517f882517f76e517f688517f662517f5fe517f5fa517f5f0517f5e4517f4a2517f3e6517f382517f2e2517f5f0503f4a2503f2e2503f28a503f84c4c7f76e4c7f4664c7f3e64c7f8824a3f5f04a3f3e6493f76e47ff3e647ffaac463fa96463fa38463f9d0463f8d8463f834463f794463f76e463f72c463f6a8463f668463f666463f466463f454463f450463f440463f3e6463f3cc463f3aa463f38c463f382463f34e463f34c463f342463f300463f2e2463f28a463f84c447f76e447f466447f3e6447f7c8437f76e437fab6427fa4c427f8e6427f7a0427f230427f else 0x3e6733f3aa733f5f070ff3e670bfab6707f9ee707f9d0707f9a0707f8e6707f76e707f688707f4a2707f3e6707f3aa707f4a26dff3e66dff3aa6dff3826dff3e66bff3826bffab660ff5f060ff9ee5f7f5f05f7f5f05e3f5ea5e3fb365c7fab65c7faa45c7faa05c7fa9e5c7fa885c7fa5e5c7fa025c7fa005c7f9ee5c7f8e65c7f8825c7f76e5c7f6885c7f60e5c7f5fe5c7f5f85c7f5f65c7f5f05c7f5e65c7f5e45c7f5d65c7f5165c7f4a25c7f3e65c7f38e5c7f3825c7f3005c7f8e65aff5f05aff2e25aff5f0523f5ea523fab6517fa02517fa00517f9ee517f980517f)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x8347cff8327cff8307cff82e7cff82a7cff8287cff7e47cff7e07cff7be7cff7aa7cff7a67cff7a47cff7a27cff7a07cff79c7cff5b67cff5787cff5767cff5347cff5067cff4f07cff4c07cff4ba7cff4ac7cff48c7cff4847cff4747cff4687cff4407cff43c7cff41e7cff3fe7cff3f87cff3f27cffab67a3f3e67a3fa4c78ff3e678ff3e6783f3e6773f3e6767fb36757fab6757faae757fa9e757fa96757fa92757fa5e757fa4c757f9ee757f9d0757f8e6757f84c757f834757f832757f7b0757f7a0757f76e757f516757f4a2757f466757f3e6757f3cc757f8e6733f else 0x76eaf3f84caebf882a6bf76ea6bf84c9e3f76e977f882963f88295bf76e95bfab0947faa0947fa54947fa00947f8d8947f8c2947f882947f86e947f854947f688947f67c947f88291bf76e91bf88290ffab690bf9ee90bf8e690bf4a290bf8828f7f4a28f7f84c7e7fb3c7cffaf07cffae27cffadc7cffab67cffab47cffa507cffa4e7cffa4c7cffa487cffa447cff9ee7cff9e87cff9d07cff9be7cff9b07cff9a07cff9927cff9907cff97a7cff96c7cff95c7cff95a7cff9547cff9407cff92a7cff9047cff8fc7cff8f47cff8e87cff8e67cff8dc7cff84c7cff8407cff) else (if page < 12 then 0xa5d3dffa553dffa0d3dffb373a3fab73a3faaf3a3fa973a3fa4d3a3fb2d1cffb231cffa391cffa191cff9d11cff9b11cffab71b3f9ef1b3f8e71b3fb3cedffaf0edffaeeedffae2edffab6edffab4edffa5cedffa50edffa4cedffa48edffa44edffa18edff9e8edff97aedff95cedff95aedff940edff92aedff8f4edff8e8edff8e6edff8dcedff8b4edff794edff77eedff776edffab6e6ff76ee6ffa4ce4ff76ee4ff84ce0bf76ed7ff76ed6bfb36d53fab6d53faaed53fa5ed53fa4cd53f8e6d53f8e6d27f76ed27fab6d13fa00d13f9eed13f8e6d13f76eb6ff882af3f else 0x92e7cc213eabcf9842f9551f3085f2513e610be3e66a4213e7ccad842f4f9954085e9f327c10be3e63d4217c7cc330427cf98f504bf55b8e6ede7ab6edcf9f9499db9f3f2743b73e7e47376e7cfc834edcf9f8f41db9f3f2adc733e73c414a27cfc720944f9f93a1289f3da39a513e7b3074a27cfc5fe944f9f8edcf99d5f1db9f3383e4413e67079882be0b8f2bfd7c171d620af828bcbb7466463a7a08cc8c66a2d19918e928a33231d3b73e6463c7c88cc7d74f41198f5ea209f31ebe32f3e63d7c8827cc7af5098f98f5ea0d1f31ebd3d03e63d7a5fe7cc7af8bf4f98f5f0f99a11ebd1f32a83d7c4665487af47cca90f5e8f99181ebd1f32063d7c76e7cc74f9104f98e9e5db9f30cde2aa3e6199e882be024f2edcf9842f2209f31ebc000aef56ff0015baadfe002cdd1cfc0055ba39f800ab13dff)) else (if page < 15 then (if page < 14 then 0xb347cc333f4bcf98667e4b9f30cdbbe43e6199f55a7cc337caa8f9866f9551f30ccfa8b3e619be4a27cc337c7ccf60667d199340cdda3325619bb46646033771047a866ee130f50cdda331ea19be3e63d4337cedc538667cf98a70ccfbb70e4199f3e61c8333f25ddb8577df23b70aefbb70cc15dfb2710424bf25e208497e20c3b092fc9776e125f882be024f70997c049edf8af8093dd935f0125f92ebe024bec597c049f58a2f8093eaff5f0127d882aa824fcbe155049fa209f3093ed913e6125f92e7cc24bec50f9849f57f9f3093ea33334125f88265424fcbe0ca849fa20995092faf832a125f5f063424fabe09a049ed7c118093dc41206127b5f040c24fa7cc81849f6208f5093dc410cc125f76e19824bebe0330497cf9866092fc410b6125f4a27cc237d104f9842f5db9f3085ed913e6109f else 0x8227cc7afcf40f98f5f9979f31ebf2ff3e63d7e5fa7cc7afcbe0f98f5fa0d1f31ebdbd03e63d7b5fe7cc7afa83cf98f5f8f99d51ebf2f83823d7e4667047afc7cce08f5f8f99a61ebf1f33423d7e3e66847af68cccc0f5fa209911ebda3331c3d7e84c5507af68ccaa0f5f8f99541ebf2332a43d7b3e65487afcedc8c0f5ecf99181ebf1f32303d7b3e640c7afa945198f1f9289f31e3f2333303c7e3e646078fc7cc7a8f1fa209f31d3ebb73e63a7d84c7cc74f7068f98e9ede81f31d3da513e63a7e4747cc74fc7ccd08e9ecf99541d3e9f32a43a7b3e64f874fc7cc8c0e9ecf98f51d3f1f3230307d8347cc59fc7cc7a8b3faadbb70eafd5b3e61d5f9ef104363f3dd7c06c7e741f30d4fd9a76e199fa5eedc333f25ddb866dddbba80ccfc41554199f76eaa8333f104f9866f5db9f30cdeb233e619bd) else (if page < 16 then 0xa5e8cc8c7740519918ee78233231dc73466463b7a08cc8c76edd19918eda3233231db07466463b5fe8cc8c76a2d19918f928a33231f233454463b4668a08c77104f9918f5db9f3231ed263e6463b7b07cc8c76f40f9918dd459f3231f2513e6463e4667cc8c768cce0918ecf99c1231daf8300463b5f05c48c767ccac118f4f9954231eaf828a463b76e4ac8c767cc95918ee39a33223dbd076e427b76e46084f6f917c0faedf22331f5da3345e3ebe7c87cc7d7d56e208f5ee7bc411ebdc738823d7bab70987af7406130f5ee39c261ebdbd076e3d7b84cbfc7af6bfd7c0f5f620a511ebdd5b4663d7ea028cc7afd3c1198f5fa39a331ebf3464663d7e5fe8cc7afcf41198f5ed19a281ebf55b3e63d7ea4c7cc7afd404f98f5fa741f31ebf4b93e63d7e8e67cc7afd104f98f5fa131f31ebf41a3e63d7e else (if page < 17 then 0xa02944f9fd3a1289f3fa39a513e7f4414a27cfe844944f9fd069289f3f9ec2513e7f3d04a27cfe720944f9fd105289f3f6742513e7bc734a27cf760e944f9fabfd289f3f53c2513e7f47348c7cfe4a2918f9fd069199f3ed7fa333e7ea51466757e8827cceafaedcf99d5f6741f33abbc733e675775167cceafc944f99d5fa209f3383ebb73e6707d84c7cce0f7068f99c1ede81f3383da513e6707e882be0b8f70997c171ed83af82e3eaff5f05c7d5febe0b8eebe179171de20af828bdc265f0517b5febe0a2fabf57c145f57c1f328bf2f8382517e3e6704a2fd56e13131eeadbb7263dd5b4664c7bab67cc98f73de20928ee7baf8251dce83e6493b7c88cc8ff6edd98118f6933b7231dbd876e463b7a0edc8c6eedd99918eddba37231f3b7466463eb368cc8c7756d19918eea9233231dd4c466463b else 0x166e503b7deabc9576fbd5b8e6edef92f1cddbef1cddbb54deadc41535f55b76ea6bea030993c7d3de20a51fa7bc414a3bc7388294778830a928ef1cddba51de20a8b4a3f4414a290beab7104f9fb49a209f3f67bc413e7ece88827cfd8e7104f9fb1060d1f3f620bd03e7ec317a07cfdab6edcf9fb499db9f3f6743b73e7ec7376e7cfd834edcf9faf41db9f3f6cdca03e7bd5792a7cf7a97208f9ef56e399f3be4bc733e7bd5b7be7cfb9d0f54f9f7499e81f3ee933d03e7bc737a07cf77b0f40f9f756d4d1f3fa932833e7f4e84f07cfeb36944f9fd56d289f3faaba513e7f5524a27cfea9c944f9fd52d289f3fa97a513e7f5264a27cfe))))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x88290bfab67cffa4c7cff9ee7cff9d07cff8e67cff84c7cff8347cff7a07cff76e7cff4a27cff4667cff3e6757f3e6707f5f05c7f5f0517f84c463f76e463f466463f3e6463f76e427f8823d7f84c3d7f76e3d7f5f03d7f4663d7f3e63d7f3e63a7f882307f8822cff76e19bf3e619bf76e15ff882127f76e127f5f0127f3e6127f3e610bf8827cfd76e7cfd4a27cfe466463b8823d7b84c3d7b4663d7e3e63d7e76e7cfc001473f0013a3f0011b3f000d53f000d13f00090bf000757f000707f0005c7f000517f000427f0003d7f0003a7f000307f0002cff00015ff00010bf else 0xab6edffa4cedffa38edff9eeedff8e6edff8d8edff84cedff76ed53f882947f76e947f) else 0
  | 9 => if page < 1 then 0x2adff3dff8e7fbb7fd28fe7cff231f8f5fc337e127f else 0
  | 10 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x42 else 0
  | 3 => if page < 1 then 0x58 else 0
  | 4 => if page < 1 then 0x6e13c39 else 0
  | 5 => if page < 1 then 0x1ec651946513c4f13c4f13c4f13c4f13c4f0e4390e4390e4390e4390e421 else 0
  | 6 => if page < 1 then 0x651946513c4f13c4f13c4f13c4f134390e4390e4390e4390e4390e4390e4390e4390e4230842107c1f07423 else 0
  | 7 => if page < 1 then 0x13c4f13c4f13c4f0e4390e4390e4390e4390e4390e421 else 0
  | 8 => if page < 1 then 0xe439 else 0
  | 9 => if page < 1 then 0x23 else 0
  | 10 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 8
  | 3 => 43
  | 4 => 175
  | 5 => 1481
  | 6 => 2202
  | 7 => 1139
  | 8 => 74
  | 9 => 10
  | 10 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 2048
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 11)

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
  | 2 => 5
  | 3 => 25
  | 4 => 81
  | 5 => 896
  | 6 => 1265
  | 7 => 771
  | 8 => 70
  | 9 => 20
  | 10 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 19
  | 3 => 89
  | 4 => 298
  | 5 => 3227
  | 6 => 4555
  | 7 => 2776
  | 8 => 254
  | 9 => 73
  | 10 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | 7 => 8
  | 8 => 7
  | 9 => 4
  | 10 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 9
  | 3 => 12
  | 4 => 14
  | 5 => 17
  | 6 => 18
  | 7 => 17
  | 8 => 13
  | 9 => 10
  | 10 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xd3605 else 0
  | 3 => if page < 1 then 0xc0b11f020a040001a00680281c0800e001001a00381 else 0
  | 4 => if page < 2 then (if page < 1 then 0x290b0000120c0a310302002f0571280a000d061e0a000014000504131b4003030011210000020e170002091700070208003c000303000e010e0b01001c330101 else 0x151a01030909800c0c01117b1a08750101) else 0
  | 5 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0xb13010109110700010a030703030406040b00030004000001000b03010006030304000201010a0204000d00070502000a0100070500080004000b07002101 else (if page < 2 then 0x401020102000808221e030503000107000001001600000b030102220d0504000302000e0d231416020a02030000000000060301030a04000100000000010102 else 0x605040c0408060005080200050000190208030a070e0504030003030f0417000e0003030b060a000e04010300051102000a0005010310051f04010003000000)) else (if page < 5 then (if page < 4 then 0x1e02020704050000010000061000001602070009000901010206000b0d050602000511190810001a09080305001403080206000000080d08090901030a061006 else 0x100010600003e080510040104000718000104120000000003113a030a04040008030c0001001809000703030b000500050000000702000005040100040b0000) else (if page < 6 then 0x1e0a00070008315e150000040819000509010100080119090a0401000811010d1e2201060101080f1805000200090005000809120200041a0808050e02000c04 else 0x10008160001000411000803010101000612151701092b060c000b0e0e00070606020f0b410405010018090a01000200030414040e0402050203030a0b0b0013))) else (if page < 10 then (if page < 8 then 0xa1f1e05010b0302050000120001000000050200000501003c0100000004000a0000020001020605050e0c082405060216000000181201063103020a101f080f else (if page < 9 then 0x50b0a00000018020002020f010c000103101b0008191810052633012400010204071900002403142209000101000c0210000000000001000900031501021d00 else 0x2031f00020c040002040509070102170b00050101040204020d0a2003010f00021d02000007010a93000f31060227000100040d010a280300002b07081a0900)) else (if page < 12 then (if page < 11 then 0xa1e0005060401030f00000b010102010d190106231813270711200700190b04550000000607000200140f06111428000306010100030e010001000813360105 else 0x16011b0a0b030302030100010d0f0500011207110f0200061e0007750209060c6b01102a032509060f2f012b152201141600110753092c000e1c03051e000500) else (if page < 13 then 0x20e02015b072500092e140100691f4308a41e030001000817003a0d1c1a1713040303020a5f160f0403000307031401011d0004010000000058065f01001600 else 0x711001f00030612002f0806320d0a00051e0d060011036006143a2007000f3c05012937250a1d0c0000050f03050003060000330703051e010d0a26)))) else 0
  | 6 => if page < 20 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x10b0000040d00140a0300000b060b02000002141608071803030403180d110b0e000902010804050c0006180300001e0d000307000000010102180502030200 else 0x2100801000100010201010101000000040805080c0d0004090a00020e080500000701020c00040206030a0001000200060104010001000a0103000200000604) else (if page < 3 then 0x4000005030900190c0a040106000005280005000601000a00000702021002150502050001050000000011000802000502040000020000010d0c0703000501 else (if page < 4 then 0xd06010703000206020d14010400070400000000020b1f0208070001000000010106070103051c08000004010c0a020106000a0e0400000a000a0216181f else 0xa000600000a060208000810002d021302000000020408003b090000051900120f00001500001503010a0a01040101000104020705150100060500260301021a))) else (if page < 7 then (if page < 6 then 0x91e031201020202220201160102010001010105000d020906100609000003000d061000200006090c000427200000050007270501030000000009020d000000 else 0x1d06000003000719042001073904010804071806030109010008070b21060a05040106000001021900010702010d000205000001060a00020004000003020a1b) else (if page < 8 then 0x30d0a010100000000042100000000010404020611280a03000709130700030c010100000509261503080920080000010004001c030104130800190b000106 else (if page < 9 then 0xb00040102010c1702050703031821040002050b0e06180e00010015200d00220309080600030100010500001d031f0b10010004070b080f03050400030105 else 0x40e2b030c000a1a0000180b0c040201091d0100080c020521061c080302030c1806002803000016020501071c000a0a0e000a040000000a030b0010382a00)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0x2503001400020d030c1c0324000005245303002f00041711010d0108040000000e041a040e02041e010e190302170d07060b0000022122011b03090504000000 else 0xb010c2211031300000c00001006050400070505000002070000003d00140701010e0e0c0b010003000001210a0019030000011418002700021a100003030008) else (if page < 13 then 0x33061b00030100050011000a190e09030202080204100004000043031511000e05052701060011020104112f00040602431c0a1806000306000209040e030000 else (if page < 14 then 0x4070300071310001400001d0005133805030b24110503022100010507000a130f1d0012140913020b050000190d0c040d040002000102152221460c06030008 else 0x7097f02044003030c0d33030302081f040a00101404084d0a01061d0f0311000c04020a0528031c000005001f0115004400040022120e090204070602052f3f))) else (if page < 17 then (if page < 16 then 0x23020109030500180c06020c120c012f00011300310002010b01090318080000090302080100020101050b180211340711071d100f00010e021107040f231701 else 0x5012900130d03010001020300172502060f0804050d03020e0d0308030008040501102b002e0f0005000523040907250603080500041202010e380305080802) else (if page < 18 then 0x1204000229060f042804350a1c11051414001f110d03170e001200030435070b020e05070f1e0212080427040900281a28405302000305000600041300000e else (if page < 19 then 0x11b150f021e1f02170d101f07050405061201000a0b1b1100040108000d01070021795b088700000005170300021b1100081a16030104000201000000001f else 0x31f3904010d00002f06040466010407000003030219000c082c140509300103091f020600041f420a1a2f0f53140f050c))))) else 0
  | 7 => if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x4060000020701020135040408040019010c1d01020301020d000006280003170e0000020004000200050f140e06000b0501010109030000030300000e0503 else (if page < 2 then 0x8091c030a0c0100070b01000308010202000b010e040c000002030c000607010a10030301231b0102000500220f060000000310000d0d07010102030d010900 else 0x1000716020c02030603000e0f030500000600021a1a000e0907010b00010c010c0207010200070402000006000c0a00030a0003000210060001000602000f00)) else (if page < 4 then 0x70a1200000001030501000202020d0705000513090602010a00040500000001000004050f0b000b171c1b00000a0101100003061d0133260d050e00060400 else (if page < 5 then 0x3e0004150000070022000220100d070209083d08000d240107003a000c020601010d01000510090a0d0b1800081605000501000e02020004020213020101050a else 0x2100e0058030c0001020304000a073111000014150363004f00020101010300010004010100002216000803000b0107240c00000100030100010c00060012))) else (if page < 9 then (if page < 7 then 0x23000a03000006032a0401080300000b000f06011c00070a031e012c0006020503000202050001010004120025060e0001013b0203020334001d010306170100 else (if page < 8 then 0x21030e06010204000007100c040f0400010200090b0910060100031d1a0c080300091e3c00191a0f0e0514150001270043020b3901000001030a05010c341f08 else 0x160d0300000924070b010602002c020d01000003261c0117000300000700030408000d02000310080200060106001e01190000030c05070a0853011102060204)) else (if page < 11 then (if page < 10 then 0x9011b25001a50060801110b013a05001601000a01381410050000050a2207250f0e020d21091c1b2100020e2a0206020b000a320942040b0304000501040b6f else 0xf000005171e0901000e0200010116000d000a2a071000011100700007031300050104010070030a001901002208121304000106172500240000000536040117) else (if page < 12 then 0x20052005070007000025203908072f0216040c040b0410006803030a0f0f163516079b0a010009010c430000080500030682000c01040b3c0001090801392f1c else 0x3012a)))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x33800cc00380002098f0e0004603041810a4e28a22020828c0004a800000102000140014000895a1010c001878a180010f022c500001c200 else 0x16833428cb8) else 0
  | 9 => if page < 1 then 0x5404d00a522f47100321 else 0
  | 10 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x8141823010202c1a000000e05020000000078683 else 0
  | 3 => if page < 2 then (if page < 1 then 0x3020827033430045409587428c00441c41407010006189440007c098049c0005c00004c08403c06000c40005c191890078254299b9c03002404406c0203880418a80000743a84a040000009401803856c10005820002c3200a44100581480142 else 0x298000a401c08002c05020006400002025c29c37410c06806c25004584c1580080000a00000) else 0
  | 4 => if page < 5 then (if page < 2 then (if page < 1 then 0x70002c096007800502780250284c12011c01c6264264028985732b407a30fc3a630ec29d00d040702a80320914023016589900c424209a834148583900144000006806109cc20a023c2350d71218000007131f4277306d860026c000023005f16118980a0a112625008200b006301580 else 0x93028c49101f833f165845a49702670c0009c000c0a200b807f795814e000006b00e82840290caa114806a08180000030053004c02c628c12c3201e8a02ac072095c0aa06b84a0300587931b4c3e0c012ab08cc0ae02058880160022027834f095009b118402d0205e6c0e0d82700800) else (if page < 3 then 0xa90000000000008d000007b1168c6250352000214228300000002018500154000009806b0d28049000001d0065219003c0ac3110087010044202614044a6805b01bcc680950146011c1430209b000000000020003e1400093040007f017802401d0c590004075322403c199409310840 else (if page < 4 then 0xac0000000000025404801340000021200000000000000151400097026411010a8059796c200017c0090000083000005b49680ac00dc23d02a0c5d157402f615c2a3007d82e60b5c00027cc526000000000000000a406408000a73130000000000002380027000005626d20002180 else 0x1700e421400b62670800038092cc00017000001d82660e2c03608bc36800c1b0001a80690db8c7c095c100015d292000009b326000e60440810294c7809841000000000000000000000))) else 0
  | 5 => if page < 51 then (if page < 25 then (if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x6246425040000876188e2d2f00d180b581000047202210455c09b2950261cab6000035031771000004d9200003f701bd80430668c943e0db83623817f205c8108b8a3b9e48663bd4929a40000568f5426c0000000000000b80076800000000053c02bb00dc801586098123480051291a04ff19cd8d608c696000000000000006f205a301a9b60000 else (if page < 2 then 0x3850320d628d20c0526191001ff01300c2f8015000ea81585202c916a004981624eac60000007224000000001986000010e58964316b0222b0cd80000000000520cf8c50000000011c006ac0b2800000005b00a805ea313b5501b047404fc143c082f000000a7e023d00458a4680a5c024631ed0166842d80811301f0031c09f00200000000a000 else 0x8b0028d02d21941c0196ad85025580101200002117a1100000066601aa081204000041ec000012880f88c280aa89300000000000001d841c9000000000012c49b3015dc3622921662cc98c680aca120718cb0127c27fe03b402090800000000000005e0341c35fc1b6a611d011a0c380042a253c074cc0192c000029099288000002540234995480)) else (if page < 4 then 0x9720c8e1a13a0d65848204041ab100d900a1003ae02c6a40182914c2f902460d489512ec57c655980c755758907f0dc7812d007cc8055002200069297e01c3307d80ac1283409ef605780aa4407e658c1ac0005bc0b3804c70099a4f3d281c2ae3485baa4cc0b3003d20d1299571283083df0da736774c65c2463311130ca867e8647c011b808b00 else (if page < 5 then 0xb66100002938c6c1186e1b6960b7a400007420000015c01310043a000000732c985c00003c851c3800000a5a300102978d5bd13fcc016008a80ca405bca1a20a9e84b30644c1000026b814b98aea62f500898cc896b8a05a8005ea4acd200001a30c98bc948045615430000001f404100490610db1474392e01a601e88654c0a2422a64ec1812282 else 0x5a01e802c6011c00a944b312a72832e121ac030b19ed0449050da234e26a8b0ed12912100002e0012343aa4c41c018f033212b5a147908fa009412222551a0290a543d268c612b000a3cf68c630a993025ea538d218c617302bd014000b0808000212800000000000000de190a40aee04145a9f00f683aa2059f028018a9c03661b9d0a068d3fc0))) else (if page < 9 then (if page < 7 then 0x520461029a014c9278804bb017f04c640a0c150c06a4825b00692c10b001401669237453163109302d520000000001d0434185420098050880adc08080402020b800fc072800460247006601246f3cc48ab3c4c8000001780092bd3880a6c041131922f55c630a941d000000facc74a954762d38000007c001dc318e24000063064073d070c9140 else (if page < 8 then 0x1ac15a73000005ccc3b400d73222830b4081a0380629b1eae442969056025f19628281632b4029d214412874124018923d4d0647805a202cabc41c081a2b44611f00000020c00fa120320d884240f0000102b811c07c0199432dd0143c001e3cc8122804c6d44fa15871a9e808fccaaa63ae49a100f7440ecc43630e1801f8359801f102589934cc else 0xad400c8024401368060e0bc001618400007a2049b0e63255ac017e03aa49ec9838407e8004431c981450209c019800ae3c91cc73a926b0e078137dca8233040cd480788667c041542bd9400008183166040000d1466aa05c5620d81328c8b4780f600000bc4c49b1042595c812180270a968001d810a4a44e632a480000080081c93b95c6180cc40)) else (if page < 10 then 0x1a8b506003024c60000001c72193a552c98ac000000000030160000000011100c18332e2346000000458092c100000f78d6b5895c6272080000ae415a661cf31778000002e804f1100000000084c20b8485fb16183000014249a8801140972039901c18124c93c803d702d904e9004de148a19fb36644c41e2800021a993bdc40cd9c5304d82fe84 else (if page < 11 then 0x77693686162314380120019030000120406209018000000000083e03e9369024451801c4d7d04000092c6000059001d800fa190000000016000f7ccae203b7027f9963c018295357831027c06518124c32ba0400004b214a4015700904c00002dc020580e85e84201d7000000b98c00000f50279010ecc72c044802518800009d201af1c453a0898 else 0xa4c01ef00000166408fe24ed023f0000003d2344c0e26816b1800005b71acd812546000048a01a59e100021c017c127080718c000022f3039311e409ee0000026d814a8088605bd0000016f8c000016e11ad81458000000000000000000000029b4800000000000000000000000008dcc21d6c00000000ad003580198991c10ad21c0c01b7363080)))) else (if page < 18 then (if page < 15 then (if page < 13 then 0x5a408206466080000434c00001b9300000000001e0d5602d980e9d24b803d230db00ca80b5e2a6040ef9800009e0200001ee82945e00004241194ac1bcc6321cb6000001024177a022449c609258078e025510a63c000000001ac71f43e02c679a01981a208000002ea057e000000d34345a037748e09937003e6033a15340507c4 else (if page < 14 then 0x34201073020a03cc035029ad00a6a5618f254f30005fb995e8e4da115c619680000019e33c9000000000064e00e24898242284b2c05a600000000000000000017918cb8028c02a212ad24329570803fb02400892004b8c0a201f1040000174000000c9185ec08e0c2d40218067a453e0000002848284063ec036d000e38c6c063805730000015e40 else 0xc000a0020c0058842f4314a49fc00f080926000000ad80d55c7866000027c8000004e2100000523000005221b3c00ed98085e27eabc50000014480a9800701a552423c15ba0000004588000000004be1aa3815e84000000000a4ac289ead20c1200000000007e4000001f48400002cc1184003d180000a06242f480001518928a92626c00012a02)) else (if page < 16 then 0x4ca1d050c0000ac409cc180000000123c00000000000000fd4c97c000002618200005a6030b02a69907814c6c1d230ad0723ccb2ac3c7484a000f48230300002d318000098663c805e619719800000530833000000000046406dea466048be0000003f9ee91200005541800015d1271a05bf00a52c7518440c54919b7016e0000810000125980000 else (if page < 17 then 0x1f005301a7a007fc02e204440847015dc869edc9f000000388c43000000239860000a40011f56b908cdcc84a225e70c7980000000000910000081008aa05300000014ec00000176127988c4068741bc6480000000000005a00800000000000051000e1185e0a00002f111040c7d402800561003480eb52622046d0000007b801a4c4e311a43058c1 else 0x36100418645521cac15661a53c0bc200003616068b009805281a0862860048c0690251311ff0d01521ce9504013c84d88081828ea540000db8906e0520322f001bc07ca0a4001c8300000a5ac2eb0a7b013d405e0000000b70084d85aa62e40000014fc61a204cd480001161c7e6042000671a000061e945f317ab04bd2b5cc5bb024f34499e))) else (if page < 21 then (if page < 19 then 0x1ae197718fd5d0000000005d80000018c9000028da5084400001051800015e0e7f0601a000000ec926ee00400661a40000a9600ac180000000000005693400005b98000027f096b00b09872e00f70000000000000047f004f9862cc000020f1865000000150007d0eac80000028c907c000000d3c07d0100000070ca7c46aac80000f6b00000 else (if page < 20 then 0x4e2000012f002304898100001a79328d295a64957a8a804b05722007e00000000005580000022b80e783422c00001820000008880000009e2d68c30000007004b335c8da2609aa02458c53d84b0140702d0071940000057d3a4630489e48694083a64000000762051401d882000077e0000000e00414c608100001740139c0a020265040001304c else 0x13204e18a9581521b0000339011080ed8000004c2425e250e404e010000000013152180054160cf194d4004a003901e1812458b260000026800000094602c532de0040408b6180001ea807800668327c0a9c800000000000001c58055d2a169d720458000ac000002e6003608aadcb0202b648000171002a811dc2a2c81370496a01e20257009583)) else (if page < 23 then (if page < 22 then 0x6701ed08f940844213a544382a1c40b2020971f29a33986c61d376e9aa4b0057d8041d04000099c000003080a3788b64e1c261d4108f803bd298eb0cc49f10954c038e62f319a30c214463e03fa01da80a940774049a60548108c0ac690ab016f811cc01601a0201448cd6805f4006300d720f2c02e4014748f500220576833e13c79000000 else 0xd603a10ac6052540a3a0000000000d9d8000052a112d80000064e600001e5251f4c6d003d202c01e00006ea056c1800016d048d60205015e800000434c54a013504cb0026e94780ccc8447805c0940b09d5a5669e1cb1000015009678000004050000000000000000000cf8b5cc300003b519e080ee928d0058a0296008a00272a88411f08570c0) else (if page < 24 then 0x694020a70000142c06182000023d0c36555f600000090bc470049cb3518575180000a7408000000015c4c03430b3012624cdc03da0543218386e4c6220c5b4029d086e802a693ce11d10166d2acc1000027d80ac00af8740000000168007f2631300201a75000000000000000a40382002500289b122580a60000020980b20000002c901f01953c0 else 0x8269596111a052a42206058200d889020200000b2000000000076eabf101f3840000000000001f3ac0000abaab1b54ce8000008f41000000000a7400000000022a30ebd500001cd0a2e98298067600fc0291008800068037e61a8015146a8000f315228940c04261d4c70dd995c900000455146aad35007c60000020204738c6a4da56027fb00000))))) else (if page < 38 then (if page < 31 then (if page < 28 then (if page < 26 then 0x7d2085702da80b0c097e6135000000fe8c0e833ad19ec0149c07c61450021f015a4000002f8024000b040b2e61bd31fe8050d20000000007c0600000000000000000a0010000000000000104c00005ba624e36000059a300002ab8034d824c189c01f61896008220ac7106e8017c012208d50187012140000000001a6068a4268ec1121909012f00 else (if page < 27 then 0x574c03318d3803e402d43000021b014a8c9e60160487480d800a4a03080ed8840000014956500ec0c7dcc40e00380163823194624012d02038706825be900300168ebd8692402af103d8753c499e0000025f241fc258804cc026580605b86e60f000fe012800508048d196730dd0037064e302270060d878891dc02c6805052334234e01f7803ac0 else 0xad0191e56d80400004ea1472616680fd8c792917931eb00d5c0aa433c30a92b8128064a055d020400cd587b6043200b301614188a307319e2a439800620168084490f84c6ca20f6013a046bcf94e000000000152097b8023002aca556c00661ad5024a30268183c00800e8b80afcc6a4036d1adbb151013500042009a247c1899492aa6221b638d6)) else (if page < 29 then 0x5eec39a48f4807009256924f02512461927340000018b250596a140ba70d54009180586240f31e8a4314000001a531448600000000585300000000058e0000000000d7401bc0000016500cf4091205610a4380f85803a024a1a8d1800000000000023d8000006b8024301a4002a821fa1b5e0d06382b80024048c0122005e807e419e67172a54d18 else (if page < 30 then 0xb440a746bb2025800000043e043f0ebd9d13c282f10b900a2246b80b840356029880b7cc85ef4a102228600003f230000000009800ae403ca014e8200000e8043d002900a54960c00c831fe98d4c0750b000000280fc00980000000078c4298ada03a94ad518909200000000088b85395694906e7a4f18b41e9f805261905954640 else 0x2da4a08808fc00000330111a84b418acc05334a260326407cc23d001191d00400960335010b0a9942380100001f3055ccf082055e027600879b3421bbe58000057923ac01b216c8805e0419a904471802a8bc042ac2e701c300849e374607d0a4b3075dc74c94ba040001668c000010002a00c00005d205bf48da0052169dc080002a3000000))) else (if page < 34 then (if page < 32 then 0x5ae02ef129db85dcc9c0e07241e40548403c2639b018e0d1619a88009d003a30b400874059979dc0022449fc1b1e02d601261810c24de595384970459605b6199780f7c02aa05240103b04480000034402bb83249b51c1d830d64b06dc01fe309b0241389680000052c0e2100cac08f0055a02138930c449ab26e089eaf6e4077892c00e3b015e00 else (if page < 33 then 0x7a80523002480e943000000002d580bcc0a740000026b00af0c42632880c5a24fb400d401ec002e002540190900002a800dad87c200520c28b147c3a7004980cf5b0b38600001f901aa3800004f614e90cb38400003f60544263708c740ae002d9014081674001c043c0e2900dd808c262e44a8d8141030b009d4189b80ef80a6a22ec000000e244 else 0x24403ce017a014658b3862fd0c810167c2a26053c71daaa720c16c00e000b38274c0046045101d02cfac07bc02ff0d65314240a381b1b30202c984084803e152ac007644a5203b9018e8c5d80b1e654802d681704c63608a30278a047120e23334020a814b40b161088109f005fc0086037d6118855240adc65af003280cbc3b6a1249000000e800)) else (if page < 36 then (if page < 35 then 0xa9c02ce01c3985c168ea02a300d101550068605970abf813780b16604031f518d240a92c15f790cb06f8c75204190189aaf180892047700828118809a603de0e61a0b804790030c02b0003e5bb0e7cb349de0ccfc049114ba4963006d401aa645414cd8006405e60c5e31fb012780024f159158624c492312030630aca443465d860da4910b13b80 else 0x4d801f83000016dc073094ba024cb0c8007d4012700e598eb40a28180000000000000000557600c0960cf596c53c654c071e8096ea5903074ad5b00b2a03da047d8a6ac38b434b93007809b1925c90f178b08159006e60528302a06e486ace6aa549c100fa0064404d10034001300648021118240922d89be04bd018380c8d3604d87800bc0c5780) else (if page < 37 then 0x81008cb018b28a9d60000200263388b68056c009e01a48d540685260eb0e278147806d8c4d549848000007e82c0a013b840000b704be202bc091bd85842462323984a2923380000000000dfd835aebd90136050580876046306368ca2c09f400810000010e0c1d848000286810652000011a495780bb4048e03e4005501328099200000088890cc0 else 0x62803e6000001478373a0487600000040c610000001a33031803cac096723630d940000000000d6000080910c0000223800000000035b16bf98000091c18ec6e049c000030c64ea008d8d1c448240d070a091856126cce00001be30c98000003fe48aa000d809b8824b017100d14074690c732b782fb0394a1524489a00c181a8e34561400000000)))) else (if page < 44 then (if page < 41 then (if page < 39 then 0x6be05c8012e0296c1034c05d0177000000660000002a5ba2182aea29a00c00000000466a2d5040000000002ea8ed6c0001251e882280000000059435b890e8624200609845405360e05054ac253290a500170506046ccc8a478beb93944b1a11b019cc0103c23c6c17860f80a97449de21ca326e802f1230004d800e498d300000000002af240b58 else (if page < 40 then 0x3050dce0845d27389000004106000071e3575000000230200000d4005f2402cc5cc900000e6002bc3b6400000046824c00a101d9530000122c3a0a121a16df011b5c31a619b72730000005fc047401b236dc0066404ce4ad0020f00000044c02b7a1150079e15c60198036e5873c05963020ad6f46ade0263029900a6927c0080e0df8036d81 else 0x2c82000011d800d40964c5420166b084de1aec16e04df9811067541b1702d7084d5221e010430649813c49bab21c02d700ee463a06417706200734c562921b00000032140000000008680000038804660094bc309200001a51468c4000054cb00001f199275b0000328028c01668042e01d801cca5079c416e300000001490c2ca04390826995612)) else (if page < 42 then 0x54825393691ad51406e8643102da82f28391ac54c292e80e380aaa30000280980f4000001d100fe993940746037a3a4101110382a25c700b904e4980000236000000c3403fc03ff180001099c000043b0800016d4300003293191ac00004ec04c202b380eec034804ed10520055cc0c202e0305fc4000050c00d90107312500ac0352f123db10184 else (if page < 43 then 0x49804430d98a4f300158c2d261d80cb6c05f81cd20149061dc68dac2850169010b0094c04740c97012506840857232af80575e134215602cc1928860c8000002a080835c000022e325424d2c39900ca9784f80c580ac6600001610042067fc628301e924000041ef00002ada55b80000000002578404e15d293fc000001638014230151804081e80 else 0x1b69000017c30b80000003630049021e42928129e01e48a85d8786937f0109800000a081528012680839e5d402de30cc88a084000018c3000010a04a623253019d00850088a136f02b78456004720315028f810bc07c069164abb02ce002f6230a000000f3c0a9a04aa0adb01501844a0000000001024274c05860185a530c02ea62240193254140))) else (if page < 47 then (if page < 45 then 0x55a2000006e0000008d803cd4806042f0c63462896000000000a8448000000000b0300000000090240000000015d60000126829d0089c6000011e8300002be000000dc409c805920000005e524f4155330000056408340430482d805f802a663bc009b06f0d4000000002e08095c238e92960eb386000085c72236000002f0091604c500c9980000 else (if page < 46 then 0x4c21000000000b4200a70022ac31d500000820a97b000007403152122130b89280223e10d68b063805e6211019f004664000002de4800003553ae060d55e790600001d80000000000000065864ee1000016bc468833d10a09251d42b62053701db0200005c2001b700e4483c049400ac00fcb1488c0000000018faab6000000000003bb13112 else 0x72e9266097b0807c024a02d54a850169003dcc31e4a01b0068c766036d600000fb8092ac59319d9aa4a2110e900001908c83802fee154068886990000001cb2e60811140000042c30000141957ba0000024db014005a0343a05c0810b4cb5203a278a8b857d871ec50201bc0000008c0000000689a00003f4016d0181b700020000000015300ad52)) else (if page < 49 then (if page < 48 then 0x51203c83a70002f8457603d300680d170c8aee98831758003482c0646701628072c04e6138811af01624075e000002200537e2b3ed28f0c0000a7008d40000005886f7c173e02976cb89911c298c017e70000046463600534101980778c958024c7a2980000042a00a63201b41d463ce058801db25710115a0252480581190c4b205bd3002a41340 else 0x9d003d131808723024320269019a8ce28048615110000000000000036818000000002fa00000232b00000000029d480000000064499096051a4e7c432a1d8401a00000000000000000000000000000000223094c8c000048e605080e792a5261d672d280f10ca4a38fe01918155400000481121a050d0070a0279018d251018420c4603188001122) else (if page < 50 then 0x7de18000100811f4089404fd007a001ec028e345a002d00000069a000001a40d25d806015c1080000d50000000e888000097c05c602f700000000006c0600002d298d41b65690000122a0dcdb3e4018a1446a5529b8e205b00000009e591fa0000022bb8b086882c341006c1861d243ec25f724d00e6d28b2dbe106d500b3185ca03f104168c2dc0 else 0x440022300e7005bc05511800007980000044b0070a4915696402cf60cd011b8068e000d08ea890ac21be03f502758145cc564001e0000000000)))))) else 0
  | 6 => if page < 72 then (if page < 36 then (if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1bb026d9017d588540047800000048e106c151cc152831159033904bd0441c19ad4031c0000000000217c2247001cc000f0ce28076d0a1b4938402250071d01f1c247000f4187c101c01c5db0910840a019d1520000134401310105493e434000053d01798083300098643510fe4600600ac522ea0173c029410445c73e011ac1000014d4c45318e54c7300075c2 else 0x314845003990c08993ea6133800660506430000000007266468400000090c0276013205661300000487005bc008a081f550c549bf181a0011380463596fc2799052cd938101390051410000006931a2804ec8c3ac5000019b5284b021ec00000000001610c000003e05158080400c7046e71952c023a013e8425d49929259149ea400000047c00000173c3280300000) else (if page < 3 then 0x2450000000000000002dc4d35802664cc6124860165965700183830710c00004cb6616183ce6164105fd6000002a960000048b08000039f79db0c35e00000034e0203ce6ff60205613900519588004be81824115c406180c305200000fbc0334315f0c57f40934077100d10371c6c00007ca01f0c04ad00b0c04ee1400007b000f8db08858e7d228105924c000000000 else 0x552016712000020258000020e0476d35131200000000066c1209821c74815002fb0110406f2761d0003608cd0d76a0000008646222003ae75a0004fd48000000001604200000e84079238000000000db8c000000000000011d466e61946cc78302060400000025287f00000010b00605821d48000086f6ddec00000119c00685c32c02f668af925df004f521e2002e01)) else (if page < 6 then (if page < 5 then 0x5ef00ad0005e00000083400000000001f64083d1000007cc30000057e30068089101a48012d01dd450110daf521660a10c0000004bc46a40d36920930079c072775c30c66301498c0d25098567af015fc043c1826405d709800058049531238231da8247049f70000801d09c40b0c53527933ce71846f01f41241348f04c3a96c129816000000045b09a84c31318aad8 else 0x491011fd277d00d00657b48c25649a1143c271721c44180660fb4000000000080f01a98030851bddc0d65914c076e305305837044f80285705fd862a71619227c012a002a861515806a0de50f7b36d909955900ac8038f01e2ce06505318c41100b5c081731330c8290cdf0438d01ff804d5021f40608314d8c76a3089046ca005f4003d015c807fd01ca0c063157905) else (if page < 7 then 0x49d00094158909cb0c7bc19d6c06e50040e33c9613a8f2930429521f0010e1878c3e10004a6040000774014d0000000000070861020200001c4864cc35b5cc0fe00000068c0070c088f60884000001abc360e00c2800000129c062f052b0205e0c72400281533ce09660cc8d343180e98738001a4f0000178804894a25c075600281c47c4c550043d00e60075849cb86 else (if page < 8 then 0x45348000000001dac033c0800007c6121e0c6b531ffc00000126c15120166803b80083c9335302e4000000fa9a1ce00000000000b54087808bbc05f961344c7b53000006d931a4c07c110000000001564c000009bc467b3142c00c900900c3d1180e030000024d875b48120018f4985c30c114f88049048ee4f6cc0131cc88009d84e2cb020fc04bb0d48d874649a244 else 0x160d2840301000000690000000000005e1848c0037924a30985426b4012d8039860938058d498142317006f8037900280012002044276c090718252110a0089601bbde067018cc00dc48c452094604bd01d200000011970000028201bbd2002309ac05de11b4c0499115701267590958291008d413e1016a4412709238043660b5800380a084337d0007400a86dd556)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0xc8599f003f76c2ec07b731de807ca788dc447608d500000009f4064f30e5c57963132dc4e209f1c06a400394042e7149005f401f14000000944039d00440447a1800001eb4800005e0096a4000001ec930980d3843091586f423d21208802b7617a4260e3ce41832f10000022d000bd221c4a02980e300495c6681141444dc106bd50000119522cc00ecca2ee040000 else 0x80201ac9204748a6013b270b7c03260000000000185c070560000016c008f80641006c403f30000003550400002ed19618c3be00d6967c00000004f00000000000000002c248000032e112c0350d0c000000000000000000000000001ffc1794311f400130d1b402b7150ed85f2006552457100e4279a31f1026b30068d55a7006ec06130834d55e4120e0136a015940) else (if page < 12 then 0x6e700c6043890173427f6092b4317000c7811a601a8001e01212462eb0026c069f3000006a75400007fa01d80000000000048259551326a54000028905dc414923c00000000000000f500000039501d1120000161c20000092417d6300000000000ec178f310c8071b01d71259358000015a019d400000000000000030c2491146b55000000000000003352000000000 else 0xa1c125411e5c54a131f84c3bf003d8003700ac127066165e286e61d88000000290544c30000046e18000000001044682a0623c088b1124953de0062183ca19934027115f2004af00330179002200e5d500000034300469825010a95253b0184826eb60cd8211700dac03850000002570124cc7cd79c70169219041e4b4012c400d548ef1b50f012d404e000dd40)) else (if page < 15 then (if page < 14 then 0x3586134c05b414b212000000000000003816000000000000004d5c87e3c00007cf01124025801ca4074110ebdd2ab18000000000f4dc174407043000020d80352516f4086a61a8c30000000004a90000002bc60000051b00000075c3178c03b90da38000001c2584ab014f800000205002624146007122219464af0d65dc19800f1800140db5c500001484066f08f0d8 else 0x5ae04e218733019f8c811389ec15d00854126a9000000786180b02000000000455009480000000e412470e1fc25ee00a0004794c12c147350dfc000c0d95825a10946407a109175e5a30193461eb00294c0ec12080074c499a9e517001e05466540f8072b21848f81d00f8c00070127003d600c74013e3065802f5002a8a6ce19f6821cc005a1c5ad010798610096a00) else (if page < 16 then 0x4a08f7d810374000000001578000000d18000001b55e6a200ed9c0ce0183436b43206108823000005ab006cc070101f38c00002235e02b00000040701c2c013b31a90c6b60126c05200125d88650009c045149478a7a10000002c648d58600e00000000000000061b000000873602c40000007b0300000e54654a013098599899bc37076107c08130123d259870e95b else (if page < 17 then 0x66c0404cf1a801d2126ed0cabd2773015d1246a544c8063f01a283898013e620a100e0923cc61c98023f0000002bd6098c007f4800000000015803bb6c00008600127836aa0da94048301a6c00000216006901905146f03ce6c650c01d4400640177020a319309e0b600048065401ea8528804800079830ad80545698d0057b00bddc396607384000017e4083e4ce99b else 0x28a044a580000000005921000000000212860000000000c65522003c102248206900000024b09a6004b800f78200000000082c0063925301997d2609020dcc557014e4c75a018718477001a437ea60ff4c75300128056b00c90068948888481900cf4336e0211806be4964c03d100af0608e489a4468019f78517719c99c7ac15120605d01e3014ef0dd95207e00e746))))) else (if page < 27 then (if page < 22 then (if page < 20 then (if page < 19 then 0xed142a9c03304a1c40c03124512be0177c2445703f820000109d857e00bf1262001e00080d018300667018e818930c95841d8009c986922037d24df01580034b481e403b289f1c145611a3026a70000c00ef150b8a5c00dcb0028c1142424a0312cc038b013756189609c0015749a0860000000000000159d229a109e5973d6149406440000002b60800006a101e541 else 0x5fe014b0c1aa01084635f00cec17dd0220c384500a0446d1010f0048830bb4c7a031e7835d10108000824997cc106098fc10fb098b00856193d0c7f6015b835630000004500142c281b01e7c055a4cdc185884919802770198837f30d6bc04750112186c7020e406ec18b3cc59d004ac0817001d5237e0182003d909b1802b21069c064948119e70a69ee0208f597682) else (if page < 21 then 0x1894034349f80c1534865975e101ee40590008ac03154927c346c193b5064c60c9c006e061fce76530e81242670d48068b11f30048119f7028440126805ec0db0403fb32230c68e30845b5350029c00f3588fcc395498c024c915b58057300e81e2164944c47fc0071020440196126ec0005c32fb04e9e161354c4007820058021130130c06c519a50068904a980 else 0x5ff01544000000000043b1800007ef04000008049401231110064022049cbcc50201c64039a0218c035760e04c511306ec205b0c5d4066c3034924762033c12c130248029201ca002d800008076d0c8b02062015e403390de3804f101038686c20900085e000000244107c40614000b8156b31c4c56fd002b407ec007a4076401c8c07220105d80c81147cc5a304f788)) else (if page < 24 then (if page < 23 then 0x5c51057801fe01d1001ae0952005fa0118523f60103d20a20c91c163a34f6481ef019ac086408eaca000004ad250a0da3c64df3017182730cd4c64f631b6cc49248aed85ed01bc5b15549a2014290223407d149eb8003b09aa8c58449e3ce8861875407d00065966b630c15285f00f94400000f7431fa000000000021b40000018198823011ec63b5290080477180000 else 0xec57f00000003aa11f180649013b913290a14407b700160466b30430084c007b800a96c06006520026457903d3d0074349c64636000d1cc2a348650062b011e0012d48200483c0034006b650b51877502134c35e302d1b851310f80697119144738199d5e8760a22c07d00c00007a80ca7002750089447b159e9c202300d69363a000b926e1610e4003158f380) else (if page < 25 then 0x57d31a3c073b29780000a0ca3440f605618023001eb116400489002490124c046818904436508f5c675a49a44063101d4008520131854a5658e5369460af1e51d79f2c07ee020f86731308f1c86909d3c036249e54011660fa8c0cc0122534650058800fd01ac123312504de5a30816925fa30b3446cf00f4866983113d20e201dc0231e11de006ea620c804b905b500 else (if page < 26 then 0x6be3000000000035c06e8015b40000017680538798c01140492a4281000564000000000000000ce8034201efc063800d9160000000001070e230066000364000000000000000f3000000162807e231b70071f0da5c600000b2807ea15f2c310d70e5001580126c25a50c00000c4002f580cd11788279e053e1633a0e104000001f34c0000000001c631a7de808618140 else 0x6ae0d25830ba600c8079e3d161075050c0924d63160d687c0199cc3e818000055f4857042a100ae9828665e5025b1083b840000201581090ccb4400000994075701b74c1c161314c6f411e5c24c5015dcc74018c3d42b008d15679f30000000000c68062100c9042271400006b55402823c900b3403b570bb580000176c084a012040713192580000000000000000000)))) else (if page < 31 then (if page < 29 then (if page < 28 then 0x29f011ac70e900f5c282b00ee894b2148b006c0083ec367330b7531f449a1185ca6a190076600720275200ebcb0a719114a781404540692689e003640000407e33220cf4e6021dc25a80d22c100000ea900f100000059159c95968501ae403380540c000001869220309774049a31e90c816498880000013f0c00000000004900cec01c60c000060f0073c059441acd2 else 0x88e08c8402f10a1bc043f0019d26eb012ec274b486a5b3a33dfbc000001d65287800000054b48174300000000073f18000068d09cdc679b007d9276131b68580f08de0000001bf0246d49a3d84a63400004f64800005a249921266e10000000000b0127cf7948de00000000029b0211d82901149cc14f0c000058c01339b4bc01879264d61288039201b10058030f789) else (if page < 30 then 0x5c2003ac036701d08047c0181c359410f79a3ad1467c039b60cc8987001e0023dd25c4085cc0e04400a4604c1328c09a4180855555404da4ccd834c10189807a500ab404d80d77007d2493a832cb15e0827f3009cc159b01a6023ce19019b724646c030db54d44039c1498503da309cc263500d3007920099005b231ddc042229211226c01674c000016282083020ec1 else 0x64600d7862b300b4d84854800006660000004785a090507b5cec0c70f6d16c679508000039d60c50000000fe5800000ad8400000ad05669114acc6e84861453f8786d0071001adc02b71043d880c0000003ee0495403a86cf1db4271a14840000012c55ae09ac0034f01ba0c7432056c05e10912dc0c3021b00719209e807ca61ff8302c05ed8072c18c48068201a78c)) else (if page < 33 then (if page < 32 then 0x4cd00b04000000cc04636093d8429812168304144000083000a58165714b31802049228009b08000083802084075f01a00111801511837f14ae0436319e1c04ba049a0285231ca82618010ac0000000000000012a8350e015bc800000f60c3350033126dc31e2435b67211c03d72142431b900000066c00f7c06721925123a2005ec016301e04017900044003f615c4c else 0x6a80cfc414cf016e807b38624c027b1172c27c93017d25331595463760e21cc14559a1c08974951826e948f9484db0172c06ec614a405d909e88c7152000006b6496d450ae6c36570da0828c039e00000000000c540000014a800000000000000000002ff0800000f400000000000989677e00af0000001d49287519c7095c671e08c83212235285a006340170100000) else (if page < 34 then 0xc04800000fb0203520000181002c90030d61c100000000000644003804000046e553fc638718c3926ee09ead106114000041b0060d857f1107863666d7a926fc019041606010cc07db00fa0833705854082909add565761191234a4a0e9286a0026003a5260f414fb01360f83c34861222975b0005fd18ab9e0524c545258041a6cc6ef0ceb0a4c4082bdb45a114e40 else (if page < 35 then 0x5c1910dc23601d4060000000001437800001e8105dc02f30a16444915c00007740c00004bf01d38078f003a4110a750f4666714e50639231e440350008cc00000150dc6e019c8000a660000043a72218084e316a185c4100000165011d0048b01e8c02060d350400001974065d18ff1c44c0000004e53213c07c20000004a83039c2551302add80e01980c6150dfd40 else 0x32a00da4081e0400000000195180000213802b500ce40850018042493488c4000000000030f486f0253b31b40069d30000008349b4803c918908171700a880000008b8100000e5d8000018483000011d067ed00ae4000001d0c60000000000000162144f500000060410000000000000000000000000000000060101940600000000000001f6c34d7858a80452480000)))))) else (if page < 54 then (if page < 45 then (if page < 40 then (if page < 38 then (if page < 37 then 0xcb80005011640000003f4300000000080c0800008105156c079539d5404d6187e406881221401480032d269c0087d21444949803bd011e40711243112000005d8010501a50619d01250c40a6a19d269a1092828113192c05ce0d9640000013d801a500cc811c500a2028677807c06ea09ce9800001288c526157e18000012a80515700000229010b403ea182f1c else 0x516020f4000000000000000ccc000000000000000000048849cc8400000000087d38000000000e646000000000430013a425b93cce00000000944000003c840c259c08033601ae0088000e4c66f6720783328003a838720069826b730d74c000011f9437c0814180000035121d000471c0f611d4d50000066c00000000003630000003160194c071a251cd561301b240) else (if page < 39 then 0x4f061b8047b0070800340133cc1d908ec5c58701960087a00000000000865246d5000004a20c000000000000000000000000001c41a7f800365600000000000000000025e00000020e0d05207310150581697598cc1ab08568127f00df0057d004858149481318000014e0000000cdc02c40000006463000003b441380c00001e28c60301e2036eb198dc2000003fc3 else 0x6190e13cc0f015de404b0084b1700001b8407eb0143826e601b08043218000086a19cb8c623010b5854701a5d82840091442aa00f9c945910c1c051d61329d28461560512600f98987e0514407403025c06aa3599400f311dc00716256d0011b61fc042e40056846120093041ed108e4007e489700462497dc35b77092845c00882037820c51536de0196065cd00d346)) else (if page < 42 then (if page < 41 then 0x1ed0300000000032b01bdca00000cdd582810db003660139c5401021f8e75b30000000001561258b3209da00001971200001a54000000000081331c34000001f08476c01d89200000cf4231b0138c3000015f121bf0206963ec0800000894d88126c3021ece000000000651187b000000004833e92461923793184406e2159fcc13230000047f009b533b701b818 else 0x8830165560000000000350864005bb12164187100c18054900000065560e4c04e20105948910917d274e499a4262c05ee443680137963c001cd4000000dcc01096c000000000000000000f79b43400000060130f95a88608b2c310871d0c0100001bc300001e58428e0062801f800438019200b680468559b816ea01dac200001dacc20a00068413459840023b01d780) else (if page < 43 then 0x1d6408051a094200001c5c62cc1032105b500000024709794076448734400000ce1b000004dd57e430ad0376e0415408290000003555400007240000000ae25cedc47d5c000019c15b89800002188000b18744382701880c5fa193cc01525409423e869c10a69931fbc682d013c0c5530000007dd0d87524d9019a4c00000b1de30b00f1007b43cc812508000000 else (if page < 44 then 0x1ac03cc1910ca64e7856c44da00ac4507600fe8c247102312305008e002120093c422c04f981000001fc066401864009f1606526db01b24c7b831bd10000010240533493c807e50016405d251808c4213197065f30084031bb650e8a7c70d6f837710825404c6004ac53ff00e4d888508000041f1800007ea000904000000000000000000712009bc121b485a90 else 0x7c0163c07e731e1cc12a017d807643150981bd0d7e4c66f00b4005f619d842000000000000002d5d17e016a851021400004b8060782269418d5202149354c64c00ae0154e013b446ad0c5d4c00001f3d204a1429864f970085614279c0860000022577de019e002560496403e9000f0063210000045810ab528660207c06b45133c20000014d364e49cd0065c0064c0)))) else (if page < 49 then (if page < 47 then (if page < 46 then 0x6a800f0c537708cccc29901cb4c6da000000274011c814c801eac027a05f40c0000172404180000006914800003c200ecdc0000000000000174d24a40427838690092c41f56109c04ca720b8057a481b4386870000000001540288e0077c068101a09837115bd4a7ce389e584950d25c03f200920182a00ad443260626445c000afc052030dbc00c001c91c197486d84 else 0x1ea0216857df30980630f00914146800000033a041380000018a0204a0400003a17a16c47f70072d28870134c200000d40200000000045c09740076230ec626670ca54000001ef002a448000000000d7d23e44c00001a40196523a1499c460e6140000000000000691797e06016090a843360400000000002401da02234c3d418b39871b18e00622501c5441de000000) else (if page < 48 then 0x6bb621dc04610dac5242500e30045c00000042019d0401c10993806430079804522da303861006c820000212406a300300322e011e137940077000000210416160cca8273a180b040230514460000135006dd00000000000000040509e5801b510661676e0c000025a01928079a016fd8226085b8065161d0c23dd0a1b863e42171c0549154d0c5f519d506498110680 else 0x51a62070053b78c4d80000000004e10000007ff195ccc15d70499b237056c0037b08661704d14958000001469e2c33128006ee48dec04aa30c94042f600000803011b46000008ac578401164666801bc0331f0007803b41136c254218d0006fa00f21c8756118127c90a10806dd0c00000000000007b15d2292000000000801008b412f81432951ca500e185b6752f58)) else (if page < 51 then (if page < 50 then 0x44e18cec374a4993c025948000044a183dc40d858000000000000076e3620404594000000874800003ba6d505e81908f35c5e80d30cc6f3009b807ac01990c00000f5c08800ce91b806198ed3146018f006693871926ee7800004cd6deec05fc30000000001d45585b003dc25bc004bcc766493240692605ad179d05e84c0000000002ee00944400001a9834e744a2c1 else 0x457021ac065d4800004da1115d67c8040000000005cdc6df0000000f0112f822d01000006d83103980d14826810000183825624a16402e501dd8000000000000000000071a6d2c4434802198681a0008981d901558040f78211449400f34a00000c1163dd21c45b6ee006dc071e08c78025d4dc50021761bb46471021d8009c00770100001010076800f7c61d2091696) else (if page < 52 then 0x5b00a05c22880d295f00001a180000000e005a050d65604001478c3dc6cf4580000043c46f96de7000000000003290031d700000000031650bf527f201d98c0ea01348030350c8802f001760088f0813c052d00ad582f80d0b4682904e186363496b834be01cb8051f00d84054d0201c91b60103000e40033d2033020fd60000018036d561ec0553b616a01000000000 else (if page < 53 then 0x44000298009260cfc015700f9db39078c0043b38800005327a0600000018a445685489805071085c687071ac80296115f0671c216dd90000025593cf60f38102b05a90188200000000001b68c46a1c000030c160000000000343000003e9c0f70000000670d4fc00ce5881435c16112980ab2c918256c60fd0000001ccc46566016c0447016cc0491492c18869189946 else 0x4b080bc100000fa5b09d00000072101e180000006ac01236dbe1b5ac01cfc000001d8c057648e4400ac744118531312c0100000a80029701e6005064153c07392852d201b01ad1208d4882c315f0c19038730088d228671ebc57b5003cd0396013e9015a6061d262b04bb002a609d7d22320126c31f20d0b187540120d602a60000016d31290d1c6005b0c00000f99b))))) else (if page < 63 then (if page < 58 then (if page < 56 then (if page < 55 then 0x85d02180235719205264801bec0025151512000004a006bc5a0dc01057613c34b4060480228190c587ad1422d584860d6d77bd4962c04691048c9389195f425c33154120000000006883187d26bf00fe120fc000000000003ed9000009fcc4da040000000002f98125640000000018c0084112184c00000000000001cec087901754200001bd5c7b9418455 else 0x41048e0cc18401918443760bf8160700000000001c6d86a90c04427e6021d8c52e00868c101003d993d260000000000000062f019a0c66e000203072004cd2399607fcc0000000004441000000000000000f6613adc6bf49d7cc000000c8132000c1d22db0224187d50000007a600000018000cf03000002c4544672228056a480000000009c02805013940000000000) else (if page < 57 then 0x49718c984422117ad7000018b847bd50e2060ba188a9281618db0c7422a0a000940400008750131c589902200f56c1824402e10543c31641400001c00c000020d0e248028370505288400b9c00000182c24e33c000078a1544180d65c78c048e19368c71825e1400c5005e9802d00b80156e3e0d4041208cf8023d11a64078b11a2c00000206d25427828d84d930f91a else 0x3915240062d05b6000000000001d4017c400740006c459240f00c58e004d9634c19fc406966083020000129cc7d40128c40590ca44456108000000000398452531f0c27b800b342000002fc030d047cc364308f11873e3169c300000000060200088164700be405640022401cb09a0043320000004d03000007a0001fc10260098843d501504000001b90667731a680)) else (if page < 60 then (if page < 59 then 0x86701cf1800000000014708b78066a605c180000000000000000003521955866663097c053731e70c12200000000002158041222051203815f4c04804800000b20184154ec75b58c59b31ec9686b1960405c801ee8015648db58795315000439617e9845b200b5201c0135926c80105c6718003e046ab0129034920c4f002130e0f800a8257b024fe1959572e2005edc else 0x5d408000024404de8048d020e80138591412794391f1686f241dc06be0021125010202d88331099806e40d19c6000019a4000001dbc01dd00f8c96a435484c3ab708a8085c015bda5d6008e4c85b04000069f01aa8111d00f75a6e36089017973968125243059c300000390148a053ae276900cc4c70e3108d8456591485000006318000000a4100001f41e4db10c8c0) else (if page < 61 then 0x48900784018b49470029d0215401d70c000063900cb40000000000000020ec06240068845ca600b8067301410000001a74008958000071960375667a01d4473a30d4c8075105ac8c6ba6003403956096c027404d5540000096cc4b000dc803d51974924b701aa8000001684000000000012e00804000000d70033908f9c8215492542816315e12331010bc615f011b80 else (if page < 62 then 0xb9800000087920000094c400000fac000000000023401fb1864830000028b0201801e5115b800000154007c508f51869e00170319e0000006c618000000000ef0900001c71a00001640400001d140000002e800000000000000000000000076c00000007c17d7320c4013b0155d44bb05ec062f200348026658f2ca00000000076151d70067431224123a30eb8b else 0x5e70977850d101969200002110c0e358ab4240164b8c054388790086560000054c0d4ac0041152c8229a00888000000000058148000069839371037101b918000005280000003a0065e01d1c059e48df8628f00000074d487dd25841000004e13000005d400000000002054000000000000000668577200bb400000108401c30a14c04c438000039c180000000010e06)))) else (if page < 67 then (if page < 65 then (if page < 64 then 0x5a20e199844d00fa184d11043c000001e08d7cb3115d06e301a943424611a810040105a000b0c00006ed61c50945c5800000b301e34179548000073a00000064a3000005420151920000082434af08e14600000b40179e093a17736002192643045b40670314bcc5f918039218200000000000c64000000ae0063e088b0346550408047a00e1d8792300000000000000 else 0x7c900000038e00f09800000dd031d30800002d260000056949b3404156c00003c500ff8c86d05e4c0000013d4c7710d0b0607801aac300001e9005a708eb5100000a64443601600417c016a825b86c9cc000000000000001e08100000d6532e900ab005d109a2001fd30f78331048491845b00040060c0c664043c60dd007e8007f0c75d020fd323501a68c53a315752) else (if page < 66 then 0x161403ca00c5d200000cc8c761006e838963026c13340c409d0e149dbcc59e50c4c03c50d5980469509f8084315005d5820024125ba0879c353c0000004bd00c852000000000000012b00000008bc02a718fa003410053924a3413dd011271ab03661000000000010000000001283000000000000018e0100000000045e79228c5fb30f4c07050d4880 else 0x54b1800006cb000000711011b0034d01228d3b049e543489319d5260a010c0662700a3c400000d49286031d94028810fc003ed3000005bb00f2c441d0224004ce0436533d019624048a4cf6cc0a010465800001fec0719698f402a005994440300b6405574a17cc3bb24c38000001411c1b0080d0476149a5802ef059540000002c0031a081e95015000000000000000)) else (if page < 69 then (if page < 68 then 0x29f04f55839b0167de1fb14cf8c71604e9094d76d1c4166848cd013330e15c05e90c0c16344487ec044b01850333400470057554a1c0207253f007494800003770000007f400a9d832208e20000001bf8c5f104000013a00974234948000000001150300000000003810000015b0807d265f0209000700c00000454881024017000000000168c367930d4d537a321e4c else 0x60b016a0253248000000001f0857cf09f6807f901f28c3700c00004e631390c69f48f9da40d00f7000000010954ef3d2b8012f00000000001d1806764974d400000000013f48a0d979209fa400000000000000196d20000000000000007923834800007930d82840000000002fe000000489353a000000182c384d0090845920151805b201db41000013dc40f9700000) else (if page < 70 then 0x6e001e8807ab14c3402e800ac851b20cd443455186b047d801c0c64db30000035448f80117272254077c016000000014e1265e49134c3ac702fd26a24994d81b80018002c501941800000a78005a0010c03f500000003b01168005f01fa587803150463a015698300d09c9c0135295dc000000e7c026709e78e84b198e0d31649a586353019f406e90093c07400183c3 else (if page < 71 then 0x4d0013c8c7670160c004a1029060e25a0780662014cde3dd6ccb0060949f0027cd0131c0708192a4c6b954000075119c68063b00e0051c261330000f01330146929dfc03024dd74c1d60c00000000000005824885127940c000087318de0c2d10000005f00167e049031300065e3000007be00c303051002ddb0000080826541a0bc04391815c41711000005a402114c else 0xfa9275619de8612a4800005f205ae1268362224076e000000))))))) else 0
  | 7 => if page < 44 then (if page < 22 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x23a9968540000d9d66fc18806000009f0232a188f007e1908c0402041e01df04b4c053c0b94020f8cca412942c1301ca9cf6d04c4d0f261fc1111cf1de209119f380538017ec1f6010124138379a32930d978080c956a91c901c5a43d04618016e0d0b0d194100000ca00e40c7cc084a0062000000a88a34863c70c000092d20000351580000e1c0 else 0x534100001d5b0ccc0000000000000087c07de11a718020000008667253008ba42ed206ef2b744000000000000000000000000056c0800000e14c698000029661bab05d0c29e0bf9604e0483d535e32a00108010a0230a91bc28b8802bcc3523087712b8a7d8319890a5308188c20c8687329080000b8028746451000000000067e01fa217b00e900) else (if page < 3 then 0x3b0d08e604112ad80804c187481400234025c03d6621c0003804240188494c0437566a4b44631cc06f70a6de28204871b06bde29400820d62a4d98233802000d29820000730046c300000afc0110033e001ea4280c244002749a580be411ea0000010a0c8a92682021a0000009f8079ac43d0a1718cdc40000000022b18938c00000f8307b009d04 else (if page < 4 then 0x3f4010006229eb40c50203de89ae2606c06de640804bda4f51e0f8514614370026cc3cee2841213980281426046804173026121e2e0b039ca80a1818a2135f084c1e8452486c25875fb8d06808407908489e0813032326919047f84f3980b6e007119000954187218790119808d021b223780cdc0ca4431dc08e3051100fb4d83a0b83310c28aed8 else 0x22d0c000000008ca0146018a1893801cc100000e7b06b5e000014c00140660927321057497401035e25200000033820000448a1f64a15980000638000001a480bfd221801110522006f5c000036a1073b10f00882044e008704000000003c40dc680000067e242c192a02894000002aa30e886000047479835470020000096100000d40cce4e))) else (if page < 8 then (if page < 6 then 0x8604126161a506c64c604036d9b8248c022a69bb701004428055e000000490c138226822a10008808ad2106c0610049068d1500003af784d186743000031401f530c84041008c355f2982ac23ea017d004c182006838032501990092008466082200001080c4ca0217060f808d520000000015b8a3c0c7d86000012282e4c000000000000007800 else (if page < 7 then 0x85001d06e38045345590039809038023066de113b11c99870586da2b7118840029cc000000000a0a400000000000000000344a1fa034701513911c0780606c30628112c05101339009f00bf5210a633600d1247d823d8c3fe60260080c382a03eb30bd2472c385602910059b0208256401a601f700e88656a9aab48b28608408806000001c800000 else 0x2c603a601e4182c0c760f07460d98c0000436029f3140987d4c750c1ca1800007e893a213e635218cd7060020375184a00d440254002b10f3ba248004263fc20d88cef833e61849611e083fc04d478c302199e8ec0000043d38902cdfc0796c12908b60686d2000044d018f10b95a078020b51e0007cc20000000019400da0035e9000004e00b580)) else (if page < 9 then 0x16a554a98848165830cd488d020000224003201118d02dc364f000019c00e780000000002211c52c000003d87a00b665180000350010ea4e04086e000000000055c129a01d9184e803ec400000000000010a4047c0357400000bb4000000000070800000000044a01468051408cc700000500200008be60836cf4bd1bc0069141d5496ac2d40 else (if page < 10 then 0x3d293920c58980740602100000ac800000000000000e584f6c41b80000007282d610000034919a9ac25c625e032c0196805d92214942734600057006de0c3231d02455408c06396600000aea12346be424700026cd8b0636301ae00744901a0242012280f9037720000000000de404f419d100d5a40000572b2361902007bc34841800000000f75c else 0x6ae244501a980899674a6149110086db407b8e22c0c4a8085407646149491e88a4421da00000143841e0c40012ab042b801a1364c046f091d1ceb8c0da001548000010454300374622a06d0c0678107b40f30a428200000000000007658830333830000094cd1ac2236015f2400001aa200000ea0701d8000023a48ef00000055e0c5f00ab008dc1)))) else (if page < 16 then (if page < 13 then (if page < 12 then 0x602019501ac80ddc013cc32a01ebb112c14bec3f360eb0092015dc03a90dd0187fc163000fb04e5926d8651a1c0f00a4062d1c2c29b9f31a300a15c3e8004c08a230ab1284c61ff49032c1f1c232b10808810872c078e637d053b0118003fa33b201cc861c406f6624a013a871a9251a126e78e2b9039e0000092492506b6c4412941749cd001944 else 0x17a13e408f906b4406e63104046e80dc9280e013564b0a400005a4039d30bf00d54d00001a5790e8080c28b6037a01072476c02e001fd00db8c600035861e500302c95836fa2000018280315578c10e4000000e60e40631c400932c00006b0239508f80000c3886001a487c80f040758908f481c3069526a400b03df210308304600a1449b802800) else (if page < 14 then 0x37f101bb045d32b401d408682062923c601d2013298965b622008e18c0a4688c23c03020dd58cbd004aa03df01f686bec2674028030428c71c172410e6016686b7421b822a958bf84b99b3dcc06d31092800008880b69722e98c01225603a909da845452000034f5a0d8000008acf00b000000de847f460753221026c9253e0439393731104f else (if page < 15 then 0x2c801d405b80c0000000043101570000006d600000000002d8000002b101db987c923800000006b8abf9273a00c70d5581120c00002eb300000f9064920307000000000004291d11a0134a65b00003300004a4000071003e400000063808847b2805eb0c6d5800000000000000000000046948c22808d200000846c0000000051ed00001ce18bc40 else 0x324001819580600006721421000000794189800ae311f02a59e6be9bc2014486df0038602c1309c08cc405c461b961be809b404980a32020e0c000000001ea793b80d3d20e69364407a030bc17f8c21e004d0c76093a603b600b39ea2da85c00fa122e80a9008d8034c19c900d7d649601d931c018fc404641c3d3044a4884000001690dcd808b40))) else (if page < 19 then (if page < 17 then 0x436a3340071887a9247010dc05f318190112ea119407980d84660098dd11b380de0077400020d3e06300312e3a5331feb0ed4c178114f11b830745875202c44a0b90f69222601e10055066d0644808954937989180620183f000000f49241a309e79c1804281502c000018687168049e003070e834000032801e400ee8200004a8180001fcb60000 else (if page < 18 then 0x30045f783020a203802d26d31170400006dc037b017d80d6966780000016586cf8c790200000cc00a4c200003983c00010fc08e218694d7d0424c62c003824841b4479659c2b41309c027ac059010000236a4bc126c002a8480000528242a0816002500625276a043e30e58c25c0000000000880021dd286000a11a118fa9a4e4d84801da868b80 else 0x22a80593000003103000035f01d6a4b1c04e20c3d0400000000000034c000000d29000000f610a1245893070dc4605949cbac039cc34e193800b6401b6004f61112904401422b3d0190186bd851edc06020518e1812326110183998ec18040045660d4b0d0804e400c60cc6870e4f1be0c1d500000870078a1335008a0015002fe1af201b2081540)) else (if page < 20 then 0x2922800000000c4cc0000000003d8911415aac14a05eca42f00000031f60ed00e60c1e201191052000018000024a080000d10065c016249ea3000000346090190b00e1848ce000000390047c01e0036219e80c0000000000001f5800000762180002178000000000237010382f81800001b860a304c38089e0000000000c2c0000000001af0d0712 else (if page < 21 then 0x7860388105f8c00004580000022e00e3cc31e0324319b05118222a600000eb8c3cdc354335b11cb9800000000000005a1400001d00439011c80fdd871203c330753200007d4d8000000002e584e829ad600000000000000000156a50e0c00001e20000000000000018d61a519124c70e19d94860860000070d26a0cd198e54c0000000020b000000 else 0xb820ce040000000000003aa186c8a1e0667a200001450000001901bc5300000a9d28c693b318c630a5400fa5195088888a68322408000150020000000005b01880038811900153014d9800001a68013491102a7034701af800fc8c434020403040216b03618482093670cf80140c0000000000000d0c14aa125a007e240000000000000000015cc))))) else (if page < 33 then (if page < 27 then (if page < 24 then (if page < 23 then 0x20f01b326e08c5b8e468488da10d0c00002de0dc22400000000117359200619564600100c122484d2690037611c30025c15780077015ea483406b2330601fc92a184652041018ebb0f3c601400fe117a84000000001693de384000000003c500d73cefc26f42a0f51b32cdd061c601e801dd806bc01ea09a700452447001f0914604a3802a82 else 0x23208b780f143390c00000d088260225803b930e890815632c000905c0987b404687346495f98a58000001cd0cc88105c23a8000001a68c1e1884010b3306b8255c4074031408000037c08ae0223052f38d6807da008468531800006ae094a0d6080899708803d7188580000029813727800000c1d7e8d4172400008bc030aa0000135982940) else (if page < 25 then 0x3b17800009403038e09030519e0000000000000000094410d80000016e866f1c8280234499e0200000000000000000b114470020c00cf00e080000024000000095023201000022a04468c6de22be3205ba000000001b160d400b95b6ae6836000000160c88a1126121a044fd27aac20a00fb810d4c00004144a0192bd4080800000000003002 else (if page < 26 then 0x46e23081000000000000014b04e590510623290de4800000000236200000dd9424004b800000059800000598039100cab0d182000021855df1827c06b8404a0cbe28258641409460c350019407a203bc080000930000000fe040000000056093760187b0fe5a1e4107878be2a00008d0007679b78608c157863b479c8983a9c0ac04614976000000 else 0x39a12817a1c82000000000000000000000830000000d62420c91061be825f486fa8925a9a9b00fc250e800cc02df692680000000000ff040d8cc6dc7f401300078b0f9811c091fa180000e78324e03e80cfa18f8813f413f46cf7840cc08323000008aac94836f0123661042441c080443be00c22abdc0000000000a324db8544801b43195800000))) else (if page < 30 then (if page < 28 then 0x22a90000000002780000025b00000116cc7486452014834cf0e78622cf6cd9bc3c8002cc3c918000000007f2315e003d3000006f461b3021200000069e9800000001004900000000000010786572b8000000010e837420000012130d3c058493da799db800001da23970235b02c8c466c225540a2409920000327000000000000002284800000000 else (if page < 29 then 0xa402c90105802049644323b10df0086c10dec053015a00338051c139000ff000000472138411710073495ce63e8223180f9801b4c3b800793306921920345304e020000432308978e600290c1ae042805bf8200002809178488904a41b0eef4460176827fc4000040068d8000000622f0000000000000000000000db308cc6442092308ee000000 else 0x7fedbe20200901a121360405300000b41232e022300000082d575af245322480cfc24400b150067088640242009a78e8021e127149a1e188398c2007c2c36601da24eb9284e00d818b5866dd8000018d0068b9048680431f801f68453035141000020b865c8046879bf014a06c24066e000901a78cfa888860b153041907dc288e1b9e0868082043)) else (if page < 31 then 0x62011ca61fb123641818000001d88000008266420010208fb001d212e90c148626982e692215442b0a8c041e0bd978702c1452848634e0189847d4644638f90518070c0c42e30ad793580fa42574da47001609188c5e603220102241c007e2608309622ae64032e1a9e01df8694401da08c90d2080920379831bd890700760862818b9190104fa02 else (if page < 32 then 0x1063376144d2400003f6011d483aa4268045a13ea192f4400007ce300001f682bf038800000004c06f9402ee901e721d050f067d2002559be0852128401a696c40911c4286c31fa0dc81800008b463cc620c8105c0800d835600000d90d13e6234309d00000000002d8600001198211e627b61de0664037e40364053c80018413001d16c5880a940 else 0x84e10a285e830fd096bab00000fa2400001084b4d208c802b03324623a5140007241000038278e700d7460ca2b5c08f60cff8686c00000041800000000032249e88c000012c0000000400fc006c20081080000000066a082f1410071143810da4b3014044c410d6046201cd98490020c044c09868466c07f0d4440128004d58462900000aa006cd2)))) else (if page < 38 then (if page < 35 then (if page < 34 then 0x61a0019101f242b800c6e00000408073064529093000000c580130a26c019d80c0c015ac2e701d7b00000868004a0a1500805284210316d9e987fc049810941a0e8c00007ec40e9022986f8463bcc10901c280f8c1166f30d31219800001a800dd04da30c64052c6000002680739b00003bc008e80e00026600a801490001520000000000000f386 else 0x294210e00ce80e98c222000001af00fd0886a0252084d840000000002d0400000000000047001d800d6c0000000001ca9ea3830ce0252022104a0c153018000206a50b464e62800014e8234803c80a390cfc810ec003e014748408c95806d801660c9280754008a324301bc18100069a127d00d0084e40000000001a58d17d20000389054b80fbc0) else (if page < 36 then 0x3e290fb00491082001a6232e60213699805669150000000ce4c000f04500710800008d2002a01b502d34068e600001d8b0f5466de046e099e18df85766c04b0dfc362ac33be030a31c402229e3ee1baa60611e36406c632e108c58017444041a4534000014126102800011f82798400002fa0d4c8000002e8008421ae2499c04c4c00000000080c8 else (if page < 37 then 0x74a1b4809fc9000000000426022400cfc12c00c6b1a138626c36946a184800001a5282c33ac30fe009800796338b4cd79817418c6f05e100000289b45c193c0615185b437fe4c2d31aa2c0000290119319a82cf3d82fa63d348dd2002041b430000166051543424ab130c8498998c00002e301bf0046105ae01a4486284000014c031e25fa8c6054 else 0x7e6300001fdb0000000000000130b09a11000007760060910804c8209b0600120ed677a038a480000d00422e620001b101160084e08f71042a4421320201c700d7303940000045e3122183b0402403e300950403c30fc030a0226030e8e518100001b02c33c442800d41861841c8c2ba000000e10000003b0dadf619a8885c74c2f14611e30632c0))) else (if page < 41 then (if page < 39 then 0x77e019a00fba444c440402ef016a009500356611a0137801c830bc018d088280dc58490145900378000008946000009982c4583ba0457320280000000004390800007bc071e02f3093d04e8cc6ba022449c20a2a402b60317018980e7c088c70d218000064c068002ca0ccb8400000b40000019d18000023a11d00160240000516c0000000004653 else (if page < 40 then 0x6aa625871d381088080043c401e5308e834e060eb05e4007b8633290be0d0faa244000002cb09fe34885472862f9000b8007c647e00000000004e4100000000000000000118c22c08c801178036894090000001fd8814026c311d18000028e0800000000d5906240000004581010c8d0a000004baa59c33f61a3a08e338e5808c661a63229851b80 else 0x57631fc48a68800006ca00641000005e525b8cb37321e8073c0416941d01be0afb4c05c180000da8c00000000046600000e30074a1000013398000000000000204007ec21c400f401290228c34f400000080009fd821e015f006b880000130ab2932330045531c0b80805bc984a000be04210dd88426407a660ee0218002dc083a382d01f783185e)) else (if page < 42 then 0x6ee643e020b8c7c807f04800000000000044001993142b2f10217a1b5441112a3d423a2d452080001164c438927101fe0cf25884a62b85df786b6814d02a5d011d2aba814d30a03022800b9006ee0800011d83021a00004410d0084e543354007209ec2484405c21b1d180582398122c03c602101c4b5281c9104116300a3d800000983800000000 else (if page < 43 then 0x3460029085d00ff4600001b030dd08000042e0230093220a680188780001438621804f0013210f90408968841c56010202a0801e2ca3401c38af2014c4d95800ba8024898747bc3051a289fc04681b9c020830739a528c078005d18000005201b91a229c1cc60fae46631b9b0095754c932a3113aeb980170007661d280fc8c5540227591d008c00 else 0x68a01803000010546000000000238073488d404720c9e8024827706464013e00f1c033a110c08a924d212230b38e001a39170c)))))) else 0
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
def cut0 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xc0c0c0c0c0c0c0c0 0x18738f59779f9a7bafdb7fbf 4 7
    pinBase [0x0,0xc0c0c0c0c0c0c0c0,0x8080808080808080,0xc0c0c0c0c0c0c0c0,0xc0c0c0c0c0c0c0c0,0xc000c000c000c000,0xc0c00000c0c00000,0xc0c0c0c000000000,0x4040404040404040,0x0,0x0,0xc000c000c000c0,0xc0c00000c0c0,0xc0c0c0c0] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xa0a0a0a0a0a0a0a0 0x14734f55775f967b6fd77f7f 4 7
    pinBase [0x0,0xa0a0a0a0a0a0a0a0,0xa0a0a0a0a0a0a0a0,0x8080808080808080,0xa0a0a0a0a0a0a0a0,0xa000a000a000a000,0xa0a00000a0a00000,0xa0a0a0a000000000,0x0,0x2020202020202020,0x0,0xa000a000a000a0,0xa0a00000a0a0,0xa0a0a0a0] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0x8888888888888888 0xc72cf4d76df8e7aefcf7eff 4 7
    pinBase [0x0,0x8888888888888888,0x8888888888888888,0x8888888888888888,0x8080808080808080,0x8800880088008800,0x8888000088880000,0x8888888800000000,0x0,0x0,0x808080808080808,0x88008800880088,0x888800008888,0x88888888] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0f0f0f000000000 0x9efdff9aedbe96dd7d92cd3c 4 5
    pinBase [0x0,0xf0f0f0f000000000,0xa0a0a0a000000000,0xc0c0c0c000000000,0xf0f0f0f000000000,0xf000f00000000000,0xf0f0000000000000,0xf0f0f0f000000000,0x5050505000000000,0x3030303000000000,0x0,0xf000f000000000,0xf0f000000000,0x0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0f00000f0f00000 0x5dfdff59edbe55dd7d51cd3c 4 5
    pinBase [0x0,0xf0f00000f0f00000,0xa0a00000a0a00000,0xc0c00000c0c00000,0xf0f00000f0f00000,0xf0000000f0000000,0xf0f00000f0f00000,0xf0f0000000000000,0x5050000050500000,0x3030000030300000,0x0,0xf0000000f00000,0x0,0xf0f00000] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf000f000f000f000 0x3dfbff39ebbe35db7d31cb3c 4 5
    pinBase [0x0,0xf000f000f000f000,0xa000a000a000a000,0xc000c000c000c000,0xf000f000f000f000,0xf000f000f000f000,0xf0000000f0000000,0xf000f00000000000,0x5000500050005000,0x3000300030003000,0x0,0x0,0xf0000000f000,0xf000f000] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xcccccccc00000000 0x9efdff9aedbe8ebcfb8aacba 4 5
    pinBase [0x0,0xcccccccc00000000,0x8888888800000000,0xcccccccc00000000,0xc0c0c0c000000000,0xcc00cc0000000000,0xcccc000000000000,0xcccccccc00000000,0x4444444400000000,0x0,0xc0c0c0c00000000,0xcc00cc00000000,0xcccc00000000,0x0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xcccc0000cccc0000 0x5dfdff59edbe4dbcfb49acba 4 5
    pinBase [0x0,0xcccc0000cccc0000,0x8888000088880000,0xcccc0000cccc0000,0xc0c00000c0c00000,0xcc000000cc000000,0xcccc0000cccc0000,0xcccc000000000000,0x4444000044440000,0x0,0xc0c00000c0c0000,0xcc000000cc0000,0x0,0xcccc0000] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xcc00cc00cc00cc00 0x3dfbff39ebbe2dbafb29aaba 4 5
    pinBase [0x0,0xcc00cc00cc00cc00,0x8800880088008800,0xcc00cc00cc00cc00,0xc000c000c000c000,0xcc00cc00cc00cc00,0xcc000000cc000000,0xcc00cc0000000000,0x4400440044004400,0x0,0xc000c000c000c00,0x0,0xcc000000cc00,0xcc00cc00] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xaaaaaaaa00000000 0x9efdff96dd7d8ebcfb869c79 4 5
    pinBase [0x0,0xaaaaaaaa00000000,0xaaaaaaaa00000000,0x8888888800000000,0xa0a0a0a000000000,0xaa00aa0000000000,0xaaaa000000000000,0xaaaaaaaa00000000,0x0,0x2222222200000000,0xa0a0a0a00000000,0xaa00aa00000000,0xaaaa00000000,0x0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xaaaa0000aaaa0000 0x5dfdff55dd7d4dbcfb459c79 4 5
    pinBase [0x0,0xaaaa0000aaaa0000,0xaaaa0000aaaa0000,0x8888000088880000,0xa0a00000a0a00000,0xaa000000aa000000,0xaaaa0000aaaa0000,0xaaaa000000000000,0x0,0x2222000022220000,0xa0a00000a0a0000,0xaa000000aa0000,0x0,0xaaaa0000] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xaa00aa00aa00aa00 0x3dfbff35db7d2dbafb259a79 4 5
    pinBase [0x0,0xaa00aa00aa00aa00,0xaa00aa00aa00aa00,0x8800880088008800,0xa000a000a000a000,0xaa00aa00aa00aa00,0xaa000000aa000000,0xaa00aa0000000000,0x0,0x2200220022002200,0xa000a000a000a00,0x0,0xaa000000aa00,0xaa00aa00] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xffff000000000000 0xe39ebbf3dfbfc31cb3d35db7 4 6
    pinBase [0x0,0xffff000000000000,0xaaaa000000000000,0xcccc000000000000,0xf0f0000000000000,0xff00000000000000,0xffff000000000000,0xffff000000000000,0x5555000000000000,0x3333000000000000,0xf0f000000000000,0xff000000000000,0x0,0x0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xff00ff0000000000 0xe39ebbf3dfbfa29aabb2dbaf 4 6
    pinBase [0x0,0xff00ff0000000000,0xaa00aa0000000000,0xcc00cc0000000000,0xf000f00000000000,0xff00ff0000000000,0xff00000000000000,0xff00ff0000000000,0x5500550000000000,0x3300330000000000,0xf000f0000000000,0x0,0xff0000000000,0x0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xff000000ff000000 0xe39ebbf3dfbf61969b71d79f 4 6
    pinBase [0x0,0xff000000ff000000,0xaa000000aa000000,0xcc000000cc000000,0xf0000000f0000000,0xff000000ff000000,0xff000000ff000000,0xff00000000000000,0x5500000055000000,0x3300000033000000,0xf0000000f000000,0x0,0x0,0xff000000] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut18 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xff00ff00ff00ff0 0x1149341559751969b61d79f7218a38259a7929aaba2dbafb 5 6
    pinBase [0x0,0xff00ff00ff00ff0,0xaa00aa00aa00aa0,0xcc00cc00cc00cc0,0xf000f000f000f0,0xf000f000f000f00,0xff000000ff00000,0xff00ff000000000,0x550055005500550,0x330033003300330,0xf000f000f000f00,0xf000f000f000f0,0xff000000ff0,0xff00ff0] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut19 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xf0ff0f00f0ff0f0 0x10c92c14d96d18e9ae1cf9ef418c38459c7949acba4dbcfb 5 6
    pinBase [0x0,0xf0ff0f00f0ff0f0,0xa0aa0a00a0aa0a0,0xc0cc0c00c0cc0c0,0xf0f00000f0f0,0xf00f0000f00f000,0xf0f00000f0f0000,0xf0ff0f000000000,0x505505005055050,0x303303003033030,0xf0f00000f0f0000,0xf00f0000f00f0,0xf0f00000f0f0,0xf0ff0f0] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xf0f0f0ff0f0f0f0 0x10c51c14d55d18e59e1cf5df828c38869c798aacba8ebcfb 5 6
    pinBase [0x0,0xf0f0f0ff0f0f0f0,0xa0a0a0aa0a0a0a0,0xc0c0c0cc0c0c0c0,0xf0f0f0f0,0xf000f00f000f000,0xf0f0000f0f00000,0xf0f0f0f00000000,0x505050550505050,0x303030330303030,0xf0f0f0f00000000,0xf000f00f000f0,0xf0f0000f0f0,0xf0f0f0f0] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0x33cc33cc33cc33cc 0x928b20d38f3218a38259a791969b61d79f731cb3c35db7d 5 6
    pinBase [0x0,0x33cc33cc33cc33cc,0x2288228822882288,0xcc00cc00cc00cc,0x30c030c030c030c0,0x3300330033003300,0x33cc000033cc0000,0x33cc33cc00000000,0x1144114411441144,0x3300330033003300,0x30c030c030c030c,0xcc00cc00cc00cc,0x33cc000033cc,0x33cc33cc] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut26 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0x33333333cccccccc 0x8a49a0cb4db828c38869c7918e59e1cf5df92cd3c96dd7d 5 6
    pinBase [0x0,0x33333333cccccccc,0x2222222288888888,0xcccccccc,0x30303030c0c0c0c0,0x33003300cc00cc00,0x33330000cccc0000,0x3333333300000000,0x1111111144444444,0x3333333300000000,0x30303030c0c0c0c,0x33003300cc00cc,0x33330000cccc,0xcccccccc] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut27 : CutCertificate target :=
  makeCutCertificate target Minor5.target 0xcc33cc33cc33cc33 0x14f55f96fd7f10e51e92ed3e04b45b86bc7b00a41a82ac3a 5 6
    pinBase [0x0,0xcc33cc33cc33cc33,0x8822882288228822,0xcc00cc00cc00cc00,0xc030c030c030c030,0xcc00cc00cc00cc00,0xcc330000cc330000,0xcc33cc3300000000,0x4411441144114411,0x33003300330033,0xc030c030c030c03,0x33003300330033,0xcc330000cc33,0xcc33cc33] Minor5.raw Minor5.nonzero (@Minor5.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut30 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0x55aa55aa55aa55aa 0x51871218a380d38f329aaba15597531cb3c1d79f739ebbe 5 6
    pinBase [0x0,0x55aa55aa55aa55aa,0xaa00aa00aa00aa,0x4488448844884488,0x50a050a050a050a0,0x5500550055005500,0x55aa000055aa0000,0x55aa55aa00000000,0x5500550055005500,0x1122112211221122,0x50a050a050a050a,0xaa00aa00aa00aa,0x55aa000055aa,0x55aa55aa] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut32 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0x55555555aaaaaaaa 0x49459828c380cb4db8aacba14d55d92cd3c1cf5df9aedbe 5 6
    pinBase [0x0,0x55555555aaaaaaaa,0xaaaaaaaa,0x4444444488888888,0x50505050a0a0a0a0,0x55005500aa00aa00,0x55550000aaaa0000,0x5555555500000000,0x5555555500000000,0x1111111122222222,0x50505050a0a0a0a,0x55005500aa00aa,0x55550000aaaa,0xaaaaaaaa] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut45 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0x9999999999999999 0x310720b30f41351761b71f823927a2bb2fc33d37e3bf3f 5 9
    pinBase [0x0,0x9999999999999999,0x8888888888888888,0x8888888888888888,0x9090909090909090,0x9900990099009900,0x9999000099990000,0x9999999900000000,0x1111111111111111,0x1111111111111111,0x909090909090909,0x99009900990099,0x999900009999,0x99999999] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut46 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0xa5a5a5a5a5a5a5a5 0x508720d28f41549761d69f8258a7a2daafc35cb7e3debf 5 9
    pinBase [0x0,0xa5a5a5a5a5a5a5a5,0xa0a0a0a0a0a0a0a0,0x8484848484848484,0xa0a0a0a0a0a0a0a0,0xa500a500a500a500,0xa5a50000a5a50000,0xa5a5a5a500000000,0x505050505050505,0x2121212121212121,0x505050505050505,0xa500a500a500a5,0xa5a50000a5a5,0xa5a5a5a5] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut60 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xf0f0f0f0f0f0f0f0 0x1cf5df9efdff18e59e9aedbe14d55d96dd7d10c51c92cd3c 5 8
    pinBase [0x0,0xf0f0f0f0f0f0f0f0,0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000,0x5050505050505050,0x3030303030303030,0x0,0xf000f000f000f0,0xf0f00000f0f0,0xf0f0f0f0] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut61 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xcccccccccccccccc 0x1cf5df9efdff18e59e9aedbe0cb4db8ebcfb08a49a8aacba 5 8
    pinBase [0x0,0xcccccccccccccccc,0x8888888888888888,0xcccccccccccccccc,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000,0x4444444444444444,0x0,0xc0c0c0c0c0c0c0c,0xcc00cc00cc00cc,0xcccc0000cccc,0xcccccccc] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut62 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xaaaaaaaaaaaaaaaa 0x1cf5df9efdff14d55d96dd7d0cb4db8ebcfb049459869c79 5 8
    pinBase [0x0,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0x8888888888888888,0xa0a0a0a0a0a0a0a0,0xaa00aa00aa00aa00,0xaaaa0000aaaa0000,0xaaaaaaaa00000000,0x0,0x2222222222222222,0xa0a0a0a0a0a0a0a,0xaa00aa00aa00aa,0xaaaa0000aaaa,0xaaaaaaaa] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut64 : CutCertificate target :=
  makeCutCertificate target Minor4.target 0xff00ff0000ff00ff 0x4384794ba4fb53c57d5be5ff0280690aa0eb12c16d1ae1ef 5 7
    pinBase [0x0,0xff00ff0000ff00ff,0xaa00aa0000aa00aa,0xcc00cc0000cc00cc,0xf000f00000f000f0,0xff00ff0000000000,0xff00000000ff0000,0xff00ff0000000000,0x5500550000550055,0x3300330000330033,0xf000f00000f000f,0xff00ff,0xff00000000ff,0xff00ff] Minor4.raw Minor4.nonzero (@Minor4.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut67 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xffffffff00000000 0x828c38869c798aacba8ebcfb92cd3c96dd7d9aedbe9efdff 5 9
    pinBase [0x0,0xffffffff00000000,0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000,0xffffffff00000000,0x5555555500000000,0x3333333300000000,0xf0f0f0f00000000,0xff00ff00000000,0xffff00000000,0x0] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut68 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xffff0000ffff0000 0x418c38459c7949acba4dbcfb51cd3c55dd7d59edbe5dfdff 5 9
    pinBase [0x0,0xffff0000ffff0000,0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff0000ffff0000,0xffff000000000000,0x5555000055550000,0x3333000033330000,0xf0f00000f0f0000,0xff000000ff0000,0x0,0xffff0000] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut69 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xff00ff00ff00ff00 0x218a38259a7929aaba2dbafb31cb3c35db7d39ebbe3dfbff 5 9
    pinBase [0x0,0xff00ff00ff00ff00,0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff00ff00ff00ff00,0xff000000ff000000,0xff00ff0000000000,0x5500550055005500,0x3300330033003300,0xf000f000f000f00,0x0,0xff000000ff00,0xff00ff00] Minor6.raw Minor6.nonzero (@Minor6.lower)
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
  | 19 => cut18
  | 20 => cut19
  | 21 => cut20
  | 25 => cut24
  | 27 => cut26
  | 28 => cut27
  | 31 => cut30
  | 33 => cut32
  | 46 => cut45
  | 47 => cut46
  | 61 => cut60
  | 62 => cut61
  | 63 => cut62
  | 65 => cut64
  | 68 => cut67
  | 69 => cut68
  | 70 => cut69
  | _ => cut0

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x200001000410000000000000000 else 0
  | 4 => if page < 3 then (if page < 1 then 0xc182850a183060c183071018300000040802040010204100000008102080010208102000000000000000000081020408102040010200001 else (if page < 2 then 0x10004091224489122450b120c588162c58000000000000000000000100000000000000000000000000000004005080000000000000000085 else 0x2040a142858b000050b160000000000000000000000000000000070e1c3881020180001c408)) else 0
  | 5 => if page < 24 then (if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xc040810218081020408102180860c1830602040810e0408602204010204088102008008043810e040810204081027c20508101040804201 else (if page < 2 then 0x8102040814301020008102142850a04204020c204080408102140810408102060c185061408402100820004201020408502042850a14285 else 0x2040810204081080408102002071a2068408102040a14307081c207081030008102840a1008306102040810204081020408102040810204)) else (if page < 4 then 0x2040070e1c207100c0800204081080420408102010210081020428102040810204004021020408040810204081081008108140810204084 else (if page < 5 then 0x1020408102040a102850a042810a040010204087021c409002040000000810200081000008102140810204281020408102042000404081 else 0x102000810204081620408122058b162048902244831224000000408102000810000000000000000000000000081020408102140810204080))) else (if page < 9 then (if page < 7 then 0x4081020408502062418912240071020480121c0870e1c3870e043881408408100040816000020408101162c10c0028581020458b1000007 else (if page < 8 then 0x20408102084010204081020810710200010204081041c08102041070408102040c4081020408120848204081020408102042410a120c489 else 0xa043070e1c3070c1c3060c203060c183060c3c182040c5851000000001c381101c401101c4010e204090e2040810204081000383060c087)) else (if page < 10 then 0xa183060c1830610203060c183060c183060c387860a18205101c38810204081224481041c40b162c2850a142850a142850a142850a14285 else (if page < 11 then 0x122438a141c3800000207001c2040e14208082020808102041a106840834200080408408102040810204081040910042040a142850a14285 else 0x1a3468d10344070e1c3870e1c3870e204090e2850810002840800384081008204103830e1c004081c387001c3870e1c3870e1c3870e1c507)))) else (if page < 18 then (if page < 15 then (if page < 13 then 0x40810200000000c285020020408142850a142850a080840810081081420508102040a14102081028502140850a14287000038d0e34380 else (if page < 14 then 0x10040810204084081020000000040c10281020408502100040e14285021c409120000100042040810204081000000142850a142850204081 else 0x142850a14000001800600183060000001020400008142050a200000000000000000000040010a144010a04081020410104201010220401)) else (if page < 16 then 0x1020408100040900000001200480002400012240000000003000000000000000000000000000004000000000000020000000000000000000 else (if page < 17 then 0x22038a100000a142c60b040810a1020008121c3881020409122440810204891224588102c40b16204891028489000c4890000580000c408 else 0xe1c3870e1c0880208188101c408102040906244081020409122818a122450912204871024489120c4890e1c3870e0440812204000e20480))) else (if page < 21 then (if page < 19 then 0x102058b0a184850a1c3080c184080c18586062c58b160030f0a1428500003870e2040710204080e1c000001c3880e200081004081021c387 else (if page < 20 then 0xa1040d0a2028d0c2030f0a1040810204881220388101c008161428510142880a2068d0a142850a1428610187861e142850a142851020408 else 0xa20004080000408002850a142850a1428000000000a1420508102850e1c00d0a2040810200070e1c38a001c007081c3870e103871020285)) else (if page < 22 then 0x12300000000180000048b0000000000040810200000000000000000000140010a140000a202851014285102040400102840a102800010285 else (if page < 23 then 0xa202881e204071020488122048910204081220408142448b0e20400002040b1620408002040810204081020580002c60c000048c0024600 else 0x800200001000008))))) else 0
  | 6 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1a0c68d1a3468d1a3468d1a340811a0408d020408d0204681020408d02040811a3468d1a3468d1a3468d1a0408102040811a340830234081 else 0x20400000000810204081000068d1a3468d1a3468d1a3468d1a3468d0204081020408d1a3468d1a3468d023468d1a3468d1a346821a3468d) else (if page < 3 then 0x20408e1c0408100000000200081000000000000000204f81020000000000813204081020418102040010004081000000002040010204001 else 0xcc9932000003264c800204000007c019004c9800000000000008002040010000000000008100040810200081020000000000813e04081)) else (if page < 6 then (if page < 5 then 0x4081011a0408e1c3c78f1c3878f1e08000007c003000c000000c181060c180060c001060c08100000000000001000000000001800000000 else 0x204081000408102001000000000000010200000000000080000000100000000000001020410002040820400100020000200080000000000) else (if page < 7 then 0x63870e1c38783060c7831c3878e1c3878f1c3c78f1e3808f1c3c78d1a3468d023418d1a3468d1a3468d1a34081040008104080000004001 else 0x400102000000002040811a340830204681020818d063468d1a3468d1a3468d0204081023808e1c38701020478102080820408103060c18e))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x1c0c000060c18d1a3468d1a3468d1a3468d1a34c8d1a3468d1a0068d0234081020408102340811a3468d1a3468d1a3468d1a3468d1c38001 else 0x20408e1a3468d1a3468d1a3468d1a3468e063868d000010e0600002043468d1a3400e1a3468d1a3468d1a3818e1c3468d1a3468d1a3468d) else (if page < 11 then 0x1c00000000000000000000000000000000d1a340000000000003468d1a3468d1a0000d1a3468d1a3468d1a0470d1a3468d1a3468d1c0468d else 0x1a3468d1a3418d1a0000d000000d1a3468d1a3468d1a3468d1a3468d1c3868d0000000000000000000000000000000068d1a3468d)) else (if page < 14 then (if page < 13 then 0x68d003468d1a3468d1a3468d1a38700000000000000000000000000000000000000000000000068d023468d04081000000100 else 0x204080000000000000800000001000000102000810264080000400104040810000001020400000700000408081000408102040000000101) else (if page < 15 then 0x200080285000000000212a00a80000000000000000000000000400000040000004000000000000001800408081000408100000810000001 else (if page < 16 then 0x2040810008081020470f1e3c08204040000000002000000002000000204001000408100041010204101020408000040000000001 else 0x43468102040010204080020408102080020200000020000002040810204081023870f1c047010204081023c7011c040801e0000e0000000))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0x400000649930204081000000000000000000000000000002040800000000008401b005408000000000004081000408102000810434081 else 0x199000000000640000000000006401f00000190600019000108002000000200000007cc80000001f324c0810004001) else (if page < 20 then 0x40c00002000000000000020008100000000000002000000000080000000000000000000000000000000000000000000000000183060c003 else 0x60c18102040800204081000000100040820004082040000102040810200081020408102040000000000000400206000000000000000c000)) else (if page < 23 then (if page < 22 then 0x680003870f1c3808f1e387001e3878e1e3800e0608102040c70e1e3c700000878f06387801e3c100000000000000130200003 else 0x20008200000000000000020800000000010000000000400000000000000100003400000000001a3468d1a3468d1a3870e1c000000000000) else (if page < 24 then 0x8000000011a0408d1a3468e1c3870d1a3c68d1e3468d1a3468d1a3468d1a3470f1c3c68d1a3468d0000000000008102000000000000 else (if page < 25 then 0x1a3468000000001a34000003468d1c347001a3468d1a3468d003400002046810204000003400000000000000680000000000000000000001 else 0x68d1a3800e)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0x8002000000000000000008000000000000680000068d00000000000000000000000000000000000000000000000001a340000000000 else 0x204000000000000000000000000000000000000000000080000000002040000000000000000204040810200081020000102000000000000) else (if page < 29 then 0x81000010004040810008002020408104080000000000000000004081000000000000000000000000004081020000002040820400081 else 0xc180000000000000000000000000000000000000000000000000000000000000001000000000000000000081000000000000000000000)) else (if page < 32 then (if page < 31 then 0x183060c180060000000000000400000000000000000000000000000010000000000000000 else 0x1020800300000000000000000008000000010000000000000000000000000000000010206000000000000000000000000000000000) else (if page < 33 then 0x1a3468d1c3c70f00000000000000000000000000000000000000000000387800038000000000000000000204103 else (if page < 34 then 0x0 else 0x0)))))) else 0
  | 7 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x2041010408083020c1810004003000c00102040000204001020008102040820204001020408102040800104103831008102040818910081 else 0x2041020404081020408102040810204081000010206000440310102040e20307101010204083020408207181c6020408102040800204000) else (if page < 3 then 0x2000800000083040c10102040810404080020c0030200081060800002041800604082020408102040810204081020408100040820204081 else 0x7100030710003060c183060c18388001c400001c488000410002201030408188040810204081020408102040c1020800088000000002200)) else (if page < 6 then (if page < 5 then 0x4402000c40004081031004401040828808002040810204080020000002060c10204081020000102040810204000000008144880c000 else 0x408082040008004001010404101020000000000000000000000810389100008d18000000000000000000000000000000000000000000000) else (if page < 7 then 0x204102040800104000810204103020c08202040810204081020800000041800204081060418102040810004083020008202000020008001 else (if page < 8 then 0x4081020408102080810204001020408102040810000080031808102040810204082040408000040800004081020408102040800200081 else 0x8100081800004082020c000000000000041010000000020400100040800004081020408102040810000081020400102000000204101)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x2041810204081000c00100040010408001020c1000004081020c083060400002040030000000060c000000c180060c000000c183060c180 else 0x408000020810000080028c081020408100000010004001020404001040c00002040800208103000c0030604080000000106000000000082) else (if page < 12 then 0x4081008c001c600023008c00002000008104000010204001020808000000800000001020408000040820200000020008000000010400082 else 0xc183060c183060008000041800204002060c003060c0810204081020810104040810204081020408102040810204000040c0c58a02302)) else (if page < 15 then (if page < 14 then 0x8004001000408102000c1830408103000c1820408102040810204081000000002000c183 else 0x204081020408102041810204181020810102040810204081020810202040810204082020408102040810204000040818000000000000000) else (if page < 16 then 0x4100020408102081020404081020410202040810204081020400102081020400100000400102041000208001020410002041810004081 else (if page < 17 then 0x60c00204081020608180060c1800004083060c180060c081020408202040810204081020408102000000008103000408102040810000082 else 0x8000000000208100040010200041030004081000418002040010600000060408002000830000103000c002))))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x7a0003f0001f8000b9fbf00000007a01e807cf57bf7abdf807af40007c01f807e01f2e00f5eaf5e0173e8cf5f2e5c0000000f57af7ab9f44 else 0x7cfc03e7ef803f) else 0
  | 9 => if page < 1 then 0x22c68a023008cbe244 else 0
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
theorem chunk2x0 : span (checked 2) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 8 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 43 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 43 0 = true :=
  chunk3x0

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
theorem chunk4x144 : span (checked 4) 31 144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 175 0 = true :=
  (@span_join (checked 4) 96 0 79 (@span_join (checked 4) 48 0 48 chunk4x0 chunk4x48) (@span_join (checked 4) 48 96 31 chunk4x96 chunk4x144))

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
theorem chunk5x144 : span (checked 5) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x192 : span (checked 5) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x240 : span (checked 5) 48 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x288 : span (checked 5) 48 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x336 : span (checked 5) 48 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x384 : span (checked 5) 48 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x432 : span (checked 5) 48 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x480 : span (checked 5) 48 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x528 : span (checked 5) 48 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x576 : span (checked 5) 48 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x624 : span (checked 5) 48 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 48 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x720 : span (checked 5) 48 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x768 : span (checked 5) 48 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x816 : span (checked 5) 48 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x864 : span (checked 5) 48 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x912 : span (checked 5) 48 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x960 : span (checked 5) 48 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1008 : span (checked 5) 48 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1056 : span (checked 5) 48 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1104 : span (checked 5) 48 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1152 : span (checked 5) 48 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1200 : span (checked 5) 48 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1248 : span (checked 5) 48 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1296 : span (checked 5) 48 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1344 : span (checked 5) 48 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1392 : span (checked 5) 48 1392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1440 : span (checked 5) 41 1440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1481 0 = true :=
  (@span_join (checked 5) 720 0 761 (@span_join (checked 5) 336 0 384 (@span_join (checked 5) 144 0 192 (@span_join (checked 5) 48 0 96 chunk5x0 (@span_join (checked 5) 48 48 48 chunk5x48 chunk5x96)) (@span_join (checked 5) 96 144 96 (@span_join (checked 5) 48 144 48 chunk5x144 chunk5x192) (@span_join (checked 5) 48 240 48 chunk5x240 chunk5x288))) (@span_join (checked 5) 192 336 192 (@span_join (checked 5) 96 336 96 (@span_join (checked 5) 48 336 48 chunk5x336 chunk5x384) (@span_join (checked 5) 48 432 48 chunk5x432 chunk5x480)) (@span_join (checked 5) 96 528 96 (@span_join (checked 5) 48 528 48 chunk5x528 chunk5x576) (@span_join (checked 5) 48 624 48 chunk5x624 chunk5x672)))) (@span_join (checked 5) 384 720 377 (@span_join (checked 5) 192 720 192 (@span_join (checked 5) 96 720 96 (@span_join (checked 5) 48 720 48 chunk5x720 chunk5x768) (@span_join (checked 5) 48 816 48 chunk5x816 chunk5x864)) (@span_join (checked 5) 96 912 96 (@span_join (checked 5) 48 912 48 chunk5x912 chunk5x960) (@span_join (checked 5) 48 1008 48 chunk5x1008 chunk5x1056))) (@span_join (checked 5) 192 1104 185 (@span_join (checked 5) 96 1104 96 (@span_join (checked 5) 48 1104 48 chunk5x1104 chunk5x1152) (@span_join (checked 5) 48 1200 48 chunk5x1200 chunk5x1248)) (@span_join (checked 5) 96 1296 89 (@span_join (checked 5) 48 1296 48 chunk5x1296 chunk5x1344) (@span_join (checked 5) 48 1392 41 chunk5x1392 chunk5x1440)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x48 : span (checked 6) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x96 : span (checked 6) 48 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x144 : span (checked 6) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x192 : span (checked 6) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x240 : span (checked 6) 48 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x288 : span (checked 6) 48 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x336 : span (checked 6) 48 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x384 : span (checked 6) 48 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x432 : span (checked 6) 48 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x480 : span (checked 6) 48 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x528 : span (checked 6) 48 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x576 : span (checked 6) 48 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x624 : span (checked 6) 48 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x672 : span (checked 6) 48 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x720 : span (checked 6) 48 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x768 : span (checked 6) 48 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x816 : span (checked 6) 48 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x864 : span (checked 6) 48 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x912 : span (checked 6) 48 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x960 : span (checked 6) 48 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1008 : span (checked 6) 48 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1056 : span (checked 6) 48 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1104 : span (checked 6) 48 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1152 : span (checked 6) 48 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1200 : span (checked 6) 48 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1248 : span (checked 6) 48 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1296 : span (checked 6) 48 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1344 : span (checked 6) 48 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1392 : span (checked 6) 48 1392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1440 : span (checked 6) 48 1440 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1488 : span (checked 6) 48 1488 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1536 : span (checked 6) 48 1536 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1584 : span (checked 6) 48 1584 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1632 : span (checked 6) 48 1632 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1680 : span (checked 6) 48 1680 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1728 : span (checked 6) 48 1728 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1776 : span (checked 6) 48 1776 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1824 : span (checked 6) 48 1824 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1872 : span (checked 6) 48 1872 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1920 : span (checked 6) 48 1920 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1968 : span (checked 6) 48 1968 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2016 : span (checked 6) 48 2016 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2064 : span (checked 6) 48 2064 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2112 : span (checked 6) 48 2112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2160 : span (checked 6) 42 2160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 2202 0 = true :=
  (@span_join (checked 6) 1104 0 1098 (@span_join (checked 6) 528 0 576 (@span_join (checked 6) 240 0 288 (@span_join (checked 6) 96 0 144 (@span_join (checked 6) 48 0 48 chunk6x0 chunk6x48) (@span_join (checked 6) 48 96 96 chunk6x96 (@span_join (checked 6) 48 144 48 chunk6x144 chunk6x192))) (@span_join (checked 6) 144 240 144 (@span_join (checked 6) 48 240 96 chunk6x240 (@span_join (checked 6) 48 288 48 chunk6x288 chunk6x336)) (@span_join (checked 6) 48 384 96 chunk6x384 (@span_join (checked 6) 48 432 48 chunk6x432 chunk6x480)))) (@span_join (checked 6) 288 528 288 (@span_join (checked 6) 144 528 144 (@span_join (checked 6) 48 528 96 chunk6x528 (@span_join (checked 6) 48 576 48 chunk6x576 chunk6x624)) (@span_join (checked 6) 48 672 96 chunk6x672 (@span_join (checked 6) 48 720 48 chunk6x720 chunk6x768))) (@span_join (checked 6) 144 816 144 (@span_join (checked 6) 48 816 96 chunk6x816 (@span_join (checked 6) 48 864 48 chunk6x864 chunk6x912)) (@span_join (checked 6) 48 960 96 chunk6x960 (@span_join (checked 6) 48 1008 48 chunk6x1008 chunk6x1056))))) (@span_join (checked 6) 528 1104 570 (@span_join (checked 6) 240 1104 288 (@span_join (checked 6) 96 1104 144 (@span_join (checked 6) 48 1104 48 chunk6x1104 chunk6x1152) (@span_join (checked 6) 48 1200 96 chunk6x1200 (@span_join (checked 6) 48 1248 48 chunk6x1248 chunk6x1296))) (@span_join (checked 6) 144 1344 144 (@span_join (checked 6) 48 1344 96 chunk6x1344 (@span_join (checked 6) 48 1392 48 chunk6x1392 chunk6x1440)) (@span_join (checked 6) 48 1488 96 chunk6x1488 (@span_join (checked 6) 48 1536 48 chunk6x1536 chunk6x1584)))) (@span_join (checked 6) 288 1632 282 (@span_join (checked 6) 144 1632 144 (@span_join (checked 6) 48 1632 96 chunk6x1632 (@span_join (checked 6) 48 1680 48 chunk6x1680 chunk6x1728)) (@span_join (checked 6) 48 1776 96 chunk6x1776 (@span_join (checked 6) 48 1824 48 chunk6x1824 chunk6x1872))) (@span_join (checked 6) 144 1920 138 (@span_join (checked 6) 48 1920 96 chunk6x1920 (@span_join (checked 6) 48 1968 48 chunk6x1968 chunk6x2016)) (@span_join (checked 6) 48 2064 90 chunk6x2064 (@span_join (checked 6) 48 2112 42 chunk6x2112 chunk6x2160))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x48 : span (checked 7) 48 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x96 : span (checked 7) 48 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x144 : span (checked 7) 48 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x192 : span (checked 7) 48 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x240 : span (checked 7) 48 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x288 : span (checked 7) 48 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x336 : span (checked 7) 48 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x384 : span (checked 7) 48 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x432 : span (checked 7) 48 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x480 : span (checked 7) 48 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x528 : span (checked 7) 48 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x576 : span (checked 7) 48 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x624 : span (checked 7) 48 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x672 : span (checked 7) 48 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x720 : span (checked 7) 48 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x768 : span (checked 7) 48 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x816 : span (checked 7) 48 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x864 : span (checked 7) 48 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x912 : span (checked 7) 48 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x960 : span (checked 7) 48 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x1008 : span (checked 7) 48 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x1056 : span (checked 7) 48 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x1104 : span (checked 7) 35 1104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 1139 0 = true :=
  (@span_join (checked 7) 576 0 563 (@span_join (checked 7) 288 0 288 (@span_join (checked 7) 144 0 144 (@span_join (checked 7) 48 0 96 chunk7x0 (@span_join (checked 7) 48 48 48 chunk7x48 chunk7x96)) (@span_join (checked 7) 48 144 96 chunk7x144 (@span_join (checked 7) 48 192 48 chunk7x192 chunk7x240))) (@span_join (checked 7) 144 288 144 (@span_join (checked 7) 48 288 96 chunk7x288 (@span_join (checked 7) 48 336 48 chunk7x336 chunk7x384)) (@span_join (checked 7) 48 432 96 chunk7x432 (@span_join (checked 7) 48 480 48 chunk7x480 chunk7x528)))) (@span_join (checked 7) 288 576 275 (@span_join (checked 7) 144 576 144 (@span_join (checked 7) 48 576 96 chunk7x576 (@span_join (checked 7) 48 624 48 chunk7x624 chunk7x672)) (@span_join (checked 7) 48 720 96 chunk7x720 (@span_join (checked 7) 48 768 48 chunk7x768 chunk7x816))) (@span_join (checked 7) 144 864 131 (@span_join (checked 7) 48 864 96 chunk7x864 (@span_join (checked 7) 48 912 48 chunk7x912 chunk7x960)) (@span_join (checked 7) 48 1008 83 chunk7x1008 (@span_join (checked 7) 48 1056 35 chunk7x1056 chunk7x1104)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 48 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x48 : span (checked 8) 26 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 74 0 = true :=
  (@span_join (checked 8) 48 0 26 chunk8x0 chunk8x48)

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

end PEqualNP.Outside.L_meta_12244_aux

open PEqualNP.Outside.L_meta_12244_aux

theorem PEqualNP.Outside.L_meta_12244 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
