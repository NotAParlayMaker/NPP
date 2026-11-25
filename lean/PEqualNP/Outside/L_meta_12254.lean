import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12254_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4269834368 * 2 ^ 32 + 2155905024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [4,5]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.and, [1,2]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.and, [0,8]⟩,
  ⟨.or, [3,7]⟩,
  ⟨.and, [10,11]⟩,
  ⟨.and, [3,6]⟩,
  ⟨.or, [0,9]⟩,
  ⟨.and, [13,14]⟩,
  ⟨.or, [12,15]⟩], 16⟩
theorem size : witness.size = 11 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
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
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 10 ≤ p.length)
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

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 51) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 51) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 3264 := by omega
  have val : fullLanes = 2^3264-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 51) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 51) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 51) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 51) (xs : List Columns)
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
    (length : rows.length = 51) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 51) (bounds : ∀ r ∈ rows, r < 64)
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

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfe80808080808000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨14,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨13,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨11,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨7,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨7,23,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨7,39,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xff88ff8800000000ff88888800000000ff80ff8000000000ff0fff0000000000ff0affaa00000000ff0aff0a00000000ff00ffee00000000ff00ffaa00000000ff00ff8800000000ff00ff0000000000ff00aaaa00000000ff00aa0000000000ff000f0000000000ff0000aa00000000ff00000000000000fefefefe00000000feeefeee00000000feaafeaa00000000fcfcfcfc00000000eeeeeeee00000000eeaaeeaa00000000ee00ee0000000000eaeaeaea00000000cccccccc00000000afaaafaa00000000af00af0000000000aeaeaeae00000000aaaaffaa00000000aaaaeeee00000000aaaaaaaa00000000aaaaaa0000000000aa88aa8800000000aa0aaa0a00000000aa00ff0000000000aa00aaaa00000000aa00aa0000000000aa00000000000000a8a8a8a8000000008a8a8a8a000000008888aaaa000000008888888800000000880088000000000080808080000000003f003f00000000002a2a2a2a000000000f0a0f0a000000000f00ff00000000000e0e0e0e000000000a0aaaaa000000000a0a0a0a000000000a000a0000000000080808080000000000ffff000000000000aaaaaa000000000000ffaa000000000000ff00000000000000eeee000000000000aaaa000000000000aa0000000000000088880000000000000f000000000000000a0a00000000000000aa0000000000000000 else (if page < 2 then 0xff880000ff880000ff00ffffffaa0000ff00ffffff000000ff00ffff00000000ff00ffaaffaa0000ff00ffaaff000000ff00ff00ffaa0000ff00ff00ff000000ff00ff0000000000ff000000ffaa0000ff000000ff000000fefe0000fefe0000eeeeeeeeeeee0000cccc0000cccc0000aaaaffffaaaa0000aaaaffff00000000aaaaff00ffaa0000aaaaff00ff000000aaaacccceeee0000aaaaaaaaaaaa0000aaaaaaaa00000000aaaa0000aaaa0000aa00ffffaaaa0000aa00ff00ff000000aa00aaaaaaaa0000aa00aa00aa0000008888aaaaaaaa000088888888888800000f0ffffff0f000000f0affaaffaa00000f00fffffff000000f00fff0fff000000f00ff00ff0000000a0afffffafa00000a0affffaaaa00000a0aaaaaaaaa000000ffffffff00000000ffff00ff00000000aaaaaaaaaa00000000ffffffee00000000ffffffaa00000000ffffff8800000000ffffff0000000000ffffaaaa00000000ffff000000000000fffefffe00000000ffeeffee00000000ffeeffaa00000000ffeeeeee00000000ffeaffea00000000ffccffcc00000000ffafffaa00000000ffaeffae00000000ffaaffee00000000ffaaffaa00000000ffaaff8800000000ffaaff0000000000ffaaeeaa00000000ffaacc8800000000ffaaafaa00000000ffaaaaaa00000000ffa8ffa800000000ff8aff8a00000000ff88ffaa else 0xf0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0a0f0f0f0a0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0affaaffaa0f0a0f0a0f0a0f0a0f080f080f080f080f00ff00ff00ff000f000f00fff0fff00f000f00f0f0f0f00f000f00afaaafaa0f000f000f000f000e0e0e0eeeeeeeee0c0c0c0c0c0c0c0c0aaaaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0a0a0aff0aff0a0a0a0a0afafafafa0a0a0a0acececece0a0a0a0aaaaaaaaa0a0a0a0a8a8a8a8a0a0a0a0a0a0a0a0a0a000a00ff00ff000a000a00aaaaaaaa0a000a00aa00aa0008080808aaaaaaaa080808088888888803030303fcfcfcfc03000300ff00ff0002020202aaaaaaaa00ffffffffffff0000ffffff00ff000000ffffff0000000000ffff00ffffff0000ffff00ff00ff0000ff00ffff00ff0000ff00ff00ff000000ff00ff00aa00aa00ff00ff0000000000ff00aa00ff00aa00ff0000ffffff0000ff0000ffff000000ff0000aaffaaaa00ff000000ff00aa00ff000000ff000000aaaaaaaaaaaaaa0000ffffffffff000000ffffffffaaaa0000ffffffff00000000ffffff00ff000000ffff0000ffaa0000ffff0000ff000000ffff0000f0f00000ffff0000cccc0000ffff0000aaaa0000ffff000000000000ffee0000ffee0000ffcc0000ffcc0000ffaaffaaffaa0000ffaa0000ffaa)) else (if page < 4 then 0x8b888b888b888b888a8aaaaaaaaaaaaa8a8a8a8ababababa8a8a8a8aaaaaaaaa8a8a8a8aaa8aaa8a8a8a8a8a8a8aaaaa8a8a8a8a8a8a8a8a8a8a8a888a8a8a888a888a88aaaaaaaa8a888a88aa88aa888a888a888a8a8a8a8a888a888a888a888a8888888a8888888a808a808a808a808a0a8a0a8a0a8a0a8a008a008a008a008888aaaaaaaaaaaa88888888ff88ff8888888888f8f8f8f888888888aaaaaaaa88888888aa88aa8888888888a8a8a8a8888888888a8a8a8a888888888888aaaa8888888888888888888888880000000088888800888888008880888088808880880888088808880888008800ff00ff0088008800aaaaaaaa88008800aa00aa00880088008888888888008800880088008800000088000000828282828a8a8a8a8282828282828282828082808280828080808080aaaaaaaa80808080888888888080808080808080800080008000800077777777000000005f5f5f5f0000000055ff55ff0000000055aa55aa55aa55aa5555ffff0000000055555555aaaaaaaa5555555555550000555555555500550055555555505050505555555544444444555555550000000055445544554455444444444444444444333333333030303033333333000000000fff0fff000000000f0fffffffff00000f0fffff000000000f0ff0f0ffff00000f0ff0f0f0f0f0f00f0f0f0ff0f0f0f00f0f0f0f0f0a0f0a else (if page < 5 then 0xaa88aa88af8caf8caa88aa88aaaaaaaaaa88aa88aaaaaa88aa88aa88aaa8aaa8aa88aa88aa8aaa8aaa88aa88aa88aaaaaa88aa88aa88aa88aa88aa88aa88aa00aa88aa88aa888888aa88aa80aa88aa80aa88aa00aa88aa00aa88a888aa88a888aa88a080aa88a080aa888a88aa888a88aa888888aaaaaaaaaa888888aa88aa88aa888888aa888888aa88888888888888aa80aa80aaaaaaaaaa80aa80aa88aa88aa80aa80aa80aa80aa808080aa808080aa55aa55ff00ff00aa55aa55aaaaaaaaaa44aa44aa44aa44aa22aa22aa22aa22aa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa00ff00ff00ff00aa00aaaaaaaaaaaaaa00aa00ffffaa00aa00aa00ff00ff00aa00aa00ff00aa00aa00aa00eecceeccaa00aa00ee00ee00aa00aa00aaaaaaaaaa00aa00aaaaaa00aa00aa00aa88aa88aa00aa00aa0aaa0aaa00aa00aa00ff00aa00aa00aa00aaaaaa00aa00aa00aa00aa008800aa008800a8a8a8a8fcfcfcfca8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a888a888a888a888a800a800a800a800a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0000000009a9a9a9a9a9a9a9a99999999aaaaaaaa9988998899889988990099009900990098989898989898988f888f888f888f888f008f008f008f008e8e8e8e8e8e8e8e8e8a8e8a8e8a8e8a8e888e888e888e888c8c8c8ccccccccc8c8c8c8c8c8c8c8c8b8a8b8a8b8a8b8a else 0xaaffaaaaaaffaaaaaaffaa00aaffaa00aaff0000aaff0000aaaaffff00000000aaaaffaaffaaffaaaaaaeeeeeeeeeeeeaaaaaaaaffffffaaaaaaaaaaffeeffeeaaaaaaaaffaaffaaaaaaaaaaffaaaaaaaaaaaaaaff00ff00aaaaaaaafefefefeaaaaaaaaeeeeeeeeaaaaaaaaeeaaeeaaaaaaaaaaeaeaeaeaaaaaaaaaccccccccaaaaaaaaafaaafaaaaaaaaaaaeaeaeaeaaaaaaaaaaaaffaaaaaaaaaaaaaaeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa0aaaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88aa88aaaaaaaaaa88888888aaaaaaaa22222222aaaaaaaa0a0a0a0aaaaaaaaa00aa00aaaaaaaaaa0000aaaaaaaaaaaa00000000aaaaaaa8aaaaaaa8aaaaaa8aaaaaaa8aaaaaaa88aaaaaaaaaaaaaa88aaaaaa88aaaaaa88aaaaaa00aaaaaa88aa88aa88aaaaaa80aaaaaa80aaaaaa0aaaaaaa0aaaaaaa00ffffff00aaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aa00aa00aaaa8888aaaa8888aaaa00aaaaaa00aaaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa000000000000aaa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa8a8a8aaa8a8a8aaa0aaa0aaa0aaa0aa8caa8caa8caa8caa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aaa88aa8aaa88aa8a8a8aaa8a8a8aaa88aaaaaaaaaaaaaa88aa88ffccffccaa88aa88bb88bb88))) else (if page < 9 then (if page < 7 then 0xccffccffccccccccccffccccccffccccccfcccfcccfcccfccceecceecceecceeccccccccffeeffeeccccccccffccffccccccccccfcfcfcfccccccccceeeeeeeecccccccccececececccccccccccccccccccccccccccccc00cccccccccc88cc88ccccccccc4c4c4c4ccccccccc0c4c0c4ccccccccc0c0c0c0cccccccc88cc88cccccccccc88888888cccccccc44444444cccccccc00440044cccccccc00000000cccccc88cccccc88cccccc00cccccc00ccccc0c0ccccc0c0cccc8888cccc8888cccc0000cccc0000cccacccacccacccaccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc8ccc8ccc8ccc8ccc88cccccc88cccccc88cc88cccccccccc88cc88cc88cc88cc888888cc888888cc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00cc00ff00ff00cc00cc00cccccccccc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0bfaabfaabfaabfaabbaabbaabbaabbaabb8abb8abb8abb8abb88bb88bb88bb88bb00bb00bb00bb00babababababababab0b0b0b0b0b0b0b0afafafaf00000000afafafaaafafafaaafafaf00afafaf00afaeafaeafaeafaeafaaafaaffaaffaaafaaafaaafaaafaaafaaaaaaafaaaaaaafa0afa0afa0afa0af8caf8caf8caf8caeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaae0cae0cae0cae0cae00ae00ae00ae00acacacacacacacacabaaabaaabaaabaaaaffaaff00000000 else (if page < 8 then 0xf0f2f0f2f0f2f0f2f0f0f0f0fafafafaf0f0f0f0f5f0f5f0f0f0f0f0f3f2f3f2f0f0f0f0f3f0f3f0f0f0f0f0f2f2f2f2f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f050505050f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0c0c0f0f0c0c0f0e0f0e0f0e0f0e0f0d0f0d0f0d0f0d0f0c0f0c0f0f0f0f0f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f080f080f080f080f000f000f000f000efeeefeeefeeefeeefaaefaaefaaefaaeeeeeeeeffeeffeeeeeeeeeefefefefeeeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000eeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceeaeeeaeeeaeeeaeeeaaeeaaffaaffaaeeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaee88ee88ee88ee88ee66ee66ee66ee66ee22ee22ee22ee22ee0eee0eee0eee0eee00ee00ff00ff00ee00ee00eeeeeeeeee00ee00ee00ee00ee00aa00ee00aa00ececececececececeaeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeac0eac0eac0eac0eaaaeaaaeaaaeaaae6e6e6e6e6e6e6e6e0e0e0e0e0e0e0e0dddddddd00000000dcfcdcfcdcfcdcfcdcdcdcdcdcdcdcdccfcccfcccfcccfcccf00cf00cf00cf00cecececececececececcceccceccceccce8ace8ace8ace8ace00ce00ce00ce00 else 0xff00ee22ff00ee22ff00ee00ff00ee00ff00cf00ff00cf00ff00cc00ff00cc00ff00aaaaff00ff00ff00aaaaff00aa00ff00aa00ffffaa00ff00aa00ff00aa00ff00aa00aa00aa00ff008a00ff008a00ff008800ff008800ff000f00ff000f00ff000000ffffff00ff000000ffff0000ff000000ffaa0000ff000000ff00ff00ff000000ff00aa00ff000000ff000000ff000000aa00aa00ff00000000ff0000ff0000000000ff00ff0000000000aa00ff00000000000000fefefefefefefefefefe0000fefe0000fefafefafefafefafef0fef0fef0fef0feeefeeefeeefeeefeaafeaafeaafeaafe00fe00ff00ff00fe00fe00fe00fe00fe00fa00fe00fa00fe00f000fe00f000fe00ee00fe00ee00fe00aa00fe00aa00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc30fc30fc30fc30fc00fc00fc00fc00fafafafafafafafafaf8faf8faf8faf8f8f8f8f8f8f8f8f8f6f6f6f6f6f6f6f6f6f2f6f2f6f2f6f2f6f0f6f0f6f0f6f0f5f5f5f500000000f4f4f4f4f4f4f4f4f4f0f4f0f4f0f4f0f3f0f3f0f3f0f3f0f300f300f300f300f2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f2f0f2f0f2f0f2f0f1f0f1f0f1f0f1f0f100f100f100f100f0f5f0f5f0f0f0f0f0f5f0f0f0f5f0f0f0f4f0f4f0f4f0f4f0f3f0f3f0f0f0f0f0f3f0f0f0f3f0f0)) else (if page < 10 then 0xffccffccffccffccffccffcc00000000ffccccccffccccccffcc0000ffff0000ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc00000ffc00000ffaf0000ffaf0000ffaaffaaffffffaaffaaffaaffeeffeeffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaaaaaffaaaaaaffaa0000ffff0000ffaa0000ffaa0000ffaa0000aaaa0000ffa8ffa8ffa8ffa8ff8aff8aff8aff8aff88ff88ffaaffaaff88ff88ff88ff88ff888888ff888888ff880000ff880000ff80ff80ff80ff80ff55ff5500000000ff30ff30ff30ff30ff0fff0f00000000ff0aff0aff0aff0aff00ffffffffff00ff00ffffff00ff00ff00ffffff000000ff00ffff00000000ff00ffaaff00ffaaff00ffaaff00ff00ff00ffaa00000000ff00ff00ffffff00ff00ff00ffccffccff00ff00ffaaffaaff00ff00ffaaff00ff00ff00ff0aff0aff00ff00ff00ff00ff00ff00ff000000ff00ff00f500f500ff00ff00f000f000ff00ff00ee00ee00ff00ff00dd00dd00ff00ff00cc00cc00ff00ff00aaaaaaaaff00ff00aa00ff00ff00ff00aa00aa00ff00ff0088008800ff00ff005500ff00ff00ff0055005500ff00ff000f000f00ff00ff0000aa00aaff00ff000000ff00ff00ff000000cc00ff00ff000000aa00ff00ff0000000000ff00f000ff00f000 else (if page < 11 then 0xffffffff00000808ffffffff00000300ffffffff00000202ffffffff0000000affffffff00000000ffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffff00ffffff00ffffff0000000000fffff0f0fffff0f0fffff0f000000000ffffccccffffccccffffaaaaffffaaaaffffaaaaffff0000ffffaaaa00000000ffffaa88ffffaa88ffff00ffffffff00ffff00ffffff0000ffff00ff00ff0000ffff00ff00000000ffff00aaffff00aaffff00aaffff0000ffff0055ffff0000ffff0044ffff0044ffff0033ffff0000ffff000affff000affff0000ffffffaaffff0000ffffff00ffff0000ffffaaaaffff0000ffffaa00ffff0000ffff5500ffff0000ffff2222ffff0000ffff0f0affff0000ffff0f00ffff0000ffff0a0affff0000ffff0000ffff0000ffcc0000ffff0000ffaaff00ffff0000ffaa0000ffff0000f0f00000ffff0000ccdd0000ffff0000cccc0000ffff0000aaff0000ffff0000aaaa0000ffff000055ff0000ffff000055550000ffff00000fff0000ffff000000ff0000ffff000000550000ffff00000000aaaaffff000000000000fffefffefffefffefffcfffcfffcfffcfffc0000fffc0000fff0fff0fff0fff0fff00000fff00000ffeeffeeffeeffeeffeeffaaffeeffaaffeeeeeeffeeeeeeffee0000ffee0000ffeaffeaffeaffeaffdd0000ffdd0000ffcf0000ffcf0000 else 0xffffffffffffff00ffffffffffff0000ffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffff0f0f0f0ffffffffeeeeeeeeffffffffccccccccffffffffaaaaffaaffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffff88888888ffffffff80008000ffffffff0f0f0000ffffffff0f000f00ffffffff0a0a0a0affffffff01000100ffffffff00ffff00ffffffff00ff0000ffffffff00aa00aaffffffff00550000ffffffff00440044ffffffff00330000ffffffff00300030ffffffff00220022ffffffff000a0a0affffffff000a000affffffff0000ff0affffffff0000ff00ffffffff0000ee00ffffffff0000ccccffffffff0000af00ffffffff0000aaaaffffffff0000aa0affffffff0000aa00ffffffff00008800ffffffff00003f00ffffffff00003030ffffffff00002a2affffffff00000f0affffffff00000f00ffffffff00000e0effffffff00000a0affffffff00000a00)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xaee9b874d7aee9b878d7aee9b888d7a6e2135c30aee27884d7aee9b884d7 else 0
  | 4 => if page < 1 then 0x8c1f96d9680dabba6e53834f48c1f96d96b0e2bb8c9f9668f9aee9b885f93e6bba6e53830f9aee2e7e5d939ebba6e5386cdcaee9b94e1039ebba6e1d7e4e7aee9b881f939e537e5b65a07d8b9f96d9680dabba6e21438e7aee2e7e5e139ebba6e1e7e4e7aee9b94e1c36a2e7e5b65ac328a9f96d96b01abb8c9f9744e7aee9b87df939ebba6e227e4e7a6e217e4e70c2bb89e217e4e794df96d9682362e7e5b65a055aee9b94df940ebba6e21724e7aee657e5d139ebba6deb744e7aee9b94e0f39e537e5b65ac79aee9b94df9412537e5b65a0788b9f96d9680c6bba6e2139cd78b9f96d96b276bba6e5388cd7aee9b8551635ebba6e53890d7aee9b885e535eb77e5b65ac9daee9b8856b35e537e5b65ac9d8a5f96d96b0069b94e2835c30aee9b94e2135ebba6e28884d7002bba6e2135eec7e5b65ac9d8a5f96d96b276bba6e53870dbaee9b885f939ebba6e21824e7aee9b94e0d3e6bba6e538a0d7aee9b94df9416bba6e53844e7 else 0
  | 5 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xaee9b94e28794d7aee9b94e285acd7002bba6e538a0d7aee297e5b65ac55bae297e5b65ac08aeeb77e5b65ac9aaee297e5b65ac9aa6e537e5b65ac3daee9b94df96d92eaee9b94df96d92bb7e9b94df96d96baee9b94df96d8adbae297e5b65ac78bae2e7e5b65ac36a6e5e7e5b65ac36aee9b94df9794f9a6e447e5b65ac22aee9b94df9668f9aee9b94e1c7e4f9aee9b94df970cf9aee9b94df96d96ba6e537e5b65ac49b069b94df96d96baee9b94df96d93eb0e9b94df96d96baee9b94df96d945b269b94df96d96baee9b94df96d8fcaee2e7e5b65ac7daee327e5b65ac36a6e5c7e5b65ac36bae297e5b65ac36aee9b94df9754e7a6e537e5b65ac8baee9b94df9744e7aee2e7e5b65ac55bae537e5b65ac78aee9b94e1c5acd7bae537e5b65ac8ba32537e5b65ac8baee9b94e287e4e7aee9b94e1c824e7aee537e5b65ac7daee587e5b65ac78aee9b94e09794e7a8e417e5b65ac22aee9b94e0d458e7aee9b94e28824e7b662e7e5b65ac36aee587e5b65ac7daee9b94dc65acd7ab6537e5b65ac36ab6417e5b65ac36aee9b94de5644e7aee9b94e0d5ace7aee9b94df9618e7aee9b94df9794e7b3e9b94df96d96baee9b94df96d8f9a32537e5b657c22a32537e5b65ac06aee9b94df9768e7aee9b94e0c5ace7aee9b94df96d939 else (if page < 2 then 0xa6e447e5b65ac17a6e537e5b65acb2a6e497e5b65ac17a6e537e5b65ac3fa6e537e5b65ac37aee9b94df96d8f3a32537e5b65ac04a32537e5b65acc5aee657e5b65acdeaee9b94db65acc2aee327e5b65acdeaee9b94df96d92faee9b94df9760e7b229b94df96d96baee9b94df96d8feaee2e7e5b65ac0bba22e7e5b65ac55a6e537e5b65ac4eaee9b94df96d958aee9b94df96d94b8b9f96d96b26c55aee9b94df9414e794df96d96b26c55aee9b94df95ad05addf96d96b26c55aedf96d96b26c55bae527e5b65ac7894df96d96b59c78aee9b94df979505ab2537e5b65ac78002bba6e537e505bae537e5b65ac7794df96d96b1e006a6e537e5b65ac7bac6537e5b65ac78bb2537e5b65ac78ab6537e5b65ac78aee9b94df9404f9b169b94df96d96baee9b94df96d931bb22e7e5b65ac31aee9b94df9728e7aee9b94e1c43ce7aee327e5b65ac78ab6537e5b65ac31aee537e5b65ac7caee9b94df973cf9a6e537e5b65ac43afe9b94df96d96baee9b94df96d942aee297e5b65ac7daee417e5b65ac9aaee9b94e2839cd7aee2e7e5b65ac9aaee9b94e1c734d7aee9b7e5b65ac99bae2e7e5b65ac78aee9b94e175acd7aee9b94e14794d7aee537e5b65ac9a94e297e5b65ac06aee9b94e155acd7ade297e5b65ac22aee9b94e1c458d7 else 0xaee2e7e5b65ac01a6e538a1f939c30aee9b94e217e4e7aee9b8a2217e4e7002bba6e217e4e7bb2537e5b65ac8da32537e5b65ac8daee9b94df9795088b9f96d96b154228b9f96d96b57855bb22e7e5b65ac55aee337e5b65ac55aee9b94e057e4e7aee2e7e5b65ac21aee9b94e28724e7aee9b94e11794e7aee9b94e1c660dbbae5f7e5b65ac8baee9b94e1c5acdbbae2b7e5b65ac8b002bba6e53870dbaee9b94e117e4e7a325f7e5b65ac8b002bba6e53844e7a322b7e5b65ac8baee9b94df9424e7aee657e5b6458e7a6e537e5e539c3faee9b8d5f9794e7ade2e7e5b65ac43aee9b94deb794e7aee9b94df975ce7aee9b99df9744e7a6e537e5b65ac4faee9b94df96d957aee9b94df96d95aa6e537e5b65ac56aee9b94df96d94994df96d96b1fc3f996537e5b65ac3faee9b94ded6d92fa6e536d96b2d43fa6e537e59f5ac43a6e537adb65ac3faee7994df96d92ba6e537e5b64e43faee9b8f1f96d92fa6e387e5b65ac43aee9b94df96912baee9b94df968139a6e377e5b65ac22a6e4a7e5b65ac22a6e497e5b65ac22aee6b7e5b65ad16aee6c7e5b65ad16aee657e5b65ad16a32537e5b659c6ca32537e5b65ac6baee9b94df96d8f4b1e9b94df96d96baee9b94df96d943b4a9b94df96d96baee9b94df96d92daee9b94df9758e7)) else (if page < 4 then 0xa6e417e5b65ac5abae307e5b65ac36aee9b94db6644f9a32537e5b65ac1daee9b94df9614e7aee417e5b65ac7db6a9b94df96d96baee9b94df96d8dbaee9b94df95ad0aaee9b885f95ace7a6e537e5b65ac8da6e537e5e539c49aee9b8e1f9794e7ade2e7e5b65ac49aee9b94dec794e7a6e417e5b659822ba62e7e5b65ac55bae537e5b65ac7dbb22e7e5b65ac36aee9b94e28438e7aee9b94e1c6d8dbaee9b94e115ace7a6e5f7e5b65ac8ba6e2b7e5b65ac8ba32537e5b65ac07aee9b94df9784e7b3e9b94df9794e7aee9b8c1f9794e7aee9b94df979ce7aee9b94df9748e7aeeb78b9f9794e7a6e53871985ac49aee9b901f9794e7a32537e5b65ac09aee9b94df977ce7bae537e5b65ac81aee9b94df9794e4aee9b94df979507aee9b94df9794d8aee9b94df9798e7aee9b94df9750e7aee9b94e247e4e7aee9b94df939cafa6e537e5e539c51aee9b8f9f9794e7ade2e7e5b65ac57aee9b94df1794e7bae537e5b65ac8caee9b94df97950aaee9b94df9428e7a36537e5b65ac06aee9b94e067e4e7aee9b94df974ce7a6e537e5e339c36aee2e7e5b654ce7a6e53865985ac22aee9b7e5ea744e7aee9b94d985ac9faee2e7e5b65ace5a32537e5b659c06aee9b94e257e4e7a6e537e5e539c30aee9b885f9794e7bae537e5b65ac8d else (if page < 5 then 0xaee9b94e096d8ecaee327e5b65ac1ca6e5c7e5b65ac1ca6e537e5b65ac6ea6e5a7e5b65ac36aee9b94df9708f4aa6537e5b65ac36aee9b94e1a7e4fcaee9b94df9790ecaee9b94e086d8ecb029b94df96d96baee9b94df96d946aee9b94df9788e7aee9b94df976ce7a6e537e5b65ac3eaee9b94df96d92aaee9b94df9780e7aee9b94df9774e7aee9b94df961ce7a6e537e5b65ac35aee9b94df96d8f2a32537e5b65ac3894e2e7e5b65ac38a6e457e5b65ac22a86417e5b65ac2294e2e7e5b65ac35a6e2d7e5b65ac22aee9b94df9770e7aee327e5b6458e7aee2e7e5a7458e7aee9b94df9764e7aee537e5b65ac7aa6e537e5b65ac70a32537e5b65ac0faee9b94df9740e7aee2e7e5b65ac47ac6537e5b65ac70a32537e5b65ac70aee9b94df95acffaee9b94e237e4e7aee9b94e1482ce7aee9b855f9458e7aee9b94e267e4e7aee9b886147e4e7ade537e5b65ac8dba6537e5b65ac7d94df96d96b1f42294df96d96b5787dbb2537e5b65ac7daae537e5b65ac7d94df96d96b27036aedf96d96b27036a6df96d96b27036badf96d96b270368b9f96d96b270368b9f96d96b59c36a6e5d7e5b65ac36ac62e7e5b65ac368b9f96d96b0d806b8a2e7e5b65ac36aee9b94df9610e7a6e537e5b65ac5aaee9b94df960ce7a6e5e7e5b65ac5a else 0xaee9b94e0d7e4f9a8e5c7e5b65ac36002bba6e53834f9a3e5c7e5b65ac36aee9b94df9718f9aee327e5b65ac08aee9b94e096d912aee9b94df96d90caee9b94e096d8f9a8e537e5b65ac49a3e537e5b65ac49a6e537e5b65ac57a6e537e5b65ac4baee9b94df96d93da6e537e5b65ac51b429b94df96d96baee9b94df96d8f5aee9b94df96f939aee9b94df96e8f9a6e447e5b657c22aee307e5b65ac06aee9b94df964cf9aee9b94e0a7e4f9aee9b94df96811caee9b94df966cf9a6e537e5b65ac38b329b94df96d96baee9b94df96d8fbaeea394dfb6d96bb1a9b94df96d8f9aeead94df96d93eaee9b8f5f96d8f9aee9b94df96851caee9b94df96e4f9aee9b94e096d939aee9b94dee6d8f9a6e7294df96d91caee9b94df96d927b46a594df96d96baee9b94df96fd3eaee9b94e016d93eaee9b94def6d93eaf29b94df96d96baee9b94df96d94cafa9b94df96d96baee9b94df96d95caee9f94dfa6d96baeea694df96d93eb529b94df96d945aee7c94df96d93eaee9b94df96f545a6e4b7e5b65ac22aee6d7e5b65ad16af69b94df96d96baee9b94df96d95bb4e9b94df96d939aee8194df96d939aee9b94df96f139aee9b94dff6d939aee9b94df06d939aee9b94df96d8fdaee9b8edf96d96baee9b94df96d928aee9b94e177e4f9))) else (if page < 9 then (if page < 7 then 0xaee9b94df9618f9a6e537e5b63e449aee9b8e1f96d8f9aee9b94dec6d8f9a6e447e5b65ac49aee9b94df96e0f9aee9b94df9778f9a3e537e5b65ac06aee9b94df9744f9bae537e5b65ac7caae537e5b65ac7ca6e537e5b65ac41aee9b94df96d930aee9b94e0d5acf9a3e5e7e5b65ac36a6e307e5b65ac8bab2537e5b65ac36aee307e5b65ac8baee447e5b65ac7db66297e5b65ac36aee9b94e167e4f9b66a394df96d96ba6e447e5b65ac2caee9b94df96a8f9b3e9b94df96d8f9aee9b8c1f96d8f9a6e537e5995ac49aee9b901f96d8f9aee9b94df9690f9aee9b94df9674f9aee9b94df9404a8a6e537e56b40449aee9b8f1f96d8f994e327e5b65ac49a6e537e5b65ac69aee9b94e0b7e4f9aee9b94df9654f9aee9b94df9670f9a6e537e5ac3e436a6e447e5b65aca8a6e447e5b657822aee9b94e187e4f9aee9b94df9704f9aee9b94e157e4f9ba6327e5b65ac36aee9b94df9414f9aee337e5b65ac36aee2c7e5b65ac36a6e537e5b63e441aee9b8d9f96d8f9a6e307e5b65ac49aee9b94deb6d8f9a6e447e5b65ac24aee9b94df9680f9aee9b94df96dcf9aee9b94df9678f9aee9b94df9708f9aee9b94db6644a8aee9b94e1c3e4d7a3e537e5b65ac1daee9b94df9700f9aee9b94e287e4f9aee307e5b65ac55aee9b94e0d6d8f9 else (if page < 8 then 0xa6e537e5b65a055b0a9b94df96d96baee9b94df96d93aaee9b885f96d912a6e537e5b65ac5ba6e537e5b65ac42aee9b94df96d937a6e4a7e5b65ac2ca6e537d9b65ac2caee9b855f96d939aee9b94df96a939a6e537e5b659849aee9b94e1c7e4f4a6e537e5b65ac7eaee9994df96d96baee317e5b65ac36a6df96d96b24036aee9b94df95ad0094df96d96b1d8368c5f96d96b0d822a6e597e5b65ac36a6df96d96b24436b3a9b94df96d96baee9b94df96d8faa6e537e5b65a036a6e537e5b65ac30aee9b94df96d968aee9b94df970d39a6e537e5b661849aee9b961f96d939aee9b94df970ceca8e537e5b65a036b3e537e5b65ac7daee587e5b65ac8ba6e587e5b65ac8bbb2307e5b65ac36ab6537e5b65ac55a6e53825b65ac30b3e9b94df96d968b66ad94df96d96ba8e5e7e5b65ac36aba537e5b65ac36aee9b94df961905a8e537e5b65ac57aee9b94df971939a6e5e7e5b65ac49aee9b94df970d45a6e537e5b66184baee9b961f96d93db66a294df96d96baee9b94df970cfcaee9b8e9f96d96bab6537e5b65ac49a6e53835b65ac49b669b94df96d939b66aa94df96d96baee9b94e0d6d939a6e53825b65ac49b3e9b94df96d939b3e9b94e096d96baee9b94df9658f9aee9b94df9768f9aee9b8e5f96d96baae537e5b65ac55 else 0xa6e537e5b65ac4aaee9b94df96d944a6e537e5b65ac4caee9b94df96d93caee9b94df96f539aee6c7e5b65ad20b2a9b94df96d96baee9b94df96d8f7aee6d7e5b65ad20a6e727e5b65ad20aee9b7e5b65ad29aee9b94df969cf4aee9b94df9668f49b1f96d96b458499ca6c7e5b65ad16a6e537e5a045849aee6c7e5a05ad16aee9b7b1a05ad16a6df96d96b34849aee9b94db6594c1a6e537e5b634849a6e537e5b6594c1a6e537e5b65ac50aee9b94df96d94aa6e537e5b65ac3baee9b94df96d8f6aee9b94df9408a8aee537e5b65acc3a6e537e5b65acc1a6e4a7e5b657822aee9b94df9794e9aee9b94df9794f4a6e537e5b65ac2faee9b94df96d959a6e537e5b65ac58aee9b94df96d95d94df96d96b20c51a0e537e5b65ac51aee9b94df36d95aa6e536d96b2e451a6e537e5ab5ac57a6e537c5b65ac51aee8994df96d94b94df96d96b22449a62537e5b65ac49a6e536d96b30049a6e537e5b45ac49aee2f7e5b65ac06a6e4f7e5b65ac2ca6e537e1b65ac2ca6e537e5b65ac39aee9b94df96d8f8aee9b855f96d94baee9b94df96ad53a6e537e5b65aca0a6e537e5b65ac2eaee9b94df96d938a6e537e5b65ac52aee9b94df96d96ab6e9b94df96d96baee9b94df96d96994df96d96b1d030a6e217e5b65ac30aee9b94df96d568)) else (if page < 10 then 0xaee9794df96d939a6e537e5b15ac49aee9b901f96d939a56537e5b65ac49aee9b94df96a539a6e537e5b65ac62aee9b94df96d933a6e537e5b654448aee9b901f96d934a6e537e5b658c3faee9b8e1f96d939a6e3c7e5b65ac46aee9b94df96a536a6e4d7e5b65ac2baee9b94df96a139aee9b94df971d39aee9b94df970939aee9b94df9780e4aee9b94e076d939aee9b94df76d8fc94df96d96b20849aee9b94df96d9409ee537e5b65ac49aee9b94df26d939a6e537e5b65ac5da6e536d96b2e049a6e537e5a85ac49aee9b94df96d947a6e537e5a45ac49aee8794df96d939a6e537e5b65ac6094df96d96b21449a4e537e5b65ac49a6e536d96b2f849a6e537e5af5ac49a6e537e5b64e449aee9b8f1f96d939a6e387e5b65ac49aee9b94df969139a6e4a7e5b65ac4994df96d96b20049a6e536d96b2d849a6e537e5a05ac49aee7b94df96d9399b2537e5b65ac49aee9b94dee6d939929f96d96b21422a4e4a7e5b65ac22a6e4a6d96b2f822a6e4a7e5af5ac22a6e537d9af5ac2294df96d96b20038a92537e5b65ac38a3e537e5b65ac3894e317e5b65ac49a6e437e5b65ac22a6e537e5b65ac40aee9b94df96d932a6e537e5b65ac44aee9b94df96d92ca6e427e5b65ac22aee317e5b65ac1caee9b94df96d90bb62a994df96d96b else (if page < 11 then 0xaee9b94df96d93b94df96d96b21849a6e536d96b2ec49a6e536d96b2fc49aee9b94df96d93fa6e537e5b65ac4594df96d96b21438a3a537e5b65ac09a6e557e5b65ac49a7a537e5b65ac49a5a537e5b65ac49a6e547e5b65ac49a6e537f1b65ac49a6e537e5b25ac49a6e537e5b65bc49a6e537f5b65ac49a6e537e5b05ac49a82537e5b65ac49a52537e5b65ac49a9e537e5b65ac49a6e5380db65ac49a6e53811b65ac49a6e537e5a15ac49a6e537e5a25ac499e2537e5b65ac49aa2537e5b65ac49a6e53809b65ac49a6e537e5a35ac499b6537e5b65ac49a6e537e5b64e451aee8394df96d939a6e387e5b65ac57aee9b94df16d939a6e537e5b65ac63a6e537e5a05ac57aee9a94df96d9399b2537e5b65ac51aee9b94df36d939a6e537e5b65ac5eaee9b94e006d939aee9b94def6d939aee9b8fdf96d96bb569b94df96d939aee7c94df96d93994df96816b20049a6e537b1b65ac51aee8994df96d939a6e537e5b65ac61a6e536816b2d8499b2537e5a05ac49b529b94df96d939aee8094df96d939aee9b94df96996ba6e537b1a05ac49aee7b94dee6d939a6e537e5b654449a6e537e5b658c49a6e3c7e5b65ac49a6e4d7e5b65ac49a6e537e5b65ac46aee9b94df96d936a6e537e5b65ac48aee9b94df96d934a6e537e5a95ac49 else 0xa6e536d96b2f049a6e537e5ab5ac4994df96d96b20c49a0e537e5b65ac49a6e536d96b2e449a6e537e5a55ac4994db65acb620049a6e537e5b633049b129b94df96d96b)))) else 0
  | 6 => if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0xaee9b94df9735b65aee8a6e537e5b65ac31aee9b911f96d96b0c6bba6e537e5b65d96baee9b94df96d96b48abba6e537e5b65ac0caee9b94df96d96b06ebba6e538716b39cd7aee9b94df9794e735ebba6e53849b65acd7aee9b8b9f96d96b1e29b94e297e5b65ac22aee9b94df96d91635ebba6e53851b65acd7002bba6e538716b35ebba6e6494df96d96baee9b94df96d96b23abba6e537e5b65ac15aee9b94df96d96b35abba6e537e5b65ac78aee9b8a5f96d96b1e2bba6e53825b65ace7aee9b94db66456b39eeba6e537e5b65ac36a6e537e5b65ac840dabba6e2e7e5b65ac36a6e537e5b65ac3608a9b94df96d96b57836aee9b94df9795b65aee9a6e537e5b65ac36aee9b94df96d9865aebba8e537e5b65ac36002cfa6e537e5b65aebba6e537e5b65acf9aee8f94df96d96b0d800aee9b94df96d8f9aee9b94df96d96b022bba6e537e5b65ac31aee9b905f96d96b0dabba6e537e5b65dd6baee9b94df96d96b472bba6e537e5b65ac0eaee9b94df96d96b072eba6e417e5b65ac36a6e417e5b65ac840da9b94df96d96b25436a6e417e5b65ac950dabba6df96d96b24836aee9b8a5f96d96b0da9b905f96d96b0d822a6e417e5b65ad5e0dabba6e537e5e55ace7ba69b905f96d96b0d800aee9b94df9794e7aee9b94e0d7e56b39ebba8e417e5b65ac36002bba6e538356b39ebba3e417e5b65ac36aee9b8b9f96d96b022bba6e537e5b65ace7aee9b94df96d96b0d800aee9b94df96d96baee9b94df964d6b39ebba6e417e5b65ac1c else (if page < 2 then 0xaee9b94df96d96b37a9b94df96d96b0d817a6e53905f96d96b05ebba6e537e56b31c17aee9b94df96d95e05ebba6e6794df96d96bb829b94df96d96b05ebba6e537e5b66296baee9b94df96d96b3bebba6e537e5b65ac04aee9b94df96d9715aebba6e537e5b65ad23aee9b94df96d96b482bba6e537e5b658817aee9b94df9794e737abba6e677e5b65acdeaee9b94df96d90e2a2bba6e537e5b65ac17a6e537e5b65ace60dabba6e2e7e5b65acdeaee9b94df9761b65aebba6e537e5b65acacaee9b94df96d96b05abba6e537e5b65acddaee9b94df96d96b1b2bba6e537e5b65346caee9b94df972db65aebba6e537e5b65acb4aee9b94df96d96b2a2bba6e537e5b6434a8ba29b8b9f96d96b0dabba6e53849f9794e7aee9ba0a537e5b65aebba6e537e5b65ac0aaee9b94df96d96b0a6bba6e537e5b65ad52aee9b94df96d96b44ae8a6e537e5b65ac36aee9b94df973d6b39eeba32537e5b65ac78a6e2e7e5b65ac9b0dabba6e53871f95ace7aee9b94df96d8f939eeba6e537e5b65ac78002eb94df96d96b1e29b94df96d96b26c36aee9b7e5b65ac9b0da9b94df96d96b1e022aee537e5b65ad4e1e2e9a6e537e5b65ac78aee8f94df96d96b1e2bba6e537e5b65ed6baee9b94df96d96b41abba6e537e5b65ac13aee9b94df96d96b19aeb94e2e7e5b65ac31aeeb78b9f96d96b0c69b94df96d96b26c31aee9b94df96d90f39ebba6e537e5b65acd7ba69b94df96d96b0c69b94df96d96b21031a6e537e5b65ac3108a9b94df96d96b57831 else 0xaeeb78b9f96d96b39ebba6e8894df9794e7aeeb78b9f96d96b08abba6e53871985ac22aee9b94df97a9e539ebba6e8694df9794e7bae8c94df96d96b01800a32537e5b65ac06aee9b94df9794e70b2bba6e537e5e5744e7002bba6e537e5d139ebba6e538a1f9794e7002bba6e538a1f939eeba32537e5b65ac08aeeb78b9f96d96b15400aee2e7e5b65ac55aee9b94df9795c939eeba32537e5b65ac8b002eb94df96d96b22c00a32537e5b65ac8ba6e537e5b65ace70febba6e357e5b65ace7a6e538b9f96d96b10ebba6e537adb65ace7aee9b94df96d93939ebba6e677e5b6458e7aee9b99e537e5e539ebba6e8494df96d96baee9b94df96d96b0fe9b99e537e5b65ac3f0029b94df96d96b0febba6e537e5b65ad2faee9b9f6537e5b64bc00aee9b94df96d92fa6e6e94df96d96b10ebba6e537e5b65ac430029b94df96d96b10ebba6e7a94df96d92baee9b94df96d96b4ac00aee9b94df96d92baee9b99e537e5b64e6bba6e537e5b65ad39002bba6e537e5b64e69b9ce537e5b65ac22b829b94df96d96b08abba6e6e7e5b65ad16aee9b99df96d96b45aeba32537e5b65ac6caee8c94df96d94e1b29b94e417e5b65ac22a6e537e5b65acd408abba6e537e5b65386caee9b9d6537e5b65aebba6e537e5b65acecaee9b94df96d96b08abba6e537e5b665d6baee9b94df96d96b366bba6e537e5b65e96baee9b94df96d96b38abba6e537e5b65ac14aee9b94df96d96b192bba6e537e5e539c17a6e537e5b65acd505ebba6e537e5b6498e7)) else (if page < 5 then (if page < 4 then 0xa6e417e5b66696b08abba6e537e5a7458e7a6e417e5b65ad1608abba6e537e59a458e7a6e53905f96d96b2a29b94e417e5b657822aee9b94e187e56b39ebba6e537e5da5ace7aee9b94df97791639c00aee9b94df9768e7aee9b94df46d90e2a2bba6e537e5b64e516aee9b94df96d96b1f6bb94e2e7e5b65ac06aee9b94e157e56b39eb7a6e417e5b65ac22aee9b94e1c7e51639ebba6e538a2147e4e7aee9b905f96d96b156ebaee2e7e5b65ac08aee9b94e1c851f939ebbade537e5b65ac7daee8c94df96d96b1f400aee537e5b65ac7daee9b94df97196b39ebba6e537e5b66096bbae538b9f96d96b0dabba6e537e5c35ace7baebb8b9f96d96b0daeba6e2e7e5b65ac36002eb8b9f96d96b0da9b8b9f96d96b21036aee2e7e5b65ac530da9b8b9f96d96b0d822a6e2e7e5b65ad5e0da9b905f96d96b1d422aee2e7e5b65ad4e0dae9a6e2e7e5b65ac36aee9b94df96196b39ebba8e2e7e5b65ac36002bba6e537e58639ebba3e2e7e5b65ac36aee9b8c1f96d96b0dabba6e53829f95ace7aee9b8b9f96d96b072bba6e538716b438e7aee9b94df96d96b22e9ba32537e5b65ac06aee9b94df97456b39ebba6e538a1f95ace7aee538b9f96d96b156bba6e7594df9794e7ba69b905f96d96b08abba6e537e5e539c22aee9b94df97951639ebba6e53851f9794e7bae8c94df96d96b0dabbade2e7e5b65ac36aee9b94e146d90e39eeba6e537e5b65ac8ba6e8c94df96d96b22c00a6e537e5b65ac8baeeb7a6e537e5e539ebba6e537e5e539c36 else 0xaee9b7e5b65ac95072bba6df96d96b23c1caee9b94df9769b65aee1a6e537e5b65ac1caee9b94df96d9855aebba86537e5b65ac1c002c9a6e537e5b65aebba6e537e5b65acfcaee9294df96d96b07000aee9b94df96d8fcaee9b94df96d96b016bba6e477e5b65ac1caee9b94df96d9725aebba6e537e5b65ad25aee9b94df96d96b036bba6e537e5b65801ca6e53905f96d96b0b2bba6e537e5b654ce7aee9b94df96d96b1cebba6e537e5b65ace5b3e9b94df96d96b39ebba6e307e5b65ace7aee9b94df96e96b39ebba6e537e5b6470e7aee9b94df96d96b3babba6e537e5b65acdfaee9b99a537e5b65ae9b94df96d9985ac49aee9b901f96d96b39e9ba32537e5b65ac49aee9b94df96d94839ebba6e537e5b65ac81aee9b94df96d96b392bba6e537e5b65ad07aee9b94df96d96b362bba6e537e5b95ace7aee9b94df96d92439ebba6e537e5b65acedaee9b94df96d96b38ebba6e5385df95ace7aee9b94df96d8e72a2bba6e537e5cc6d96baee9b94df96d96b2869b94df96d96b39c49aee9b8e1f96d96b39e9b94e2e7e5b65ac49aee9b94dec6d96b39e9b94e417e5b65ac49aee9b94df96d96b1c6bba6e537e5b66256ba32537e5b65ac7208a8c94df96d96b1a822aee9b94e0b7e56b39ebba6e537e5965ace7a32537e5b65ac2201a9b905f96d96b0881caee9b94df96516b39e9b94e4c7e5b65ac22aee9b94df96d92039ebba6e537e5b85ace7aee9b94df96d91639ebba6e537e5de5ace7a6e537e5b6578e70dabba6e2e7e5b6458e7) else (if page < 6 then 0xb9edca6e537e5b65aebba6e537e5b65dc22a6e537e5b65dd6b08abba6df96d97f5ad16b729b94df96d96b08abba6e607e5b65ad16b729b94df96d96b0da9b94df96d9600d822a6e537e5b65ac5301abbab6537e5b65ad1caee9b94df9711b63e69b94df96d96b53c36a6e537e5b65ad1c0da9b94df9721b65ac22aee9b94df96d95045abba6e7594df96d91caee9b94df96d95f08a9b94df96d9905ac36aee9b94df97a1b65aebba6e537e5b65aca2aee9b94df96d96b076bba6e537e5b65acf0aee9b94df96d98b5aebba6e537e5b65ac06aee9b94df96d96b45abba6e537e5db6d96baee9b94df96d96b296bba6e537e5b65ac26a6e53839f96d96b03abba6e537e5c35ac0eaee9b94df96656b03abba6e537edb65ac36aee9b94df96d9640dadda6e537e5b65ac36aee9d94df96d96b0dabba52537e5b65ac36aee9b929f96d96b0dabba6e536d96b2f40eaee9b94df46d96b03adca6e537e5b65ac0eaee9b94df96d96f5aebba72537e5b65ac0e002c1a6e537e5b65aebba6e537e5b65ad3eaee9b945f96d96b03800aee9b94df96d93eaee9b94df96d96b00abba6e537e5b65cd6baee9b94dfe6d96b03abba6e537e5b65b96baee9b94df96dd6b03800b0e9b94df96d96baee9b94df96d96b516bba6e537e5b35ac0e002bba6e537e5b6516bba6e537e5b65ac03aee9b94df96d96503abba8e537e5b65ac1caee8f94df96d96b072bba6e537e5b65dc1cb869b94df96d96b0dabba86537e5b65ac36aee9094df96d96b0dabba6e467e5b65ac36 else 0xaee9b94df970d6b3e6bba6e5c7e5b65ac36b668f94df96d96b0da8f94df96d96b2103694e327e5b65ac950dabb8c9f96d96b25436a6e307e5b65ac840dabba3e297e5b65ac36a3e537e5b65ac3608a8f94df96d96b57836ba68f94df96d96b0dabba6e537e5b6648f9aeeb7a6e537e5b63e6bba6e537e5b63e436aee9ba22537e5b63e6bba6e307e5b65ac22aee9b94df96656b08abba6e537e5ea6d8f9aee9b9fe537e5b63e6bba6e447e5b65ac220029b911f96d96b08abba6e537e56b40422aee9b94df96d99a3e400aee9b94df9668f9aee9b94e1c7e5b63e400aee9b94e1c7e4f9aee538c9f96d96b0d800aee327e5b65ac36aee9b9a6537e5b63e6aba6e537e5b65ac67aee9b94df96d8f9066bba6e537e5b63e4f0aee9b94e147e5b63e6bba6e537e5b63e4d7aee9b94df970db63e400aee9b94df970cf9a6e5c94df96d96b0d800a6e5c7e5b65ac36aee9b8c1f96d96b022bba3e537e5b65ac08b3e9b94df96d96b0dabba6e527e5b65ac36aee9b7e5b65ac8f022cfa6e537e5b65ac08aee9b949f96d96b022bba6e537e5b65b56baee9b94df96d96b552bba8e537e5b65ac31aee9b911f96d96b0da9b94df96d96b12436a6e537e5b65dc3608abba8e537e5b65dd6baee9b98a537e5b63e6bba6e8694df96d96baee9b94df96d96b1269b94df96d9775ac490029b94df96d96b126bba6e7794df96d96baee9b94df96d96b066bba6e537e5b65ac24aee9b94df96d96b47ebba6e537e5e76d96baee9b94df96d96b0eabba6e537e5b65aceb))) else (if page < 11 then (if page < 9 then (if page < 8 then 0xbae537e5b65ac840da9b94df96d96b59836bb29b94df96d96b0daeba8e537e5b65ac36ab69b94df96d96b0dabba6e537e5b65ac25aee9b94df96d96b46ebba6e538a1f96d96baee9b94df96d96b156e3b3e9b94df96d96bb3e9b94df96d96b08abba6e537e5b661822aee9b961f96d96b45aebb3e9b94df96d96baee9b961f96d96b0da9b97a537e5b65ac36bb2a394df96d96b0daa394df96d96b21036ab6537e5b65ac950daa394df96d96b25436a6e5e7e5b65ac840dabba8e307e5b65ac36a8e537e5b65ac3608aa394df96d96b57836ba6a394df96d96b0daecb3e9b94df96d96baeea394df96d96b156e9b3e9b94df96d96baee9b979f96d96b0d800a6e5e7e5b65ac36b3e9b94df96d96b0c6bba6e53825e56d96baeead94df96d96b0d800ab6537e5b65ac36b92cfa6e537e5b65aebba6e537e5b661825b669b94df96d96b076bba6e587e5b65ad1bb669b9d6537e5b65aebba6e53835b65ac22aeea394df96d96b08ad9a6e537e5b65ad16b3e9b9d6537e5b65aebba6e53825b65ac22aeead94df96d96b08acfa6e537e5b65ad16b3e9b94df9795b65aebba6e53825b65ac36bae8f94df96d96b0dad9a6e537e5b65ac36a6e53911f96d96b08abba6e537e59a5acf9aee9b94e1c7e56b3e6bba6e327e5b65ac36aee9b9d6537e5b63e69b972537e5b65ac22aee9b94df96d8f908abba6e537e5b6458f9aae9b94df96d96b0dabba6e537e5e56d8f9aee9b94df97956b3e400aee9b94df9794f9aee9b9a6537e5b65aebba6e537e5b65ac67 else 0x94df96d96b23c840dabba6df96d96b24c36a6e537e5b65ac8a0daeb94df96d96b1d436aee537e5b65ac850dabba4e537e5b65ac36aee9b7e5b65ac960dabba6e536d96b2f836aee9b94df96d9630dabba6e537e5b65acaaaee9b959f96d96b0daa2a6e537e5b65ac36a6e5694df96d96b0da9b959f96d96b0d822a6e477e5b65ac3608a9b94df96d96b58436a6e537e5b65ac4908abba6e537e5b65d56bac69b94df96d96b0da9b9d2537e5b65ac36a6e537e5b65aca80da9b94df96d95e0d822aee9b7e5b65f96b45a9b94df96d9755ac36a6e537e5b65ac540dab0a6e537e5b65ac36aee9b7e5b65ac940dabba6e387e5b65ac36aee9b94db65acba0dabba6e537e5b654436aee9b94df96d9885aebba6e537e5b65ac34b7a9b94df96d96b0da9b94df96d97c5ac36aee9b94df96d96b2a6bba6e537e5b65ac1ea6df96d96b23c3608a9b94df96d96b0d806aee9b96df96d96b0dabba6e347e5b65ac36aee9b94df96d96b1bebba6e537e5b65ac3394df96d96b538840dae2a6e537e5b65ac36a6e537e5b65acc40dabba6e537e5b65ad21aee9b94df96d96b0469b9ca537e5b65ac36aee537e5b65ac800dabb9b2537e5b65ac36aee9b94db65acb60dabba6e537e5b64e436a6e537e5b66016b0da9b94df96d96b31836a6e537e5b65ac360b29b94df978db65ac36aee9b94df96d98e5aebba6e537e5b65ac2aa6e537d1b65aca60dabba6e537e5b65acabaee9b94df96d96b0b2bba6e537e5b65ad53a6e537e5b65ac880dae9a6df96d96b25436) else (if page < 10 then 0xaee9b94df96d8cf01a9b94df96d96b0b422a6e537e5f46d96b0b2e6a6e537e5b65ac2caee9b94df96d98f5aebba6e537e5b65ace8aee9b94df96d96b01ebba6e537e5b65d16baee9b94df96d96b462bbae29b94df96d953a6e53865f96d96b08abba6e537e5b659d16aee9b94e237e5b65aebba6e537e5b65ac9eaee9b94df9789b65aebba6e537e5b65ac9faee9b94df96d96701a9b94df9795b65ac30aeeb7a6e537e5b65a2bba6e8b94df96d96baee9b94df96d96b006bba6e537e5b65ac30a6e538a1f96d96b0c000a6e537e5b65ac30aee9b94df96d96b5a2ecaee9b94df96d968002bba6e537e5b65a2bba6df96d96b25c08a6e537e5b65ac5508a9b94df96d96b57855bb29b94df96d96b156bba6e537e5b65e56baee9b94df96d96b45ebba6e537e5b65ac10aee9b94df96d96b086bba6e538a1f96d912ada9b94df96d96b08abba6e537e5b645912aee9b9aa537e5b65aebba6e537e5b65ac59aee9b94df96d96b06abba6e537e5b65ad10a6e537e5e56d96b126bbade9b94df96d939ade9b94df96d96b126bba6e53871f96d939b8e9b94df96d96b0b2bba6e7594df96d953ba69b94df96d96b126bba6e537e5e56d939aee9b94df96d8ce08abba6e537e5b659822baecba6e537e5b65aebba6e537e5e56d8ecba69b94df96d96b156bba6e537e5e56d912aee9b7e5b65ac970daeba6df96d96b25c36a6e537e5b65ac970daeba6e527e5b65ac36a6e537e5b65ad670dabba6df96d96b26036a6e537e5b65ac980dab794df96d96b21036 else 0xaee9b94df96d96b4d6bba6e537e5b65ac47aee9b94df96d96b446bba6e537e5de6d939b869b94df96d96b08abba6e717e5b65ad16a6e537e5b65acd108abba6e537e5b66316baee9b94df96d96b386bba6e537e5b65ac0faee9b94df96d96b28ebba6e537e5b661d6baee9b94df96d96b3c69b94df96d96b34c1cb269b94df96d96b45abba6e537e5f46d8fcaee9b94df96d95e3b2bba6e537e5de5acdeaee9b94df96d95e2a2e3a6e537e5b65ac22aee9b94df96d95e08a9b94df96d96b32c22a6e537e5b6578cb08abba6e757e5b65ad16b8e9b94df96d95e08abba6df96d97d5ad16aee9b94df9785b65ae9b94e1c7e5b65ac49baebba6e537e5b64e6bba6e537e5b65ac09aee9b94df977db65aeeba6e537e5b65ac49aee9b94e147e5b64e6bba6e537e5e96d96baee9b94df96d96b452e9b2e9b94df96d96baee9b94e147e5b63b2bba6e537e5e66d96baee9b94df96d96b556bba6e53891f96d96baee9b94df96d96b2be9b94df9795b65ac51aeeb7a6e537e5b656ab7a6e537e5b65ac57aee9b94e1c7e5b652ebbaea9b94df96d96baee9b94df96d96b1469ba1a537e5b65ac510029b94df96d96b146bba6e537e5b65ad5aaeeb9a6e537e5b656800aee9b94df96d95aae29b94df96d96b15ebba6e537e5b65ac570029b94df96d96b15ebba6e8a94df96d94baee9b94df96d96b52c00aee9b94df96d94bbaa9b94df96d96b126cba6e537e5b65ac06aee9b94df96d9815aebba6e537e5b65ad13aee9b94df96d96c5aebba6e537e5b65ad56)) else (if page < 13 then (if page < 12 then 0xaee9b94df96d96b196bba6e537e5ce6d96baee9b94df96d96b1a2bba46537e5b65ac06b2e9b94df96d96b08abba6e567e5b65ac1caeea194df96d96b08abba6e487e5b65ac22aee9b9da537e5b65aebba6e537e5b65ac18aee9b94df96d96b08ebba6e537e5b65ad1daee9b94df96d96b0f2bba6e537e5b65aceab9edda6e537e5b65aebba6e537e5b65cc22a6e537e5b65ad2008abba6e757e5b65ad20aee9b94df9775b65aebba6e537e5b65aca7aee9b94df9771b65aebba6e537e5b65aca4aee9b94df96d96b07ebba6e537d5b65ac0eaee9c94df96d96b08abba6e4e7e5b65ac22aee9b94dfa6d96b08abba6e537e5b35ac22aee9b94df96d96308abba6e537e5b85ac17aee9b94df96d96108a9b94df96d9a75ac49aee9b94df96a56b45a9b94df96d9ac5ac49aee9b94df96d95145abba6e537e5b65acb7aee9b94df96d96b456bba6e577e5b65ad16aee9b94df96d9163b2bba6e537e5b65ad1eaee9b94df96d96b382bba6e537e5d96d96ba6e537e5b66696b126bba6e537e5a85ad16a6e537e5b65ad4e126bba6e537e5a45ad16a6e537e5b65ad5e126bba6e537e5b65acb3aee9b94df96d9705aebba6e567e5b65ad16a6e537e5b65ad16126bba6e537e5a05ad16aee9b94df96d96b3069b9d5f96d96b45849aee9b9b1f96d96b45abb9d66c7e5b65ad16002bb9b1f96d96b45a9b9d6537e5b645849aee9b9d5f96816b45ae7a6e537e5b65acc1a6e537e5f46d96b30400a6e537e5b65acc1aee9ba16537e5b65aebba6e537e5b65ac2b else 0xaee9b94df96d96305ebba6e5384df96d939ad29b94df96d96b17ebba6e387e5b65ac34aee9b94df96d948392bba6e4a7e5b65ac1ca6e7f94df96d96b126bbace9b94df96d939aca9b94df96d96b126bba6e8894df96d939b8e9b94df96d96b126bba6e7594df96d939aee537e5b65ac8608abba6e4d7e5b65ac22aee9b94db65acbf08abba6e537e5b15ac22aee9b94df96d8cc08a9b94df96d96b13422a6e7e94df96d96b08abb94df96d96b20822aee9b8f1f96d96b08abba6e536d96b2e022aee9b94df96916b08abba6e537e5b632822aee9b94df96d93908abba6e537e5b65ad41aee9b94df96d96b082bba6e537e5b65acb1aee9b94df96d96b1b6bba6e537e5b634022a6e537e5b65acd008a9b9ca537e5b65ac22aee537e5b65ac8008abba6e387e5b65ac22aee9b94db65acb608abba6e537e5a05ac22aee537e5b65ac8508abba6e4a7e5b65ac22aee9b94db65acbe08abba6e537e5af5ac22a6e7594df96d96b126bba6e7f94df96d939b8e537e5b65ac8508ae3a6e4a7e5b65ac22a6e53929f96d96b08800a6e4a7e5b65ac22b8e9b94db65acbe08ae3a6e537e5af5ac22b8e9b94df96d8cb08abb94df96d96b1d822aee9b8bdf96d96b08abba6e537e5b65ac27aee9b94df96d96b46a9b95a537e5b65ac49aee9b94df96d96b0e29b96e537e5b65ac380029b94df96d96b0e2bba6e537e5b65acf4aee9b94df9715b63d000aee9b94df96d8f4b369b94df96d96b08a9b98e537e5b65ac22a6e6194df96d96b08abba6e6894df96d96b) else (if page < 14 then 0xa6e7594df96d96b15ebba6e7f94df96d94bae29b94df96d96b1269b94df96d96b200499d6537e5b65ac801240094df96d96b20049a6e8694df96d96b1269b9d6536d96b2d849a6e537e5b65acb612400a6e536d96b2d849b969b94df96d96b126bba6e537e5b66356baee9b94df96d96b3a6bba6e537e5b65e16baee9b94df96d96b466bba6e537e5b65ac12ace9b94df96d96b126a4a6e537e5b65ac49a6e8e94df96d96b1269b94df96d96b12409a6e537e5b65ac540d29b94df96d96b15006a6e537e5bb6d96b1269b94df96d9ad5ac49a6e537e5b65ac4904a9b94df96d96b13420aee9b94db65acbe03abb94df96d96b21c0eaee9b94df95acc803abba6e537e5b63340eb5a9b9d6537e5b65aebba6e7f94df96d93eb5e9b9d6537e5b65aebba6e7f94df96d945a6e537e5b66816b1269b9b2537e5b65ac49aee9ba1a537e5b64e6bbae69b94df96d939aee9b941f96d96b03abba6e537e5a05ac49a6e7594df96816b12400a6e537e5a05ac49aee7b94df96d96b4e6bb9fe7b94df96d939002bb9ee537e5b64e6bba6e8a94df96d9399d66c94df96d96b126bb9b2537e5b65ac490026c94df96d96b126bba6e537e5b15ac0eaee9b9fe537b9b64e6bba6e537b9b65ad39002bba6e537b9b64e69b9ca537e5b65ac49aeeb2a6e537e5b64e6bba6e7094df96d96baee9b94df96d96b172bba6e537e5e06d96baee9b94df96d96b17ebbad69b94df96d939aeeafa6e537e5b64e6b4a6e537e5b65ac5caee9b94df96d939082bba6e537e5b654515 else 0x2bba6e6f94df96d96ba6e7594df96d96b146bba6e7f94df96d95a)))) else 0
  | 7 => if page < 3 then (if page < 1 then 0xba6bba6e537e5b65ac36002bba6e537e5e56d96b002e9a6e537e5b65ac36aeea3a6e537e5b65ac36002bba6e537e5b66196b002bba8e537e5b65ac3600000b3e9b94df96d96baee9ba3e537e5b65ac36002bba6e537e5b65acf9002bba3e537e5b65ac3600000aee9b94df96d8f9aee9b94df96d96b0d808002bba6e537e5b65ac08aee9b94df96d96b0d831002bba6e537e5b65ace7aee9b94df96d9775ac36002bba6e537e5b65dd6baee9b94df96d96b58036002bba6e537e5b65ad1caee9b94df96d96b2980e002bba6e537e5b65ac0eaee9b94df96d96b0d81c002bba6e537e5b65ac1caeeb7a6e537e5b65ace7aee9b94df96d96b39c36aee9b94e2e7e5b65ace7aee9ba22537e5b65ace7aee9b94e2e7e5b65ac22aee9b94df96d9985ac22aee9b94df97a9b65ace7aee9b9d6537e5b65ace7aee9b94e417e5b65ac220029b94e417e5b65ac22aee9b94df96d96b39c22aee9b94df96d96b458e7002bba6e537e5b6458e7aee9b94e147e5b65ace7002bba6e53871f95ace7aee9ba32537e5b65ac36aee9b94e2e7e5b65ac36002bba6e2e7e5b65ac36aee9b94df96d96b438e7aee9b94df9795b65ace7002bba6e537e5e55ace700000aee9b94df9794e7aee9b99e537e5b65ace7002bba6e6794df96d96baee9ba32537e5b65ac6c002bba6e537e5b65ac6caee9b94df96d96b39c17002bba6e537e5b65ac17aee9b94df96d96b39cde002bba6e537e5b65acdeaee9b94e127e5b65ace7002bba6e537e5cd6d96baee9ba32537e5b65ac78002bba6e537e5b65ac78aee9b94e2e7e5b65ac31002bba6e537e5b65ac31aee9b94df96d96b39cd7002bba6e537e5b65acd7aee9b94e417e5b65ac36002bba6e537e5b65ac36002bba6e417e5b65ac36 else (if page < 2 then 0xaee9b94df96d9ac5ac22aee9b94df96d96b45822aee9b94df96d96b53916aee9b9d6537e5b65ad16002bba6e757e5b65ad16aee9b94df9779b65ad16002bba6e537e5da6d96baee9b94df97d1b65aca8002bba6e537e5b65aca8aee9b94df96d96b4581caee9b94df96d96b458deaee9b94df96d96b57822002bba6e537e5b65ac22002bba6e537e5b657822aeeb7a6e537e5e56d96baee9ba22537e5e56d96baeeb7a6e537e5b65ac22aee9b94e1c7e5b65ac22aee9b94e1c7e5b65ad16aee9ba1a537e5e56d96b002bba6e8694df96d96bbaebba6e537e5b65ac06002bba6e537e5b65ac06aee9b94df9795b65ac2c002bba6e537e5b65ac2caeeb7a6e537e5b65ad53002bba6e537e5b65ad53aee9b94e287e5e56d96b002bba6e538a1f96d96bbaebba6e537e5b65ac08aeeb7a6e537e5b65ac55002bba6e537e5b65ac55aee9b94e1c7e5b65ad12002bba6e537e5b65ad12aee9b9d6537e5e56d96bba6bba6e537e5b65ac22aee9b94df9795b65ac22aee9b94df9795b65ad16aee9b94e147e5e56d96bbaebba6e537e5b65ac36002eba6e537e5b65ac36aee9b94df96d96b14c36aee9b94df96d96b254360029b94df96d96b25436aeeb7a6e537e5b65ac36aee9b94df96d96b210360029b94df96d96b21036aee9b94df96d96b1d436b8ebba6e537e5b65ac36aee9b94df96d96b32422aee9b94df96d96b0d8220029b94df96d96b0d822aee9b94df96d96b578360029b94df96d96b57836aeeb2a6e537e5b65ac36aee9b94df96d96b2b822aee9b94df96d96b1d422aee9b94df96d96b53836aee9b9d6537e5b65ac36aee9b94df96d96b29822aee9b94df96d96b21022aee9b94df96d96b45836aee9b94df9795b65ac36aee9b94df96d96b29836 else 0xaeeb3a6e7594df96d96baee9ba1a7594df96d96baee9b9d6537e5b65ac490029b9d6537e5b65ac49002bba6e537e5b65ac4900000a6e537e5b65ac49b9ebba6e537e5b65ac0eaee9b9fe537e5b65ad39002bba6e7f94df96d939002bba6e537e5b65ad3900000aee9b94df96d939aee9b9fe7594df96d96bb96bba6e537e5b65ac22aee9b94df96d96b0a022aee9b9fe537e5b65ac22aee9b94df96d96b2c022aee9b94df96d96b1c822aee9b94df96d96b32c220029b94df96d96b32c22aee9b9d6537e5b65ac22aee9b94df96d96b2f422aee9b94df96d96b1a822b8ebba6e537e5b65ac22002bba6e7594df96d96b002e3a6e537e5b65ac22aee9b95a537e5b65ac22002bba6e537e5b662d6baee9b94e477e5b65ac22002bba6e537e5b65acecaee9b94df96d96b08806aee9b94df96d96b0881caee9b94df96e1b65ac22002bba6e537e5b65cd6baee9b94df96d9ae5ac22002bba6e537e5b65ad20aee9b94df96d96b0880eaee9b94df96d96b08817002bba6e537e5b65ad16aeeb3a6e537e5b65ad16aee9b94df96d99a5ac22aee9b94df96d9a75ad16aee9b9fe537e5b65ad16)) else 0
  | 8 => if page < 1 then 0xaee9b9d6537e5b65ac00002bba6e537e5b65ac2200000aee9b94df96d96b45800002bba6e537e5e56d96b00000aee9b94df96d96b0d800002bba6e537e5b65ace7 else 0
  | 9 => if page < 1 then 0xaee9b94df96d96b else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 6
  | 4 => 58
  | 5 => 713
  | 6 => 899
  | 7 => 170
  | 8 => 6
  | 9 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 1024
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 10)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (10*(k+1)) i)

def bucketCount : ℕ → ℕ
  | 3 => 7
  | 4 => 60
  | 5 => 597
  | 6 => 820
  | 7 => 205
  | 8 => 20
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 25
  | 4 => 217
  | 5 => 2157
  | 6 => 2953
  | 7 => 742
  | 8 => 73
  | 9 => 2
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x200000007000000080000 else 0
  | 4 => if page < 1 then 0x370000000200180037000b000c0004000000010004000100180000002500030005000200050013000000210009000c000000140002000400090004000600020002000000010003000200010006000000050001000b000100020002000300000008000b00020001000f001600040001000200150001000a else 0
  | 5 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0xc0000000100040000000000080007000200000000000c00000000000a0003000000110006002400020018000200040000000200020001000200010001000500050000000000060001000e00000000000b00000001000c000000000003000600000005000200050000000a0007000200000003000000190001000000050004 else 0xd00020008000e001500000001000400020000000200050000000000010002000100110000002b0029000200290005000200010010000100020001000a0004000800120005000100050005000e00040000000a000200010001000300040002000200020001001d000000020020000100010000002f00010000000200020000) else (if page < 3 then 0x10000000c000f0006000500040000001000030003000200050004000500020000000100090006000100010003000d000000020019000000010008000000010000000000020005000000090000000400070000001700020000000d000000040009000100050000001c0001000a0003000f0000000a0000002b000100020001 else (if page < 4 then 0x3000400010000000000020004000100040000001400000009002300020003000b00050002000a000100000007000300020000000400010006000500070006000400150008000e0004000f0000003c000a00060005001b00030028000200090026000100020000001c00020005000700020002000a00050019000e0000000f else 0x40005001a000a00030003000100120007000000000002000d000b0000000e000700060005000000020000000300000000000000020013001f000e0003000b0000000000030020000200000001000a000100020018000200010007000500090000000700020005000d0008000e0010000000050004000200000009000b0002))) else (if page < 7 then (if page < 6 then 0x1c001c0009000900050007000100010014000900080001000c001a001a00020002001100010005000300080007000a000700030000000a001e0004000400080003000e0004000400080000000000000000000000030001000500340005000e0004000b000f000a0001000900150000000b001100010000002d000300040008 else 0xd000d00000004000a000e000a0002001e00020000000f0000000500010001000300470003002a000b0002000000000007000a0000003f000300290003000800020001000700230000000100010001000e00010007000d0001000200030010003e001c000000020000000600050008000000080014000a0009001200010003) else (if page < 8 then 0x380006001800020003000b0002001b00020000001f0000002a000100020046000300000001000b000000000002000f00100004001b00010002000300100003000900000008000200000003000800070001000e00010007000100030006000500010000002100020004000100180000000000010002000b000f000100050000 else (if page < 9 then 0x290000000100300002000b002200030001000100290039001d000d00070000002200040050000d0001000b000c001a00090000005600010003003f000d00020000001a00080004001000000017000800180026000f0003000d0001000c000c00010009000a00230008000c000d000300180000000b00010002002d00110002 else 0x2000400070003000800370047000c00040000003a002c006000010016004000720011000100010005)))) else 0
  | 6 => if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x10006000000010005000f0006000300030000000b000a0003000000040007000000000004000a00010006000100010003000000070004000100050000000d0004000400080000000000000010000200050000000000000001000d000200000000000300000000000d0001000d00160001000100080006000b000000000003 else (if page < 2 then 0x4000300000003000000030005000a000c00010005000c0007000100010000000200020002002a00050000000b0001000a000300030009000300010000001200030002000100040000000000030002000200120002000200030000000a00000000000d00000003000800050004000d00000005000100010000000400020009 else 0x4000000140000000c000500000003000300000003000d0000001800160000000d000b00030007000500050000000300130006000c000000010005001e000f00060000000a000e00050002000000010003000c000300060006000000010011000000070029000b0000001a000000000008000a00090000000000000007)) else (if page < 4 then 0x4000200160007000900030000000a00020006000400050003000000010004000100020008000700000000000f0002000600020005001b000600000003000500040000000700000001000100030000000500000002000000080000000100000000000d000000030002000900060009000b000000000000000d000000000006 else (if page < 5 then 0x10016000000000009002f00010009000000000001001600040000000d0001001a002d0001000800010005000900010001001400000000000b0000000400050000000a000100080002000400040016000200100000000900010000000600050010000400120000000000050000000100080000000000000004000f00040001 else 0x20000000600000007003b00160003000000000007000d000400150000001c0007003d0000001e000400230018001d000a00000000000400010005000200270000000e0001000e001c0001000000040000000c0010000c00220001001300000000001300000001000100020000000b0000000400000000001e000d000e000c))) else (if page < 9 then (if page < 7 then 0x1300020001000c0005000600000000000200010024004a000d0006000300030007000400200002002800040001002700030001000c0001000300010001001100000006000300190031000000480001001b0002000000020011000000070000000500050000000b0005000000040000000000030002000c003500090005 else (if page < 8 then 0x1400050001000d0006000000000007001b0007000000010008000b000b000200000014000100030001000d000000260009000800010000000700010019000b0023000400010000000400150004000c000b002400050011002f0014000100010008000e00170010000b00060001001500150005000000010006002000070002 else 0x4000e0003000f000300290002000000030003000b0000000c001b001400080001000a00000001000000150000000b00460001000500040024004e0005001700000001000b000600010019002d000c0000000b00120001001500000002003200050000004000010003000000010003000000020001000a000000040014001e)) else (if page < 11 then (if page < 10 then 0x44000000040007000900010005004f0002001b0015000c000100050004000100040007001000010002001c0000000900040003000400000019000a0000000b000000000001002800050000000d000400000006000c00230001002d001000040000000000070000000c0030000200040049002d002700000010000100010001 else 0x80008000c0009000000160001001b000600000000000000100009000b000d002f0006001f0006001d002400180000000800050000000700000006001100370068001300030006000700230009000f0017002c00000003001f0005000100040000000700060003001800050016000c0002000200060035001f00070026) else (if page < 12 then 0x100000000200050000000d001500080002000100000000000b00000004000000050050000f000700120046001b005b000500130008000e001a001e00020020000000040001001100070007000d000c00000001003900150004000f000e000300010001000a001800000000000f001e0009000400020018000000030000 else 0x10004007c0001000a0003000600160006001100a20000001900050023000f0001000000040009000c0000000e0045001b00090006000300040000001c000000310004000c000100160001002400030000000900040022000a0001000a00000000000b0001003b)))) else 0
  | 7 => if page < 4 then (if page < 2 then (if page < 1 then 0x9000200010002000100070013000f00030015000400080012001100030003001c00080000000700020001000e00010002000900000000000d00040000000300000001000100040006000500090000001c00080004000300020035000000000002000100110026000600110001000200000004000500000000000200030000 else 0x100210022000600040000000000300008000000020016000000070000000100000019000c0004000800000006000c00020008000000040004002a00000001001700000006000f000200040000000c001100060011000100010015000100080002000300000005000100080002000d000100000027001200060000000e) else (if page < 3 then 0x1e000400050002000c002300010011000000090001000100030007001f0006000600050003002f000a00240005002c0002000000360015000100270009000a00050003000500010011000a001c0002000b000900020008000000100008000500040000000b0000002e000400020000000c000c000100020009000e00030000 else 0x170000000b000600000001002a000300190000003e00000011)) else 0
  | 8 => if page < 1 then 0x5000400000004000d00000000000a000500020002000f00040007000100000000000300020001 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xa4802020100014180204000002030040000080000000000c00080003840102000180a00050402020103006f000000024 else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x30200aa033041825092100c0023000283094180000260a08240809012000f0001920a810120817001a83091205c0016060b00024186a0804480a12000000000174801a803c900c480f061736078104e0000000886081200a002f060e8103c10329000000f1807c003a08245000000440000001000178200000180020180da8000000000000018a8 else 0x78182a002b00050302c185a00050c07020000002a0000000240040000001e001c8c000006e90360a03a4000000000000001a509980689c17240aa4019205c4800500b8c00000449000001824040206600120c1a80070006c0819500724069b000002f4a1c80019302648040000000b8605808040602a4088001a9c25501c240380000000e061128) else (if page < 3 then 0x58104c08000015240052060082c000918085b000002d2400000892810902d4806a608cc01400211801a9000000698000000000a8183e9022021603091e00a943450168c000005ea0327a0502000000a0800000d00065302800355000000600046181f50000000d38000039240025061b04200244a0c1209410260011041b800d52800001d0001a4 else 0x18030e1380000044a06010441816000000118200000509020001b8400800080818181092034000490120003270a4901a9023020582)) else 0
  | 5 => if page < 34 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x8355402a800004f8014d214000000000004f5e09602000cf90105d2918a8d304c9260000124069c640000ab00806e026422002475218a9400001d3c919300000127cdd280000000028e0cbf037f5b8000279003b800000302116a50e6c06100a660000015fc6a4c0304a0d2006a80118f27a482f051580238054406aa8e650521db27cc1717844a4 else 0x2840000027d0000005205914d8fd51108000001f91581484a800a5e066918100d0906540088067c000242350000001930a510014a108c60400023067041cca0009494730769e42000bf4c00003c00054911f090a8144c200000000000007bc018c5a70765828038000002690000000000000011b6d12460000000012b18000065c0378a00000b7c6) else (if page < 3 then 0x53a1a1814000045800000182028d24c53aa14049ef0504862805c4054009ff0022804b8649caa664c5d8232801f6011d04000045c0308093d190f808cd3194100000498100003ce168a00c2a87fc62f294656c27375c8637ca1f94c3e247100b7009635067a807c7ae6a9e21ef1150f004ac198d012c0094c0b48a000011d9b000052c1e15011824 else 0xa4154a4000000ff0102149780a973cf9800000000000000462799803c8908d482f4200003810a2c4c8b24000000001cb0200004b15370004e74323665141f69863504c8084d82d2e075603a0006862160dc160880c83d505eb551110c240c13d347800015b821c023821682482e817e150000003729bbd3ad2386a000005334000000000b1300000)) else (if page < 6 then (if page < 5 then 0x39c0170a018044e2401c03ac0179483000a459c86019c50d802678292209c9066083a7403e0c00d53050c000017c007a195f9d8446806d8a650000076954f6002636428c1fc31905a3300918500001ba00c10416a41001a20024c032d800246530dec400fa04215bc0201ae080ea50940824fce600701332e008400790c45ac98001200817513a26 else 0x4f81008009800e4922189188d97f50b128430210aa000004d12049e3ec9de0000000804101295e54ce001ad80558569230000006920000289012e010a813c03193006380950085eb251080000050127c49348c040c1f8ec9c1ab800a3b3000000001ea00060057944bcf2a81b2a8d84952b49da406ec9268549ee9cce50144390803ce10c2015080) else (if page < 7 then 0x4540210909c4f10003a94068a289641cbc00002ee9000000000000006c9c38026f82181b536c10b002a033d93c10006f00cd3d08802c47114007c265ad301096908ce3a6000028cdde60000000000000000000000023c90e830000000000d86000002612cf821694038042e04a5b07a40a2404434835288adc80002136c00000c40112c078741398 else 0xaaa286214d06d2e86aa1dc24f11d07548c5602cb2480604d18041494ba021e4d2500000003602630d5e3e1f1e4920032045cb698020fa0aad4e00000000062105f2520bd0c95000010502000000003280c0301461b058653e78f64834264d9ec30012c04ddaa37d408e0051500f362f405100101043a245062a3d1a367f47a47d013a6a2c7185fa7))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x6b40a2e90320662009ac02d4e4264ccf3089d5054a8004a6d00000000a91b9003636179b18a92bc000000b0c687e6000008324068924e00000090a40b87d50e4000114a48fc0b8a30000011b66e02262012362000000000da9a63268ca466d2d5e9c3e2400002c86420057600802a644047204000000000000384025d205b8c000050c02930c5d36 else 0x611c800017002e905360012601a5254e330561234d82900a1c04f4057c0106008780444016e011800a2a635cdbf29c25089aaa6e5402a082f553ea93d949dc08060955a48c1522a600030ad1580cc04ce9ff0902a7940004800260058808500252010e8408258d62b1c091c48430c380000000d130000019001021400014780a38630494374d332c) else (if page < 11 then 0x5d124aa95d900d5a898801fc0149388f470213b669a1d00ad030a81800018470000000003ea30000000005f01854c0fa84894200005246621800000000000000bd503f805ed4062f1d9194bc3000002e923c2526802001b4ea00000904216db1e4903d0127828da28000214021527000000001634a00001e41b10a01b0504bf00001640148127012 else 0x5b9b86a0092009c0006d20ea15a95400000000042f05d6c77802fc0c98003f0000008793cb401e148062aa54609805151817034a804aa182a78433636431f4f1756c512407d2b16a82a247ea75c42000002e4c0c8076c294a000001370c0340000002100c31c54431860251003e0140825863210489a1d000020eaac1000e8000002daa00000a79d)) else (if page < 14 then (if page < 13 then 0x2104a1c25071c4dc00520864256406a003360118a501181250c1b8d8074b640056c03f0025c002a807381c4b045301598623c0221093c8a34299504d80040b0a0000a74327811ca48cfa825432d6065f0000008d1900000000000008880444082d501e3c000036e088c08000028c121c0400007c2400003f8025301618600000bc0000000000 else 0x97833b6118e060000000052adc281617250815000000000f33c0000060a0744ce1a56a0003001610a120c59953009e1632fa003e4230e0000008fc54900000000000000007123a09d975429825e8008ec1e50065c603d20508d144afeba45d2a4830000014840000000019950a6338ae2caaf26e24d381875258e189218338000000000000011412) else (if page < 15 then 0x688dd1eaa4e0494a485c349a424e01392c5a08a1214434ec20001809120c886421a64f801c200288eef81299d10a480060000f5a5958401b75073827500c88496232722409c205268000415043cc1b3216961ec0283f924b4902e48051836c337a0c11481680235526630114e41c000003403490012a80364058c01fc06b9a4aa63aec0400010c2a else (if page < 16 then 0x2cd216a90a3010900a8800009cd748ba8088ce08c0000009580019e256a28a18cb826cd39a60c90487802000000000ab48e40381801be0c000000006201b0608b64800000000176968028000011154f0080001469d562300425c105148000003a6a4420612aa1d9d1f401eb0059b06bc2c2c000000f3922180000029b00808377810aa1966009780 else 0x5ac230400be0c0000000012ca9b86c05002940c389c170d102564428049e6d4ad503a143332100000000025461fa02360000004e200000224380000660146202ab767b2813610dc01a0180000000023c100000fa01ac14aee94417c03a41f8e17a91c525242d00002b7161a6000005014116084f087b0051c5800010e00000058634de90514b41a7))))) else (if page < 25 then (if page < 21 then (if page < 19 then (if page < 18 then 0x454341c013f7a000000002223000010890000010a0066082e0081d3b4a90410051832dc932809ee505e251e4141e00634917b076018000000000000390036e0c00007b0203c18b604000047864e928000000015345000000000fc04798200000000279240000a9808440ea218de820000000021b00f602061b26432aa54fb0000001580055480000 else 0xb14005ca4da48218092162280e4702f6801b093a294bb502a302b80000989c0000001f9500000be30b62a7dc02f405e35a0882194002e62454845aa3f00180d8000144028bc0a6a05ce04f9a5ac401fea8374e8a020a863ea49ca4e8f007b001ec0c000c0000000030601cc068585574480000ed007e4203c0414028b067ba82f41992312a840182) else (if page < 20 then 0x43db1e0f1695100a400001c492a1021d806640458916678010c18524e652626b31011480aaf0c19053f0600000e2ea378ab8aa0c41c08913b0aa19804404ae001a4d1d00048042c600d3c06042a140000062014a921a14198a0283a5380151b0e89e3400a2892500004002800c5000bc02609d4f36fe278bc3580a83049282a399220690510d30c6 else 0xa51944661fa02000095002e20400005e28000013690a90000000006040f00c02f3808200816f00000000000004f8e13d04000000002e8a9d55006863252354d86b00000000003740064182203580e00001694cd780000057211e7180000000004c900000000059233f6118f0305060000406788d046924000038c956a6600002900b94a971480000)) else (if page < 23 then (if page < 22 then 0x5b0114a384d007ab632d25220420012c2a4e42320141e054a4331800b70a651d4e014784376081648890000000000000012786b1c00c2a04178201214154aa556050df002b5243e050d0ace25318bc5e0026768280259200000f64b0ab30380b64a0840234801f151be001b6c1da40c5231e01081872040a408a81677522f8060d334c1000002e36 else 0xaa9800015d0009c096c480000ef0485c0000000000c8000000000006c00e32400000080a435489b6000036800000000a701540000000000000225cab86d846ca52a37805080146124b802f80922000000da019640164900000a9aa044190a9e910096806c93d0e19b100a3031f0058418590924b0af8840a98a504000040520380132010d00) else (if page < 24 then 0x7e800000123045e823b8080002a3608fb626182be440001190015d205aa6890202a9221837e99fc050c8000001ca04000140927c4016801ae0529b01dc12faa29e8d1d45a286800dd2e006d808edd000006d4f4e8ca9d853204f64cdc3848c72ce1687001380000051a6c45247700b18083a901d0534b20a8004ef122006e00092000001f804ae00 else 0x3d00bf6f11002f5bc0000176923402000043404f29cbb00a746000052401993155b94b01800023160000010894840a632491b0000001099034cdf0167c1bae01da48a62a57e3c1e0a300c000015925340043048500424040401c74e00001cc000001e602748000000000000000000ac13800022f1800000d149f9100000000000002e802a048e700))) else (if page < 29 then (if page < 27 then (if page < 26 then 0x1e4054a91aa001f8657e290e01ad04b527108157490cd0000002f0000002a98a000081150d8309c4cab4300000000068480000141e000000000c9b09b200ae024b01088670942eea10706192479c1800004f0244000000318005000b406000017e10aa503a828a8000000f50400000b800fe08000011300f801644a2208ae28a8e2c9001b8724ea7 else 0xd89198623000a2095992104f2bd0015011201a28a107001446000027400bb0600000146000000001128c000000000766c080c245325e30000000004a003ce06c454d482a38000000000000000000098f25e014f3c000000000000072807a1d0000000013b04000000000130109060000000025f6c2436409e340a400008ca70000344a000003524) else (if page < 28 then 0x578c2c30c7d0071809ea30441432025e035a0022249cf1e33840c0000ea00600e281020030c9def06a38922409a2002c00a21e79522b20cc94a068c0b120e699126c1b039f8b2a119588704bc000044c319a5000004c0900001a52604a6ad4350e116b005b0c02120000070489fa56f0028410000079808306530990400cb002f1224208f1002492 else 0x3060c0a4f520d8b4a9e2625b4ea40c9914b12009600ba3c90029d80116008080949342200054e45010920aa908d34800007b4083a0c002417280754516a10a0b42ac484012865f5000b805c89048f40001353f9580272162a1800000cdb1da922c8007025245533189c18a0855f0004e08196c42a45752bfc10b600f1a609410b10104488b25)) else (if page < 31 then (if page < 30 then 0x69012fc00d9782c810ac006a04000729bcad000d6115d4c0000000000000014c00000000114c0660000007953a761029306a010a0600ca95508bd300540c0e98d508ca0000004f6500000000000005889077030000000039e54000016250254b30b96e7479a4000000000000000000000528cd25046b00000000000fa02bfa700005187550860009 else 0x8d5f84e69e17a520017c61f20400009f0c4ed558491bf50828c8b860f6aaa442ad853b9b064c1cb0b05805b400589cc20877a4224026292bb8200003dd2b1a10000013aa2f82082fc00004602230000000e76cff92379b542c8bd4b2a0d09401129e2a38f22571953350c0000130c548e00000000157a95ad38eac4c800ee82000024c901a4edea8) else (if page < 32 then 0xd8faaa140804a7460307000f40063a8724601d08054a082465940420e9f012da681808bc056b49113c1c004509d4d36a5c55940d64002300d60001c35483032012a8c04d297e007d0216a69d4001a4ac84953a10881166a1400071055f53c9c423d4819800c129b0628c6437a402d54a425785025248b8000000880200007c0022209e34ec280 else (if page < 33 then 0x592bee704624740074169e402171888120000000003600a53c000000002864c00000c550e8f60b4e0000509f800002254ee0006803c40a2d0023a4031e166d86c4e940240950fe0653724e0a32404b09e7100012516c2c040a68011f26580ca1001b68405808e230dc04587a48a7676123800bf48d1a879823ce09630039015ed4c5a5c060a4f00 else 0x1628ab93b6b0a4180f0123d423d40d67500000000049e021300d428a955048916e06c6a42bd236e00000086001a424ca1966065a809fc0800008574968c000000002a52a00000b52ccf19985e6198052158ac0c20260a400003fe049366e904)))))) else 0
  | 6 => if page < 47 then (if page < 23 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0xb64141201772953bc7880082008100de005e004ba001309130075496aa059703a20101521ba4ac6019c869380148916b055d8081d4b9c0ecd03b21c768194406e910f58403006ae00ca00463680805008a782500008a419700a6548f9a6db801b401ae0400003709b8e131618e70238021a8c95b00d5ad90001e80138819b1eb42007656ba00b12a else 0x24402ec5c0000b4a458de3500895190124c68023a1832016c8080938000261795e005f01cfa01ce01aa80cccb4ae05e4797180450080002fd8a2aa900003541800001d836a540000089016501d29e02a156f08c30211d24bc028f0020242d8012000db24253c0541d2c04d74c5b03239e30a00ed003f83925243ec22800a2927cd211cb2d5196083) else (if page < 3 then 0x23968000247071000579e4bca90a4a10002f00000000a4a6f00cc96e24a87b0d2c82ddd56c60261483d8c941269204163068004792190024a01532d20128c702c338d3a840804da90181998becf123fc491949308023806b60059196f10db00112fc4d02fca6305234a029a0c2a00341c034903a487d02768ab1a007f4a00001182166001d000000 else (if page < 4 then 0x1694d7b01df891de0981540e29c593ee018000111037241000000001960db4833a0940000000000006d0181f54fb3f0d000c471dd180000989e000019600430c148000000564e8b908e8042318760cb99276ca2387948740000d74301eaa4b0174c6264933e009e4e59360000258182c6c00002ac03b0f8cc052802000012a2690027eaa else 0x75c037a00970039ad19c01f27b2702000076006c118000007b6b19257e9cd44d2b92a0494f2dac1040aa716800c672cd4905a745c021a01d07885a5b507546e5031cbe8093864f20e6e011c3c40c1be200b400f68036d835a0d5a7db2bc6b0100000168326bf6a000429f561ace250000358a80001a83000004bc10f152eb8d5e5e0000187798c10))) else (if page < 8 then (if page < 6 then 0x5416ac31134adf03ae81074f33300eb937d00e2600b70805aaa18908e00155a90808ec2508005800c5b41fd218202cc1901bc000016e04344d52801a000d801080134010d5b3fa9362001e1240c6460798f016f86251e34ac196482e240680868f3770dacaf1b42800000001a181a821170e5010b70869a426640912483100d78daee05d2246102 else (if page < 7 then 0x14820c2c1b30000001f031a013570c5100a6e0000013680000089122b0f00000aba46c13286f0c7842d803dc0068b5921950367094411080000000023c08fc1a0f0181bf1f814d690d700c60c0000006a80000b52800003ac516a000eb67180000005b18000000006221a030367004d405e801df08000000004669000003c2400005509f1a0441b6 else 0x4c4129a004204001262921540999482b1e76c73860263013b000bd382601f14833b949828824b804fa3c77d80d3e61181925bccc4042e04bc2566254503122326e038baa011402c2b458c5181060926e005500c4002e5c98015e30001c22fd20000000000000c9494280185020000498304c0400018a80079417a982d07678cd7002da9af662a780)) else (if page < 9 then 0x1cdf800022d000c80104619e0d64838f80cb800f40985810c24c5c01f70131013b2414c0356aa480d1f84254911cfd5801350055803e8104a54ec942bcc2346111306a807e53ab3052800198320c1866389600e6ac13db11cf8214d6e80e0132d70977000000dbc30d894000000000e06196f2c8020000484614a0800017184a4c92d0e5b20b2a27 else (if page < 10 then 0xb1d851899c08a0000bdc64d80a0d009782a209114305f060000000030c9d340087292498044f23e072581369240a635a4e600154400dcf65708198c34c15d475ad04e982ac408ec0adf4ad50caa01b0ea8430416004c000189c3100800e9e9d0d21a8c4e1f8037895de018201a5807241848f1d50044bc00006ac1800057b8270418da1954860c85 else 0x4bde00001658f3a0305a0000036700000000000aaa15f510caa845535a0000002b2500000ae11b000c3807f5b31418fe027e0089004fc48000000003c53ad29d8b752e00000053e000f00fe80151b000027a6e89826c808000000010f3396c00000354020000000020afd0d0400004609348c0000122854d4611402ef0563818640c58a83d554204)))) else (if page < 17 then (if page < 14 then (if page < 12 then 0xc102ef8533805ce01f67c1c8000003a891a9001700188500000dd60e30393d5488a8db18c481ce00db43000000000d84b800030b4c9a92aac016662954f69802a00000000000f800b000e3a904000a20025863e4f31a550200000000003478cc61200004c80c00000000324191ca97704fec26d1402a495c4f33263880692002700feb0 else (if page < 13 then 0x3a614aa0216338a007a8001001ba0a2012e04041cc103493845790140c92ab79a700dbd94b201034f7592300136606e17881860846162004d002e81c38063a0063007d00d2535bcf92d6c9212df0064cff581984aab546868f8bb07a426124936400266173085e921cc99050d2c83c9003ac0a9b00d48382c2d58035a014aa68d401c89230846e01 else 0x7143e4048580d82797cad5090fb00e082cad302c728d4cfd80d3c00c688344f7dbcce131a6326f00dc00dfd236e332a592a00439249032855546a71c41818963a6dba26120000a001722ca004f87986d9934965000913dda987218c0124909832aa39002f3e26d23a2016b032f83d65700609c4507a8086c032a05d2000db00902e54021c66112a)) else (if page < 15 then 0x5a5482f14cb7cb30cc94000001bf4b03000000196fc00000000958100002757f5b01a2522ae9a587e00000000670cc0000a28000006f2033d8d5e0c29c0278a845493192000038e000000323a00003de00bc2c0000000068204000123857616582392f55b81c00000fa0a872486028c40674a80000000081814b6f000000d8200005ea076086d080 else (if page < 16 then 0x26014586d67bf43db000033b0d4727cd5e636093f0a0000b4123cc00bf00e43fade34c632b20151b8c0003ac0f20780b801ec24d2025c2444bea8800b21825002d4221de1c8308c0289a4c8c0c1c02aa7f1b858241000033865b4801500856db580c1a2a0a4c1a40000004d127b8028c4a7448aa46128b00000d07273294589650b49454c0a4 else 0xe8052c01b501818db3001c290f5380000351c000000001b8a3b240800031404bab4005280000b30d4900bdc009ad89624fabcc292670031c18f02554443a642490400000561000025f1ed403820031e0800002c8003d80000333200f846d8648a0c0001b2021b424660084547900ba006ba31662588bcb81923e0000000000b6938d699b6000000))) else (if page < 20 then (if page < 18 then 0x253800000000000000000000000018b00059e00000f1005026000066402d77a00009e4058a02980daab222a0602f00000818215520000000010e4500002c0a31e04eb8100004180576233e9c75874b40d890001bc930000001b62468367282800022b3c0000c7c0800000000f882320306449ff000000d30f6ea05e1000000a5123380307552192 else (if page < 19 then 0x312a8fa780000cb09ad40918009142000020202ad140000000000001b7018b0929c66601b428cc509a2d25ac0ad17948001fc0020080000000000001daf0000080008680b9aa8170aa8b6c0810d0077a00000074862621b39028800bdd39de02f3480000988057a48120a9183988600002d50d128000004680364010542b512a180032180000 else 0x31eab780181be74c268602c961532733d301f091b432a0190c2dd2907b24d0003f40114f4f00153030b8099c7b0c00f580c6c25a83e0c014e0454003a092e00cf480130634e0117081a8117c0492032100143c00004c449950646bf15c2eb8c1323a7c8cd6c6000024f7899922d41022004c2421a43b831d8000000f12a83523fc0000016e83)) else (if page < 21 then 0x73142c2f02b0142bc01034f69282784b265a81e06014c54000071616de928118163000003720000000000000029e6000006300c2d381c30ba07578000003ba00907267180600692c30518c106000062a10f24e00008700b420716256b82c00100000bf50248cb7ca8000000019600000018a180560afa540c7a44d92e0c000000000de280000f9a7 else (if page < 22 then 0x8fc1c0499cb51010490020f901dc5a000000002dd08b900d79244c1800017948b13c25c6324483305584034d20c705501993800401a78f0cc00ac860000644fd15080000000016c09bb0aaa8100001ac00000095245d544a00000000000000025800940148800000000025b7e00004f8abfaf00000ca3c42cc256632b4ec5030000000009c489528 else 0x830600000331e2b804a4017a013e0060842c80314a2010000000000000028038000086c165afd4a01452468c1d4e02777200000000170002524000000000d2080001568020600a03400015b080000000000000090054c119e0000000000000066e90000000002d9200001ed0a0000cc0b2000800001e00dd8052406307821b022c030030ad6ce43c))))) else (if page < 35 then (if page < 29 then (if page < 26 then (if page < 24 then 0x424100001cd04128c0000002cf444f66061b823a8a86e01ba802080b4c0353023fa8854257090cd04fbaa68a2b9ab41e52000074431b8036b0532a7c75501401d9041fa4ab60000011b368ebc8c0c27e447d540000702253c91b308b88100004ce980000000020823e8009f4e4100cdc02326c000050279f0000002c000ee3f0000064600000068c else (if page < 25 then 0x3aa1000037c0200001f401a208842471a45a182ce080000000056d3d30630c02ff84054000001648f55840c006a802c50c0000ad8213c9a1b1e6712b35546e32b50f7b43da430a2107f0d79121b80e04fc00010d127d5f8000000009405948927802d700140089c011a1802000580324156f0c0001230000004d69800013404abdeee0000000c5a8 else 0x1800000005000ad00b9004a60000012183b88036e4a1b2ae08000006b209d06c0000000059201bb0166807f550000313544424000001c016700882a4106000000000b4006595446db510153841713362a2c65400000000170e31305a312ba4d80002840293800ec7a3693384e7f801bce6521a346130120ccac7a00e752e8307301000032f014881)) else (if page < 27 then 0x4a460429252018a822c12228001518b8831c9eae01637258810e08056a721000b5c50fc91e009260026009c493640b5a0275986b81de80824192f248549630002d00ce80c3c05dcfc96129e92aa003b098f2022da709953d8007a071f80090061a087c7b158099000b6924b08ea8132c06549823003336888939801e048ce8c6681aa0fc00011500 else (if page < 28 then 0x7c08549226852b0041d2b22116870a81262800e4000001b9c000000309c00000000db403c614000000001ddd4da9d510c00003ee0800000000000068c1142058a046f8073c06ba37750d6c0c844c172e024245d0019805d90266480d3cae5fbb89c776ed8802f80044000000adaa18c55e2f056000f824ac00fe24954cf492625e4e0fcee31a912 else 0x2a521ce4ac2302c92c80027c0f6f003601cb8665249ae51a8b019db4bcf1f304f48c501528401fb6d7f1256602c2900f78a30078d5062487d0200005fde2621f7218180312d4000006d009ea46bcb6ee90f1047580394066a02f5095d240053c6c700000e32861420000000000000751e246a3428e998c000028e29345a0f250000048fd210c530c))) else (if page < 32 then (if page < 30 then 0xddc004004000111860000000024319bd80000062e042504790253861b201f7480000ab5ec0204c26c00001a9db30006a747442035e1c4c20f022480ce466de39230480848941adc780f48d9a82007a0432ab7ea406ab1e27a26564f752376471d806da4c21b61482a7e5dc87cc286c6035b608b14951363400800025d24e74216c92ac08cf040aa4 else (if page < 31 then 0x3b860ec0f01373f80000018a0000015b470000336f0842fa4272fd2bc414bb0017a600003840279042200380011206f68c6992a71e35436d97ac5250712d46023c0035a7a1400bcf0354926ad75460f401e819068601d3016f04f0019927440820000000b93f2c005c002fb03aab3ce404ce9d4519043c92553d0001a0132a6000027a9d7301b502 else 0x15932c8a800015945000035aa000003780585549a0238003882000004c01030015b061c080000c0081802000000002de00b906d9862a6004804f412d911356b2e1305e135bc100001ae01ba9001129b83400000000000048e026a02388000004b0fad5000000000012a003918000077490000000019f84be403ce013d4ca30ca84027e08e1000f24)) else (if page < 33 then 0x3b120000337600000000008890510ac182000011af800000000bdd301c489d49780000001540e03018e86030600000323ce1a8000045c00000000000000000007c000000814f6a401b209a6009a40dd31c0001738279000be08ca0801a4bac64da99a0040abcb51242a000001278000001760a460b550065c02900368003f82ba0300000b7013f00 else (if page < 34 then 0x4a08e88817e00ef00000045e0021532a81000057e98f6009da60000558122205a800ad40000003c180e24bd820d200f078e5804bc05b602c23800005b204240800007c0c5d5d62e900001a48cca13ae8305f241e82284000001011800000000000000001700e638056830fc4830a484cc38108ef0c448466c180000502400001e402e849ca603c84 else 0x3a65b2f7ed882ae135cc18000014a785926ac02ff8c0a81000008c02b68ced0f9a8200003341934000ad26140257000000c1860ca488a832dbe00000bcfe01081c92000000001a0060000cd800f60014012c3c140600002d724ad3c114324800be0400007d4000000000000002381800000001992c00003b6092e198c8064001bc080000b526)))) else (if page < 41 then (if page < 38 then (if page < 36 then 0x7e9c4f1800002b1b51c985002bb050000046183300000015944c0326b4e492440d2c8a003e00d928de40e8203145427364a033f401c90178a4b2cc1b0003e780000524d80000000000000000000002a4b173f000000000000126020000334f2420a7d820000000011500a946000000000000000000000000000000c3a400000faf05e000000 else (if page < 37 then 0xd8a0ac400000000003bc190859f70074013352112a83d00068068a2666083448278dd9c3048100000280212dd116082d042781000000a0570009e8000006bee649780000b4d8000001b6c0f0c828c62ef147012180a5ce000027500b98c17400d2061e080000ba5565afb400400000000000006c040000055f8000000012a8600000000000000000 else 0x21123a018f6197d0013c9868b3017da48263004360c42080003d4c009c02db078e0d0b1217a900d24c3241ce28a04f1000049e7e00458037224718085a011c0a9b7ad205654000002dd49b8070000000000000000000004a6900000903661930641a1518000033d24f6980019332700006c2557f0030807e80beaf83a080000000046a922005ab8d)) else (if page < 39 then 0xc1060000197787fac00000b4f0000087810a151a2d81648a424351406c00187e252424c862c9b571803a7911204c900000a8ba3f925a448000039800e004e230dd49a235c70012a9d59000cbc2b9b26a90c90079240000000007e00e3021b830f831001911b06c1200000000082c50c4609e4a4606e280520c22202b905083ca7c30000000000000 else (if page < 40 then 0x174207290b54928845dc719c1a1a000d80cb4064a04147800003c9300001c950000028c03880000013704b8c32c2004b691b8400004e69dd05510a9730180000000000002e810fa1a410024b67f8091edaee010fc280c23a2612e011180bf00346020d546d8000002a2ee9c031c06944605c1000010d0c2941de2aaa4008e122f81846920655bea4 else 0x44804e4ff7554668029806fa0004013783070656a08bb30f2808e429e0fcf07d7d80d6404d600ed048506ab801cea0784d95823653074a800009e8c0000454096582000006d23a108ff5a00004880358b174004838000053afc0000df8077c06884979845c366c41b900929259400c40347109d40c72a4b7ca2d71366251d803c41dae3000000aaa))) else (if page < 44 then (if page < 42 then 0x22c1e9a000000a882400080000000000005542000002804fe004ac36524dac5ae38658c05f8095e48d0844344120d93a00000015836b002834852259855426f0c7019b120bd262403190cc900778215e0168072e8c260923e1a2048d918dd5f4306719789c818140672357b7800008ac11980da851bc060d580cee07001628c504c1e6db2e2400b9 else (if page < 43 then 0x6a8835e029e00b1247941156067f72aea4c04466802be490a426c81d90c0565242c6069507c90830154809513000028478bc80058304e10000000008c802c87b440049847940912307a5000002e5b45ada440024247c152c893760c7f0020c333ea26001a7b0c6c066aaa56061a801d1c8b89df84860034100598905618d3280fc602ca800004600 else 0xa68c494f7638022a60000328041f00d5824c91eba01f6782f0496811a008862483000000322426748d482d60680000000036303e0002e5c00003a92b392094000001bc860dc01e6051c31159805d200604000164001f4211630a500a01800005b8712a09c081830919406f8046f0c62522c0956804b436a80049805fa08e9011d803c805f2004980)) else (if page < 45 then 0xc04d802b337360301802b2f2d101110c000058e03400692803fc300002a424f204c94620a018402b38f53c313e99f948a1801380cb4002606000064c000002f610600054a1a966f08549f0200002e8096707ad265914d9670ce18e38194403eef34e2d8103108008031fe0869806942de0323630958167801000d3f00ff0c5b94dca1abb780b00 else (if page < 46 then 0x14db1b4c0000000006e420ac48d5480000b783000a828859f000000212006c4800002d403b20eff86d793374611e027c096e820000000024c08000000005484c0000288068a12dcf0dd005a834a92850da1d19b89d5ec051e04234a6236c481086031e498880c7030490a48000000319258871be780000d28006650964e1a3f0542028a81644c896 else 0xe281000000002270400002f53a021a997f2412)))))) else 0
  | 7 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x9e0570000003d80000013a408a003f2a0740038186b480e240c09016008800278c0380842903200110024000b0001e083f02000001a10654c49802813000007108000019939480022040b0c0ad503a3800001384278013a5800003f01208693218000036001e46114188d7a148c0ade08e08a7003c22230011c088b0435a511819360819840000 else (if page < 2 then 0x20ca04a6000003b01168789e10831c220000000ee881c045281139f934082d2e1280104c016083f002e3f200005a444100200c12c00e6f04f840e8209411361853602d0313968b230a14e3f241080904489108388101db0780000004da726c409800210602a417520ba3c43041193171681ed8480c108e25c00f29c6c06508c2180038009d0c2512 else 0xb1e056902c5400000612032009e4a44060913000000000000000000240c00004d930000020e428501685000010400400c128313090d2087b48548000c0144300000000013de0f8009c001faa000003a907f2c00001ac10d0008024268200000b4906708412c07c1090f82000338124c2000001c180cb609c287aa85c7c3f90144001a004b180000)) else (if page < 4 then 0x6600950c223c034309610496c00002401096f00000000007d6894f05c784180294000000a90e254213c28000000000ba40000000004b84519c00000000000000000000000000260251a2204000000804c3eaa09c113a009e0c0e8c07861049c2f000000170100000760040861282000007a4800001993000002924150c00000000035505486 else (if page < 5 then 0x1fc00821800004abe0a40026001a00418712c289200804a3ca6299504294a24e340117410344800002d8d000000000000000000000000001b0c4bbf1c8215018a14c3700070784460980022a416400f07075484da60b8613e9c720026800847890004b2417120a020941474002d80024900000a2242e000ac30e8106d2a00000a408000017600000 else 0x2d200000a60253aa07df01a04000054811cc20b8a8207c151214000dc4800001624181200000a748103f119b11b001d1e3c401092142481f7e102d26c60d01018600a001789100182004220611c08a400390200bc2a00082041c06138027c60363069723d060481038948e000e831f400b6041500400c104185004270c238d2089892086c044186))) else (if page < 9 then (if page < 7 then 0xad10eca845184ebf11400fe184604402700000e06018001a0010cb0ba0049600ea521df80000a3822ea500000ba30957814241b8b0de902b000000248184c10824c4dad000011248000000001a400f248000000001d92000002b3814820000000004d24242c1dce05c00630000000095028308218448c1716020e07d480b802806088a836003828 else (if page < 8 then 0x18007d023c4123011060429482d2500000440c00540000068f00000000018000cdb09c9c6a72412d000003ef02a00000014c01409c37500000081e0de9c000000002581000007100083600000da9006484280275f03c189900178c00000ef000000060211120000043202d8615000180c6b0c088323d213e98831e532428090b6400e080900 else 0xf5e1342091003580078087ef05f242e8e09c188e005a00368019520844843083aa506cc15094696c5424268308c48878a2a0503800b6107a004e06185214c00314a2904021b148a825504f9228930d2e01f54139811860ae0016000f0d16210da507f7e40811442000004108000006c00b4384c180d0c10c008cc0940022aa100f01ee41e001d00)) else (if page < 10 then 0x26c68b0d8301820851de08ba0c7006108608160ba1899043fbe268003eb0452442032955084a846001f2515db0e4f0850c179208150464804003200091207698960002801c0010c18700451c020ca8b40824000000295213220654e278000000000091780000000000000a402248c11c991e98000049bc0a5504e0421042bc210800da486e262018 else (if page < 11 then 0x26c9090982300000000000920c5a0c3d25000000000000029a40788000001c1c52240e0000000810e00001d400de984c04270607c008a040b4a5381258085704110410800280000006a700000084604c003d00250c1d1e0ea188b00000008cb12a00000024920000000000000000010090d60c4f24378000000aa0000004f240000044a04a004d80 else 0xb06270000550000000002b001992050947e00338003dc000009b581227201209a3042180100001e0b430820c000002c30d4d894044b2a04400c4d85b1820820a0003a1800004b2420810000082102000)))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x6100a54016000810042806540200023f0115008340506011800c1808f00154020c005200210032802040147008b4044c028200400020c031e00000092002d804020082000000a48005000000003008580178018c0109000000400012500c1000000250021301120000005180294001200a3c0030018000000041803240280011f0009404200227 else 0x31c00000000000000000022c) else 0
  | 9 => if page < 1 then 0x0 else 0
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
  let slot := field targets k 17 ((h / b + shift) % slotCount k)
  (slot / 128,slot % 128)

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
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s14 : Switch := ⟨14,0xcccc0000cccc,0x3333000033330000⟩
theorem s14_ok : s14.Valid := by unfold Switch.Valid; decide +kernel
def s25 : Switch := ⟨28,0xf0f0f0f0,0xf0f0f0f00000000⟩
theorem s25_ok : s25.Valid := by unfold Switch.Valid; decide +kernel
def s15 : Switch := ⟨30,0xcccccccc,0x3333333300000000⟩
theorem s15_ok : s15.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s05 : Switch := ⟨31,0xaaaaaaaa,0x5555555500000000⟩
theorem s05_ok : s05.Valid := by unfold Switch.Valid; decide +kernel

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
  | 36 => [s03, s14, s25]
  | 37 => [s03, s14, s25, s12]
  | 38 => [s03, s14, s25, s01]
  | 39 => [s03, s14, s25, s01, s02]
  | 40 => [s03, s14, s25, s02, s01]
  | 41 => [s03, s14, s25, s02]
  | 42 => [s03, s15, s24, s12]
  | 43 => [s03, s15, s24]
  | 44 => [s03, s15, s24, s01, s02]
  | 45 => [s03, s15, s24, s01]
  | 46 => [s03, s15, s24, s02]
  | 47 => [s03, s15, s24, s02, s01]
  | 48 => [s04, s13, s25, s01]
  | 49 => [s04, s13, s25, s01, s12]
  | 50 => [s04, s13, s25]
  | 51 => [s04, s13, s25, s02]
  | 52 => [s04, s13, s25, s12]
  | 53 => [s04, s13, s25, s12, s01]
  | 54 => [s04, s15, s23, s02, s12]
  | 55 => [s04, s15, s23, s02]
  | 56 => [s04, s15, s23, s12]
  | 57 => [s04, s15, s23, s12, s02]
  | 58 => [s04, s15, s23]
  | 59 => [s04, s15, s23, s01]
  | 60 => [s05, s13, s24, s01, s12]
  | 61 => [s05, s13, s24, s01]
  | 62 => [s05, s13, s24, s02]
  | 63 => [s05, s13, s24]
  | 64 => [s05, s13, s24, s12, s01]
  | 65 => [s05, s13, s24, s12]
  | 66 => [s05, s14, s23, s02]
  | 67 => [s05, s14, s23, s02, s12]
  | 68 => [s05, s14, s23, s12, s02]
  | 69 => [s05, s14, s23, s12]
  | 70 => [s05, s14, s23, s01]
  | 71 => [s05, s14, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s45_ok, s34_ok, s35_ok, s12_ok, s01_ok, s02_ok, s03_ok, s14_ok, s25_ok, s15_ok, s24_ok, s04_ok, s13_ok, s23_ok, s05_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def goalColumns : Nat := 0xfe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000fe80808080808000
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def checked (k i : Nat) := decide (pool k i).Nodup && Vector.packedClosed target negative goalColumns pool counts lookup steps k i
theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 6 0 = true :=
  chunk3x0

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
theorem chunk4x48 : span (checked 4) 10 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 58 0 = true :=
  (@span_join (checked 4) 32 0 26 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 10 chunk4x32 chunk4x48))

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
theorem chunk5x704 : span (checked 5) 9 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 713 0 = true :=
  (@span_join (checked 5) 352 0 361 (@span_join (checked 5) 176 0 176 (@span_join (checked 5) 80 0 96 (@span_join (checked 5) 32 0 48 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 32 chunk5x32 (@span_join (checked 5) 16 48 16 chunk5x48 chunk5x64))) (@span_join (checked 5) 48 80 48 (@span_join (checked 5) 16 80 32 chunk5x80 (@span_join (checked 5) 16 96 16 chunk5x96 chunk5x112)) (@span_join (checked 5) 16 128 32 chunk5x128 (@span_join (checked 5) 16 144 16 chunk5x144 chunk5x160)))) (@span_join (checked 5) 80 176 96 (@span_join (checked 5) 32 176 48 (@span_join (checked 5) 16 176 16 chunk5x176 chunk5x192) (@span_join (checked 5) 16 208 32 chunk5x208 (@span_join (checked 5) 16 224 16 chunk5x224 chunk5x240))) (@span_join (checked 5) 48 256 48 (@span_join (checked 5) 16 256 32 chunk5x256 (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288)) (@span_join (checked 5) 16 304 32 chunk5x304 (@span_join (checked 5) 16 320 16 chunk5x320 chunk5x336))))) (@span_join (checked 5) 176 352 185 (@span_join (checked 5) 80 352 96 (@span_join (checked 5) 32 352 48 (@span_join (checked 5) 16 352 16 chunk5x352 chunk5x368) (@span_join (checked 5) 16 384 32 chunk5x384 (@span_join (checked 5) 16 400 16 chunk5x400 chunk5x416))) (@span_join (checked 5) 48 432 48 (@span_join (checked 5) 16 432 32 chunk5x432 (@span_join (checked 5) 16 448 16 chunk5x448 chunk5x464)) (@span_join (checked 5) 16 480 32 chunk5x480 (@span_join (checked 5) 16 496 16 chunk5x496 chunk5x512)))) (@span_join (checked 5) 96 528 89 (@span_join (checked 5) 48 528 48 (@span_join (checked 5) 16 528 32 chunk5x528 (@span_join (checked 5) 16 544 16 chunk5x544 chunk5x560)) (@span_join (checked 5) 16 576 32 chunk5x576 (@span_join (checked 5) 16 592 16 chunk5x592 chunk5x608))) (@span_join (checked 5) 48 624 41 (@span_join (checked 5) 16 624 32 chunk5x624 (@span_join (checked 5) 16 640 16 chunk5x640 chunk5x656)) (@span_join (checked 5) 16 672 25 chunk5x672 (@span_join (checked 5) 16 688 9 chunk5x688 chunk5x704))))))

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
theorem chunk6x480 : span (checked 6) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x496 : span (checked 6) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x512 : span (checked 6) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x528 : span (checked 6) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x544 : span (checked 6) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x560 : span (checked 6) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x576 : span (checked 6) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x592 : span (checked 6) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x608 : span (checked 6) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x624 : span (checked 6) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x640 : span (checked 6) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x656 : span (checked 6) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x672 : span (checked 6) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x688 : span (checked 6) 16 688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x704 : span (checked 6) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x720 : span (checked 6) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x736 : span (checked 6) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x752 : span (checked 6) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x768 : span (checked 6) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x784 : span (checked 6) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x800 : span (checked 6) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x816 : span (checked 6) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x832 : span (checked 6) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x848 : span (checked 6) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x864 : span (checked 6) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x880 : span (checked 6) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x896 : span (checked 6) 3 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 899 0 = true :=
  (@span_join (checked 6) 448 0 451 (@span_join (checked 6) 224 0 224 (@span_join (checked 6) 112 0 112 (@span_join (checked 6) 48 0 64 (@span_join (checked 6) 16 0 32 chunk6x0 (@span_join (checked 6) 16 16 16 chunk6x16 chunk6x32)) (@span_join (checked 6) 32 48 32 (@span_join (checked 6) 16 48 16 chunk6x48 chunk6x64) (@span_join (checked 6) 16 80 16 chunk6x80 chunk6x96))) (@span_join (checked 6) 48 112 64 (@span_join (checked 6) 16 112 32 chunk6x112 (@span_join (checked 6) 16 128 16 chunk6x128 chunk6x144)) (@span_join (checked 6) 32 160 32 (@span_join (checked 6) 16 160 16 chunk6x160 chunk6x176) (@span_join (checked 6) 16 192 16 chunk6x192 chunk6x208)))) (@span_join (checked 6) 112 224 112 (@span_join (checked 6) 48 224 64 (@span_join (checked 6) 16 224 32 chunk6x224 (@span_join (checked 6) 16 240 16 chunk6x240 chunk6x256)) (@span_join (checked 6) 32 272 32 (@span_join (checked 6) 16 272 16 chunk6x272 chunk6x288) (@span_join (checked 6) 16 304 16 chunk6x304 chunk6x320))) (@span_join (checked 6) 48 336 64 (@span_join (checked 6) 16 336 32 chunk6x336 (@span_join (checked 6) 16 352 16 chunk6x352 chunk6x368)) (@span_join (checked 6) 32 384 32 (@span_join (checked 6) 16 384 16 chunk6x384 chunk6x400) (@span_join (checked 6) 16 416 16 chunk6x416 chunk6x432))))) (@span_join (checked 6) 224 448 227 (@span_join (checked 6) 112 448 112 (@span_join (checked 6) 48 448 64 (@span_join (checked 6) 16 448 32 chunk6x448 (@span_join (checked 6) 16 464 16 chunk6x464 chunk6x480)) (@span_join (checked 6) 32 496 32 (@span_join (checked 6) 16 496 16 chunk6x496 chunk6x512) (@span_join (checked 6) 16 528 16 chunk6x528 chunk6x544))) (@span_join (checked 6) 48 560 64 (@span_join (checked 6) 16 560 32 chunk6x560 (@span_join (checked 6) 16 576 16 chunk6x576 chunk6x592)) (@span_join (checked 6) 32 608 32 (@span_join (checked 6) 16 608 16 chunk6x608 chunk6x624) (@span_join (checked 6) 16 640 16 chunk6x640 chunk6x656)))) (@span_join (checked 6) 112 672 115 (@span_join (checked 6) 48 672 64 (@span_join (checked 6) 16 672 32 chunk6x672 (@span_join (checked 6) 16 688 16 chunk6x688 chunk6x704)) (@span_join (checked 6) 32 720 32 (@span_join (checked 6) 16 720 16 chunk6x720 chunk6x736) (@span_join (checked 6) 16 752 16 chunk6x752 chunk6x768))) (@span_join (checked 6) 64 784 51 (@span_join (checked 6) 32 784 32 (@span_join (checked 6) 16 784 16 chunk6x784 chunk6x800) (@span_join (checked 6) 16 816 16 chunk6x816 chunk6x832)) (@span_join (checked 6) 32 848 19 (@span_join (checked 6) 16 848 16 chunk6x848 chunk6x864) (@span_join (checked 6) 16 880 3 chunk6x880 chunk6x896))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x16 : span (checked 7) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x32 : span (checked 7) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x48 : span (checked 7) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x64 : span (checked 7) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x80 : span (checked 7) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x96 : span (checked 7) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x112 : span (checked 7) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x128 : span (checked 7) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x144 : span (checked 7) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x160 : span (checked 7) 10 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 170 0 = true :=
  (@span_join (checked 7) 80 0 90 (@span_join (checked 7) 32 0 48 (@span_join (checked 7) 16 0 16 chunk7x0 chunk7x16) (@span_join (checked 7) 16 32 32 chunk7x32 (@span_join (checked 7) 16 48 16 chunk7x48 chunk7x64))) (@span_join (checked 7) 48 80 42 (@span_join (checked 7) 16 80 32 chunk7x80 (@span_join (checked 7) 16 96 16 chunk7x96 chunk7x112)) (@span_join (checked 7) 16 128 26 chunk7x128 (@span_join (checked 7) 16 144 10 chunk7x144 chunk7x160))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 6 0 = true :=
  chunk8x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x0 : span (checked 9) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer9 : span (checked 9) 1 0 = true :=
  chunk9x0
theorem verified : ∀ k ≤ 9, ∀ i < counts k, checked k i = true := by
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
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 10 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 9
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => Vector.closed_sound target negative goalColumns mask_valid pool counts lookup steps (by decide +kernel) (fun r hr => (neg r hr).1) k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    9 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full



namespace SignedFrontier.CliqueLink
def target := SmallCert.Full.target
def raw := SmallCert.Full.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 10 ≤ p.length := by
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
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 10 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 10 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12254_aux

open PEqualNP.Outside.L_meta_12254_aux

theorem PEqualNP.Outside.L_meta_12254 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834368 * 2 ^ 32 + 2155905024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834368 * 2 ^ 32 + 2155905024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
