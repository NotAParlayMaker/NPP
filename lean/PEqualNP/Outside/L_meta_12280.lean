import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12280_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4276676608 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [0,1]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.and, [2,7]⟩,
  ⟨.or, [2,7]⟩,
  ⟨.or, [6,8]⟩,
  ⟨.and, [3,4]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.and, [5,11]⟩,
  ⟨.and, [5,12]⟩,
  ⟨.or, [11,14]⟩,
  ⟨.and, [10,15]⟩,
  ⟨.and, [9,13]⟩,
  ⟨.or, [16,17]⟩], 18⟩
theorem size : witness.size = 13 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
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
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 12 ≤ p.length)
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
    exact ⟨witness, legal, by rw [size]; change 13 ≤ C.gates.length; omega, value⟩

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

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 45) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 45) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 2880 := by omega
  have val : fullLanes = 2^2880-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 45) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 45) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 45) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 45) (xs : List Columns)
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
    (length : rows.length = 45) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 45) (bounds : ∀ r ∈ rows, r < 64)
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

namespace SignedFrontier.SmallCert.Sub7x0

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

end SignedFrontier.SmallCert.Sub7x0

namespace SignedFrontier.SmallCert.Sub7x1

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

end SignedFrontier.SmallCert.Sub7x1

namespace SignedFrontier.SmallCert.Sub7x2

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

end SignedFrontier.SmallCert.Sub7x2

namespace SignedFrontier.SmallCert.Sub7x3

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

end SignedFrontier.SmallCert.Sub7x3

namespace SignedFrontier.SmallCert.Sub7x4

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

end SignedFrontier.SmallCert.Sub7x4

namespace SignedFrontier.SmallCert.Sub7x5

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

end SignedFrontier.SmallCert.Sub7x5

namespace SignedFrontier.SmallCert.Minor7

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
  | 0 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xfafa0000fafa0000faaa0000faaa0000f3f00000f3f00000f0f00000f0f00000f0a00000f0a00000f0300000f0300000f0000000f0000000eeee0000eeee0000eafa0000eafa0000e0f00000e0f00000e0e00000e0e00000e0000000e0000000cccc0000cccc0000baba0000baba0000baaa0000baaa0000b0b00000b0b00000b0a00000b0a00000aaaa0000aaaa0000aaa00000aaa00000a8a80000a8a80000a8880000a8880000a2a20000a2a20000a0f00000a0f00000a0aa0000a0aa0000a0a00000a0a00000a0000000a00000008aaa00008aaa000088aa000088aa0000888800008888000080a0000080a0000080800000808000007350000073500000707000007070000033300000333000003232000032320000322200003222000030f0000030f000003030000030300000300000003000000022aa000022aa0000222200002222000020aa000020aa000020300000203000002020000020200000200000002000000010f0000010f00000101000001010000010000000100000000eee00000eee00000aaa00000aaa0000022200000222000000fa000000fa000000f0000000f0000000ee000000ee000000e0000000e0000000ba000000ba000000aa000000aa000000a0000000a000000088000000880000003000000030000000220000002200000010000000100000000a0000000a0000000000000000 else (if page < 2 then 0x100010001000100010000000100000000fff00000fff00000f0f00000f0f00000f0a0f0a0f0a0f0a0f00ff000f00ff000f000f000f000f000eeeeeee0eeeeeee0ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0c0c0c0c0c0c0c0aaafaaa0aaafaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a088888880888888805550000055500000222aaaa0222aaaa022222220222222200ff000000ff000000fe00fe00fe00fe00fc00fc00fc00fc00fafafa00fafafa00f0f0f000f0f0f000f0aafa00f0aafa00f000f000f000f000f0005000f0005000f0000000f0000000eeeeee00eeeeee00eeee0000eeee0000ee00ee00ee00ee00e0e0e000e0e0e000cccccc00cccccc00ccaaee00ccaaee00cc00cc00cc00cc00bababa00bababa00b0b0b000b0b0b000aaf0fa00aaf0fa00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa00a0a0a000a0a0a0008a8a8a008a8a8a008888880088888800808080008080800070707000707070006666660066666600323232003232320030f0f00030f0f000303030003030300030003000300030002222220022222200202020002020200010101000101010000efeee000efeee0000fff00000fff00000ffaa0000ffaa0000ff000000ff000000fefe0000fefe0000fef00000fef00000feee0000feee0000fcfc0000fcfc0000fccc0000fccc else 0x30103010301030103000ff003000ff003000f0f03000f0f03000f0003000f0003000baaa3000baaa300030303000303030003000300030003000200030002000300010003000100030000000300000002aaaaaaa2aaaaaaa2aaa2aaa2aaa2aaa22f2f2f222f2f2f222aaaaaa22aaaaaa22aa22aa22aa22aa22323232223232322222f2f22222f2f22222aaaa2222aaaa2222323222223232222222222222222222220202222202022222000022220000222033302220333022202220222022202200220022002200220000002200000020aaaaaa20aaaaaa2030f0f02030f0f02030a0f02030a0f020303030203030302020f0f02020f0f02020aaaa2020aaaa2020a0a02020a0a02020303020203030202022222020222220202020202020202000aaaa2000aaaa2000a0a02000a0a020003000200030002000222220002222200020002000200020000000200000001f1f00001f1f000011ff000011ff000011110000111100001110fff01110fff011101110111011101100ff001100ff001100110011001100110000001100000010f0f0f010f0f0f010f010f010f010f01010ff101010ff101010fefe1010fefe1010f0f01010f0f010103030101030301010101010101010101010001010100010100000101000001000f0f01000f0f01000f0001000f000100030301000303010003000100030001000101010001010)) else (if page < 4 then 0x5555550055555500555500005555000055505550555055505550505055505050554444445544444455105510551055105500ff005500ff00550055005500550055000000550000005454545454545454544454445444544450f050f050f050f05050f0f05050f0f0505070705050707050505050505050505050000050500000500050005000500050000000500000004c4c0c0c4c4c0c0c45450000454500004444444444444444444400004444000040404040404040403fff00003fff00003f0f00003f0f000033ff000033ff000033f0f0f033f0f0f033aaaaaa33aaaaaa333333003333330033332222333322223333000033330000333233323332333233323232333232323330fff03330fff033303330333033303330303033303030332233223322332233222222332222223300f3f03300f3f03300330033003300330003003300030033000000330000003232fafa3232fafa32323232323232323222faaa3222faaa322232223222322232222222322222223130313031303130311130003111300030f0f0f030f0f0f030f030f030f030f030f000f030f000f030707070307070703030ff303030ff303030f0f03030f0f03030baba3030baba303070703030707030303030303030303030300030303000303010103030101030300000303000003020ffaa3020ffaa30203020302030203020202030202020 else (if page < 5 then 0xa0a0ececa0a0ececa0a0b0b0a0a0b0b0a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a0a000a0a0a000a0a00000a0a00000a080f0c0a080f0c0a080a080a080a080a0808080a0808080a020f030a020f030a020a020a020a020a000f0f0a000f0f0a000f000a000f000a000aaaaa000aaaaa000a0a0a000a0a0a000a000a000a000a0000000a00000008ccc8ccc8ccc8ccc8c8c8c8c8c8c8c8c8aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a8a8a00008a8a00008a008a008a008a0088f8f8f888f8f8f888cc88cc88cc88cc88aaaaaa88aaaaaa88aa88aa88aa88aa88a8a8a888a8a8a88888f8f88888f8f88888cccc8888cccc8888aaaa8888aaaa8888888888888888888808088888080888880000888800008880888088808880880088008800880080a0c0f080a0c0f080a0aaaa80a0aaaa80a0a0a080a0a0a08080a0a08080a0a0808088888080888880808080808080808000a0008000a00080008888800088888000800080008000800000008000000077770000777700007770777077707770770077007700770075307530753075307500750075007500735073507350735073335000733350007070f0f07070f0f07070707070707070705070507050705070307030703070307030500070305000700070007000700070000000700000005fff00005fff00005f0f00005f0f0000 else 0xb0a0a0a0b0a0a0a0b000b000b000b000b000a000b000a000b0000000b0000000afff0000afff0000afafaf00afafaf00afaf0000afaf0000af00af00af00af00af000000af000000aaff0000aaff0000aafafafaaafafafaaafafa00aafafa00aafaaafaaafaaafaaaf0f0f0aaf0f0f0aaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaaccccccaaccccccaaaaffaaaaaaffaaaaaafafaaaaafafaaaaafaaaaaaafaaaaaaaeeeeaaaaeeeeaaaababaaaaababaaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0000aaaa0000aaa8a8a8aaa8a8a8aaa0fff0aaa0fff0aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aa8aaa8aaa8aaa8aaa88aa88aa88aa88aa888888aa888888aa22aa22aa22aa22aa222222aa222222aa20aa20aa20aa20aa0a0a0aaa0a0a0aaa00ff00aa00ff00aa00faf0aa00faf0aa00aaaaaa00aaaaaa00aa00aa00aa00aa000a00aa000a00aa000000aa000000a8fcfcfca8fcfcfca8a8fcfca8a8fcfca8a8a8a8a8a8a8a8a888fccca888fccca888a888a888a888a8888888a8888888a2a2a2a2a2a2a2a2a2a2a0a0a2a2a0a0a2a0a2a0a2a0a2a0a222a222a222a222a222a000a222a000a0f0f0f0a0f0f0f0a0f0a0f0a0f0a0f0a0ecf0fca0ecf0fca0b0b0b0a0b0b0b0a0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0ffa0a0a0ffa0a0a0f0f0a0a0f0f0a0a0f0a0a0a0f0a0))) else (if page < 9 then (if page < 7 then 0xcfff0000cfff0000cfcfcf00cfcfcf00cfcf0000cfcf0000cfcccfcccfcccfcccf8acf8acf8acf8acf00ff00cf00ff00cf00cf00cf00cf00cf000000cf000000cececececececececcff0000ccff0000ccfcfcfcccfcfcfcccfcccfcccfcccfccceeeeeecceeeeeeccccffccccccffccccccfcfcccccfcfcccccfcccccccfccccccceeeecccceeeeccccdcdcccccdcdccccccccccccccccccccccc00cccccc00cccc8888cccc8888cccc4444cccc4444cccc0ccccccc0ccccccc0000cccc0000ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc888888cc888888cc44cc44cc44cc44cc0c0c0ccc0c0c0ccc00ff00cc00ff00cc00cccccc00cccccc00cc00cc00cc00cc000000cc000000c0f0f0f0c0f0f0f0c0f0c0f0c0f0c0f0c0f00000c0f00000c0ccc0ccc0ccc0ccc0c0f0f0c0c0f0f0c0c0eaeac0c0eaeac0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0c04040c0c04040c0c00000c0c00000c000c000c000c000c0000000c0000000bbbbaaaabbbbaaaabbbb0000bbbb0000bbb0bbb0bbb0bbb0bbaabbaabbaabbaabb00bb00bb00bb00babaffbababaffbababafafababafafabababababababababababa00bababa00baaafafabaaafafabaaabaaabaaabaaaba30ba30ba30ba30ba00ba00ba00ba00b3a0f3f0b3a0f3f0b3a0b3a0b3a0b3a0b3a0a0a0b3a0a0a0b0b0b0b0b0b0b0b0b0a0bbaab0a0bbaab0a0b0a0b0a0b0a0 else (if page < 8 then 0xf000c000f000c000f000a000f000a000f0005000f0005000f0003000f0003000f0000000f0000000efef0000efef0000efccefccefccefccefaaefaaefaaefaaef00ef00ef00ef00eeff0000eeff0000eefefefeeefefefeeeeefefeeeeefefeeeeeeeeeeeeeeeeeeeee0e0eeeee0e0eeeee0000eeee0000eee0fff0eee0fff0eee0eee0eee0eee0eecceecceecceecceecccccceecccccceeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaee00ee00ee00ee00ee000000ee000000ececfcfcececfcfcecececececececececcceccceccceccceccccccceccccccceca0eca0eca0eca0eafafafaeafafafaeaeafafaeaeafafaeaeaeaeaeaeaeaeaeac0faf0eac0faf0eac0eac0eac0eac0eaaafaaaeaaafaaaeaaaeaaaeaaaeaaae888e888e888e888e0f0e0f0e0f0e0f0e0e0ffe0e0e0ffe0e0e0f0f0e0e0f0f0e0e0eeeee0e0eeeee0e0e0e0e0e0e0e0e0e0e000e0e0e000e0e00000e0e00000e0a0f0a0e0a0f0a0e0a0e0a0e0a0e0a0e000f0f0e000f0f0e000f000e000f000e000eeeee000eeeee000e0e0e000e0e0e000e000e000e000e0000000e0000000df00df00df00df00ddddccccddddccccddd0ddd0ddd0ddd0ddccddccddccddccddccccccddccccccdcdcdcdcdcdcdcdcdcdc0000dcdc0000dcccdcccdcccdcccdcccccccdcccccccd0d0d0d0d0d0d0d0d0d0c0c0d0d0c0c0d0c0d0c0d0c0d0c0d000d000d000d000 else 0xf8888888f8888888f7f3f5f0f7f3f5f0f5f5f0f0f5f5f0f0f5f0f5f0f5f0f5f0f5f0f0f0f5f0f0f0f555f000f555f000f3f3f300f3f3f300f3f3f0f0f3f3f0f0f3f30000f3f30000f3f2f2f2f3f2f2f2f3f0f3f0f3f0f3f0f3f0f0f0f3f0f0f0f3a2f3a2f3a2f3a2f3a2a2a2f3a2a2a2f333f000f333f000f3330000f3330000f2f2f2f2f2f2f2f2f222f222f222f222f2222222f2222222f1f10000f1f10000f1f0fff0f1f0fff0f1f0f1f0f1f0f1f0f1e0f1e0f1e0f1e0f111f000f111f000f0ff0000f0ff0000f0fefefef0fefefef0fcf0fcf0fcf0fcf0fafafaf0fafafaf0faf0faf0faf0faf0f0fff0f0f0fff0f0f0fefef0f0fefef0f0fcfcf0f0fcfcf0f0fafaf0f0fafaf0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f0a000f0f0a000f0f05050f0f05050f0f03030f0f03030f0f03000f0f03000f0f000f0f0f000f0f0f00000f0f00000f0e0f0e0f0e0f0e0f0e0f000f0e0f000f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f0aaaaaaf0aaaaaaf0a0ffaaf0a0ffaaf0a0f0a0f0a0f0a0f0a0a0a0f0a0a0a0f050f050f050f050f050f000f050f000f030f030f030f030f030f000f030f000f0303030f0303030f010f010f010f010f0101010f0101010f000faaaf000faaaf000f0f0f000f0f0f000f000f000f000)) else (if page < 10 then 0xff00aa00ff00aa00ff00a000ff00a000ff005500ff005500ff003300ff003300ff003000ff003000ff000f00ff000f00ff000000ff000000fefefefefefefefefefeeeeefefeeeeefefe0000fefe0000fefafffafefafffafefafefafefafefafef0fff0fef0fff0fef0fef0fef0fef0fef0f0f0fef0f0f0fef0ee00fef0ee00feeefeeefeeefeeefeeefaaafeeefaaafeeef000feeef000feeeeeeefeeeeeeefeee0000feee0000fee0fee0fee0fee0fee00000fee00000fe00fe00fe00fe00fcfcfefefcfcfefefcfcfcfcfcfcfcfcfcfcccccfcfcccccfcfc5454fcfc5454fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcccfcccfcccfcccfcccecccfcccecccfcccccccfcccccccfccc0000fccc0000fca8cc88fca8cc88fc00fc00fc00fc00fbfafbfafbfafbfafbfafafafbfafafafbf0faf0fbf0faf0fbbbfaaafbbbfaaafafafffafafafffafafafefefafafefefafafafafafafafafafafa00fafafa00fafaf0f0fafaf0f0fafaaaaafafaaaaafaf0fff0faf0fff0faf0faf0faf0faf0faf0f0f0faf0f0f0faeafaeafaeafaeafaeaeaeafaeaeaeafac8fac8fac8fac8faaafeeefaaafeeefaaafafafaaafafafaaafaaafaaafaaafaaaf000faaaf000faaac888faaac888faaaaaaafaaaaaaafaaa0000faaa0000fa00fa00fa00fa00f8f8fcfcf8f8fcfcf8f8f8f8f8f8f8f8f888f888f888f888 else (if page < 11 then 0xfffefffefffefffefffefff0fffefff0fffefefefffefefefffcfffcfffcfffcfffbfffafffbfffafffafffafffafffafffafff0fffafff0fffafafafffafafafff8fff8fff8fff8fff3fff0fff3fff0fff2fff2fff2fff2fff1fff0fff1fff0fff0fffafff0fffafff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0fff05550fff05550fff00000fff00000ffeeffeeffeeffeeffeeeeeeffeeeeeeffecffecffecffecffe0ffe0ffe0ffe0ffe0e0e0ffe0e0e0ffe00000ffe00000ffcfff00ffcfff00ffccffccffccffccffccff00ffccff00ffccccccffccccccffbaffbaffbaffbaffaafffaffaafffaffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0f0affaa0f0affaa0000ffaa0000ffa0fff0ffa0fff0ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ffa00000ffa00000ff8aff8aff8aff8aff88ff88ff88ff88ff888888ff888888ff55ff00ff55ff00ff50ff50ff50ff50ff505050ff505050ff33ff00ff33ff00ff330000ff330000ff30ff30ff30ff30ff30ff00ff30ff00ff303030ff303030ff22ff22ff22ff22ff20ff20ff20ff20ff11ff00ff11ff00ff10ff10ff10ff10ff00fff0ff00fff0ff00ffccff00ffccff00ffaaff00ffaaff00ff30ff00ff30ff00ff00ff00ff00ff00f000ff00f000ff00ee00ff00ee00ff00e000ff00e000ff00cf00ff00cf00ff00cc00ff00cc00 else 0xfffffffafffffffafffffff0fffffff0ffffffccffffffccffffffaaffffffaaffffffa0ffffffa0ffffff30ffffff30ffffff00ffffff00fffffcfcfffffcfcfffffcccfffffcccfffffafafffffafafffffaaafffffaaafffff0f0fffff0f0fffff000fffff000ffffeeeeffffeeeeffffe0e0ffffe0e0ffffe000ffffe000ffffcf00ffffcf00ffffccccffffccccffffc888ffffc888ffffc0c0ffffc0c0ffffc000ffffc000ffffbabaffffbabaffffaaaaffffaaaaffffaa00ffffaa00ffffa888ffffa888ffffa0f0ffffa0f0ffffa0a0ffffa0a0ffffa000ffffa000ffff8a8affff8a8affff8888ffff8888ffff3300ffff3300ffff3030ffff3030ffff3000ffff3000ffff2222ffff2222ffff1100ffff1100ffff1010ffff1010ffff0aaaffff0aaaffff00f0ffff00f0ffff00eeffff00eeffff00ccffff00ccffff00aaffff00aaffff0000ffff0000)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x2698007000903 else 0
  | 4 => if page < 2 then (if page < 1 then 0xaba002e4757400560df34788dc4f30e10e3a925b19e33cc38310e13800621d48f50af4ac24315e53cc382b8eae800571cf30e09a3aca0010873c9181e0e6575c384801203e7c0023f7cf8004c0eef0007cddce0016acc0d002dd979a0054d2e5400b8ea9380171d347002b4802600561004c009c2009801354013002007c2600400f7cc009a1d798013cbac7002a8738e004f2ba1c0095151d0012a245a0026c47b80056441cc0047878e000f98dfc0025e19f2004f2309c007b457e001270afa001f314f8003e628700086c3858014106a700279048e0042607ac009e40c38013c814700279024e000012ff4000025ee800005a2f00000b31e0000108ec0000210d80000197b0000023760000039f80000047780000086f else 0x27984e007cd1eb8ea4a7e1e7ceddb62b2981699e613801e65a679922136b530b02007a9d747a7984e006b4b2b02b297a005a6e3ac20a6b569aba6f801ad5a6b29ae006b569aba51801ad5a6ae922006b569aba44801ad5a6ae8c6006b569a5a13801ad5a67e84e006b5699ee13801ad5a6ae801f36b5699e61c75dad5a6a8801d76b5699e613739ad5a679871ad62d699e61c6b5755a67984dad5a533a12136b5694c2ae801ad5a530b6a85879f347aae801ad5a51e9e6136b56940eae801ad5a4d29e6136b5692f28484dad5a4b9) else 0
  | 5 => if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x16fe2d7c57f8abf153e29fc52f8a3f13fe277c4df897f12be24fc42f87ff0fbe1e7c39f871f0dfe1b7c35f869f0cbe18fc2ff85df0afe14fc27f84df097e127c22f841f073e0d7c19f82ff05be0afc13f825f047e087c0ff81df037e05fc0af813f023e017e5eebcddb69f096e10d99db237639f8427801f else 0xd2fe8ff43f9ffcefe57f23f85fc1fe07ef7f79fbbfdd7ee7f71fb7fdb7ecff61faefd6feb3f53fa5fd27e8ff45fa1fd07e7bf39f9bfcd7e67f31f97fcb7e4bf23f8dfc5fe2bf13f88fc3fe1bf09f83fc17e07f01f7ffbf7de3ee9f73fb7fdb7ed9f68fb3fd8bebff) else (if page < 3 then 0xc67f15fc4ff11fc2ff09fc1ff03fc07efffbf7efbfbe7eebfb97ee3fb7fed9fb1fea7fa97ea3fa87e9ffa77e93fa47e8dfa2fe81f9f7e7bf9e7e73f9bfe6df9a7e67f997e61f97fe4df917e3ff8f7e33f8c7e2ff8b7e29f89fe25f88fe21f857e13f82fe09f81fe05f72fdc9f6e7da7f else 0x95ff2a7e50fc9ff937f267e4afc93f923f23fe46fc8bf903f1ffe3efc6df8d7f197e31fc5ff8bbf16fe2bfc53f8a3f137e22fc25f843f06fe0afc0df817f027e03fc05f803eff7dfcfbf7f7d7efa7df3fbe1f7bfef1fde2fbc1f77beeefddafbb3f763eebfdd6fba9f74fee97dd1fba1f73fee77dcdfb1bf)) else (if page < 6 then (if page < 5 then 0x25435788a1abed40c9f65064f6f43279d8193e480bbd2285de9102ef4741779e20bbcc405de9782eecba173dc60b9e9585de1002e7da014bd000a5f2404de1c826f4c00d750706b730033d97819edba0cbc7d065e3b033d92017f3e208bc38045f2f48bcb765e6ccb07e66075f35840139ca009be6a7f25e1cf83b8e7c97867cd5d000c00affe0057df002bdf8015dfc00aebe00571f002b6f8015a7c00acbe00561f00278f8013afc009cfe004e5f00271f80137fc009bbe004dbf0026cf8012d7c00967e004b1f else 0x9bc427c90213e00109ef9884fa7c3f7cf21fbdb60fdf6f87cfb743e7b501f3c7d0f9e3707cfb2c3d7b6c1ebe5e0f3b39079bb1c3c7d1c1e3e790f1efd078f7d83c7be21e3de90f1ebd878f5dc3c7a1a1e5ce70f1e66079b2f83c792a1e3c900f1e46079b1883c7cbc1cf5e60e7b67072fb24397be21cbd7b0e5e74072f33439d9681cf87d0e5e39873e98038edb61c3ec30e1f3b870f9d8387ca21c3e2c0e1f09870f84838dbf61c3dd90e1e4a070f24c38790a1c3c6a0e2e33870f110387db61abe790d5f0986bb) else (if page < 7 then 0x62c67db0433ed7819f6bb8cfb43467ba0e33ecce19f65c8cfb2d867d96433f88719f63d0cf71cc67f400315e5415fd228afe7cc57f3d62bf9ea15fcf48afe72057f3162bf97515fcb88afe97857ecc22bee8415eeb08afe57857f2b82bf95a15fc7e0afe3ec57f1ee2bf8ce15f6590afe29857f11c2bf87715fa398afe5d455f2b42af8f115773309bd9784deb6a26f65413770709bb68c4de9e226edf312faaf097e3ec4bf3e223bd9211dea088ef24c477db8223ead111ef8888f7a8447926223c8f111ef5086f else 0x62ca0f252507928283cf413dd7089ed9e24f6ced27bb2412fe9e48ddbe646edea2376f491bbac889dcf244be132276eb913b75489dcc043f6b021f71510fba0c87bc3843ee1221f6ec90fb36c87ecc03ff5c51ffaed8ffb75c7fdcc039fa5e1cfd240e7e91473f40039f9fb1cfcf98e7e65073f32639fa5e1cfa980e7e4bc73f23c39f8ef1cfc770e7e3ac73f17239f8b61cfc560e7e1dc73ecbc36765e19faf68cfd9e067dca833ee4e19f7240cfb91467dc8233ee2f19f7120cfbb30677c1433ee0519f6f50cf7))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x93cc6dc76636e0e31b6f118db764c6db82636da631bad298dd68cc6db3c636d7a31b6ba98db520c6da14636d0631b67918db3c4c6d9b46374ce31b67898bb3c4c1dd645eee352f773c97af84cbddb3a5eed9c2f7709979b914b9f4bc5cf5e62e7ae2973d6c0b9ed0e5cdece2e5f0e173b85cb9dbae5cedab2e7ad4973d4b8b9ea0e5ced012e5e7a173b388b9ec8a5b7a5e2dbb6e96cf678b6dbf65afab02cbd4f965e7ecb2f2a85978f72cbd2415de384adec90567a452b3cc4159e978acec38566cf52b3c78943b else 0x91530f3ba9879884c3cb6261e97930edaa983e1c4c36b3a61e9152ff4bc97f6004b3cfda59e95124f2a8927a4847fcf123fe5311ff4bc8f761c47b6f122dea850abaf2846ee341f74820fb9e507dbf683ed7841f71e20bb51d05dc2681ed8b383b4f9bfd72cdded486e769f353cf51a9d688d4ecde69766034baf99a5d6a0d2ec8a68f9c9343a929a1dac0cedd3e676e7933b6fd99db6e4cedb70676d5433b74f997bac4c9dca264ed4732772898fb914c6f4bc6375e831bae298dd6d4c6ed70636eb031b74998db) else (if page < 11 then 0x9bdd7dc90ebee2275f710bafbb69d77d06ebde8275ef0e3afb849d7dc08ebee0175f6fdbafb7ddd7dd54e75eda739f09b9dbac18bdc38c5ee60623b2d301b95180dc6ac06e665d77522c9e64962f53eb0f9c9547d37a9fe9214ff3e6a7f65e53bb4fa9be63d4bf490a57a6652372a291b80148dbf6a46e62507728283b90941ddbaa0bed6505f61282fa65417d22a0be0f507704283b70941dabea0fa13503722a79e7893cf3109e79754f3d2f279d8393cdb829e6d5e4f3d4e2677b75337c2699ee484cbd24261e else 0x981ceebcce776a471fafcb8fdb61c5ebe6e2f600713afdb89da91b5ed48d9f6606bfb71db6fb86d37dbb673ed9b29f66d94fb4ec97db9633eddb15f4bc917a2248bdaf243ed5921f6ec8afb4e317c910eee4887376e425b9e212dcdf096e4884b756421ba7e10dd71056eb082b72a415b94607dc71036eb081774b4017a3a00bd17005eda801f3940179ae007c31006e15803709c01b84a00ddbafdbece7edf663f6fb25fb7db4f9be1c7cf7093e7b841f3dcccf16e7876772a3b3b84dd9dc00ecee7875f7393afb)) else (if page < 14 then (if page < 13 then 0x8007319f4fd8e633eae39e4623be68f0c5ca91f315f9584a82bea797a857b5633c8ae7ac20015e6ac9ee2bda5419c57d3e62f0afc95067157571cf2269e6619c4dcd3f2a07eeb4e480f9d3ccbc1e365e84c3cccf309878b84df10f173cbd41e1e791e83c3d652407339e6130e4f591721cce131f4395ccaf9870d84e000e1709bae1c2dcb24c386cf2300707b4e480b9d594bd00468484e001cf3098723002dc983a005652f7400ac25ee801364bdd0026697ba004c12f740097a54e8012f491d0025e917a005b118f4009960fe8013341dd0025e83ba004bd007400981ffe8012f3ffd0025e7efa004bcf9f400b61e8e801523cfd002dd79ba004c0f37400801e6e800fdbcdd001f379ba003f6f2f400981d7e800f33afd else 0x7edf347b8f9bb28f71ea75d1ee3e6e723dcac20047a73cc0083ce487ccd2e565001a539e60033a73cc2664ae9f950c6d4a8fc18da951c731b2e3a5a6365c741cc6cccc7898d9980f131b2e29e26365b13c4c6cb5c7898d9580f131b4951e26369293c4c6d5bb591733aca482e676ec265caeb2800b99d610017339819d2e73481e25cceb23bcb99d650016d39e6002cad243e65672b0800ac9b1678939a84df12256f9a3c44f1d771c87cdc73c90e77cd1e21f8f523c43f11e23c87e565000ff37cd1e1ff92f40039f25e7ec73e5bafd8e6e800771cf8fd8ee39f2a499867ccf32f0cf997a0019f32f3f633e6b0800679d09000cf3b75fb19d6f9a3c33f26631867cb6a630cf968cc619f3098f433ce001e8679bf63d0cf3) else (if page < 15 then 0x7cdd747887c565003f639cadd9e60019c771cf2fd8ce3b8e79318671cf3098f4338e7984e0015c73cc263d07839e60019c3c1cf309c001c8e7984c670e46004bd22c01c0025e915fbe00130490f9f0007cdc762f8005bb6c4c0d002d8b4e606801534cb07e400a926683b2005652f4015002dd97a0068013043500640097a138032005bb2f3f6d00213801e6c80130400ebe400981f375f2003e6ebb8f9002e3ac29f380171d494f9c00aca6f80260056328c013002b09220098015948b004c00aca4480260056518c013002dd84e00580167427002c00b321380160059309c00b0027980600380159400fdcc00ac2007ce6004e5003e73002e39e5d7380155400ebcc009e60075e600400f53af3002b2801ce980171cf2c59c00aca006226005c73caea7002607cd4fe001003e6a7f000b8e79520e004f30029130025184d41d0013cc26a0ac0084d795056005650026730024884d30d0016ec26982c00ac2004c26004def9a3dc else 0x2d8aca608023594bd003f71aca60801f38cf324427000e798721380073cc27003f639e613801f31cf309c00980e13801f347b1003e6eba3d89e6138011e1cccc59e26361c762cf131b171cf27898c371d293c4c6c565304005cc67984e002e473cc27001583)))) else 0
  | 6 => if page < 31 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x2bfe567ca8f941f27fe4f7c9df939f25fe48fc89f911f21fe3ffc73f8d1f19fe317c59f8b1f15fe2afc53f89bf12fe1f7c3cf877f0ebe1cfc38f86bf0cbe187c2ef85bf0b3e157c29f851f09be127c21f83ff07be0efc1bf835f067e0c7c14f823f03be067c0af80df017e027c03f803f97bb0e6d07d8e7e else (if page < 2 then 0x807eff7dfcfbf7f7d3ef7fde2fbc3f77feecfdd8fbaff73bec87d8bfb11f613ec17d80fafdf5d7eb6fd63faa5f53fea47d42fa83f4ffe9e7d3bfa71f4d7e99fd32fa63f4c3e97fd24fa43f47fe8f7d1bfa2df457e88fd0efa15f40fe6f7cd5f9a9f34be657cc9f991f317e60fcbff97bf2f3e5d7cb9f96df else 0xa443c7cf21e3df10f1ebc878f43c3c7a1a1e5d070f3666879b1f43c788c1e3edd0e5f09873b1f4397db81c3e130e1e49870f0f0387c901779e10bbd5705cf98c2e79621778720bbc2385cf1042e7d940d3dbd069f584013002e9f8015ffc00ae7e00571f002b7f8015b7c00ad7e00567f002b2f801587c009e3e004e9f00272f80137fc0096be004adf00255f8012a7c0094fe004a1f0024bf801247c0091fe0048bf00240f8011cfc008d7e00469f00233f80118fc008bbe00455f0020cf80105fc0082be00405f)) else (if page < 5 then (if page < 4 then 0xac8c9dca864ee1332773018dd79cc6eb8e6375b131bb5818db950c6dc9e636e1f31b70e18db83cc6dc12636dd731b6e198db698c6eb34636d2d31b68398db3ccc6d9b66376602e7b481737674b9dcf2597a542bbd24159e62cacf438566da72b3a6e959d62c9cf2524e78f12736e390fd75c87da5243fa001cfcfd8e7e95067dc0033edfb19f6630cfb95057f3e62bf95415fc7b8afe2b057f5a623bdf311deb288ef4784779c223bcac11def9888f9e43f7b501fbe4f0f3720879ba5c3cbd981e3ec10f1f4e878f else 0x4f006f878037c2e01bf7180bf47805f85c02fee3013f53009f31804f878027ee300ff53007f2b003f85c01feb2007e17003fb6260ecbd00765e7efb303e7da99e7ec00f375f371fb6eda6fb8ecf7db167bedeb31f6c582fb32b27ca90e6e5481f7584017a5e00bd0f005ece801f66400f87200dc33006e1680370a401bb75fb7c38f9ee127cf73c3afb951d7dc00ebee54507709a83b9213cf3169e7a1c4f3707a79b57d3cf490987a1c47b6b123deb8d07dd6483ee7941f70020fb478ddebe66a75a0353b3c99db) else (if page < 6 then 0x95017fc260bfe0005fef982ff65c17fa780bfcf105fe7082ff31817f8d60bfc6505fe2e02ff15817f8780bfed8053e9e029f31814f9580a7c3c053e17029fb4c11fbe608fcc6047e43823f0f011fc00077c2e03bf71819f9500cfd4205fe5402ff00017f7cc0bfaac05fd3c02fe8f017f3600bf98c05fcac02fe38017f0b80bfdc6057df302bf5900ffa9807fccc03fe5401ff0000ff7cc07fb4003fd9701fe9e00ff47807f9e203fceb01fe6c00ff31807f95803fc7901fe3a80ff1c007f87803fc3301ff7180df else 0x4781ff8780ffed807bf5903dfb601dfca80efda006fe1e037fb8c1afda60d7eca06bf59035fa981afd420d7e9006bf3c835f9981afcca0d7e5406bf09835f8001afbe60d7dbd06bedc835f6801afb340d7d9706bec5835f5941afaac0d7d3c06be94835f4781af9fc0d7cf806be78835f3ac1af9c20d7cd806be63035f30c1af9720d7cac06be4e035f21c1af8f20d7c7006be35835f1941af8b80d7c5606be26035f1141af85c0d7ed8067f00033f31819f9720cfc3c067ed0031f0b818fdbc0bfeb205ff3302ff))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x1042ef872177eb20b7e1705bf9982cf85c167c750abe17055f51c29f9f014fc3c0a7e3c851f0b828fdc613fed809ff5904ffa9827fd4213fe7909ff3304ff84c27fc0013fdf309fed404ff68027fb2e13fd5609fe8f04ff3e027f9e213fceb09fe7084ff36027f98c13fcac09fe3c84ff1d427f8d613fc6509fe2e04ff15827f88a13fc3309ff0004df4f026f878137c2e09be6c049f0b824fdbc11feb208ff2a047f84c23fc0011fd3c08fe63047f1ac23f8ca11fc5608fe1e047f4f021fa3c10fc3c087e17043f else 0xfe85dffd85dff985dff885dff085dfeb85dfe585dfe385dfdb05dfda05dfd385dfce85dfcd85dfcd05dfcc85dfcb85dfcb05dfca85dfca05dfc905dfc585dfbb05dfb985dfb805dfb105dfa885dfa685dfa385dfa185dfa085df9805df9185df8a05df7e85df7b05df7885df7805df7785df7485df7305df7085df6e85df6685df6405df6305df6205df6185df5c85df5885df4e05df4985df4385df3e85df3b05df3905df3485df3385df3305df3285df3205df3185df2e85df2e05df2385df) else (if page < 10 then 0x47839f9c21cfcc60e7e5c873f2b039f8fa1cfc720e7e33873f19439fdbc1c7edc0e3f59071f9e038fc261c7e000e3ef9871f7c438fbae1c7cac0e3e49871f21c38f8d61c7c650e3e30071f0f038fbe61afdd70d7e1e06bf62c32f98c197ceb0c3e1e061fba02efdc4177edd0bbf6b05dfb282efd88177ec20bbf5e05dfae82efd66177eb20bbf5785dfab82efcf0177e670bbf3305df9942efcc8177e630bbf3105df9802efca2177e480bbf1b85df8d42efc4e177e250bbf0985df83c2efc0e177e020bbf0005df else 0x5d83cfae01e7d5f0f3eae879f5643cfab01e7d560f3eaa879f5503cfa8e1e7d410f3e9d079f4c03cfa461e7d210f3e8f079f4743cfa381e7d1a0f3e8a079f43c3cfa1a1e7d070f3e73079f3843cf9b61e7cd90f3e6c079f35c3cf9ac1e7ccd0f3e61879f2e43cf9621e7caf0f3e56079f2ac3cf9541e7ca70f3e4e079f24c3cf91e1e7c870f3e3e879f1ec3cf8f41e7c710f3e33879f1643cf88c1e7ea10efe1e077f0f03afdba1cfed30e7f2a073f92039fc261cfe000e7efd873f7cc39faca1cfd3c0e7e98073f)) else (if page < 13 then (if page < 12 then 0x2b04bfda623fdf311feb288ff47847f9c223fcac11fef9889fb8c3ffdb01ffea60fff3c87ff6a03ffb401ffce10ffe6c07ff9203efc001f7cd80f7f73079fb703cfda41e7ecc0f3f65879fb203cfd821e7eba0f3f58879fab43cfd441e7ea10f3f4f879fa783cfd3a1e7e970f3f48879fa343cfcf21e7e780f3f28879f93c3cfc901e7e410f3f1a879f8bc3cfc461e7e0b0f3f03879f7ec3cfbe81e7df30f3ef9079f7c43cfbd81e7dea0f3eeb879f6483cfb221e7d8f0f3ec7079f62c3cfb041e7d790f3ebc079f else 0x8007ffbe63ffcc61ffe5c8fff21c7ffc0039fdfb1cff3c8d1f95068fdc633feb219ff580cffa8467fd3e33fe7a19ff3c8cff95067fc0033fdfb19fef98cff5d467fab433fd5619feaa0cff4f067fa3c33fcd819fe6b0cff31867f95833fe7918bef98c5fac057fd482bfe9f15ff3c8aff99857fca82bfdfb15fef98aff67c57fb2e2bfd5415fe9e0aff47857f9ee2bfcf115fe758aff35857f98c2bfcac15fe338aff17857fcf22afd3c157e338abf9e453fa3c29fea4137f3c89bf3184df8ce26fea412ff3c897f) else (if page < 14 then 0x72c9efa824f7cfe27be6313df2b09dfdc64e7eb2273f53139fa849cfd204e7e79273f33139f8009cfbe64e7dd7273ee3939f6e49cfb404e7d97273ec5939f5589cfa524e7cf8273e78939f3609cf98c4e7cb9273f0012ff4f097f98c4bfcb925fe5612ffac891fbe648fdf3227ef8913f59488f98c447ee321ff5910ffab487fd4243fe9021ff4510ff9e487fcf043fe5421ff0010ff7dc87fbe643fdea21feeb90ff62c87faf043fd5621fe9e10ff4a487fa3c43fcd821fe6310ff2e487f95843fc9c21fe4790ff else 0x594b9fa785cfd302e7e95973f48cb9fa3c5cfcfe2e7e78973f3bcb9f9c25cfcc62e7e61973f800b6fbf65b7cc62dbe5c96df9e4b2fd64577e542bbf0015df4f0aef9e2577ee82b3f5e159fae8acfd6a567eb22b3f58159f9e0acfcc0567e482b3f17159f888acfc38567e012b3f00159f7ecacfbae567dca2b3ee3959f700acfb62567da72b3ecd159f660acfb28567d8b2b3eb6959f588acfa82567d3d2b3e98159f3f4acf9e2567cef2b3e6e959f2e4acf95e567eb22a3e56151f6f4a0f98c507da827fe9e13ff)))) else (if page < 23 then (if page < 19 then (if page < 17 then (if page < 16 then 0x580c6fab6637d5931beab98df558c6faa8637d4131be9818df4a8c6fa52637d2731be9018df478c6fa34637d1431be8618df42cc6fa0e637cff31be7d18df3e4c6f9f0637cf331be7198df374c6f9b6637cd431be6518df324c6f990637ee3317e6318bfa84c1f98c60fcc62ffedb17bf360bdfc005e7da82f3e63175fb78b9fdba5cfed82e7f69973fb28b9fd925cfeb22e7f33173f980b9fca85cfe482e7f1a973f84cb9fc005cfdfb2e7ef9973f6fcb9fb6c5cfda82e7ece973f65cb9fb285cfd8b2e7ec4173f else 0xa38c6fd18637e8a31bf4398dfa18c6fd02637e7f31bf3e98df9ecc6fcf2637e7831bf3018df950c6fc9e637e4831bf1e18df888c6fc3e637e1c31bf0798df82cc6fc12637e0731bf0098df7ecc6fbf0637df731bef718df7a8c6fbce637dd731bee618df724c6fb8e637dc331bedf18df6f0c6fb76637dba31bedc98df6e0c6fb6e637db231bed898df6bcc6fb58637da631bed218df688c6fb42637da031becf98df668c6fb28637d8f31bec598df620c6fb0e637d8631bec118df5e0c6fadc637d6a31beb418df) else (if page < 18 then 0xac914fd428a7e79453f00229f55914fc0088fd3c447e8f223fac90efa3c877ee341ff5920ff9e507fc0083fe0040fe8f207fac8defb506f7ed8377f699bbf7ccddfb506efd65377e8f1bbf9e4dcfca86afda8357f719a9fa98d4fcf26a7df3353ed01a9f62cd4fc90697e0034bf3c99dfac8c9fd4264fe54327f09993f800c9fb7a64fd56327e9e193fba0c6fdce637ee631bf7218dfb8cc6fd78637eba31bf5918dfac0c6fd5a637ea731bf5218dfa8cc6fd42637ea031bf4f98dfa60c6fd2a637e9031bf4798df else 0xb8d3bfa789dfea64e3e9e271f4f135fc0099fd414cff00265f4f131fdbc987edd4c3f6c261fb4d30fccc987e604c3f24261f84d30fc00987dfb4c3ef9a61f6a130fb2e987d944c3eb2a61f51d30fc0097fdfb4bfe9e25ff9e524fdb08ffeb247ff2a23ff8e11ffc008ffda847fecd23ff6491ffa788ffee847bf5d23dfadd1efd648f7eb047bf2423df9011efc448f7e1c47bf00a3df8011efbf68f7dd747bec5a3df5b51efac48f7d4147be9ea3df4c11efa428f7eb246fe8f237f66916fa788b7d1e457f71a29f)) else (if page < 21 then (if page < 20 then 0x5b541fab2a0fea64f7f50a7bf7cd3dfdd09e7ee74f3f73279fb953cfdc69e7ebc4f3f58279fab53cfd569e7ea64f3f52a79fa913cfd3e9e7e9a4f3f4a279fa493cfd109e7e804f3f3e279f9e53cfcc49e7e604f3f24279f8d53cfc449e7e204f3f0e279f83d3cfc0e9e7e014f3efda79f7cd3cfbd89e7dea4f3ef2279f75d3cfb929e7dc74f3edca79f6c93cfb589e7da24f3ed0a79f6813cfb349e7d8f4f3ec5a79f6113cfaf09e7d6e4f3eb5a79f5a13cfabe9e7d5d4f3eaca79f55d3cfa849e7d414f3e9fa79f else 0xac98bfd4cc5fea362ff50b17fa418bfcf2c5fe7862ff33317f9518bfc00c5fdf362ff00311fb8d82fd64c17e7960bf00305f62d82fb1ec07e005fbf3caebf9e571fd4cb6fea15b7ef9adbf8016cfd64b5fe545aff002d7f7cd6bfd64b1fed858bf69ac5f7cd62fcf2b0fe6654bf71aa3fa8551fcf2a8fe6053ff0029ffb8d4dfd42a6fe79537f00295f9e548fcf2a27ee3507f6f283fb6141fda6a0feb2507f53283fa8541fd38a0fe95507f3ca83f99941fca8a0fe3d507f09a83f80141fbe6a0fde8507ee5a83f) else (if page < 22 then 0x8ba00fc3f007e1c803f0cc01f85a00fc29007e0b803f03c01f80a00fc03007ed37fbf003fdf801fcfd64fdfeb07eff2a3f7f921fbfc8afdfe007eff743e7fafdf3fd74f9feb27cff583e7f9e1f3fce4f9fe6f7cff243e7f8a9f3fc44f9fe217cff0e3e7f849f3fc08f9fe017cff003e7f7edf3fbe8f9feb27bfef9bdffb8de1fd42f0fe79787ef9bc3f801ddfbe6ecfdf3763f71baffac9d7fd5aebfeaa75ff50baff9e5d7fcf0ebfe5475ff003aff7cdd7fbd4ebfde175ff0039df7cdcefbaee77eb2643f71b17f else 0x99a4ffca925fedf923f6f491fb7648fdb1247ed3923f59491f9be48fccd247e60923f2a491fb8e41fd6520fee38e7f6f46bfb4e35fd971afea68d7f2a46bfa8633fdc717feb28bff2a445faca1ffd4d0ffe6687ff2a439fa860cfdbd05fed882ff33417f9220bfd3f057ede81ff69c0ff95207fca900fee0803f6fc01fb7a00fdbb007edc803f69c01fb3a00fd99007ec9803f64401fb1600fcf1007e6f803f2a401f94a00fca3007e48803f23c01f91600fc89007e41803f20401f8e200fc63007e30803f17c01f))) else (if page < 27 then (if page < 25 then (if page < 24 then 0x3c4c606b6630ea0d74c61d41addbb594013b4eb2802759491004edd84e005cf309c007aca007ee759400f9cee39e53c3d65002613ac9f347b93c3e68f72007cd1ee3e6eba3dcaca0047a771cf2631e663c4c6cb8e7898d94a4f131b5594005cceb2800ac9be68f10fcb8e7919cf3cc0033cee39e4573cf309878b9e6000f0ef9a3c1e72b2800399be68f071caca000ba73cc27000c00ba6b2f80170565f002bfacbe00573597c00adeb2f8015b565f002b5acbe00567597c00b8e78f801594f1f002ad9e3e005d32a7c00ba254f80173ca9f002e6953e005c72a7c00afe54f8015e4a9f002b8953e005612a7c00ab654f801534a9f00274953e004b52a7c0095a54f8012aca9f002e394fe004a929fc00b7a4ff8016c49ff else 0xac9650bbd332ca177a005942ef32eb285deac8fe0bbd331fc177a3d3f82ef4007f05de72cfe0bbccb9fc177ab23f82e7ccc7f05cf8f4fe0b9f001fc173dcb3f82e7b2e7f05cf504fe0bbca09fc173d203f82ef2407f05cf998f10bb67f1e01778fe3c02e79fc7505de3f8ea0b9f3318c1776543182edc3e6305dbb4cc60b9f0b98c176d973182edaca6305de3f8c60bbc7f18c173cf13182edb405885de3f8930bbc7f126173e001c82ef4003585d7ac8650baf438ca175ed31942e7cfa3285d79e4650baf000ca176d651942ef1fc3285de3f8650b9e3c8ca175c6b1942ebda62e05cf5945c0bbc6c0b81774d81702ebd642385cf998410b9f3318c0d75b13181aeca863035bb28c6069f0d18c0d6dbd3181a7b2e63035b) else (if page < 26 then 0x3e0d80f2f3c9ac1e3da03343cdd9463078f9e4c60f1ede98c1e3e1330c3cdbe656079db78ac0f1f3c9581e3e132b03cda3c56079e3acac0f3b000fa1e3ea11f03c7be63e078f5587c0f1e8f0f81e3cd81f03c79583e078f84c7a0f37098e21e6e7919c3c7cf22b878fa84460f1f2a08a1e3df31143c7a7822878f478450f1e6308a1e3cac1143c7d65000737b76000e5f0a4001cee1380039dc003e872f8006b0e6f3c8ce1cde0019439ddb8f9870fb4df30e1f09be61c3df347838ebe670870f7ccac0e3af99261c3df30f0387c910005de785970bbd53542175ea6a1c2ebda75905cfacaae0b9f69ccc173e6698c2e7ccd0b85dbaca000baf43c00175ed38002e7c2f0005db84e000bb73332e17766665c2edda6cb85cf else 0x801fb19f73c98c33ee7995057f4f2f98afeb8e7915df3cc002bde7955857f4f2aa0afe9e4f815fd3c9ee2bfa792b057f5a75908efac9f311df592ca23beb2478477d647088efac8ac11df3c3e6223e799503f7ca8d407efa9aa10f2f6f5421e3ea1a743c7d613c878fa86790f1f4fcf21e3e799503c7d6309879ba86130f3728c261e6e7984c3c7dbb00078f9e6000f2f3cbf61e3e137ec3cddbcf9878f9e5f30f1f09be61e6df37c43c7d42ab079e93d560f3750aac1e5ede5583c7cf2ab078f84d560f373caa81e3e794f03c7c269d079b7cd1e0f3b20a3c1e6e974783cbdbc8f078fb311e0f1f3ca3c1e3e134783cda3c87878f4790d0f2e8f20e1e6ea63603ced426c0797b78d80f1f3c9b01e3e133603cdb406c0797)) else (if page < 29 then (if page < 28 then 0x41cf131b7509b66376a1360c6bd206c18d7674d831b6789b0636e60800b9ed6500173784e002e770033a5cee66318b9ecc063173d950c62e774818c5cddb9318b9bb3a63173b65cc62e767898c5cee7967cb2f4a8d415de922002b3d593e65676787ccacec00f9959d7cdd72b3b71c38566eb2800acbc2700159bac9a72b3b5923c567a00478acf56475959d800eb2b3b591ba56758b318acf25263159e3c4c62b36e39e24e6d8b3189cf4cc63139d79cc6273b2a18c4e6dc33189cdb2e63139b4a4c6273c7898c4e6df371c87ebe6eb90fb7cd1e21fac598c43fa6631887eb8e6310fd950c621f6eb98c43ed9731887da526310fe3c4c621f6f995843f6007ec73f4f32a0cfbb8e7919df3cc0033ee7980067bcf2fd8cfb else 0x84d953276f9b16637ae3998c6ed433318dda426631bb3cccc637660800c6ecccdc98ddac27931b771ca8636ea6950c6dd432a18dba425431b73cca8636ed8b4cc67db16518cfb8e79319f71c38636e90800c6bcf30018d77cdd731b72a372636ea66e4c6bc00dc98d7a85a631bb2a340636ee365cc6dd42cb98dba419731b73cb2e636db965cc6dcccc598dd9518b31b6cbb16636ea1558c6f4ccab18dd9515631b727aac636ea1558c6bb2eab18db62d3c31bcf9a52637a664a4c6eca89498db65d2931b69e25263792941cc6dccc7c18dda98f831aeab1f0635d653ccc6db8e7898ddb8cf131b7509e2636e903c4c6dcf27898db950f131b6f99e2636d8b3c4c6daf07898db558f131b6949e26379293c4c6da3c7898db) else (if page < 30 then 0xb761c803769c33006ee384e00dd6309c01ba8613803724427006edd84e007cf309c00f87213803759400fddedd801fb7c27003f7bb8e1c7cf756c24f9eeb2801f3bc27003e7b9e1f375f72a3e6ebee007cdd7ddc72a279ea9a544f3d3cca89e7a488013cf54cf3a79db8e544f37534a89e6e799513cddb169a78fb8ecf4f1f6c59e9e3ee39e53c7dc70e279ba9a0f4f373cc009e5ea66813ced4cd02797a995f4f3d24400987a0079930ed65002617b3a004c1f09c00986eb27cd1eecf0f9a3dd801f347baf9bae8f76deb311e7d995923cfb8e1c47b7594008f5e978011ebd990023cf84e0047b7592c48f7ae347907dd648f20fb9e51e41f70023c83eeb2478ddecf0f99a9d951a0353b3cb3e676eb26a0c9dca8d4193b else 0x16c4c100765e801fbecc1003e7db62d3ac9f6c5a72a3ee39521cddbb594017b4eb2802f6eda7003ed8b4e007d65244017))))) else 0
  | 7 => if page < 5 then (if page < 2 then (if page < 1 then 0xba3f5d7eb2fd61f9e3f2a7e4ffc91f907f1afe2ffc45f87ff0e7e0bfc0ff807f007dfbfbe7f787eebfd8bfb05f5b7eb5fd62faa3f537ea0fd3dfa79f4c3e8ffd1efa29f41fe6efcd4f993f31be5cfcaef959f273e43fc67f8aff11fe1ffc3cf873f0e3e177c27f847f06be0bfc0bf80ffb31f0e6d07d88ef else 0x8002efbe6177daf0bbed505df6a02efb2e177d650bbe9e05df4782ef9fc177cf10bbe7585df3842ef98c177cac0bbe3585df1942ef8b8177c560bbe1e05df0cc2efa7813fc3c09fe1704ff47823f85c11fed806be63035f0f01afdb00bfcac05fe1702ffb8c0bf87805fee301fe1700ffb62d37dc70e6eb2802f09c01b9513cf4a89e6df347bb6623cf47907dccc63765431b6cb98db3c4c6dbe656751e2b3c75959dac8477dbc1e3e790f1f09879b1f03c788a1e3ed30b9eb285de3f82ef1fc173eb28026f9a3dc) else (if page < 3 then 0x360c6fc005cfcc62e7ed415dfac8acfccc567e542b3f17959f800acfbe6567dc32b3ecb959f4f0acfa3c567cf12b3e75959f318acfa784e7cc6273e56139f7cc87f98c43fe7919ff3c8affac847fca81ffee30f3f6f079fb4c3cfd641e7ea10f3f44879f9e83cfcf21e7e540f3f09879f8003cfbe61e7d6d0f3eb3079f5943cfaac1e7d3c0f3e8f079f3843cf9b01e7cc60f3e56079f1f03cf8d61e7c650f3e22879f80039f8781cfdf30e3f6f05dfb602efda6177eb20bbf3305df9502efc3e177e170bbf0985df else (if page < 4 then 0xa860bfdbd007edd803f69c01faca00fca9007e48803f09c01f801fbfd64f9fe787cff2a3e7f801f3fbe6ebfeb258bf332a3fb8d3cfd649e7ea64f3f50a79fa6d3cfcf29e7e664f3f2a279f8013cfbe69e7de74f3ed0279f65d3cfaac9e7e004c3e9e261fac91efca88f7e4147bf0023df7cd1efa788f7d3c453e8f229f47907fd646efe54353ed4193fb8cc6fd64637ea631bf5098dfa40c6fcf2637e6631bf2a18df800c6fbe6637db931bed018df65cc6fb16637d5631be9e18df4a4c6fa3c637cf831be7898df else 0x5d1597edeacbf5d565fb8e54fd752a7eb2953f534a9fa8654fcf12a7e66953f71c39f))) else 0
  | 8 => if page < 1 then 0x2b2fca9f803ef9fd3cfa3df31be567c3cf85df else 0
  | 9 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x33 else 0
  | 4 => if page < 1 then 0x19047 else 0
  | 5 => if page < 1 then 0x16c5b11c470cc330cc330cc330cc3307c1d06c1f else 0
  | 6 => if page < 1 then 0x4711c4711c4711c4711c330cc330cc330cc330cc330cc330cc330cc310cc330cc330cc3307c1f else 0
  | 7 => if page < 1 then 0x330cc330cc1f else 0
  | 8 => if page < 1 then 0x1f else 0
  | 9 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 2
  | 4 => 97
  | 5 => 978
  | 6 => 1931
  | 7 => 267
  | 8 => 10
  | 9 => 1
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
  | 3 => 1
  | 4 => 47
  | 5 => 508
  | 6 => 1005
  | 7 => 215
  | 8 => 14
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 3
  | 4 => 170
  | 5 => 1829
  | 6 => 3620
  | 7 => 774
  | 8 => 48
  | 9 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 1
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 7
  | 8 => 5
  | 9 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 5
  | 4 => 11
  | 5 => 14
  | 6 => 15
  | 7 => 13
  | 8 => 8
  | 9 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
  | 4 => if page < 1 then 0x850d001029508a400219007211201e8322cc5002408404020418a003028600104820a200040a38000 else 0
  | 5 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x808701003800a0e0008c0204080000c98206000810a043070200180001c38f0a2830000000823a0450110003070a0c0800e04002101408f else 0x43801432240820c04c801a08003460410604389000014204183818300701861c0c2800650a0700306100400c80021860914000020834382) else (if page < 3 then 0x500c180260410122002040806b80040000012040800e045800020989022049f161030002080001e34407080400904201011a008000000010 else 0x18d811200aa204241070a08a01260800108380012c00584061008c000820a16283b10c0449a1020c820444509142000a12015072008000)) else (if page < 6 then (if page < 5 then 0x42408d000808b080d904000010404401000c1870a0000e281e3c12b0298a0400004831e0c00004001800018182044c71040403060418004 else 0x120010826988801c100120600184040000f1208300040c80216146061c041032c1c10d0898a831e0420d02105090a0808722482850014284) else (if page < 7 then 0x1ce824e2c1801e288080a30201064408000000011a380a014588860a742110270582520c106123c000222468a0030b030030005d804086 else 0x41908f00a829776316080000f01001cf01027ca881400085003c5801070280001c90a3e000474e20096444c1880419e82280c503))) else 0
  | 6 => if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x10301100402010002010001020000010003070016050a0000000302021e0008000000160103010000031a002401020100000204020003020a0002090a0100 else 0x5080401051b0501081402060205080001002700000001001e0003060013000600020008010300010400060501050214000302020001080600000e1c070001) else (if page < 3 then 0x600020400002405060c0c0206000001120101000b0402000106030201150b002e0200060e0003030605010204060016070f0303090016030100000109000c00 else 0x1011f0103000202084a09000c0200000c032a010204030803000601070002000202002000000f0913010a01020814070702070d000439000600030007000101)) else (if page < 6 then (if page < 5 then 0x309030711000f00000a00020e04030f00010006022603050a0101040108081d0800040103000101000001201903020005090400000001000e35080b02010300 else 0x200050a3501090603041002000000081a0400000005040001010206021a040600030a01000c01090f00051f07130f03000e00000003000000000c0401000506) else (if page < 7 then 0x10105140801030203101100061200000e02310b000605060400020b190202000b040000020b1501000402050603020417020100060800001902010300080101 else 0x2a00091009010b3114011602020e03002200012c120000010c26030006021a00000b0614021112540500012603090500060400020713101302000f0201000002))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x20d0201001d0c0b0700060105010a01010019000e080e05000303021505000e03280b0803000412180115560c1d040a070300160200071b0006010d00230628 else 0x500021300051d31070e0c0b11040a000018030506062f0e040006001c00110e06020a0606020b10021605040003000a022b001b28000c02010918000f14020e) else (if page < 11 then 0x1030003050118010d0300072103441e0d0105000100020d1300000117020f060b0036030006040828020000003a1c02260d010713010003002c1d13001e18 else 0x405030a131f04453509031701000401000c3302000009040115000b07072530020120030a00040800020e19321d0c28050d000900060702043e031019050005)) else (if page < 14 then (if page < 13 then 0x2a2b00190b0003200f02271b000b0f04080b19290000020c0a0327010d00001f0a021404080008000d0c250e11261604062805602005060102000848001a0500 else 0x120000010c2b00000c04050c020510000015220815000801020101001006323f070400071d0000020800270002000012000421071a2d0d182230090803012600) else (if page < 15 then 0x1682006a231601251a02090833011d210b003b26095a0404000941020b01040103080109030603000626460e0003360a041400030407321203061503040000 else 0x718010301240001290107010016072f0604022805160201322125030d000e0910080f0117030a050645011d10)))) else 0
  | 7 => if page < 4 then (if page < 2 then (if page < 1 then 0x3004697044c28b0410000161c38b0638004002001200101011e04080080008400044012400126241c30300000023c000000084300060c601 else 0x10045802008107a200000180cc00020c2034e04486101809500049860a7404626081941610006043810000344011a18000021c7002a1c00a) else (if page < 3 then 0x21400006044090c08284000768300007010008000120898018207ae08949851444b860c1000102003890a0400606140001808e800004000 else 0x1c38606e088200002003e7cb94d620080140808d)) else 0
  | 8 => if page < 1 then 0x22180791003e31c0b else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x4000 else 0
  | 4 => if page < 3 then (if page < 1 then 0xa040818b4318e45c07825484058141ce17815c0312b0a802c1d01334693ca88053200e0000049620759f84309e1551292c02612820b8960e0f915d441220219288711c8e48c0000702f82e05f334809ab0190a40dc1b8cb0 else (if page < 2 then 0x280002802e08a1741a83d3526000005510c01d2454b43c0000f8c4438c29978000681102f00000000cc00240920f8658a008c0b41d8800180848d829000144c00120000002c1b51460842014c183521d980101a1449734d0 else 0x300000184002d8320b2c00000000b00000618000009d0004e4000e4d53c00868f41508002a0d81304e0000e42d4d308e00084830076000110000)) else 0
  | 5 => if page < 29 then (if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0xe746ec0f7000004104e28b7063c0b36d140000655b490878353000010645e6808000031a161d21b2eb92e7042cce100002fb600026c026ab176e4037406464c54500b8303ed9e5689c0000e4c2a9054040006cca700a741af3c0405940818000634dd00a698ba20000000cc4024a else (if page < 2 then 0x39833c0c500c82354241000000007f970700002bf27edf1d200000008742e80cbc31b05d53a600f42c346ec4922b340380534ef205658915a51e4d95c54b73926bb51a49d0b21504cf6da5946115173b3ef432e3a0c0aba37130800000e827b090278b0183252127230543160969b2a0 else 0x1a2b0a045871b6e999173e282a6300000001000ef128e5f25df4018a3fd0c0200000003f0c000314000055538e000004a0b280cd2000254700033d05c53ac00c400000001a70a9d37b3984000089433f6c747c1a1ca8536b3066039a039201ee4c648842558c40e8c07f54e421e6d6d0)) else (if page < 5 then (if page < 4 then 0x5fc00000000000d1c000000000005481504be811331cac00067a4f3045415306e096733680580ed916320000db4c2dba04c7540009e400000001f11d6c000000000706983124520a19045ca57072980001d2976a6a806f0c881960de03520c711d7004c1df6e6472e5f34e9d9f282882 else 0xf9800000008f4404c000000000000034a2ecc1af0c4440000c04c210ac5ac9bd0400000007e02c400008698ec091d80003bc146408a800000017b566431c00000000c25b0e48c410c3255b1a4ee4c6904ac0f13ee480004493273000240000005a0789b050d28ec104950000ac0a780) else (if page < 6 then 0x6e41bc66cc000000011b2d102714f1400000911bf0a558617000000059d4850c3c000000036b13bd03305043293abc3b20ac40a1a87c18b9069e27a80c0cb57349a2071d800000006c00003280d3c0000cb440000002f36f442e1062c00f0a6e1dc6c64dd60b0006a0291c520e903942 else 0xd90649b50095e806040a000000006490002980aa27840689b2310b05030000206068023f0db407f0e1e822b4cd13876301df0c742406d6007c6f398f037c01c801aeb1f68d40562df00db0630c0000002b01ae00000000000006c376a0d679520801ee0be18000b2022004e814a1))) else (if page < 10 then (if page < 8 then 0x23c022445da2c00000cec26599642f760002df3cfc2390078fb900d1b0e14dd34235b8cd449764d60e200fa69d42ae0840318074db86a1dc9be664ca519e989600a6a7ce000018a4c38075a25c39e008985b029428b0ad51fc67181812c80000008441c021000003f5c4e6ad84000 else (if page < 9 then 0xfe20001c900001b03afc05e0a6c3173285c00089688d0b80c00031100003800a223ba5b66d7e4f504eef6429bc2982942574aa140b93f3aa170e3412c0d74b4014980240f2c0b50b68c172d08a7f0d31a760b90e6204444984e44ae5091a24a706960b9bd400103ac0e020341176 else 0x45a22190c00000000714000000003c900027a6cad2d2042c25a0090400024c16e500000004cc25801c03a909708131dd43000e641de642a3779a9180006b822a0b5935509f40ff07e029b10d4f43602180000000000bad8000b6eac900003b060003630d2998449982aa25290000)) else (if page < 12 then (if page < 11 then 0xcc0000002662a20d1f0bb18b06089d9b06a02e12f000f4020813317ec211618e8b441ead8e00002bd20d59f306e5b2306d439c000000000001f6300026c69f9800042044205e00bf026299339b82683c54800055039137b40e1278c08c4bb86380ba580006901601000000026829a0 else 0x574190025040000002c822f008934e589944e1a663000000000016c51869690171313023c0770af0000000000000000000384c0000000da100020200001cd00ecc3d9d8822f088d832357c317097eb6700dac53bebc3a10d1815f1ae85ad993a6e3270c01a13b08000ed840004e40000) else (if page < 13 then 0x1ef423eaab0d80337193e4000e04baf6d2c16a0b700000ce6454413a836ac3d80629c10000000000021dbc406f59f04870bb1000000006148986dbc2bb0ef835401d6e9985ad14406681d106c278b01f5a8f0b595ea07bc10a2bf9a6b8ee0fa8064837903a0c00014437591313910 else 0xa309e1620a5566c452f604fd57b3668d850bf587602028120bc16ea60a52d107e9d6d100000004391b0000037b20003330b4c0f8641cd100eb5a80600000004c01a510598460ab087f6720b5a0288ee620740906d981f439598000000000000000001f48000efc0000c5980000002ad0)))) else (if page < 21 then (if page < 17 then (if page < 15 then 0x10600001b20b0900007b00096bb5000008871d35a4e9b66840eba2a9bb98000000020c00007c41da0f2927a0da02b4001009a689819700000000b09400092a86065980be0c5ca90045800000003c800b433f2ef0000056c00001a5a3b66be51d0441b822000000000030a67300c24 else (if page < 16 then 0x4fc1d2037920c9050000048017a1344104412c04b1a382ef0a283c7043425c8965ab7000002a13f8cea0e204000be98000c8532c178ca06685d8600a3e8f2089a9586c7524668f5a8905781e7071035c602802c0a5802e18cc1cb08d021e260900c053844e148c27e000000004680446 else 0x5c027920a835101d5d1096a18000c950000f05a586e583caadf831a03f092db79831530d0365025800002dcb2d4911b0f27058358000330b9b4177081429ea1b823e993265e9b658cc029671e027db6a15c462307a11e805c4dc701729fc05080f96b5cecf28d5b3e6e0017350001dd0)) else (if page < 19 then (if page < 18 then 0x650d46078cca0592e8730e7cbb99c1038f07e430d0de5b0c05243c206f5e5081d8fd00e081022eb4def14e10000b0c204058494c325289a18442b33b40a479a1005b64c824096d0e2b723da2807a040e00641eb1b0832419228000b310000000000083da5293f8169500012468a68000 else 0xf298250c4192a25a174c3a6a00b02be6fe0e9489d6700d394282c976b883570e9c173047866507c82c31d7994e40f019f06398616c5430e6ea4a27786c0ab634c3ac223c6870e681280b74d110b60fcd04601270f393720dcc17401c80292bdc3006cc24ce004d0430a7c8300799a142) else (if page < 20 then 0x5a12a0982649e000017c001240d200020d90243a230001b1963423394eaefc338ceb91a34fcd27d4d1d2751a8800690000a7034b2d383ca100020744b43b400003bb03592d5000017129dc1ac3000000000000000001403a34800043d8490ab00e23110000027c20e65f8019667e6130 else 0x70c5d800003370345b98000000009cccc34d1183d6be5b5909418d70d842c503883c064f048b08600ed40002670921fb6091594c1c9113809a400004512fc6000186400000001c41b330002b420001fd0620000013c1b76d201f35f3874d3b2c22e03602f40ce0736968c15a47383911))) else (if page < 25 then (if page < 23 then (if page < 22 then 0x70805544bc2e52349802629da24780593810001b70ee863664d0105ac049e7632408a008580000003c140003857530a5393901bc385803c67fec3f0340b3e0b1837f0a08a4209b9a74019ad210b11857385409a730816b00003b704a1a220c2c01f08b43036b300224d6d31780504740 else 0x7500d15708e328801e827ca8ce92af9a9305444230a443c9071c96556418903828f120e8079b44b85ca0c704379dc02a102ecab2051d0a606943c6652801618898a8618ad5762d8db8171cf662f05fca77a4225753c01810b132f6ea82ff0a30dee2f0464480982c028b191c0ad0ee45) else (if page < 24 then 0x7642a40b982d42190341058974b640854c4e743a3300026ab0001f3420e7953899e2066bdaff6e1dc2e00002b0300000002f423b0a08ea20180b421394aa36755bae10000000068ccb021c80006c841000a026b0dc41dd617850202c806d0c3cf430ac02cf011c2eb8a8c0610d358274 else 0x52cb56000013d14a8081300033a0c0813d0000263700027c0000171017418948dc36e6a0817a0b1cceda13d065ae240980e301e10c9807a20001f9b26e91e40bd131a3316e225f400004ca871a57000005104000e2245300001ab950458617c05092c5aa90123590f163daa583742be0)) else (if page < 27 then (if page < 26 then 0x7001930d74c3430001a900000ed137974c004533206b4c0006d0af1900019800002ec867402912a685fa91e1b80218c000734d221d000000b1519c0b3900538229510c1583d30001e000e80ce645c16410002de0a0516a451423002e141e40003350b78d72a104d2e0b5d52900e424d3 else 0x63580000000000e5d455008411640000bf60000b197c50000000229000011031410000f0c1e412b244d0f043cc00c83a46b8c1da6d282db773da036cd000009885dc069cc000c18000000000000d2400000000009ec0000600ad820001cf000016f000013664d4000000008e0709ba50) else (if page < 28 then 0x90d800000006793be02900411b7366a68a28e98000b101db6de8a510c5e4af600000006c8800050c000000033e38b8e1c01200c733280000f39cad02495003ce4c0006e80b410001401c884000e958000a5dbab02b803c38c80df31b989d08683b965085b237dce64700000000000000 else 0x29391a5b721e2e1200003b00c0c20a9759b7a330425b84f89594849919000010d10002866271f6c60611c010002140f3c2da1a1d95785348f6092dfaa2475b3e2))))) else 0
  | 6 => if page < 57 then (if page < 28 then (if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0xacc1649ba10af6cc9c02ba54569da1b2c2221f6a3e837da4b4c06812ba6175401008740ec635f001c013a0962d47c0f88f4a0d1838d292f83600e30535597b08000e7a0210daa8aec0b12c000000004007ae600034198000a780ed42888010775f27ec2ad83310ec00128b5b8b621a1400000ef85d53 else (if page < 2 then 0xef8000017e82661bcc4761d5b337203c2c00005900c11eb818082d013140548da795a4b847022c7d4501688c90170cdc19948b3d89120bd0d03b9d031241686ee7300007341de9f1f2560369a234a4b1067542a409d0000000009c4400017c80000eb217b8000000000960b80f3d8f2f1d2472dd14285ec0 else 0x1b58000000006ae78fc347b4824b5259f075704dc950c46218cc8173416c083072906180840209835d130d3dfc06002c303f509dc07a41470718025cc0a82cc810a093eaa90a55d405034812d041598520a01582c30a8152666a00001e580610334814400000000ee840001709a131744000022701be0)) else (if page < 5 then (if page < 4 then 0x22013c4c0003cf00001448c000000048200001da88000d7e54a412197016430551840004ef90001cf58000296202e0000336af140124425cb64856b000000002f680000d6e00000890000046f4b7c38902290ef098608773000000017f4163a9ed1cac38ba82f03e5027a03bc08105a40c44000032c00000 else 0xae481a69d935f92e14cb3c58f4e437c18e21410d359d73252d642e59903656e1030158850477002fcc26214df05ed5c7009c31c7423310d437536a534f815d96f0874a6e5e0a5440000ae02aa5156c7ebe5e00001b741fc824270f60570c00000003742000000016649b331280000776059e4344c3135d31) else (if page < 6 then 0x300000000005641cd003707480000019286e30000cac0d18164971306180b7814e205468480ba030f0000058612bcb1b57226f000e54021d2d6271815681ab800a0d66029c2579dfb4032c154352aa4a14e60cb84ff82120d82536daec25cc0dee0c8d9730800026a7aa8cbb842c188808e86b3175e3 else 0x942953837e800000000d0076d82d10000000000004130000001c25325bc2000154035e4ac81b16b9fce6e00000356cd9c800037fb8854b84b75033510000350000000005b0279c80006230000000022e80000000000000005a230001d90400038400e60e6197103480ca6c0000000240025ec5e845482ac0))) else (if page < 10 then (if page < 8 then 0xa8a0000338280000000f84330155f2e12266dba4132d29cd18f8198180006f940000699d94051e27918a2969d1e6e7bdddfd86ba1540850cc8f15cc89b869108b88bc323595d11853051596ae45441de81d90d0405d1f0dd5f4035415ee074b08831be1c080cf0b2f64c0dbe84000000000006d2c98864e2 else (if page < 9 then 0x13b8f0ca01c06c414b5b1fa000000011f015fb1d408360000000000000000000000018d11a120c81e5300005ee20003c1a09a0928cd1034195340abc24a426b800000000d5c40004c22a0c0c88c1405a72a6c0e90f02048d00b01ca8065868949c8194c25f83c401aa1a158f90d6c0b921ce600000952 else 0x29a1c3a0000703712c12f833606c2196c67601bc8084267c03c5a31c34524fe0000000000004aa00002bc82a860000eac6ef800000000b9c1d380b04d5c20001899e410d443d4c1239532801a1af9ac62cae4df648c9b7b8a6b062f2a981988da22bb8ad34d080204001a35e2b16d1bda04a175c12824753)) else (if page < 12 then (if page < 11 then 0x2ec9bfc23d90000bf60942505048b62c817f0213b6f60e582d4065388ed6c3a24b0210804ea762000006b863804f491f419684e722242ccdc0ea5986652d5a81eb059a43e00fedb8d070f026cd162b70800009466000166864d2a9c34b01a5b27810757a6ce445c42161212e429d02cc0e4acff6a3c86e63 else 0x502503e1da95ce3af8521c0c6a3c0029052edde084ae62d49dc881d0a38747a9db47a1c53b014853e021509d62258c2d02c3b65a144c19fcbc356b504dc1559bac16100d360f502ed85c206801c25baec1140892398887004770ada20ee99c85650d6c10d02971b2438020564282543e13446b48719572b6) else (if page < 13 then 0x203152040003920980c09e7c205ec618a1740268273a90f0c69072396aa22c056284000629a9e03d1cdef06960570031021a34cf39080b6953ca54d1ebc498585e867749d8c44db8582482a7e096800b12b04d405229b880168063f25a07c4836e872e00a251b90451efe115eb7b15d9076e1c1054e32cb0 else 0x352ef0228851e9eca0e2c20a01bb14840998a6994b8ab3005f900001c61000187ea894f4564a4083c95486260ef6ee4000000000e6a14b18691f6e68fe000000002840d321aa8111013900000038800020c60000c95f5f800000000f66aae03f20c2e08442d312bf4ae0cd34a179000019486fc043c8ee1)))) else (if page < 21 then (if page < 17 then (if page < 15 then 0x117c32b827e450e0ccc09016d307e00a9d3aa80000dc4c0001ce337400000000008099f6000000000000be4f064940000063b0dc400001fc032b03941416a7d00000000000000000000000130d0000000034cc6c417a85b50ecd07a8b088f1d0a016e04400000006000c200000000077e803c3ba060a7 else (if page < 16 then 0x9508d25a5e81757e64102c40000000ceca3ac71ad18b2230400009d3bb6007548049512a1600bd48e998b31f69ef41650426d35f090c01d0f32833b178220000000326323e47b0000070310001964925b0db000214380090c9530000718096b57707d41b69811be4f0ce48f0832e258d003e00002ee26550 else 0xe9e600016130000e59246c00e8e3c0c3c34fc73703ba6000000022796b24bec001cf5d425542e020002e7146fabc40e0ee2d5a79059e9720de404dc8e92684c126859e34d00c9da4601244e400ed905f083f0a352112a9c84ad092e099827a03fd252e8bc082e26eb0a843a8c010044310001b9080001eb2)) else (if page < 19 then (if page < 18 then 0x2b80b61382b0a4300010404000585000001f58000587038adad4e58005445a60358836900000000480d06000003b655888d3b6f300000000000057a00c015a980000000cfc600009b80000ea8014d6e415840704318c00000000afa40000000304988034e0000000000001ae8cb588000e85217500000000 else 0x38880000c80144e5c0d1970d18879c0cec75673e05ac12230c6aa6b8a0c0d4d877b0000059437e0690444e15842abb6850712c240af5b46ea2060db82b58872653cc44c0e6819d9098057425883189dee4fe8272c2cb4dca0f18d1cd4d98000067a8e0072801d208f833f2c380ae80c459839d0c0) else (if page < 20 then 0x4ce06bc02b05306000100ce1c8c68647401e00e9943d090ec0001ad880001aa7a7047083f103aac9241cc80e3022e0b68630875d0000000031d066f0ef217c405604cd20000ee19ab0800031cec54d7f200000000000195300000001950213ca9c182c0fd4604041a0000115edd2b5c780001711abd15824 else 0xcc8c640736065c531c2b81290011c8000000036a040c15d9057814d600014080000448920800003008b0a6c788f2815c98000916026200005270000139ce7e2b45000010ac2748a0006006d2c1e2d67f073a8188009d53e1ae06000014350ea6040880854014638f318c2ad81ac158bc13fc39646122))) else (if page < 24 then (if page < 22 then 0x3f1b2f800009c019d46d902f709d4c410b348501016ea00022180240cb8108034999c360001530788400000c6d3718d7560ba000000000002ff3e78c00000000000b721875b0b015a00001a91000000003ae200013822090de2000030281322b240a2dda4361aa84e4da19e4b2c505f000002b3861c2 else (if page < 23 then 0x8d6000026a480009409d2c8b38672500006e1a33c8191cdeb119800037700001a2940003e609368564c0004312d9e000011293cf6b16800000000000b684e8dae680000814068440003c700000aa814501e360000e51800000000000e94000000005b2082d000000007c856edac1a4ce43440000351a0000 else 0xf7280001e604da17e45df87036cac97a829932975000086de6bb4f50000000006398ad0000064c24ea4c92798567c3a904462000000039b832e0e4a0f6134a9af3a47b41948e6370972be6db4291b56738cb5da4000014993dc14dc2cba0e5a694d12000006442cf0c7bcb3b84e5663466d473404232)) else (if page < 26 then (if page < 25 then 0x3be40002c700000cce1b9480000b42644000006cb03100001154c0000000000179821288000bc66b74080480000000dc58000686012e60001e8817845246000000014e20001461a38803700000a6439fd0000000000019233ec023e04182fa80000adcc00022dde911ec228d4000000000001684c0000000 else 0x5c88d3c7743509b9e2d621000000002560418b3c02e05a3c600009e1800052619acdce0dc52204c5d400004170acc600015b0a450e58187425a86ca000003d80d002b9200017e0e4e231200000cc0000038a686cd9d4114074e032801dcacb800006de12f0239171b000000e81a701bba00009c92d99c56b) else (if page < 27 then 0xa018a59f2d0c774000307800009e619cc1dc01e960849929167810e00001be9c0001c100000ac040003426846600000002b960000239800000000001a78dd28dff6d0e0000000011e0d2803b180000000000000000005536d560a540aa9f1903794000183192e018ebded965a800000005d45e59ec50 else 0xe48c3682ca56e80d4c6b11952869f3000000002306090176141e9d5d3b40b7a1c286b231db9a5e183293d85930c3d52413b082ab0e8c0e6d8fb30cd06e653859ff8d852e6f3918b6e043f0d3495901f705f20a48c421a6081333a8e19a8f35941f8e8a1914002925d004400002b19ef8221e58042cbadd08))))) else (if page < 42 then (if page < 35 then (if page < 31 then (if page < 29 then 0x4ec8e69b6103500b6e19a8aea02d40d88770c0bf0eee647ac1fd7618e8d0b946f5c338af7a26307a245c052be7a1a192c2ea174c034a1c1426536a6531ee5b019a18e7701ec95c1c9aefa0530118225911fc0506097828d91b20dc81838a53323479947e0839d812515ac18d83100a3041e0079e0398e691 else (if page < 30 then 0x9ba8354800076d07acc454b460000000000002e316031ee474f40ab80000234067400005f8200009cc88cb0000afc480800006df00642fe6aa414250e8c4d902e018221ada07dc5e8039600b62f8c4bcbba265245ddc000077e2de80000150b14700000208a79070a0b5a5aec64b020718e84f4c70494803 else 0xc8e0f406882f81788f6243af4b4f00280e6c1568105300006b1f26077a100002d0e984617250c6ecc2028a682450f07401aa8000c94e00000006d2600002c90d4000000000864000021ba0001bc823998de0cbc4940b2e973e0adc052e59b0359389edd6c3060050271ab36a25482621a50d8d40b300000)) else (if page < 33 then (if page < 32 then 0x392dae00d6d39e35340d75580ce4318e01d7c18131931ed71410368b6ed939e4878226065841fd4c9828fb631a74c00001168279600000001f7874d0e08d7482f4010b03a40ef8b61835309c64b353368379258cdbb2ad915266438f5202b6a3fb1b7c0dcc2ff840b60000168182c9ef071e000025604410 else 0x24406085683c7a0e0c0d601e481f68bee1a541770361047cf78cbab13170d3e550c003058a44b21a3c008331c359c1a494f500fdad2a5d389d9a328616825059ea81832d760831c5803430c9008b12e6c34919f210da4a81689091e398022c3ea7049c020d55eb0e236aa09b035d4e151754edf819901550) else (if page < 34 then 0x8a414c658e875e1be006a9b934010aefa14868588d8c2df44441c7988d469a295e4b970510043a1ba5a4b0c7c23da028829f075a0a0e11f9b991e746968c96c1348d8c0ae4152c2a7920ba4ea9b802902674021800bccfc137613ba07e65f401f562b61279387c750047a1da0088527706ea136013a84b56 else 0x12841b1937132c3776516691d3a4f7d4019e50d68e0d0ca00105a04987103754c281ba9b4a7b32412018ccf7f258a727d26c9b6500e00ca400003cd00d148f875c19073db6c99436603b006ec15a0ced25fa013e000007e41a01c988c8c0000000083c00001ac115630d60358712800005440965c8d11941))) else (if page < 38 then (if page < 36 then 0x3085dccd7502540d50b7ac2d79a6b296c54d406bb57e0ce019640fd000001eed4ec709864a019899491dc83f9100000000a2102c1b1891a0000042906fa3d4474983ef14a0ef3834400341afe1aa0da230d0061c187c5c4863d4a9e1b81b2193bf1bcc29603a58391080458d026d075804ac16e001e5e200 else (if page < 37 then 0xd88cdfe8e201c51c8e09b107d836f11ce0d4817286cd0c4219682a201691e2e143c0db09b96e3e10180b4835c4062dd4d9e4378a61ce40000c3977b4bdace8001c37835ecc158cb07bf3c2abc93d882c9e576eec5b85a73b343194c0c3ce92b6662ef89ba400952721d5e0294449b08207e822fdc0f32b41 else 0xd90000000003c30a6722319bd03581ede01ad8000000038400d802db372640a18900ca847f2b221b046b90cd697ce1085bc010000000000035e000000000000000000002be1864131800008d8800026594885a9c400024e2dac279c43618bfd31901d40bd608884f12da8119ccaa123f02da1704c9384d18)) else (if page < 40 then (if page < 39 then 0xee0a56335e084c10c208498000e101c1035f020da9226b8580004a404f000000000783048ae88c9bd19cb477660000000282436a07c8090bb2f0b504000284d3a900d40000336280002f8cd9457e25960a32c4b400000000000000035e98000360122824703daaa0741769a8b6f96d388c6e76337850 else 0xc5149d86db034903c8081d8cb041891407b603630740aaea06a47988bc421cd3c781708800045e03642865c85047d4cf46d3854f1d2022cd38a852e203443c41629779236942dd39201ab8a36c63000332fb02364b71d78a00004de955195e3dbc0d6d352803aa8ffa0000b9072a322b18d6c8ec24a00000) else (if page < 41 then 0x6ace8c423c000000000000230b60b790011d8000029c0e56093eadf4596407cc00000000000e18c00037706763608000000004a562540be900000080c2410f022803632c1447a2a6e17556d8015001618d280d00d28930ebad701ee109c2238879666e77fc6a8ac0d070a152585f1ee7675b5c2403b2b3f0 else 0xcec1a6d6721721003610a112449449674db401318a9443ceda9060f808a900002ac0000000000010f4400073c000000000000765300000000c280000000142c05f019c7ef4ca1d86e800002a64b680ac188009ecd549400078807a4000009a134d0b36e27012220be5479458012e0744042a45b81ea08f21)))) else (if page < 49 then (if page < 45 then (if page < 43 then 0x3e64a7c1f0033c099a76e836200a30c6f551cddc8c3307d22d504f2808644c808966f224fea17216768e726b10c7543903823cd923bc0fd8362b3acadce0fecb0006436d46345e66dcc5ba9349e218bd8770211e0dac26730a50a4545f5b2ab16a5cba16818d4800009980d98000000005aa0bb48930b256 else (if page < 44 then 0x9cc467980000000094400048360000d041ce06bc3a1b45fc574869d418400001038166651a0000000000000000000318000000001640319d000000000000fe83240ae1200016d1849ba56c22c2b78000068e0c024010000000000000db800000001531c0004d8860e0d3033eb431076409013773f290 else 0x618cc64f5c8cc8600000002aab76e000001d905d075608c475f430380000ec6197453b9181a7c41ab4c1531ae740a267c3418446080e1d9c108a0000ae000003770800088d0a001878606000006203c30f5468761dc404605460e70000007a87561b4a0d4400000a14adec1f810138293080ca741a2b8000)) else (if page < 47 then (if page < 46 then 0x3d02c2c0369800000007acdb4c0000aa496d01b883560d00017df83b1296000000000007358dbc03a0000024b0000188c400035a1320807c72300000954c0002679334093219b960887896c14119aa7300a61d4498beadf95fe04ca2ca01668b331d4290c0157807a07a05d7a03fa78420cd28f9bab87000 else 0x10d897186f005de14d878c32a23e83536c28e361f0d021318000002f2c86000000004ab1000030c08e014000000c74c000558063e04f872883250aa800000ee10000d9c108e400031502300fdc67780273000157500001fe0112560d4be0549029e70700000000085c198400003db3000152cc00041e6) else (if page < 48 then 0x22a672c4fc926b19755a68459868a330c078100001f89000000005a84db375000001570472056012602d71039512209e8000059f279649a92d51d9ca75d40001a2b5ba600009104b902b440001b5407c04aa2000145a40002b50000000020c000000001010000000000000e1c00001b01d5aa26c2f480bd4 else 0x2a00000000000006213dac3bd8e44094a1a283853f330ae6c000363829701da180c165320304549be401aa1b23000065c6eea75e01f41584800000000000f4c0840000005c73c294483eb127e1b6405e2d4d0bf20918ab486cf619c9a652f31b3363dedb04fbe0930073e4e181bdac278e061530229855f3))) else (if page < 53 then (if page < 51 then (if page < 50 then 0x81c9bdd8000142167a0fd286eb08d4a0779e8575844b0b930d7539103c50d081d88611c0dc06d21e0994a2a4c26407cb09818127105e163887fdc4510e2ccad946000007fc1901f48814f940a443c2e781e2797088c093e923864f8d11c0c4b041748860609d9b000067060002cb969c0510460911080000 else 0xee252cc0000000052260019969db19a84084476880fc0a6ad778295332c0ae27d498868000024600000000000000004950b782530b0357fdfbf01c80000123c033b0000082258c23e9c4d0eea1c9c1941e7712fa0c946eb0787400005bc537080007be1379f601800086917693c085503664d40c02784fdb) else (if page < 52 then 0xe7406dc66b4005300613dc28402c9042e963d2c0000c00de5c1c00608000df00045b3d829f200009bc34d047400000e8c0a6000006a67cc0721076a04dacf18b77855c17f898c811b009b10000448800000000000cec380837dbd1c0b00e49820e0d595c8c170a68b063c105498948214cac475195d06d20 else 0x652fa854b5020d400005500640bdd1b824000000000005b600003ab300009a40360182373f7d820a5815c8f6d2b2a10dc5eb9000000000001500f396ad23ae400000d6018d562523db5ab98a8250459133ed0b6055e2d0582332b7607385aa00000784d8381c700000ba20264000015e08740000163a53d1)) else (if page < 55 then (if page < 54 then 0x6540204ef780000006cee69dd000004280c7ce1103f0800002c5115800000000b20000000000000db037a81915000000000003213d7405d0000035667100740b39b23e4bce000000000000d2e1c5839618f40e1c0000000001da86403e401d880002d4398c2f22800023a1aa42a0b00007f70df071c50000 else 0x66124892520000c56000031e3800017ab436eac80000a863825dfe8e2caa4ec67580004986000107e749965b0ee018aa8d9b5f3080010f8313d2a30bca08c1f7184fbbc10082011800d73cd038e68a532a438a9401011703be0250016990f86b44672d68d4c085708e9a4bd14e8832f3a9c69c43083a1a0) else (if page < 56 then 0x120567da8fa6000109cda102bb298ae00028a5291259eb531b2485b628b939909bc06e46b520c4e4000464012a605427b1800052030b403e03502c7a1600bae44eb468a200037d34ad6882261c29e0a510d02796c94b191b147899e472890000c2808904fa113b30001c70855133a083220001184c120 else 0xce20274236d2cf3a460f55bb6037da8125c3475e82620c22002c234a18a04684c21b6fb0093a3b578036b84f17346200004f233e100013a18760699536566604b082f28)))))) else 0
  | 7 => if page < 13 then (if page < 6 then (if page < 3 then (if page < 1 then 0x280f800000007e20184a00a4475182c5a047944103dc0726440828bc81684da27f11de9e2c9a0801b941260000710ab400005100001c29d2cef025021596a40e04d212419528460b0340076498023a886d20a0002f0214024400000000420e60000980001e866a1 else (if page < 2 then 0x5f89419ba50860000001accfd00003c8cbb2da368c8a400000004bb004dbe8a3650983440006f224980016a0fb01603b81db00004e0a8591606b0144be980000006718001c606141c024011a086010a94cd2a200074820102c2ac35899bc40009067f99c09208747 else 0x212bc158022a54980c192054436337c0fa09f00d93f01bcc54049036997941f11c90500fe0cd651135c02cca12390935932cd2658b174d3ca0003388424cc078000000018c0da91b9211d2eaab2091a445940d182300f0de840002a81dd1b00fe10a300013a01c0)) else (if page < 4 then 0x6d42a0dbc6cc04700000eac65a00014997684446c10f453428220000bd0d0061120033a4ee088a7710000ea0ca36b98248dee0f013b2515f2d08000000014800004a809580000004e204c9b88b922903204360c896a8344585043044a25d00c08006f007d9a20ec1 else (if page < 5 then 0x7d12b80e228640000dc02665a30000001d86ec0620374de921e40001a41de60007389b88f050a083824047cc940000230122cab35db0000108b60690b0a43840005798000e280004a22a80948d8304000017e07e15b300000000000000c4ccb6f527382700000000 else 0x6002f45084de20002ac0000a70000328800071082b1e41962eb10001d006c45413181b406643070482580c541d049185d9dcc7e62990a180870108280000b801f022800017c000040927458607571501649df20002c80000000d03024c1e5f0000082c0000902000))) else (if page < 9 then (if page < 7 then 0x2422984c809a35a3364146a07a00000000007e704b280176218a30025c00e0a5579820c14a10314c800000e20002e11e81f200006298640000e60691000054680a00009997007463d83f910e05308481254f74f502c133c1726b826942f40840e2049130808e0f61 else (if page < 8 then 0x521b800000001d9bac1d523f0481c0805a0fc64a08d0856cca6101a8809426366d83904000fa861189c1da2a530000001da0be64ab2201512b7069cadd81680404eb1905e62e01450221e0c28011852cc0e44a3478339c812207b3411da8ea47816281c100a6ee8 else 0x63840c1fc09667c132c854441012837a59107607709fa997048051800008a8e620353a818a42066f401d9ae46c02c01fd80680c04011cd16403a618923c0102b104813858874fa03d31dc4e007c00d039d93c0c514932c980009a26982dc5d000230001e886a60b0)) else (if page < 11 then (if page < 10 then 0x41937c5cc6352678b0882269352682d4c0000001d180002b422b0003d912c600067039e100e4f049b0000eec5f360800005101b33a500016640007201e9c6c70520000000000000472000000057000016d00008910000cc00000000002040d84fa15303480aaccd0 else 0x81ae8c1c24e02733d81420ac24d91a81e44f460c5b045482cb649a0dcdb80d6073319d0eee0001d83201666f40699b841b40f48648a589108c761918e196006700320f841a8e69680a6c10f4246090070c472d4b1a83b089610603f222400000008491c81ea69e3) else (if page < 12 then 0x1c000000002c48de0d4a2b041010800001709319db30417f9000184c0003f000000009420001cc0000000000069934a6d25c1aec0c200005a02e4098069601880017400120003cd0000f100002209102000654370530cb435d120c5ba094300010a974c910 else 0x15e4b7465839a0000000)))) else 0
  | 8 => if page < 1 then 0xa1389113615715633389110011400006088832082535200398059061286709407263204005040305800000000907400 else 0
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


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x55550000
    (fun r => ⟨(0x79c698594490 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x55005500
    (fun r => ⟨(0x79c69838c288 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x50505050
    (fun r => ⟨(0x79c59438c184 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x44444444
    (fun r => ⟨(0x79a59238a182 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x33330000
    (fun r => ⟨(0x75c658554450 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x33003300
    (fun r => ⟨(0x75c65834c248 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x30303030
    (fun r => ⟨(0x75c55434c144 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0xf0f0000
    (fun r => ⟨(0x6da6584d2450 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0xff0000
    (fun r => ⟨(0x5d65544d2450 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0xff00
    (fun r => ⟨(0x3ce34c2ca248 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0x55555555
    (fun r => ⟨(0x210620a30e41251661a71e >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0x33333333
    (fun r => ⟨(0x110520930d41151561971d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut16 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x3.target 0xf0f0f0f
    (fun r => ⟨(0x61969b41149320928b001083 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x3.raw 5 (@Sub7x3.lower) Sub7x3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut17 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x3.target 0xff00ff
    (fun r => ⟨(0x515597411493105187001083 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x3.raw 5 (@Sub7x3.lower) Sub7x3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut18 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x3.target 0xffff
    (fun r => ⟨(0x30d38f20928b105187001083 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x3.raw 5 (@Sub7x3.lower) Sub7x3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut19 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x2.target 0x5555aaaa
    (fun r => ⟨(0x3491417185103cb1c379a592 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x2.raw 5 (@Sub7x2.lower) Sub7x2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x2.target 0x3333cccc
    (fun r => ⟨(0x38a1827185103cb1c3759551 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x2.raw 5 (@Sub7x2.lower) Sub7x2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x1.target 0xa5a5a5a5
    (fun r => ⟨(0x6984902880807dd5d53cd1c5 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x1.raw 6 (@Sub7x1.lower) Sub7x1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut22 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x1.target 0xaa55aa55
    (fun r => ⟨(0x5944901840807dd6d93cd2c9 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x1.raw 6 (@Sub7x1.lower) Sub7x1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut23 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x1.target 0xaaaa5555
    (fun r => ⟨(0x38c2881840807dd6d95d54d1 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x1.raw 6 (@Sub7x1.lower) Sub7x1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x1.target 0xc3c3c3c3
    (fun r => ⟨(0x6584502480407de5d63ce1c6 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x1.raw 6 (@Sub7x1.lower) Sub7x1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut25 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x1.target 0xcc33cc33
    (fun r => ⟨(0x5544501440407de6da3ce2ca >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x1.raw 6 (@Sub7x1.lower) Sub7x1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut28 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x2.target 0x55aa55aa
    (fun r => ⟨(0x5511417183085d31c379a38a >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x2.raw 5 (@Sub7x2.lower) Sub7x2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut32 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x2.target 0xf00ff00f
    (fun r => ⟨(0x4d24500c20407de75c3ce34c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x2.raw 5 (@Sub7x2.lower) Sub7x2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut34 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x2.target 0x5a5a5a5a
    (fun r => ⟨(0x6512417143046d32c3796386 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x2.raw 5 (@Sub7x2.lower) Sub7x2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut44 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x2.target 0xff0000ff
    (fun r => ⟨(0x1c61440c20407de75c6da658 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x2.raw 5 (@Sub7x2.lower) Sub7x2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut46 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0xffff0000
    (fun r => ⟨(0x7de75c6da6585d65544d2450 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut47 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0xff00ff00
    (fun r => ⟨(0x7de75c6da6583ce34c2ca248 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut48 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0xf0f0f0f0
    (fun r => ⟨(0x7de75c5d65543ce34c1c6144 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut49 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x5.target 0xcccccccc
    (fun r => ⟨(0x7de6da5d64d23ce2ca1c60c2 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x5.raw 5 (@Sub7x5.lower) Sub7x5.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut50 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x5.target 0xaaaaaaaa
    (fun r => ⟨(0x7dd6d95d54d13cd2c91c50c1 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x5.raw 5 (@Sub7x5.lower) Sub7x5.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p
def cutFor : Nat → List (Nat × Nat) → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 7 => cut6
  | 8 => cut7
  | 10 => cut9
  | 11 => cut10
  | 15 => cut14
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
  | 29 => cut28
  | 33 => cut32
  | 35 => cut34
  | 45 => cut44
  | 47 => cut46
  | 48 => cut47
  | 49 => cut48
  | 50 => cut49
  | 51 => cut50
  | _ => cut0

def suppliedPrefix : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | j+1, z => if z=0 then [] else ((z%256)/16,z%16) :: suppliedPrefix j (z/256)
def selectCut (code : Nat) := cutFor (code%128) (suppliedPrefix 3 (code/128))
def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x580000000 else 0
  | 4 => if page < 2 then (if page < 1 then 0xc0000000800000000000000800000014000000000000000000000040000000600000004000000100000008000000100000002000000020000000200000000000000180000000000000060000001000000010000000400000001000000040000000c00000050000002100000016000000080000001800000080000001000000020000000080000001000000080000002000000000000000100000010000000b400000008000000100000002000000000000000800000010000000200000004000000080000001000000020000001000000020000000100000002000000080000002000000050000001000000004000000080000001 else 0x2b23228f9b8b895e000000200000004000000084535341e00000028000000400000008000000000000002c00000018000000200000010000000215919147800000080000000e00000008000000400000008000000100000002000000040000000100000002000000080000000800000020000001000000000000000400000007) else 0
  | 5 => if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x4400000078000000f0000001e0000003c000000780000011000000640000004400000088000000f0000001e0000004400000178000002f0000005e0000004400000088000002f0000005e000000440000008800000110000005e000000bc00000088000000f0000001e0000004400000078000000f0000001e0000003c00000078000002f0000002a0000004400000088000000f0000001e00000044000000780000011000000220000004400000178000000f0000001e000000440000017800000110000005e0000004400000088000000f0000002200000044000000880000010000000220000003c00000178000000f else 0x64000000c800000188000003200000020000092bc0001247800000000000002200000044000000880000011000000000000004400000088000001100000022000000440000000000000320000001e000000c80000007800000320000001e00000044000000880000011000000220000003c00000088000000f0000001e0000003c00000088000000f0000001e0000003c00000000000003200000022000000000000019000000110000002200000044000000880000011000000220000004400000088000001100000022000000440000000000000110000001e0000003c00000078000000f0000566200000044000000000000011) else (if page < 3 then 0x2200000000000000880000011000000000000b23c0000000000000000000002200000044000000880000011000000220000004400000090000001000000024000000440001a1800000000000068620000003c00000000000000f0000001e0000003c000000880000000000000220000004400000088000000f0000001e00000044000000780000011000000220000004400000078000000f0000001e0000000000000078000000f0000001e0000004400000078000000f0000001e0000003c00000078000000f0000001e0000003c00000000000000000000020000000440000008800000110000002400000048000001880000000 else 0x660000003c00000090000000f00000022000000440000019800000110000002200008a3c0000000000000110000451e00000000000001880000031000000240000000000000000000000f0000451e0000000000000090000003200000000000000c40000009000000110000002200000048000000880000011000000200000004400000088000228f000000220000004400000088000001100000064000000c800000078000000000008960000000440000008800000000000002200000040000000000000011000089620000004400000088000001100000022000000440000008800000000000002200000044000000880000033)) else (if page < 6 then (if page < 5 then 0x22000000bc000000a0000002f0000495e000000cc0000019800000130000002600008a60000001980000033000000260000004c00000098000000f0000005e000000440000008800000110000001e0000004400000088000001100000022000000440000008800000110000451e000000c8000000a000000110000002200000044000000880000012000000240000003c00000088000001100000022000000c0000000e800000300000004600000074000000e8000002300000060000000c0000000880000012000000460000008c00000090000001200000024000000c8000001980000000000000640000008c000001180000012 else 0x64000000cc00011578000003200000066000000bc0001657800000140000005e000000bc0001157800000330000005e0000b2bc0000008800000310000005e00000000000000980000011000000260000004c000000980000011000000260000983c0000008800000110000000000000044000000000000011000000000000004400000088000001100000022000112bc000000880000011000000220000004400000088000001100000064000000bc00000178000003200000064000000cc00000000000002f0000006400008abc00000190000000000000064000000c80000019000025af0000005e00000044000001780000011) else (if page < 7 then 0x22000000440000008800000120000002400000044000000880000011000000220000004800000088000001100000022000000000000007800000120000001e00000048000000900000012000000240000923c000000000000000000000240000004800000090000000f0000001e0000003c000000780000000000000000000004800000090000000f0000001e0000004800000090000000f000000220000003c0000007800000110000002200000044000000880000011000000220000004400000078000000f00000064000112bc0000e178000122f0000895e0000005000000190000003200000064000000c8000001900000000 else 0x491e0000003c00000078000001100000022000000440000008800000110000002400000000000000900000012000000220000004c0000008800000110000002200000044000225880000032000000640000004400000088000001100000064000000440000008800000110000002200000044000000880000011000000220000004400000088000000f000000220000004400000088000000f0000001e0000003c0000008800000110000001e0000004400000088000000f00000022000000c80000008800000120000566200000044000000900000011000000220000acc4000159880002b3100004b5e00000044000000880000012))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x62000000c400000088000001100000022000000440000008000000100000002000000044012521780000011000000220000000000000088000001100000022000000c800000080000001100000022000000440000000000000130000002200000044000000880000011000000220000004400000088000001100000022000092c00000008800000110000002200000044000114800000011000000220000004400000088000001100000064000000440000008800000110000002200000044000000900000012000000240000003c00000090000228f00000064000000cc00000198000003200000064000052bc000001900000011 else 0x2200000044000000880000011000000220000004400000088000000f00000022000000440000008800000110000001e0000003c0001147800000000000001e000000c800008d78000001100000000000000440002f07800000110000561e00000044000000880000000000000220000004400000190000003300000064000000c800000198000003200000064000000c800000190000003200000064000000cc000001900000000000000240000004800000090000001100000022000000480000009000000000000002200000044000000880000011000000220000004400000088000001100000022000000c4000001880000000) else (if page < 11 then 0x64000000440002258800044b100000022000000c800000000000001100000022000000440000008800000110000002200000044000000880000011000038620000004400000088000003300000022000000000000000000000320000691e0000ac3c0000019000000320000451e0000003c000001900002b0f0000591e00008a3c00000088000001100000022000000440001a1880003431000068620000004400000088000122f000000260000004c000000880000011000000220000983c000000880000011000000220000004400000088000001100000022000000440000007800000110000002200000044000114780000011 else 0x220000004400000190000003200000064000000c800000088000001100000064000000c800000190000002f0000005e0000004400000178000002f0000005e0000005000000178000001700008a6000000000000000880000011000000000000004400000088000003200000064000000c800000088000003200000066000000cc00000000000001100000022000000000000000002b228f00000000000000c0000000880000012000000000000004400000088000001100000022000000440000008800022af00000022000112bc000225780000032000000640000000000000190000001100000022000000440000019000044b1)) else (if page < 14 then (if page < 13 then 0x2200000044000000000000000000000000000000000000090000001300000024000000480000000000000000000002200000000000000880000033000000660000004c00000088000001300000026000000000000009800000110000005e000000440000008800000320000455e00000000000001900000000000000660000004400000188000002f000000640000004400000090000003200000022000000440000008800000110000002200000000000000880000011000000220000004400000088000001100000022000000c800000190000003200000022000000440000008800000110000001e00000044000000880000011 else 0xc800d4d07800000000000236200ac8a3c000001980000000000000240000004c0000000000000000000002200000044000000880000011000000220000004400000088000001100000022000000440000008800000110000002200000044000000880000012000000220000004400000088000001100000024000000cc0000a5880000011000000260000000000000088000000000000064000000c800000190000001100000064000000440000008800000110000002200000044000000000000012000000220000004400000090000001200000022000000000000008800000110000002200000044000000880000011) else (if page < 15 then 0x6400000044000000900000012004b495e0000004c00000000000001300004c6000008abc00012d780000011000000220000000000000190000000000000000000000c80000019000000110000002200000044000000880000011000000220000004400000190000003200ab8b5e013716bc0000000000000110000002400000044000000000000000000000220000004400011578000001100000060000000440002258800044b1000000000000004400000000000000000000022000000000000008800000000000006400008a3c000000900000012000000220000004c0000008800000110000002200000044000000900000032 else 0x27269800000011009a8960000000000001157800022af0000000000000000011914780229a0f000000000000004400000088024a42f0000002200000044000000000000000)))) else 0
  | 6 => if page < 31 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x4c1e0000003c00000078000000f0000001e0000006400000078000000f0000001e000112c00000000000000190000002c00000058000000780002b3100004b5e00000000000130780001e0f0000001e0000003c0000007800000190000001e000000bc00000178000002f0000005e000000bc00000178000002f0000005e000000bc00000078000000f0000001e0000003c00000178000000f0000001e0000003c00000078000002f0000005e000000bc000001780000019000000320000003c0000007800000160000001e000000bc00000178000000f0000001e0000006400000078000000f00000000000000bc00000078000000f else (if page < 2 then 0x6000008abc0001148000022af0000895e000112c00000000000000100000341e00000000000225880001a0f00000000000156400001247800000000000591e0000004000000000000229000000000000000bc0001a18000034310000001e0000000000017078000260f00003c1e0000003c00000078000000f0000001e0000000000000078000000f0000001e0000003c00000078000260f0000001e0000003c00000078000000f0000001e0000003c0002ac7800000000000451e0001564000022880000003100000000000092bc00000080000248f0000003200000064000000c800000000000452000000064000000c80000019 else 0x4c20000000bc00022578000242f00004c1e0000983c0001307800026100000455e000000bc00000178000002f0000455e000000bc0000017800044af0000005e00008a3c0000d07800055af00009a5e0000003c00000078000002f0000005e00000064000000c800000310000005e000000c000000180000003100000060000000c000000180000003000000060000000c40000018800000310000006200000000000001880000031000000620000003c00022978000003100008a6000008a3c0001147800000000000451e0001784000000188000003100008b200000000000011478000003100006a60000000c000000000000228f)) else (if page < 5 then (if page < 4 then 0xab20000114400001188000000190000003200000064000000c8000003100000062000000c40000018800024af000000320000923c000000c8000001900000020000000640000008000000100000491e000092c0000000c80000019000000320000ac3c00000078000228f0000491e000052bc0000008000014b0000000320000003c0000007800000160000002c0000006400011478000000000005662000098c00000000000000000000001e0000003c000000780002b0f0000001e000000bc00022578000002f0000235e000000bc0000a57800044af0000005e000000bc00000188000003100004c1e000000bc0000017800045af else 0x1e000000bc00000078000002f0000001e0000003c00000178000003000000032000000bc0000017800000300000001e0000003c00000180000000f000000000000000000000000000000000009b1e00008a3c00026878000002f0000005e000000bc00000178000002f0000ab1e000114bc00022880000003100000060000000c000011478000228f0000006000008abc0001148000022af0000455e000112bc0002258000044b10000341e0000000000013078000122f0000451e0000923c0000917800012300000001e00008a3c00008d78000000f0000bc1e0001563c00015878000228f0000ab200000923c000228800002b10) else (if page < 6 then 0x1e000000bc00011478000000f0000341e0000003c00000078000002f0000491e000000bc00012c780001d8f0000001e000000bc00000178000000f000000320000003c00000178000000f0000005e000112bc000000c800000160000005e00008a3c00000078000002f00008a5e000000c00002297800000300000895e000000c00000917800011af00000060000092bc0000a578000152f0000005e000000bc000225780000030000000600001343c0000007800000300000001e000000c00000d078000000f0000001e0000003c0000007800000300000491e0000003c000001800001d0f0000001e000000bc00000178000002f else 0x4c1e000000bc0000017800055af0000005e000114bc00013080000002f0000005e000000bc000000c800055af00004c20000116bc000000c8000002f000000320000006400022978000002f0000455e00009840000000c8000001900004c2000000064000000c800000190000005e00004abc00009178000001900004c20000000bc00016178000242f00004c20000000bc0001308000000190000003200000064000130800000019000000320000b4bc0000a978000002f00004b5e000098400000ad7800000190000005e000000bc0000017800022af0000003200000064000001780001a8f0000001e000000bc0002ac780004d0f))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x5e000000bc0002ac78000000f00009a1e0000003c0000e878000000f000000000000b0bc000001780002d0f0000001e000000bc00000178000558f00009b1e0000003c000001780004d0f0000005e00008a3c00000078000002f0000351e0000683c00000078000000f0000001e0000003c00000078000002f0000591e0000923c000000780002d0f00003a1e000000bc00012c780001d8f0000001e000000bc00000178000228f0000001e000000bc000000780002c8f0000001e000000bc0002ac78000000f0000005e00008a3c0000007800000100000005e0000963c00000078000002f0000001e0000003c00000178000000f else 0x451e00008abc0000007800000180000341e0000683c000000c00004d0f0000595e000058c00000b080000000000002c20000068bc0000d0780001a0f0000341e000058400000b08000000180000491e0000006000012c780001d8f0000001e0000003c00000078000258f0000001e0000006000000078000000f0000001e0001563c00026878000000f0000003000008a3c0000d07800016100000005e000058c00000b080000248f0000491e0000923c0001257800000000000001e0000003c000000c0000248f0000455e0000584000000078000163000004b5e0000963c00012c78000258f00004b5e0000763c0000ec78000002f) else (if page < 10 then 0x235e000000bc0001257800000000000295e00008abc0000000000025af00004b5e000000bc0000017800055af00000000000000bc000115780001e0f0000895e000000000000f07800044af00000000000000bc00012d7800000000000005e000112bc00000000000002f00000000000092bc00013080000002f0000005e000000bc00000178000002f0000005e000000bc0000017800016300000ab1e0001563c0002ac78000558f0000ab5e0001343c000268780004d0f00009a5e0001343c000269780001610000000000000006000011478000161000002c620000b4bc0000b080000002f00002c600000584000011478000228f else 0x585e0000984000013078000260f0000255e0000983c00013078000260f00004c1e0000b0c400013078000260f00004c1e0000983c00013078000260f00004c1e0000983c00013078000260f00004c1e0000983c0001307800026100000005e000098c00001657800026100000595e0000b2bc0001308000024af000059620000983c00013078000260f00004c1e0000983c00013078000260f0000895e000000000002258800022af000000620000b4bc0001307800025af00004c1e000000bc00022d78000002f0000005e000000bc00000178000452f00000000000000bc0001157800022af0000895e000000bc000091780000000)) else (if page < 13 then (if page < 12 then 0x1e000000bc00022578000002f0000235e000000bc0000a57800044af0000005e000000bc00026d78000002f0000005e00006abc000001780002caf0000000000008abc00016578000002f0000005e000000bc00000178000002f0000005e000000bc0000018800055af00004c60000116bc0001307800045af00008b5e000116bc00013078000261000004c1e000000bc00000188000452f00000062000116c400000188000003100000062000000c40001318000026100000455e000112bc0001307800044af0000895e000098400000000000044b10000385e0000984000000000000261000003862000098400001217800012b1 else 0xc800000190000002c00008a3c000000000002b3100005662000096bc000131800002b3100004c600000000000012d7800025af00005662000098c00001598800000000000000000000000000131800000000000056620000000000013180000000000005662000000000000000000000000000000000000000000158780002b0f00009a1e0000003c00000000000000f000000000000683c00000078000000f0000001e0000ac3c00000078000000f000000000000923c000000780000000000000000000ac3c0000007800000000000561e0000003c0000000000000000000003200000000000000000002b0f) else (if page < 14 then 0x190000001e0001783c0002ac780004d8f0000001e000000640001587800000190000451e0000003c000000c800000190000003200006a3c000000c800000190000001e0000003c00000078000000f0000591e00000064000000c8000228f0000001e00000064000000c8000000f00008960000112c00000000000000000000491e000000640000000000044b1000000000000923c000000c8000001600000000000112c4000000b000044b10000002c0000923c0000000000000160000002c00000058000124780000016000000320000923c000120800000019000000320000923c000000c80000000 else 0xb2c40000000000000190000003400008a40000000000002cb10000000000008a40000000c800000190000000000000000000000c800000190000561e0001563c00000078000228f0000001e0000003c0000a57800055900000ab1e0001563c0002ac7800014b100009a1e00008a4000011478000228f0000295e000052bc0000a580000228f000000000000683c0002ac780004d0f0000451e00009840000000800002610000000200000004000012478000260f0000001e0000983c00000078000000f0000ab1e0000003c000114780005590000045200000983c0002ac78000000f000000000000923c0000d878000000f)))) else (if page < 23 then (if page < 19 then (if page < 17 then (if page < 16 then 0x320000923c00000000000248f0000491e0000923c0001a188000248f000000320000006400012478000001000000020000000400000008000000000000491e000000400001257800024b00000491e0000923c000124780005e1000000062000116400000018800024af000000200000923c0001257800000190000496000000064000000c800000000000000000008a4000011480000001900005962000000000001148000000000000003200000064000125800000019000000320000b2c400000000000001a0000596200008a4000000000000229000000032000000680001148000000190000003200008a40000000c80000019 else 0x64000000c8000248f000000320000006400012578000248f0000495e0000ac4000000188000001900000062000000c400022d88000003100000062000000c4000125780000019000049600000923c0000008000024b00000566200000000000000c8000248f0000252000000064000000c800000190000582000000064000000c800024af00000062000092c0000000c8000001900000000000000c40001708000000190000491e0000004000000080000001000005c2000000040000000800000010000000320000004000022c800000019000000320000923c00000000000001000002562000092bc000000c8000248f) else (if page < 18 then 0xab1e0000003c00015878000228f0000001e00008a3c00000078000000f0000ab1e0001563c0002f078000558f0000561e00008a3c00011478000228f0000ab20000156400002ac8000046300000ab20000156400000998000055900000566200011440000228800005e3100008a200000acc40001247800045100000491e00000000000000000002b100000ab2000011640000228800002310000045200000d44000009480000121000000062000178400001257800024af0000bc20000000c40000018800000310000006200011640000125800002b10000049600000923c0001247800000000000491e000092c0000000c80000019 else 0xbc1e0000003c00026c78000000f0000001e0000000000000000000228f0000001e0001583c000000000004e0f0000001e0001343c00000000000228f0000461e00008a3c00000000000000f0000361e0000683c00000000000000f00004b1e00008a3c00000000000000f0000561e0001383c0002ac78000000f0000000000008a3c0000d87800000000000691e0000003c00008d78000558f0000ab1e0001563c00008d88000228f0000451e000046bc00008d7800011b00000451e000000000000d078000248f00004c1e0000003c00013078000000f0000001e0000983c0002ac78000000f000000000000003c000000780005e0f)) else (if page < 21 then (if page < 20 then 0x4c1e0000000000026c78000000f0000001e000000c4000091780005e0f0000bc1e0001783c00000188000003100009b1e0001363c00026c780001210000000000000ac3c00015878000558f00002460000048400000917800012100000561e000000c400026d88000228f00000062000000c400000188000122f0000246000004840000091800002b310000001e00006a3c0000d4780001a8f0000341e0001363c000268780001ab10000245e000048400000000000012100000351e0000d2c400016478000248f0000591e0000b43c000170780001e0f0000001e0000003c000000780002e0f0000001e0000b83c000130780001e0f else 0x38620001144000000000000248f00000000000000000002288000045100000491e000070c40001247800000000000bc20000156400001588000022900000491e0000000000011480000000000005620000136bc00013078000260f0000455e000156400000f0780002290000000200000d0c000027078000000f0000001e0000ac3c0001a1880005e0f0000001e0000ac3c00000000000228f0000bc1e0000003c00015878000228f000000000000ac3c00009178000122f0000245e0000983c0001a188000000000004c1e0000000000000000000122f000068620000983c0001a188000122f000068620000983c000000000000000) else (if page < 22 then 0x451e000000c40000018000022af0000452000008abc0000018000000300000451e000000c00001157800022af0000452000008cc0000159880002b3100000000000000000001157800044af000089600001563c0002ac7800044b100009a1e000112c400000000000228f00008962000112bc0002257800044af00008960000112c000022580000228f00000000000112bc0002258000044b00000bc200000683c00015880000001000004520000000000002258800000000000896200000000000000000001a0f00000000000112c40000d07800044b10000341e000000000000d078000000000000000000000000002ac800000000 else 0x62000114c00000000000045b1000000000000000000011478000453000000000000116c400000000000228f0000bc1e000000c40002f080000003100008c62000000000002ac80000003100008b200001783c000001880000031000000620001363c00000188000452f00006a60000158c0000271800004d300000451e000000000002b080000461000008a20000114c00000018800022af0000006200008abc00011578000228f0000451e00008a3c00011578000228f0000451e000000c400000000000003100000062000118c400011478000228f000000000000000000000188000228f0000006200000000000114800000031))) else (if page < 27 then (if page < 25 then (if page < 24 then 0x64000000c8000563000008c60000114c0000115780002b3100004660000112c00000917800012300000ab1e0001343c000114780001a0f00002360000092bc0000018800000000000491e000092c00000a580000248f00004b5e000000000000ad78000002f0000455e0000983c000131800001e0f00002c600000000000000180000003100000060000000c000000180000003000000060000000c00002f188000003100000000000000c400000188000452f0000bc1e0001783c00000188000003100000062000000c400026c780004d8f00000062000000c400000188000003100008a5e000114bc000001880004e0f else 0xab1e0001343c000114780001a0f0000ab1e0001343c000000c0000228f000000300000683c0002ac780004d0f0000003000008a3c000000c00001a0f0000003000000060000000c0000001800009a1e00000060000000c0000001800000030000058c400012478000248f0000491e0000923c0000b080000248f0000491e0000923c000124780001a8f00000030000000600001147800022af00002c600000963c00012c78000258f00004b5e000058c000012c78000258f00004b1e000058c000012d780001d8f00003b1e000058400000b08000055af00009a5e00000064000000c80004e310000003200000064000000c80000019) else (if page < 26 then 0xb2bc0001308000024af0000495e000092bc00012578000260f0000295e000052bc0000a578000260f00004c1e00008abc00022d7800044af0000255e000046bc0001657800014af00005a5e000054bc00012d7800015af00008b5e000114bc00022578000122f0000235e000092bc0000a57800026300000455e00008abc0001157800022af0000455e000096bc0001318000044af00003c1e000112bc0000f078000161000003c1e000112bc00022578000228f0000341e0001363c00026c78000558f0000ab5e0001343c000269780004d0f00002c6000008a3c00011478000228f0000455e000058400000b0800001a0f else 0x158780002b0f00002b5e00000000000158780002b0f0000561e0000ac3c0001587800055af00008960000156bc00008d8000055af00002960000112c400022978000452f00004c60000116bc00022d7800055af00008b5e000116bc0002297800055af00008b5e000114bc0000017800022af0000455e00008abc0001157800044af0000895e000112bc00022578000260f00004c1e0000983c0000957800012af0000255e00004abc00009178000122f00004c1e0000983c0001307800011af00004c1e000046bc00008d78000260f00004c1e0000983c0001318000026300000595e0000b2bc000165780002610)) else (if page < 29 then (if page < 28 then 0x491e000092c000022c80000559000004b20000090400000000000024b00000000000000000000000c800000190000596200000064000000c800000190000003200000000000158800001b0f0000451e0001563c00026878000228f0000341e000052bc0000a58000000000000ab200001563c00011478000558f0000451e000052c000012478000248f0000491e0001343c000000c80000019000000320000923c000000c80000019000000320000923c0000000000000000000491e00000064000000c800000190000491e00000064000000c800000190000491e0000923c000000000002b3100004b5e000098c0000159880000000 else 0x4620000114400002f18800045b1000000320000acc400026d88000001900005662000178c400022880000248f00003b620000acc40002308000056100000495e000092bc000125800002b310000242000006ac4000168800001ab100008b20000114400002f0800004590000000320000ac40000000c800000190000491e000000640001247800012b10000491e0000923c0001247800012900000491e0000923c000000c8000248f000000320000923c000124780002c31000058200000923c0001247800014b1000000000000923c000000000000000000000620000923c0001247800000000000491e0000923c00012478000248f) else (if page < 30 then 0x455e00008abc00011578000233000004660000000000001157800023300000455e00008cc00001157800022af0000895e000112c0000225800000000000089620000683c000000000005e0f00009b1e0000ac3c000114780004d8f0000bc1e0001363c000158780004e0f0000bc1e0001383c00009178000122f000024600000acc400009080000121000009b1e00008a3c0001147800012300000451e000000000002ac780004d0f0000451e0000683c0002b078000558f0000235e000046c000011478000228f000000000001563c0002f078000558f0000561e00008a3c0002ac8000044b100008a200000ac400002ac800004510 else 0xab5e0001383c00022978000563000008c6000008abc000115780004530))))) else 0
  | 7 => if page < 5 then (if page < 2 then (if page < 1 then 0x5e000000c0000001800000031000000620000003c0000007800000000000001e000000c400000078000002f0000001e000000bc00000180000001000000060000000c000000000000000f00000020000000000000000000000100000005e0000004000000078000000f0000001e0000000000000078000000f0000001e0000003c00000078000000f0000001e000000c0000001880000010000000200000000000000078000000f0000001e0000000000000000000000f0000005e000000bc00000178000002f0000005e0000003c00000078000000f0000005e0000003c00000178000000f0000001e000000bc00000078000002f else 0x3c00000078000000f0000005e0000000000000078000000f0000001e0000003c00000078000000f0000005e0000000000000078000002f000000000000000000000078000002f0000005e0000003c00000178000000f0000001e0000003c0000017800000000000005e000000bc00000078000000f0000005e000000bc00000178000000f0000005e000000bc0000018000000000000001e0000003c00000078000000f0000001e000000c4000001880000010000000000000003c00000078000000f00000060000000bc00000178000002f0000005e000000bc00000078000000f0000001e0000003c00000180000000f) else (if page < 3 then 0x2000000000000000000000010000000000000004000000078000000f000000000000003c0000007800000100000001e0000003c00000078000000f000000200000003c00000000000000f000000000000000000000000000000000000060000000c400000178000002f0000005e000000c400000000000002f0000005e000000bc00000188000002f000000620000000000000178000002f0000005e000000000000018800000000000005e000000000000018800000000000005e000000bc00000188000002f00000000000000bc00000000000002f0000005e0000003c0000000000000000000001e0000003c00000078000002f else (if page < 4 then 0x60000000c400000000000000000000060000000c4000000000000031000000000000000000000000000000f000000000000000000000180000003100000000000000c400000000000000f0000001e0000000000000188000000f000000620000003c000000780000000000000620000003c00000000000000f000000000000003c0000007800000000000001e0000003c00000078000000f0000001e000000c000000188000001000000000000000c40000008000000000000000000000000000000800000031000000620000004000000000000001000000020000000000000000000000310000000000000040000000000000031 else 0xc000000188000003000000000000000c40000018800000000000001e000000c400000188000002f))) else 0
  | 8 => if page < 1 then 0x0 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 31 i

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

theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 2 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 97 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 97 0 = true :=
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
theorem chunk5x560 : span (checked 5) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x784 : span (checked 5) 112 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x896 : span (checked 5) 82 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 978 0 = true :=
  (@span_join (checked 5) 448 0 530 (@span_join (checked 5) 224 0 224 (@span_join (checked 5) 112 0 112 chunk5x0 chunk5x112) (@span_join (checked 5) 112 224 112 chunk5x224 chunk5x336)) (@span_join (checked 5) 224 448 306 (@span_join (checked 5) 112 448 112 chunk5x448 chunk5x560) (@span_join (checked 5) 112 672 194 chunk5x672 (@span_join (checked 5) 112 784 82 chunk5x784 chunk5x896))))

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
theorem chunk6x1008 : span (checked 6) 112 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1120 : span (checked 6) 112 1120 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1232 : span (checked 6) 112 1232 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1344 : span (checked 6) 112 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1456 : span (checked 6) 112 1456 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1568 : span (checked 6) 112 1568 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1680 : span (checked 6) 112 1680 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1792 : span (checked 6) 112 1792 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1904 : span (checked 6) 27 1904 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1931 0 = true :=
  (@span_join (checked 6) 1008 0 923 (@span_join (checked 6) 448 0 560 (@span_join (checked 6) 224 0 224 (@span_join (checked 6) 112 0 112 chunk6x0 chunk6x112) (@span_join (checked 6) 112 224 112 chunk6x224 chunk6x336)) (@span_join (checked 6) 224 448 336 (@span_join (checked 6) 112 448 112 chunk6x448 chunk6x560) (@span_join (checked 6) 112 672 224 chunk6x672 (@span_join (checked 6) 112 784 112 chunk6x784 chunk6x896)))) (@span_join (checked 6) 448 1008 475 (@span_join (checked 6) 224 1008 224 (@span_join (checked 6) 112 1008 112 chunk6x1008 chunk6x1120) (@span_join (checked 6) 112 1232 112 chunk6x1232 chunk6x1344)) (@span_join (checked 6) 224 1456 251 (@span_join (checked 6) 112 1456 112 chunk6x1456 chunk6x1568) (@span_join (checked 6) 112 1680 139 chunk6x1680 (@span_join (checked 6) 112 1792 27 chunk6x1792 chunk6x1904)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x112 : span (checked 7) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x224 : span (checked 7) 43 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 267 0 = true :=
  (@span_join (checked 7) 112 0 155 chunk7x0 (@span_join (checked 7) 112 112 43 chunk7x112 chunk7x224))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 10 0 = true :=
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
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 9
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    9 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor7


namespace SignedFrontier.SmallCert.Minor10

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
  | 0 => if page < 6 then (if page < 3 then (if page < 1 then 0xff000000ff000000fefefe00fefefe00fe00fe00fe00fe00fc00fc00fc00fc00fa00fa00fa00fa00f000f000f000f000eeeeee00eeeeee00ee00ee00ee00ee00ccaaee00ccaaee00cc00cc00cc00cc00afafaa00afafaa00aafcfe00aafcfe00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa0088888800888888000afffa000afffa000afafa000afafa000aeeea000aeeea000aaaaa000aaaaa000a555a000a555a000a505a000a505a000a222a000a222a0003fffc0003fffc0002aaaa0002aaaa0000fffe0000fffe0000fffc0000fffc0000fff00000fff00000ffaa0000ffaa0000ff000000ff000000fefe0000fefe0000fcfc0000fcfc0000f0f00000f0f00000eeee0000eeee0000eee00000eee00000eaea0000eaea0000cccc0000cccc0000aafe0000aafe0000aaee0000aaee0000aaaa0000aaaa0000aaa80000aaa80000a8fc0000a8fc0000a8a80000a8a8000088aa000088aa0000888a0000888a00008888000088880000888000008880000080800000808000000ffe00000ffe00000ffa00000ffa00000eee00000eee00000aaa00000aaa000000fe000000fe000000ee000000ee000000cc000000cc000000aa000000aa000000a8000000a800000088000000880000003c0000003c0000000e0000000e0000000a0000000a000000080000000800000002000000020000000000000000 else (if page < 2 then 0xaaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa22aa22aa22aa22aa00aa00aa00aa00a8a8fcfca8a8fcfca8a8acaca8a8acaca8a8aaaaa8a8aaaaa8a8a8fca8a8a8fca8a8a8aaa8a8a8aaa8a8a8a8a8a8a8a8a8a8a800a8a8a800a0aaa0aaa0aaa0aaa0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0999999aa999999aa999899989998999888aa88aa88aa88aa888aaaaa888aaaaa888a888a888a888a8888fff88888fff88888f8f88888f8f88888aaaa8888aaaa8888aaa88888aaa8888888aa888888aa8888888a8888888a8888888888888888888888808888888088808880888088808080888880808888808080888080808880808080808080808000800080008000555555505555555055555544555555445555550055555500555554545555545455554444555544445555000055550000550055005500550054545454545454544444444444444444333f0000333f0000333322223333222233003300330033003030303030303030222222222222222211ff000011ff000010f010f010f010f00fff00000fff00000f0f0f000f0f0f000f000f000f000f000e0e0e0e0e0e0e0e0ccc0ccc0ccc0ccc0c0c0ccc0c0c0ccc0c0c0c0c0c0c0c0c0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a00050505000505050000ffffee00ffffee00ffffaa00ffffaa00ff00cc00ff00cc00ff00aa00ff00aa else 0xeeeeeeeeeeeeeeeeeeeeeeeceeeeeeeceeeeeee0eeeeeee0eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeee0e0eeeee0e0eeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eeeceeeceeeceeeceeeaeeeaeeeaeeeaeee0eee0eee0eee0ececececececececeaeaeaeaeaeaeaeaeac0eac0eac0eac0e0e0e0e0e0e0e0e0ddddddccddddddccdddddcdcdddddcdcdcdcdcdcdcdcdcdcccff0000ccff0000ccfeccfeccfeccfeccfcccfcccfcccfccccceeeecccceeeeccccececccccececcccccccccccccccccccccc00cccccc00cccc8888cccc8888cccc4444cccc4444cccc0000cccc0000cccacccacccacccaccc0ccc0ccc0ccc0cc00cc00cc00cc00c8c8c8c8c8c8c8c8c0ccc0ccc0ccc0ccc0c0eaeac0c0eaeac0c0c0c0c0c0c0c0c0c04040c0c04040c0c00000c0c00000c000c000c000c000aafeaafeaafeaafeaafaaafaaafaaafaaaeeaaeeaaeeaaeeaaaceeecaaaceeecaaaafffeaaaafffeaaaafffcaaaafffcaaaafefeaaaafefeaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaaeaeaaaaaeaeaaaaaaafeaaaaaafeaaaaaaeeaaaaaaeeaaaaaaccaaaaaaccaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa88aaaaaa88aaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaa8888aaaa8888aaaa0202aaaa0202aaaa00aaaaaa00aaaaaa0000aaaa0000aaa8fffcaaa8fffc)) else (if page < 4 then 0xffaacc00ffaacc00ffa8ffa8ffa8ffa8ff88ff88ff88ff88ff0fff00ff0fff00ff0eff0eff0eff0eff0eff00ff0eff00ff0aff0aff0aff0aff02ff02ff02ff02ff00ffeeff00ffeeff00ffe0ff00ffe0ff00ffaaff00ffaaff00ff0aff00ff0aff00ff00ff00ff00ff00fe00ff00fe00ff00cc00ff00cc00ff001100ff001100ff000000ff000000fefefffefefefffefefefefefefefefefefefef0fefefef0fefefeaafefefeaafefafefafefafefafeeefeeefeeefeeefeaafeaafeaafeaafcfcfefefcfcfefefcfcfcfcfcfcfcfcfcfcfcf0fcfcfcf0fcfcfcccfcfcfcccfcfcfca8fcfcfca8fcfcfc00fcfcfc00fcfcdcdcfcfcdcdcfcfc5454fcfc5454fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafaf0fafafaf0fafafaaafafafaaafafafa00fafafa00fac8fac8fac8fac8faaafaaafaaafaaaf8f8f8f8f8f8f8f8f888f888f888f888f3f3f3f0f3f3f3f0f3f2f3f2f3f2f3f2f3f0f3f0f3f0f3f0f3f0f2f0f3f0f2f0f2f2f2f0f2f2f2f0f1f10000f1f10000f1f0f0f0f1f0f0f0f0f0fff0f0f0fff0f0f0fefef0f0fefef0f0fef0f0f0fef0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0f000f0f0f000f0f010f0f0f010f0f0f01010f0f01010f0f00000f0f00000f000f0f0f000f0f0f000f000f000f000eeeefffeeeeefffeeeeefefeeeeefefe else (if page < 5 then 0xfffff0a0fffff0a0fffff000fffff000ffffeeeeffffeeeeffffeee0ffffeee0ffffee00ffffee00ffffececffffececffffe0e0ffffe0e0ffffdcdcffffdcdcffffccfcffffccfcffffccccffffccccffffccc0ffffccc0ffffcc88ffffcc88ffffcc00ffffcc00ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaa8ffffaaa8ffffaaa0ffffaaa0ffffa8a8ffffa8a8ffff88aaffff88aaffff8888ffff8888ffff8880ffff8880ffff0e0effff0e0effff00eeffff00eeffff00ccffff00ccffff00aaffff00aaffff00a8ffff00a8ffff000affff000affff0008ffff0008ffff0000ffff0000fffefffefffefffefffeff00fffeff00fffefefefffefefefffefe00fffefe00fffe0000fffe0000fffcfffcfffcfffcfffc0000fffc0000fffafffafffafffafff8fff8fff8fff8fff0fff0fff0fff0fff0ff00fff0ff00fff0fef0fff0fef0fff0faf0fff0faf0fff0f3f0fff0f3f0fff0f0f0fff0f0f0fff0f0e0fff0f0e0fff0ccc0fff0ccc0fff0aaa0fff0aaa0fff00000fff00000ffeeffeeffeeffeeffeeffe0ffeeffe0ffeeff00ffeeff00ffeefaeaffeefaeaffeeeeeeffeeeeeeffeeee00ffeeee00ffe0ffe0ffe0ffe0ffccffccffccffccffccccccffccccccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff88ffaaff88ffaaff00ffaaff00ffaafca8ffaafca8ffaaeeaaffaaeeaaffaacc88ffaacc88 else 0xfffffffefffffffefffffffcfffffffcfffffffafffffffafffffff0fffffff0ffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffffa0ffffffa0ffffff88ffffff88ffffff22ffffff22ffffff0affffff0affffff00ffffff00fffffefefffffefefffffe00fffffe00fffffcfcfffffcfcfffffcccfffffcccfffffca8fffffca8fffffc00fffffc00fffffafafffffafafffffac8fffffac8fffffa00fffffa00fffff0f0fffff0f0))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x50a32bf else 0
  | 3 => if page < 1 then 0xa850e32bf8436c481ea0421c68aa54514c898cb75142691c21b61da14654c8aa545d4c8aa544d4c8aa53414c8aa53354c8a8ca99140f8a299140b8fb254c8a else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x5f9c38bf36717e69e414d365e1a38da34699e68d2fccdc5e99b8bf31f17e62e528867a5108f4a1a9d6a2ce4185969a8b1d2f1638ac2c744455a6d8ab53514ba28215bc842784076b0e0c5a1a18b4103168f061d050bd9b615d2fc25c8c83a6ef059dd808d36811a6d81f4bf0371cc05caf807c5f80b9428c8e9516180278f004c1e00973c012c780256f00499e00923c0094e80124f00227c0038f8006ef00065e000b7c001678002bf00053e000a1e0013f80026780001f else 0x732383d884b983d18cb743d1843283d19dc203c594c203c59f4643c35b9543cc730ec3d8840903c5732fc3989b4203258cb60312a54003068cb74311828943067336c1586aafc158962fc14c9ec201459b420145a541c145a5450143a036410aa036010a98c14106a0390109a0460103a545010398c14066a0421c41005264270052a407004f61c7004f61a7004ee1a70052a1870052a1670052a147004f20a7004ee0a7004d2087004c6087004d20670052a0470052a027005360070052a00700529fe700515fc700511fc7004fdfa700445f87004edf67004a9f47004edee700421435004c512e00414ff60040cff6003e0ff600478fee003a8eda0036ceda) else (if page < 3 then 0x9b4157e0a2002a1438c8c0151a0464600a7d023230053a811918029b408c8c014ca0464600a5d023230052a8716180295408b0c014a8cc58600a55022a30054e95141802a34a8a0c014fa5450600a546e2830052232ed18028319768c014a8a3b4600a1465b630050632db180295166d8c01418cb60600a5451b03005020ad8180285196b8c014a8a34c600a5501a430052a8ed118029543688c014a8a2fc6009f46566300466109188020ce648c40132732452008cc20f71004d9cc7a4801bcbf3b600119741da400a236ceca004c9cc76480232dd3b4401448c9d860098c14d06004f17e66600272bf333000c85f99b00087acccd40052a28661801ccdb1ce00119828ba400842805940052a242930026ca214b000bf33099800732c443800466102188020ce610c40132730852008ec143d4004220a1ea001fabf0f5000e65887b000732583d8 else 0x14aa0421b6bfa550232bf3353e81087322aa53684399154084399c48aa850232bf4552a81195aa2a813679bb4ed238cb717e76a54f61ec93348e3308730b247198436c3d3d84415921e98c220ac90f4da0ac91c07a471b84398314aa046d4c18)) else 0
  | 5 => if page < 6 then (if page < 3 then (if page < 1 then 0x75fdd3f60fd81f5ffd7bf5a7d67f49fd23f46fd19f45fd13f407cfff3dfcf1f3bfcedf3afcd9f357cd3f347ccff337ccbf327cc5f1f7c73f1a7c5ff14fc4df10fc3df0efc35f0cfc31f0bfc2df0afc27f097c23f06fc17f057c11f03fc0df027c07f017c03f9e3e5cf44f853e133c01f else (if page < 2 then 0x2407bc3b0f78641ef0903cf5f873d360cbe4418f3b431e5f863cb90c795a18f2a831e4b863c910c7a0c18bc7030f36863c5c0c787a18f0e031e12861eed0af92215f36c2bb41857ce605767a0a7cc414f94829ef0055ca80ab91815e76823cbf04797608f2e811e57023c8c0479ca08dccc10f43823c860478bc08f17411e26023c4a04748e08f11411e22023cbf01fa62037a2007e2f80fc5201fa95003c14ff66d9db4db0aea95141802abf0048be00907c00eef801dbf else 0xa3a45f3648bdcc8fed5113e8ea27ce644fa447ff3b4ffe829fef193dedcc7adbb4f3e769dbce83b792276f378edba21d9f1b3579b66af36cd1e989a1e85347a7c667a20cde730e7aed197a322edc7459e8d8b3ca01678fc2cf46453e890a7d1d13fa44267bb44cf5f899f1910ee92217cf442f98885eef10be3a1eeb983dd7087badd0f75641eeab03dd5487baa70f76121ebbd83d79f079f390f3e521e7c403cf67079ec60f6d041ef1d03de2a879e510f3ca01ed93c3cf)) else (if page < 4 then 0xa543c3168dc20316a84143168ec143168441431698bb430e98afc30e842803157316c31c5f90431c829003166d8f031a9b0e031c730e031c878e0316988e030e6d88031a7336c2ba6d8802ba9b2fc14da53bc1475f99815c84078155a936c11a7336c11a98c1410e98afc10ea53c41079b29410d9897410e5f82411ca7d02323a5466283844143d498c141060054a7af0055262f0051e62f0051a62f004ea62f004e262f004de62f004da62f0051e5cf004da5cf004c65cf004da5af0054a58f0050e58f0052a52f0050252f005424ef0051e4ef0054a4af00521daf004eddaf004f97ef004f17ef004e57ef0043d6770042567700415677004f166f0046523b else (if page < 5 then 0xa550232081cc60a23041a954084398200a54f61e70052a8f053802953d829c01529b414e00a84c60a70052a6d0438028136821c014a9b40ce00a54160070052a80fd380295367c9c014a9b3d4e00a5501e8700501cc9158026cbf47b4011d829fec0084414ff600415cc7fb001ccdb3ce80119769db400a536ceda00475b676d00236db3b6800e66d9db4008cb70ed3003994076c80233053558010f7699b800a92fccdc004897e66e001dabf337000cb5f99b8005facccdc005018e665801ccdb19680119840b2c008cc1459600501da21580280db10ac00bf330878008436c3dc00399b61ee00295080f5401198407aa00844143d5004d9da1e68027ae60f34013673079a0098b983cd004d9701e68026cb60f3400e65787b2008cb083d3004f5081e70017e760f7000ed3307b8009e9543cd004d8aa1e68017e550f3401361c079a00330e03dc else 0x2a54aa046474aa046e323a550233141d2a87196d8e95408436c74aa0415b63a550232bf1c65ccbf3b628136731d934aa02fcccca04f57e66652a8119330e11055f87a9366dafc3cc9b2fd081e64f57e660f3262bf2a87994a8cb6c3128cc21b61894c611050c1a33087306233182900306842fc7018a4d97e1e0c3295406d82154a98c14106))) else 0
  | 6 => if page < 6 then (if page < 3 then (if page < 1 then 0x9cafdeed3b79b676db6cd5e6e99bb3e333dcc32f2fc65e4d8cbc66197a322cf3983dd9e879f310f3dda18f2fc31e58863c950c7a0c18bcc830f37863c5b0c789e18792c31d24063c380c797e08f4c410f42823c5d04788c08f36ceda0048be0076fc00e9f80181f002cfe00587c0091f8011ff001ffe003dfc0076f800d7f001a3e00337c0064f800c7f00183e001cfc0033f80061f00087e000f7c0018f8002bf00053e00087c000cf80015f00023e00037c0003f80258f else (if page < 2 then 0x1e063e380c7c6e18f8d831f10063e1e0c7dcc15f8802bf0c057e540a7c3014fd0025f9884bf19097db612fb1025f6104be72097ca612f8fc25f1d04be31097c3e12f99821f0c043ec2067c300cfd2815f5f82be1e057ea008fd3c11fa5023f08047e0a08fb9811f5f823ea5047d3e08fa6c11f42823e66047cba08f95c11f27023e4d047c9208f91811f11823e22047c3608f82411fa501be66037c3006fd4807f8c80fe1801fe8f317d0258f98cb1f4a93be6d277cf97ef else 0x33183eef1cfd7e39fb9865f5f8cbe9b197ccc32fbbc61f330c3f19167dda21fafc43fa007bf3d0f7e621efc643df7687bedb0f7d961efb143df6207bec20f7d7e1efad83df5787be8f0f7d021ef9c83df3307be380f7e8e18fcf431f99063f280c7e3a18fbb431f73863ee60c7dc018fb7c31f6e863ebf0c7d6218faac31f54863ea40c7d4018fa7431f4e063e9b0c7d3418fa6431f4c063e950c7cec18f9bc31f30863e5b0c7cb018f93c31f25863e480c7c8218f90031f)) else (if page < 4 then 0xa54143168441431698afc30e7326c3195f8d831ca53bc107a550232300489dbf0043ddbf005497ff004897ff0046d7ff004657ff003b57ff003a57ff003017ff0046569f002fd67f0052963f0041563f002fd63f0039923f004c51ff004651ff0036d1ff002fd1ff0052919f00474fff00398fff00398f7f00398f3f00528edf00474edf00414edf003b4edf00398edf00370edf00464d5f0036cd5f00528d1f00548cdf0046ccdf00468cdf00464cdf00450cdf003b4cdf0036ccdf00358cdf00350cdf00330cdf0031ccdf0030ccdf00308cdf00240cdf001f8cdf001cccdf001accdf00464c9f00198c9f00198c7f00528c3f00414c3f003bcc3f001f0c3f else (if page < 5 then 0x58a6c31ea54203178cc20317a541431784414317843d43179ecc430f98b9830f98a9030f7328c31d7326c31b8326c3179926c30f98a6c30f9b21031e7320431e4da0431e9b16c31e7316830f4d96830f6113c30f6112c31d6112031e9890030f5f8fc31e5f8e031e9b0d831d730d831d5f8d831d540d831d988d830f408d831e3e8d831e2a0d8317840c431e730c431e4f8c431e4d8c431e268c431e248c431e5f87831e7306c31d1886c31ea52fc11ea54d810fa54c410fa549c10fa53bc10fa521411ea517411ea5164117a5134117a511811e8288c117a508810fa54da0a7a54c60a77336ceda8cafccdc76afccdc5fabccdc8cb08cd39b2fc3cd5f9983dc else 0xa1cda62f9ecda62f9b4c658fa55017efa04f57efa04c57ef9b4c57ef76b98ede732fcede8cb98edb7336cedb73354edb97398ecf8cafccdd76afccdd5fabccdda5500ccfa04c4ccf9b4c4ccfa04b0ccf96464ccf8cb08cd77eb08cd796308ccf77b9865e77afc65e77a6c65e7799865e8cc4059e9b2fc3dd732fc3dd9ecc43cf9eafc3cf98afc3cf5f9983dd76b9831ea02fc31e9eafc31e98afc31e8cafc31e76afc31e732fc31e5fad831e6da8831e6da7831e82a6c31e5fa6c31e))) else 0
  | 7 => if page < 1 then 0x4657ff76affedb5ffdcc76fc64cdf6d99bed5337d8466fafccdf3919be6630fdde32fafc3df9b063f310c7dcc18fafc31f54063ea30c7d4418fa6c31f40863e660c7cb418f8fc31f1b063e310c7c3618f99825f0c04bf4a047c3008fcda62f5f99bb2c333dde32f2fc31e98861e810c78b41878c431e5f99b80076fc00bff80163f0023fe003b7c006af800cdf00187e00197c001ef80031f0004be00047c012c780065e else 0
  | 8 => if page < 1 then 0x5ffd9be31f else 0
  | 9 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x36 else 0
  | 3 => if page < 1 then 0x48 else 0
  | 4 => if page < 1 then 0x168531042f else 0
  | 5 => if page < 1 then 0x14c531042f0bc1d else 0
  | 6 => if page < 1 then 0x104411042f0bc2f else 0
  | 7 => if page < 1 then 0x2f else 0
  | 8 => if page < 1 then 0x1b else 0
  | 9 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 14
  | 4 => 209
  | 5 => 346
  | 6 => 367
  | 7 => 57
  | 8 => 3
  | 9 => 1
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
  | 2 => 1
  | 3 => 8
  | 4 => 181
  | 5 => 267
  | 6 => 307
  | 7 => 77
  | 8 => 14
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 2
  | 3 => 29
  | 4 => 654
  | 5 => 965
  | 6 => 1103
  | 7 => 275
  | 8 => 48
  | 9 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 5
  | 4 => 7
  | 5 => 8
  | 6 => 7
  | 7 => 7
  | 8 => 5
  | 9 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 11
  | 4 => 15
  | 5 => 16
  | 6 => 16
  | 7 => 13
  | 8 => 9
  | 9 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x190e105809 else 0
  | 4 => if page < 3 then (if page < 1 then 0x8000020220202002840e183840a5008224081120230604020008026002000a18101280441a060800020080110a183006a701811008000 else (if page < 2 then 0x6140961810d0c020019218a0284100c001061c005040c5800c0098002001070e101023600980160401500501001c101820e102083210013 else 0x127a1813944104990204019000011b261c002368848d06040000044013040d383200c3030e140320004182380890c)) else 0
  | 5 => if page < 5 then (if page < 2 then (if page < 1 then 0x31c2e000e020b04050013010402190203081003123701020002020b0e0403050002000d0000010201021112000002040b000300041508090300000101042003 else 0x104001400010324051502200f000001030000010306040000010017041a02030000040000240f0102000d0506000035090c0001080100090007010001040200) else (if page < 3 then 0x5070e05212b080b030828000000010103070003000e00052d03002404020c1c000b0508021b0d0d0d05010102000005001b0f0217010b000405001b2b050010 else (if page < 4 then 0x2e26013202060f0b040f01080203010200530e03000f3686061f09050a1c064f000b1d003c010339050d0b6c00070117052c060a1e0101171a0000010e011707 else 0x2051f000804050203021e))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x261c4000e04484002c38c00004a704d4502021c100567408600006040c04980122048c0a08501062c08e48000010608f000224202160018c else 0x121c20300000841400980000968030540880c60c8b0c2d1870208081044810002f440408200000030500022410802000000c54e890060382) else (if page < 3 then 0x5e006033a343820e040841eac529009801c086000627348100c116830608183149c202140c28e1a0c0910034308340098206344802600056 else (if page < 4 then 0x3d3801df8d042e000830a0d4840441700065038200100025800b8500144a0140418018060020801112001898a020058d1004e863000394 else 0x447890c30d250c180000008005180020d42100810c010820a45900043c88000009800009e0108300060e08200))) else 0
  | 7 => if page < 2 then (if page < 1 then 0x20a08021040146f4002060461c4c6808000503840a54006000158200000000028b0a001c811008c0010c100000e0000800581802a04300 else 0x114280041a871260804d85) else 0
  | 8 => if page < 1 then 0x22180791003e31c0b else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x1800584bedc5a0581680b0000100280278c0e5e0000010028c38010c2024918300080482000 else 0
  | 4 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x4da1880331209208b3f5b6db04320006017ccb3810c9eac64f7230430000af612601b00a39c4bc0c81900614b0c4d844811ced24c4bc813c03c9271e810410780003c80b6089786ac95e00ce3c000004000008eb4b67acedc09a160d980a121e80021400000b400000ce011e0000065880f44a731b40b406 else 0xabcac367358a822a7f7a0a48237db14c6000076d280512c37c1de8093825232381af821cdbb434d80b386a48583c00000000280dae0cb0000005800501c00015320b3260c11e0c681ba120b4000028a64202c4e0fec2a598000610400001b80e809aacce198a55870000118000003e4867920002f580081) else (if page < 3 then 0x551a0000000000013c03d6a6282680000000000004df100001e033c0000000002458334cb800000a7240000000960316015c2b9e150982810a2629c85692d862e0139673bb6ec0a919df8248054556ba52e49980c2c12e44ad8d520196621cb2e03a60981800000980140000032c048833ab69869281c52d else (if page < 4 then 0x83e02ac2dc1b4078401321afe06400960eba062c80a0112c010632c18288be617a0160d3886b1076f36b185308af9038016c1226016616f2f04950826f0470272e5659a3c414f25886800000000001f800888122407a72c134800b42df7aded5580045af80b17800e01244264af645fb20000e031b030000 else 0x73258e028e63b00388000033922f01bd7982231b851cd63004c1248098000000ce1cfe0244800018b828a5b8800124b60e10c658c0e792a189c0284894b6f608a8560805503006161f2f8029e56f554c03588a41f4b78941000026880002378dd03cb6600001423a82a9c200010c917f17a007af44000000))) else (if page < 8 then (if page < 6 then 0xf3e5002f892c3c4a925126b020a87123f2c003cf1515a92584000005d886b0cdf69741c03100004600000000026dcc4d86806749215e36794c6288d6a004e6800032019d3c00012708e5b650cc520cc64100883d0e01d59538c00016a09c10284935b55cc1986045d6b319a789808c404709371c8318000 else (if page < 7 then 0x77355e1800047828deef86a90814da8eb65121b805bcc853ce221540338cbe063a0f17102c06f00ee0a9834802263932028402300700443a6f81545eb50716354c85fb04200d8250401000aa003600f9e0fbc583083409803b1a7700ea68906208642d2341a4004f9ece213002e01be802a0ed4617824671 else 0xbd069c832cd95dd00005401386000000000002b6f00008b04b368000515a4424809cf800000c3daf6689a13604a6644c6458414809e3ca2001f88000213d92005c007e022003b71b3010ea8484c29281e3d180000b402f842fda00012a02cef2e80ac100000000000006e20001f8c0000b70400000000000)) else (if page < 9 then 0x531a43a02888000763025907800a83721994227c00000000000013a456da000152240000000477b98400b480005b180000000431ebcbb180800000008ebd7ac8cad000075114e2ca2d000000000000bb8595ab436fa60000000058ac000000000844f016ac0d2d5083000000009cc671ab9220001eb03680 else (if page < 10 then 0xc2040000000398804001a633004e7551924e2ae4786203600521b1768e9b1411516e04056060000000000062800001600ad808000af017e0000000000800a9c80f02010600339a562a310631e000009b60000ba044286ec72c022f01880a1cc165d70000001943c4806292f0014083600cc1a60080000000 else 0x13125fbda6600000dc00000be0cd720000648c61008a86e803612)))) else 0
  | 5 => if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x613c00000000000026000000565e4c80555b2f4870183604659265849f9b00000000000000008280a2603db09d197c0695644c125ca0099e613e440030993a1f789ca646484152f69d9f50f072a6220079843a19a32d3018a68224cc2e03668443827348aab48398160c76044a897e0c55db3098068324908a803880 else 0x89147d8c4a6051219380ab10768026e06284a8cc74981e7000005a64a8904fad1a9e769e299b24010b9224c92b0600005c2061543e9a3b195aef8615361c228228009682541801a13c00870b0000351e6f437e92590072d129068663a94d979e7b66873540829c0257700f81a498aab10000068c021fa2e0aa3100009dc82283) else (if page < 3 then 0x2adda292ac04a88d9d9027dd968087430ead372361186f6d3201589e94804e001f004c920000161e000088829a9053de00009d800000920600000000000019980d922b30808114986a950212aa8c00004c8100004a98000000006e9eaa069a19000021845b750000701b6d2b083c0e00000032607f0000006681258090801289 else 0xa806b379a4c9d9910da0d8080008500a61881180680ac1c8702a5807580585000002e5a87950000576da08600009f9a6ea07048000000009c94000000009dcca1814c0157634b9e000032806f80000000009a10808270324a8059a100006e084c002fdaa6c30000000018e90000889aaab74b0000003f807dad27dc00000000)) else (if page < 6 then (if page < 5 then 0x51f062819f8260009dc9889887185da127002983700d9f83620078992692065a32827a0644e031e0a88c03009d4e9c8c97a076016f8500009f9831000b007f1945002a5d745a2f039880369f043d0200162137887f1f215a4900a6c215a16a12118894a5043c164c92a11921339e81007901335b34809a803102a8c809816f83 else 0x5002da908ed1e006801260931819f801648ab6167607c98361911bd2d183219318409081ba058566d929f4847b747b138000682760e7c00a3866f427e028b806f4600008700000068040000000060206cbe3d0425c19a49178013404f693c80271871801a1865121d804e80000026946f84231e0000488049803b6c4b80a780) else (if page < 7 then 0x6780219200007e003b420b696300000000002e80000049183aad1200a881a461000000003aa300009f86535c6998888a0000026000006cbc3981610200008d8009e84c842f188600990d3000718107003b9899033ca092567e843c686f7000004b5a618273da00009e03349e059e00008be15089000000006912288600000000 else 0x7be95b811c04535d1b0042497fe6000032120a51930365003b012fdd0000328113db2fdc6a04a60232848a026504000000000000000000003292000000006e00595000000000000000000000a184a91000005f0000005f062c01000000000000000000007de40000099f000088b523a1ab835e2116da3d98a800000009929c80))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x945a99808eb0175d88809cc80000424f3d12a700000003216da0000091635f9e7619771e2f1b0000821800006180000032e00000809800009a0000007fe0000000000000000000004a356f822a80a02158802e5c49980000ac1904407de8012d69006d802b8099828080920019dd54803f188580a4122181680074820f700000 else 0x580056983b800000338082009d00764b361861bc2f5d57d097801b1ea6f000006ea1000088029a0d715d00000b1e5c1e06da4d002780ac004383939b2c00000000008d5c0000a1008f8000004be030800000916d0000959f00004b9200009d8d0c807ae06c344c6066006ec83f989c8aac18a6c67f06000057800000) else (if page < 11 then 0x6280182170028bb0a6ec330081989386968c6e04658143487e0173dc8b3000001c089c0c4481250900000000761800006080535a7686149e00004d0600000d84a28076008b06048000009c8e065c1d007a0066e063804898078091806960320c0280a900517100009d4867aa8b866bb86d9ea368458020032c801b18061b4530 else 0x3b6e1e06000000000de035806f02503f0000779e369996816de99e029b85a6ed61560b84200010008780980c4b983318ac42097087983b0422808963321806c83c1e9e9e20c835a07003a38086ed62029000611a36814ce04d806d1a569e16208115372d6dad043078811cbe32c847308e00308184007d69161012b33e82a980)) else (if page < 14 then (if page < 13 then 0xaa00000248d8b130c01ab3270802f001c803c181e886e01468083001fa11b21a020703c000000000000970000002e1b7a1f6de0a01e4840ab8274808c70000039004c040406a600ab8047369250418009e9ab126601ab0874061d8954003b1caa878d826f6c781c76020000000000005fa03601000009e06a0100000000 else 0x61d46a0068ca00002180a08c6f8180843c9e4a433180061006189a9942c88f09060340000f049b0467000000a39d02220000335e8d5a2d009da24b7212bd000072e05d213600565b62011ebc3c6941028480890272005e801b20a38405808099ac010d00320041980000341e961989801a000000000008e3038000000000153c) else (if page < 15 then 0x4d3044802480142006003b446da326883980788409a2a67137698a403c605271701a610064c86da15c80a8c9945c75003c668782871a0d814d49179e65010080a5001cbc3e0009a042ce644860060b1800009dd0a0c9ac80978658065b6b09a19cca5f8070004630000000000000aa8a8cf100001c98075a000053db67018498 else 0x115a3c98679c6b319d8c)))) else 0
  | 6 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1a1a058151023d001a09722060207f01b0be979f3501a266aada2c8c6b3d59807a3cab80898600005218000012487a3e75200504378000c11d3c0c18520210901c5ab50457811dbc860000000000b2a5a81aa6989f0c00009206000054840000000000000000000000004b0000003f04a38000005b830300888089009019 else 0x3f01000000008e8c6b800000000000000000773c000062800000380100006f8183c83e0c7f1c50ac68897f02244000005780b3809ea21b1bad810000859073988d0000005682000000004f8069da31820000739e11800f03239200003b809d0c00005ddc90993f1c5a803e8092994f190000289b000000009b9ca5016fa06d80) else (if page < 3 then 0xaeb25004058022e9a000ad8455ec3c9e270100004b6079061bdd0000901c53827abc96e993e00000288200002580b7638b06813c23845a000000a1ac22ac00000000b4b2000000001f1e4b18000097927f0c2d069f80189e29dca519b203794031026083a51c4d1b55003a8eb39e716930dd00008200000000009e60ae009780 else 0xa388158ea54277a173004d126b0831836ced3c1e6818a704705d4e001fb1902a2586119085482681a11f880197a29e8c55807a3db287888122e83b4b00c01a350000444b00002986000052803e02000059122d9b931c01c8548012600ba0a11928a8aa5d08613d181d00000000001fb00000000000009e12600c97e0b4b0)) else (if page < 6 then (if page < 5 then 0x890121981b5aa56c05120000a8188300492a471b9892b080611eac3c976987900000000000004a4b00000000000040aa530067bca56e00000000101b351849860000000000007fe000000000630800003660ae841e83b71a000045807a00b501a469229875b602038586278c1388698314086f483288501cb56c653600000000 else 0xaeb01918aadc0d0cac0000000000a11e000042a12f023ca000009c1203cb000017194b88048000000000b4c27989830600005cdca680b21b000000000000a9716b0917800000b488000048490000a30100008b98b0bc199230dc930412dc00000000b542af04b5058412420818604e0115697830a79211001c5c50e86b3c) else (if page < 7 then 0x58982e00b6805bda6ce302024e1fac82191200009c1f0000399c7a815f5a1dbe57822949075a491c9b000288b71800006f0c00009a008f0e3e998f809c223f192d283c20230820844480000000009e82b2865b702d839b06182d00002282a49c40e6000089a69a868b80850c386c129b8a0300000ca052007900a2604e1822a2 else (if page < 8 then 0x6300b09890003898310043800000371e78bcb5c28080831b42808f00b6e000000000000000000000000000000000000089873688583c21003b0e502aac54568000006748384213017f19a700000000000000000089818a81a8950000450077005fbc000060da930109090000a83500006e10000040e84d226e807c0074a0ac02 else 0x5d5d068122806bc070216c5e74a15f801a3372988b002e21894893199d8c22a38f99a8809c607a182c82131cb49c5c5ab00047800f808c1b1d98041e0780248091996a09aa21529896803acb6a3100003000000070f218984d1f065a04981a0b2a29b5bc00009d826d703fa27a800000a48400004d600000a31863b05c830000)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x4012a42d82bc3c80b18020926183038e2600b4817ee95718b2807f921af1229f64981ba1b58135b159607b807a33668399807620acbc8d8c653010032e8c571a4c001b5c86062b1b0c005602afb618808e823f9f9f02a8099f2c0400a300761e219c34304ea1844c4e19601e7cbc4e1e198450666906a1aa9a8051804060018c else 0x152d809815cb210130862dda1304845025031800121200008e002700908072218c026c5b729eae88a1e650a298600000000091801a188a9800000560115d325ab4c4972d2e5d6b0001039d84a1e88a5a4c80a9da7c0118810000828090aa89a400009219a3bc000031da875db4860000181800008f19218080e358e000008414) else (if page < 12 then 0xa28026063a04318058804d029412678036b350604e806900b0188800a800290c898029da5380b20064674f00a59f8580b7154188a802a6009800189942a39d9c560019002d29b4ee8601436987803d9e5b717e005c9b75b0b5ec6b331d803908a3bea9700a308a06ac805582a319120c3f8054605d21841070e496696f1e8681 else 0x8303790300001f0019804722501247605318afb05eda6fa17b3c0d8047025a01ae997930a83317004680160023c16d810ba1b2065dda3d807a32b28195085702751e5982af3c02006261acd41a00a99b98840f81991f71a19922a1186048b2cf9d814b6664809f680c9ea9832b03b49977a07318000059842810a08022ad7ead)) else (if page < 15 then (if page < 14 then 0xb6006f200000abbc46002499a59e3788008800005981683c8700590013190000a544683e000000003080a7e0000094884d80358600000880ad000ebc9baa39aa1b0321aa2b80b4002ddc0000553c471200008480958800003da00000000022010933203c39000000b7000420000068b3000018697b00000000000b69229a6b32 else 0x4888890c22e064612c001680909c689851009c92000093e698120aa16f80305aa286338071a07a09b6922c2100001e63000081b000006e9e8a00840d00000000269853b1471f1e9b50a32204b18650ad6b18b71459ec00000000ae9c9c009e9f6e211e6d946076a1000009de0000a618928019e06a800000612050e9) else (if page < 16 then 0x45197d80ab5d9d0237182f904108a09e7f04b48412da53b0838c0f10000000005c0389ce50803308911924411cddae81a9dc3c8159c2a5801960000000000000844e6930af018c8c7a0884491af080957b402b90521ab2d237bc0000b3002f0c00003a010000b762000023c07d0068005400238849b19f2a58002ec891000000 else (if page < 17 then 0x5cda06038680b702b2a81a02480c8d822add2a802d002fda54e09f662583a8e374205a8134b07b81a80bb58458924a0e5e5d9d99a0a0b101a0068cc98f4b432d01daa50427c8800029803804ae86010000006309960089d0148800006589a3980e3032034ea009db86075904025a440e666055c240ac81008481b1002292b4ec else 0x9ce0000018668a1b5700b306689e8a5c9200389e4a80189f12839900a898))))) else 0
  | 7 => if page < 5 then (if page < 2 then (if page < 1 then 0x1482559a014804202f0599a0ae8003706409d1ee8f1e000800000a12ac000090f8206232000910ec084c0e01e023602f372e9880be21f1800002e6625e04703bcc3620706c809804a21ab4a011ad2649c0080cd81e211d0d38030f56b68003829c3244a555222 else 0x7024ba2db9780d20000293f1920000002238e8856d0601731404d8c5b75b0c0000006409609b1b000281a94600050c0003540a0800004009c6f8e2cc00000017000000002501586a415063600000910062221059eb0200000000000004000000d5d0003e02400000) else (if page < 3 then 0xcd9947a0198811c00d7430d6dadc02c053c0d5cb815402942000c804782833a04bc1d7a7400000609660a0cc280140b20800148c9c40002803202ad500015bb983956c1a0a439b06463c30e00a000c085729448804010001f05100973000000110660acc22f3549e else (if page < 4 then 0xc00544930141c38128100baf860000000001104ccdd01a447998740000330c780000040800000058000006b94a010930511d210c0424a180b44f088c0612811601c81b1824189600ad6602301060c402864c41306ac416818c55ac56e318f542800e00ec6ac01703 else 0x2e02bcd580a402873704000cd97002004000d4f000243d9883449886bd04ed))) else 0
  | 8 => if page < 1 then 0xe086661f3308d7ab0169a27a1e008880000804ca121284225100034c196618104c179400c980580400219002a590000000004f18000 else 0
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


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x11111111
    (fun r => ⟨(0x718510308100 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x5050505
    (fun r => ⟨(0x698490288080 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x550055
    (fun r => ⟨(0x594490184080 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x5555
    (fun r => ⟨(0x38c288184080 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x3030303
    (fun r => ⟨(0x658450248040 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x330033
    (fun r => ⟨(0x554450144040 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0x3333
    (fun r => ⟨(0x34c248144040 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0xf000f
    (fun r => ⟨(0x4d24500c2040 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x0.target 0xff
    (fun r => ⟨(0x1c61440c2040 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x0.raw 4 (@Sub7x0.lower) Sub7x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0x55555555
    (fun r => ⟨(0x79c69859449038c288184080 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0x33333333
    (fun r => ⟨(0x75c65855445034c248144040 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0xf0f0f0f
    (fun r => ⟨(0x6da6584d24502ca2480c2040 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0xff00ff
    (fun r => ⟨(0x5d65544d24501c61440c2040 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub7x4.target 0xffff
    (fun r => ⟨(0x3ce34c2ca2481c61440c2040 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub7x4.raw 7 (@Sub7x4.lower) Sub7x4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p
def cutFor : Nat → List (Nat × Nat) → CutCertificate target
  | 2 => cut1
  | 3 => cut2
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
  | 15 => cut14
  | _ => cut0

def suppliedPrefix : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | j+1, z => if z=0 then [] else ((z%256)/16,z%16) :: suppliedPrefix j (z/256)
def selectCut (code : Nat) := cutFor (code%128) (suppliedPrefix 3 (code/128))
def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2 else 0
  | 3 => if page < 1 then 0xa0000000c000000000000001000000040000000c000000400000003000000060000000000000000000000a else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x80000001000000020000000400000008000000100000002000000040000000800000000000000600000028000000080000001000000020000000400000008000000400000004000000040000000000000000000000200000004000000080000001000000080000000400000008000000100000000000000000000000800000010000000200000004000000280000001000000020000000800000018000000100000002000000040000000800000010000000200000004000000080000000000000020000002800000008000000100000002000000040000004000000010000000000000004000000000000001 else 0x20000000400000000000000100000002000000040000000000000010000000000000000000000080000001000000040000000c000000100000000000000020000000400000008000000100000002000000000000000000000020000000400000004000000100000002000000060000000400000028000000000000000000000040000000800000010000000c0000000c0000005000000010000000200000004000000080000001000000060000000c000000180000003000000060000000c000000180000002000000080000000400000008000000100000002000000040000000800000010000000200000010000000080000001) else (if page < 3 then 0x20000000000000000056460e000000117959562ef2b2ac5de56558b000000080000001000000018000000800000000000000000000001800000030000000000000008000000000000002000000040000000c00000010000000a0000000400000008000000500000000bcacab1800000000000000180000008000000000000001400000028000000500000002000000040000001800000030000000200000008000000180000001000000020000000400000010000000100000006000000040000001000000010000000e0000000400000000000000000000000000000000000000000000000000000200000004000000080000000 else 0xbcacab16000000000000000000000050000000000000020000000280000003bc9c9b16000000200000000000000010000000200000006ae6e685de56558b)) else 0
  | 5 => if page < 6 then (if page < 3 then (if page < 1 then 0x1123400000000000448d0000001600000000000000600000000000000000000000000000000000000c000000000000002c00000000000000b00009a1e0000000000000058000000b000000160000000000000058000000b000000160000002c00000058000000b000000160000002c00000000000448e0000000000000000000000580000000000000000000782c00000000000000000002c180000002c000000580000000000000160000002c00000058000000b000000000000000000000000000000b000000160000002c00000000000000b000000160000002c00000000000000b000000160000002c00000000000000b else (if page < 2 then 0x3c16000000000000f058000000000002c1800005830000000000004d0b000000160000000000000000000000000000000000000000000b060000000f0000001600000000000000000001d8b000000000001342c00000000000000b0000001600000000000000000000000000000000000000000000000000000000009a160000002c000000000000000000000000000000000000000000160e000000160000002c000000000005e0b00003a160000000000000058000000b000000000000002c00000058000000b000000000000002c00000000000000b000000160000002c0000007000000000000000000000000000000000004d0b else 0x600000000000000000001342c000000000004d0b000000160157343c000090600004d0b00009a160000000000000000000120c000000000001562c00000058000000b000000160000002c00008c68000000b009a891c0001342c02ad305800000000000ab160000000000000058000558b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160c009a3c16000000000000f05804d1e0b000000000000782c000000000000000000000000000000000000000000448f0000891e000000000000f0580001e0b00693c160001123c00000000000448f)) else (if page < 4 then 0xbc9b160157362c026e2c78000000000009b160001342c00000058000160c009c9a160112763c0001ac580000000009c3b160134762c026cec580001d8b009a8a1e0001342c000000000000000000000000000000000000000000000000009a160000002c00000058000160e000000000001782c0000000000000000000001c00000000000000580000000000000000001343c027230680004e0b009c8c1a0139183400000078000000000009c160000002c0002705800000000000ac16000000000000000004e460e00000000000000000000000000000000000891a000000000002246800000000000000000000000000000000000000 else (if page < 5 then 0xb82c000000000000000000000000179382c00000000000000000bc9c160159382c00000078000000000bcac160179382c00022c7805e560b0000000000000030000000000004d8b00009a160001342c02ae68580005e0b000000000001562c000268580000000000024180001562c026e68580000000000000000001342c0000000000000000000231a0001342c02ae6c58000558b0000000000000000000000000000000000000000137123c0000000004d9e0b00000000000000000000b06004d1e0b0000891e0001123c000000000000000009c3c160000782c0268f05800000000000000000d2782c0000000001e1d8b else 0x2f06800000000000ac1c000000000000000005e560b000000000157342c0000000005e560b00ac9c1600000000000000000000000009c3c160138782c0000000005e558b00ab9b160001362c00000000000358b009b3b160000583002f2b0580005e0b))) else 0
  | 6 => if page < 6 then (if page < 3 then (if page < 1 then 0x891a0001342c00000058000000b000045180000463400026858000000b000034160000002c0002ac580000000000000000000782c00026858000000b000034160000762c0000b060000160c000000160001382c00000078000160c000000160000762c00000058000000b000000160001782c00000058000000b000000000001342c00022468000448d000000000000682c00000000000000c000000160001343c00000058000260b000000160000002c00000058000000b00000016000112380000f058000000b000000000000782c00000058000000b000000160000002c000000580000000000000160000002c00000058000000b else (if page < 2 then 0x762c0000ec580001d8b00009a1e0000782c000268580000000000000160000b22c00000058000560b000000160001562c00000058000230b000045160000002c00000060000358b00004b160000002c00013058000000b0000001600008a2c0000005800000000000000000000000000000000005e0b0000bc160001362c000000580004d0b00000016000000000000d4580001a0b000000160000002c0002f058000000b000000000000b42c0000e858000000b00005c160000b82c0000f05800000000000bc160000002c0000005800000000000ab160000002c00000000000560b000000160001782c00027058000448d else 0x1600011238000224700004d0b000000160000682c000000580002b0b000000160001562c0000000000000000000891e0001123c0000f0580000000000000000000782c0000000000000000000891e000000000000f058000448f000000000000782c0000f0580001e0b00003c1600000000000268780004e0b00002c1800005830000000000004d0b00009a160001342c00026858000000f00002c1a0000002c0000d058000000f00002c1a00006c2c0000b060000160c000034160000682c0000d058000000f00002c180000762c00000058000000b000000160001382c00026858000000f00002c180000002c0000ec78000358b)) else (if page < 4 then 0xbc160001362c00000058000160c00003b1600005838000000000000000000000000000000000000000000558b0000ab160001342c00022468000448d0000ab18000000000002f0600001a0b00000018000000000000f058000558c00003c16000000300002f060000000000009a160001343c000268580005e0b000000000000002c000268580004d0b000000000001562c000000580005e0b000000000001562c0002ac58000558b0000231c0001342c00000058000228b000045160000463800008c68000118d000045160000982c00000058000000b00004c160001562c00000058000000b0000bc160000002c00015858000000b else (if page < 5 then 0x34160001363c000000000005e0b00009b160001362c000270580004d0b000036160001342c0000b060000160c00002c180000682c000270580004d0b000034160001382c000268580001a0b00002c1a0000583400011458000358b00006b160000762c0000b060000160c00003b160000762c0000ec580001d8b00003b160000583000026c580004d0b000035160000682c000168580001d0b00003c16000058300000f0580005e0b000000000001782c0002f058000160e0000bc160001782c0002f058000160e0000bc160000b82c0000b07000000000000bc160001342c0002ac580004d0b0000341600004634000000000001e0b else 0x270580004e0b00000000000000000002b0580004e0b00009a160001342c000000000004d0b00009a160001342c0002ac580004d0b00003416000000000002b0580004e0b0000ac160001562c00008c68000228b0000451600013438000158580001a0e000056160001563c00022478000000000000000000000000000f0580001e0b00009a160001582c00027058000000b0000ab160001342c000268580001b0b000036160000682c0000d0580001a0b))) else 0
  | 7 => if page < 1 then 0x2c000000000000000000000160000002c00000000000000b000000160000002c0000007000000000000001e0000002c00000000000000b000000160000002c000000780000000000000160000002c00000058000000f000000000000002c00000078000000b0000001600000000000000580000000000000160000002c00000070000000b000000160000002c00000058000000b000000160000000000000058000000c000000180000002c00000058000000b000000160000002c00000000000000b000000160000002c00000058000000b else 0
  | 8 => if page < 1 then 0x0 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 31 i

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

theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 1 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 14 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 14 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 97 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 209 0 = true :=
  (@span_join (checked 4) 112 0 97 chunk4x0 chunk4x112)

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
theorem chunk5x336 : span (checked 5) 10 336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 346 0 = true :=
  (@span_join (checked 5) 224 0 122 (@span_join (checked 5) 112 0 112 chunk5x0 chunk5x112) (@span_join (checked 5) 112 224 10 chunk5x224 chunk5x336))

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
theorem chunk6x336 : span (checked 6) 31 336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 367 0 = true :=
  (@span_join (checked 6) 224 0 143 (@span_join (checked 6) 112 0 112 chunk6x0 chunk6x112) (@span_join (checked 6) 112 224 31 chunk6x224 chunk6x336))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 57 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 57 0 = true :=
  chunk7x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 3 0 = true :=
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
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
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
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 9
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    9 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor10


namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfee8e800e8000000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 48, 49, 50, 52, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,26,27),(0xcccccccccccccccc,25,27),(0xf0f0f0f0f0f0f0f0,25,29),(0xff00ff00ff00ff00,19,27),(0xffff0000ffff0000,11,27),(0xffffffff00000000,11,43)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffffffff00000000ffffff00ffffff00ffff0000ffff0000ffaaffaaffaaffaaff00ff00ff00ff00ff000000ff000000f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaaa00aa00aa00aa0088888888888888880f000f000f000f000a0a0a0a0a0a0a0a00000000ff00ff0000000000aaaaaaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 10 => if page < 1 then 0xfff7fbfe7f6fd7f4fcff2fc7f else 0
  | 11 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 10 => if page < 1 then 0x15 else 0
  | 11 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 10 => 10
  | 11 => 1
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 6)

def bucketCount : ℕ → ℕ
  | 10 => 20
  | 11 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 10 => 73
  | 11 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 10 => 4
  | 11 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 10 => 10
  | 11 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 10 => if page < 1 then 0x5404d00a522f47100321 else 0
  | 11 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 10 => if page < 2 then (if page < 1 then 0x27a152304111555600db3180d80d9850cd82180c2004455004838c930a021004353c0090092004420021271000418162614c0480000241508009101330000832147020f461400018654a00369c1040c3 else 0x5380040000000c8) else 0
  | 11 => if page < 1 then 0x0 else 0
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


def goalColumns : Nat := 0xfee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000fee8e800e8000000
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut39 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0x5555555555555555 0x210620a30e41251661a71e822926a2ab2ec32d36e3af3e 5 10
    pinBase [0x0,0x5555555555555555,0x0,0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000,0x5555555555555555,0x1111111111111111,0x505050505050505,0x55005500550055,0x555500005555,0x55555555] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut41 : CutCertificate target :=
  makeCutCertificate target Minor10.target 0xf0f0f0f0f0f0f0f 0x108320928b41149361969b8218a3a29aabc31cb3e39ebb 5 10
    pinBase [0x0,0xf0f0f0f0f0f0f0f,0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0x0,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000,0x505050505050505,0x303030303030303,0xf0f0f0f0f0f0f0f,0xf000f000f000f,0xf0f00000f0f,0xf0f0f0f] Minor10.raw Minor10.nonzero (@Minor10.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut88 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0xffffffff00000000 0x828c38869c798aacba8ebcfb92cd3c96dd7d9aedbe9efdff 5 10
    pinBase [0x0,0xffffffff00000000,0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000,0xffffffff00000000,0x5555555500000000,0x3333333300000000,0xf0f0f0f00000000,0xff00ff00000000,0xffff00000000,0x0] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut89 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0xffff0000ffff0000 0x418c38459c7949acba4dbcfb51cd3c55dd7d59edbe5dfdff 5 10
    pinBase [0x0,0xffff0000ffff0000,0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff0000ffff0000,0xffff000000000000,0x5555000055550000,0x3333000033330000,0xf0f00000f0f0000,0xff000000ff0000,0x0,0xffff0000] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 42 => cut41
  | 89 => cut88
  | 90 => cut89
  | _ => cut39

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 10 => if page < 1 then 0x2d28b4a142854a2ca8 else 0
  | 11 => if page < 1 then 0x0 else 0
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

theorem root : pool 11 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk10x0 : span (checked 10) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer10 : span (checked 10) 10 0 = true :=
  chunk10x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk11x0 : span (checked 11) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer11 : span (checked 11) 1 0 = true :=
  chunk11x0
theorem verified : ∀ k ≤ 11, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer10 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer11 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 12 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 11
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    11 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full



namespace SignedFrontier.CliqueLink
def target := SmallCert.Full.target
def raw := SmallCert.Full.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 12 ≤ p.length := by
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
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 12 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 12 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12280_aux

open PEqualNP.Outside.L_meta_12280_aux

theorem PEqualNP.Outside.L_meta_12280 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
