import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12268_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4269866496 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.or, [1,2]⟩,
  ⟨.or, [0,6]⟩,
  ⟨.and, [1,2]⟩,
  ⟨.and, [0,8]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.and, [3,10]⟩,
  ⟨.and, [4,5]⟩,
  ⟨.and, [7,11]⟩,
  ⟨.and, [9,12]⟩,
  ⟨.or, [13,14]⟩], 15⟩
theorem size : witness.size = 10 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
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
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 9 ≤ p.length)
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
    exact ⟨witness, legal, by rw [size]; change 10 ≤ C.gates.length; omega, value⟩

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

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfe80fe00fe000000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 32, 33, 34, 35, 36, 37, 38, 39, 40, 48, 49, 50, 51, 52, 53, 54, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨24,25,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨24,26,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨24,28,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨17,25,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨9,25,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨9,41,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 6 then (if page < 3 then (if page < 1 then 0xf0000000f0000000e0e0e0e0e0e0e0e0ccc0ccc0ccc0ccc0b0a0b0a0b0a0b0a0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0a8a0a8a0a8a0a8a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a0008080808080808080303000003030000030003000300030002aa02aa02aa02aa020202020202020200ff00ffff00ff0000ff00ff00ff00aa00ff00ff00ff000000ff00ff0000000000ff00aa00ff00aa00ff0000ffff000000ff000000ff000000ff00000000000000fe00fe00fe00fe00ee00ee00ee00ee00aa00aaaaaaaaaa00aa00aa00aa00aa00aa0000ffff000000aa000000aa00000088008800880088000f0000000f0000000a000a000a000a0000ffffffff00000000ffff000000000000ffaa0000ffaa0000ff00ff00ff000000aaaaaaaaaaaa00000000ffffffaa00000000ffffff0000000000ffffaaaa00000000ffff000000000000ffeeffee00000000ffaaffaa00000000ffaaff0000000000ff88ff8800000000ff00ff0000000000ff00000000000000fefefefe00000000eeeeeeee00000000aaaaffaa00000000aaaaaaaa00000000aaaa000000000000aa00aa000000000088888888000000000f0f0000000000000f000f00000000000a0a0a0a0000000000ff00000000000000aa00aa000000000000ff00000000000000aaaa0000000000000000 else (if page < 2 then 0xaa88aa88aa88aa88aa88aa00aa88aa00aa80aa80aa80aa80aa0aaa0aaa0aaa0aaa00aa00ff00ff00aa00aa00aaaaaaaaaa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a08e8e8e8e8e8e8e8e8c8c8c8c8c8c8c8c8aaa8aaa8aaa8aaa8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a8a8a0a0a8a8a0a0a8a888a888a888a8888aa88aa88aa88aa88888888aaaaaaaa888888888888888888880000ffff0000888800008888000088008800880088008282828282828282808080808080808055555555000000005555000055550000550055005500550050505050505050503f3f00003f3f00003f003f003f003f003c3c3c3c3c3c3c3c33333333333300003333330033333300332233223322332230303030303030302e2e2e2e2e2e2e2e2aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a0fff0000ffff00000fff00000fff00000ff00ff00ff00ff00f0f0f0ff0f0f0f00f0f0f0f0f0f0f000f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f000000000f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f0f000f0f00000f0f0f000f000f000f0f0a0a0f0f0a0a0f0f03030f0f00000f0f03000f0f03000f0f0000ffff00000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f080f080f080f080f000f00ff00ff000f000f000f000f00 else 0xcececececececececcccfcfcccccfcfccccccccceeeeeeeecccccccccccccccccccccccccccc0000cccccccc44444444cccccc00cccccc00cccc0c0ccccc0c0ccc88cc88cc88cc88cc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0babababababababab0b0b0b0b0b0b0b0afafaaaaafafaaaaafaf0000ffff0000afaf0000afaf0000afaaafaaafaaafaaafa0afa0afa0afa0af00af00af00af00aeaeaeaeaeaeaeaeaaffaaaaaaffaaaaaaff0000ffff0000aaff0000aaff0000aaeeaaeeaaeeaaeeaaaaaaaaffffaaaaaaaaaaaaffaaffaaaaaaaaaaeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaa8888aaaaaaaaaaaa0a0aaaaaaaaaaaaa00aaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa0a0a0a0aaaaaaaaa00000000aaaaaa88aaaaaa88aaaaaa0aaaaaaa0aaaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaa0000aaaaaa00aa00aa00aaaaaa00aa000000aaaa8a8aaaaa8a8aaaaa8888aaaa8888aaaa2a2aaaaa2a2aaaaa0aaaaaaa0aaaaaaa0a0aaaaaaaaaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0000aaaa0a0a0a0a0a0aaaaa0a00aaaa0a00aaaa0202aaaa0202aaaa00aaaaaa00aaaaaa0000ffff0000aaaa0000ffaa0000aaaa0000aaaaaaaaaaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa8aaa8aaa8aaa8aaa88aa88aaaaaaaa)) else (if page < 4 then 0xff00ff00ff00aa00ff00ff00ff000f00ff00ff00ff000000ff00ff0000000000ff00aa00ff00aa00ff000f00ff000f00ff000000ffff0000ff000000ff00ff00ff000000ff000000ff00000000000000fefefefefefefefefefe0000fefe0000fef0fef0fef0fef0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcf0fcf0fcf0fcf0fcccfcccfcccfcccfcc0fcc0fcc0fcc0fafafafafafafafafaf2faf2faf2faf2faf0faf0fafafafafaf0faf0faf0faf0faf0f0f0faf0f0f0faaafaaafaaafaaafa0afa0afa0afa0af8f0f8f0f8f0f8f0f6f6f6f6f6f6f6f6f4f4f4f4f4f4f4f4f2f2f2f2fafafafaf2f2f2f2f2f2f2f2f2f2f0f0f2f2f0f0f2f0f2f0f2f0f2f0f0f3f0f0f0f3f0f0f0f2f0f2f0f2f0f2f0f0ffff00000000f0f0fafafafafafaf0f0fafaf0f0fafaf0f0f0f0fefefefef0f0f0f0fafafafaf0f0f0f0fafaf0f0f0f0f0f0faf0faf0f0f0f0f0f8f8f8f8f0f0f0f0f2f2f2f2f0f0f0f0f0fff0f0f0f0f0f0f0faf0faf0f0f0f0f0f0fff0f0f0f0f0f0f0fafaf0f0f0f0f0f0f0f0f0f0f0f000000000f0f00000ffff0000f0f00000f0f00000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000eeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeee0000ffff0000eeee0000eeee0000eecceecceecceecceeaaeeaaeeaaeeaaee00ee00ee00ee00eaeaeaeaeaeaeaeadcdcdcdcdcdcdcdcdcd0dcd0dcd0dcd0 else (if page < 5 then 0xffffffff0f000000ffffffff0a0a0000ffffffff03030000ffffffff000f0000ffffffff000a000affffffff000000aaffffffff00000000ffffffaaffffffaaffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff00ff000000ffffff0000000000fffff0f0fffff0f0ffffeeeeffffeeeeffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaa00ffffaa00ffff8888ffff8888ffff5555ffff0000ffff3333ffff0000ffff0f0fffff0000ffff0f00ffff0f00ffff0a0affff0a0affff00ffffff0000ffff00aaffff00aaffff0000ffffff00ffff0000ffffaaaaffff0000ffff0000ffff0000ffaa0000ffff0000ff0f0000ffff0000ff00ff00ffff0000ff000000ffff0000aaaa0000ffff00000f0f0000ffff000000ff0000ffff000000000000fff0fff0fff0fff0fff00000fff00000ffeeffeeffeeffeeffee0000ffee0000ffccffccffccffccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc00000ffc00000ffaf0000ffaf0000ffaaffaaffaaffaaffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffff0000ffaa0000ffaa0000ffaa0000ff000000ff88ff88ff88ff88ff880000ff880000ff0fff00ff0fff00ff0f0000ff0f0000ff0aff0aff0aff0aff00ff00ffffff00ff00ff00ffff0000ff00ff00ffaaffaaff00ff00ff00ffaaff00ff00ff00ff00 else 0xffffffffffffff00ffffffffffffaaaaffffffffffff0000ffffffffff0f0000ffffffffff00ff00ffffffffff000000ffffffffaaaaaaaaffffffffaa000000ffffffff55550000ffffffff3f3f0000ffffffff0f0f0000))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x7eb4178947eb41788c9cc89e466 else 0
  | 4 => if page < 1 then 0x268fd682f1471a7eaf146518d3f5a0bc4f52200d05e255fad05e28c334880341788c9cbf5a0bc4bbf5a0bc5189e06d05e28c511a7eb4178a38f3f5a0bc51cd200d05e28e8b00682f12f397eb4178968e3f5a0bc51ce5fad05e23a8b00682f11cfd682f136857eb4178a3424e600ea5e2227318803bd473991401e07f9cc01c4bc444e6310060a8e732280390ff3991401e0709cc8a00c051ce64500721c27322803ccd739913c9a06b9cc8a00f133ce64500729ae730068324d53989401e2a39cc8a00ee51ce64500789f6732280340e93991401ea66 else 0
  | 5 => if page < 5 then (if page < 2 then (if page < 1 then 0x9cc8a00d55e28e73228034178939f48a00d05e28e7300682f160a39cc8a00e15e28e73228034178719cc8a00bc5191277228034178a39cc4600d05e28e73228037978a39cc8a00d05e2067322803a978a39cc8a00e05e28e73228034178729cc8a00c15191e73228038978859cc8a330060a8e73228038978239cc8a00bc598da73228030546369cc8a00d0649c27322802f0ec409cc8a00d05b1c27322803c5a0709cc8a00d0398da7322803417e709cc8a00bc590da7322802f15aa39cc8a00f0519ae732280341886b9cc8a00d05196a7322803c4d6369cc8a00d0559ae7322802f1465f9cc8a00b4518c6732280341866b9cc8a00f5681ae732280340d63e9cc8a00f15197e7322802d1465f9cc8a00f15198683228034178a39cc01a0bc519aa73228035978a39cc8a00d05e246732280341788e9cc8a00d0649a64500682f146119cc2200d05e28e7322802f146429cc8a00d05e1f6732280341787f9cc8a270078a8e73228034192209cc8a00e65e28e73228034178599cc8a00d05e0ea7322803c546589cc8a00f15199a73228038978a39cc8a00d05e1c2732280341926b9cc8a00e4519ae73228034178a3 else 0x9cc8a00d05e22e7f228034178a39cc01a0bc54a8e7318802f146409cc8a00bc411027322802f1463c9cc8a00d05e1ba8f228034178a39cc01a0bc5188a75228034178a39cc8200d05e28e73228034d78a39cc8a00d05e2664500682f146139cc2e00d05e28e7322803b178a39cc8a00d05e0e27300682f110799cc2e00d05e1e67322803416e799cc8a00bc519567322682f146559cc8a00d05e25e73228035d78a39cc8a00d05e24287228034178a39cc01a0bc5195e7322803a578a39cc8a00d05e0ee7322803a98aa39cc8a00ef5191e7322803a978859cc8a330077a8e7322803418a7f9cc8a00ef680ea7322803407a3a9cc8a00ea5e08e7b228034178a39cc01a0c75e28e73228036978a39cc8a00d05e22a4500682f146149cc5a00d05e28e7322802f146459cc8a00d05e20e7322803cd78a39cc8a00d05e0c24500682f1460e9cc01e8d05e28e7322682f146269cc89e4d05e28e73006832578889cc8a00d0649b27318803b578a39cc8a00f1681fe732280341927f9cc8a00ef518da7322803a178369cc8a00e75e28e7300682f110369cc2e00d05e0da73228032d78369cc8a00d05b8da73228036578a3) else (if page < 3 then 0x9cc8a00bc519467322802f1464a9cc8a00d05e2368122802f146519ccaa00bc5192a732980341788d913f5a0bc5182e6d00682f1460b95c01a0bc5182e911c8034178a39cc8a02d05e28e73227f34178a39cc8a00d15e28e73228034178a09cc8a00d95ea8e7322802f946479cc8a00d05f23a732280341708ea44e600d05e23a7300682f11c1591401a0bc4e04273007bb41788e9cbf5a0bc51a16730066af14651a2c01a0bc51a16732b803417885a4401a0bc4da167322802f1465491401a0bc51952732280341789e9cc8a00d85e28e732280341788fa4401a0bc51a1281228034178a39cc01a0bc51a228500682f1468591401a0bc5184a730a8034178a39cc8a00bc5190e732280341787e9cc8a00e35e28e732280341786f9cc8a00db5e2164500682f146189cc8600d05e28e7322802f1464f9cc8a00d05e26a79228034178a39cc3200d05e28e73228037d78a39cc8a00d05e20200d05e28c361385c01a0bc5184e1f0b8034178a39140178a32204e730b802f146449cc8a00a32e1124500682dd46139cc5200d05e1fe7322802dd46449cc8a00cc5e1fe7300672f146409cc8a00bc5193a7322802f14649 else (if page < 4 then 0x9cc8a00bc519327322803417895a4401a0bc5186673228037178a39cc8a00d05e2327322802f146539cc8a00d05e28a911e8034178a3a3489fad05e28e6700682f146159140178a32705e6722802f1464e9cc8a00a32e93a4500682f12e1799c8a00d05e25e7322802f12e4e9cc8a00d05ca5e91398034178979cc01a0bc4b85672fd682f14628a434178a3158a27322682f1462c9cc8a00d45e28e7322803417898a4401a0bc5189e6722682f146289cc8a00eb5e28e73228034178399147e00d05e28e3d00682f1461091401a0bc4e8424500682f146178d401a0bc5180a73228034978a39cc8a00d05e27e4500682f1460c9cc01a0bc51a1e45038034178a37e34178a31405634fc7bb4178a399c89eed05e28e7322682f1462e99c01eed05e28e4500682f1462e9cc01eed05e25e731e8034178a39b46a00d05e28e73227eb4178a39cc8a00bc5193673228034178969b401a0bc518568b1e8034178a39ccd9a0bc518a28b227eb4178a3a34da00d05e28e7336802f1464d9ccda00d05e25a8b228034178a39cc01a0bc518a68b00682f146289cc89a0bc518b673227fb4178a39cc8a00bc5194a73228034178a1 else 0x9cc8978a3288b273227eaf146519cc8a00a32f1467322682f13c2c9cc89fad05e27a7322802f13c519cc8a00d05da7a44fd682f1461591401a0bc51876451a7eb4178a3a4401a0bc518763500682f1461da4469a0bc518b2911a7eb4178a38d401fad05e28c011a7eb4178a3a446a00bc51946911a80341789ea446a00d05e28e91358034178a3))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x9cc8a00d05e28c473991401a0bc3c88e733191401a0bc51ce64500682f146329cc8a00d05e28c1b3991401a0c65e28e73228bc01a0bc51ce64500682f146319cc8a00d05e28c4b3991401a0c35e28e7322803d5a0bc51ce64500682f1463e9cc8a00d05e28cef3991401dabc5191e73228034192bc42ce64519803b578a39cc8a00d064af047399140178a3200da73228032978a31b4e6450078af146369cc8a00d05e1906d3991401a0bc428da732288401a0bc1b4e64500682f06c239cc8a00bc519886d399140178a32d8da732791401a0bc51ce64500682f15ea39cc8a00d05e28c0b3991401a0bc518d6732282c01a0bc51ce64500682f158a39cc8a00d05e28c3d3991401a0bc518d273228034192bc51ce6450076af146369cc8a00d05e2ad473991401a0bf518d8013991401c4bc51ce64500682f146709cc8a00d05aa8c6c009cc8a00d05e1c273228034178a317ce64500682f1466b9cc8a00bc519d4813991401a0bc3c9ae7322803c5a0a335ce64500682f0d6369cc8a00d064a8cd6009cc8a00d0649ae732c91401a0bc51ce64500682f146619cc8a00d05e28c113991401a0bc519a6732284c01a0bc51ce64500682f146609cc8a00d05e28c413991401a0bc519a273228034184bc51ce64500682f146589cc8a00d05e28c673991401a0bc5199a73228034178a31b4e64500682f0ea36 else 0x9ccc24500682f10b3998401a0bc51a16732f91401a0bc51ce64500682f146489cc8a00d05e28c153991401a0bc51a1273228034178a323ce600d066af146479cc8a1d00682f1473991401a0bc5190673228034190bc51ce64500682f146379cc8a00d05e28c173991401a0bc4d82e733891401a0bc51ce64500682f1461f9cc8a00d05e28c272288401a0bc5184c01228034178a309ce6450b8034178a39cc421700682f146009cc2e00d05e28e73228840178a3224e64500682f14644004e645005e28c89399145600d05e1fe73228034178a33f802732280341787f9cc8a00bc5191c8139914019abc51902732891401a0bc51ce64500682f150a39cc8a00d05e28c0d3991401a0bc518fe73228cc0178a3204e64500682f15ca39cc8a00d05e28cdb3991401a0bc3188e7322682f1466311ce64b228034178a39cc8a0d00682f1473991401a0bc5180e73228034178a310ce645108034178a39cc8a20d05e28c473991401a0bc53a8e73228034178a33e4e64500682f146799cc8a00ca5e28c8f3991401a0bc429e6732288401a0bc3cce64510682f146799ccb64500682f1473991401a0bc5195a73228034178a304ce64500682f146789cc8a00d05e28c81399134194bc5190273228034188bc51ce64500752f14679004e64500752f1473991401a0bc518ea73228034194bc1d002732280341783a) else (if page < 3 then 0x9cc89f8f7682f147399bc89eed05e28e7337803dda0bc51ce66d228034178a3a2c8a00f7682f14600a2c8a00d05e28e73228034178a314ce600fc682f14629004e600d05e28c533991401a0bc5183e7322803d9a0bc51ce64500682f146289cc01eed05e28c513991401a0bc5184273227e34178a3084e6450d8034178a39cc8a00d05e28c49499cc8a00d05e28e73228034178a30b4e6451d8034178a39cc8a00d05e28c553991401f6d05e28e73228034178a325ce64500682f146929cc8a00bc519408f3994c8a00d05e28e81228034178a32380281228034178a39cc8a00d05e28d112280375a0bc5191c01398034178a3444e64500682f146079cc8a00d05e28c8d399141e00d05e28e73228034178a33dce66522802f146479cc8a00d05e2c5473991401a0bc519b291228034178a305c8a00d05e28c380b91401a0bc518401722803f1a0bc5182e732280341786505c8a00d05e28cca0b9ccc24500682f1474491401a0bc5182e732391401a0bc51ce6451c8034178a39cc8a00d05e28c03399140a00d05e28e7322803e9a0bc51ce64500682f148a39cc8a00d95e28c16009cc8a00d95e28e73228034178a3474e64500682e9460b004e64500682f11d3991401a0bc51a1691398034178a342ce600d05e28d0a1591401a0bc51a6c2139803dda0bc51a1673228033d78a323ce64500682f13685 else (if page < 4 then 0x9cc8a00fd682f146009cc89fad05e28e91399140178a328ce64500682f14651004e645005e28ca3489cc8a00d05e27a73228034178a34f002732280341789e91401a0bc518702b489cc8a00d05e28e91228034178a30ace6451a8034178a39cc8a0900682f1473991401f0d05e28e73228034178a651ce64500682f14686a448a3500682f14600a446a00d05e28e73228034178a30ace63500682f146159ccd64500682f1473991401a0bc5186a732e91401a0bc51ce64500682f14619a54e64500682f1473991401a0bc5185e6f228034178a30b8024500682f146179cc8a3d00682f147469cc7a00d05e28c01398f401a0bc51d228d228034178a39ccde00d05e28c2b399bc8a00bc5193a73228034178a3270027322802f1464e9ccde4500682f12f3991401a0bc51a5c013991401a0bc4bd227300682f146289cc01a0bc518a02b399134178a3158a2732691401a0bc51ce645007cb4178a39cc8a00d05e28c093991401a0bc5189e73379134178a3144e64500682f154a39cc8a00d05e28cf5228034178a30a842451a8034178a3084e644d05e28c561091401a0bc518ac21399bc8a00d05e28e8d228034178a3084e649228034178a39cc8a3700682f1473991401a0bc5180a7322803dda0bc51ce64500682f14aa39cc8a00d05e28d1322803f1a0bc51856731a803dda0bc51ce644fc682f14628 else 0xa44e644d05e28c593991401a0bc518b001399134178a31652273227eb4178a3))) else 0
  | 7 => if page < 1 then 0x52273228034178a3004e64500682f14615004e6451a8034178a3004e66f228034178a3004e64500682f14628004e64500682f14610004e645007bb4178a3004e661228034178a3004e64500682f14647004e64500682f1460b004e64500682f14685004e645108034178a3004e64500682f14640004e64500682f14623004e64500682f14679004e645006832578a3004e64500682f14636004e64500682f1466b else 0
  | 8 => if page < 1 then 0x273228034178a3 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 3
  | 4 => 38
  | 5 => 276
  | 6 => 260
  | 7 => 18
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
  | 3 => 7
  | 4 => 86
  | 5 => 553
  | 6 => 521
  | 7 => 60
  | 8 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xf3b62e5bb7bc3b04ab53834a92cfd0428209291a5d6751c25c02dfd0 else 0
  | 4 => if page < 2 then (if page < 1 then 0xb9b4e0adb8b1eb24b6a1cdd6b308d0d4ae711252ada50dffa94024b6a289bd3ca109101f9fa49e2d9dbd4b889701cde596e7c5c3962f2b6995759cc79456ee4492c6f91192a54dae8d0dd4b889b1316d88a338ac808395097b583d4475ed8a7574a9cfc46f50b0306ca20c7a65bf59eb635dd9e062061a785dadc7f95c0771205994cad4578dbc9256372dfe529d9fcd50228d654fb209ec4f215e394bddf8c547ce0bae44fb59224482ae303fb24a0f38d2ee3633e3fd7c30b712912f279e692cf8cf232664ce8c24cd6dd6200626cc1f95a3531df4b89814c2f8ff145c0f3f0e4807480d2797510d1bb81d0bd52eda0a9aa51605eafaf4035df2020215724e else 0xff1da36ffe16711afcdc688afb44a1f6f57c9baff3c69f87f1745b22f0ae828feff941a8eef541a7eec5b76ceb78fbc3e478805be152f938d590a16ad57703c1d4afdd46d3ae935ec897076ac666292ac5603516c51e0132) else 0
  | 5 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1b927ac11b5df5851b5371a61b0ba3481b0adf5e1ad1b1f11ac345aa1a6d00ab1a5b3a6619f3255c19ea9c4119160efe18e3d70b186fc0571852892b18519ba31800b61b17f7fc3217b080c117631120175051bb173e715116f9d25816f08b0c14cea86f14133b5e13e9ea021386476a13816dd412c99f1212772a47124fdc7f11d678a810a374b010a11e6110421c430f6658750f31327a0f28a0f80f1724a30ea6a5860e86da0c0d99d1960d4c50480cfb90b50cb7b4bf0c9fcbb70b3610550a3803b609f715eb09676d770901f37308bfbf8f07721634072862f9065e34df061cf05005ed6418058f0af104a68ae0043ecd250264f156019e08300131f55a else 0x3edc6c193e9cd7693dfb038c3dbca2d53da7df953c1ee7f63c1322b33bd83e6f3b10cbea3a9df40439ac01f7399e5c50395eb1b838a7ea0c3847224036edcb1636d9fb413685d13e366043ca34b437bb34a168d1347e4932345b33be342ec8f4340f045c33fcb6b333aff094337f3fb23336ae2e32e671873192a0dc303d705b302f8e552d796fb52ce5e9b72ce333f62ba950312b90b8202b7819682b0db57029339810289158c82851bb4f2844855e281a3eb8267f5479262af4312614a06b2613f93f24f50e6d2424fc65236939c62319e7b622d52063213fa239213056821f7010c21f3ae8b91e6cdecb1e28aba71e0dd9591dd8a77e1d9d55e01c80e8c8) else (if page < 3 then 0x5c1b8d6f5c0569b45bfd8aae5b84249b5aecc6e25a693b445a5f3736588d2b8b5849dc8b583f223657fdcd9c579c7d61576debb3561124f255a828a954971d96549165625434a91552d7b68d5211d9de5105727b5053868d5037b60c4f76ed374f6486604ecf82784ece03a54e3c63734e2b0c3f4dbdbcc14d8693624be076144bb9503f4b6be5f84ae2361b4aad3ebb49eda60449976e5b48c4a81b48686605481c018e48113617479b2c5f476ee45f475a3bfe46f59f7e45cba2ee457996ca455fd55044d1c63444bd51c244bc7448445eb699443972e143d023b343aa5c6f423203bc41eb692f413fe1c3413b5a3d40e87750407e26e7406222273ee66053 else 0x7b8fc8447b6ecf1d7b5396007aeef1ca7a38c0487a21e34479de13fd79ddadd379bb82ea787fa7237839409a7819739377a8175f779036a97775956d772989717598cf0574c83e607477fe8a74709dea745c74487458d0ee74481d577446a90773c5b2e97220c3287187ce0d71636533710a95f86f6b36e06e0832c06d6ebcec6d3ea7f56c9e614f6b06ceb16a5bd4a769a2b3f7691ed52e68ee3e5068c462c4686f2c33678a960d673ccc0567206dbb669bde1d6572d8a4652b936163a7e529635a0620633761b062999b7062988191608ab9b560536c8560329ca6601ce53c5fe49c4d5fc712f05e93f0865e6315925e5e4f3d5e3722135d7a876c5d6f32b9)) else (if page < 6 then (if page < 5 then 0x96c2495d96986f29965628809631b618962f2b699621f383961cc0b7961c265995f0360395ca66ca94e3d13494c1764e949c167c93aaf4db93a7fe39935a9b4791dfa5fd91a2a00390d40d7c904b78eb8fbf7fea8f2160ae8f1b4d888ee706f98e3911058e35f1798df88c9c8d66b4ca8cbe02d88c2c934e8b8121408b6fca0b8aed0e218aa149928a7508698a2a1d818a21936189d21816893cee778927e31487f82c7687c44f7f86814b5e860988e485c79f4c84e9ec4984e32b6784d735eb849125ee83e2713a839cac2781f5384980fbb1e3806b88208023bac07fa04da77f9ac9e27f4694937f1093c37ebb04aa7ea83ccd7e2c1d497d67ffb87ba39d65 else 0xb44e9a01b43b1c17b3407aefb315d098b2e1fa36b2788b7ab0d82f37b08b6c38b07ee23eb0544a2cb0089cb5afed2cd6af3b3aa2af319b42af031060aed0f5f0ae38a72cae01f868ad402320ad3290eead2e35d0ad166b20ac87bc5eaabbbc7ba9dd2787a95b0b8ea953f9fda8cbc0f4a84f2c24a7eccd66a7e77a6ca79152f3a745f00aa6d6807da65c1646a5cf2cd4a5a7d8d5a480df77a337582aa2ca0be9a25a1cffa1ddef24a15e93aba13f0758a11419dba1090402a00b29759e9cdb7f9db37b1e9d3689319b3eddb79ab926439aaf3eb59a287507994712df992a0d2e990a7669990a144f98e0d69b9888c24c9839c0589831377296fb3afb96eff8d0) else (if page < 7 then 0xd36851bad25cc676d24b0325d1e9c4f8d136e83dd0bc4e96d0af9315d09ddb50d000c205ce884487ce2192e3ce06690acd9b9c06cce6f44bcc44f709cbfb4f74ca886f91ca3de53cc9ee2485c999d187c809b770c7890062c7112f17c6b2ce96c5b46181c572de63c558e5ecc4d4b363c4d30a36c40be08ec36b98e6c367e7a3c34a478fc1b0edf7c14de1aec006bf1ebffb641ebeecca9fbe3df95dbd6a881dbcddaf75bc668bdfbc0f567fbba04912bb85b78dbae60685bad350a0ba4ed9e6b9dab11cb98f48d2b95ff03eb931ac4ab891d707b88b7b26b84b8e21b83dff76b81c1bb0b7d92ecbb7832d70b751c00ab5bd4763b5b992d8b55ec21fb451a66a else (if page < 8 then 0xedcfc2d3ed5eb00bed4bf959ed0f55afecde4538eccf8ce2ecccc066ecca7118ec7391d1ec2bbd18eb95031eeb3f756deab4cd18eab00c55ea56b68bea5391ece9a1f343e941d400e8fc5058e84aa80de74b0a05e72a2b8de6e481d1e6630a46e599e7c5e56a7d3ae4e3247ee4daac39e46a28c0e388e133e2cbcd12e208473fe1e50a49e1e315fce115a2cfe0ff45a6e0f9385ce063c831dfefbb7ade1ccb5bddf1586ddd5c59f1dd32d1b9dcc1d2a2dc41e18edc3efffedc16770ddbc1d9e4db0757cad9d0e9c6d8e8967bd8250d97d7f8aca1d791dbd5d7618b6ad75201d7d6470c0bd62b3a41d544b638d4e3b503d4e3381fd4726370d467094dd3b2f948 else 0xff77bd32ff7049fcfe000fcefdf64d28fd8970f2fd569f0afd514ff8fd322e9afd013d25fcc020fcfc40fdf2fb85868afb52755dfb45eaa6fae41b17fa0ea658f97e43fff94b242bf762e05bf74155e4f7122cd7f6de9d7ef6c1473ff6bed5fbf67db8f2f65bfc31f63d9727f6302bbcf56a8c0df551ea7bf4ab786df389ed7cf33938d0f325671bf1fe4787f178c4e2efd9d4dfefb8ba59ef4d6c05ee72fecbee719175)))) else 0
  | 6 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x208a52b0206912ba20525ee01fe0be5b1f4e4f5e1dd0ceee1b616c301a889e0b19ea9c4119a24814199247b41912d01118c09d3b15c559a515c36b8015b8334e1587a6ec150395ba1490680214799dba133aee6c12d65afc11c3514010a497e70f46ef4e0f31327a0ea8d0ee0e0c658a0d7dc7c10d7af6000cdb7ce70cb32e710c39de9b0c2666de0befac440ba184230b88fdbd0b3610550b2d42370aea44f10ae9b8f20994bc4c09149cc00900844a08ce1bcb07f6729407ac34640794046f0757eb960754fefe06aeddf10692ba8706566bf0063974cb0570d53e05550f40050ec898039d27da0370718702e30d4a02467fb2017c4a0201448b600010a60f else 0x3ea94ab03dfbd8fe3c5a2a8d3c1322b33bd83e6f3b59953e3ad1b9a33abf91613a7488593a55918b3984a1ae37e522af37c03c1637a60edd377fe71d376b174036533ac436475e5d35ce130f356bdad834f4ece9348e6a0e3468224b32af480231e8c0aa31df70d231ca9b9631a7be7231853819315793e930e35eb2308a8e5430714b3f2fda503d2f36c17b2eb3cec52e568b752db0e07b2c64811d2bc4ed422b9af5122b8924ef2afed7772aa96e402a4240b82a3e0ba42a0358d728e3410528c4668627f6727d27e236e62719452f25808e1d2539119a24aa608123488b3e234186da22f6715522627c8d225da99022239a42220595b52193dccb21305682) else (if page < 3 then 0x5d9316205d8ade275cbc840d5c8ec2935c6e6cd45c68c7bc5bf4de655b523f1e5b3e74ad5b315c385a700b0e59c57a4f595ad61e587066cc5850a8fe5842343e57382288570268145665308d555b1ed7549a04a3549165625442dcbe51b12deb513b8ff35053868d4f03fb574ee059d84e9bad584e73a0964e5c06dd4e054bc34df6a9bf4dc14a914d6bfefa4d5b67f44cc8e0374bb9503f4b3443e64a5139d64a25ed7c49b0270b49314b6847e08b8247cc9b38478c57b44787c718474ef53c4740366845bb6a4a45a17d91454bc3cd42ff50a942c426d542769923423ce218423203bc41b33865415d35754127eb1840a2fb823f04a19d3ed33b9c3ecfc3aa else 0x7c375e6d7c0e0fa97bb52fb87ac3d0c97ab232d77a37c26d79bb82ea79491c2a792e2602792a19f5782d3bcb77c741b2775924067729897176431513758bdfad75606fad748f000974709dea7469fc0c74259b1173ff0c4073fbff7273df2eb873d38eba71eaf08d71b472457193de867110df1c710bc9026f9c017e6f6971dc6f64d5f26f3848f06db1444b6c31c4696c24a6306c05726f6aee64a46ae7c5de6a9036b26a1edea8699a8cec681fd134680d7aef68000f11669bde1d66413b73660653c665dd896f64d9b88e639b39ba6356a9f1633fba0162e2718562c3378562a29279624da85861c5eed161740a915fe647db5fe49c4d5fbea8665e412549)) else (if page < 6 then (if page < 5 then 0x9d3b11b69ccd963c9b6d19aa9b3ce19f9b38fef39a244e9d998939e5996b43f89960cc7098e0d69b98d5e22d985d9bec9828cd989722ea969671a476956792c094ea41a1942f3bd2930644bd92ba1f2f9180d41a8fd0fae08f2160ae8e1c02638df88c9c8cd79a5b8cbe02d88c8f5be08c2c934e8beac3728b9518ab8b80926e8aa149928a01d4fb89dafefc89a751748875a084885e32a587f6a2c387f30449877c145e875bea978702b24286fdf0788694d2a6868c831d865916ea861e2067860988e48603526d8525b5b78523b59c84a6a22b83fb5704827bef02812120c67f2fae8d7efc12107ed280aa7e76e5d57e5d48fc7dd3f1f77d67ffb87d401aad else 0xb79a727ab730f5b7b710ae1db6ae435db6426ce2b5e4fdbeb5b5fdd3b55ec21fb5597297b506f403b49c1838b411e503b3e17f99b31dbd15b2a6f067b2a542fcb2553af3b22ae0aab1ba3cecb1a9f11db19a479ab0e06652b0be7dd0b0b5ba85aea9b721aea6ca7faea3e4feae8059faae5ddc57ad3e398caca04568abcc0ad6ab7001b6ab1e1dadaa740283aa41da5faa34876ea95b0b8ea8d63e31a8419fa1a7ab3c2fa76df0e6a749237aa63a8ba9a5c21fe8a58ceebca4b0b5eda4156119a3b78626a3443dd6a29dc6c2a2933cbda27eb934a1ddef24a11419dba0f8ac6ea0d967b1a084d7c59fb5e72d9f876e9b9e15b8139de89d109d78d2e19d48e894) else (if page < 7 then 0xda1b4596d9d9dd0dd9d0e9c6d9537342d90a47d2d9025483d791dbd5d746a49cd6fc59a4d6438838d49dbfb6d30dd7ccd26e5703d180c5ecd0de0d6ed0658902cfa575b9ce34151acd2eaca5cb7cb34acb596b7fcb1d6c10ca70092cca106d59c9b7e6bfc9826d74c9135292c8e2f9ffc8a7010dc81337eac77992d9c73b156dc71161bdc6b9b1b0c63f7ac5c558e5ecc49f3bafc49e2b2bc4372aaec25f5032c2112b25c1b0edf7c1057cfec074d295bf5090febf047141beecca9fbe579551bbc05dd4bb875fd5bb4eb684baf11f01bad350a0bacb47ceba8e9bbeba6e0aa3ba301498ba17090cb99ea329b931ac4ab9065fccb8ca21aab88c9b73b886fbb6 else (if page < 8 then 0xfd7c6f79fd31026afcfc7a86fc4dcfaefaf37e67f9ed6e8ef9b5b277f88b6c2cf85f84d0f844439ef817ee25f802285bf7ff3a0bf7c2a441f6b4115bf6afd0a0f3e938dbf3a675fcf33938d0f28c8f9af2184135f1def0bff1d90c5bf102e4bbf0b8297df03072abf0297abbeff191bcefbc004def2724e8ef02cc23eee52abdee2c5ecfecf5b85aebd83e67ebc32eecebab7d36eba24cd4ea2a5c51e941d400e9046b9fe80ff8c6e62d230ce5763434e51c317fe4daac39e2985052e24cd5abe208473fe0ff45a6dfb5a4c3df1c3dabdec203a2de930189de7ed653de5d1c72de50fd12de136937ddf29c28dd1012f6dbc1d9e4db8709d8dab8d4d0da7e69ce else 0xfffa4492ffb114dcff2f8b9cfee35215fed30586fec2dccbfe9632fdfe72e1bdfe414e9b)))) else 0
  | 7 => if page < 1 then 0xfffa4492fe72e1bdfca901f4f9ed6e8eedf999cbdec203a2ddf29c28dd5a3459dc85062ed9bd0a73d9a32ddcd5be91f6d575a3ced26e5703c9135292c490b053c1cad45ac0a1015cc08b0830bfedd0a9be32bc74bbc05dd4bacb47ceb88c9b73b710ae1db12b935aa5c21fe8a2933cbda0f8ac6e98d5e22d8eb8b44e89dafefc877c145e8619e7d080e3dbec7c77496b7c2645777aaea44975313bfe7289246671eaf08d699a8cec6955227066413b73624fd1fd618c4fd05e9d27d65d93162058e2630d491d5d2c3f7611d13c9f6e6332af48022539119a2523acaa16a79d960c39de9b0c2666de0990f9b50010a60f else 0
  | 8 => if page < 1 then 0x1852892b else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x26001000200024001a0018 else 0
  | 4 => if page < 2 then (if page < 1 then 0x248000000b200d20226018001100041020a020800590082001001c0011a0178012201f00230019501e0011100f701700160011801200020018101400190003601f500b002200250015b019100e00070021000800185015001040050021400ba015900e101b0016b01f100c800a8021601d1010200d60242023401d000300088 else 0xa6018701690236019701a000ea00680018020000f200c00240004602240127013001360090004001f70134) else 0
  | 5 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x7c805d00d800dd00881034a00860a700f9000160402003008280f94000009f00f3409840ec107f409f60d51086209b00b940a880e4905c00cc00fc20aab0b0b003a09900a950f4106d00a200f580a4804f111320f701104076106e004b306960b7001b00b770ee709f400b600560b2a0ca1096902800bd410a00de0040809a1 else 0x2120f2600400f4302a2077707200bf80de205e001a00a910e3110600b8500900dd40258031908f705e201e40d100a810d90032808800df00c750ef00e500b970aa0007002c804d006790e9007c106c20c0405d80e4b0066103002200e61079400540c1005fa00600af90e2004140812022405b009720b500aba10500e100602) else (if page < 3 then 0x450025601b20f1705610e52107009e1061904a10fd60e140e8105400d340f52081007c001c00c71091609e0095310320a900478046210240d300c830d7007e00e00088207390dc106c4003408d30de80e01002208640b300362070201010fe005b208500ba10a970f10068210b009220c600900063b0a3901000ad901d41026 else 0x6f801f40b1007f00c81055102000cf2040003021090050105160c91031a0d000fc00fa207b403900b810fd4030110d20a670b0901230da005500ac010f002740b9508080802084403cb07580fa009310f800ba506400d500bf0027a0ce60adb07a20ee100a0053600d608540b4808e80340004403480c400580067b10e00f30)) else (if page < 6 then (if page < 5 then 0x9e804420ab1060110400be80290094004b005a00ed40ef204f00cf00a100ec00e9209d603f20fba1100072101760fb80ae9024a0bf20ed00a2403920e870fd0059900200d6000e01114065902b807160f5002c01080034203b20c060d1110e21000012010d004a804a0082102fa0ac90e3004c001590cb10a6608a00a260914 else 0x2a401370d7103d008c008560ff8083005200d610951089200320bd00c5006100e8506e7024004c70a0b10c00f710f020cb006940b91085101f0019601100f610c610bc10f6004800a50014009860acb0780069002e2049800c40ca001d60bc00fe60ee50a3804101128033204320a740bb30a090ea00cf807d7089000720186) else (if page < 7 then 0x31807420e980f4904300f96102002d2064204400a9406b8062000c00e700b28066006800d4101770a76016001b80be20ff011200c5108600fe4037a06140e16039801290577099208e2071109200e600ce011380b900bb907400ff20d21037b10a10b600490007a043103580ad000f007b00dd60d360b960cd10f1109d70e11 else (if page < 8 then 0x17004aa02d000c2042011220c300c770a800b8010f4089110c104c204280ce40d2000380b3208700fa81130050008d90f0404e00482012b069103a902600042029804700288007803810048073b0f000c2004410cd00f24111010f602f8081810e4101006c002da0b68071000140db00ee009c60f20026209d00300021a03e9 else 0xa4901d005f8110601e6103802e008400a9600500c12063908b00b870ab8046a0c890234056003800f400a1206d10ed604600600086506a80da106180458040100c6011102b007b20eb00f150aa90d4000f1)))) else 0
  | 6 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x1020055602a20fa60e96020a03b005b808a2100003c705f1074b05f00ae40cb0011a09e007800c6002100974085403080fc20f8008340f9403a0068206b102ca0866047800f40c90051a0d960754082002ba0a920fd003100aa00328013407a0045406070ae607a605f2061109400c3709f008e000b20f100cd002b604840142 else 0x9d702700c7006d00fb8103008f4036000f007100070012205f9083006060224059604e1078803b10e7002600fc00c500f1602f002c603a1071402500d510b000fd20f700fa403240f51045600560a2004800b1109870da40880038007090cf7096502920d00022006b0093100300a700002049606540dd00490032203400dc2) else (if page < 3 then 0x79809f800b10bb005800239027a0d8100d001000251063002210994056102a002b0081907f009c80f050dc008550da00e000a4007210b3007b60be009c0011005180530088205500db40e400f9605e8084008f002820ef00947044008c605780e86063106c00db008990836052406800ba000720ab00666085601e009800b10 else 0x7b4030a07b00f300e80071608a0095003900ae004b1075601140fe00af708d90c100494067003120a080a6103c609970eb00ed00f140560083105260c3502320e600c0104420c00046805d0032903d2018809200c510b040bd009850fb0054000c60bc109610e8401b40b6000a201c207c9042802c001c80290043006f00e21)) else (if page < 6 then (if page < 5 then 0x5f803c00cc103d008c402da02f401fa012010100b2104b007e00c4604e004f808000ac1085001700a00057906d10d700fb202e00f84015006720a840dd801a000e006e00012082401f008570551038603f004f00ec1042a03d1032007020132043200b00f0704a90565055408b202800de8000800a008f60e940a020f860851 else 0xd31072000180b50031401040a860a1709760cb10ec000860cf50a09089b03230af108100cc00fa00062099501e4026801f203020db6096003150581023b0d300d410ce0011605d80a900d94031105c405e104810df00c210936013804860981024a0ea006280b400dd20d9006440546041a00c703c40c2004d009100c4402f2) else (if page < 7 then 0x6920c310ee004910a370da606a006200d800384062101f80ca107d109b405e002220c91061005a00e9001300d0400a107700c800f400844041803920700090807690a5004c00b7109a30de209f206900f21087906560c4003e00f9006a10d100ca00d2009b007080e110f6000d102d002b1097001c0040a02e4024b07310826 else (if page < 8 then 0xef106f105c00bf009960ed1000004a804f90d0602a107a40de0084605670c11023005900646023109210350071101e20f5005a60e0104600f010e50066402d80749099105e209670fc80af505b201680b91095701560f710060087b06c108b0019204080b810d60050601240e3100900fd8002001d206e10dc80cd10b060370 else 0x5000990004609a90ff00cf10ad008610336)))) else 0
  | 7 => if page < 1 then 0x30007100a70101001400360022007400d1009300840064007500e100f000a400100044009900a0005200e0011000810018005000a600d0006600c10090001200400028008000850086009100c00020010000b100a50060001a000000700098001600920087000800b000a1004600340076005800770002 else 0
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
  (slot / 16,slot % 16)

def s45 : Switch := ⟨16,0xffff0000,0xffff00000000⟩
theorem s45_ok : s45.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s45]
  | 2 => [s12]
  | 3 => [s12, s45]
  | 4 => [s01]
  | 5 => [s01, s45]
  | 6 => [s01, s02]
  | 7 => [s01, s02, s45]
  | 8 => [s02, s01]
  | 9 => [s02, s01, s45]
  | 10 => [s02]
  | 11 => [s02, s45]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s45_ok, s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 3 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x16 : span (checked 4) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x32 : span (checked 4) 6 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 38 0 = true :=
  (@span_join (checked 4) 16 0 22 chunk4x0 (@span_join (checked 4) 16 16 6 chunk4x16 chunk4x32))

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
theorem chunk5x272 : span (checked 5) 4 272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 276 0 = true :=
  (@span_join (checked 5) 144 0 132 (@span_join (checked 5) 64 0 80 (@span_join (checked 5) 32 0 32 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 16 chunk5x32 chunk5x48)) (@span_join (checked 5) 32 64 48 (@span_join (checked 5) 16 64 16 chunk5x64 chunk5x80) (@span_join (checked 5) 16 96 32 chunk5x96 (@span_join (checked 5) 16 112 16 chunk5x112 chunk5x128)))) (@span_join (checked 5) 64 144 68 (@span_join (checked 5) 32 144 32 (@span_join (checked 5) 16 144 16 chunk5x144 chunk5x160) (@span_join (checked 5) 16 176 16 chunk5x176 chunk5x192)) (@span_join (checked 5) 32 208 36 (@span_join (checked 5) 16 208 16 chunk5x208 chunk5x224) (@span_join (checked 5) 16 240 20 chunk5x240 (@span_join (checked 5) 16 256 4 chunk5x256 chunk5x272)))))

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
theorem chunk6x256 : span (checked 6) 4 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 260 0 = true :=
  (@span_join (checked 6) 128 0 132 (@span_join (checked 6) 64 0 64 (@span_join (checked 6) 32 0 32 (@span_join (checked 6) 16 0 16 chunk6x0 chunk6x16) (@span_join (checked 6) 16 32 16 chunk6x32 chunk6x48)) (@span_join (checked 6) 32 64 32 (@span_join (checked 6) 16 64 16 chunk6x64 chunk6x80) (@span_join (checked 6) 16 96 16 chunk6x96 chunk6x112))) (@span_join (checked 6) 64 128 68 (@span_join (checked 6) 32 128 32 (@span_join (checked 6) 16 128 16 chunk6x128 chunk6x144) (@span_join (checked 6) 16 160 16 chunk6x160 chunk6x176)) (@span_join (checked 6) 32 192 36 (@span_join (checked 6) 16 192 16 chunk6x192 chunk6x208) (@span_join (checked 6) 16 224 20 chunk6x224 (@span_join (checked 6) 16 240 4 chunk6x240 chunk6x256)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x16 : span (checked 7) 2 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 18 0 = true :=
  (@span_join (checked 7) 16 0 2 chunk7x0 chunk7x16)

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
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full



namespace SignedFrontier.CliqueLink
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
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 9 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 9 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12268_aux

open PEqualNP.Outside.L_meta_12268_aux

theorem PEqualNP.Outside.L_meta_12268 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
