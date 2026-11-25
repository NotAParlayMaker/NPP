import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12316_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [1,2]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.and, [0,7]⟩,
  ⟨.or, [6,8]⟩,
  ⟨.or, [0,7]⟩,
  ⟨.and, [3,10]⟩,
  ⟨.and, [5,9]⟩,
  ⟨.or, [11,12]⟩,
  ⟨.and, [4,13]⟩,
  ⟨.and, [5,11]⟩,
  ⟨.or, [14,15]⟩], 16⟩
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

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 39) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 39) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 2496 := by omega
  have val : fullLanes = 2^2496-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 39) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 39) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 39) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 39) (xs : List Columns)
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
    (length : rows.length = 39) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 39) (bounds : ∀ r ∈ rows, r < 64)
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

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeac0fffeeac0fffe
def negative : List Nat := [0, 16, 17, 18, 19, 20, 21, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 3 then (if page < 1 then 0xaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa02aa02aa02aa02aa00ffaaaa00ffaaaa00ff00aa00ff00aa00aaaaaa00aaaaaa00aa0aaa00aa0aaa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a888cc88cc88cc88cc88aa88aa88aa88aa8888aaaa8888aaaa88888888888888888888000088880000808080808080808055ff000055ff00005555000055550000550055005500550044444444444444443fff00003fff00003f3f0c0c3f3f0c0c3f3f00003f3f00003f003f003f003f003c3c3c3c3c3c3c3c333300003333000033003300330033002aaa2aaa2aaa2aaa2a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a2a2a0a0a2a2a0a0a2a0a2a0a2a0a2a0a0fff00000fff00000ff00ff00ff00ff00f000f000f000f000aaa0aaa0aaa0aaa00ffff0000ffff0000ff00cc00ff00cc00ff00aa00ff00aa00ff000000ff000000fc00fc00fc00fc00ee00ee00ee00ee00cccccc00cccccc00cc00cc00cc00cc00cc000000cc000000c000c000c000c000aaffaa00aaffaa00aaaaaa00aaaaaa00aa00aa00aa00aa00aa000000aa0000008800880088008800550000005500000044004400440044000f0000000f0000000a000a000a000a0000fcfc0000fcfc0000eeee0000eeee0000aaaa0000aaaa0000aa000000aa000000888800008888000000cc000000cc000000aa000000aa0000000000000000 else (if page < 2 then 0xfcfcfcfcfcfcfcfcfcfcccccfcfcccccfcfc0000fcfc0000fafafafafafafafafaf0fff0faf0fff0faf0fafafaf0fafafaf0faf0faf0faf0f3f2f3f2f3f2f3f2f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f0f0fffaf0f0fffaf0f0fff0f0f0fff0f0f0fafaf0f0fafaf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeee0000eeee0000eeceeeceeeceeeceeeccffcceeccffcceecceecceecceeccececececececececeaeaeaeaeaeaeaeaccfcccfcccfcccfcccccfcfcccccfcfccccceeeecccceeeecccccccccccccccccccc4444cccc4444cccc00cccccc00cccccc0000cccc0000cc00cc00cc00cc00c4c4c4c4c4c4c4c4c0f0c0f0c0f0c0f0c0c0fcfcc0c0fcfcc0c0f0f0c0c0f0f0c0c0ccccc0c0ccccc0c0c0c0c0c0c0c0bfbf0000bfbf0000afafaaaaafafaaaaafaf0000afaf0000afaaafaaafaaafaaaeaeaeaeaeaeaeaeaaffaaaaaaffaaaaaaff0000aaff0000aaeeaaeeaaeeaaeeaaaaffaaaaaaffaaaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaa8a8aaaaa8a8aaaaa88aaaaaa88aaaaaa8888aaaa8888aaaa2a2aaaaa2a2aaaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0202aaaa0202aaaa00aaaaaa00aaaaaa000aaaaa000aaaaa0000aaaa0000aa8aaa8aaa8aaa8aaa88aaaaaa88aaaaaa88aa88aa88aa88aa2aaa2aaa2aaa2aaa22aa22aa22aa22 else 0xffffffaaffffffaaffffff00ffffff00fffffcfcfffffcfcfffff0f0fffff0f0ffffeeeeffffeeeeffffc0c0ffffc0c0ffffaaaaffffaaaaffffaa00ffffaa00ffff8888ffff8888ffff8080ffff8080ffff00ccffff00ccffff00c0ffff00c0ffff00aaffff00aaffff0000ffff0000fff0fff0fff0fff0ffeeffeeffeeffeeffccffccffccffccffc4ffc4ffc4ffc4ffc0fffcffc0fffcffc0fff0ffc0fff0ffc0ffccffc0ffccffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffaaffaaffaaffaaff80ff80ff80ff80ff55ff44ff55ff44ff55ff00ff55ff00ff54ff54ff54ff54ff50ff50ff50ff50ff44ffccff44ffccff44ff44ff44ff44ff44ff00ff44ff00ff40ff40ff40ff40ff05ff00ff05ff00ff04ff04ff04ff04ff00fffcff00fffcff00fff0ff00fff0ff00ffeeff00ffeeff00ffccff00ffccff00ffc0ff00ffc0ff00ffaaff00ffaaff00ff88ff00ff88ff00ff44ff00ff44ff00ff0cff00ff0cff00ff0aff00ff0aff00ff00ff00ff00ff005500ff005500ff000f00ff000f00ff000000ff000000fefefefefefefefe)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x27ca032c501 else 0
  | 3 => if page < 1 then 0x28e85aa138fed50a3a1280ce3f9405fca085000f6db10077399003a1cc801e0de400ea6f200ae294805794240200a1200fe5090069284803414240278a06012a503008d281802f942400a05920000776 else 0
  | 4 => if page < 3 then (if page < 1 then 0x5c1ceb80f9740b65c0aefe50901417013b701397013770133701317012f7012d70129701277012570123701217011f7011d70119701177011570113701117010f7010d7010b70154f0150f014cf00b6f00a1e009de009be0097e0095e0093e0091e008fe008de0089e0087e0083e007fe007de007be0079e0073e0071e0054f0053d0050f004db0047e0045e0043e0041e003fe003b7003570034f002170001f else (if page < 2 then 0x7f5c284bfae10e268b45cd605a1c600796cc8039b3e40285e660112e7300ac9c38055c49c01a1278011a936008249b003a23e801911f800ec8ba007345d0044a2d801b8fb800f87da00a33eb003d1ce802c0e6c0142736009a39b00449cd802ace5c01626f600a237b004d1bd80160dec00a66f60077379803a1bcc0268dac00fe51900ae285803f942c01f0a160138507005d286803f936401709b200f843a009c21b005610b80184878005042e002721b002f106801807f400a62f60053177003b8bcc01d05e600b82d9006a13e003009e401784f2005026d00530eb003b874c01d03a600741d6 else 0xa37c3794d3c9bcac2acdcd55346e6)) else 0
  | 5 => if page < 3 then (if page < 1 then 0x58fabfd5beabf54fa9fd4be9ff4cfa4fd1fe8bf42f9f7ce7e6ff36f9afcd3e67f32f98fcc3e5ff28f90fc7be37f19f8c7c5fe2df15f8a7c4fe25f11f87fc3be1bf0cf85fc2be13f08f83fc1be0bf04f81fc0be03f9cbcbde4ef17789bd53d27c8fe3ef1cf8a1e43e else (if page < 2 then 0xab457bc9beec0def426f79a37bd51bbdc4c7ab850f5c21f2b0bfac05ef422f79a17bd58bbe045de722fe2d177aa09f9c44fb422776313eb109f5704fa8027e2b13e9289f4904ef601d7a10ebcd075d143bc6e1de2d0ef16075c703aee60bb8905bd582be0c16eca0bd4505f1b82f8b417c5a0af2c05f4d1bd802bfe015bf00abf80557c02a7e014ff00a5f80407c01ffe00fdf007df8038fc01c3e00dff006bf80357c016be00b3f else 0x147437b0ab7d5a2fa6917ce28be)) else 0
  | 6 => if page < 1 then 0x2afefff71fa2fcdfe63f17f89fc3be0bf else 0
  | 7 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2b else 0
  | 3 => if page < 1 then 0x3b else 0
  | 4 => if page < 1 then 0x3b0ec29 else 0
  | 5 => if page < 1 then 0x2b0ac1b else 0
  | 6 => if page < 1 then 0x1b else 0
  | 7 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 22
  | 4 => 132
  | 5 => 133
  | 6 => 10
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
  | 2 => 2
  | 3 => 16
  | 4 => 84
  | 5 => 82
  | 6 => 14
  | 7 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 5
  | 3 => 58
  | 4 => 304
  | 5 => 297
  | 6 => 48
  | 7 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 5
  | 4 => 7
  | 5 => 7
  | 6 => 5
  | 7 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 8
  | 4 => 11
  | 5 => 11
  | 6 => 7
  | 7 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x144292082a1180008060 else 0
  | 4 => if page < 2 then (if page < 1 then 0x9ee402e485000402008802e7819d040400202202000a14000000d70b00003930018017260000c06001010000009140c284000c40b001c001 else 0x2a20c0a0a949000c55580023000000cc5ab) else 0
  | 5 => if page < 2 then (if page < 1 then 0x105812e08a8b0004f000414007020c0b712180022c68384001428c2a04d8708080020c3c10204500000410000080c0800a103010208000 else 0xde94d203000c545081c007800630400) else 0
  | 6 => if page < 1 then 0x22180791003e31c0b else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x820e6 else 0
  | 3 => if page < 1 then 0x643922aa7d2c00961d08100ea24086323458297042621a0077506c1c00005c489e765200279a4e2f005a8e92ab3a020078004a316a9000000088 else 0
  | 4 => if page < 5 then (if page < 2 then (if page < 1 then 0x2d1cb2785126ed880994008fc0020f0003195937a000bd800227760a81c7243426001740003b0880000000000001a228790c88fc0252745697980000038967a3460c200212ba058000321ba2cc000001fb7740014984e else 0x180e3c4883a1c6de1d23c12b07c05fbf21a46194341945ad0148211780b210f1066e0d603d235634eb1c128b000ae5cb9523b42f4502fb3e4d85a0bca6b2b49901763a64e1652d95803504a2400003e4841405a200000016) else (if page < 3 then 0x3f45cc882d02967820830038c5085498e7b02b1fc03841d02184000394321271502a6b8150ace396bf48d1a662470c768d57a0de410bf0112d80951432c0e71334112d6885d68d101c94c910004168615c2755b05286fb28 else (if page < 4 then 0x6900003f00058410c0000033c4d84b0dd4d8c65a8aaa000b180000000095400280524168000000f6fe8001ae1eab693a1e8834d40c4092380000002986d0b880024b4bc709f9a8844c93c1db8403c0016492b796c606723e else 0x2fcce1f43e63408181a9ee000f80f18000a48b18580000046121000000000ab000470a894d000361000310f47760006b800000bdc001960f01c43709566078800000))) else 0
  | 5 => if page < 5 then (if page < 2 then (if page < 1 then 0x1a58000d6ec1493301c0a2805319000000001b43e4d6c96b1b0004e80006875ca21f8252583041c80000dc0004d0d6560e69801253b066d6000000088000000376368000ce000e6db003854ca00a011075000071306 else 0x6787b15d710572052f04f0594002130005c14089d1502c9c00804563202b09f7a0fe10e0000000013f3267bc9a154258746f099411b7e2418bb0000003e9cc02c0002847080081064416b123f616cd7238000000002e9) else (if page < 3 then 0x5701802125084cd20219807742a8003d84688a8330000decd401127494958bc3132dcdc1ac3e07b6d28f9aa0740a6075b4d414f20183537cc980000105c0f84503e75c2ba0b7af61b6000991a60002e54f3a68001c07c270 else (if page < 4 then 0x424e85ed2d0194520d0149032badad0d80d42620c36317409957378196cb44c9e838c81c000c0794400001ca56cf8db41b55fc001ab0a53743de00b3468082c443bb158d3071800000b205804e6d4c80018003ac620aa000 else 0x38e0b4be0000ee7d0910000006100018c310847008999e6396b605c3385201c4a1b1e21c00000078284864003ee23400205800000d99a8090))) else 0
  | 6 => if page < 1 then 0x14625112e699aa363a583105000070f241384c14003ce59020d012ce2058a92008500b480000000f5b00 else 0
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
  (slot / 8,slot % 8)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | 2 => [s01, s23]
  | 3 => [s01, s03, s02]
  | 4 => [s02, s01, s13]
  | 5 => [s02, s13]
  | 6 => [s03]
  | 7 => [s03, s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s01_ok, s23_ok, s03_ok, s02_ok, s13_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 7 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 22 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 22 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 20 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 132 0 = true :=
  (@span_join (checked 4) 112 0 20 chunk4x0 chunk4x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 21 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 133 0 = true :=
  (@span_join (checked 5) 112 0 21 chunk5x0 chunk5x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 10 0 = true :=
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

end SignedFrontier.SmallCert.Minor0

namespace SignedFrontier.SmallCert.Minor1

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfeeaeaaafeeaeaaa
def negative : List Nat := [0, 2, 4, 6, 8, 10, 12, 16, 18, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,12,14),(0xf0f0f0f0f0f0f0f0,10,14),(0xff00ff00ff00ff00,6,14),(0xffff0000ffff0000,6,22)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 3 then (if page < 1 then 0xccc8ccc8ccc8ccc8ccc4ccc4ccc4ccc4ccc0ccccccc0ccccccc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0cc00cc00cc00cc00c8c8c8c8c8c8c8c8c4c4ccccc4c4ccccc4c4c4c4c4c4c4c4c4c0c4c0c4c0c4c0c444c444c444c444c0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c000c000c000c000b0b0b0b0b0b0b0b0aaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaa0000aaaa0000a8a8fcfca8a8fcfca8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a08888cccc8888cccc8888aaaa8888aaaa8888888888888888808080808080808070707070707070705555aaaa5555aaaa5555000055550000550055005500550054545454545454545050f0f05050f0f0505050505050505044cccccc44cccccc4444eeee4444eeee4444cccc4444cccc4444c4c44444c4c4444444cc444444cc44444444444444444440444044404440404040404040404033330000333300000ccccccc0ccccccc0aaaaaaa0aaaaaaa00ffff0000ffff0000fc00fc00fc00fc00cccccc00cccccc00aaaaaa00aaaaaa0000fffc0000fffc0000fefe0000fefe0000fcfc0000fcfc0000fccc0000fccc0000f0f00000f0f00000eeee0000eeee0000dcdc0000dcdc0000cccc0000cccc0000c0c00000c0c00000aaaa0000aaaa000088880000888800005454000054540000444400004444000000cc000000cc000000aa000000aa0000000000000000 else (if page < 2 then 0xffffc000ffffc000ffffaaaaffffaaaaffffa8a8ffffa8a8ffffa0a0ffffa0a0ffff88aaffff88aaffff8888ffff8888ffff8080ffff8080ffff2222ffff2222ffff0aaaffff0aaaffff0a0affff0a0affff00aaffff00aaffff0088ffff0088ffff000cffff000cffff000affff000affff0000ffff0000fffcfffcfffcfffcfffaaaaafffaaaaafff0fff0fff0fff0fff00000fff00000ffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaff88ff88ff88ff88ff0aff0aff0aff0aff00ffaaff00ffaaff00ff00ff00ff00ff000000ff000000fefefefefefefefefeaafeaafeaafeaafe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfc0000fcfc0000fcccfcccfcccfcccfca8fca8fca8fca8fc00ff00fc00ff00fc00fc00fc00fc00fc00cc00fc00cc00fafafafafafafafafaaafaaafaaafaaaf500f500f500f500f4f4f4f4f4f4f4f4f2f2f2f2f2f2f2f2f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f00000f0f00000f0c0f0c0f0c0f0c0f050f050f050f050f040f040f040f040f000f000f000f000eeeeeeeeeeeeeeeeececececececececeaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaadcdcdcdcdcdcdcdcdc00dc00dc00dc00d8d8d8d8d8d8d8d8d0d0d0d0d0d0d0d0ccccfcfcccccfcfccccceeeecccceeeeccccccccccccccccccccccc0ccccccc0cccc4444cccc4444cccc0000cccc0000 else 0xffffff00ffffff00ffffeeeeffffeeeeffffccccffffcccc)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1f964f3f3199ef5943 else 0
  | 3 => if page < 1 then 0xfcd8b49bf9b16867f362d21fe6e5943fcd8ac87f970ccbb02e19976d4e2e19b8665c1bf98d550f8ac9e177162392ee2b8725dc58cccbb8b11997715e332ee2ba665dc570ccbb8ad99977148332ee2cc9643c538b8638ae170bf1482e17 else 0
  | 4 => if page < 2 then (if page < 1 then 0x2019c8f8ce5845f2922f982133b2899d68434b41cb5a0d5b6069d7034e441a7190d689069c7c256a610b65023ae19c4012bc00fef007e7803ebc01ede00f4f00797803bbc01d5e00e8f0073780393c018ee00bd70047d80217400ffa007dd003de801e7400efa0071d0037e801b7400d7a0060f002c78012780091e003dd001de800e74006fa0035d0019e800c740057a0029e001378007bc0039e001af000c78004bc0011e0001f else 0xfcd89a6fcd8b43fcc2669c2b86719c74671fc9a32cfcd8325dc9c3319a3e338fc3e329443e331c2661a9d8b40d2fcd8b4200fc96e00fc5ee00fcd8700fcd670104d4700fcd2700f4d2700fcd0700ecd0700fcce700d87f500d879500fc78d00da78d00c873900c273900b46f900fc6ed00ec6ed00b06f500c867900c267900be67900b8679009267900b867300b443a006643900d839500d639500fc38d0040399009a33c009633c005e33c00fc32d00f832d00f432d00f032d00ea32d00a833900a233900a0339009e339008c339004a339) else 0
  | 5 => if page < 2 then (if page < 1 then 0x3e11b3211d2c10f1610fd80d7ce0d7fc0cf820dd5a0de460de460cf320ddfc06f3207dfcd87c26799a33cfc32d3e33900e1f00c9f00c3f00bff009bf0099f0097f0093f008bf0089f0079f0073f006ff0069f0067f0065f005ff0057f0053f0051f004ff004df0043f0039f0033f002ff0023f0021f001bf0015f0011f000ff000df000bf0007f0005f0003f00fcf00f4f00eaf0079d006fd0039d0033d001af else 0x205f9f00fcf7e617bf26bdb8f3ab473b6133dad19edf8cde7467d4d27f2693f5f89def44ef2d1cea68cf9b867ac233d5a19eab8cf53867a9a33d7e197998cf4c467a5433d2719e8f8cec645fac21af4d0aea68475b022f0010f7e087a9043d0023a4610f) else 0
  | 6 => if page < 1 then 0xc3f9bf67f4ff33f11f0dffcf33d else 0
  | 7 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2e else 0
  | 3 => if page < 1 then 0x3e else 0
  | 4 => if page < 1 then 0xe42b else 0
  | 5 => if page < 1 then 0xac29 else 0
  | 6 => if page < 1 then 0x19 else 0
  | 7 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 3
  | 3 => 24
  | 4 => 124
  | 5 => 102
  | 6 => 9
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
  | 2 => 2
  | 3 => 20
  | 4 => 105
  | 5 => 102
  | 6 => 16
  | 7 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 6
  | 3 => 72
  | 4 => 378
  | 5 => 366
  | 6 => 61
  | 7 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 5
  | 7 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 7
  | 3 => 10
  | 4 => 12
  | 5 => 12
  | 6 => 9
  | 7 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x150970800842425420a420700f006 else 0
  | 4 => if page < 2 then (if page < 1 then 0x4040422082413c00111432c48a82800001c50c00041821462023690003c088600008b0800400000804e40080d21c2007 else 0x6c0299ce000883c01dd08a02d0080502006050863810c21900451c04c30cb) else 0
  | 5 => if page < 2 then (if page < 1 then 0x8304010003478a0468d730004a2000412c0084f870832c3004501f8728100300044210809a00004210144005d14a042 else 0x430d40501127c700225c1460007160c004a48004021100f00004b007) else 0
  | 6 => if page < 1 then 0x8026c0038201d4040101 else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x24158001009 else 0
  | 3 => if page < 2 then (if page < 1 then 0x1c2a0630ac3d9a40002130900824cc3b1a8a9800700a148400b0180088006c8ada1292082205808c780c10000830d2c200c09b0000000093181811205b161000001244040400900608b08100448 else 0x802889a6e000140730d0) else 0
  | 4 => if page < 6 then (if page < 3 then (if page < 1 then 0xe0062760a041e41d307868e84ac5601c4149726a6368c0006e5000a00e20d01de6626ce0000000000a124644e1607000349cc4b00ac1b655e07c39f5b83000c81dc6020da00008262e67e4a149520000c0148d56000883000524df2000000b20 else (if page < 2 then 0xe01ec05f1c201b6a8eb6d160ccd3a80006acde00009800008a9000d60dc0a22770e630000ec9408eb000000d00949372e600007e84d2000f215a0b80000346b43928c28a8cc67b03ec9452a81a20129886f00484000084c4aac0d04869ca3602 else 0x564f0cea0340f46ce28433929268c49a0a02da1c82000660bad941329561a66a326a0000000ae6e42be3040c4790100082f0008c65017303c93486c1a34a409c08822e06003a92a4080000541ae0e88540572960000e80b45921000d80d6c720)) else (if page < 4 then 0xf40140000b810000000a10003136800000000f02ed861000d539f2000384800000640a601d2f600000008027505f00000002c97c20000001d42b24a45c10006e6661829081aa65e2831ea27e6401b630927a0f66c6a1b3d62ec851242ca80948 else (if page < 5 then 0xc8c6e0000c405040001660003f1900ec16e39e02c88097e5521aa08f56c03168425008682102113440001f5888f01ba39c2e21864bb0cad4812e32f00002328e91908a38c0ba01914a0ae81e0580705acc9469444c4e409864e09f4d02f62ee0 else 0x3e6e69ea61090004b2e66000220d525c0ec40000000000005cc000bc3be0000e62169c80000021f204442f1000060b8dcc3272803240666ae21d51c0e89703cd29a9280c00515000de47c08c1904c420a04a1920252bc0))) else 0
  | 5 => if page < 6 then (if page < 3 then (if page < 1 then 0xbc80881a02602b47603f3355bc91a1ba2a42a28000b048b4aa01665c12300009a30c4a210002e2c94bc0000892000154920001000a660001e10000002505800c000062c840c101220000001c4a296847b5000000000000528000000772640380 else (if page < 2 then 0x7640000000009c6b21352960600a200004664868748759012808800207e78aa9e19a0251681a604e98727089e815284b4684e8bc6660b004a9be0aa4168070543732360000900110200a43be6b26af55297c1ba0b866662b58eb4a8a838b2680 else 0x8a17eb6202010005a27209a2c0300010c7e64489828840003a19435630a42620008c49425c40634c00297005a38a4c6c0000000006a01640000000007424260003f69e4922000855b80aa1c28b818a00000007c00003007620000000002e3000)) else (if page < 4 then 0x9c3000a24706824509686c410008c19894294106c0a001301611029235a0a63bac0000890f22b2a8200076c40d0008a71414a69880000e09490008a20008542c0688a40c467616419e01e03545c0c61a62780a801e4b24946000832000403428 else (if page < 5 then 0x9c27e92e0052ca8ca66b2b878c09830004607400540008156441d2449c606e0814aa86d2b405620a17e8120000aa9ac08127e0980b606220005816689863350b23a074c8005e0ca0b203c31551442638f5c841a29407e206d84a860842500c95 else 0x1000007c40550004e65c6c408e9c926f27eab01140160c29000c0dc625e9a09a69b28948000ba10c1a68000c48820000af2a869c0c441311925c8560309488af47a09e6782))) else 0
  | 6 => if page < 1 then 0x2443100883254c4012727343110528020000007499c00000000198683580000e8000000ce03202000c020a80cca800408010310985a020449a4eac3301a94c7466b0a1a00 else 0
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
  (slot / 32,slot % 32)

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
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s23_ok, s24_ok, s12_ok, s13_ok, s14_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 7 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 3 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 24 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 24 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 12 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 124 0 = true :=
  (@span_join (checked 4) 112 0 12 chunk4x0 chunk4x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 102 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 102 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 9 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 9 0 = true :=
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

end SignedFrontier.SmallCert.Minor1

namespace SignedFrontier.SmallCert.Minor2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xe8fefe00e8fefe
def negative : List Nat := [0, 8, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 30, 31]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,19,27),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 4 then (if page < 2 then (if page < 1 then 0xff00ff00ff00ff00f0ff0f00f0ff0f00f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0f00000f0f00000f0a0f0a0f0a0f0a0f00ff000f00ff000f000f000f000f000f0000000f0000000e0e0e0e0e0e0e0e0ccccccc0ccccccc0ccc0ccc0ccc0ccc0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0a2a0a2a0a2a0a2a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a00080808080808080806ee06ee06ee06ee03ff000003ff00000303000003030000030003000300030002ea02ea02ea02ea02aa02aa02aa02aa020202020202020200ffff0000ffff0000ffaaaa00ffaaaa00ff00ee00ff00ee00ff00aa00ff00aa00ff008800ff008800ff000a00ff000a00ff000000ff000000fe00fe00fe00fe00f0f0f000f0f0f000eeeeee00eeeeee00ee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000eaeaea00eaeaea00ea00ea00ea00ea00cccccc00cccccc00cc0ccc00cc0ccc00cc00cc00cc00cc00aaaaaa00aaaaaa00aa0aaa00aa0aaa00aa00aa00aa00aa00aa000000aa00000088008800880088000f0000000f0000000a000a000a000a0000ffaa0000ffaa0000ff000000ff000000fefe0000fefe0000eeee0000eeee0000aaaa0000aaaa0000aa000000aa00000088880000888800000f0000000f0000000a0a00000a0a000000aa000000aa0000000000000000 else 0xeaeaeaeaeaeaeaeaeaeaaaaaeaeaaaaaea00ea00ea00ea00ccccfcfcccccfcfccccceeeecccceeeecccccccccccccccccccc4444cccc4444cccc0c0ccccc0c0ccc00cc00cc00cc00cc000000cc000000c0c0c0c0c0c0c0c0afafaaaaafafaaaaafaf0000afaf0000afaaafaaafaaafaaaf00af00af00af00aeaeaeaeaeaeaeaeaaffaaaaaaffaaaaaaff0000aaff0000aaeeaaeeaaeeaaeeaaeaaaeaaaeaaaeaaaaaffaaaaaaffaaaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaa8a8aaaaa8a8aaaaa8888aaaa8888aaaa2a2aaaaa2a2aaaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0202aaaa0202aaaa00aaaaaa00aaaaaa0000aaaa0000aa88aa88aa88aa88aa2aaa2aaa2aaa2aaa0aaa0aaa0aaa0aaa00ff00aa00ff00aa00aaaaaa00aaaaaa00aa00aa00aa00aa000000aa000000a8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a08aaa8aaa8aaa8aaa8a8a8a8a8a8a8a8a88aaaaaa88aaaaaa88aa88aa88aa88aa8888aaaa8888aaaa88888888888888888888000088880000880088008800880080808080808080805555000055550000550055005500550050505050505050503f3f00003f3f00003f003f003f003f003c3c3c3c3c3c3c3c2aaa2aaa2aaa2aaa2a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a2a2a0a0a2a2a0a0a22222222222222220fff00000fff0000) else (if page < 3 then 0xff02ff02ff02ff02ff00fff0ff00fff0ff00ffeeff00ffeeff00ffaaff00ffaaff00ff88ff00ff88ff00ff0aff00ff0aff00ff00ff00ff00ff00f000ff00f000ff00ee00ff00ee00ff00af00ff00af00ff00aaaaff00aaaaff00aa00ff00aa00ff008800ff008800ff005500ff005500ff003f00ff003f00ff000f00ff000f00ff000a00ff000a00ff000300ff000300ff000000ff000000fefefefefefefefefefe0000fefe0000fef0fef0fef0fef0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafaf8faf8faf8faf8faf0fafafaf0fafafaf0faf0faf0faf0faf0f0f0faf0f0f0fa00fa00fa00fa00f8f8fafaf8f8fafaf8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f800f800f800f800f3f0f0f0f3f0f0f0f2f0f2f0f2f0f2f0f1f1f0f0f1f1f0f0f0f8f0f8f0f8f0f8f0f0fefef0f0fefef0f0fafaf0f0fafaf0f0faf0f0f0faf0f0f0f8f8f0f0f8f8f0f0f2f2f0f0f2f2f0f0f0faf0f0f0faf0f0f0f0f0f0f0f0f0f00000f0f00000f000f000f000f000ef00ef00ef00ef00eeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeee0000eeee0000eeeaeeeaeeeaeeeaeecceecceecceecceeaaeeaaeeaaeeaaee00ff00ee00ff00ee00eeeeee00eeeeee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ececececececececeaeaeeeeeaeaeeee else 0xffffffaaffffffaaffffff00ffffff00fffff0f0fffff0f0ffffeeeeffffeeeeffffaaaaffffaaaaffffaa00ffffaa00ffff8888ffff8888ffff0f00ffff0f00ffff0a0affff0a0affff00aaffff00aaffff0088ffff0088ffff0000ffff0000fff0fff0fff0fff0fff0faf0fff0faf0fff0f0f0fff0f0f0ffeeffeeffeeffeeffccccccffccccccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffaa0000ff88ff88ff88ff88ff550000ff550000ff3f0000ff3f0000ff0fff00ff0fff00ff0f0000ff0f0000ff0aff0aff0aff0aff03ff00ff03ff00ff030000ff030000)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x9e2a8541342786a1502d0 else 0
  | 3 => if page < 1 then 0x15b50ff0a8a67f8543fbec2b6a12035af8761a87f1d854528cc27a3066150fe2b0cf141180d8a08c002a2270015101800a87fc00543f6002a1b30018b50900c37c480278d5002a0562006a234003411a000a08d0004c42800002d6 else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0xd37e2bedef6d7b5bda5ecef637b0bd7debaf5b7ab7d4de36f0d785bc25e0ef0577dbb4799bcc9e63f317987cbbe57f2a794bc8db45f22790fc85e3fd9fdcfb67cf33f1978c7c61e29b92f88ee46f22b90dc82e3f71eb8edc72e35719b8c5c5ee2b711f087821e01f else 0xa21d9cf0ece54767903a7c31d3d68e9d8876c863b6321db188edaa066a5c3367f15b6788eb2c46d92236b211b5688d9dc46cec2361d11b0a08f05046b70216a20fd4a87eb243ed681f6870fb4207d8d03ea281f58c0de63033aa1ff02823400d0d8067ec02ab60149b00a3d80516c02876013fb009ed804eec027360135b0099d804c6c025f6012db0095d804a6c024f60125b0091d8060dc0302e017f700bdb805e5c02eee01757) else (if page < 3 then 0xad8c4fa464227d2a1d50f19f5a3a38c4f1da46278cd33eb44655a3a226ad1411a460907d2b52c18c019f9b900cca8c8068d3e4028a232014b03900a87fc8068be640255ef2019f71300d0b498068d84c033eb66015b45300ada198051504c02b67a6013d37300ad9a9805e4acc02ca566015b2b300d7ad38055424c02b5b8e00f8c5c00be62b0058315802b58ac00f0c5c00955fd00462f7002955b4015aa56008c50e004627f002313b8015091900ad4838054236401d51b2015a87600ad403803e1de402b4cec014e65c00ad32b003b995800d0cb801025dc008c2be005312d8033c76601463b3 else 0x5452c6633f36b633d189f8)) else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0x58fab7d4fea3f50fa7fd3be9bf4cfa47d1fe87f40f9efcf3e77f3af9cfce3e6ff36f997cbfe5df2df967cafe51f27f927c83e3bf19f88fc3fe1df0df867c2fe15f09f83fc1be0bf04f81fc0be03fcfdd16e7b72bbbcbda5ec2f5b784bb1790fc65e20b8edc66e23e else 0x9506dde035f6419f640d7ad06bbc83757c1bc960de4b0678e835c3c1bd9f5b38c4fe568e9eb446c01bbf00dcf806d7c0367e01b1f00d7f806b7c0357e01a9f00cef8065fc032be0193f00c8f8063fc0313e0187f00c2f805e7c02d3e0161f00adf80567c0233e0117f008af8043fc0213e00fff0074f8039fc01cbe00e3f0070f8037fc01bbe00dbf006bf80357c019fe00cbf0062f80307c017fe00bdf005cf802dfc016be00b3f) else (if page < 3 then 0xcb59f512cef2d66f5ab377759bd6ac5e313fb3c9fbad4fbbaa1fb6cef74a77bad3bbc79dbf44e375a7178e38bd69bde38cbd965de8c2ef52976eb4baebe5de552ef25977924bb6825ded920bee0edf6476f963b7ad1dbd68ebe3076ede3b75f1dbad0edd6476e9e3b73b1db9c0edcb876f18337ad11f5688df643fd181fecb0fbd687dddc3eeb21fe4a0ff2507dcb83fc3a1f7120fb8e875c7432fb812fad09b8e84dc7425f960de else 0xdbd1de7d6ef46977514bbd9b4bee56df66b6f975b7c9adbee56beb632f19097d95ff462ffb657df5abf7)) else 0
  | 6 => if page < 1 then 0x1b9fd9fe5feb7f19f5ffacfd3fe77f38f977c77e1ff09f837eb6e3b7 else 0
  | 7 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2b else 0
  | 3 => if page < 1 then 0x3b else 0
  | 4 => if page < 1 then 0xec3b0ac1b else 0
  | 5 => if page < 1 then 0xac2b0ac1b else 0
  | 6 => if page < 1 then 0x1b else 0
  | 7 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 4
  | 3 => 25
  | 4 => 195
  | 5 => 208
  | 6 => 17
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
  | 2 => 2
  | 3 => 14
  | 4 => 110
  | 5 => 135
  | 6 => 14
  | 7 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 7
  | 3 => 51
  | 4 => 399
  | 5 => 492
  | 6 => 62
  | 7 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 7
  | 5 => 6
  | 6 => 5
  | 7 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 5
  | 3 => 8
  | 4 => 11
  | 5 => 11
  | 6 => 8
  | 7 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x8 else 0
  | 3 => if page < 1 then 0x370fcf38221e2 else 0
  | 4 => if page < 2 then (if page < 1 then 0x6046854e64112063812aa2003001c106891c00088500c00109001011828a802a1c68a6200006202808b1604001004420802341010c00080 else 0x71d0c443b25214603009828a044c18674d00034c0c40026000010229280300c00100482002208c12) else 0
  | 5 => if page < 3 then (if page < 1 then 0x410850c564c4c008500144201124800008608f0410901012c60011c50050433095c3140005141003141081080080004 else (if page < 2 then 0x1c701601008400e0c0be93090001802ce08040205b4d308014a0050020470061000c824000a3100000020c42040c81c0 else 0x10000017400)) else 0
  | 6 => if page < 1 then 0x311002d0880120806 else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x718002200 else 0
  | 3 => if page < 1 then 0x103c8c90ab8088a81ab3c00070a0945391212878300819631100c358039b005b4b6bbb00a498000000b8004300a540b05a3d22 else 0
  | 4 => if page < 7 then (if page < 3 then (if page < 1 then 0x949172545f8af653175d78933651208e5b60e0e88c08920d2a84378b72ea9a29e80e1561083a94d18022649177006154369a9297081ab9000001280000000523dbc0001355241b09733e09ac58b80f309e574218332f844d else (if page < 2 then 0x9e0821b5b305300026e984b86d8800000000e48005388e60006e32854000000000b920a2661ab15874c00000000ad4c64b8700c0598a99502002555304b10c0b45848881415c0c460026dec3e9786d21a4d609315a1b43e0 else 0xbc2b843c4a196255148040163531bdda0320001d42c0168be1a5bcd758d1030200a037600d5e8460dc8105e42e84242c3e88030d449d956b00013a123b514a20c5a26706800daa9737542e53dc842daa41d102294d185488)) else (if page < 5 then (if page < 4 then 0x604000e84c80016e0000007e01200026084966dc4000a0000018130000001b860a6a13ac000009d0d440000017850c003b496000000000000881644cd740b45780000002b6a0deb16aac56a000b9000195d20800b80e4548 else 0xb10f42302d87782c1d15752f1551fcad014a555de8008c6c2479800456e46acc6bb56002b20e86c65c0f2d19818003083180004d11c455000ac07d8006b63a99c800000002204a9000d680036000000000008a801a2e8000) else (if page < 6 then 0x5b382179a51620000000009c9708000000706e15a51c3e6560003f82c14c62a4336c3425e41984b331181b73379024fc218637081dabe3640220759c30011e2141d8a72001890d4900001445818717800acd4204a7209a79 else 0x10f5c808027a460959318780011ca840002f4004dc))) else 0
  | 5 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x8000241000720236c85108857e1114b100116cc8d78347692d0258000929c50000019609c6293c8c88000008647cca69644856a101800000000aa8004388ae6964ba833e2f4481aa80603c82ba97481822853f54cd2d642 else 0xc6119000781341d9a5b000562185006670e1599ec001362a85487607453d0002f156800000000706be000748be06a0000012d255320810182240884c55c079ac317024310000924001f00008a60d24c0004005d000118) else (if page < 3 then 0x1b35b0516083571e2e41201a31cb08900706640605715152b2584c0a6b34f28628146fc1384508d70a2e0000ac2766de5ac7861e2741414e44cb1ddb3a9af6e4809495b74d1e4c42754219c640a726111e80054780172000 else 0x106d8264108910581c138ba80f6079000000c4030e3aa30001a421da943a3322f0bb35d33800025132c883a887200316612b4361071800001984e43e83f09ce9e56d9b56054d588550b24004ecb70001b5c58cdaf466dd0a)) else (if page < 6 then (if page < 5 then 0x5928000006a0622ec089c2140d050c9650142a66389e0b62c03b2000002609c03387ee650005711a4004936b17c21649a0011cc005f1a5a652b0480c902600037119b041fc339392949e8298886a20f0a536800021011a else 0x6106e03e58c101382a484cb28000000cc00048a341310010a400460cd26cece154aa32a6f1a959c4023013a1ce8de119d02b32094640000016880016156400071024104000005d24c636294558cd92f1180f07b580d91cb9) else (if page < 7 then 0x14e089b680e1001c414ccf990cee0005d11aa749897f2002f1598c316e6202085a01c5240031c02c2e833024688e5c0007009ac0811b151060488000010cc0000000084cbca280000000049b000ee1e45ca2d938ef050b else 0x272264501441f0001d03bb0014c0006306e0001cc2c20001a01aa0b497280000009503402c4ab000230000000019c49800089200121c7007000000000))) else 0
  | 6 => if page < 1 then 0x302000000000334c7360390000101300350000681812005b0831223c5338008040282370345232000049787b44500000007a7200414800585a00006461 else 0
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
theorem root : pool 7 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 4 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 4 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 25 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 83 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 195 0 = true :=
  (@span_join (checked 4) 112 0 83 chunk4x0 chunk4x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 96 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 208 0 = true :=
  (@span_join (checked 5) 112 0 96 chunk5x0 chunk5x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 17 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 17 0 = true :=
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

end SignedFrontier.SmallCert.Minor2

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfee8fe00fe000000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 32, 33, 34, 35, 36, 37, 38, 39, 40, 48, 49, 50, 52, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,24,25),(0xcccccccccccccccc,24,26),(0xf0f0f0f0f0f0f0f0,24,28),(0xff00ff00ff00ff00,17,25),(0xffff0000ffff0000,9,25),(0xffffffff00000000,9,41)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffffffffffff0000ffffffff00000000ffffff00ffffff00ffffaaaaffffaaaaffff0000ffff0000ffff000000000000ffaaffaaffaaffaaff00ff00ff00ff00ff000000ff000000f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaaaaa0000aaaa0000aa00aa00aa00aa0088888888888888880f0f00000f0f00000f000f000f000f000a0a0a0a0a0a0a0a00ff000000ff000000aa00aa00aa00aa00000000ffff000000000000ff00ff0000000000aaaaaaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 8 => if page < 1 then 0x31fdbfaff3fe5fc3f77ebfd5fa7f47e7fcdf97f27e3fc5f87f else 0
  | 9 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 8 => if page < 1 then 0x17 else 0
  | 9 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 8 => 18
  | 9 => 1
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
  | 8 => 20
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 8 => 73
  | 9 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 8 => 4
  | 9 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 8 => 9
  | 9 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 8 => if page < 1 then 0x5404d00a522f47100321 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 8 => if page < 2 then (if page < 1 then 0x2d3dca81120a9d607931015e2b8509a0a404281014c307a1cce0f0080854a0080158022000359c000410d8b09403000010150002200730001a8f6603d51090002c92cd03c3046871 else 0x14800400000072) else 0
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


def goalColumns : Nat := 0xfee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000fee8fe00fe000000
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0x5555555555555555 0x20a61aa2ae3a30e71eb2ef3e002412822c32106516926d36 5 8
    pinBase [0x0,0x5555555555555555,0x0,0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000,0x5555555555555555,0x1111111111111111,0x505050505050505,0x55005500550055,0x555500005555,0x55555555] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xf0f0f0f0f0f0f0f 0x209619a29e3928b69baabebb001411821c310834938a3cb3 5 8
    pinBase [0x0,0xf0f0f0f0f0f0f0f,0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0x0,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000,0x505050505050505,0x303030303030303,0xf0f0f0f0f0f0f0f,0xf000f000f000f,0xf0f00000f0f,0xf0f0f0f] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xffff0000ffff00 0x4304714b24f35345755b65f72282692aa2eb32c36d3ae3ef 5 8
    pinBase [0x0,0xffff0000ffff00,0xaaaa0000aaaa00,0xcccc0000cccc00,0xf0f00000f0f000,0xff000000ff00,0xff000000ff0000,0xffff0000000000,0x55550000555500,0x33330000333300,0xf0f00000f0f00,0xff000000ff0000,0xff000000ff00,0xffff00] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut19 : CutCertificate target :=
  makeCutCertificate target Minor1.target 0xffff00000000ffff 0x300710b20f31341751b61f72382792ba2fb33c37d3be3ff 5 8
    pinBase [0x0,0xffff00000000ffff,0xaaaa00000000aaaa,0xcccc00000000cccc,0xf0f000000000f0f0,0xff0000000000ff00,0xffff000000000000,0xffff000000000000,0x5555000000005555,0x3333000000003333,0xf0f000000000f0f,0xff0000000000ff,0xffff,0xffff] Minor1.raw Minor1.nonzero (@Minor1.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xffffffff00000000 0x9e69648e2860df6d74cf2c70beeb6caeaa68ffef7cefae78 5 8
    pinBase [0x0,0xffffffff00000000,0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000,0xffffffff00000000,0x5555555500000000,0x3333333300000000,0xf0f0f0f00000000,0xff00ff00000000,0xffff00000000,0x0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xffff0000ffff0000 0x5d65544d2450df6d74cf2c707de75c6da658ffef7cefae78 5 8
    pinBase [0x0,0xffff0000ffff0000,0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff0000ffff0000,0xffff000000000000,0x5555000055550000,0x3333000033330000,0xf0f00000f0f0000,0xff000000ff0000,0x0,0xffff0000] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 4 => cut3
  | 11 => cut10
  | 20 => cut19
  | 21 => cut20
  | 22 => cut21
  | _ => cut1

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 8 => if page < 1 then 0x2ab1544b1084221056152a2 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 5 i

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

theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 18 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 18 0 = true :=
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
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
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

end PEqualNP.Outside.L_meta_12316_aux

open PEqualNP.Outside.L_meta_12316_aux

theorem PEqualNP.Outside.L_meta_12316 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
