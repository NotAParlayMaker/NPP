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

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfee8fe00fe000000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 32, 33, 34, 35, 36, 37, 38, 39, 40, 48, 49, 50, 52, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  | 0 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xaaeeaaee00000000aaaaffaa00000000aaaaeeee00000000aaaaaaaa00000000aaaaaa0000000000aaaa888800000000aaaa0a0a00000000aaaa00aa00000000aaaa000000000000aa88aa8800000000aa0aaa0a00000000aa00ff0000000000aa00aaaa00000000aa00aa0000000000aa00000000000000a8a8a8a8000000008a8a8a8a0000000088aa88aa000000008888aaaa0000000088888888000000008888000000000000880088000000000080808080000000003f3f0000000000003f003f00000000002a2a2a2a000000000fff0000000000000f0f0f00000000000f0f0a0a000000000f0f0000000000000f0a0f0a000000000f00ff00000000000f000f00000000000f000000000000000e0e0e0e000000000aaa0aaa000000000a0aaaaa000000000a0a0a0a000000000a0a0000000000000a000a0000000000080808080000000003030000000000000300030000000000020202020000000000ffff000000000000ff00aa0000000000ff00000000000000ee00ee0000000000aaaaaa0000000000aa00aa0000000000aa0000000000000088008800000000000f000000000000000a000a000000000000ffaa000000000000ff00000000000000eeee000000000000aaaa000000000000aa0000000000000088880000000000000f000000000000000a0a00000000000000aa0000000000000000 else 0x88888888888800000f0ffffff0f000000f00ff00ff0000000f000f000f0000000a0aaaaaaaaa00000a0a0a0a0a0a000000ffffffff00000000ffffff0000000000ff00ff0000000000aaffffffaa000000aaaaaaaaaa000000aa00aa00aa00000000ffffffee00000000ffffffaa00000000ffffff8800000000ffffff0a00000000ffffff0000000000fffffefe00000000ffffeeee00000000ffffaaaa00000000ffffaa0000000000ffff888800000000ffff0f0000000000ffff0a0a00000000ffff00aa00000000ffff000000000000fffefffe00000000ffeeffee00000000ffeeffaa00000000ffeeff0000000000ffeaffea00000000ffccffcc00000000ffaaffaa00000000ffaaff0000000000ffaaaaaa00000000ffaa000000000000ff88ff8800000000ff0fff0000000000ff0f000000000000ff0aff0a00000000ff00ffaa00000000ff00ff0000000000ff00aa0000000000ff000f0000000000ff00000000000000fefefefe00000000feeefeee00000000fcfcfcfc00000000eeeeffee00000000eeeefefe00000000eeeeeeee00000000eeeeaaaa00000000eeee000000000000eeaaeeaa00000000ee00ee0000000000eaeaeaea00000000cccccccc00000000afafaaaa00000000afaf000000000000afaaafaa00000000af00af0000000000aeaeaeae00000000aaffaaaa00000000aaff0000) else (if page < 3 then 0xaa008800aa008800aa000a00aa000a00aa0000ffff000000aa0000aaaaaaaa00aa0000aaaa000000aa000000ff000000aa000000aa00aa00aa000000aa000000aa00000000000000a800a800a800a8008a008a008a008a00880088aaaaaaaa00880088888888880088008800aa00aa0088008800880088008800000088000000800080008000800055005500000000003f0000003f0000003c003c003c003c002a002a002a002a000f000ffff0fff0000f000f000f0000000f000a000f000a000f0000ffff0000000f00000f0f0000000f000000ff0000000f0000000f0000000f000000000000000e000e000e000e000a000aaaaaaaaa000a000a0a0a0a0a000a000a00aa00aa000a000a000a000a000a0000000a00000008000800080008000300000003000000020002000200020000ffffffffff000000ffffffffaaaa0000ffffffff00000000ffff0000ff000000ffff0000f0f00000ffff0000aaaa0000ffff000000000000ffee0000ffee0000ffaaffaaffaa0000ff00ffffff000000ff00ffff00000000ff00ff00ff000000ff00ff0000000000ff000000ff000000fefe0000fefe0000eeeeeeeeeeee0000cccc0000cccc0000aaaaffffaaaa0000aaaaff00ffaa0000aaaacccceeee0000aaaaaaaaaaaa0000aaaa0000aaaa0000aa00ff00ff000000aa00aaaaaaaa0000aa00aa00aa0000008888aaaaaaaa else 0xffff000000000000ff00ffffff000000ff00ffff00ff0000ff00ffff00000000ff00ffaaaaaaaa00ff00ff0ff00ff000ff00ff00ffff0000ff00ff00ffaaaa00ff00ff00ff00ee00ff00ff00ff00aa00ff00ff00ff008800ff00ff00ff000a00ff00ff00ff000000ff00ff00f000f000ff00ff00aa00aa00ff00ff0000000000ff00fe00ff00fe00ff00ee00ff00ee00ff00aaffffaaaa00ff00aa00ff00aa00ff00aa00ff000000ff00aa00aa00aa00ff008800ff008800ff000f00ff000000ff000a00ff000a00ff0000ffffff0000ff0000ffff000000ff0000ff00ff0000ff0000ff00000000ff0000aaffaaaa00ff0000aaff000000ff00000fff000000ff000000ffff0000ff000000ff00aa00ff000000ff000000ff000000aa000000ff0000000f000000ff00000000ff0000ff00000000000000fe00fe00fe00fe00fc00fc00fc00fc00ee00eeeeeeeeee00ee00ee00ee00ee00ee00aa00ee00aa00ee0000ffff000000ee000000ee000000ea00ea00ea00ea00cc00cc00cc00cc00af00aa00af00aa00af000000af000000ae00ae00ae00ae00aaaaaaaaaaaaaa00aa00aaffff00aa00aa00aaffaaffaa00aa00aacceeccee00aa00aaaaaaaaaa00aa00aaaaaa00aa00aa00aa88aa88aa00aa00aa0aaa0aaa00aa00aa00ff00aa00aa00aa00ee00ee00aa00aa00aaaaaa00aa00aa00aa00aa00aa00aa00aa0000)) else (if page < 6 then (if page < 5 then 0xa020a020a020a020a000a00ff00ff000a000a00aaaaaaaa0a000a00aa00aa000a000a000f000f000a000a000a0a0a0a0a000a000a000a000a0000000a00000008aa08aa08aa08aa0888088808880888080a080a080a080a08080808aaaaaaaa0808080888888888080808080a0a0a0a08080808080808080808000008080000080008000800080007070707070700000707070007070700070703030505000007070000070700000706070607060706070007000700070006ee06ee06ee06ee0606060606060606050005000500050003ff0000ffff000003ff000003ff000003fc03fc03fc03fc03cc03cc03cc03cc030f030f030f0000030f0300030f0300030f0000030f000003030303fcfcfcfc03030303030300000303030003030300030302020303020203030000ffff0000030300000f0f000003030000030300000303000000000000030203020302030203000300ff00ff00030003000f000f000300030003000300030000000300000002ea02ea02ea02ea02aa02aaaaaaaaaa02aa02aa0aaa0aaa02aa02aa02aa02aa02aa020202aa0202020a020a020a020a02020202aaaaaaaa020202020a0a0a0a0202020202020202020200000202000002000200020002000101000001010000010001000100010000ffffffffff000000ffffff0000000000ffff00ffff000000ffff00ff00ff0000ffff0000ffff00 else 0xaaa0aaafaaafaaa0aaa0aaaceeeceee0aaa0aaaaaaaaaaa0aaa0aaaaaaa0aaa0aaa0aaa8aaa8aaa0aaa0aaa2aaa2aaa0aaa0aaa0eee0eee0aaa0aaa0afa0afa0aaa0aaa0aaaaaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0a0a0aaa0aaa0aaa00aa0aaa0aaa0aaa00000aaa0a8a0aaa0a8a0aaa0a2a0aaa0a2a0aaa0a0aaaaaaaaa0aaa0a0aaaaa0a0a0aaa0a0a0aaa0aaa0aaa0a0a0aaa0a0a0aaa0a0a0a0a0a0a0aaa0a000aaa0a000aaa02aa0aaa02aa0aaa02220aaa02220aaa00aa0aaa00aa0aaa00000aaa00000a8a0a8a0a8a0a8a0a5a0a5a0a5a0a5a0a2a0a2aaaaaaaaa0a2a0a2a2a2a2a2a0a2a0a2a0aaa0aaa0a2a0a2a0a2a0a2a0a2a0a0a0a2a0a0a0a0f0a0a0a0f0a0a0a0f00000a0f00000a0e0a0e0a0e0a0e0a0aaaaaaaaaaaaa0a0a0a0affff0a0a0a0a0a0aff0aff0a0a0a0a0afafafafa0a0a0a0acececece0a0a0a0aaaaaaaaa0a0a0a0aaaaa0a0a0a0a0a0aaa0aaa0a0a0a0a0a8a8a8a8a0a0a0a0a2a2a2a2a0a0a0a0a0f0f0a0a0a0a0a0a0f0a0f0a0a0a0a0a0e0e0e0e0a0a0a0a0aaa0aaa0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a000a0a0a000a0a08080a0a08080a0a02020a0a02020a0a000a0a0a000a0a0a0000ffff00000a0a0000aaaaaaaa0a0a0000aaaa00000a0a00000f0f00000a0a00000a0a0a0a0a0a00000a0a00000a0a0000000000000a080a080a080a08) else (if page < 7 then 0xf0f0000000000000f0e0f0e0f0e0f0e0f0e0f0a0f0e0f0a0f0e0f000f0e0f000f0c0f0c0f0c0f0c0f0a0f0affaaffaa0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0a0a0f0a0a0a0f0a00000f0a00000f080f080f080f080f070f000f070f000f060f060f060f060f030f000f030f000f0300000f0300000f020f020f020f020f00ff00ff00ff000f00ff000f00ff000f000f00ffff0f000f000f00fff0fff00f000f00ff00ff000f000f00ff000f000f000f00afaaafaa0f000f00af00af000f000f003f003f000f000f000f0f0f000f000f000f0a0f0a0f000f000f00ff000f000f000f000f000f000f000f0000000f000f00000000000f000a000f000a000f0003000f0003000f000000ffff00000f000000ff00ff000f000000ff0000000f0000000f0f00000f0000000f000f000f0000000f0000000f000000000000000eee0eee0eee0eee0eaa0eaa0eaa0eaa0e0e0e0eeeeeeeee0e0e0e0e0e0e0e0e0e0e0a0a0e0e0a0a0e0e00000e0e00000e0a0e0a0e0a0e0a0e000e000e000e000ccc0ccccccccccc0ccc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0c0c0c0c0c0c0c0c0b0b0a0a0b0b0a0a0b0b00000b0b00000b0a0b0a0b0a0b0a0b000b000b000b000aff0a0a0aff0a0a0aff0000ffff00000aff00000aff00000afa0afa0afa0afa0aea0aea0aea0aea0ace0ace0ace0ace0aaaaaaaaaaaaaaa0aaa0aaafafafafa else 0xf0f0f0a0f0f0a0a0f0f0f0a0f0f00000f0f0f0a0f0a0f0a0f0f0f080f0f0f080f0f0f030f0f0f000f0f0f030f0f00000f0f0f020f0f0f020f0f0f00ffffff000f0f0f00afafafaa0f0f0f00afafaf000f0f0f000fff0f000f0f0f000f0fff000f0f0f000f0f0f0a0f0f0f000f0f0f000f0f0f000f0f0a000f0f0f000f0f03000f0f0f000f0f00000f0f0f000f0a0f000f0f0f000f030f000f0f0f000f000f000f0f0f000f0000000f0f0e0e0f0f0e0e0f0f0b0b0f0f0a0a0f0f0b0b0f0f00000f0f0b0a0f0f0b0a0f0f0b000f0f0b000f0f0a0affffaaaa0f0f0a0a0f0f0a0a0f0f0a0a0f0f00000f0f0a0a0a0a0a0a0f0f0a000f0f0a000f0f08080f0f08080f0f07070f0f00000f0f07000f0f07000f0f030f0f0f00000f0f03030f0f03000f0f03030f0f02020f0f03030f0f00000f0f03030f0003000f0f03020f0f03020f0f03000f0f0f000f0f03000f0f03000f0f03000f0f00000f0f0300030003000f0f02020f0f02020f0f01010f0f00000f0f01000f0f01000f0f000f0f0f00000f0f000a0f0f000a0f0f0000fffff0f00f0f0000ffff00000f0f0000ff0fff000f0f0000ff0f00000f0f0000afafaaaa0f0f0000afaf00000f0f00003f3f00000f0f00000fff00000f0f00000f0f0f000f0f00000f0f0a0a0f0f00000f0f00000f0f00000f0000000f0f00000a0a00000f0f0000030300000f0f0000000f0000))) else (if page < 12 then (if page < 10 then (if page < 9 then 0xfff0ffff000f0000fff0fff0fff00000fff0fff000000000fff0f00ffff00000fff0f000fff0f000fff0aaa0fff0aaa0fff00ff0f0f00000fff00f00fff00f00fff0000ffff00000fff00000fff00000fff00000f0f00000fff000000ff00000fff0000000000000ff00ff0ff00ff000ff00ff0f0f0f0f00ff00ff00ff00ff00ff00f000ff00f000faf00aa0faf00aa0faf00000faf00000faa0faa0faa0faa0f3f00000f3f00000f3c0f3c0f3c0f3c0f0fffffffff00000f0fffff000000000f0ff0f0ffff00000f0ff0f0f0f0f0f00f0ff0f00f0ff0f00f0f0f0fffff00000f0f0f0fff00ff000f0f0f0ffafafafa0f0f0f0ff0f0f0f00f0f0f0ff0f000000f0f0f0ff000f0000f0f0f0fafafaaaa0f0f0f0fafaf00000f0f0f0fafaaafaa0f0f0f0faf00af000f0f0f0faaaaaaaa0f0f0f0f3c3c3c3c0f0f0f0f303030300f0f0f0f0fff0f000f0f0f0f0fff00000f0f0f0f0ff00ff00f0f0f0f0faa0faa0f0f0f0f0f0fff000f0f0f0f0f0ff0f00f0f0f0f0f0faaaa0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a000f0f0f0f0f0f08080f0f0f0f0f0f03000f0f0f0f0f0f02020f0f0f0f0f0f000a0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0f0000000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0e0f0f0f0e0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f00 else 0x333333330303000033333333000000003333333033333330333333223333332233333300333333003333330033330000333333003300330033333030333330303333030333330000333303003333030033330000333300003322332233223322330033003300330030f030f030f030f030303030303030302f2f22222f2f22222f2f00002f2f00002f222f222f222f222f002f002f002f002eaa2eaa2eaa2eaa2e2e2e2e2e2e2e2e2e2a2e2a2e2a2e2a2aea2aea2aea2aea2aaa2aaaaaaaaaaa2aaa2aaa2aaa2aaa2aaa2a2a2aaa2a2a2aaa0aaa2aaa0aaa2aaa0a0a2aaa0a0a2a2aaaaaaaaaaaaa2a2a2a2aeeeeeeee2a2a2a2aeaeaeaea2a2a2a2aaaaaaaaa2a2a2a2aaaaa2a2a2a2a2a2aaa2aaa2a2a2a2a2a2e2e2e2e2a2a2a2a2aaa2aaa2a2a2a2a2a2aaaaa2a2a2a2a2a2a2a2a2a2a2a2a2a2a22222a2a2a2a2a2a0a0a2a2a2a2a2a2a00002a2a2a222a2a2a222a2a2a0a2a2a2a0a2a2a2a002a2a2a002a2a22222a2a22222a2a0a2a2a2a0a2a2a2a0a0aaaaaaaaa2a2a0a0aaaaa0a0a2a2a0a0a2a2a2a2a2a2a0a0a2a2a0a0a2a2a0a0a222200002a2a0a0a0a0a0a0a2a2a00002a2a00002a0a2a0a2a0a2a0a2a002a002a002a0022aa22aa22aa22aa22222222aaaaaaaa22222222222222221f1f00001f1f00001f001f001f001f001e1e1e1e1e1e1e1e1a1a1a1a1a1a1a1a11111111000000001100110011001100) else (if page < 11 then 0x5555555550505050555555554444444455555555000000005555550055555500555550505555505055554444555544445555111155550000555511005555110055550000ffff000055550000555500005555000000000000555055505550555055445544554455445500ff005500ff0055005500ff00ff0055005500550055005500550000000000545454545454545450f050f050f050f05050f0f05050f0f050505050f0f0f0f050505050505050504ccc4ccc4ccc4ccc4c4c4c4c4c4c4c4c44cc44cc44cc44cc44444444444444443fff0000ffff00003fff00003fff00003fc03fc03fc03fc03f3f3f3fc0c0c0c03f3f3f3f3f3f00003f3f3f003f3f3f003f3f3c3c3f3f3c3c3f3f30303f3f30303f3f2a2a3f3f2a2a3f3f0f0f333300003f3f0c0c3f3f0c0c3f3f0000ffff00003f3f00003f3f00003f3f00000f0f00003f3f0000000000003f3c3f3c3f3c3f3c3f2a3f2a3f2a3f2a3f0f33003f0f33003f0f00003f0f00003f0c3f0c3f0c3f0c3f00ff00ff00ff003f003f00ff00ff003f003f003f003f003f000f003f000f003f0000003f0000003e3e3e3e3e3e3e3e3cfc3cfc3cfc3cfc3ccc3ccc3ccc3ccc3c3c3c3cfcfcfcfc3c3c3c3ccccccccc3c3c3c3c3c3c3c3c3c3c0c0c3c3c0c0c3c3c00003c3c000033333333333333003333333333333030333333333333222233333333333300003333333333003300 else 0x88aa88aaaaaaaaaa88aa88aa88aa88aa88aa888888aa888888aa00aa88aa00aa88aa000088aa000088a888a888a888a8888a888a888a888a8888aaaaaaaaaaaa88888888ffff888888888888ff88ff8888888888f8f8f8f888888888eeeeeeee88888888aaaaaaaa88888888aaaa888888888888aa88aa8888888888a8a8a8a8888888888a8a8a8a8888888888aa88aa888888888888aaaa88888888888888888888888888880000888888008888880088888080888880808888080888880808888800888888008888880000ffff000088880000aaaaaaaa88880000aaaa00008888000088888888888800008888000088880000000000008880888088808880880888088808880888008800ff00ff0088008800aaaaaaaa88008800aa00aa0088008800888888888800880088008800880000008800000080aa80aa80aa80aa808880888088808880808080aaaaaaaa80808080888888888080808080808080808000008080000080008000800080007f7f00007f7f00007f007f007f007f007777777700000000770077007700770070707070707070706e6e6e6e6e6e6e6e6a6a6a6a6a6a6a6a5f5f5f5f000000005f5f0a0a5f5f0a0a5f5f00005f5f00005f005f005f005f005a5a5a5a5a5a5a5a55ff55ff0000000055aa55aa55aa55aa5555ffff0000000055555555aaaaaaaa55555555555500005555555555005500)) else (if page < 14 then (if page < 13 then 0xaa000000ff00ff00aa000000ff000000aa000000aaaaaaaaaa000000aaaa0000aa000000aa00aa00aa000000aa000000aa00000000000000a8fca8fca8fca8fca8aaa8aaa8aaa8aaa8a8a8a8fcfcfcfca8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a8a88888a8a88888a8a80000a8a80000a888a888a888a888a800a800a800a800a2aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a0f0a0f0a0f0a0f0a0aaa0aaa0aaa0aaa0a0f0f0a0a0f0f0a0a0aaaaa0a0aaaaa0a0a0aaa0a0a0aaa0a0a0a0f0f0f0f0a0a0a0a0aaaaaaaaa0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a000a000a0009a9a9a9a9a9a9a9a99aa99aa99aa99aa99999999aaaaaaaa99998888999988889999000099990000998899889988998898f898f898f898f898989898989898988f8f8f8f8f8f88888f8f8f8f8f8f00008f8f8f888f8f8f888f8f8f008f8f8f008f8f88888f8f88888f8f00008f8f00008f888f888f888f888f008f008f008f008ccc8ccc8ccc8ccc8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aaa8a8a8aaa8a8a8aaa0aaa8aaa0aaa8aaa0a0a8aaa0a0a8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a8a8a88888a8a88888a8a0a0a8a8a0a0a8a8a00008a8a00008a888a888a888a888a0a8a0a8a0a8a0a8a008a008a008a0088ff888888ff888888ff0000ffff000088ff000088ff000088f888f888f888f8 else 0xaaaa0000aaaaaa00aaaa0000aaaa8888aaaa0000aaaa0a0aaaaa0000aaaa00aaaaaa0000aaaa0000aaaa0000aa000000aaaa000088880000aaaa00000a0a0000aaaa000000aa0000aaaa000000000000aaa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa8aa00aaa8aa00aaa0aaa0aaa0aaa0aa8aaa8aaa8aaa8aaa88aa88ffccffccaa88aa88aaaaaaaaaa88aa88aa88aa88aa88aa00aa88aa00aa888888aa888888aa880000aa880000aa80aa80aa80aa80aa5aaa5aaa5aaa5aaa55aa55ff00ff00aa55aa55aaaaaaaaaa55aa00aa55aa00aa2aaa2aaaaaaaaaaa2aaa2aaa2aaa2aaa2aaa0aaa2aaa0aaa2aaa00aa2aaa00aa2a2a2aaa2a2a2aaa2a0a0aaa2a0a0aaa22aa22aa22aa22aa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa0aaa00aa0aaa00aa0a0a0aaa0a0a0aaa0a0000aa0a0000aa08aa08aa08aa08aa02aa02aa02aa02aa00ff00ff00ff00aa00ff00aa00ff00aa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaa0000aaaaaa00aa00ffffaa00aa00aa00ff00ff00aa00aa00ff00aa00aa00aa00eecceeccaa00aa00ee00ee00aa00aa00af00af00aa00aa00aaaaaaaaaa00aa00aaaaaa00aa00aa00aa88aa88aa00aa00aa0aaa0aaa00aa00aa00ff00aa00aa00aa00aaaaaa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000aa008800aa008800aa000a00aa000a00aa000000ffff0000) else (if page < 15 then 0xaaaa0e0eaaaa0e0eaaaa0afaaaaa0afaaaaa0aaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0a0aaaaa0aaaaaaa00aaaaaa0aaaaaaa0000aaaa0aaa0aaa0aaaaaaa0a8aaaaa0a8aaaaa0a2aaaaa0a2aaaaa0a0afafafafaaaaa0a0afafa0a0aaaaa0a0aeeeececeaaaa0a0aeeee0e0eaaaa0a0aaaaafafaaaaa0a0aaaaaaaaaaaaa0a0aaaaaaa0aaaaa0a0aaaaa8a8aaaaa0a0aaaaa2a2aaaaa0a0aaaaa0aaaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a00aaaa0a0aaaaa0808aaaa0a0aaaaa0202aaaa0a0aaaaa000aaaaa0a0aaaaa0000aaaa0a0aaa0a0a0aaaaa0a0aaa000a00aaaa0a0a8a8a0a0aaaaa0a0a2a2a0a0aaaaa0a0a22220202aaaa0a0a0aaa0a0aaaaa0a0a0a0a0a0aaaaa0a08aaaa0a08aaaa0a02aaaa0a02aaaa0a00aaaaaaaaaaaa0a00aaaaaa00aaaa0a00aaaa0a0aaaaa0a00aaaa0a00aaaa0a00aaaa0000aaaa0a000a000a00aaaa0808aaaa0808aaaa02aaaaaa02aaaaaa020aaaaa020aaaaa0202aaaaaaaaaaaa0202aaaa0a0aaaaa0202aaaa0202aaaa0202aaaa0000aaaa020202020202aaaa0200aaaa0200aaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa0000aaaa00aa00aa00aaaaaa0088aaaa0088aaaa000aaaaa000aaaaa0000ffff0000aaaa0000ffaaff00aaaa0000ffaa0000aaaa0000eeeeccccaaaa0000eeee0000aaaa0000afaf0000aaaa0000aaff0000aaaa0000aaaaaaaa else (if page < 16 then 0xaaaaaa2aaaaaaa2aaaaaaa22aaaaaa22aaaaaa0aaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa00aaaaaa0aaaaa0a0aaaaaaa0aaaaa0000aaaaaa0aaa0aaa0aaaaaaa08aaaaaa08aaaaaa02aaaaaa02aaaaaa00ffffff00aaaaaa00eeeeeeccaaaaaa00eeeeee00aaaaaa00aaffaa00aaaaaa00aaaaff00aaaaaa00aaaaaaaaaaaaaa00aaaaaa88aaaaaa00aaaaaa0aaaaaaa00aaaaaa00aaaaaa00aaaa8800aaaaaa00aaaa0a00aaaaaa00aaaa0000aaaaaa00aa88aa00aaaaaa00aa0aaa00aaaaaa00aa00aa00aaaaaa00aa000000aaaaa8a8aaaaa8a8aaaaa0a0aaaaa0a0aaaa8aaaaaaa8aaaaaaa8a8aaaaaaaaaaaaa8a8aaaaa8a8aaaaa8a8aaaaa8888aaaa8a8aaaaa0a0aaaaa8a8aaaaa0000aaaa8a8a8a8a8a8aaaaa8a88aaaa8a88aaaa8a0aaaaa8a0aaaaa8a00aaaa8a00aaaa88aaaaaa88aaaaaa8888ffffccccaaaa8888aaaaaaaaaaaa8888aaaa8888aaaa8888aaaa0000aaaa888888888888aaaa8800aaaa8800aaaa8080aaaa8080aaaa5a5aaaaa5a5aaaaa55aaaaaa55aaaaaa5555ffff0000aaaa5555aaaaaaaaaaaa5555aaaa0000aaaa5500aaaa5500aaaa2e2eaaaa2e2eaaaa2aaaaaaa2aaaaaaa2a2aaaaaaaaaaaaa2a2aaaaa2a2aaaaa2a2aaaaa0a0aaaaa2a2aaaaa0000aaaa2a2a2a2a2a2aaaaa2a0aaaaa2a0aaaaa2a00aaaa2a00aaaa2222aaaa2222aaaa2222aaaa0000aaaa2200aaaa2200 else 0xaaaaaaaaffaaaaaaaaaaaaaaff00ff00aaaaaaaafefefefeaaaaaaaafafafafaaaaaaaaaeeeeeeeeaaaaaaaaeeeeaaaaaaaaaaaaeeaaeeaaaaaaaaaaeaeaeaeaaaaaaaaaccccccccaaaaaaaaafafaaaaaaaaaaaaafaaafaaaaaaaaaaaeaeaeaeaaaaaaaaaaffaaaaaaaaaaaaaaeeaaeeaaaaaaaaaaaaffaaaaaaaaaaaaaaeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa0aaaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0aaaaaaaaaaaa8a8aaaaaaaaaaaaa88aaaaaaaaaaaaaa8888aaaaaaaaaaaa8800aaaaaaaaaaaa8080aaaaaaaaaaaa2a2aaaaaaaaaaaaa2222aaaaaaaaaaaa0aaaaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a00aaaaaaaaaaaa0808aaaaaaaaaaaa0202aaaaaaaaaaaa00aaaaaaaaaaaaaa0088aaaaaaaaaaaa000aaaaaaaaaaaaa0000aaaaaaaaaa00aaaaaaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa22222222aaaaaaaa0aaa0aaaaaaaaaaa0a0aaaaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a00aaaaaaaa0a0a0000aaaaaaaa00aa00aaaaaaaaaa0000aaaaaaaaaaaa000000aaaaaaaaaa00000000aaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa8aaaaaaa8aaaaaaa88aaaaaaaaaaaaaa88aaaaaa88aaaaaa88aaaaaa00aaaaaa88aaaa8888aaaaaa88aaaa0000aaaaaa88aa88aa88aaaaaa80aaaaaa80))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0xaeeeaeeeaeeeaeeeaeccaeccaeccaeccaeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaaaaaeae0c0caeae0c0caeae0000aeae0000aeaaaeaaaeaaaeaaae0cae0cae0cae0cae00ae00ae00ae00acecacecacecacecacccacccacccacccacacacacacacacacababaaaaababaaaaabab0000abab0000abaaabaaabaaabaaab00ab00ab00ab00aaffaaffaaffaaaaaaffaaffaaff0000aaffaaffaaaaaaaaaaffaaff00000000aaffaaeeaaffaaeeaaffaaaaffffaaaaaaffaaaaaaffaaaaaaffaaaaaaaaaaaaaaffaa00ffff0000aaffaa00aaffaa00aaff88ccaaff88ccaaff5500aaff5500aaff00ffaaaa0000aaff0000ffff0000aaff0000aaff0000aaff0000aaaa0000aaff000000ff0000aaff000000000000aafeaafeaafeaafeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaee00ccaaee00ccaaee0000ffff0000aaee0000aaee0000aaeaaaeaeeeeeeeeaaeaaaeaeaeaeaeaaaeaaaeaaaeeaaeeaaeaaaeaaaeaaaeaaaeaaaaaaaeaaaaaaaccaaccaaccaaccaaafaaaaaaafaaaaaaaf0000aaaf0000aaaeaaaeaaaeaaaeaaaaffffffff0000aaaaffff00000000aaaaffaaffaaffaaaaaafefeaaaafefeaaaafafaaaaafafaaaaaeeeeeeeeeeeeaaaaeeeeaaaaeeeeaaaaaaaaffffffaaaaaaaaaaffffeeeeaaaaaaaaffffaaaaaaaaaaaaffff0000aaaaaaaaffeeffeeaaaaaaaaffaaffaa else 0xc4ccc4ccc4ccc4ccc4c4c4c4c4c4c4c4c444c444c444c444c0ccc0ccc0ccc0ccc0c0f0f0c0c0f0f0c0c0ccccc0c0ccccc0c0c0ccc0c0c0ccc0c0c0c0c0c0ccccc0c0c0c0c0c0c0c0c0c0c0c000000000c0c00000c0c00000c000c000c000c000bfbfaaaabfbfaaaabfbf0000bfbf0000bfaabfaabfaabfaabf00bf00bf00bf00bebebebebebebebebcbcbcbcbcbcbcbcbbaabbaabbaabbaababababababababab0b0b0b0b0b0b0b0afffaaaaafffaaaaafff0000ffff0000afff0000afff0000aff0aff0aff0aff0afafafafafafaaaaafafafafafaf0000afafafafaaaaaaaaafafafaf00000000afafafaaafafafaaafafaf00afafaf00afafaeaeafafaeaeafafaaaaffffaaaaafafaaaaafafaaaaafafaaaaaaaaaaaaafafa0a0afafa0a0afaf8c8cafaf8c8cafaf5050afaf5050afaf0f0faaaa0000afaf0000ffff0000afaf0000afaf0000afaf0000aaaa0000afaf00000f0f0000afaf000000000000afaeafaeafaeafaeafacafacafacafacafaaafaaffaaffaaafaaafaaafaaafaaafaaaaaaafaaaaaaafaa0f00afaa0f00afaa0000afaa0000afa0afa0afa0afa0af8caf8caf8caf8caf50af50af50af50af0faf0faf0faa00af0faf0faf0f0000af0faf00af0faf00af0faa00af0faa00af0f0000af0f0000af00af00ff00ff00af00af00af00af00af00aa00af00aa00af000f00af000f00af000000af000000) else (if page < 20 then 0xcccccccceeeeeeeecccccccceeeecececccccccceeeecccccccccccceecceeccccccccccececececccccccccceeeceeecccccccccececececcccccccccffcccccccccccccceecceeccccccccccccffccccccccccccccfcfccccccccccccceeeecccccccccccccccccccccccccccccc00ccccccccccccc0c0ccccccccccccaaaacccccccccccc8888cccccccccccc4444cccccccccccc0c0ccccccccccccc00cccccccccccccc0000cccccccccc88cc88cccccccccc44cc44cccccccccc00cc00ccccccccc4c4c4c4cccccccc4c4c4c4ccccccccc44cc44cccccccccc4444cccccccccccc4444c4c4cccccccc44444444cccccccc0c0c0c0ccccccccc00000000ccccccc0ccccccc0ccccccaaccccccaacccccc88cccccc88cccccc44cccccc44cccccc0ccccccc0ccccccc00cccccccccccccc00cccccc00cccccc00cccc0000cccccc00cc00cc00cccccc00cc000000ccccc4c4ccccc4c4ccccc444ccccc444ccccaeaeccccaeaeccccacacccccacaccccc8c8ccccc8c8ccccc4c4ccccc4c4ccccc44cccccc44cccccc4444cccc4444cccc444444444444cccc0ccccccc0ccccccc0c0ccccccccccccc0c0ccccc0c0ccccc0c0ccccc0000cccc0c0c0c0c0c0ccccc0c00cccc0c00cccc0000ffff0000cccc0000cccc0000ccc8ccc8ccc8ccc8cc4ccc4ccc4ccc4ccc44cc44cc44cc44cc00cc00cc00cc00cacacacacacacaca else 0xeaeaeac0eaeaeac0eaeaeaaaeaeaeaaaeaeaea00eaeaea00eaeacacaeaeacacaeaeac2c2eaeac2c2eaeac0c0eaeac0c0eaeaaaeaeaeaaaeaeaeaaaaaeeeeeeeeeaeaaaaaeeeeaaaaeaeaaaaaeaeaeaeaeaeaaaaaeaeaaaaaeaeaaaaaaaaaaaaaeaea2a2aeaea2a2aeaea0a0aeaea0a0aeaea0202eaea0202eaea0000ffff0000eaea0000eaea0000eae8eae8eae8eae8eac0eac0eac0eac0eaaaeaaaeaaaeaaaea00ea00ea00ea00e8e8e8e8e8e8e8e8e6e6e6e6e6e6e6e6e4e4e4e4e4e4e4e4e0e0e0e0e0e0e0e0ddddddddccccccccdddddddd00000000ddddccccddddccccdddd0000dddd0000ddccddccddccddccdd00dd00dd00dd00dcdcdcdcdcdcdcdcdcccdcccdcccdcccd5d50000d5d50000d500d500d500d500d0d0d0d0d0d0d0d0cfcfcccccfcfcccccfcccfcccfcccfcccfc0cfc0cfc0cfc0ceeeceeeceeeceeececececececececececccecccecccecccceecceecceecceeccecccecccecccecccccffff00000000ccccfefeccccfefeccccfcfcfcfcfcfcccccfcfcccccfcfcccccfcfcccccccccccccfcccccccfccccccceeeeeeeeeeeecccceeeecccceeeeccccececccccececccccdcdcccccdcdccccccececccccececcccccffccccccccccccccfcccccccfccccccceecccccceeccccccccffffccccccccccccffccffccccccccccfefcfefcccccccccfcfcfcfcccccccccfcfcccccccccccccfcccfccc)) else (if page < 23 then (if page < 22 then 0xeeeeaaaaaaaaaaaaeeee6666eeee6666eeee2222eeee2222eeee0e0eeeee0e0eeeee00eeeeee00eeeeee0000ffff0000eeee0000ffee0000eeee0000fefe0000eeee0000eeeeeeeeeeee0000eeee0000eeee0000aaaa0000eeee000000000000eeeceeeceeeceeeceeeaeeeaeeeeeeeeeeeaeeeaeeeaeeeaeeeaeeaaeeeaeeaaeeeaeaeaeeeaeaeaeeeaaaaaeeeaaaaaeee0eee0eee0eee0eecceecceeeeeeeeeecceecceecceecceecccecceecccecceecccccceecccccceeaeeeaeeeaeeeaeeeaaeeaaffaaffaaeeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaeeaa0000eeaa0000ee66ee66ee66ee66ee44ee44ee44ee44ee22ee22ee22ee22ee0eee0eee0eee0eee00ee00ff00ff00ee00ee00eeeeeeeeee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ececfcfcececfcfcececeeeeececeeeeecececeeecececeeececececfcfcfcfcececececeeeeeeeeececececececeeeeececececececececececececccccccccececccccececcccceccceccceccceccceaeeeaeeeaeeeaeeeaeafafaeaeafafaeaeaeeeeeeeeeeeeeaeaeeeeeaeaeeeeeaeaeaeeeaeaeaeeeaeaeaeafefefefeeaeaeaeaeeeeeeeeeaeaeaeaeeeeeaeaeaeaeaeaeeeaeeeaeaeaeaeaeaeeeaeeeaeaeaeaeaeaeeeeeaeaeaeaeaeaeaeaeaeaeaeaeaeac0c0eaeaeaeaeaeaaaaaeaeaeaeaeaea0000 else 0xf0f0f0c0f0f0f0c0f0f0f050f0f0f050f0f0f000f0f0f000f0f0f000f0f00000f0f0a0a0f0f0a0a0f0f07070f0f07070f0f05050f0f05050f0f03030f0f03030f0f01010f0f01010f0f000f0f0f000f0f0f00000ffff0000f0f00000f0f0f0f0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f070f070f070f070f050f050f050f050f030f030f030f030f000ff00f000ff00f000f0f0f000f0f0f000f000ff00ff00f000f000f0f0f0f0f000f000f000ff00f000f000f000f000f000f00000000000f0000000f0000000efefeeeeefefeeeeefefaaaaefefaaaaefef0000ffff0000efef0000efef0000efeeefeeefeeefeeefe0efe0efe0efe0efaaefaaefaaefaaef00ef00ef00ef00eeffeeeeeeffeeeeeeffaaaaeeffaaaaeeff0000ffff0000eeff0000eeff0000eefeeefeeefeeefeeeeeeeeeffffeeeeeeeeeeeeffeeffeeeeeeeeeefefefefeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeeeaeaeeeeeaeaeeeee0e0eeeee0e0eeeececeeeeececeeeeecccceeeecccceeeeaeaeeeeeaeaeeeeeaaeeeeeeaaeeeeeeaaaaffffaaaaeeeeaaaaeeeeeeeeeeeeaaaaeeeeaaaaeeeeaaaacccc0000) else (if page < 24 then 0xf0f0f0f0fafafefef0f0f0f0fafafafaf0f0f0f0fafafaf0f0f0f0f0fafaf8f8f0f0f0f0fafaf2f2f0f0f0f0fafaf0faf0f0f0f0fafaf0f0f0f0f0f0fafaaaaaf0f0f0f0fafa5050f0f0f0f0fafa0000f0f0f0f0faf8faf8f0f0f0f0faf2faf2f0f0f0f0faf0fff0f0f0f0f0faf0fafaf0f0f0f0faf0faf0f0f0f0f0faf0f0f0f0f0f0f0faaafaaaf0f0f0f0fa50fa50f0f0f0f0fa00fa00f0f0f0f0f8faf8faf0f0f0f0f8f8fafaf0f0f0f0f8f8f8f8f0f0f0f0f8f8f0f0f0f0f0f0f8f0f8f0f0f0f0f0f2faf2faf0f0f0f0f2f2fafaf0f0f0f0f2f2f2f2f0f0f0f0f2f2f0f0f0f0f0f0f2f0f2f0f0f0f0f0f0fff0faf0f0f0f0f0fff0f0f0f0f0f0f0fff000f0f0f0f0f0ff0000f0f0f0f0f0fef0fef0f0f0f0f0fafafaf0f0f0f0f0faf0faf0f0f0f0f0faf0f0f0f0f0f0f0f8f0f8f0f0f0f0f0f3f0f0f0f0f0f0f0f2f0f2f0f0f0f0f0f0fffaf0f0f0f0f0f0fff0f0f0f0f0f0f0ff00f0f0f0f0f0f0fefef0f0f0f0f0f0fcfcf0f0f0f0f0f0fafaf0f0f0f0f0f0faf0f0f0f0f0f0f0f8f8f0f0f0f0f0f0f3f0f0f0f0f0f0f0f2f2f0f0f0f0f0f0f0faf0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f070707070f0f0f0f05050f0f0f0f0f0f050505050f0f0f0f030303030f0f0f0f010101010f0f0f0f000f000f0f0f0f0f00000f0f0f0f0f0f000000000 else (if page < 25 then 0xf5f5f5f500000000f5f50000f5f50000f5f0f5f0f5f0f5f0f5a0f5a0f5a0f5a0f5550000f5550000f500f500f500f500f3f3f0f0f3f3f0f0f3f30000f3f30000f3f0f3f0f3f0f3f0f300f300f300f300f2f2f2f2f2f2f2f2f2f0f2f0fafafafaf2f0f2f0faf0faf0f2f0f2f0f2f2f2f2f2f0f2f0f2f0f2f0f2f0f0f0f2f0f0f0f0ffffff00000000f0fff0fff0f0f0f0f0fff0ff00000000f0fff0f0f0fff0f0f0ff0000ffff0000f0ff0000f0ff0000f0faf0faf0faf0faf0f8f0f8fafafafaf0f8f0f8f8f8f8f8f0f8f0f8f0faf0faf0f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f1f0f0f0f1f0f0f0f0ffff00000000f0f0fefefefefefef0f0fefef0f0fefef0f0fcfcf0f0fefef0f0fcfcf0f0fcfcf0f0fafafcfcfefef0f0fafafafafafaf0f0fafaf0f0fafaf0f0fafaf0f0f0f0f0f0faf0fafafafaf0f0faf0faf0faf0f0f0faf0f0f0faf0f0f0f8f8fafafafaf0f0f8f8f8f8f8f8f0f0f2f2fafafafaf0f0f2f2f2f2f2f2f0f0f2f2f0f0f2f2f0f0f0fff0f0f0f0f0f0f0ff00000000f0f0f0fcf0f0f0fcf0f0f0fafafafafaf0f0f0faf0faf0faf0f0f0faf0f0f0faf0f0f0f0fffff0f0f0f0f0f0fff0fff0f0f0f0f0fefefefef0f0f0f0fefefafaf0f0f0f0fefef0f0f0f0f0f0fefafefaf0f0f0f0fef0fef0f0f0f0f0fcfcfcfcf0f0f0f0fafffafaf0f0f0f0fafff0f0f0f0f0f0fafefafef0f0f0f0fafafffa else 0xfaf0faf0fafafafafaf0faf0fafafaf0faf0faf0faf8faf8faf0faf0faf2faf2faf0faf0faf0fff0faf0faf0faf0fafafaf0faf0faf0faf0faf0faf0faf0f0f0faf0faf0faf0aa00faf0faf0faf00000faf0faf0f0f0f0f0faf0fa50faf0fa50faf0fa00faf0fa00faf0f8f0faf0f8f0faf0f2f0faf0f2f0faf0f0f0fafafafafaf0f0f0fafaf0f0faf0f0f0faf0faf0faf0f0f0faf0f0f0faf0f0f0f0f0f0f0faf0ba30faf0ba30faf050f0faf050f0faf05050faf05050faf03230faf03230faf00000faf00000faeafaeafaeafaeafacafacafacafacafaaafaaafaaafaaafa70fa70fa70fa70fa5afa5afa5afa5afa0afa0afa0afa0afa00fa00fa00fa00f8f8fafafafafafaf8f8fafaf8f8fafaf8f8f8f8fafafafaf8f8f8f8fafaf8f8f8f8f8f8faf8faf8f8f8f8f8f8faf8faf8f8f8f8f8f8fafaf8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f8f8f8f88888f8f8f8f8f8f80000f8f8f8f0f8f8f8f0f8f8f888f8f8f888f8f8f800f8f8f800f8f8f0f8f8f8f0f8f8f8f0f0fafafafaf8f8f0f0fafaf0f0f8f8f0f0f8f8f8f8f8f8f0f0f8f8f0f0f8f8f0f0f0f0f0f0f8f8b8b8f8f8b8b8f8f87070f8f87070f8f83030f8f83030f8f80000ffff0000f8f80000f8f80000f8f0f8f0fafafafaf8f0f8f0faf0faf0f8f0f8f0f8f8f8f8f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f870f870f870f870f800f800f800f800)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0xfefcfefcfefcfefcfefc0000fefc0000fef8fef8fef8fef8fef0fef0fefefefefef0fef0fef0fef0fef0faf0fef0faf0fef0f0f0fef0f0f0feeefeeefeeefeeefeee0000feee0000feccfeccfeccfeccfeaafeaafeaafeaafe0efe0efe0efe0efe00fe00ff00ff00fe00fe00fe00fe00fcfcffff00000000fcfcfcfcfefefefefcfcfcfcfcfcfcfcfcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcfcccfcfcfcccfcfcfc00fcfcfc00fcfcf0f0fcfcf0f0fcfcdcdcfcfcdcdcfcfc5454fcfc5454fcfc3c3cfcfc3c3cfcfc1414fcfc1414fcfc0000ffff0000fcfc0000fefe0000fcfc0000fcfc0000fcf8fcf8fcf8fcf8fcf0fcf0fef0fef0fcf0fcf0fcf0fcf0fcecfcecfcecfcecfce8fce8fce8fce8fcccfcfcfcccfcfcfcccfcccfcfcfcfcfcccfcccfcccffccfcccfcccfcccfcccfcccfcccccccccccfcccccccfcccccccfcc0fcc0fcc0fcc0fc3cfc3cfc3cfc3cfc00fc00fc00fc00fafaffff00000000fafafafafafafafafafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000ffff0000fafa0000fafa0000faf8faf8fafafafafaf8faf8faf8faf8faf8faf0faf8faf0faf8f8f8faf8f8f8faf8f0f0faf8f0f0faf0fafafafafafafaf0fafafaf0fafafaf0fafaf0f0fafafaf0faf0fefcfefcfaf0faf0fef0fef0 else 0xff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00ff00ff00ff00af00ff00ff00ff00aaaaff00ff00ff00aa00ff00ff00ff008800ff00ff00ff005500ff00ff00ff003f00ff00ff00ff003300ff00ff00ff000f00ff00ff00ff000a00ff00ff00ff000300ff00ff00ff000000ff00ff00f000f000ff00ff00aa00aa00ff00ff0055005500ff00ff000f000f00ff00ff0000ff0000ff00ff000000ff00ff00ff0000000000ff00fe00ff00fe00ff00f000ff00f000ff00ee00ff00ee00ff00af00ff00af00ff00aaaaff00aaaaff00aa00ffffaaaaff00aa00ff00ff00ff00aa00ff00aa00ff00aa00ff000000ff00aa00aa00aa00ff008800ff008800ff005500ff005500ff003f00ff003f00ff000ff0ff000ff0ff000f00ff00ff00ff000f00ff000f00ff000f00ff000000ff000f000f000f00ff000a00ff000a00ff000300ff000300ff0000ffffff0000ff0000ffff00ff00ff0000ffff000000ff000000ffffff00ff000000ffff0000ff000000ffaaaaaaff000000ffaa0000ff000000ff0f0000ff000000ff00ff00ff000000ff00aa00ff000000ff000f00ff000000ff000000ff000000aa000000ff0000000f000000ff0000000000ff00ff00000000000000feff0000feff0000fefefefefefefefefefefefe00000000fefeeeeefefeeeeefefeaaaafefeaaaafefe0000ffff0000fefe0000fefe0000) else (if page < 29 then 0xff880000ff880000ff80ff80ff80ff80ff55ff5500000000ff55ff00ff55ff00ff55aa00ff55aa00ff550000ff550000ff50ff50ff50ff50ff40ff40ff40ff40ff3fff00ff3fff00ff3f0000ff3f0000ff3cff3cff3cff3cff30ff30ff30ff30ff2aff2aff2aff2aff22ff22ff22ff22ff0fff0fff0fff00ff0fff0fff0f0000ff0fff0f00000000ff0fff0aff0fff0aff0fff00ffffff00ff0fff00ff0fff00ff0fff00ff00ff00ff0ff000ff0ff000ff0faa0aff0faa0aff0f0f0fff000000ff0f00f0ff0f00f0ff0f0000ffff0000ff0f0000ff0f0000ff0f0000ff000000ff0f00000f0f0000ff0f000000000000ff0eff0eff0eff0eff0aff0affaaffaaff0aff0aff0aff0aff0aff00ff0aff00ff0a0a0aff0a0a0aff0a0000ff0a0000ff08ff08ff08ff08ff03ff00ff03ff00ff030000ff030000ff02ff02ff02ff02ff01ff00ff01ff00ff00ffffffffff00ff00ffffffff0000ff00ffffff00ff00ff00ffffff000000ff00ffff00000000ff00fff0ff00fff0ff00ffaaffaaffaaff00ff00ffffffaaff00ff00ffffff00ff00ff00ffff0000ff00ff00ffeeffeeff00ff00ffaaffaaff00ff00ffaaff00ff00ff00ff88ff88ff00ff00ff0fff00ff00ff00ff0aff0aff00ff00ff00fff0ff00ff00ff00ffeeff00ff00ff00ffccff00ff00ff00ffaaff00ff00ff00ff88ff00ff00ff00ff0aff00ff00ff00ff00 else 0xffeeffaaffeeffaaffeeff00ffeeff00ffeeeeeeffeeeeeeffeeaaaaffeeaaaaffee0000ffff0000ffee0000ffee0000ffee0000ffaa0000ffee0000ff000000ffeaffeaffeaffeaffea0000ffea0000ffccffccffccffccffccffcc00000000ffcc0000ffcc0000ffc8ffc8ffc8ffc8ffc0ffc0ffccffccffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffc0ff00ff00ff00ffc0c0c0ffc0c0c0ffc00000ffc00000ffafffaaffafffaaffafff00ffafff00ffafaaaaffafaaaaffaf0000ffaf0000ffaeffaeffaeffaeffaaffaaffffffaaffaaffaaffeeffeeffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaaaaaaaaaffaaffaa00000000ffaaff88ffaaff88ffaaff0affaaff0affaaff00ffffff00ffaaff00ffaaffaaffaaff00ffaaff00ffaaff00ff00ff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaafaaffaaafaaffaaaaaaffffaaaaffaaaaaaffaaffaaffaaaaaaffaaaaaaffaaaaaaff000000ffaaaaaaaaaaaaaaffaa5500ffaa5500ffaa0f0affaa0f0affaa00aaffaa00aaffaa0000ffff0000ffaa0000ffaaffaaffaa0000ffaa0000ffaa0000ff000000ffaa0000aaaa0000ffaa000000000000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ff8aff8aff8aff8aff88ff88ffaaffaaff88ff88ff88ff88ff88ff00ff88ff00ff88ff00ff00ff00ff888888ff888888)) else (if page < 32 then (if page < 31 then 0xffff0000ffffff00ffff0000ffffeeeeffff0000ffffaaaaffff0000ffffaa00ffff0000ffff8888ffff0000ffff0f00ffff0000ffff0a0affff0000ffff00aaffff0000ffff0000ffff0000ffee0000ffff0000ffaf0000ffff0000ffaa00aaffff0000ffaa0000ffff0000ff880000ffff0000ff550000ffff0000ff3f0000ffff0000ff0f0000ffff0000ff0a0000ffff0000ff030000ffff0000ff00ff00ffff0000ff000000ffff0000fefe0000ffff0000f0f00000ffff0000eeee0000ffff0000afaf0000ffff0000aaff0000ffff0000aaaaaaaaffff0000aaaa0000ffff0000aa000000ffff000088880000ffff000055550000ffff00003f3f0000ffff00000fff0000ffff00000f0ff0f0ffff00000f0f0000ffff00000f000000ffff00000a0a0000ffff000003030000ffff000000ffff00ffff000000ff0000ffff000000aa0000ffff0000000f0000ffff00000000ff00ffff00000000aaaaffff000000000000fffefffefffefffefffe0000fffe0000fffcfffcfffcfffcfffc0000fffc0000fffafffafffafffafffa0000fffa0000fff8fff8fff8fff8fff80000fff80000fff0fff0fffafffafff0fff0fff0fff0fff0fff000000000fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff00f00fff00f00fff00000fff00000ffef0000ffef0000ffeeffeeffeeffeeffeeffee00000000 else 0xffffaa00aa000000ffffa8a8ffffa8a8ffff8a8affff8a8affff88aaffff88aaffff8888ffffaaaaffff8888ffff8888ffff8888ffff0000ffff888888888888ffff8800ffff8800ffff8080ffff8080ffff5555ffff0000ffff5555aaaa0000ffff555500000000ffff5500ffff5500ffff5500ffff0000ffff3f3fffff0000ffff3f00ffff3f00ffff3333ffff0000ffff3300ffff3300ffff3300ffff0000ffff3030ffff3030ffff2a2affff2a2affff1111ffff0000ffff0fffffff0000ffff0f0fffff0f00ffff0f0fffff0a0affff0f0fffff0000ffff0f0fff000f00ffff0f0ff0f00000ffff0f0faaaa0a0affff0f0f00000000ffff0f0affff0f0affff0f00ffffff00ffff0f00ffff0f00ffff0f00ffff0000ffff0f000f000f00ffff0f000f000000ffff0e0effff0e0effff0aaaffff0aaaffff0a0affffaaaaffff0a0affff0a0affff0a0affff0000ffff0a0a0a0a0a0affff0a00ffff0a00ffff0808ffff0808ffff0505ffff0000ffff0303ffff0000ffff0300ffff0300ffff0202ffff0202ffff00ffffff00aaffff00ffffff0000ffff00ffff00ff00ffff00ffff000000ffff00ffaaaa00aaffff00ff00000000ffff00eeffff00eeffff00aaffffaaaaffff00aaffff00aaffff00aaffff0000ffff00aa00aa00aaffff0088ffff0088ffff000fffff0000ffff000affff000affff0000ffffffaa) else (if page < 33 then 0xffffff00ffffff00ffffff00ffffaa00ffffff00ffff0f00ffffff00ffff0000ffffff00ffaaff00ffffff00ff0fff00ffffff00ff00ff00ffffff00ff000000ffffff0000ff0000ffffff000000ff00ffffff0000000000fffffefefffffefefffffcfcfffffcfcfffffafafffffafafffffaf0fffffaf0fffff8f8fffff8f8fffff0f0fffffafafffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f00f0f0000fffff0f000000000fffff000fffff000fffff000ffff0000ffffeeeeffffeeeeffffeeeeffffaaaaffffeeeeffff0000ffffeeeeeeeeeeeeffffeeaaffffeeaaffffee00ffffee00ffffeaeaffffeaeaffffccccffffccccffffc0c0ffffc0c0ffffafafffffaaaaffffafafffff0000ffffafaaffffafaaffffaf00ffffaf00ffffaeaeffffaeaeffffaaffffffaaaaffffaaffffff0000ffffaaeeffffaaeeffffaaaaffffffaaffffaaaaffffeeeeffffaaaaffffaaaaffffaaaaffffaa00ffffaaaaffff8888ffffaaaaffff0a0affffaaaaffff00aaffffaaaaffff0000ffffaaaaffaaaaaaffffaaaaff00aa00ffffaaaaeeeeaaaaffffaaaacccc8888ffffaaaaafafaaaaffffaaaaaaffaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaa88ffffaa88ffffaa0affffaa0affffaa00ffffff00ffffaa00ffffaaaaffffaa00ffffaa00ffffaa00ffff0000ffffaa00aa00aa00 else (if page < 34 then 0xffffffffee000000ffffffffccccccccffffffffaf000000ffffffffaaaaaaaaffffffffaaaaaa00ffffffffaaaa0a0affffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffff88888888ffffffff88000000ffffffff55550000ffffffff55000000ffffffff3f000000ffffffff15150000ffffffff11110000ffffffff0f0f0f00ffffffff0f0f0000ffffffff0f030000ffffffff0f000f00ffffffff0f000000ffffffff0a0a0a0affffffff0a000000ffffffff07070000ffffffff05050000ffffffff03030000ffffffff03000000ffffffff02020000ffffffff01010000ffffffff01000100ffffffff00ff0000ffffffff00f000f0ffffffff00aa00aaffffffff00030000ffffffff00020002ffffffff0000ff00ffffffff0000f0f0ffffffff0000aaaaffffffff000000f0ffffffff000000eeffffffff000000ccffffffff000000aaffffffff00000088ffffffff0000000affffffff00000000fffffff0fffffff0fffffff000000000ffffffeeffffffeeffffffccffffffccffffffcc00000000ffffffaaffffffaaffffffaaffffff00ffffffaaffffaaaaffffffaaffff0000ffffffaaffaaffaaffffffaa00000000ffffff88ffffff88ffffff5500000000ffffff3300000000ffffff0fffffff00ffffff0fffff0000ffffff0f00000000ffffff0affffff0affffff00ffffffaa else 0xffffffffffffffaaffffffffffffff00fffffffffffff0f0ffffffffffffeeeeffffffffffffccccffffffffffffaaaaffffffffffffaa00ffffffffffff8888ffffffffffff0f00ffffffffffff0a0affffffffffff00aaffffffffffff0000ffffffffffaaffaaffffffffffaaaaaaffffffffff030000ffffffffff00ff00ffffffffff000000fffffffffafafafafffffffff0f0f0f0fffffffff0f00000fffffffff0000000ffffffffeeeeeeee)))))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x6f25cc4d63e67936f26af5438537b76b252a else 0
  | 4 => if page < 3 then (if page < 1 then 0x8537b77006af4518537006af53042f8537767006af42f8537b770069c42f8537b77006a65438537b77006581978537b77006a55438537b770054328b8537b77006ae5437936f26584f342f8537b77006aa5438537b77006a75438537b770069d5438537b770065847f8537b77006af5488537b77006af5328537b77006af5718537b77006af1838537b76af5430f38537b76f26af5438537b770054311d8537b77006ad5438537b770059312e8537b77006af54088a7937006af5437b77006af54306f8537ab7006af5438537b770054311c8537b77006a95438537b770059312d8537b77006af53d8857b77006af5438537006af5430e58667b77006af5438537006af6a35438537b77006af5498537b77006af5317b770065859306485378f7006af5438537b770059312a8537b77006af52e8537b77006bd5938537b77006af1118717b77006af5438537006af5435308537b77006b05438537b77006a45437b77006af5430618537767006af5438537b77005431168537b770069c5438537b77006bf5438537b77006581287b77006af5430528537006c06af5438537b76af5430d88537b76b26af5438537b77006c552a8537b77006af5338537b77006af2697936f25cc4f325a8537b77006af5358537b77006af4528537b77006af543 else (if page < 2 then 0x8387005cc4f33ed8857005cc4d93ed8387004f342f1ef8356f24f342f1ef8387005cc4f33ea8356f25cc4f33ea8536f25cc4d83ea8537005bc4d83ea7ab6f25cc4f342f70d5cc4f342f0dd6f25cc4f342f0d98385cc4f342f0dd8387005cc4f342f7936f25fe4f342f7936f25cc4f33ab85378d70069d42f8537b77006a857179c6f25cc4f342f6f25cc4f345d42f7936f25cc4f342f7a36f25cc4f342f6f25cc4f342f2337936f26794f342f8537b778669842f7936f25cc4f31768537b77006af5448537b77006af5476f25cc4f342f08a8537b77006af5458537b77006af5468537b77006af56f79a6f25cc4f342f6f25cc5744f342f8537b77006a05718537b770059312c8537b77006af54c8537b77006af5378537b77006af5388537b77006af5708537b77006af5728537b77006af56e8537b77006af4538537b77006af4558537006af69157a85378f7006915938537b77006ac5488537b77006a045a8537b77006af53c8537b77006914758537b77006af5428537b77006af5418537b77006af5367936f25cc5932ec8537b77006af53f8537b77006af53e8537b77006af5398537b77006af4548537b77006af53b8537b770059331b8537b76b25272ec8537b77005931b38537b77005931b48537b776e6af42f8537b77006af534 else 0x8537b770054411d8537b77006ae5417936f24f342f20f7936f25cc4f342c7936f24f342f1eb7936f25cc4f33e68386f24f342f1eb8386f25cc4f33e67db6f25cc4f342f7ff6f25cc4f342f7936f26784f342f7936f25cc4f31777936f24f342f20d7936f25cc4f34278386f24f342f2077936f242f2812077936f25d24f342f7936f25cc4f34218386f25cc4f341a7936f24f341a2077936f25cc4eb41a7937005ca4eb41a7936f24f342f2077936f25cc4f341a7936f24f342f1ec7936f25cc4f33e78385cc4f342f0f38387004f342f2078387005cc4f341a8387004f342f1ec8387005cc4f33e788a7005cc4d73e77936f261c4f342f7936f25cc4f339f7ab6f24f342f2077ab6f25cc4f341a8356f24f342f1f27936f24f342f1f28537b770054a11c8356f25cc4f33ed8536f25cc4d93ed7936f25cc4f33ed8537b77006aa53e70d4f342f2070dd70d5cc4f341a0dd6f24f342f2070d96f25cc4f341a0d97155cc4f342f0f37936f25d64f342f7936f25cc4f341d7005cc4f342f0da7936f24f342f1ef7936f25cc4f33ea8385cc4f342f0d98387004f342f1eb8387005cc4f33e68386f25cc4f342f8387004f342f1f2)) else 0
  | 5 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x8537005cc4f325a0e58537b77006044f325a8537b77005cc4ca25a8537b77005cc4f32628537b77005cc4f324e8537b770069e4f325a8537b77005cc2a81768537b77006634f342f8537b77005cc4f31618537b77005fe4f325a8537b77005cc4d525a8537b77006794f325a8537b77005cc4bf25a8537b77005cc5292ec8537b77004f34ae42f8537b77006af4ae42f8537b77005cc5291318537b77006af4b242f8537b77005ea4f342f8537b77005cc5931308537b770064d4f342f8537b77387006af42f8537b77005cc59309c8537b77006254f342f8537b77006434f342f8537b77006585931318537b77005cc55230a8537b77005cc2ec2cc8537b77006af5432d48537b77005cc4f32cb8537b77006584f325a8537b77005cc4f33c88537b77005cc4f32608537b77005cc4f33638537b77005cc4f32678537b77005fe4f342f8537b77005e54f342f8537b77005cc4f33e18537b77006794f342f8537b77006314f342f8537b77005cc4f330f8537b77005cc4f342f8537b77005cc55014d8537b77005cc4f33ab8537b77005cc51414d8537b77005cc4f31768537b77005cc55214d8537b770069155242f8537b77004f342f2878537b770069155214d8537b77006af42f2998537b77005cc5932e28537b77707006af42f8537b77005cc5930b18537b77006af54342f8537b77006585932ec0008537b77006af5438537b77006af4b725a8537b77005cc5931318537b77006af42f2878537b77004b742f2878537b77005cc5932ec8537b77006584f342f8537b77005cc4f325a else 0x8537b770069155237b8537b77757006af5438537b77006af5431a38537b77006915520c18537b77006915523458537b77006af5935438537b77006af54314d8537b77006915521098537b770069155233488a8537b77006af5438537b77006af5430668537b77937006af54385383f7b77006af5438537b77006af5430dd8537b77006af5430568537b77006cb6af5438538337b77006af5438537b77006af5431188537b770065859304d8537b77006af6a15438537b77907006af5438537b77006af5431138537b77006585930d58537b77006af6935438538217b77006af5438537b770065859312b8537b77006af5430488537b77006af54352f8537b77777006af5438537b77006585931298537b77006af5430d18537b77006af54352b8537b77006c56af5438537b77006585931278537b77006af5431098537b77006af54352a8537b77005cc4ce25a8537b77004f32cd1768537b77004f328725a8537b77006af28725a8537b77004b728725a8537b77006af29925a8537b77005cc4f32618537b77006af4b525a8537b770064a4f342f8537b77707006af25a8537b77005932cd0b18537b77005cc4f32698537b77006414f342f8537b77006af54325a8537b75cc4f325a0f38537b76f25cc4f325a8537b77004f325a2078537b77005cc4eb25a8537b77004f342f3188537b77005cc4f325788a7937005cc4f325a7b77005cc4f325a06f8537ab7005cc4f325a8537b77004f325a1f28537b77005cc4d925a8537b77004f342f3168537b77005cc4f32548857b77005cc4f325a) else (if page < 3 then 0x8537b77006584f33ab8537b77006af54337b8537b77005cc55236d8537b77647006af5438537b77006585931a38537b77006af5430c18537b77006af5433458537b77006584f31768537b770065859314d8537b77006af5432ec8537b77005434f32878537b77006af5432878537b77005434b728785381f7b77006af5438537b77006af5432998537b770065859302c8537b77006585932e28537b77707006af5438537b77006af54328f8537b77006585930b18537b77006585932da8537b76584f342f0f38537b76f26584f342f8537b77004f342f12e8537b77006554f342f8537b770055242f2078537b77006584f341a88a7937006584f342f7b77006584f342f06f8537ab7006584f342f8537b77004f342f12d8537b77006524f342f8537b770055242f1f28537b77006584f33ed8857b77006584f342f8537006584f342f0e58687b77006584f342f8537006586484f342f8537b770065850242f8537b77006584f33917b77005cc5434f306185378b7006584f342f8537b77005434f31b98537b77006584f33748537b770069e55242f8537b77006584f310e8537b770065d4f342f8537b77006494f342f8537b77006584ff42f8537b77005cc5523ab8537b770068d55242f8537b77005cc5521578537b770065851542f8537b77005cc55235c8537b77006884f342f8537b77005cc4f31838537b770067955242f8537b77005cc5521768537b770065851742f8537b77006914f33348537b770065855242f8538207b77006af5438537b77006af5431c48537b770069155203c else 0x8537b77435cc5930d58537b77706af69342f8537b77005cc5931b58537b77004f342f1f28537b77005cc4f33998537b77004f342f1de8537b77005cc4f33c38727b77005cc4f342f8537005cc4f342f3028537b77005cc5612ec8537b77006255932ec8537b77005ae5932ec8537b77006624f342f8537b77006af69442f8537b77005cc5610b18537b77367006af42f8557b77005cc4f342f8537b07005cc4f342f8537b77005da4f342f8537b77005cc4f33ff8537b77005cc4f33fc8537b77005cc5930b08537b77006244f342f8537b77005cc4f33648537b77435cc5930b18537b77006af45242f8537b77006255930b18537b770069151442f0008537b77006af4528537b77005ae5930b18537b77005cc51435c8537b77004b742f28b8537b75cc4f342f2a38537b77006435932ec8537b77006af4b72678537b77465cc4f31768537b77005e84f342f8537b77005cc4f33ca8537b77005cc4f33bc8757b77005cc4f342f8537005cc4f342f2a58537b77006424f342f8537b77005cc4f32688537b77005cc4f317d8537b77005cc54f1768537b77005cc2a91768687b77005cc4f342f8537005cc5304f342f8537b77005cc4f33917b77005cc4f342f0618537767005cc4f342f8537b77005cc4f33748537b77005cc4f310e8537b77005cc59312b8537b77006af52f42f8537b77777006af42f8537b77006af42f0d18537b77005cc5931278537b77006af52a42f8537b77006585931948537b77006af5433348538147b77006af5438537b77006585931c48537b77006af54303c)) else (if page < 6 then (if page < 5 then 0x8537b77005cc4f34258537b77005cc4f34278537006af4c542f2997b77005cc5932cf04d8537006af6a142f2998537b77005cc5932f48537b77006af42f2858537b77004f342f2078537b77005cc4f33a68537b77004f342f1df8537b77005cc4f33c68537b77005cc5932e68537b77006af42f2978537b77377006af42f8537b77004f342f1b48537b77005cc4f33618537b77005cc5932f38537b77006af4b342f8537b77005cc57e2ec8537b77005ea5932ec8537b77005ba5932ec8537005cc4ca42f2998537b77025cc4f342f8537b76f75cc4f342f8537b77005d04f342f8537b77005cc4f34248537b77005cc4f34218537b77005cc50b3ab8537b77005cc4d03ab8537b77004b742f2897b77005cc4f342f2a28537b770064d5932ec8537b77006af4b72608537b77004f342f2898537b77006af42f2898537b77004b642f2898537b77006af42f29a8537b77005e94f342f8537b77005cc4f33c98537b77005cc4f33b08537b77005cc5932e18537b77415cc4f342f8537b75cc4f342f2918537b770064c4f342f8537b77005cc4f32638537006af4b542f2998537b776f7006af42f8537b77006af53542f8537b770064d5932e28537b770069155042f0008537b77006af5358537b77006af4b62608537b77005cc5511577b77005cc4f342f0718537b27005cc4f342f8537b77004f342f1fc8537b77005cc4f34008537b77005cc4f34058537b77005cc59336d8537b77466914f30c18537b77006af42f0ad8537b776c7006af42f8537b77006af42f0ac8537b77006af69542f else 0x8537b77006af42f2a18537b77005cc5932eb8537b77005cc5932f78537b77005cc5932e388a7937005cc5932ec7b77005cc5932ec06f8537ab7005cc5932ec8537b77005932ec1f28537b77005bd5932ec8537b77004b742f11c8537b77005cc58a2ec8537b77006af42f2a08537b77005cc5932ea8537b77005cc5932f68537b77005cc5932e78857b77005cc5932ec8537005cc5932ec0e58537b776d7006af42f8537b77005cc5930b38537b77006af42f29d8537b77005cc5932e98537b77005cc5942ec8537b77005cc57c2ec8537b77005cc5932f58537b77005cc5932e88537b77006af53a42f8537b77005cc5931338537b77004b742f1168537b77005cc56d2ec8537b77005cc5933138537b77005cc5932d78537b77005cc5933008537b77005cc5932df8537b77006b85cc2ec8537b77005cc2ec1978537b77006af52d42f8537b77005cc5931368537b77006af42f29f8707b77005cc5932ec8537005cc59357a2ec8537b77005cc59331e8537b77006095932ec8537b77005b75932ec7b77005cc5932ec06485377a7005cc5932ec8537b77005932ec1be8537b77005b15932ec8537b77006af42f2968537b77005cc59331c8537b77006bb5932ec8537b77006af4b710e7b77005cc5932ec0528537006c05cc5932ec8537b75cc5932ec0d88537b76b25cc5932ec8537b77006af42f28c8537b77005cc59331a8537b77006c55272ec8537b77005cc59331d8537b77357006af42f8537b77006af4af42f8537b75cc4f342f0f58537b76f95cc4f342f8537b77004f342f20b) else (if page < 7 then 0x8537b77006094f342f8537b77004f342f1be8537b77006bb4f342f7b77005cc4f342f0528537006c05cc4f342f8537b75cc4f342f0d88537b76b25cc4f342f8537b770063559314d8537b770059e4f342f8537b77006915931098647b77005cc4f342f8537005cc5a14f342f85d7b77005cc4f342f8537827005cc4f342f8537b77006354f33348537b77005cc52914d8537b77005cc4f33218537b77004f342f3198537b77006564f342f8537b77005cc5912ec8537b77006574f342f8537b77005cc4f325b8537b770064e4f342f8537b77005cc4f325f7936f25cc4f342f2ec8537b77006154f342f8537b77005cc4f33c58537b77005cc4f339f8537b77004f342f3178537b77006534f342f8537b77005cc58b2ec8537b77006544f342f8537b77005cc4f325c8537b77006444f342f8537b77005cc4f32668537b77005cc4f316d8537b77006514f342f8537b77005cc4f325e8537b77006274f342f8537b77005cc4f33608537b77005cc5852ec8537b77004f349242f8537b77005cc5712ec8537b77005cc47f2ec8537b77005cc4f325d8537b770064b4f342f8537b77005cc42f2868537b77005cc4f31658537b77005cc4f326a8537b77005cc47542f8537b77005cc4f32428537b77006af42f29b8537b77005fe5932ec8537b77005b85932ec8537b77006af51942f8537b77006795932ec8537b77006af4b71768537b77006af4c042f8537b75cc5932ec0f38537b76f25cc5932ec8537b77005932ec2078537b77005ca5932ec8537b77004b742f11d8537b77005cc5902ec else 0x8537b770050a42f1c48537b77006124f337b8537b77005cc5103e18537b77005cc50c3d68537b77006124f33d68537005cc4f349a42f8537b77005cc55414d8537b77005f94f342f8537b77005e44f342f8537b77005cc4f33e28537b77005cc5571428537b77005cc58f2f37b77005cc4f342f0708537ae7005cc4f342f8537b77004f342f2018537b77004f342f1f98537b77005cc4f33f78537b77005cc5933588537b77004f348742f8537b77004f342f1e68537b77005cc4f33da8537b77004f342f1d68537b77005cc4f33ed87d7b77005cc4f342f8537005cc4f342f1868537b77005cc57314d8537b77006654f342f8547b77005cc4f342f8537b57005cc4f342f8537b77005dc4f342f8537b77005d84f342f8537b77005cc4f34078537b77005cc57309e8537b77005cc51536d8537b75cc4f348a42f8537b771f6794f342f8537b77004f34a742f8537b77005f14f342f8537b77005e34f342f8537b77005cc4f33e38697b77005cc4f342f8537005cc4f34a942f8537b770066d4f342f8537b77006304f342f8537b77005cc4f33108537b770069842f1c48537b77006794f337b8537b778970069842f8537b77006794f30c18537b770067951642f8537b770051f42f1c48537b77006314f337b8537b778970051f42f8537b77006314f30c18537b77006985cc30f8537b77005cc56b2fe8537b77006314f32fe8667b77005cc4f342f8537005cc57a4f342f7b77005cc4f342f06485377a7005cc4f342f8537b77006af69159385370069163e4f337b8537b771f6914f30c1))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x8537b77006b44f342f8537b77005cc5930b28537b77005cc5930b48537b77006914f32fa8537b77006915140c18537006af68b4f342f8537b77006914f333585378f7006914f342f8537b77006914f33748537b77006914f33368537006a16914f337b8537b77006af6915818537b77006af56d42f8537b76914f30d70c18537b77006af69145a8537b77006af42f2458537b77006914f33328537b77727006af42f8537b77006914f30b68537b77006914f32428537b77005274f32428537b77006915931188537b77006af6915768537b77907006915938537b77006af6910d57936f25cc4f342f14d8537b770061c4f342f8537b77006134f342f8537b77005cc4f33dd8537b770067f4f342f8537b77006324f342f8537b77005cc4f330e8537b77006664f314d8537b77005cc55514d8537b77004e042f2898537b770069d5cc14d8537b77006624f30c18537005cc57a4f314d85377a7005cc4f314d8537b77005b14f314d8537b77005cc5931328537b77005931bb14d8537b77005cc5931408537b77006af52714d8537b75cc4f342f0f48537b76f45cc4f342f8537b77004f342f20d8537b77004f342f2098537b77005cc4f341f8537b77004f342f1e88537b77005cc4f33de8537b77004f342f1da8537b77005cc4f341a8537b77005cc5931347b770063f5fe4f342f8537b77004f342f2188537b77015cc4f342f8537b76fc5cc4f342f8537b77005d24f342f8537b77005ce4f342f8537b77005cc4f34298537b770051042f1c48537b770061b4f337b8537b77005fe4f942f else 0x7b77005cc4f342f0658537917005cc4f342f8627b77005cc4f342f8537006c65cc4f342f7b75cc4f342f0d80528536c05cc4f342f0d87b76b25cc4f342f0528536c06b25cc4f342f8537b76bb6b24f342f8537b770069842f1948537b76b24f342f1948537b76b25cc4f33348537b77004f342f2438537b77006794f33348537b770069155542f8537b770051242f1c48537b77006b642f1c47b77006c44f342f1c48537b76b24f342f1c48537b77006af42f29c8537b77005cc5932f88537b770069155442f8537b77006af54b1c48537b77006af42f2988537b77717006af42f8537b77006af54842f8537b770065d5932f30008537b77006af5488537b77006af4bb24e8537b77006af42f2868537b77004bb42f2868537d27005cc4f337b8537b77004f342f2228537b77006204f337b8537b77006bb4f337b7b77006c45cc4f337b7b77005cc4f340a0528537b76b25cc4f337b8537005cc5934c637b8537b77005cc5932e48537b77005cc5932e58537b77006734f342f8537b77005cc59336c8537b77006914f33338537b770069155037b8537b77006a059342f8537b77005cc59336e8537b77897006b642f8537b77896b24f342f8537b77005cc59336f8537837006914f337b8537b77897006af5718537b770069157342f8537b77006af42f22b8537b77005cc59336a8537b77006af57142f8537b770068859336d0008537b77006af5718537b77006af5b01618537b77006914f31658537b77005af4f31658537b77005cc42f1228537b77006bb4f30c18537b76b25cc4f30c1) else (if page < 11 then 0x8857005cc5764f342f7b77006ab5fe4f342f8537b77006074f342f8537b77005cc4f339388a7005cc5744f342f8707005cc5764f342f7b77005cc4f342f0628537787005cc4f342f8537b77004f342f1bc8537b77005cc4f33727b77005cc4f342f0738537b67005cc4f342f8537b77004f342f2028537b77005cc4f340985e7b77005cc4f342f85377b7005cc4f342f8537b77006234f342f8537b77005cc4f33757005cc4f342f09206477a7005cc4f342f06478077a7005cc4f342f7b77004f342f1be06485377a7004f342f1be7b77005b14f342f06485378f7005cc4f33748537b77006884f337485378d7004f342f1b98537b77004c442f1b98537b77004f342f1d18537b77005cc4f338e8657b77005cc4f342f8537005cc5994f342f8537b76985cc42f0d58877b77005cc4f342f8537005cc4f342f0d38587b77005cc4f342f8537ad7005cc4f342f8537b77005de4f342f8537b77005cc4f33f68537b75b14f342f0d58537b76935cc4f33748537b75cc4f342f1238537b77006054f342f8537b77005cc4f339587f7b77005cc4f342f8537005cc4f342f1258537b77006b94f342f8537b77005cc4f31108537b76b55cc4f30c18537b77006bb56b42f8537b770069e4f310e8537b770069e69842f7b77005cc4f342f06e8537aa7005cc4f342f8537b75cc4f342f0ef8537b76ea5cc4f342f8637b77005cc4f342f8537006c15cc4f342f8537b77175cc4f342f8537b76b35cc4f342f7005cc4f342f08b0527b77006094f342f0527006c05cc4f342f0527006c46c05cc4f342f else 0x8537b770069e4f32678537b77006985cc1768537b77005cc18e1768537b77006794f31768537b77005cc56b1768537b77004f32721768537b75cc4f342f2308567b77005cc4f342f8537af7005cc4f342f8537b770067956b0c18537b77006792a70c18537b772570069842f8537b77006794f30b88537b77004f342f2308537b77646794f30c18537b77005cc5932ed8537b77005cc5932f27936f25cc5934f342f88a7005cc4f342f08a8537b77006214f342f8537b77005cc4f338f8537b77005cc5932ee8537b77006bc4f342f8537b77005cc4f310d7b77005cc4f342f04f8537005cc5794f342f8537b77005cc5932f18537b77005cc59336b8537b77005cc5932ef7b77005cc4f342f04e8537005cc5784f342f8537b77005cc5932f08537b77005cc5933338537b77005cc5933068537b77005cc5932fa7b77005cc4f342f0518537006b75cc4f342f8537b77005cc5933318537b75cc4f342f0f78537b76fe5cc4f342f8537b77004f342f20e8537b77005cc4f342b8537b77004f342f1d28537b77005cc4f33908537d17004f342f1da8537e97004f342f1d28537d17005cc4f33907e97005cc4f342f04d7b76f25cc4f342f04d7b77005ca4f342f04d83c7005cc4f342f04d88a79a7005cc4f342f8537b77055cc4f342f8537b76f35cc4f342f8537b77005d44f342f8537b77005cc4f341e8537005cc4f344937b8537b77006094ff42f8537b770061e4f33918537b770060450242f7b77005cc4f342f11e8536f25cc5764f342f8537006a15cc4f341a85370068a4f342f207)) else (if page < 14 then (if page < 13 then 0x8537b770068856b42f8537b77006985cc1618537b77005cc4ff1768537b77005cc4ce1768537b77005e74f342f8537b77005cc4f33db8537b77004f32301768537b75cc4f32301768537b77005cc5001768537b77005cc4cc1768537b77005cc4f317f8817b77005cc4f31768537005cc4f32371768537b77006965cc1768537b77005cc18f1768537b770066a4f342f8537b77006981c41768537b77006985b31768537b77897006981768537b75cc4f31760f38537b76f25cc4f31768537b77004f32071768537b77005ca4f31768537b77005cc2811768537b77005cc4eb1768537b77004f348842f8537b77005cc4f317388a7937005cc4f31767b77005cc4f317606f8537ab7005cc4f31768537b77004f31f21768537b77005bd4f31768537b77005cc27b1768537b77005cc4d91768537b77005cc4f316b8857b77005cc4f31768537005cc4f31760e58537b77005cc5021768537b77005cc4ca1768537b77005cc4f31808537b77006044f31768537b77005b84f31768537b77005cc4f317e8537b77005cc4f31698537b770069e4f31768537b77005cc47e42f8537b77005fe4f31768537b77005be4f31768537b77005cc4fa1768537b77005cc4d41768537b77005cc5161768537b77005cc4bf1768537b77005cc5141768537b77005cc4c31768537b77005cc47f1368537b77005ae4f31768537b770067956b42f8537b77005cc51f1768537b77005cc3111768537b77006794f32fe8537b77005cc4f326c8537b77005cc47442f8537b77005cc42f28a8537b770067954f42f else 0x8537006985cc42f2378537b770067956942f8537b77006985cc17d8537b77006986641c48537b770067956b37b8537b777570069e5658537b76794f342f0f38537b76f26794f342f8537b77004f342f1218537b77006764f342f8537b770056b42f2078537b770069e4f341a8537b770069842f2078537b77006794f341a8537b770069e50542f8537b77006794f338088a7937006794f342f7b77006794f342f06f8537ab7006794f342f8537b77004f342f1208537b770056b42f1f28537b770069e4f33ed8537b770069842f1f28537b77006794f33ed8537b770069e50442f8537b77006794f338c8857b77006794f342f8537006794f342f0e58537b778570069842f8537b77006794f30c88537b77006644f31e48537b77005cc56b4058537b770067950342f8537b770069e4f33948537b770069e50242f8537b77006794f33888537b770069e51a42f8537b770069842f1e48537b77006794f33d68537b77006814f342f8537b77006684f342f8537b770069e4ff42f8537b77005cc56b3ab8537b770069e52242f8537b77005cc4f31968537b770069e56b42f7b77006985cc42f0518537006be6794f342f8537b76b26794f342f8537b77006794f33748537b77006b85cc3318537b77005cc56b1618537b77006794f33878537b770069842f1bf8537b772c70069842f8537b77006694f342f8537b77006794ff42f8537b77006985cc3ab8537b770069842f1cd8537b77006794f33768537006985b342f1c48537b778770069842f8537b770069842f0a48537b778370069842f) else (if page < 15 then 0x8537b77005cc4f342c88a7a37005cc4f342f8787b76f25cc4f342f8858027005cc4f342f8536f25cc4f342f2368537005ca4f342f2368857005cc4f342f2368537b75cc4f342f0f38537b77004f342f1dd8537b77005cc4f33b98537b77005cc4f33f088a7005cc4f342f2337b77005cc4f342f06f8537ab7005cc4f342f8537b77006464f342f8537b77005cc4f32648537b77004f342f21f8537b76f55cc4f342f8537b77005d14f342f8537b77005cc4f34228537b77005cc4f341d8537b77005f14fc42f8537b770050e42f1c48537b77006174f337b8537b77005cc50e3bc8537b77005cc4cc3bc8537b77006174f338c7b77005cc4f342f23f8788017005cc4f342f8537b77005cc4f33ea8538287004f342f1c48538017005cc4f33ea8777b77005cc4f342f8537b77005f04f342f8537b77005cc4f33bd8537005cc4f342f2378537b770066c4f342f8537b77005cc4f31818817005cc4f342f2368777b770066d4f342f8537006975cc42f2378537b770066d56942f8537b770069742f1c48537b77006754f337b8538287005cc4f317d8537005cc4f323717d8537b77006975cc17d8537b77005cc18f17d8537b77006754f30c886b7b77005cc4f342f8537005cc4f346142f8537b77006064f342f8537b77005cc4f33948537b77005cc56b3d68537b770067950242f8537b770069e4f33ab8537b77006794f33ab8537b772a70069842f8537b770069842f2308537b76985cc42f2308537006985b342f2368537b77006794fc42f8537b77006985cc3bc8777b77006794f342f else (if page < 16 then 0x8537b77005cc4f335f8427257005cc4f342f85373a7005cc4f33ed8607af7005cc4f342f8537b77035cc4f342f8537b77005cd4f342f8537b77005cc4f342d8537b170b5cc4f342f8537b87005dc4f342f8537b17005dc4f342f8537b77005dc4f742f8597b77005cc4f33fc8427b77005cc4f33fc8537b77005cc5073fc8537b77005cc4db3fc8567b77005cc4f33ed8467b77005cc4f33ed8537b770060c4f33ed8537b77005cc4dc3ed8537277005cc4f342f8537b770067f4f30c18537b77005db4f342f8537b77005cc4f33fd8537b77006834f30b87b77005cc4f342f0728537b37005cc4f342f86d7b77005cc4f342f8537005cc4f345742f8537b77006014f342f8537b77005cc4f339d8537b77005f44f342f8537b77005cc4f33b78537b77006884f30c18537b77005cc4f33688537b770062951442f8537b77004f348942f8537b77006774f342f8537b77006784f342f8537b77005cc4f31778537b770066e4f342f8537b77005cc4f317c7936f25cc4f342f34588a8007005cc4f342f8537b77006184f342f8537b77005cc4f33b88537b77006724f342f8537b77005cc4f317a8537b77006454f342f8537b77005cc4f32658537b77005cc4f31798537b770066b4f342f8537b77006714f342f8537b77005cc4f317b8537b77006334f342f8537b77005cc4f330d8537b77005cc4f31788537b77006744f342f8537b77595cc4f33458537b77005cc4f33e78537b77004f342f22f8537b77005cc4f33658537b76fa5cc4f342f8537b77004f342f20c8537b77005cc4f3426 else 0x8537b77004f342f1d48537b77005cc4f33978537b77004f342f1ec8537b77004f342f20f8537b77004f342f20a8537b77005cc4f342088a79c7005cc4f342f86c7b76f25cc4f342f8857de7005cc4f342f8537b770042f27b1d68537b77004f32b81d68537b770042f2761c48537b77004c542f1d68537b77004f33991f28537b77004f33c01d68537b77005cc4c73998536f25cc4f346042f85370062a4f342f2078857005cc4f346042f8537b77006024f342f8537b77005cc4f339c8537b77005e14f342f88a7005cc4f345d42f8537b77006344f342f8537b77005cc4f330c8537b77005cc4f33cc8537b77005d64f342f8537b77005cf4f342f8537b77005cc4f34288537005cc4f346342f86c7dd7005cc4f342f8537b77004f342f1ef8537b77004f342f1d58537b77005cc4f33988537dd7004f342f1ef8537f17005cc4f337b8537ec7004f342f1d58537dd7005cc4f33988737005cc4f346042f8537b77004f342f1e78537b77005cc4f33dc8537b77005ec4f342f8537b77005cc4f33c48537b77005cc4f33208537b770063d51f42f7936f25cc4f342f0c17937307005cc4f342f8537b770060d4f342f8537b77005cc4f33f88537b77006264f342f8537b77005cc4f33628537b75cc4f342f0f68537b77004f342f2088537b77005cc4f341c88b7937005cc4f342f85f7ab7005cc4f342f8437937005cc4f342f8537b76f25cc4f342f8537b77004f342f1fa8537b77005cc4f33f98357257005cc4f342f8857b77005cc4f342f8537005cc4f342f0e58537b77006284f342f))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0x8537005b351042f1c48537b770061b4ce37b7937617005cc4f342f7937646f25cc4f342f8537b77004f342f1fd8537b77005cc4f34018537b77004f342f2108537b77005cc4f342e8487b75cc4f342f0ec7b77004f342f2010728487b77004f342f2018537b770042f27c2017b77005cc4dd42f07284e7b77005cc4f34058537b77004dd42f2018537b77005bf4f34057b77005cc4f32bc0728517b77004f342f1f28537b770042f27d1f28537b77004f34081f28537b77005d94f342f8537b77005cc4f34068537b77006894f342f8537b77005cc4f31607b37005cc4f342f05f7b77005cc4ea42f05f7937005cc4f342f0098537b77005d74f342f8537b77005cc4f341b84874b7005cc4f342f7b77005cc4f342f0aa8537737005cc4f340584a7937005cc4f342f8537b77004f342f1fe8537b77005cc4f34027ab7005cc4f342f05f83574b7005cc4f342f7b77005cc4e842f05f8537737005cc4f33ed8537837004f342f1f28537b778970069a42f7b77005cc4e142f05f8537737005cc4f33ab7b77887005fe4f342f7b77005cc4f342f0638537797005cc4f342f8537b77004f342f1bd8537b77005cc4f33738537b77004f342f1d88537b77005cc4f339e85377a7005cc4f336d8537b77005b14f336d8537b77004f342f22a8537b778e70069d42f8537b77005cc58636d8537b77005f54f342f8537b77005cc4f33b68537b77006854f342f8537b77005cc4f31648537b770069d42f1c48537b77006884f337b8537b778970069d42f7936f25cc4f342f1a388a7dc7005cc4f342f else 0x8537b77005cc4e12608537b77005cc5852e88537b77005cc4e22608537b77005cc50a3ab8537b77005cc4d13ab8537b770061b4f33d68537b77005cc4f33cb8537b77005cc4d242f8537b77005cc4f33d18537b77005fe4fb42f8537b770061e4f33c88537b770061b4f33ab8537b77005cc50c3ab8537b77005cc4ce3ab7936f25cc4f342f37b8537b770067f4f337b8537b770066f4f342f8537b77005cc4f31708537005b34f342f1ef8537005b34f342f1da8537b770064f4f342f8537b77005cc4f32518537b77004c542f1da8537b77005cc4f33cd8797ab7005cc4f342f8357005cc4f342f1cd8537005bd4f342f1cd88a7937005cc4f342f8537b77006504f342f8537b77005cc4f32508537b77004f342f22088279d7005cc4f342f8537b77005f94fd42f8537b770050f42f1c48537b77005cc50f3b08537b77005cc4cb3b08537b770061a4f33808537005cc4f342f2278537b770061c4f337b8537b770061c4f33768537b77004f342f2008537b77005cc4f34048537b77006874f342f8537b77005cc4f31628537b77004f342f1d78537b77005cc4f339b8537b77006834f337b8537b75cc4f342f2328537b77006084f342f8537b77005cc4f33928537b77006ba4f342f8537b77005cc4f310f8537b77005e64f342f8537b77005cc4f33df8537b770065e4f337b8537b77005cc42f2888537b770068d55042f7b77005cc4f342f2218537b77005fe4ff42f8537b77005cc5103ab8537b77005cc4ca3ab8537b77004f342f2218537b770061a4f337b8537b770061b50c37b) else (if page < 20 then 0x8537b76f55cc4f33ab8537b77005cc4f53ab8537b77005cc4ed3ab8537b77005cc4f33b18537b77005cc50f3ab8537b77005cc4cb3ab8537b77005f74f342f8597b77005cc4f33ab8427b77005cc4f33ab8537b77005cc5073ab8537b77005cc4db3ab8537b77005cc4f33be8537b77005cc50e3ab8537b77005cc4cc3ab8537b77005ee4f342f8537b77005103ab1c48537b75cc4f33ab0f38537b76f25cc4f33ab8537b77004f33ab2078537b77005ca4f33ab8537b77004f33c22078537b77005cc4eb3ab8537b77004f342f21d88a7937005cc4f33ab7b77005cc4f341006f8537ab7005cc4f33ab8537b77004f34101f28537b77005c94f33ab8537b77004f34141f28537b77005cc4e83ab8537b77004f342f1f68537b77005cc4f33a485383c7005cc4f33ab8537005cc4f33ab0e57b77005cc4f33ab06f8357b77005cc4f33ab8537b77004f33ab1f28537b77005bd4f33ab8537b77004f33c21f28537b77005cc4d93ab8537b77004f342f21b8857b77005cc4f33ab8537005cc4f34100e58537b77005cc5023ab8537b77005cc4e13ab8537b77005cc4f33b58537ee7005cc4f33ab8537005cc4ca42f3878537b77006044f33ab8537b77005cc4e23ab8537b77005cc4f33b38537b77005cc4f33a18537b770061e4f33ab8537b77005cc4d342f8537b77005fe4f33ab8537b77005c64f33ab8537b77005cc4fe3ab8537b77005cc4e33ab8537b77005cc5093ab8537b77005cc4d53ab8537b77005c54f317d8537b77005cc56a3ab8537b77005c44f317b8537b77005cc5503ab else 0x8537b75fe4f342f0f38537b76f25fe4f342f8537b77005f64f342f8537b77004ff42f2078537b77006044f341a8537b770050242f2078537b77005fe4f341a8537b770060b50242f8537b770061b4f338088a7937005fe4f342f7b770061b4f342f06f8537ab7005fe4f342f8537b77005ed4f342f8537b770050c42f1f28537b770061e4f33ed8537b770051042f1f28537b770061b4f33ed8537b770060a50242f8537b770061b4f338c85383c7005fe4f342f8537005fe4f342f0e57b77005fe4f342f06f8357b77005fe4f342f8537b77004f342f1d98537b77005cc4f33f38537b77004ff42f1f28537b77006044f33ed8537b770050242f1f28537b77005fe4f33ed8857b77005fe4f342f85370061b4f342f0e58537b77004f34481e48677b77005fe4f342f8537005cc4f34463878537b770061f4ff42f8537b77006044f33a88537b770061e50242f8537b77005fe4f33a67b77005cc4ff42f0648537b770069f4ff42f8537b770061e4f316a8537b770061b4f31688537b770051042f1e48537b77005cc4f33bf8537b77006044ff42f8537b770061d4f342f8537b77005cc4f33b28537b770061e4ff42f7b77005fe4f342f0527b77005cc51042f04e8537006a25fe4f342f8537b77005cc5942f08537b77005cc50c24e8537b77005cc4f33b48537b770061b4ff42f8537b770065d4ff42f8537b77005cc51024e8537b77005c54f33ab8537b77005cc4ff3ab8537b77005fb4f342f8537b77005cc4f33ae8537b77004f34102217b77005cc4f34102218537b77065cc4f33ab)) else (if page < 23 then (if page < 22 then 0x8537b77005f24f342f8537b77005cc4f33bb8537b77005fa4f342f8537b77005cc4f33af8537b77005dd4f342f8537b77005cc4f33fa8537b77005fc4f342f8537b77005cc4f33ad8537b77005eb4f342f8537b77005cc4f33c785a7b76f25cc4f342f8857bd7005cc4f342f85379d6f25cc4f342f88579d7005cc4f342f8537b77004f342f1ed8537b77005cc4f33e88537b77006164f342f8537b77005cc4f33a285379d6f55cc4f342f8537a17005cc4f341a85b7b76f55cc4f342f8537b77035d24f342f8537b76f85d24f342f8537b77005d24f442f8537b77065cc4f34218537b76f55cc4f34218537b77005cc4f54218537b77005cc4ed4218537b77035cc4f341a8537b76f85cc4f341a8537b77005d24f341a8537b77005cc4ee41a85379e7005cc4f342f8537b77004f342f1f38537b77005cc4f33ef8537ab70b5cc4f342f8857b770b5cc4f342f8537b770067d4f342f8537b77005cc4f31718357b76db5cc4f342f8537b77004f342f1f08537b77005cc4f33eb8427b76db5cc4f342f8537b76df5cc4f33ed8537b76dd5cc4f342f8537b77005ff4f342f8537b77005cc4f33a88537b77006804f342f8537b77005cc4f316a8537b770050242f2217b77005cc50242f2218537b77035fe4f342f8537b76f85fe4f342f8537b77005fe4f442f8537b77005cc5024218537b77005fe4fd42f8537b77005cc5103b08537b87005fe4f342f8537b17005fe4f342f8537b77005fe4f742f8537b77005cc5103fc8537b77005fe4fc42f8537b77005cc5103bc8537b77005104481c4 else 0x8537a46f25cc4f342f8537a97004f342f2078147936f25cc4f342f8537b77004f342f1ff8537b77005cc4f340383c7005cc4f342f06c8857a47005cc4f342f85383c5cc4f342f0ec8537b77005e24f342f8537b77005cc4f33ee8537b770067c4f342f8537b77005cc4f31728487b76e35cc4f342f8537b75cc4f342f0fa8537b77004f342f1f18537b77005cc4f33ec8357b75cc4f342f0ec8357b76e35cc4f342f8537b76e94f342f1f28537b77004f342f1db8537b77005cc4f33a98537b770050a42f1e48537b77004f342f2197936f25cc4f342f1c48537b770051142f1c48537b770069a42f1c48537005bc4f342f1c48537b770069b42f1c48537b77004f342f12c8537b77005cc4f324d86e7ab7005cc4f342f8537e57005cc4f33ed8537b770042f2811da8537b77004f32b91da8537b770042f2771c48537b77004f33a62078537b77004f33c11da8537b77005cc4c93a68357005cc4f342f3878537005cc4d942f3878537005b54f342f1f28747a47005cc4f342f8537005cc4f342f3cf8537b770065f4f342f8537b77005cc4f324c8537b77004f342f1fb8537b77005cc4f33fb8537b77005f34f342f8537b77005cc4f33ba8537b75cc4f342f3678537b77004f342f1e98537b77005cc4f33e08537b770055842f1c48537b770054d4f31188537b77005cc4f331f8537b77004f342f21e8537b77005f84f342f7936f25cc4f342f03c8537b77004f342f21c8537b77005ef4f342f8537b77004f342f1f78537b77005cc4f33f48537b77005fd4f342f8537b77005cc4f33ac) else (if page < 24 then 0x85383c7004f342f1ef85383c7005cc4f33ea8857987005cc4f342f8537005cc4f342f1028857005cc4f342f0e588a5cc4f342f0f00dd6eb5cc4f342f0dd06685383c5cc4f342f0dd88a7005cc4f342f0d98357b75cc4f342f0dd8536f25cc4f342f0dd83c5cc4f342f0f00dd8856f25cc4f342f0dd8857004f342f2050dd8857005cc4f34170dd83c70d7005cc4f342f8857005cc4f342f0dd6eb6d25cc4f342f0dd83c7006d25cc4f342f7b770d7005cc4f342f6eb6cb5cc4f342f0d983c7005cc4f342f0d98356cb5cc4f342f0dd88583f5cc4f342f0dd8357006cb5cc4f342f88683c7005cc4f342f7b77ac7005cc4f342f7b77005cc4f342f0fd7ab7005cc4f342f0567937005cc4f342f0088357b76cb5cc4f342f8537b75cc4f342f0fd7ab6eb5cc4f342f0567986eb5cc4f342f0667936eb5cc4f342f0538537b77006864f342f8537b77005cc4f31638537005cc4f342f23c8537005cc4f346642f8537b77004f342f2318857b770066d4f342f8537006754f342f0e58537b778570069642f85383c7005cc4f317d8537005cc4f317d0e58537b74f342f20d0f68537b76fa4f342f20d8537b770042f28220d8537b75cc4ef42f0f68537b76fd5cc4f34278537b77004ef42f20d8537b77005cb4f34278537b75cc4f32c10f68537b76ff4f342f2078537b770042f2832078537b77004f342a2077b76fa5cc4f342f06c7b77005cc4f342f07e8537a46fa5cc4f342f8537b77004f342f1ee8537b77005cc4f33e98537b77006144f342f8537b77005cc4f33a37b76f25cc4f342f06c else (if page < 25 then 0x83c7005cc4f342f01183f8387005cc4f342f83c8387005cc4f342f0008387005cc4f342f88683c5cc4f342f0dd88683c6f25cc4f342f88583f7004f342f1f288583f7005cc4f33ed8857b37005cc4f342f8857b76fa5cc4f342f85383c7004f342f1ff85383c7005cc4f340383c7004f342f1ef06683c8357004f342f1ef88683c7004f342f1ef85383c4f342f1ef0dd85383c6f24f342f1ef85383c70042f27a1ef8857af7005cc4f342f8857b76f55cc4f342f8857b77005dd4f342f85383c7005cc4f33fa83c7005cc4f33ea06683c8357005cc4f33ea88683c7005cc4f33ea85383c5cc4f33ea0dd85383c6f25cc4f33ea85383c7004f33ea1ef85383c7005cc4d83ea8537005bc4f342f1ef8537b77006704f342f8537b77005cc4f316f8535cc4f342f0fd0e58536eb5cc4f342f0e37005cc4f342f0fd0e57006eb5cc4f342f0e370d7005cc4f342f0e58538375cc4f342f0e56eb5cc4f342f0d90538537004f342f1ef0e58537005cc4f33ea0e58537004f342f2060e58537005cc4f34180e57b77006d35cc4f342f8537005cc4f342f0e38535cc4f342f0f30e58536f25cc4f342f0e58537004f342f2070e58537005cc4f341a0e58538395cc4f342f0e57005cc4f342f0e506f8357005cc4f342f0e58537004f342f1f20e58537005cc4f33ed0e58537006824f342f0e58537005cc4f316f0e57b77005cc4f342f08f8537b75cc4f342f0fc8357005cc4f342f0537cc7b77005cc4f342f83c7937005cc4f342f83c7005cc4f342f0668857ab7005cc4f342f8857b76f25cc4f342f else 0x8357006cb5cc4f33ed7b77005cc4f34180fd8537006cb5cc4d93ed7936f26cb5cc4f342f7ab6eb6cb5cc4f342f83c7005cc4f342f08f7937005cc4f342f08f83c7ab7005cc4f342f8537ab6f25cc4f342f83c7936f25cc4f342f7937006f25cc4f342f7b76f25cc4f342f0667b77936f25cc4f342f0007936f25cc4f342f83c7935cc4f342f0dd8357b77004f342f1ef83c7937004f342f1ef8537b76f24f342f1ef8537b770042f27a1ef8357b77005cc4f33ea83c7937005cc4f33ea8537b76f25cc4f33ea8537b77004f33ea1ef8537b77005cc4d83ea7ab6f26cb5cc4f342f8387b76cb5cc4f342f85383c5cc4f342f0fd8387006cb5cc4f342f83c7005cc4f342f0fd8857b75cc4f342f0f38857b77004f342f2078857b77005cc4f341a83c70e7005cc4f342f8857b770e5cc4f342f8857b77005e14f342f85383c7005cc4f33f088a7ab7005cc4f342f8357005cc4f342f06683c8397005cc4f342f83c7005cc4f342f06f85383c7004f342f1f285383c7005cc4f33ed83c5cc4f342f0dd06683c8355cc4f342f0dd83c5cc4f342f0dd01183c5cc4f342f0dd0d97ab7005cc4f342f0088857bf7005cc4f342f8857b77005d64f342f8857b77005cc4f341d7ab7006f25cc4f342f8867b76f25cc4f342f88583c7005cc4f342f83c6f25cc4f342f0667b76f25cc4f342f0118857ab6f25cc4f342f7b77ab6f25cc4f342f0007ab6f25cc4f342f88583c6f25cc4f342f7b77005cc4f342f0138387b77005cc4f342f8857b77004f342f1f28857b77005cc4f33ed83f7005cc4f342f013)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0x7005cc4f342f0d90087936f25cc4f342f00885c7b76f25cc4f342f7937005d64f342f0088537b76f25d64f342f8537b77005d64f642f7937005cc4f341d0088537b76f25cc4f341d8537b77005d64f341d8537b77005cc4ec41d8537997005cc4f342f7936ec5cc4f342f0568537b77006004f342f8537b77005cc4f33a78537b770065b4f342f8537b77005cc4f32528537b77005cc4f33d08537b770060a50042f7b76ed5cc4f342f06670d7005cc4f342f0d97b770d5cc4f342f0117b770d6f25cc4f342f79370d7005cc4f342f7b77005cc4f342f0e483f70d7005cc4f342f7005cc4f342f0e606670d7005cc4f342f0dd8377005cc4f342f0668535cc4f342f0fe0dd85370d5cc4f342f0dd7b770d5cc4f342f0dd70d6eb5cc4f342f0dd70d5cc4f342f0dd06600070d5cc4f342f0dd7b76ed5cc4f342f0dd8376eb5cc4f342f0668375cc4f342f0dd0667ac7006cb5cc4f342f8537005cc4f342f0df7936eb6cb5cc4f342f7b770d6cb5cc4f342f8537b76d45cc4f342f7ab6eb5cc4f342f0537ab6eb5cc4f342f0668867b770d5cc4f342f8357936cb5cc4f342f7b75cc4f342f10006f8537ab5cc4f342f0fd7b75cc4f342f1000138535cc4f342f0fd0e38357b76cb4f342f1f28537b74f342f2060fd8357b76cb5cc4f33ed8537b75cc4f34180fd8537006d45cc4f342f8356cb5cc4f342f0d98387ab7005cc4f342f7ab6eb5cc4f342f0dd7005cc4f342f10006f7ab7005cc4f342f0fd7005cc4f342f1000137005cc4f342f0fd0e38357006cb4f342f1f27b77004f342f2060fd else 0x8537005cc4f342f0788617ab7005cc4f342f8537ab70e5cc4f342f8537ab7005e14f342f8537b77005e14f842f8357b77005cc4f33f08537b77006114f33f08537b77005cc4da3f06f25cc4f342f0dd0d97157005cc4f342f0dd8537006d65cc4f342f88a8395cc4f342f0dd7b76f25cc4f342f0d97b77157005cc4f342f88a5cc4f342f0f30d988a6f25cc4f342f0d97006f25cc4f342f0d90006f25cc4f342f0d988a7004f342f2070d988a7005cc4f341a0d988a7157005cc4f342f7157005cc4f342f0d988a8397005cc4f342f88a8395cc4f342f0d98537b77006844f342f8537b77005cc4f316c8355cc4f342f0dd0668357b74f342f1f20dd8357b75cc4f33ed0dd8537b77006034f342f8537b77005cc4f339a8537b770067f56c42f8537b770069b5cc16d8537b77005cc18d16d8537b770069b42f0a48537b77005cc4f336688a7ac7005cc4f342f7b75cc4f342f0ff0dd7005cc4f342f0dd0137005cc4f342f0e30568367005cc4f342f0567b77004f342f1f206f8357b77004f342f1f28537b770042f27b1f27b77005cc4f33ed06f8357b77005cc4f33ed8537b77004f33ed1f28537b77005cc4d93ed7ac7ab7005cc4f342f7ab7004f342f2060567ab7005cc4f34180567b77005cc4e84180567bf7ab7005cc4f342f7bf7006d25cc4f342f8537b77006194f342f8537b77005cc4f33a07ac7005cc4f342f0087957005cc4f342f0567936f25cc4f342f0568537986f25cc4f342f7b77957005cc4f342f8397005cc4f342f0087957937005cc4f342f7957005cc4f342f008) else (if page < 29 then 0x8537b77004f342f2178537b77006114f33ed8537b77005cc4da3ed8537b77005e04f342f83c8357005cc4f33ed88a8357005cc4f33ed85383f6f25cc4f33ed8357005cc4f33ed0668538367005cc4f33ed7b77005cc4d942f07284e7b77005cc4f33ed8537b77004d942f2018537b77005cc4df3ed8537b77004f342f2147b77004f33ed1f206f8357b77004f33ed1f28537b77003ed27b1f28577b77005cc4f33ed8427b77005cc4f33ed8537b770060f4f33ed8537b77005cc4db3ed8537b77005cc4de42f7b77005cc4d93ed06f8357b77005cc4d93ed8537b77004d93ed1f28537b77005bd4d93ed88a8537005cc4d93ed8537005cc4d93ed0668537b75cc4f33ed0f38537b76f25cc4f33ed8537b77004f33ed2078537b77005cc4eb3ed8537b77004f342f21688a7937005cc4f33ed7b77005cc4f341806f8537ab7005cc4f33ed8537b77004f34181f28537b77005cc4e83ed8537b77004f342f1f58537b77005fd4f33ed8537b77005c94f33ac8538017005cc4f33ed8537b77006174f33ed8537b77005bd4f33bc8537b77005cc58b2ea8537b77006544f33ed8537b77005cc4e825c8536f24f342f2070dd8536f25cc4f341a0dd7b770d5cc4f342f0f37b770d7004f342f2077b770d7005cc4f341a6f25cc4f342f0dd0667936f25cc4f342f0dd8866f25cc4f342f0dd6f25cc4f342f0f00dd88a4f342f2070f00dd88a5cc4f341a0f00dd88a70d5cc4f342f0dd70d5cc4f342f0f00dd7b76f26d25cc4f342f6f25cc4f342f0dd0118357006d25cc4f342f88a70e5cc4f342f0dd else 0x83f7936f25cc4f342f7ab7005cc4f342f06f8357ab7005cc4f342f7b77004f342f20106f8357b77004f342f2017b77005cc4f340506f8357b77005cc4f34058537b770042f2841f28537b77004f342c1f28537b770050842f1f28537b77004f33f01f283c8357004f342f1f288a8357004f342f1f285383f6f24f342f1f28357004f342f1f20668538367004f342f1f27b77004f342f1f20728487b77004f342f1f28537b770042f27c1f28537b77004f34051f27b770042f27b1f206f8357b770042f27b1f28537b77002bc27b1f28537b77004f342f1dc8537b77005cc4f33aa8537b770065a4f342f8537b77005cc4f32558537b74f342f1f20f38537b76f24f342f1f28537b770042f2811f28537b77004f341a1f28537b77005df4f342f88a7937004f342f1f27b77004f342f20606f8537ab7004f342f1f28537b770042f2801f28537b77005cc4f33f28537b770042f2801dc8537b77004f340f1f28537dd7004f342f1f28537b770055642f1f28537b77004f32561f28537b77004b942f11c7b77005cc4f342f0768537b47005cc4f342f8567b77004f342f1f28597b77004f342f1f28427b77004f342f1f28457b77004f342f1f27b770060c4f342f06f8537ab7005dc4f342f8537b770050642f1f28537b770050742f1f27b77005cc4f33fc06f8357b77005cc4f33fc8537b77004f33fc1f28537b77004f33fe1f27b77005cc4f33ed0728487b77005cc4f33ed8537b77004f33ed2018537b77005cc4dd3ed8537b77004f342f2158537b77004f33ed20f8537b77005cc4f23ed)) else (if page < 32 then (if page < 31 then 0x7937005cc4f342f1048537b75cc4f342f1018087936f25cc4f342f7936f25cc4f342f1bf7937005cc4f344c42f7936f25cc4f342f08588a79370061c4f342f8537b770051142f1bf88a7937005cc4f339f8537b770061c50d42f8537b77005cc51139f8537b77005cc4c839f7936f25cc4f342f3767937005cc4f342f2298537b77004f342f2268537b74f342f20f0f38537b770042f28420f8537b75cc4f342c0f38537b77004f342c20f8537b77005cc4f242c7b77006114f342f06f7b77005cc4f33f006f7b77004f342f20f06f7b77005cc4f342c06f7b77005d64f342f06f7b77005cc4f341d06f7b77005e14f342f06f7b77005cc4f341906f7b77005fd4f342f06f7b77005cc4f341106f7b77005cc4f342f0798537ab7004f342f20f8537ab7005cc4f342c8537b770060e4f342f8537b77005cc4f33a58537ab7004f342f1ec8537ab7005cc4f33e786b7ab7005cc4f342f8357b770060e4f342f8537ab7005cc4f33a58777ab7005cc4f342f8537ab5cc4f342f0f37b76f25cc4f342f06f7b77004f342f20706f8537ab7004f342f2078537b77005cc4f33f17b77005cc4f341a06f8537ab7005cc4f341a8537b77004f342f1f488a7005cc4f342f0788357005cc4f342f07888a7ab5cc4f342f0f388a7ab6f25cc4f342f83f6f25cc4f342f06f8867ab6f25cc4f342f85383f5cc4f342f0df8536f25cc4f342f0df88a7ab7004f342f2078867b76f24f342f20788a7ab7005cc4f341a8867b76f25cc4f341a8357b76ce5cc4f342f8367005cc4f342f06f7ab7006ce5cc4f342f else 0x88a7005cc4f342f09888a7935cc4f342f0f688a7936fa5cc4f342f8907936f25cc4f342f88a7937004f342f20d88a7937005cc4f34277936f25cc4f342f20788a7004f342f2070977937004f342f20709788a7934f342f2070f37937004f342f20700888a7936f24f342f2077937006f24f342f2070007936f24f342f20788a79370042f2812077936f25cc4f342f00688a7947005cc4f342f88a7937035cc4f342f88a7936f55cc4f342f88a7937005d24f342f88a7937005cc4f34217936f25cc4f342f41a88a7005cc4f341a0977937005cc4f341a09788a7935cc4f341a0f37937005cc4f341a00888a7936f25cc4f341a7937006f25cc4f341a0007936f25cc4f341a88a7937004f341a20788a7937005cc4eb41a7937005ca4f342f2077b77005cc4f342f0977936f25cc4f342f06688a7005cc4f342f0977937005cc4f342f09788a7935cc4f342f0f388a7936f25cc4f342f88a7937004f342f20788a7937005cc4f341a8387937005cc4f342f8397936f25cc4f342f88a7937004f342f1ec88a7937005cc4f33e78397b76f25cc4f342f88a7005cc4f342f07788a8387005cc4f342f8398387005cc4f342f88a8395cc4f342f0f388a8396f25cc4f342f8397006f25cc4f342f88a8397004f342f20788a8397005cc4f341a8397b76ce5cc4f342f88a8397004f342f1ec8537b770042f2791ec88a8397005cc4f33e78537b77004f33e71ec8537b77005cc4d73e77936f25cc4f342f0d97937157005cc4f342f7936f25cc4f342f08e7937005cc4f342f08d7936f26c75cc4f342f) else (if page < 33 then 0x8537b77005cc4ed41a8537b77005cc4f042f8537b75cc4eb41a0f38537b76f25cc4eb41a8537b77004eb41a2078537b77005ca4eb41a8537b77005f94f341a8537b77005ca4f33b08777b77005cc4f341a8537b77006784f341a8537b77005ca4f31778537b77005cc5912eb8537b77006574f341a8537b77005cc4eb25b8537b74f342f2070f38537b76f24f342f2078537b770042f2812078537b75cc4f341a0f38537b76f25cc4f341a8537b77004f341a2078537b77005cc4eb41a7b76f24f342f2070667b76f25cc4f341a0667b770e6f25cc4f342f8537b770067e4f342f8537b77005cc4f316e7b770e6ce5cc4f342f8537b76d55cc4f342f8537b770065c4f342f8537b77005cc4f324f8537b77005cc4f33ce8537b770060b50142f7b75cc4f342f0f30977b76f25cc4f342f0977936f25cc4f342f0538387b76f25cc4f342f7b77004f342f2070977b77936f24f342f2077b77005cc4f341a0977b77936f25cc4f341a88a7167005cc4f342f7937006c85cc4f342f88a7005cc4f342f09988a7937004f342f20f88a7937005cc4f342c88a5cc4f342f0f30977935cc4f342f0f309788a5cc4f342f0f307788a7957005cc4f342f88a7937005d64f342f88a7937005cc4f341d8947936f25cc4f342f88a6f25cc4f342f0977936f25cc4f342f0977936f25cc4f342f0f388a8386f25cc4f342f8387006f25cc4f342f8387936f25cc4f342f0008386f25cc4f342f7936f25cc4f342f08d7937626f25cc4f342f7936f25cc4f342f1a27936f25cc4f342f0c27936f25cc4f342f344 else (if page < 34 then 0x8537b74f342f20d0f38537b76f24f342f20d8537b75cc4f34270f38537b76f25cc4f34278537b770042f2842078537b77004f342c2078537b77004f642f2078537b77004f341d2078857b76f24f342f2078537b74f342f2070f68537b76fa4f342f2078537b770042f2822078537b77004f34272078537b742f2812070f38537b76f242f2812078537b77002c12812078537b770067b4f342f8537b77005cc4f31748537b77006594f342f8537b77005cc4f32588537b770069942f2078537b77004f320717486b7b77004f342f2078537b770055342f2078537b77004f32592078537b77004b842f11d8667b77004f342f2078537b75cc4f342f0f88537b76fb5cc4f342f8537b77034f342f2078537b77064f342f2078537b76f54f342f2078537b76f64f342f2078537b75d24f342f0f38537b76f25d24f342f8537b77004f442f2078537b77004f542f2078537b75cc4f34210f38537b76f25cc4f34218537b77004f34212078537b77004f34232078537b75cc4f341a0f68537b76fa5cc4f341a8537b77004f341a20d8537b77005cc4ef41a8537b77004f342f2128537b77004f341a20f8537b77005cc4f241a8537b77004f342f2138537b77005d64f341a8537b77005cc4ec41a8537b77005d54f342f8857b76f25cc4f341a8537b75cc4eb42f0f68537b76fd5cc4f341a8537b77004eb42f20d8537b77005cc4f141a8537b77004f342f2118537b74f341a2070f38537b76f24f341a2078537b770041a2812078537b77045cc4f341a8537b76f55cc4f341a8537b77005d34f341a else 0x8537b770067a4f342f8537b77005cc4f31758537b75e14f342f0f38537b75cc4f33f00f38537b767a4f342f0f38537b75cc4f31750f38537b75d64f342f0f38537b75cc4f341d0f38537b75cc4f342f0f98537b76f24f342f20f8537b76f25cc4f342c86b7b76f25cc4f342f8777b76f25cc4f342f8537b76f26784f342f8537b76f25cc4f3177)))))) else 0
  | 6 => if page < 56 then (if page < 28 then (if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x8537b77005cc4f342f1308537b771b7005cc4f342f8537b77005cc4f34b042f8537b77005cc4f342f09c8537b77005cc4f342f12f8537b77005cc5434f342f8537b77006584f342f1310008537b77006584f342f8537b77005cc4f332e1318537b77005cc5932ec2d48537b77006584f342f2d48537b77005cc4f34b725a8537b77005cc4f32ec25a8537f67b77005cc4f342f8537b77005cc4f342f2d18537b77005cc4f342f0298537b77005cc4f342f2d38537b773e7005cc4f342f8537b77005cc4f342f2d08537b77005cc4f342f0af8537b77005cc4f342f2d28537b77005cc4f342f25a8537b77005cc4f32d425a0008537b77005cc4f325a8537b77005cc55242f14d8537b77005cc42f2a814d8537b77005cc4f32b614d8537b77005cc4f337b14d8537b77647005cc4f314d8537b77005cc4f314d0c18537b77005cc5934f314d8537b77005cc4f324614d8537d77b77005cc4f342f8537b77005cc4f349742f8537b77005cc4f342f01a8537b77005cc4f342f1428537b771f7005cc4f342f8537b77005cc4f348342f8537b77005cc4f342f09e8537b77005cc4f342f1398537b77005cc5934f342f8537b77006914f342f14d8537b77005cc4f347c42f8537b77005cc4f342f30a8537b77005cc4f342f1098537b77005cc4f342f1318537b77005cc4f332514d8537b77005cc4f32c814d8537b77005cc4f332314d8537b77467005cc4f314d8537b77005cc4f32460b18537b77004f342f2aa14d8537b77004f33252aa14d8537b77005cc5524f314d8537b77005cc55232514d0008537b77005cc55214d8537b77005cc3252a814d8537b77005cc4f32461318537b77005cc59342f2ec8537b77006914f332514d0008537b77005cc5932ec8537b77005cc4f342f2ec8537b77005cc4f342f14d0008537b77005cc4f342f else (if page < 2 then 0x8537b77005cc4f325a03c8537b77005cc4f337b25a8537b77647005cc4f325a8537b77004f342f2cd1a38537b77005cc4f325a0c18537b77005cc4f334525a8537b77004f342f2cd14d8537ea7b77005cc4f342f8537b77005cc4f342f3148537b77005cc4f342f0268537b77005cc4f342f24b8537b77337005cc4f342f8537b77005cc4f342f3128537b77005cc4f342f0ab8537b77005cc4f342f2498537b77006af4f34b725a0008537b77006af4b725a85381f7b77005cc4f325a8537b77005cc4f329925a8537b77004f342f2cd02c8537b77005cc4f34b525a8537b77707005cc4f325a8537b77005cc4f328f25a8537b77004f342f2cd0b18537b77005cc4f34b425a8537b77005cc5434f325a88a8537b77005cc4f325a8537b77005cc4f325a0668537b77937005cc4f325a85383f7b77005cc4f325a8537b77005cc4f325a0dd8537b77005cc4f325a0568537b77006cb5cc4f325a8538207b77005cc4f325a8537b77005cc4f325a1c48537b77005cc42f2a803c8537b77005cc4f34c525a8537b77757005cc4f325a8537b77005cc4f325a1a38537b77005cc42f2a80c18537b77005cc4f34c125a8537b77006af5cc4f325a8537ea7b77005cc4f325a8537b77005cc51e4f325a8537b77005cc4f325a0268537b77005cc4f325a24b8537b77337005cc4f325a8537b77005cc51d4f325a8537b77005cc4f325a0ab8537b77005cc4f325a2498537b77005cc5934f325a8537b77005cc4f34be25a8537b77005cc4f325a14d8537b77005cc4f325a1318537b77005cc5932ec1318537b77004f342f2cd1318537b77006584f342f2ec8537b77005cc4f332e2ec8537b77005cc4f342f2d48537b77005cc59342f1310008537b77005cc5931318537d37b77005cc4f342f8537b77005cc4f34b242f8537b77005cc4f342f017 else 0x8538217b77005cc4f342f8537b77005cc4f342f12b8537b77005cc4f342f0488537b77005cc52f4f342f8537b77777005cc4f342f8537b77005cc4f342f1298537b77005cc4f342f0d18537b77005cc52b4f342f8537b77006af5434f342f0008537b77006af54342f8537b77005cc4f342f33485382e7b77006584f342f8537b77006584f342f1c48537b77005cc5434f303c8537b77005cc5434f337b8537b77897006584f342f8537b77006584f342f1a38537b77005cc5434f30c18537b77005cc5434f33458537b77006584f342f14d8537b77005cc55242f2ec8537b770065859342f2ec0008537b77006585932ec8537fa7b77006584f342f8537b77005cc5434f32998537b77006584f342f02c8537b77006584f342f2e28537b77437006584f342f8537b77005cc5434f328f8537b77006584f342f0b18537b77006584f342f2da88a8537b77006584f342f8537b77006584f342f0668537b77937006584f342f85383f7b77006584f342f8537b77006584f342f0dd8537b77006584f342f0568537b77006cb6584f342f8538307b77006584f342f8537b77006584f342f12b8537b77005cc5434f30488537b77006586474f342f8537b778c7006584f342f8537b77006584f342f1298537b77005cc5434f30d18537b77006586404f342f8538147b77006584f342f8537b77005cc55242f1c48537b77006584f342f03c8537b77006584f342f37b8537b77647006584f342f8537b77005cc55242f1a38537b77006584f342f0c18537b77006584f342f3458537b77006916584f342f8537b77005cc5434f314d8537b77006584f342f1098537b77006584f342f3348537b77006585934f342f0008537b770069155242f0000008537b77006af5438537b77006af4b742f25a8538147b77005cc4f325a8537b77004f342f2cd1c4)) else (if page < 5 then (if page < 4 then 0x8537b773f7005cc4f342f8537b77005cc4f342f1b58537b77005cc4f342f3698537b77005cc4f342f36d8537b77435cc4f342f0c18537b77435cc4f342f3458537b77467006914f342f0008537b77707006af42f8537b77006af4b742f28f8537b75cc4f342f2c70c18537b75cc4f34c142f28f8537ef7b77005cc4f342f8537b77005cc4f342f3018537b77005cc4f342f0278537b77005cc4f342f28d8537b77647005cc4f342f8537b77005cc4f342f2fe8537b77005cc4f342f1a38537b77005cc4f34b142f8537b77005cc4f342f2d88537b77005cc5932ec0b18537b75cc4f342f2ce0b18537b77006254f342f2ec8537b77005ae4f342f2ec8537b77005cc4f335e2ec8537b77005cc4f342f2da8537b77005cc59342f0b10008537b77005cc5930b18537c37b77005cc4f342f8537b77367005cc4f342f8537b77005cc4f342f00c8537b77005cc4f342f0b08537b77437005cc4f342f8537b77435cc4f342f0b18537b77005cc4f345242f8537b77006254f342f0b10008537b77006254f342f8537b77005cc4f342f3638537b77005ae4f342f0b10008537b77005cc4f33638537b77005cc4f342f35c8537b77005cc4f335e0b18537b77005cc5932ec2da8537b77435cc4f342f2da8537b77006434f342f2ec8537b77005cc4f34b72678537b77005cc4f33251768537b77005cc4f342f0b18537f77b77005cc4f342f8537b77005cc4f342f2a48537b77005cc4f342f02a8537b77005cc4f342f2d98537b77005cc4f342f28f8537b75cc4f34b442f28f8537b77005cc52c4f342f8537b77006434f342f2da0008537b77006434f342f8537b77005cc4f342f2678537b77005cc4f34b42670008537b77005cc4f32678537b77005cc4f342f1768537b77005cc4f33221760008537b77005cc4f31768537b77006585cc5932ec else 0x8537005cc4f34c542f2998537b77006af4f342f2990008537b77006af42f2998537f07b77005cc4f342f8537b77005cc4f342f2e68537b77005cc4f342f0288537b77005cc4f342f2978537b77377005cc4f342f8537b77005cc4f342f2de8538147b77005cc4f342f8537b77005cc4f342f2f38537b77005cc4f342f1c48537b77005cc4f34b342f8537b77005cc4f342f2d68537b77005cc5932ec02c7b77005cc4f342f2cf02c8537b77005ea4f342f2ec8537b77005ba4f342f2ec8537b77005cc4f33c22ec8537b77005cc4f342f2e28537fa7b77005cc4f342f8767b77005cc4f342f02c8537bb7b77005cc4f342f8537b77a07005cc4f342f8537b77005cc4f342f0048537b77097005cc4f342f8537b77006de5cc4f342f8537b77005cc4f343842f8537b77005ea4f342f02c0008537b77005ea4f342f8537b77005cc4f342f3c88537b77005c74f342f02c0008537b77005cc4f33c88537b77005cc4f342f3ab8537b77005cc4f341402c0008537b77005cc4f33ab8537b77005cc5932ec2e28537fa7005cc4f342f2e28537b770064d4f342f2ec8537b77005cc4f34b72608537b77005cc4f33251578537b77005cc4f342f02c8537b77005cc59342f2e20008537b77005cc5932e28537f97b77005cc4f342f8537b77005cc4f342f29a8537b77005cc4f342f02b8537b77005cc4f342f2e18537b77005cc4f342f2998537005cc4f34b542f2998537b77427005cc4f342f8537b77005cc4f342f2908537b77005cc5354f342f8537b770064d4f342f2e20008537b770064d4f342f8537b77005cc4f342f2608537b77005cc4f34b62600008537b77005cc4f32608537b77005cc4f342f1578537b77005cc4f33241578537b77437005cc5932ec8538477b77005cc4f342f8537b77005cc4f342f0ad8537b77005cc4f342f05b) else (if page < 6 then 0x8537b77005cc4f34b71768537b77005cc56b42f2ec8537b77005cc4f342f26b8537b77005cc4f347342f8537b77005cc51742f2ec8537b77005cc4f342f2878538147b77005cc5932ec8537b77006914f33251c48537b77005cc5932ec03c8537b77005cc59337b2ec8537b77647005cc5932ec8537b77006914f33251a38537b77005cc5932ec0c18537b77005cc5933452ec8537b77006915cc5932ec8537b77006af4b742f14d8537b77005cc5932ec14d8537b77006914f33252ec8537b77006af4f342f2878537b77004f34b742f2870008537b77004f342f28788a8537b77005cc5932ec8537b77005cc5932ec0668537b77937005cc5932ec85383f7b77005cc5932ec8537b77005cc5932ec0dd8537b77005cc5932ec0568537b77006cb5cc5932ec85382e7b77005cc5932ec8537b77005cc5932ec1c48537b77006af4b742f03c8537b77005cc5b35932ec8537b77897005cc5932ec8537b77005cc5932ec1a38537b77006af4b742f0c18537b77005cc5a65932ec8538277b77005cc5932ec8537b77006af4b742f1188537b77005cc5932ec04d8537b77005cc5935762ec8537b77817005cc5932ec8537b77006af4b742f1138537b77005cc5932ec0d58537b77005cc59355b2ec8537b77006c55cc5932ec8537b77006af4b742f1098537b77005cc5932ec1948537b77005cc5935272ec8537b77006af4b742f2870008537b77006af42f2870008537b77004b742f2878537fa7b77005cc5932ec88e8537b77005cc4f342f8537b77005cc4f342f06a8537b77a27005cc4f342f8537b77005cc4f342f0e98537b77006e05cc4f342f8537b77005cc4f342f1e08537b77005cc4f342f3d28537b77005cc4f342f3d68767b77005cc4f342f03c8537fa7005cc4f342f37b8537b77006af4b742f2997b77005cc4f342f2ca03c else 0x8537b77005cc59314d1318537b77005cc51742f1318537b77005cc4f332e14d8537b75cc4f342f2ec0f38537b76f25cc4f342f2ec8537b77004f342f2ec2078537b77005ca4f342f2ec8537b77004f342f3252078537b77005cc4f341a2ec8537b77005cc4f342f2a18537b77005cc4f342f2eb8537b77005cc4f342f2f78537b77005cc4f342f2e388a7937005cc4f342f2ec8537f87b77005cc4f342f8537b77005cc4f342f07f7b77005cc4f342f2ec06f8537ab7005cc4f342f2ec8537b77004f342f2ec1f28537b77005bd4f342f2ec8537b77004f342f3251f28537b77005cc4f33ed2ec8537b77005cc4f342f2a08537b77005cc4f342f2ea8537b77005cc4f342f3038537b77005cc4f342f2db8537b77005cc4f342f2f68537b77005cc4f342f2e78857b77005cc4f342f2ec8537005cc4f342f2ec0e58537b77407005cc4f342f8537b77005cc4f342f0b38537b77005cc4f342f29d8537b77005cc4f342f2e98537b77005cc4f342f3158537b77005cc4f342f2d58537b77005cc50242f2ec8537b77005cc4f33ab2ec8537b77005cc4f342f2f58537b77005cc4f342f2e88537b77005cc53a4f342f8537b77005cc4f342f1338537b77004f34b742f1b98537b77005cc4f33712ec8537b77005cc4f342f2958537b77005cc4f342f2e08537b77005cc4f342f3138537b77005cc4f342f2d78537b77005cc4f342f3008537b77005cc4f342f2df8537b77006985cc42f2ec8537b77005cc4f32ec1768537b77005cc52d4f342f8537b77005cc4f342f1368537b77005cc4f342f29b8537b77005cc4f349c42f8537b77005fe4f342f2ec8537b77005b84f342f2ec8537b77005cc4ff42f2ec8537b77005cc58642f2ec8537b77005cc4f342f2928537b77005cc4f348c42f8537b77005cc51542f2ec8537b77006794f342f2ec))) else (if page < 10 then (if page < 8 then 0x8537b77006af6384f342f8537b77006914f342f1428537b771f7006914f342f8537b77006914f342f09e8537b77006354f324614d8537b77004f34ac42f1c48537b77005cc5174f337b8537b77757005cc47c42f8537b77005cc5174f30c18537b77006af4f347c42f8537b77005cc5204f314d85381a7b77005cc4f342f8537b77005cc4f342f18a8537b77005cc4f342f0428537b77005cc4f347942f8537b77677005cc4f342f8537b77005cc4f342f1888537b77005cc4f342f0cd8537b77005cc4f347642f8537b77006c55cc4f342f8537b77005cc4f342f1948537b77006354f342f1c48537b77005cc4f347c37b8537b77897006354f342f8537b77005cc4f347c0c18537b77006af6354f342f8537b77005cc4f347c14d8537b77005cc4be24614d8537b77004f34ab42f1c48537b77005cc4f337b30a8537b77647005cc4f330a8537b77005cc4f330a0c18537b770051c4f342f14d8537b77005cc51c4f314d8537b77005cc5934f330a8537fd7b77005cc4f342f8537b77005cc4f342f26f8537b77005cc4f342f02f8537b77005cc4f342f3078537b77457005cc4f342f8537b77005cc4f342f26d8537b77005cc4f342f0b58537b77005cc4f342f3048537b77006914f342f30a8537b77005cc59314d1098537b77005cc4be42f1098537b77006354f342f14d8537b77005cc4f333414d8537b77005cc4f32b61098537b77005cc4f337b1098537b77647005cc4f31098537b77005cc4f31090c18537b77006914f342f1098537b77005cc42f2a61098537cf7b77005cc4f342f8537b77005cc5a04f342f8537b77005cc4f342f0148537b77005cc4f342f1088537b77187005cc4f342f8537b77005cc59c4f342f8537b77005cc4f342f09a8537b77005cc4f342f1078537b77006354f342f1098537b77005cc4f3334109 else (if page < 9 then 0x8537b76365cc4f342f1a38537b77005cc4f349042f8537b77005cc4f342f0c18537b77005cc4f342f3458537b763a5cc4f342f09e8537b77006294f342f14d8537b77005cc4f337114d8537b77004f342f2aa09e8537b77005cc5934f309e8537b77005cc4f324609e8537c17b77005cc4f342f8537b77687005cc4f342f8537b77005cc4f342f00a8537b77005cc4f342f09d8537b771f5cc4f342f09e8537b77005cc4f345a42f8537b77006294f342f09e8537b77005cc4f344d42f8537b77005cc4f342f3708537b77005cc4f337109e8537b771f5cc4f342f1398537b77006794f342f14d8537b77005cc51642f14d8537b77005cc4bf42f14d8537b77005cc4f332c14d8537b77005cc4f32b61398537b77005cc4f337b1398537b77647005cc4f31398537b77005cc4f31390c18537d47b77005cc4f342f8537b77005cc4f34a842f8537b77005cc4f342f0188537b77005cc4f342f1388537b763a5cc4f342f1398537b77005cc5654f342f8537b77006794f342f1390008537b77006794f342f8537b77005cc4f347842f8537b77005cc51642f1390008537b77006314f342f8537b77005cc4f342f30f8537b77005cc4bf42f1390008537b77005cc4f330f8537b77005cc4f332c1398538277b77005cc4f342f8537b77005cc4f342f1188537b77005cc4f342f04d8537b77005cc5764f342f8537b77817005cc4f342f8537b77005cc4f342f1138537b77005cc4f342f0d58537b77005cc55b4f342f8537b77006914f342f1c48537b77005cc5934f337b8537b77897006914f342f8537b77005cc5934f30c18537b77006af6914f342f8537b77006914f32b614d8537b77006914f337b14d8537b77647006914f314d8537b77006914f314d0c18537b77006914f32aa14d8537b77006915934f314d8537b77006914f324614d else 0x8537b77005cc4f342f0028537b77077005cc4f342f8537b77006e75cc4f342f8537b77005cc4f343b42f8537b77005fe4f342f01a0008537b77005fe4f342f8537b77005cc4f343442f8537b77005cc4f942f01a0008537b77005e54f342f8537b77005cc4f342f3e18537b77005cc4e742f01a0008537b77005cc4f33e18537b77005cc4f341601a8537d77005cc4f342f1428537b770068d4f342f14d8537b77005cc4f332714d8537b77005cc4f32bd1428537b77005cc4f340a1428537b77004f342f2aa1428537b77005cc5934f31428537b77005cc4f32461428537d67b77005cc4f342f8537b77005cc4f349842f8537b77005cc4f342f0198537b77005cc4f342f14185370063e5cc4f342f1428537b771e7005cc4f342f8537b77005cc4f348442f8537b77005cc5814f342f8537b770068d4f342f1428537b77005cc4f347b42f8537b77005cc4f342f30b8537b77005cc4f332a1428537b771f5cc4f314d0c18538417b77005cc4f342f8537b77005cc4f342f0ce8537b77005cc4f342f0588537b771c7005cc4f342f8537b77005cc4f342f1b98537b778971f5cc4f342f8537b771f5cc4f342f1a38537b77005cc4f342f1b08537b77005cc4f342f3588537b771f5cc4f342f0c18537b771f5cc4f342f3458537b77397005cc4f314d8537b77347006914f342f8537b77327005cc4f314d8537b763a5cc4f314d0c18537b77005cc4f317614d8537b77004f348342f1c48537b77005cc5214f337b8537b77005cc5214f30c18537b75cc5214f342f0c18537b75cc5214f342f34585381b7b77005cc4f342f8537b77005cc4f342f1858537b77005cc4f342f0438537b77005cc4f348042f8537b77897004f348342f8537b770063a5cc4f31768537b77005cc59d4f342f8537b77005cc4f342f1378537b77645cc4f348342f)) else (if page < 12 then (if page < 11 then 0x8537b77005cc42f2a714d8537b77005cc4f32c614d8537b77004f342f2c614d8537b77005cc42f2a61188537b77005cc5764f314d8537b77817005cc4f314d8537b77005cc4f314d0d58537b77005cc5274f314d8537b77005cc59327514d8537b77005cc5934c514d8537b77757005cc59314d8537b77005cc59318c0c18537b77006af5cc59314d8537b77005cc59318c14d8537b77006af4f347342f8537b77005cc5284f314d8537b77005cc4f33ab14d8537d77005cc4f337b14d88c8537b77005cc4f342f8537b77005cc4f342f0688537b779b7005cc4f342f8537b77005cc4f342f0e78537b77006d85cc4f342f8537b77005cc4f342f1e488386a7b77005cc4f342f8537d77005cc4f342f1c48537b77005cc4f342f1d38537b77005cc4f342f3968537d77b77005cc4f33ab8537eb7b77004f342f1c486a7b77005cc4f342f03c8537d77b77005cc4f337b8537d77005cc4f342f37b85370063e5cc4f337b14d8537b77004f34a342f1c48537b77005cc5254f337b7b77005cc5254f342f03c8537005cc5234f342f37b8537b77006af4f349742f8537b77005cc5234f314d85381d7b77005cc4f342f8537b77005cc4f342f1478537b77005cc4f342f0458537b77005cc4f349442f8537b776a7005cc4f342f8537b77005cc4f342f13e8537b77005cc5a24f342f8537b77005cc4f342f1348538147005cc4f349742f8537006385cc4f342f1c48537b77005cc4f349714d8537b77005cc4f349e42f8537b77005cc4f342f03c8537b77005cc4f342f37b7b770063f5cc4f342f01a8537b77005fe4f342f14d8537b77005cc4f942f14d8537b77005cc4d542f14d8537b77005cc4f33e414d8537b77005cc4f32bd01a8537b77005cc4f340a01a86a7b77005cc4f342f01a8537b97b77005cc4f342f8537b77a77005cc4f342f else 0x8537b77005cc4f343b14d8537b77005cc4f33c214d8537b77005cc4f342f1588537b77005cc4f342f1498537b77005cc5814f314d8537b77005cc4f324714d8537b77005cc4f347a42f8537b77005cc4f342f10a8537b77004f342f1bb14d8537b77005b04f342f14d8537b77005cc4f348b42f8537b77005cc4f342f1408537b77005cc4f34ad14d8537b77005cc4f32fe14d8537b77005cc4f342f26e8537b77005cc4f342f1358537b77005cc4f345a14d8537b77005cc4f335e14d8537b77005cc4f342f1828537b77005cc4f342f13f8537b770069e4f342f14d8537b77004f342f27214d8537b77005cc5654f314d8537b77005cc4f324814d8537b77005cc4f347742f8537b77005cc4f342f10c8537b77005cc4f32ae14d8537b77005cc4f338714d8537b77005cc4f32b514d8537b773c7005cc4f314d8537b77005cc4f332814d8537b77005cc5244f314d8537b77004f342f29e1c48537b77005cc4f32c914d8537b77005b94f342f14d8537b77005cc4ff42f14d8537b77005cc4ce42f14d8537b77004f342f2ab14d8537b77005cc4f32b714d8537b77005cc4f337614d8537005cc4f337b2b614d8537b775a7005cc4f314d8537b770068d4f337b14d8537b77005cc4f32ab14d8537b77004f340a2ab14d8537b77005cc5864f314d8537b77005cc4f33ab37b8537b77004f342f2710a48537b774b7005cc4f314d8537b77005cc5af4f314d8537b77005cc4f327414d8537b77897004f348c42f8537b770063c5cc4f314d8537b77005ad4f342f14d8537b773a7005cc4f314d8537b77005cc4f314d0b88537b77645cc4f314d0c18537b77006294f314d0c18537b77005cc5ad4f314d8537b77005ad4f314d0c18537b77005cc5154f314d8537b77005cc4f31760c18537b77004f342f2ad14d8537b77005cc56b42f14d) else (if page < 13 then 0x8537b77006914f33348537b77006af69159342f0008537b77006af6915938537b75cc4f342f14d0f38537b76f25cc4f342f14d8537b77004f342f20714d8537b77005ca4f342f14d8537b77005cc42f28114d8537b77005cc4eb42f14d8537b77005cc4f32c114d8537b77005cc4f341a14d8537b77005cc4f34a542f8537b77005cc4f342f14c8537b77005cc4f344314d8537b77005cc4f338014d8537b77005cc4f342f15b8537b77005cc4f342f14388a7937005cc4f342f14d8537d57b77005cc4f342f8537b77005cc4f342f07a7b77005cc4f342f14d06f8537ab7005cc4f342f14d8537b77004f342f1f214d8537b77005bd4f342f14d8537b77005cc42f27b14d8537b77005cc4d942f14d8537b77005cc4f32bc14d8537b77005cc4f33ed14d8537b77005cc4f34a142f8537b77005cc4f342f14b8537b77005cc4f342f1878537b77005cc4f342f13a8537b77005cc4f344014d8537b77005cc4f338c14d8537b77005cc4f342f15a8537b77005cc4f342f1488857b77005cc4f342f14d8537005cc4f342f14d0e58537b77537005cc4f314d8537b77005cc4f314d0c88537b771d7005cc4f342f8537b77005cc4f342f0a08537b77005cc4f32bb14d8537b77005cc4f349e14d8537b77005cc50242f14d8537b77005cc4ca42f14d8537b77005cc4f343c14d8537b77005cc4f342f1598537b77005cc57d4f342f8537b77005cc4f32b414d8537b77005cc4f349014d8537b77005cc4f342f1848537b77006985cc42f14d8537b77005cc42f18e14d8537b77006645cc4f314d8537b77005cc55f4f342f8537b77005cc4f32ba14d8537b77005cc4f33d614d8537b77005cc4f349b42f8537b77005cc4f342f14a8537b77005cc4f342f2708537b77005cc4f342f1328537b77006044f342f14d8537b77005b84f342f14d else 0x8537b77006914f342f1598537b77005c04f342f1598537b77006914f342f1578537b77006914f337b1428537b77005cc59337b2e28537b77645cc4f342f0d58537b77645cc55b4f342f8537b77006914f342f1b98537b77005cc5934f336d8537b77006914f342f0a48537b77837006914f342f8537b77897006794f342f8537b77897004f342f1138537b77755cc59342f0d58537b77897006604f342f8537b77896916604f342f8537b77005cc5934f31b98537b77897006c54f342f8537b77757005cc42f1948537b77757006af42f1c48537b77897006914f337b8537b77647006914f31b98537b77757005cc59336d8537b77005cc59342f36d0008537b77005cc59336d8537b77897757006af42f8537b75cc4f342f2730d58537b76605cc4f342f1a38537b77006af6374f342f8537b77005cc5934f32fe8537b77005cc4f31260c18537b77005cc55b4f30c18537b77006c55cc4f30c18537b77005cc4f31940c18537b77006914f31c40c18537b77005cc5934c50c18537b77897006914f30c18537b77005cc5930d00c18537b77257006914f342f8537b77005cc5934f30b88537b77645cc5934f30c18537b77006af5cc45a42f8537b77006916614f342f8537b77005cc5604f30c18537b77006914f342f35c8537b77006914f30c109e8537b77005cc5930c10b18537b77006795934f342f8537b77006af5cc4f31768537b77006916794f342f8537b77006915cc4f31768537b77006914f342f1948537b77005cc5934f33348537b77006914f342f1188537b77006af68a4f342f8537b77907006914f342f8537b77006af5cc42f0d58537b77006af59342f1c48537b77006af6914f337b8537b77897006af59342f8537b77006af6914f30c18537b77006af59342f1948537b77006af6914f33348537b77006914f342f334)))) else (if page < 21 then (if page < 17 then (if page < 15 then 0x8537b77005cc4f342f0a28537b77005cc4f342f1908537b77006c54f342f1948537b77006c55cc4f33348537b77005274f342f1a38537b77005cc4f33453348537fe7b77005cc4f342f8537b77005cc4f342f2458537b77005cc4f342f0308537b77005cc4f342f3328537b77477005cc4f342f8537b77005cc4f342f2448537b77005cc4f342f0b68537b77005cc4f342f33087c7b77005cc4f342f04d8538147005cc5764f342f8537b77006914f342f1e48537b77005cc5934f33d67b77005cc4f342f27e04d85370068a5cc4f342f1c48537b77006af6394f342f8537b77005cc5934f32f38537b77004f342f2031188537b770068e4f342f1c48537b77005cc42f27e04d7b77005cc59342f27e04d85370069168a4f342f1c48537b77004f342f1c41138537b77006604f342f1c48537b77006c54f342f1c48537b77005cc42f2751948537b77006af42f27e1c48537b77006af42f2751c48537b77005cc5934f33878537b77006914f342f1bf8537b772c7006914f342f8538327b77004f342f1c48537b770061b4f342f1c48537b77006af4f349e42f8537b77006af51b42f1c48537b77005cc59342f2f38537b77006914f332a1c40008537b77005cc5932f38537b77005fe5934f342f8537b77006af5cc4f33ab8537b77006915fe4f342f8537b77006915cc4f33ab8537b77005cc4e042f1188537b77005cc58d4f337b8538277b77005cc4f337b8537b77005cc4f340a04d8537b77005cc4c542f1138537b77005cc55b4f337b8537b77006c55cc4f337b8537b77005cc4f337b1948537b77006914f340a1c48537b77005cc5934e037b8537b77006914f337b1c48537b77005cc5934c537b8537b77006914f342f1cd8537b77005cc5934f33768537006915b34f342f1c48537b77877006914f342f8537b77006af68c4f342f else (if page < 16 then 0x8537b778e7004f342f1b98537d07b77005cc4f342f8537b77005cc5984f342f8537b77005cc4f342f0158537b77005cc4f342f1128537b77006374f342f1138537b77005cc4f347042f8537b77005cc4f342f3378537b75cc4f342f2400d58537b75cc4f342f0d70c18537b75cc5a64f342f0d58537c87b77005cc4f342f8537b77197005cc4f342f8537b77005cc4f342f0108537b77005cc4f342f0d28537b77815cc4f342f0d58537b77005cc4f345c42f8537b77005cc4f342f3578537b77815cc55b4f342f8537b77006bb5934f342f8537b77006af5cc4f310e8537b76935cc4f342f0c18537b76935cc4f342f3458538227b77005cc4f342f8537b77005cc4f342f1248537b77005cc4f342f0498537b77005cc5594f342f8537b76935cc4f342f1138537b77006b55cc4f342f8537b77006bb55b4f342f0008537b77006bb4f342f8537b77005cc4f342f10e8537b77006935cc4f310e0008537b77005cc4f310e8537b77006796604f342f7b77005cc5934f342f0528537006c05cc5934f342f8537b75cc5934f342f0d88537b76b25cc5934f342f8538347b77005cc4f342f8537b77005cc4f342f1068537b77005cc4f342f0527b77006c55cc4f342f0520007b77005cc4f342f0528537b77006c05cc4f342f8537006c56c05cc4f342f0008537006c05cc4f342f8537b77927005cc4f342f8537b77005cc4f342f1058537b77005cc4f342f0d88537b76c55cc4f342f0d80008537b75cc4f342f0d88537b77006b25cc4f342f8537b76c56b25cc4f342f0008537b76b25cc4f342f8537b77005cc4f32ae1098537b77004f342f1a31948537b77005a64f342f1948537da7b77005cc4f342f8537b77005cc4f347142f8537b77005cc4f342f01d8537b77005cc4f342f1928537b77217005cc4f342f8537b77005cc4f346f42f else 0x8537005cc57a4f342f8537b77005cc4f342f0168537b77005cc4f342f1178537b771a7005cc4f342f8537b77005cc55d4f342f8537b77006394f342f1188537b77005cc4f347242f8537b77005cc4f342f3357b77005cc4f342f24104d8537b77006095934f342f8537b77006af5cc4f339188a7b77005cc4f342f04d7b77005cc4f342f09304d7b77005cc4f342f05604d7b77006eb5cc4f342f04d7b77005cc4f342f05003c7b77005cc5c04f342f04d8807b77005cc4f342f04d8537be7b77005cc4f342f8537b779a7005cc4f342f8537b77005cc4f342f0078537b770c7005cc4f342f8537b77006d75cc4f342f8537b77005cc4f343d42f8537b77006094f342f04d0008537b77006094f342f8537b77005cc4f342f3918537b77005c34f342f04d0008537b77005cc4f33918537b77005cc4ff42f04d8538277005cc5764f342f88a8537005cc5764f342f8537005cc5764f342f0667b77005cc58d4f342f0568537006cb5cc5764f342f7b77006ab5cc4f342f03c8537006a15cc4f342f37b8538257b77005cc4f342f8537b77005cc4f342f11a8537b77005cc4f342f04b8537b77005cc5744f342f8537006a15cc4f342f1188537b777e7005cc4f342f8537b77005cc4f342f1158537b77006c25cc4f342f8537b77005cc4f342f10b7b77005cc5934f342f06485377a7005cc5934f342f8537b77005934f342f1be8537b77006af5cc4f33748538507b77005cc4f342f8537b77005cc4f342f09b8537b77005cc4f342f0647b77817005cc4f342f0640007b77005cc4f342f0648537b777a7005cc4f342f85378177a7005cc4f342f00085377a7005cc4f342f8537b77817004f342f1be8537b77005cc4f342f1be0008537b77004f342f1be8537b77907005cc4f33748537b77005cc4f342f3740008537b77005cc4f3374)) else (if page < 19 then (if page < 18 then 0x8537b77005cc4f342f08a7b77005cc5934f342f06f8537ab7005cc5934f342f8537b77005934f342f1f28537b77006af5cc4f33ed8537b77005cc4f342f11c8537b77005cc58a4f342f8537b77006914f342f1f28537b77005cc5934f33ed8537b77005cc59b4f342f8537b77005cc55c4f342f8537b77005cc5954f342f8537b77005cc57b4f342f8537b770069160a4f342f8537b77005cc5934f338c8857b77005cc5934f342f8537005cc5934f342f0e58537b777d7005cc4f342f8537b77005cc4f342f0d68537b77857006914f342f8537b77005cc5934f30c88537b77005cc4f342f11b8537b77005cc5884f342f8537b77006af4f342f1e48537b77006915cc4f33d68537b77005cc5a34f342f8537b77005cc4f342f3368537b77005cc5944f342f8537b77005cc57c4f342f8537b77006af5fe4f342f8537b77005cc5934f33ab8537b77006c35cc4f342f8537b77005cc4f342f1958537b77006af68d4f342f8537b77005cc5934f31578537b77005cc4f342f1168537b77005cc56d4f342f8537b77005cc59f4f342f8537b77005cc4f342f3388537b77006916374f342f8537b77006915cc4f32fe8537b77005cc5974f342f8537b77005cc55e4f342f8537b77006af6294f342f8537b77005cc5934f335c8537b77006b85cc4f342f8537b77005cc4f342f1978537b77006af6794f342f8537b77005cc5934f31768928537b77005cc4f342f8537b77005cc4f342f06d8537b77a87005cc4f342f8537b77005cc4f342f0ee8537b77006e85cc4f342f8537b77005cc4f342f1ea8537b77005cc4f342f3e58538327b77004f342f1e48707b77005cc5934f342f8537005cc59357a4f342f8537d17b77005cc4f342f8667b77005cc4f342f1180008667b77005cc4f342f8537b77005cc57a4f342f7b77006b15cc4f342f118 else 0x8537b77757005cc4f31768537b77005cc4f32731768537b77005cc42f18e0c18537b77005cc4f34c11768537d97b77005cc4f31768537b770063b5cc4f31768537b77005cc4f317601c8537b77005cc4f31761678537b77647005cc4f31768537b77005cc4f31761398537b77005cc5ad4f31768537b77005cc4f32480b18537b77005cc5184f31768537b77005cc4f34bd1768537b77005cc4f324810c8537b77005cc4f31761368537b77004f342f2ad1398537b77005cc56b42f1398537b77005cc42f2a71398537b77006794f342f3458537b77006314f342f3458537b77005cc5a64f330f8537b77005cc4f33452fe8537b77006794f342f2da8537b77005cc4f34b41768537b77005cc56b42f2da8537b77006434f342f3458537b77005cc4f34c12678537b77005cc5a64f31768537b77005cc4f33451768537b77006794f342f0c18537b77005cc42f2a70c18537b77645cc4f342f3458537b75cc4f342f2b00c18537c67b77005cc4f342f8537b77257005cc4f342f8537b77005cc4f342f00e8537b77005cc4f342f0b88537b77645cc4f342f0c18537b77005cc4f33450c18537b77005cc4f32b00c18537b75cc4f33452b00c18537b77005cc56b4f30c18537b77006794f33450c10008537b77006794f30c18537b77005cc3452a70c18537b773a7005cc4f33458537b77005cc4f33450b88537b77647005cc4f33458537b77645cc4f33450c18537b75cc5934f342f0f38537b76f25cc5934f342f8537b77005934f342f2078537b77006af5cc4f341a8537b77005cc4f342f11d8537b77005cc5904f342f8537b77006914f342f2078537b77005cc5934f341a8537b77005cc5964f342f8537b77005cc5774f342f8537b770069160b4f342f8537b77005cc5934f338088a7937005cc5934f342f8538247b77005cc4f342f) else (if page < 20 then 0x8537b77757006794f342f8537b77005cc56b42f1a38537b770069e4f342f0c18537b770069e4f342f3458537b77006bf6794f342f8537b77005cc5654f31918537b770069e4f342f10c8537b77006985cc42f3318538147b77006794f342f8537b77006985cc42f1c40008537b770069842f1c48537b77006794f342f03c8537b77006794f342f37b0008537b77006794f337b8537b77647006794f342f0008537b778970069842f8537b77006985cc42f1a38537b77006794f342f09e8537b77005cc56b42f36d8537b77006985cc42f1768538147b77005cc4f31768537b77005cc4f32b61768537b77005cc4f317603c8537b77005cc4f337b1768537b77005cc4f32b01768537d97b77005cc4f342f8537b77005cc4f348542f8537b77005cc4f342f01c8537b77005cc4f342f1678537b77005cc4f347f42f8537b77005cc4f342f3058537b77005a64f31c41768537b77005b35a64f31768537b77897005a64f31768537b77895cc5a64f31768538297b77005cc4f31768537b77005cc4f32361768537b77005cc42f2a70328537b77005cc5a44f31768537b75cc5a64f31a31768537b77006985cc5a61768537b77006985cc4f31760008537b77006985cc1768537b77005cc5a618e1768537b77005cc42f18e1760008537b77005cc18e1768537b77006645cc4f317688a8537b77005cc4f31768537b77005cc4f31760668537b77937005cc4f317685383f7b77005cc4f31768537b77005cc4f31760dd8537b77005cc4f31760568537b77006cb5cc4f317685382e7b77005cc4f31768537b77005cc4f31c41768537b77005cc42f2a703c8537b77005cc5b34f31768537b77897005cc4f31768537b77005cc4f31a31768538207b77005cc4f31768537b77005cc4f32751768537b77005cc42f18e03c8537b77005cc4f34c5176 else 0x8537b75cc5a54f342f1ab8537b77005cc5634f342f8537b770066d4f342f33a0008537b770066d4f342f8537b77005cc4f342f17d8537b77005cc5a54f317d0008537b77005cc4f317d8537b77005cc4f342f0c88537b77005cc4f33430c88537b77004f342f1c41a38537b77005b34f342f1a38537de7b77005cc4f342f8537b77005cc4f346042f8537b77005cc4f342f01f8537b77005cc4f342f1998537b75cc5a64f342f1a38537b77897004f342f1a38537b75a64f342f1c41a38537b75b35a64f342f1a38537b77895a64f342f1a38538237b77005cc4f342f8537b77005cc4f342f11f8537b77005cc4f342f04a8537b77005cc5624f342f8537b77005cc4f342f1918537b77005cc4f342f3318537b77006644f342f1c48537b77005cc56b4f337b8537b77897006644f342f85382e7b77006794f342f8537b77006794f342f1c48537b77005cc5654f303c8537b77005cc5654f337b8537b77006794f342f1a38537b77005cc5654f33458537b77006985a642f1c48537b77006794f337b3458537b77647006794f33458537b77646794f342f3458538027b77006794f342f8537b77006985cc42f2368537b77006794f342f0328537b77006794f342f33a8537b76985cc5a642f1a38537b770069e5654f342f8537b770067956b42f3450008537b770067956b42f88a8537b77006794f342f8537b77006794f342f0668537b77937006794f342f85383f7b77006794f342f8537b77006794f342f0dd8537b77006794f342f0568537b77006cb6794f342f8538317b77006794f342f8537b770069e4f342f11f8537b77005cc5654f304a8537b77006796674f342f8537b770069e4f342f1138537b77005cc5654f30c18538207b77006794f342f8537b77005cc56b42f1c48537b770069e4f342f03c8537b770069e4f342f37b))) else (if page < 24 then (if page < 22 then 0x8537005b35a64f342f2368537b77005a64f342f1c488a8537005cc4f342f2368537005cc4f342f2360667b77005cc4f342f23d0568537006cb5cc4f342f2368537b77004f342f23d1c48537b77005c04f342f2367b77005cc4f342f2c503c8537005cc5b34f342f2368537e87b77005cc4f342f8537b77005cc4f342f3408537b77005cc4f342f0258537b77005cc4f342f23385383f7b77005cc4f342f8537b77005cc4f342f3508537b77005cc4f342f0dd8537b77005cc4f342f34b8537b77005cc4f34aa42f8537b77005cc4f342f2dd7b77005cc4f342f2c50328537b76df5cc4f342f3458537b77005f14f342f3458537b77005cc4cf42f3458537b77005cc4f338c3458537b77005cc4f342f33a8537b77005cc4f32bd0328537b77005cc4f340a0328538027b77005cc4f342f8787b77005cc4f342f0328537bc7b77005cc4f342f8537b779f7005cc4f342f8537b77005cc4f342f0058537b77006db5cc4f342f8537b76ef5cc4f342f0328537b77005cc4f343942f8537b77005f14f342f0320008537b77005f14f342f8537b77005cc4f342f3bc8537b77005cc4e542f0320008537b77005cc4f33bc8537b77005cc4f342f38c8537b77005cc4f340d0328538027005cc4f342f33a8777b77005cc4f342f3458537005cc5a64f342f2378537b75cc5a64f342f1ab8537b770066d4f342f3458537b77005cc5a64f317d8537b77005cc4f33450c88537b77005cc4f342f0328537b77005a54f342f1c48537b77005cc4f340a33a8538017b77005cc4f342f8777b77005cc4f342f33a0008777b77005cc4f342f8537b77005cc4f342f2378537005cc5a54f342f2370008537005cc4f342f2378537b77005cc4f342f0318537b77005cc4f342f3398537b77005cc4f342f2368537005cc5a44f342f2368537b77005cc4f342f1ab else (if page < 23 then 0x8537b77005a64f342f1e48537b77005cc4f33d63458537b77005cc4f342f23a8537b77005cc4f342f3428537b77005cc4f348642f8537b77005cc4f342f2dc8537b77006044f342f3458537b77005cc4ca42f3458537b77005cc4f343b3458537b77005cc4f33ab3458537b77005cc4f342f34e8537b77005cc4f342f3418537b77005cc5644f342f8537b77005cc4f342f13c8537b77005cc4f342f22c8537b77005cc4f34903458537b77005cc4f345042f8537b77005cc4f342f2388537b772a7005cc4f342f8537b77005cc4f33873458537b77005a64f342f1bf8537b773c7005cc4f33458537b773b7005cc4f33458537b772a7004f342f1c48537b770b5cc4f342f3458537b77005fe4f342f3458537b77005cc4ce42f3458537b77005cc4f337b3458537b775a5cc4f342f3458537b77005a64f342f1cd8537b77005cc4f33763458537005b35a64f342f1c48537b775a7005cc4f33458537b775a5cc4f337b3458537b75c05a64f342f1ab8537b77005cc4f33ed37b8537b77005cc4f342f2308537b77005a64f342f0a48537b774b7005cc4f33458537b77897004f342f2308537b77005a64f342f2300008537b77004f342f2308537b77895cc4f342f2308537b75cc5a64f342f2300008537b75cc4f342f2308537b77005cc4f33ed3458538027005cc4f337b34588f8537b77005cc4f342f8537b77005cc4f342f06b8537b77a37005cc4f342f88a8787b77005cc4f342f8538027005cc4f342f0668537b77006e35cc4f342f8787b77005cc4f342f0568538027006cb5cc4f342f8537b77005cc4f342f1e18537b77005cc4f342f3d38538027b77005cc4f33ed8537b77005cc4f342f3ed0008537b77005cc4f33ed8538297b77004f342f1c48787b77005cc4f342f03c8538027b77005cc4f337b8538027005cc4f342f37b else 0x8537b77005cc4f342f00d8537b77005cc4f342f0b785373a7005cc4f342f0b88537b775a7005cc4f342f8537b775a5cc4f342f0b88537b77005cc4f345942f8537b77005cc4f342f35d8537b77005cc4f33530b885384d7b77005cc4f342f8537b77005cc4f342f0a48537b77005cc4f342f05f8537b774b7005cc4f342f8537b77645cc4f32b00c18538177b77005cc4f342f8537b77005cc4f342f1b18537b77005cc4f342f03f8537b77005cc4f345642f8537b77005cc4f342f15d8537b77005cc4f342f2fa8537b77006294f342f1c48537b77005cc4f345a37b8537b77897006294f342f8537b77005cc4f345a0c18537b77005ac4f342f1c48537b77005cc4f337b35c8537b77647005cc4f335c8538057b77005cc4f342f8537b77005cc4f342f22d8537b77005cc4f342f0358537b77005cc4f342f3598537b77005cc5684f342f8537b77005cc4f342f1668537b77005ad4f342f09e8537b77005cc4f336d0c18537b77005cc51542f0b18537b77006254f342f0c18537b77005cc4c342f0c18537b77005cc4f335c0c18537b75cc4f342f3450f38537b76f25cc4f342f3458537b77004f342f3452078537b77005cc4eb42f3458537b77005a64f342f2078537b77005cc4f341a3458537b77005cc4f342f23e8537b77005cc4f342f3448537b77005cc4f34433458537b77005cc4f33803458537b77005cc4f342f3518537b77005cc4f342f33b88a7937005cc4f342f3458538007b77005cc4f342f8537b77005cc4f342f0817b77005cc4f342f34506f8537ab7005cc4f342f3458537b77004f342f3451f28537b77005cc4d942f3458537b77005a64f342f1f28537b77005cc4f342f23b8537b77005cc4f346542f8537b77005cc4f34403458857b77005cc4f342f3458537005cc4f342f3450e58537b77537005cc4f3345)) else (if page < 26 then (if page < 25 then 0x8537b75cc4f342f2b10c18537b77005cc5224f30c18537b77004f342f2301a38537b77005cc4f32c40c18537b75cc4f342f2301a38537b75cc4f342f2c40c188b8537b77005cc4f342f8537b77005cc4f342f0678537b77977005cc4f342f85f7b77005cc4f342f06685f7b77937005cc4f342f8537b77005cc4f342f0ec88685f7b77005cc4f342f8537c67005cc4f342f0dd8537b77005cc4f342f1cf8537b77005cc4f342f38985f7b77005cc4f342f03c8537c67005cc4f342f37b7b772f7005cc4f342f0668537937257005cc4f342f8538437b77005cc4f342f8537b77005cc4f342f0bd8537b77005cc4f342f0598537b77227005cc4f342f85383f7257005cc4f342f8537257005cc4f342f0dd8537b772c7005cc4f342f8537b77005cc4f342f0568537b77006cb5cc4f342f7b773d7005cc4f342f03c85373a7005cc4f342f37b8537b77257004f342f1a38537b77697005cc4f342f8537b77005cc4f342f0b47b773d7005cc4f342f00e8567b77005cc4f342f0c18537b17005cc4f342f0c18537b770b5cc4f342f0c18537b77005dc4f342f0c18537b77005cc4dc42f0c18537b77005cc4f33ed0c185f7b77005cc4f342f00e8537b87b77005cc4f342f8537b87005cc4f342f00e0008567b77005cc4f342f8537b77af7005cc4f342f8537b17005cc4f342f00e0008537af7005cc4f342f8537b77005cc4f342f0018537b770b7005cc4f342f8537b770b5cc4f342f00e8537b77005cc4f343242f8537b77005dc4f342f00e0008537b77005dc4f342f8537b77005cc4f342f3fc8537b77005cc4e942f00e0008537b77005cc4f33fc8537b77005cc4f341800e8537c67005cc4f342f0b88537b775a5cc4f342f0c18537b77005cc4f334b0c18537b77005cc4f32b00b88537c57b77005cc4f342f8537b77267005cc4f342f else 0x8537b77004f342f1a30a48537b77837004f342f1a38537b77004f349042f1c48537b77005cc5224f337b8537b77897004f349042f85381c7b77005cc4f342f8537b77005cc4f342f15e8537b77005cc4f342f0448537b77005cc4f348d42f8537b77005cc4f342f1898537b77005cc4f342f3068537b77004f342f32d1a38537fc7b77005cc4f342f8537b77005cc4f342f2938537b77005cc4f342f02e8537b77005cc4f342f2fb8537b77005cc54e4f342f8537b77005cc4f342f24a8537b77005cc4bc42f1138537b77006374f342f1a38537b77005cc4f34901398537b77005cc51642f1a38537b77005cc4f332f1a38537b75cc4f342f0f30c18537b76f25cc4f342f0c18537b77004f342f2070c18537b77005cc4eb42f0c18537b77005cc4f32c10c18537b77005cc4f341a0c18537b77307005cc4f342f8537b77005cc4f342f0c08537b77005cc4f342f0cb8537b77005cc4f342f0b988a7937005cc4f342f0c18537c47b77005cc4f342f8537b77005cc4f342f0747b77005cc4f342f0c106f8537ab7005cc4f342f0c18537b77004f342f1f20c18537b77005cc4d942f0c18537b77005cc4f32bc0c18537b77005cc4f34680c18537b77005cc4f342f0ca8857b77005cc4f342f0c18537005cc4f342f0e50c18537b774e7005cc4f342f8537b77297005cc4f342f8537b77005cc4f342f0bf8537b77005cc4f342f22e8537b77005cc4f342f0b28537b77006044f342f0c18537b77005cc4ca42f0c18537b77005cc4f343b0c18537b77005cc4f33ab0c18537b77005cc4f342f0c98537b77005cc4f342f0be8537b77005cc5814f30c18537b77005cc4f31570c18537b77005cc4f345842f8537b77005cc4f342f09f8537b77005cc4f32b30c18537b76df5cc4f342f0c18537b77005fe4f342f0c18537b77005cc4ce42f0c1) else (if page < 27 then 0x8537de7b77004f342f1f28537b77005cc4f342f1f20008537b77004f342f1f288386c7b77005cc4f342f8537de7b77004f342f1c48537de7005cc4f342f1c48537f27b77005cc4f337b8537ed7b77004f342f1d68537b77005cc4f342f1d60008537b77004f342f1d68537de7b77005cc4f33998537b77005cc4f342f3990008537b77005cc4f339985370062a4f342f1c41a388a8537005cc4f346042f8537005cc4f346042f0667b77005cc4f346b42f0568537006cb5cc4f346042f8538187b77005cc4f342f8537b77005cc4f342f19e8537b77005cc4f342f0408537b77005cc4f345d42f8537b77005cc59a4f342f8537b77005cc4f342f13d8537b770062d4f342f1c48537b77005cc4f346b37b8538147005cc4f346042f85370062a5cc4f342f1c48537b77005cc4f346842f7b770062d5cc4f342f01f8537b76e95cc4f342f1a38537b770060a4f342f1a38537b77004f342f20301f8537b77005c04f342f01f86c7b77005cc4f342f01f8537ba7b77005cc4f342f8537b77a67005cc4f342f8537b77005cc4f342f0038537b76f15cc4f342f01f8537b77005cc4f344042f8537b770060a4f342f01f8537b77005cc4f343542f8537b77005cc4f342f3d98537de7005cc4f342f19986b7b77005cc4f342f1a385370062b5cc4f342f1a38537b75cc5a94f342f1a38537b77857004f342f1a38537b77004f342f2031998537b77005c04f342f1998537dd7b77005cc4f342f86b7b77005cc4f342f19900086b7b77005cc4f342f8537b77005cc4f346142f7b770062f5cc4f342f1990008537005cc4f346142f8537b77005cc4f342f01e8537b77005cc4f342f19885370062a5cc4f342f1998537b75cc5ab4f342f1998537b77537005cc4f342f8537b77857004f342f1998537b77005cc4f348f42f8537b77005cc4f342f2ff else 0x8537b77005ca4f342f1a38537b77005cc42f2811a38537b77005cc4f341a1a38537b77005cc4f346d42f8537b77005cc4f342f1a28537b770060b4f342f1a38537b77005b44f342f1a38537b77005cc4f342f1ad8537b77005cc4f342f19a88a7937005cc4f342f1a38537dc7b77005cc4f342f8537b77005cc4f342f07c7b77005cc4f342f1a306f8537ab7005cc4f342f1a38537b77005bd4f342f1a38537b77005cc42f27b1a38537b77005cc4f33ed1a38537b77005b64f342f1a38857b77005cc4f342f1a38537005cc4f342f1a30e58537b77005cc4f32b00c88537b75cc4f342f2b00ec8537b772c5cc4f342f1a38537b77005b54f342f1a38537b77004f342f1bf1a38537b772c7004f342f1a38537b772c4f342f1c41a38537b75ab4f342f1c41a38537b77004f342f1f21c48537b77005cc50242f1a38537b77005cc4f33ab1a38537b77005cc4f342f1ac8537b77507005cc4f342f8537b77004f342f1cd1a38537b77005b24f342f1a38537005b34f342f1c41a38537b77877004f342f1a38537b77507005cc4f337b8537b77847004f342f1a38537b77004f342f1e41a38537b77005bb4f342f1a38537b77005cc4f346442f8537b77005cc4f342f1a08537b77005cc4f342f2948537b77005cc4f342f13b8537b77005fe4f342f1a38537b77005b84f342f1a38537b77005cc4ff42f1a38537b77005cc4f33c21a38537b77005cc4f342f1a98537b77005cc4f342f19f8537b77005cc4f348e42f8537b77005cc4f342f1148537b77004f342f1f21a38537de7004f342f1c41a38537b77005cc42f2761a38537b77005cc4f33991a388d8537b77005cc4f342f8537b77005cc4f342f0698537b779c7005cc4f342f88a86c7b77005cc4f342f8537de7005cc4f342f06686c7b77005cc4f342f0568537de7006cb5cc4f342f))))) else (if page < 42 then (if page < 35 then (if page < 31 then (if page < 29 then 0x8537b77647005cc4f334b8857b77647005cc4f342f8537647005cc4f342f0e58537b77005cc4f342f0a88537b77577005cc4f342f8537b776b7005cc4f342f8537b77005cc4f342f36f7b77005cc4f342f06003c7b77747005cc4f342f03c8537b77657005cc4f342f8537b774f7005cc4f342f8537b77757005fe4f342f8537b77757005cc4f33ab8537b77897005fe4f342f8537b77647005cc4f33ab7b77005cc4f34e042f05f8537737005cc4f342f37b8537b777f7005cc4f342f8537b77005cc4f342f1ba8537b778970068d4f342f8537b77647005cc4f31577b77647005cc4f342f06485377a7647005cc4f342f8537b77647004f342f1be8537b77757005cc4f33748537b77004f342f1c41b98537b77005b34f342f1b98537e07b77005cc4f342f8537b77005cc4f344e42f8537b77005cc4f342f0218537b77005cc4f342f1b68537b77005cc4f349342f8537b77005cc4f342f2f98537b77005cc4f32b409e8537b77817005cc4f336d8537b77757006884f342f8537b77757005cc4f31618537b77005af4f342f1c48537b77005cc4f337b36d8538067b77005cc4f342f8537b77005cc4f342f22b8537b77005cc4f342f0368537b77005cc4f342f36a8537b77005cc5714f342f8537b77006884f342f36d0008537b77006884f342f8537b77005cc4f342f1618537b77005cc5b04f31610008537b77005cc4f31618537b77897004f342f1b98537b77647005cc4f336d87c7b77005cc4f342f05f85381474b7005cc4f342f8537b77645cc4f342f0ec8537b77646e35cc4f342f7b77005cc4f342f2bd05f8537837005cc4f342f1c48537b778972c5cc4f342f8537b77645cc4f342f3508537b77647005fe4f342f8537b77897005cc4f33ab8537b75cc4f342f1a30f38537b76f25cc4f342f1a38537b77004f342f2071a3 else (if page < 30 then 0x8537b77897004f342f2078537b77647005cc4f341a8537b77667005cc4f342f8537b774c7005cc4f342f88a7937647005cc4f342f8538497b77005cc4f342f8537b77005cc4f342f0917b77647005cc4f342f0728537b37647005cc4f342f8537b77647004f342f2018537b77757005cc4f34058958537b77005cc4f342f8537b77005cc4f342f07284d7b77005cc4f342f0720007b77005cc4f342f0728537b77b37005cc4f342f8898537b37005cc4f342f0008537b37005cc4f342f85384d7b75cc4f342f0ec85384d7b77004f342f2018537b77005cc4f342f2010008537b77004f342f20185384f7b77005cc4f34058537b77005cc4f342f4050008537b77005cc4f34058538527b77004f342f1f28537c27b77005cc4f342f8537b774d7005cc4f342f8537b77005cc4f342f00b8537b77005cc4f342f0a38537b772c5cc4f342f0a48537b770062c4f342f0a48537b77005cc4f344f42f8537b77005cc4f342f36e7b77005cc4f342f0ae05f7b77005cc4f342f06605f7b77937005cc4f342f05f8897b77005cc4f342f05f8537c07b77005cc4f342f8537b77967005cc4f342f8537b77005cc4f342f0098537b77005cc4f344142f8537b77005cc4f342f38885384d74b7005cc4f342f7b775f7005cc4f342f06685379374b7005cc4f342f85384a7b77005cc4f342f8537b77005cc4f342f0a78537b77005cc4f342f05c8537b77487005cc4f342f8537837005cc4f342f0a48537b777c7005cc4f342f8537b77005cc4f342f0a17b77647005cc4f342f06f8537ab7647005cc4f342f8867b77005cc4f342f05f85383f74b7005cc4f342f8537b77647004f342f1f28537b77757005cc4f33ed8537b77897004f342f1f28537b77647005cc4f33ed7b77005cc4f342f0f005f85374b7005cc4f342f0dd8537b778970062c4f342f else 0x8537b770066d4f342f37b8537b77005cc5c04f317d8537b77005cc4f340a0c88538267b77005cc4f342f8537b77005cc4f342f1198537b77005cc4f342f04c8537b77005cc5754f342f8537b77005cc4f342f0d48537b77005cc55a4f342f8537b77005cc4f342f1938537b77005cc4f342f3338537b770068f4f342f1c48537b77005cc58f4f337b8537b77006904f342f1c48537b77005cc58e4f337b8537b770068d4f342f1c48537b77005cc5814f337b8537b77005cc4f32bd1578537b77005cc4f32b61578537b77005cc4f337b1578537d87b77005cc4f342f8537b77005cc4f349542f8537b77005cc4f342f01b8537b77005cc4f342f1458537b77207005cc4f342f8537b77005cc4f348142f8537b77005c54f342f1578537b77005cc4f347d42f8537b77005cc4f342f3088537b77004f342f2ac1428537b77005cc4f340a2f38537b77005cc58642f2e28537b770064d4f342f37b8537b77005cc4f34e02608537b77005cc4f340a1578538147005cc4f342f37b8537b770061b4f342f37b8537b77005cc4ce42f37b7b77005cc4f342f2bd03c87c7b77005cc4f342f03c8537bd7b77005cc4f342f8537b779d7005cc4f342f8537b77005cc4f342f0068537b77005cc4f342f0378537b77005fe4f342f03c8537b77005cc4e242f03c8537b77005cc4f340a03c8537b77005cc4f32bd03c7b77005cc4f340a2bd03c8538147b77005cc4f337b87c7b77005cc4f340a03c8537f37b77005cc4f337b8537b77005cc4f340a0378537b77006df5cc4f337b8537b77005cc50c4f337b8537b77005fe4f340a03c0008537b770061b4f337b8537b77005cc4e240a03c8537b77005cc4f342f0a98537b77617005cc4f342f8537b77645cc4f342f0f38537b77646f25cc4f342f8537b77647004f342f2078537b77757005cc4f341a)) else (if page < 33 then (if page < 32 then 0x8537b77005f94f342f37b8537b77005cc4e442f37b8537b77005cc4f340c37b8537b77005cc4f342f3768537b77005cc4f32bd03785380f7b77005cc4f342f8797b77005cc4f342f0378537a17005cc4f342f0378537b770a7005cc4f342f8537b77006dc5cc4f342f8537b77005cc4f343a42f8537b77005f94f342f0370008537b77005f94f342f8537b77005cc4f342f3b08537b77005cc4e442f0370008537b77005cc4f33b08537b77005cc4f342f3808537b77005cc4f340c0378797b77005cc4f342f3768537005cc5b34f342f1cd8537b77005cc4f337b0858537b77005cc4f342f1cd8537005cc5b24f342f1cd8537b77597005cc4f342f8537b77005cc4f342f1af8537b77005cc57f4f342f8537b77005cc4f342f15c8537b77005cc4f342f0858537b77005cc4f33760858537b77004f342f2031c48537b77005c04f342f1c48537e57b77005cc4f342f8537b77005cc4f342f3878537b77005cc4f342f0228537b77005cc4f342f1bf8537005cc5b34f342f1c485382e7b77004f342f1c48537005b34f342f2031c48537005c05b34f342f1c485382e7005b34f342f1c485384c7b77005cc4f342f8537b77005cc4f342f0a58537b77005cc4f342f05e8537b774a7005cc4f342f8537b775a5cc4f342f0dd8537b775a6cb5cc4f342f8537b77005cc4f342f1b88537b77005cc4f342f36c8537b775a7005cc4f33ed8537b75cc4f342f1ae0dd8537b76eb5cc4f342f1ab8537b77004f342f1c41ab8537b77005b34f342f1ab8537df7b77005cc4f342f8537b77005cc4f345e42f8537b77005cc4f342f0208537b77005cc4f342f19c8537b77005cc4f349142f8537b77005cc4f342f2fc8537b75cc4f342f2b20b88537b77005cc4f340a34b8537b775a5cc4f342f33a8777b77005cc4f342f37b8537005cc5c04f342f237 else 0x8537b77005cc4f341037b8537b77005cc4f342f3848537b77005cc4f342f3788537b77005cc5804f342f8537b77005cc4f342f21a8537b77005cc4f349e37b8537b770061e4f342f37b8537b77005cc4ca42f37b8537b77005cc4f344637b8537b77005cc4f343742f8537b77005cc4f342f1ce8537e37b77005cc4f342f8537f57b77005cc4f337b8537b77005cc4f337b3508537f47b77005cc4f337b85382b7b77004f342f1c48537b77005cc5264f337b8537bd7005cc4f342f37b8537b77005fe4f342f37b8537b77005cc4e242f37b8537b77005cc4f340a37b8537b77005cc4f342f2218537b77005c04f342f0228538077b77005cc4f337b8537b77006e35cc4f337b8537b77005cc4f337b1e48838537b77004f342f2218537b77005c04f342f2210008537b77004f342f2218837b77005cc4f342f2217b77005cc5c04f342f2210007b77005cc4f342f2218537b77005cc4f341a37b8797b77005cc4f340a37b8537b77a47005cc4f342f8797b77005cc4f342f0668797b77937005cc4f342f8537b77005cc4f342f0eb8537b77006e25cc4f342f8868797b77005cc4f342f85380f7005cc4f342f0dd8537b77005cc4f342f1e38537b77005cc4f342f3d585380f7b77005cc4f341a8537b77005cc4f342f41a0008537b77005cc4f341a85382d7b77004f342f1c48797b77005cc4f342f03c85380f7b77005cc4f337b85380f7005cc4f342f37b8537005c05b34f342f1cd7b77005cc4f342f2280668537937005cc4f342f1cd85383f7005cc4f342f1cd8537005cc4f342f1cd0dd7b77005cc4f342f2c303c88a8537b77005cc4f342f8537b77005cc4f342f0668537b772d7005cc4f342f8537b77005cc4f342f33f8537b77005cc4f349f42f8537b77005cc4f342f2e57b77005cc4f342f2c30378537a17005cc4f342f37b) else (if page < 34 then 0x8537b77005c54f342f01a8537b77005cc4ff42f01a8537b77005cc4e242f01a8537b77005e54f342f03c8537b77005cc4e742f03c8537b77005cc4f341503c8537b77005fe4f342f02c8537b77005c44f342f02c8537b77005cc4ff42f02c8537b77005ea4f342f03c8537b77005cc4e642f03c8537b77005cc4f341003c8537b75cc4f342f37b0f38537b76f25cc4f342f37b8537b77004f342f37b2078537b77005cc4eb42f37b8537b77005b34f342f2078537b77005cc4f342f2248537b77005cc4f344242f8537b77005cc4f344337b88a7937005cc4f342f37b8538087b77005cc4f337b7b77005cc4f342f40a06f8537ab7005cc4f342f37b8537b77004f342f40a1f28537b77005cc4e842f37b8537b77005c04f342f1f28537b77005cc4f341837b8537b77005cc4f342f1f88537b77005cc4f342f37a8537b77005cc4f346c37b8537b77005cc4f337b34b8537b77005cc4f346242f8537b77005cc4f342f33c8537b77005cc4f344037b8537b77005cc4f340d37b8537b77005cc4f342f3868537b77005cc4f342f37785383c7005cc4f342f37b8537005cc4f342f37b0e58537b77527005cc4f342f8537b77005cc4f342f0bb7b77005cc4f342f37b06f8357b77005cc4f342f37b8537b77004f342f37b1f28537b77005cc4d942f37b8537b77005b34f342f1f28537b77005cc4f342f2238537b77005cc4f346837b8537b77005cc4f343e42f8857b77005cc4f342f37b8537005cc4f342f40a0e58537b77537005cc4f337b8537b77005c04f342f1e48537b77005cc4f341537b8537b77005cc4f342f1e58537b77005cc4f342f3798537e57005cc4f342f37b8537005cc4f34c642f37b8537b77005cc4f349942f8537b77005cc4f342f2e48537b77006044f342f37b8537b77005cc4e142f37b8537b77005cc4f343b37b else 0x8538147b77005cc4f33ab8538117b77005cc4f342f8537b77005cc4f342f1c98537b77005cc4f342f0398537b775d7005cc4f342f8537b77005cc4f342f1a88537b77005cc5854f342f8537b77005cc4f342f1548537b77005cc4e22bd03c7b77005cc4e242f2bd03c87c7b77005cc4e242f03c85b8537b77005cc4f33ab8537e17b77005cc4f33ab8537b77005cc4ce42f0068537b77005cc4e242f0378537b77117005cc4f33ab8537b77006db5cc4f33ab8537b77005cc4e242f00e8537b77005cc4e242f0328537b77005cc5104f33ab8537b77005fe4e242f03c0008537b77005cc5103ab8537b77005cc4ca42f3ab8537b77005c54e242f03c0008537b77005cc4ca3ab8537b77005cc4f34483ab88a8537b77005cc4f33ab8537b77005cc4f34100668537b77005cc4f33ab0668537b77937005cc4f33ab8868537b77005cc4f33ab8537b77005cc4f34100dd8537b77005cc4f33ab0568537b77006eb5cc4f33ab85383f7b77005cc4f33ab8537b77005cc4f33ab0dd8537b77005cc4f34100568537b77006cb5cc4f33ab8838537b77005cc4f33ab8537b77005cc4f34101c48537b77005cc4ce42f03c85382e7b77005cc4f33ab8537b77005cc4f33ab1c487e8537b77005cc4f33ab8537b77005cc4f34141c48537b77005cc4ca42f03c8538207b77005cc4f33ab8537b77005cc4f33c21c48537b77005cc4e142f03c87a8537b77005cc4f33ab8537b77005c54f342f1c98537b77005cc4f33ab0398537b77005cc4f34103788537b77005b84f342f1c48537b77005cc4f341001a8537b775d7005cc4f33ab8537b77005c54f342f1a88537b77005cc4f33ab0be8537b77005cc4f33ab3418537b77005cc4f33c22e28537b77005cc5874f33ab8537b77005c44f342f1548537b77005cc4f33c21498537b77005cc4f33ab2e8))) else (if page < 38 then (if page < 36 then 0x8537b77005cc4f342f1508537b77005cc4f342f2f08838537b77005fe4f342f8537b77005cc4f343b03c85382e7b77005fe4f342f8537b77005fe4f342f1c48537b77005cc4f344603c8537b77005fe4f32bd03c7b77005fe4f342f2bd03c87c7b77005fe4f342f03c8537bd7b77005fe4f342f8537b77a17005fe4f342f8537b77005fe4f342f0068537b77005fe4f342f0378537b770b7005fe4f342f8537b77006ef5fe4f342f8537b77005fe4f342f00e8537b77005fe4f342f0328537b77006044f343b42f8537b77005fe4ff42f03c0008537b77005fe4ff42f88a8537b77005fe4f342f8537b770061b4f342f0668537b77005fe4f342f0668537b77937005fe4f342f8868537b77005fe4f342f8537b770061b4f342f0dd8537b77005fe4f342f0568537b77006eb5fe4f342f85383f7b77005fe4f342f8537b77005fe4f342f0dd8537b770061b4f342f0568537b77006cb5fe4f342f8848537b77005fe4f342f85382f7b77005fe4f342f8537b77006044f342f1c18537b77005cc4f344603d8537b77005cc4f343b3838537b778a7005fe4f342f8537b770061e4f342f19f8537b77005cc4f343b0c38537b77005cc4f343b34d87e8537b77005fe4f342f8537b77005cc50c42f1c48537b77006044f342f03c8538207b77005fe4f342f8537b77005cc4ff42f1c48537b770061e4f342f03c8537b77006b05fe4f342f8537b77005cc4f343b1508537b770061e4f342f1498537b77005cc50242f2f087c8537b77005fe4f342f8537b77005cc51042f1c40008537b770051042f1c48538147b77005fe4f342f8537b77005cc50242f1c48537b770061b4f342f03c8537b770061b4f342f1428537b77005cc4ff42f2f38537b77005cc51042f3ab87c8537b77005cc4f33ab8537b77005c44f342f1c48537b77005cc4f33ab03c else (if page < 37 then 0x8537b77005cc4f342f0808537a17005cc4f342f00685a7b77005cc4f342f03c8537b77035cc4f342f03c8537b76f85cc4f342f03c8537b77005d24f342f03c8537b77005cc4ee42f03c8537b77005cc4f341a03c85a7b77005cc4f342f0068537b77037005cc4f342f8537b77035cc4f342f0060008537b77035cc4f342f8537b77006f55cc4f342f8537b76f85cc4f342f0060008537b76f55cc4f342f8537b77005cc4f343042f8537b77005d24f342f0060008537b77005d24f342f8537b77005cc4f342f4218537b77005cc4ee42f0060008537b77005cc4f34218537b77005cc4f341a0068537bd7005cc4f342f0378537b77005f94f342f03c8537b77005cc4e442f03c8537b77005cc4f340c03c8538407b77005cc4f342f8537b77005cc4f342f0db8537b77005cc4f342f0578537b77006d05cc4f342f8868537b770b5cc4f342f8537b770b5cc4f342f0568537b770b5cc4f342f0dd8537b770b6cb5cc4f342f8537b77005cc4f342f1a58537b77005cc4f342f3498537b76ee5cc4f342f0dd8537b76ee6cb5cc4f342f85383f7b76db5cc4f342f8537b76ee5cc4f342f05685383d7b77005cc4f342f8537b77005cc4f342f0e18537b77005cc4f342f0548537b77006c95cc4f342f8537b77006db4f342f1c48537b77567005cc4f342f8537b77005cc4f342f0c68537b76ef5cc4f342f00e8537b87005cc4f342f03c8537b17005cc4f342f03c8537b77005dc4f342f03c8537b77005cc4e942f03c8537b77005cc4f341803c8537b770b5cc4f342f0328537b77005f14f342f03c8537b77005cc4e542f03c8537b77005cc4f340d03c8537b77004f344842f1c48538157b77005cc4f342f8537b77005cc4f342f1c18537b77005cc4f342f03d8537b77005cc4f342f3838537b77005cc4f342f0c38537b77005cc4f342f34d else 0x8537b77005cc4f32c103c8537b77005cc4f342f0888537b77005cc4f344303c88a7937005cc4f342f03c8537b77a57005cc4f342f8537005cc4f342f09603c8537ab7005cc4f342f03c8537b77004f342f20603c8537b77005cc4e842f03c8537b77005cc4f32c003c8537b77005cc4f342f0fb8537b77005cc4f344003c85383c7005cc4f342f03c8537005cc4f342f0e503c8537b77006e65cc4f342f7b77005cc4f342f06f03c8357b77005cc4f342f03c8537b77004f342f1f203c8537b77005cc4d942f03c8537b77005cc4f32bc03c8537b77005cc4f33ed03c8537e47b77005cc4f342f8537b77005cc4f342f03b8537b77005cc4f342f0e28537b77005cc4f342f0338537b77005cc4f342f0878537b77005cc4f342f0388857b77005cc4f342f03c7b77005cc4f342f10303c8537b77006d15cc4f342f8537b77005cc4f342f00f8537b77005cc4f32be03c8537e27b77005cc4f342f8537b77005cc4f342f03a86e7b77005cc4f342f03c7b77005cc5134f342f03c8537b77005cc4f342f1ca8537b77005cc4f342f02d8537b77005cc4f342f0868537b77004f342f2251c48537b77005cc4f32c203c8537005cc4f342f2251c47b77005cc4f342f2c203c87c7b77005cc4f32bd03c8908537b77005cc4f342f8537b77005cc4f342f06c88a85a7b77005cc4f342f8537bd7005cc4f342f0668537b77005cc4f342f0de8537b77006cd5cc4f342f85a7b77005cc4f342f0568537bd7006cb5cc4f342f8537b77005cc4f342f1c58537b77005cc4f342f37e88a85379d7005cc4f342f85379d7005cc4f342f0668537b77937005cc4f342f7e17b77005cc4f342f05685379d7006cb5cc4f342f85383a7b77005cc4f342f8537b77005cc4f342f0838537e17b77004f342f1c47f37b77005cc4f342f03c85380a7b77005cc4f342f)) else (if page < 40 then (if page < 39 then 0x8537b77005cc4f342f3568538087b77005cc4f342f85382c7b77004f342f1bf8537b77005cc4f349d42f8537b77005cc4f342f2f88538447b77005cc4f342f8537b77005cc4f342f0ba8537b77005cc4f342f05a8537b77247005cc4f342f8537b772c5cc4f342f0dd8537b772c6cb5cc4f342f8537b772c7004f342f1f28537b77005cc4f342f1b28537b77005cc4f342f35b8537b75cc4f342f3550dd8537b76eb5cc4f342f3508537b77005a94f342f1c48538047b77005cc4f342f8537b77005cc4f342f2348537b77005cc4f342f0348537b77005cc4f342f33e8537b77005cc5674f342f8537b77005cc4f342f1688537b75cc5ab4f342f0a48537b770062c4f342f1c48537b772c5cc4f342f19986b7b77005cc4f342f1c47b770062f5cc4f342f1c48537b77857004f342f1c48537b77004f342f20302285382a7b77004f342f1c48537b77006e94f342f1c48537b77004f342f2781c48537b77004f34a442f1c485381e7b77005cc4f342f8537b77005cc4f342f1448537b77005cc4f342f0468537b77005cc4f349642f8537b77005cc4f342f0cf8537b77005cc4f348242f8537b77005cc4f342f18b8537b77005cc4f342f3098537b77005cc55742f1c48537b77005cc4f32531c48537b77004f342f32b1c48537fb7b77005cc4f342f8537b77005cc4f342f2988537b77447005cc4f342f8537b77005cc4f342f28e8537b77005cc5484f342f8537b770065d4f342f2f30008537b770065d4f342f8537b77005cc4f342f24e8537b77005cc4f34bb24e0008537b77005cc4f324e8537b77005cc4ba42f1188667b77005cc4f342f1c47b77006925cc4f342f1c48537b77006394f342f1c48537b77005cc4f349e1428537b75cc4f342f0f303c8537b76f25cc4f342f03c8537b77004f342f20703c8537b77005cc4eb42f03c else 0x8537b77005cc4f342f0a67b77005cc4f342f1c406f8357b77005cc4f342f1c48537b77005bd4f342f1c48537b77005cc42f27b1c48537b77005cc4f33ed1c48537b77005aa4f342f1c48857b77005cc4f342f1c48537005cc4f342f2030e58537b77005cc4f32bd0c87b77005cc4f342f2bd06c8537b77004f342f2041c48537b77005c84f342f1c48537b77005cc4f342f3d88537b77005cc4f342f1c28537b77005cc4f342f29c8537b77004f342f2071c486e7b77004f342f2031c48537b77005cc42f27f1c48537b77005cc4f340e1c486e7b77005cc4f342f06686e7b77937005cc4f342f8537b77005cc4f342f0e88537b77006da5cc4f342f88686e7b77005cc4f342f8537e57005cc4f342f0dd8537e57b77004f342f2078537b77005cc4f342f2070008537b77004f342f20788386e7b77005cc4f342f8537e57b77004f342f1c48537e57005cc4f342f1c48537ee7b77004f342f1da8537b77005cc4f342f1da0008537b77004f342f1da8537e57b77005cc4f33a68537b77005cc4f342f3a60008537b77005cc4f33a68537005b54f342f2031c47b77005cc4f344b42f0668537937005cc4f342f38785383f7005cc4f342f3878537005cc4f342f3870dd8538147005cc4f342f3878537b775c7005cc4f342f8537b77005cc4f342f19d8537b77005cc5834f342f8537b77005cc4f342f1467b77006225cc4f342f0228537a97005cc4f342f1c48537b770060b4f342f1c486e7b77005cc4f342f0228537a97005cc4f342f0228537b77087005cc4f342f8537b77006e45cc4f342f8537b77005cc4f344342f8537b770060b4f342f0228537b77005cc4f343642f8537b77005cc4f342f3d786e7b77005cc4f342f1bf8537005cc5b54f342f1c485382c7b77004f342f1c48537005cc5b54f342f1bf8537b772b7005cc4f342f) else (if page < 41 then 0x8537b77005cc4f342f0c58147b77005cc4f342f06f87c8537ab7005cc4f342f85383f7b75cc4f342f0ec85383f7b76e35cc4f342f8538147b77004f342f1f28538207b77005cc4f33ed85382e7b77004f342f1f28538147b77005cc4f33ed8537b75cc4f342f0f10568537b76f05cc4f342f0568838537b770060a4f342f8538147b77005cc4f338c8858147b77005cc4f342f87c8537005cc4f342f0e585380b7b77005cc4f342f8537e67b77005cc4f342f8537b77005cc4f342f3828537b77005cc4f342f0238537b772e7005cc4f342f8537b77005cc4f342f34c8537b77005cc4f34a042f8537b77005cc4f342f2ef8537b77005cc4f32bf01a87e8537b77005e54f342f8538207b77005cc4f33e18538277b77005cc4f33d68538127b77005cc4f342f8537b77005cc4f342f1c88537b775e7005cc4f342f8537b77005cc4f342f1a78537b77005cc5894f342f8537b77005cc4f342f15385382e7b77004f342f1e48538147b77005cc4f33d687c7b77005cc4f342f06c8538147a47005cc4f342f8537b75cc4f342f1c40f38537b76f25cc4f342f1c48537b77005ca4f342f1c48537b77005cc42f2811c48537b77005cc4f341a1c48537b77005c14f342f1c488a7937005cc4f342f1c48537b77005cc4f32b60857b77005cc4f342f20306f8537ab7005cc4f342f1c48537b77004f342f2061c48537b77005c94f342f1c48537b77005cc42f2801c48537b77005cc4f34181c48537b77005cc4f342f3f58537b77005cc4f342f1c38537b770062e4f342f1c48537b77005a84f342f1c48537b77005cc4f342f2398537b77005cc4f342f19b8537b770060a4f342f1c48537b77005c24f342f1c48537b77005cc4f342f1cc8537b77005cc4f342f1c085383c7005cc4f342f1c48537005cc4f342f1c40e58537b77287005cc4f342f else 0x8907b77005cc4f342f06c8537b770f7005cc4f342f8537b77006cc5cc4f342f8537b77005cc4f344442f8537b77005cc4f342f37d8908537a47005cc4f342f85383b7b77005cc4f342f8537b77005cc4f342f07d85380c7b77005cc4f342f8537b77005cc4f342f07b88a7b77005cc4f342f06c88a8537a47005cc4f342f8538147b75cc4f342f0f38538147b76f25cc4f342f8538147b77004f342f2078538207b77005cc4f341a85382e7b77004f342f2078538147b77005cc4f341a8537005cc4f342f0940668537a47005cc4f342f0668838537b770060b4f342f8538147b77005cc4f338088a8147937005cc4f342f8537b77005cc4f342f02485380d7b77005cc4f342f87c7b77005cc4f342f06f8538147ab7005cc4f342f87c8537b77004f342f1f287e8537b77005cc4f33ed8838537b77004f342f1f287c8537b77005cc4f33ed8538197b77005cc4f342f8537b77006e55cc4f342f7b77005cc4f342f06c0568077b77005cc4f342f0568538167b77005cc4f342f8537ca7b77005cc4f342f7b77006eb5cc4f342f06c8537a47006cb5cc4f342f85384b7b77005cc4f342f8537b77005cc4f342f0ed88587c7b77005cc4f342f8538147005cc4f342f0e58147b77005cc4f342f07287c8537b37005cc4f342f8538147b77004f342f2018538207b77005cc4f34058537b75cc4f342f0f10dd8537b76eb5cc4f342f0ec8537ce7b77005cc4f342f8537b77006cf5cc4f342f8537b77005cc4f342f0128537b77005cc4f342f0dc8537b77005cc4f346a42f8537b77005cc4f342f3488537b75cc4f342f0f201f85384d7b76e35cc4f342f8537b76f05cc4f342f0dd8537b76f06cb5cc4f342f85383e7b77005cc4f342f8537b77005cc4f342f0e08537b77005cc4f342f0558537b77006ca5cc4f342f8537b77587005cc4f342f)))) else (if page < 49 then (if page < 45 then (if page < 43 then 0x85383c7005cc4f342f0568537005cc4f342f0e505685383f7006cb5cc4f342f7b77005cc4f342f0660567b77937005cc4f342f0567b77005cc4f342f0f00568867b77005cc4f342f0568537bf7b77005cc4f342f8537b77987005cc4f342f8537b77005cc4f342f0088537b77005cc4f342f0538537b76eb5cc4f342f0567b76eb5cc4f342f0660567b77936eb5cc4f342f0568537b75cc4f342f0f00567b76eb5cc4f342f0f005685383c6eb5cc4f342f0568536eb5cc4f342f0e505685383f7b76cb5cc4f342f8867b76eb5cc4f342f0568537c97b76cb5cc4f342f8537b76eb5cc4f342f0538857b77537005cc4f342f8537607005cc4f342f0e58537b77005cc4f342f05d8537b77497005cc4f342f8537b77005cc4f342f1b78537b77005cc4f342f36b8857b77005cc4f342f1998537005cc4f342f1a10e586b7b77006cb5cc4f342f8537006eb5cc4f346142f85383c7005cc4f342f0c88537005cc4f342f0e50c88537b77005cc4f32af0c88537c77b77005cc4f342f8537b77237005cc4f342f8537b77005cc4f345b42f8537b77005cc4f342f35a8857b77005cc4f342f33a8537005cc4f342f3430e58537b77537005cc4f333a8777b77006cb5cc4f342f8537006eb5cc4f342f2378537b77006cb66d4f342f8537b77006eb5cc4f317d8538147b75cc4f342f0f68538147b76fa5cc4f342f8538147b77004f342f20d8538207b77005cc4f34278908537b75cc4f342f0f68537b77005cc4f342f0f60008537b75cc4f342f0f68908537b76fa5cc4f342f8537b77006fa5cc4f342f0008537b76fa5cc4f342f8908537b77004f342f20d8537b77005cc4f342f20d0008537b77004f342f20d8918537b77005cc4f34278537b77005cc4f342f4270008537b77005cc4f34278938537b77004f342f2078537005cc4f342f095022 else (if page < 44 then 0x85383c7005cc4f342f0e58868537005cc4f342f0e588a8537005cc4f342f0e58537127005cc4f342f0e58537005cc4f342f0e50668537005cc4f342f0e50d985383f7005cc4f342f0e58537006ec5cc4f342f0e58537005cc4f342f0e50dd8537005cc4f342f0e50538537005cc4f346942f0e58537005cc4f342f3520e58537005cc4f342f0e50a68537005cc4f342f0e50bb7b77005cc4f342f1030538857b77006cb5cc4f342f8537987006cb5cc4f342f8537b76ec6cb5cc4f342f8537b77006c75cc4f342f8537005cc4f342f0930538537937005cc4f342f0538537b75cc4f342f0f005385383f7005cc4f342f05385383c7b77005cc4f342f8857b77005cc4f342f0530008857b77005cc4f342f8537987005cc4f342f0538537b77006ce5cc4f342f8537b76ec5cc4f342f0538537b77005cc4f343f42f8537b77005cc4f342f38d8857b77006c75cc4f342f8537006eb5cc4f342f0e58537006cb5cc4f342f0e58537b76cb5cc4f342f08e8537b77005cc4f342f0e58537006c75cc4f342f0e50008537005cc4f342f0e58537b77005cc4f342f08e8537b76c75cc4f342f08e8537b77517005cc4f342f8537b77005cc4f342f0cc8857b77005cc4f342f0dd7b77005cc4f342f1030dd88a8537005cc4f342f0dd8537005cc4f342f0dd0668537b75cc4f342f0f00dd8537b76eb5cc4f342f0dd8537cd7b77005cc4f342f8537b77006d25cc4f342f8537b77005cc4f342f0118537b77005cc4f342f0d98537006cb5cc4f342f0dd85383f7b75cc4f342f0dd8536cb5cc4f342f0f00dd8536eb6cb5cc4f342f0dd8858537005cc4f342f0dd8857006cb5cc4f342f0dd0008857005cc4f342f0dd7006cb5cc4f342f1030dd8537005cc4f342f0dd0538537127006cb5cc4f342f8537006cb5cc4f342f0d985383f6cb5cc4f342f0dd else 0x8537b77ab7005cc4f342f8858537ab7005cc4f342f0008537ab7005cc4f342f8857b77005cc4f342f06683c7b77005cc4f342f0668857b77937005cc4f342f83c7b77937005cc4f342f00083c7937005cc4f342f88683c7b77005cc4f342f85383c7b76f25cc4f342f8537b77006f25cc4f342f0008537b76f25cc4f342f85383c7b75cc4f342f0dd8857b77005cc4f342f05685383c7b76cb5cc4f342f85383c7006cb5cc4f342f85383c7b77004f342f1ef8537b77005cc4f342f1ef0008537b77004f342f1ef85383c7b77005cc4f33ea8537b77005cc4f342f3ea0008537b77005cc4f33ea83c7006eb5cc4f342f0668857ab7006cb5cc4f342f85383c6eb5cc4f342f0dd8857b76f26cb5cc4f342f88583f7b76cb5cc4f342f88583f7006cb5cc4f342f85383c7006eb4f342f1ef85383c7006eb5cc4f33ea88a8857b77005cc4f342f85383c7005cc4f342f06600083c7005cc4f342f0668857b77005cc4f342f0118857b77ab7005cc4f342f0008857ab7005cc4f342f8868857b77005cc4f342f85383c7005cc4f342f0dd00085383c5cc4f342f0dd8857b77005cc4f342f0088857b77006f25cc4f342f0008857b76f25cc4f342f88583f7b77005cc4f342f00088683c7005cc4f342f8888857b77005cc4f342f85383c7005cc4f342f1ef00085383c7004f342f1ef8857b77005cc4f342f00f85383c7005cc4f342f3ea00085383c7005cc4f33ea7937006eb5cc4f342f0e58536eb6cb5cc4f342f0e57b77006eb5cc4f342f0667b77005cc4f342f1030668537937005cc4f342f0e57b77005cc4f342f1030568537b77005cc4f346942f8537b77005cc4f342f33d8868536eb5cc4f342f0e58867006eb5cc4f342f0e57006eb5cc4f342f0e50667006eb5cc4f342f0e50d98536eb5cc4f342f0e50dd8536eb5cc4f342f0e5053)) else (if page < 47 then (if page < 46 then 0x7937006eb5cc4f342f0668538397936cb5cc4f342f8538397006cb5cc4f342f8537936cb5cc4f342f08e8537ab7937005cc4f342f7b77006eb5cc4f342f06f83f7006eb5cc4f342f0668537b77005cc4f342f0e68537b77006eb4f342f1f28537b77006eb5cc4f33ed7006eb5cc4f342f0dd0668537cb7b77005cc4f342f88a8536eb5cc4f342f0dd8536eb5cc4f342f0dd0667b76eb5cc4f342f0dd0660006eb5cc4f342f0dd0667b77936eb5cc4f342f0dd8537cd7b76cb5cc4f342f7b76eb5cc4f342f0dd0117b76eb5cc4f342f0dd0d98537cb7b76cb5cc4f342f8538377b75cc4f342f0dd7937006cb5cc4f342f0568537bf7006cb5cc4f342f8537b76eb6cb5cc4f342f7937006eb6cb5cc4f342f7b76eb6cb5cc4f342f0667b77936eb6cb5cc4f342f0007936eb6cb5cc4f342f7b77006cb5cc4f342f06f8357b77006cb5cc4f342f8537b77005cc4f342f0fd8537b77006cb4f342f1f28537b77006cb5cc4f33ed8537b76eb5cc4f342f01183f7b76cb5cc4f342f06f8538357b76cb5cc4f342f83f8357b76cb5cc4f342f0008357b76cb5cc4f342f8867b76eb5cc4f342f06685383f7936cb5cc4f342f8868537b75cc4f342f0fd8537b76eb5cc4f342f0fd0008537b75cc4f342f0fd85383f7b76cb4f342f1f285383f7b76cb5cc4f33ed7b77006eb5cc4f342f01183f7006cb5cc4f342f06f8538357006cb5cc4f342f83f8357006cb5cc4f342f0008357006cb5cc4f342f8867b76eb5cc4f342f0dd8867b76eb6cb5cc4f342f8867b77005cc4f342f0fd7b77006eb5cc4f342f0fd0007b77005cc4f342f0fd85383f7006cb4f342f1f285383f7006cb5cc4f33ed8537ab7006cb5cc4f342f8857937006cb5cc4f342f8537b76f26cb5cc4f342f8857b76eb6cb5cc4f342f8537b77006eb4f342f1ef8537b77006eb5cc4f33ea else 0x8537bf7005cc4f342f0667bf7b77005cc4f342f0667bf7b77937005cc4f342f8867bf7b77005cc4f342f85c8537005cc4f342f0dd8537b77005cc4f342f1c68537b77005cc4f342f37f7987005cc4f342f0660567b77005cc4f342f05601188a8537987005cc4f342f8537987005cc4f342f0668537c97b75cc4f342f0dd7c97b77005cc4f342f0568538097b77005cc4f342f8537b77005cc4f342f0827937005cc4f342f0560088537987005cc4f342f00885c7b77005cc4f342f0568537b76f25cc4f342f0568537b77005d64f342f0568537b77005cc4f341d0567b77005cc4f342f0660087b77937005cc4f342f0080007937005cc4f342f0088867b77005cc4f342f0088537005cc4f342f0dd00885c7b77005cc4f342f0088537b76f25cc4f342f0088537b77005cc4f343142f8537b77005d64f342f0080008537b77005d64f342f8537b77005cc4f342f41d8537b77005cc4f341d0080008537b77005cc4f341d7937005cc4f342f0560538537bf7005cc4f342f0538537b76ec5cc4f342f0568537b77005cc4f342f03e8537b77005cc4f342f3858537b77005cc4f342f1518537b77005cc4f342f2f18538107b77005cc4f342f8537b77005cc4f342f1cb8537b77005cc5844f342f8537b77005cc4f342f1558537b77005c24f342f01f8537b77005cc4f34400328537b77005f14f342f0568537b77005cc4f34130568537b76cb5cc4f342f0f38537b77005cc4f342f0fe8537b77006cb4f342f2078537b77006cb5cc4f341a8537b770d7005cc4f342f8537147006cb5cc4f342f7b76eb5cc4f342f0660117b76eb5cc4f342f0660538537137006cb5cc4f342f7b770d7005cc4f342f0660007b770d7005cc4f342f8537937006cb5cc4f342f8537b770e6cb5cc4f342f88a7937006cb5cc4f342f8538397b76cb5cc4f342f) else (if page < 48 then 0x8537b77006834f342f0dd8537b77005cc4f316d0dd8538037b77005cc4f342f8537b77005cc4f342f2358537b77005cc5664f342f8537b770067f4f342f34b0008537b770067f4f342f8537b77005cc4f342f16d8537b77005cc5aa4f316d0008537b77005cc4f316d8537b77005aa4f342f0a48537b77005cc4f34680b88537b75cc4f342f0f30568537b77004f342f2070568537b77005cc4f341a0568537b77005cc4f342f0908537b770e5cc4f342f0567b770e7005cc4f342f0567b770e5cc4f342f0660567b76ec5cc4f342f0660567b77005cc4f342f06f06688a7937005cc4f342f0568537b77ac7005cc4f342f7937005cc4f342f0660568397b77005cc4f342f0567b77ac7937005cc4f342f7b77ac7005cc4f342f0560007b77ac7005cc4f342f8537b75cc4f342f1000dd8537b75cc4f342f0fd0567b77006d25cc4f342f0568537005cc4f342f1000dd7b77005cc4f342f0fd0568357b77005cc4f342f05683f7005cc4f342f0660568537b77004f342f1f20568537b77005cc4f33ed0567005cc4f342f0dd0660567b77005cc4f342f0d90567937005cc4f342f08c0568537005cc4f342f0960568537ab7005cc4f342f0568537b77004f342f2060568537b77005cc4f341805683f7b77005cc4f342f06f8868537ab7005cc4f342f88a8867b77005cc4f342f85383f7005cc4f342f06685383f7b77004f342f1f285383f7b77005cc4f33ed8867005cc4f342f0960568867ab7005cc4f342f0567b77ab7005cc4f342f0560007ab7005cc4f342f0568867b75cc4f342f0f00568867b77004f342f2060568867b77005cc4f34180567b77005cc4f342f06f0567bf7005cc4f342f0660568948537b77005cc4f342f8537b77005cc4f342f06f7bf7b77005cc4f342f06f0007b77005cc4f342f06f88a85c7b77005cc4f342f else 0x8537cd7b75cc4f342f0f38537b77005cc4f342f0f30008537b75cc4f342f0f38868617b77005cc4f342f8537cd7b75cc4f342f0dd8537cd7005cc4f342f0dd8537b77005cc4f342f1d08537b77005cc4f342f38b7127005cc4f342f0dd0668536d25cc4f342f0f00dd7b77127005cc4f342f0668537127005cc4f342f0668537937006d25cc4f342f85383f7006d25cc4f342f88a7b77006d25cc4f342f8537b77557005cc4f342f8537b77005cc4f342f0bc88a7005cc4f342f0dd0117b77127005cc4f342f0118537ab7005cc4f342f0dd8537b770e5cc4f342f0dd8537b77005e14f342f0dd8537b77005cc4f34190dd88a7b77005cc4f342f0117b77005cc4f342f0930118617b77005cc4f342f0118537ab7005cc4f342f0118537b770e7005cc4f342f8537b770e5cc4f342f0118537b77005cc4f343342f8537b77005e14f342f0110008537b77005e14f342f8537b77005cc4f342f3f08537b77005cc4f34190110008537b77005cc4f33f088a7005cc4f342f0dd0d98617b77005cc4f342f0d98537006d25cc4f342f0dd8538397b75cc4f342f0dd88a7b77005cc4f342f0d900088a7005cc4f342f0d98537005cc4f342f0d90668537006d25cc4f342f0d98538397b77005cc4f342f8538397b75cc4f342f0d98537b77005cc4f346742f8537b77005cc4f342f3547b77005cc4f342f0dd06f8357b77005cc4f342f0dd8537b77004f342f1f20dd8537b77005cc4f33ed0dd8537b75cc4f342f0f001183f7b75cc4f342f0dd06f8538357b75cc4f342f0dd83f8357b75cc4f342f0dd0008357b75cc4f342f0dd88a85383f5cc4f342f0dd85383f5cc4f342f0dd06685383f7b74f342f1f20dd85383f7b75cc4f33ed0dd8537b77005cc4f342f0418537b77005cc4f345f42f8537b77005cc4f342f15f8537b77005cc4f342f2fd))) else (if page < 52 then (if page < 50 then 0x8538357b77005cc4f33ed83f8357b77005cc4f33ed0008357b77005cc4f33ed88a85383f7005cc4f33ed85383f7005cc4f33ed06685384f7b77005cc4f33ed85383f7b77004f33ed1f28537b77005cc4f33ed1f20008537b77004f33ed1f28537b77005cc4e842f00e85383f7b77005cc4d93ed8537b77005cc4d942f3ed0008537b77005cc4d93ed8537b77005bd4f342f1f28538137b77005cc4f342f8537b77005cc4f342f1c78537b77005cc58b4f342f8537b77005cc4f342f14f88a8537b77005cc4f33ed8537b77005cc4f34180668537b77005cc4f33ed0668537b77937005cc4f33ed8868537b77005cc4f33ed87b8537b77005cc4f33ed8537b77005c94f342f1c78537b77005cc4f33ed03b8537b77005cc4f341837a8537b77005cc4f34180328537b77005cc4f33ed0b88537b77005cc58c4f33ed8537b77005c94f342f14f8537b77005cc4f33ed14b8537b77005cc4f33ed2ea8537b76f25cc4f342f0dd8537b77004f342f2070dd8537b77005cc4f341a0dd88a8535cc4f342f0f30dd88a8536f25cc4f342f0dd8537006f25cc4f342f0dd0008536f25cc4f342f0dd88a8537004f342f2070dd88a8537005cc4f341a0dd88a7b770d7005cc4f342f8537137005cc4f342f0dd8537b76ec5cc4f342f0dd88a7005cc4f342f0dd06685370e5cc4f342f0dd0668537006ec5cc4f342f0dd8536ec5cc4f342f0dd06688a7937005cc4f342f0dd8537b75cc4f342f0dd08e7b77005cc4f342f0f006f88a8867005cc4f342f0dd8537b77004f342f2060dd8537b77005cc4f34180dd88a7005cc4f342f0f00dd88a7b75cc4f342f0f00dd00088a5cc4f342f0f00dd8535cc4f342f0f00dd0668617005cc4f342f0dd0668537b75cc4f342f0f30dd8617b75cc4f342f0f00dd8617b77005cc4f342f0668617b77937005cc4f342f else (if page < 51 then 0x8867b77006ce5cc4f342f7b77937005cc4f342f06f88a83f7937005cc4f342f8867b77005cc4f342f06f85383f7ab7005cc4f342f88a88683f7005cc4f342f83f7b77005cc4f342f0728868537b37005cc4f342f84d7b77005cc4f342f06f8898537ab7005cc4f342f85383f7b77004f342f20185383f7b77005cc4f34057b77005cc4f342f1f206f8357b77005cc4f342f1f28948537b77004f342f1f28537b77004f342f2060118537b77004f342f1f206f83f7b77004f342f1f206f0007b77004f342f1f206f8538357b77004f342f1f283f8357b77004f342f1f20008357b77004f342f1f288a85383f7004f342f1f285383f7004f342f1f206685384d7b77004f342f1f285383f7b770042f27b1f28537b77004f342f27b1f20008537b770042f27b1f28537e77b77005cc4f342f8537b77005cc4f342f3818537b77005cc4f34a242f8537b77005cc4f342f2ee88a8537b77004f342f1f28537b77004f342f2060668537b77004f342f1f20668537b77937004f342f1f28868537b77004f342f1f286f8537b77004f342f1f28537b77006104f342f1f28537b77004f342f1f20248537b77004f342f2061c38537b77004f342f20601f8537b77004f342f1f20a48537b77004f34a242f1f28537b77004f342f3291f28537b77004f342f1f211c8537b77004f342f1f214b8537005cc4f342f09600e8537ab7005cc4f342f00e8537b77004f342f20600e8537b77005cc4f32c000e85683f7b77005cc4f342f8868537af7005cc4f342f8868537b77005dc4f342f85383f7b77005cc4f33fc7b77005cc4f342f3ed06f8357b77005cc4f342f3ed8537b77004f342f3ed1f285384d7b77005cc4f33ed8948537b77005cc4f33ed8537b77005cc4f34180118537b77005cc4f33ed06f83f7b77005cc4f33ed06f0007b77005cc4f33ed06f else 0x8538087b77005cc4f337685383f7b77004f342f20f85383f7b77005cc4f342c8948537b75cc4f342f0f38948537b77004f342f20f8537b77005cc4f342f20f0008537b77004f342f20f8948537b77005cc4f342c8537b77005cc4f342f42c0008537b77005cc4f342c8868537b77005e14f342f85383f7b77005cc4f33f08537005cc4f342f0960118947b77005cc4f342f06f8537b77005cc4f344542f8537b77005cc4f342f37c83f7005cc4f342f06f0087b77005cc4f342f06f0087b770e7005cc4f342f06f7b77005cc4f342f06f0117b77005cc4f344542f06f7b77005cc4f342f40b06f7b77005cc4f342f06f0247b77005cc4f342f06f03b8948537ab7005cc4f342f85380e7b77005cc4f342f8537b77005cc4f342f0758357b77005cc4f342f06f8868857ab7005cc4f342f8537ab7005cc4f342f0538538397ab7005cc4f342f8537ab7005cc4f342f0d985380e7ab7005cc4f342f8537ab7005cc4f342f1c38357b77005cc4f342f0758537ab7005cc4f342f37a88a7b77005cc4f342f06f88a8537ab7005cc4f342f85383f7b75cc4f342f0f385383f7b76f25cc4f342f85383f7b77004f342f20785383f7b77005cc4f341a88a83f7005cc4f342f06f88a8867ab7005cc4f342f88a7b77ab7005cc4f342f00088a7ab7005cc4f342f88a8867b75cc4f342f0f388a8867b76f25cc4f342f8867b77006f25cc4f342f0008867b76f25cc4f342f88a8867b77004f342f20788a8867b77005cc4f341a8537005cc4f342f0960668537ab7005cc4f342f0668868537b770e5cc4f342f85383f7b76ce5cc4f342f8357b77005cc4f342f06683f7005cc4f342f06f0668538357005cc4f342f06683f8357005cc4f342f0660008357005cc4f342f06688a83f7005cc4f342f0668867b77ac7005cc4f342f8538367005cc4f342f066)) else (if page < 54 then (if page < 53 then 0x88a7b77937005cc4f341a88a7937005cc4f342f09700088a7005cc4f342f0970007937005cc4f342f09789488a7937005cc4f342f88a7937005cc4f342f0f300088a7935cc4f342f0f388a7937005cc4f342f00888a7937006f25cc4f342f00088a7936f25cc4f342f0007937006f25cc4f342f0000007936f25cc4f342f89088a7937005cc4f342f88a7937005cc4f342f20700088a7937004f342f20788a7937005cc4f342f00688a7937005cc4f342f41a00088a7937005cc4f341a88a7b77005cc4f342f0668537937005cc4f342f0667b77005cc4f342f0930667937005cc4f342f09306688a7b77937005cc4f342f88a7937005cc4f342f06600088a7937005cc4f342f7b77937006ce5cc4f342f88a8397937005cc4f342f8537b77937004f342f1ec8537b77937005cc4f33e788a8397b77005cc4f342f00088a8397005cc4f342f8538397005cc4f342f0668538397b77004f342f1ec8537b77005cc4f342f1ec0008537b77004f342f1ec8538397b77005cc4f33e78537b77005cc4f342f3e70008537b77005cc4f33e788a7937005cc4f342f0d988a7937005cc4f342f08e8537b75cc4f342f0d908e8537b77005cc4f344a42f8537b77005cc4f342f38a88a7937006c75cc4f342f8538397b76c75cc4f342f88a8087937005cc4f342f8537b77005cc4f342f0ea8537b77006e15cc4f342f8537b77005cc4f342f1e28537b77005cc4f342f3d488a7937005cc4f342f1bf88a7937005cc4f342f0858537b77005cc4f32b50858537b779370061c4f342f8537b77937005cc4f339f8537b77107005cc4f342f8537b77006d95cc4f342f8537b77005cc4f344742f8537b770061c4f342f0850008537b770061c4f342f8537b77005cc4f342f39f8537b77005cc4cd42f0850008537b77005cc4f339f88a7937005cc4f342f376 else 0x8537b77005cc5914f342f8537b77005cc4f342f14e8537b77005cc4f341a0378537b77637005cc4f341a8537b77005ca4f342f1a48537b77005cc4f341a0c08537b77005cc4f341a3448537b77005cc5924f341a8537b77005ca4f342f14e8537b77005cc4f341a14c8537b77005cc4f341a2eb8537005cc4f342f0970667b77005cc4f342f0970668537b75cc4f342f0f30668537b76f25cc4f342f0668537b77004f342f2070668537b77005cc4f341a06688a8537b75cc4f342f0f388a8537b76f25cc4f342f88a8537b77004f342f20788a8537b77005cc4f341a88a7005cc4f342f09306688a7b75cc4f342f0f306688a7b76f25cc4f342f0667b77006f25cc4f342f0660007b76f25cc4f342f06688a7b77004f342f20706688a7b77005cc4f341a06688a7b770e7005cc4f342f8537147005cc4f342f0668537b77005cc4f342f1a68537b77005cc4f342f34a7b77006ce5cc4f342f0668537b77547005cc4f342f8537b77005cc4f342f0c78537b76ec5cc4f342f0118537b77005e14f342f0668537b77005cc4f34190668537b770e5cc4f342f0538537b77005cc4f342f0c48537b77005cc4f342f34f8537b77005cc4f342f1528537b77005cc4f342f2f28537b775b7005cc4f342f8537b77005cc4f342f1aa8537b77005cc5824f342f8537b77005cc4f342f1568537b77005c14f342f0228537b77005cc4f34430378537b77005f94f342f0668537b77005cc4f34120668537b77005cc4f342f0978537b77935cc4f342f0f38537b77936f25cc4f342f8537b77937004f342f2078537b77937005cc4f341a88a7b77005cc4f342f0977b77937005cc4f342f0970007b77005cc4f342f09788a7b77935cc4f342f0f388a7b77936f25cc4f342f7b77937006f25cc4f342f0007b77936f25cc4f342f88a7b77937004f342f207) else (if page < 55 then 0x88a8537b75cc4f342f0f688a8537b76fa5cc4f342f8908537b75cc4f342f0f38908537b76f25cc4f342f88a8537b77004f342f20d88a8537b77005cc4f34278537b75cc4f342f2070f38537b76f25cc4f342f2078948537b77004f342f20788a8537b74f342f2070f38537b77004f342f2070f30008537b74f342f2070f38537b77004f342f20700888a8537b76f24f342f2078537b77006f24f342f2070008537b76f24f342f2078908537b77004f342f20788a8537b770042f2812078537b77004f342f2812070008537b770042f2812078537b77317005cc4f342f8537b77005cc4f342f3478537b77005cc4f34a642f8537b77005cc4f342f2ed8537b77004f342f2070228537b77317004f342f2078537b77005a74f342f2078537b77004f342f2070a98537b77004f342f2071a28537b77004f34a642f2078537b77004f342f3262078537b77004f342f20711d8537b77004f342f20714c8537b75cc4f342f0f30068537b76f25cc4f342f0068537b77004f342f2070068537b77005cc4f32c100688a8537b77035cc4f342f88a8537b76f55cc4f342f88a8537b77005d24f342f88a8537b77005cc4f34218537b75cc4f342f41a0f38537b76f25cc4f342f41a8537b77004f342f41a2078908537b77005cc4f341a8948537b77005cc4f341a88a8537b75cc4f341a0f38537b77005cc4f341a0f30008537b75cc4f341a0f38537b77005cc4f341a00888a8537b76f25cc4f341a8537b77006f25cc4f341a0008537b76f25cc4f341a8918537b77005cc4f341a88a8537b77004f341a2078537b77005cc4f341a2070008537b77004f341a2078537b77005cc4eb42f00688a8537b77005cc4eb41a8537b77005cc4eb42f41a0008537b77005cc4eb41a8537b77005ca4f342f2078537b77637005cc4f342f8537b77005cc4f342f1a4 else 0x88a8537b77004f342f20f88a8537b77005cc4f342c88a7b75cc4f342f0f30118537b77005cc4f346e42f8537b77005cc4f342f3468537b75cc4f342f0f30118537b75cc4f346e42f0f38537b75cc4f342f3460f38537b75cc4f342f0f30a98537b75cc4f342f0f30c08537b75cc4f342f0f300888a8537b77005d64f342f88a8537b77005cc4f341d8948537b76f25cc4f342f8537b76f25cc4f342f0f388a8857b76f25cc4f342f8537b77627005cc4f342f8537b77005cc4f342f0c28537b76f25cc4f342f0538537b77626f25cc4f342f8537b76f25cc4f342f1a28537b76f25cc4f342f0c28537b76f25cc4f342f344)))))) else 0
  | 7 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x8537b77005cc4f342f1098537b77005cc4f342f14d1310008537b77005cc4f342f2ec88a8537b77005cc4f342f2ec8537b77005cc4f342f2ec0668537b77937005cc4f342f2ec85383f7b77005cc4f342f2ec8537b77005cc4f342f2ec0dd8537b77005cc4f342f2ec0568537b77006cb5cc4f342f2ec85382e7b77005cc4f342f2ec8537b77005cc4f342f2ec1c48537b77005cc4f34b742f03c8537b77005cc5b34f342f2ec8537b77897005cc4f342f2ec8537b77005cc4f342f2ec1a38537b77005cc4f34b742f0c18537b77005cc5a64f342f2ec8538147b77005cc4f342f2ec8537b77005cc4f342f3251c48537b77005cc4f342f2ec03c8537b77005cc4f342f37b2ec8537b77647005cc4f342f2ec8537b77005cc4f342f3251a38537b77005cc4f342f2ec0c18537b77005cc4f342f3452ec8537b77006915cc4f342f2ec8537b77005cc4f34b742f14d8537b77005cc4f342f2ec14d8537b77005cc4f342f3252ec8537b77005cc5934f342f2ec0008537b77005cc59342f2ec0000008537b77005cc5932ec8537fa7b77005cc4f342f2ec0008537fa7b77005cc4f342f8537b77005cc4f34b742f2990008537b77005cc4f342f2998537b77005cc4f342f2ec02c0008537b77005cc4f342f02c8537b77005cc4f342f2ec2e20008537b77005cc4f342f2e28537b77437005cc4f342f2ec0008537b77437005cc4f342f8537b77005cc4f34b742f28f0008537b77005cc4f342f28f8537b77005cc4f342f2ec0b10008537b77005cc4f342f0b18537b77005cc4f342f2ec2da0008537b77005cc4f342f2da8537b77006585cc4f342f2ec0008537b77005cc5434f342f0008537b77006584f342f2ec0000008537b77006584f342f8537b77005cc4f34b742f25a0008537b77005cc4f342f25a0008537b77005cc4f34b725a0000008537b77005cc4f325a8537b77005cc4f342f2ec1310008537b77005cc4f342f1318537b77005cc4f342f2ec2d40008537b77005cc4f342f2d48537b77005cc4f342f32514d0008537b77005cc4f342f14d0008537b77005cc4f332514d else 0x8537b77005cc4f342f14d0dd8537b77005cc4f342f14d0568537b77006cb5cc4f342f14d85382e7b77005cc4f342f14d8537b77005cc4f342f1c414d8537b77005cc4f342f2a603c8537b77005cc5b34f342f14d8537b77897005cc4f342f14d8537b77005cc4f342f1a314d8537b77005cc4f342f2a60c18537b77005cc5a64f342f14d8538207b77005cc4f342f14d8537b77005cc4f342f27514d8537b77005cc4f342f18c03c8537b77005cc4f34c542f14d8537b77757005cc4f342f14d8537b77005cc4f342f27314d8537b77005cc4f342f18c0c18537b77005cc4f34c142f14d8537b77006af5cc4f342f14d8537b77005cc4f342f18c14d8538147b77005cc4f342f14d8537b77005cc4f342f2b614d0008537b77005cc4f32b614d8537b77005cc4f342f14d03c8537b77005cc4f342f37b14d0008537b77005cc4f337b14d8537b77647005cc4f342f14d0008537b77647005cc4f314d8537b77005cc4f342f2b014d8537b77005cc4f342f14d0c10008537b77005cc4f314d0c18537b77005cc4f342f34514d8537b77005cc4f342f2aa14d0008537b77004f342f2aa14d8537b77005cc5934f342f14d0008537b77005cc5934f314d8537b77005cc4f342f27114d8537b77005cc4f342f24614d0008537b77005cc4f324614d8537d77b77005cc4f342f14d0008537d77b77005cc4f342f8537b770063e5cc4f342f14d0008537b77005cc4f349742f8537b77005cc4f342f14d01a0008537b77005cc4f342f01a8537b77005cc4f342f14d1420008537b77005cc4f342f1428537b771f7005cc4f342f14d0008537b771f7005cc4f342f8537b770063a5cc4f342f14d0008537b77005cc4f348342f8537b77005cc4f342f14d09e0008537b77005cc4f342f09e8537b77005cc4f342f14d1390008537b77005cc4f342f1398537b77006915cc4f342f14d0008537b77005cc5934f342f0008537b77006914f342f14d8537b77005cc5174f342f14d0008537b77005cc4f347c42f8537b77005cc4f34be42f14d0008537b77005cc4f342f30a8537b77005cc4f342f14d109) else (if page < 3 then 0x8537b77005cc4f342f1760008537b77005cc5a64f31760000008537b77005cc4f31768537b77005cc4f342f3451398537b77005cc4f342f3452da8537b77005cc4f342f3450c10008537b77005cc4f342f0c10008537b77005cc4f33450c188a8537b77005cc5934f342f8537b77005cc5934f342f0668537b77937005cc5934f342f85383f7b77005cc5934f342f8537b77005cc5934f342f0dd8537b77005cc5934f342f0568537b77006cb5cc5934f342f85382e7b77005cc5934f342f8537b77005cc5934f342f1c48537b77006af5cc4f342f03c8537b77006af5cc4f342f37b8537b77897005cc5934f342f8537b77005cc5934f342f1a38537b77006af5cc4f342f0c18537b77006af5cc4f342f3458538277b77005cc5934f342f0008538277b77005cc4f342f8537b77006af5cc4f342f1180008537b77005cc4f342f1188537b77005cc5934f342f04d0008537b77005cc4f342f04d8537b77005cc5935764f342f0008537b77005cc5764f342f8537b77817005cc5934f342f0008537b77817005cc4f342f8537b77006af5cc4f342f1130008537b77005cc4f342f1138537b77005cc5934f342f0d50008537b77005cc4f342f0d58537b77005cc59355b4f342f0008537b77005cc55b4f342f8537b77006c55cc5934f342f0008537b77006c55cc4f342f8537b77006af5cc4f342f1098537b77005cc5934f342f1940008537b77005cc4f342f1948537b77006af5cc4f342f3340008537b77005cc4f342f3348538147b77005cc5934f342f8537b77006915cc4f342f1c40008537b77006914f342f1c48537b77005cc5934f342f03c8537b77005cc5934f342f37b0008537b77005cc5934f337b8537b77647005cc5934f342f0008537b77897006914f342f8537b77006915cc4f342f1a38537b77005cc5934f342f0c10008537b77005cc5934f30c18537b77005cc5934f342f3458537b77006915cc5934f342f0008537b77006af6914f342f88a8537b77005cc4f342f14d8537b77005cc4f342f14d0668537b77937005cc4f342f14d85383f7b77005cc4f342f14d else (if page < 4 then 0x8537b77005cc4f342f2b60c18537b77005cc4f342f0c103c8537b77005cc4f342f37b0c18537b77005cc4f342f2b00c10008537b77005cc4f32b00c10008537b75cc4f342f2b00c18537c67b77005cc4f342f0c10008537c67b77005cc4f342f8537b773a7005cc4f342f0c10008537b77257005cc4f342f8537b77005cc4f342f0c100e0008537b77005cc4f342f00e8537b77005cc4f342f0c10b80008537b77005cc4f342f0b88537b77647005cc4f342f0c10008537b77647005cc4f342f0008537b77645cc4f342f0c18537b77005cc5154f342f0c10008537b77005cc4f345a42f8537b77005cc4f34c242f0c10008537b77005cc4f342f35c8537b77005cc4f342f0c109e8537b77005cc4f342f0c10b10008537b77005cc4f342f34588a8537b77005cc4f342f3458537b77005cc4f342f3450668537b77937005cc4f342f34585383f7b77005cc4f342f3458537b77005cc4f342f3450dd8537b77005cc4f342f3450568537b77006cb5cc4f342f3458538207b77005cc4f342f3458537b77005cc4f342f3451c48537b77005cc4f34c142f03c8537b77005cc4f34c542f3458537b77757005cc4f342f3458537b77005cc4f342f3451a38537b77005cc4f34c142f0c18537b77005cc4f34c142f3458538147b77005cc4f342f3458537b77005cc5a64f342f1c40008537b77005a64f342f1c48537b77005cc4f342f34503c8537b77005cc4f342f37b3450008537b77005cc4f337b3458537b77647005cc4f342f3450008537b77647005cc4f33450008537b77645cc4f342f3458538027b77005cc4f342f3450008538027b77005cc4f342f8537b77005cc5a64f342f2360008537b77005cc4f342f2368537b77005cc4f342f3450320008537b77005cc4f342f0328537b77005cc4f342f34533a0008537b77005cc4f342f33a8537b77005cc5a64f342f1a30008537b77005cc4f342f1a30008537b75cc5a64f342f1a38537b77005cc56b4f342f3450008537b77005cc5654f342f0008537b77006794f342f3450000008537b77006794f342f8537b77005cc5a64f342f176 else 0x8537b77647005cc4f342f1c48537b77757005cc4f342f03c8537b77757005cc4f342f37b8537b77817647005cc4f342f8537b77647005cc4f342f1b90008537b77005cc4f342f1b98537b77897005cc4f342f09e8537b77757005cc4f342f36d0008537b77005cc4f342f36d8537b77757647005cc4f342f8538147b77647005cc4f342f8537b77897005cc4f342f1c48537b77647005cc4f342f03c8537b77647005cc4f342f37b88a8537b77005cc4f342f1a38537b77005cc4f342f1a30668537b77937005cc4f342f1a385383f7b77005cc4f342f1a38537b77005cc4f342f1a30dd8537b77005cc4f342f1a30568537b77006cb5cc4f342f1a385382e7b77005cc4f342f1a38537b77005cc4f342f1c41a30008537b77004f342f1c41a38537b77005cc4f342f2b003c8537b77005cc5b34f342f1a30008537b77005b34f342f1a38538147b77005cc4f342f1a38537b77005cc4f342f2751a38537b77005cc4f342f1a303c8537b77005cc4f342f37b1a38537b77647005cc4f342f1a38537b77005cc4f342f2731a38537de7b77005cc4f342f1a30008537de7b77005cc4f342f8537b770062a5cc4f342f1a30008537b77005cc4f346042f8537b77005cc4f342f1a301f0008537b77005cc4f342f01f8537b77005cc4f342f1a31990008537b77005cc4f342f1998537b77897005cc4f342f1a30008537b77897004f342f1a38537b77005cc4f349042f1a30008537b77005cc4f349042f8537b77005cc4f342f32c1a30008537b77005cc4f342f2fe8537b77005cc4f342f1a31138537b77005cc4f342f1a313988a8537b77005cc4f342f0c18537b77005cc4f342f0c10668537b77937005cc4f342f0c185383f7b77005cc4f342f0c18537b77005cc4f342f0dd0c18537b77005cc4f342f0c10568537b77006cb5cc4f342f0c18538207b77005cc4f342f0c18537b77005cc4f342f1c40c18537b77005cc4f342f0d003c8537b77005cc4f34c542f0c18537b77757005cc4f342f0c18537b77005cc4f342f1a30c18537b77005cc4f342f0d00c18538147b77005cc4f342f0c1))) else (if page < 8 then (if page < 6 then 0x8537b77006eb5cc4f342f37b85383f7b77005cc4f342f37b8537b77005cc4f342f37b0dd8537b77005cc4f342f40a0568537b77006cb5cc4f342f37b87e8537b77005cc4f342f37b8537b77005cc4f342f40a1c48537b77005cc4f34c542f03c8537b77005cc4f34e042f37b8538207b77005cc4f342f37b8537b77005cc4f342f37b1c48537b77005cc4f34e042f03c8537b77005cc4f34c542f37b87c8537b77005cc4f342f37b8537b77005cc5c04f342f1c40008537b77005c04f342f1c48537b77005cc4f342f37b03c8537b77005cc4f342f40a37b0008537b77005cc4f340a37b8538147b77005cc4f342f37b0008538147b77005cc4f337b0008538147005cc4f342f37b8798537b77005cc4f342f37b00085380f7b77005cc4f342f8537b77005cc5c04f342f1cd0008537b77005cc4f342f1cd8537b77005cc4f342f37b0370008537b77005cc4f342f0378537b77005cc4f342f37b3760008537b77005cc4f342f3768537b77005cc5b34f342f1c40008537b77005cc4f342f1c40008537005cc5b34f342f1c48537b775a7005cc4f342f37b0008537b775a7005cc4f342f8537b77005cc5c04f342f1ab0008537b77005cc4f342f1ab8537b77005cc4f342f37b0b88537b77005cc4f342f37b33a8537b77005cc5864f342f37b0008537b77005cc5814f342f8537b77005cc5c04f342f1570008537b77005cc4f342f1578537b77005cc4f342f37b1428537b77005cc4f342f37b2e28537b77005cc4f342f40a03c0008537b77005cc4f342f03c0008537b77005cc4f340a03c88a8537b77647005cc4f342f8537b77647005cc4f342f0668537b77937647005cc4f342f85384d7b77647005cc4f342f00085384d7b77005cc4f342f8537b77897005cc4f342f0a40008537b77005cc4f342f0a48537b77647005cc4f342f05f0008537b77005cc4f342f05f8537b776474b7005cc4f342f0008537b774b7005cc4f342f85383f7b77647005cc4f342f8537b77647005cc4f342f0dd8537b77647005cc4f342f0568537b77647006cb5cc4f342f8538207b77647005cc4f342f else (if page < 7 then 0x8537b77005cc4f349e42f1c40008537b77005cc4f349e42f8537b77005cc4f342f32a1c40008537b77005cc4f342f2f38537b77005cc4f342f1c41188537b77005cc4f342f1c414288a8537b77005cc4f342f03c8537b77005cc4f342f09303c8537b77005cc4f342f06603c8537b77937005cc4f342f03c8868537b77005cc4f342f03c8537b77005cc4f342f0f003c8537b77005cc4f342f05603c8537b77006eb5cc4f342f03c85383f7b77005cc4f342f03c8537b77005cc4f342f0dd03c8537b77005cc4f342f08c03c8537b77006cb5cc4f342f03c87e8537b77005cc4f342f03c8537b77005cc4f342f20303c8537b77005cc4f342f04703c8538207b77005cc4f342f03c8537b77005cc4f342f1c403c8537b77005cc4f342f08903c8537b77005cc4f342f2bd03c0008537b77005cc4f32bd03c0007b77005cc4f342f2bd03c8538147b77005cc4f342f03c8537b77005cc4f342f2b603c8537b77005cc4f342f08403c87c8537b77005cc4f342f03c0008538147b77005cc4f342f00087c7b77005cc4f342f03c8537bd7b77005cc4f342f03c0008537bd7b77005cc4f342f8537b77a17005cc4f342f03c0008537b779d7005cc4f342f8537b77005cc4f342f03c0060008537b77005cc4f342f0068537b77005cc4f342f03c0378537b770b7005cc4f342f03c0008537b770b7005cc4f342f8537b77006ef5cc4f342f03c0008537b77006db5cc4f342f8537b77005cc4f342f03c00e8537b77005cc4f342f03c0328537b77005cc4ff4f342f03c0008537b77005cc4f343b42f0008537b77005fe4f342f03c0000008537b77005fe4f342f8537b77005cc4f34e242f03c0008537b77005cc4f342f3ab0008537b77005cc4e242f03c0000008537b77005cc4f33ab8537b77005cc4f342f03c01a8537b77005cc4f342f03c02c0008537b77005cc4f342f37b88a8537b77005cc4f342f37b8537b77005cc4f342f40a0668537b77005cc4f342f37b0668537b77937005cc4f342f37b8868537b77005cc4f342f37b8537b77005cc4f342f40a0dd8537b77005cc4f342f37b056 else 0x87c8537b77a47005cc4f342f0008537b77a47005cc4f342f88a8538147b77005cc4f342f87c8537b77005cc4f342f0668538147b77005cc4f342f0668538147b77937005cc4f342f8868538147b77005cc4f342f87c8537b77005cc4f342f0dd8538147b77005cc4f342f05687c8537b77006cb5cc4f342f85384d8147b77005cc4f342f8538147b77005cc4f342f0ec0008537b77005cc4f342f0ec8838537b77005cc4f342f01f8538147b77006e35cc4f342f0008537b77006e35cc4f342f85383f8147b77005cc4f342f8538147b77005cc4f342f0dd87c8537b77005cc4f342f0568538147b77006cb5cc4f342f87e8538147b77005cc4f342f8538278147b77005cc4f342f8538147b77005cc4f342f1e40008537b77005cc4f342f1e48838537b77005cc4f342f01a8538207b77005cc4f342f3d60008537b77005cc4f342f3d68538208147b77005cc4f342f87c8538147b77005cc4f342f88a8537b77005cc4f342f1c48537b77005cc4f342f2030668537b77005cc4f342f1c40668537b77937005cc4f342f1c48868537b77005cc4f342f1c48537b77005cc4f342f2030dd8537b77005cc4f342f1c40568537b77006eb5cc4f342f1c485383f7b77005cc4f342f1c48537b77005cc4f342f1c40dd8537b77005cc4f342f2030568537b77006cb5cc4f342f1c48838537b77005cc4f342f1c48537b77005cc4f342f2031c40008537b77004f342f2031c487c8537b77005cc4f342f1c48537b77005cc4f342f27e1c48538147b77005cc4f342f1c48537b77005cc4f342f2751c486e8537b77005cc4f342f1c40008537e57b77005cc4f342f8537b77006225cc4f342f1c40008537b77005cc4f342f3878537b77005cc4f342f1c40220008537b77005cc4f342f0228537b77005cc4f342f1c41bf0008537b77005cc4f342f1bf8537b772c7005cc4f342f1c40008537b772c7005cc4f342f8537b77005cc5ab4f342f1c40008537b77005cc4f342f3508537b77005cc4f342f1c40a48537b77005cc4f342f1c419985382e7b77005cc4f342f1c400085382e7b77004f342f1c4)) else (if page < 9 then 0x85383f7b77005cc4f342f0568537b77005cc4f342f0dd0568537b77005cc4f342f08c0568868537b77005cc4f342f05600085383f7b77005cc4f342f0008867b77005cc4f342f0568537bf7b77005cc4f342f0560008537bf7b77005cc4f342f8537b77987005cc4f342f0560008537b77987005cc4f342f8537b77005cc4f342f0560080008537b77005cc4f342f0088537b77005cc4f342f0560530008537b77006cb5cc4f342f8537b77005cc4f344042f0560008537b77005cc4f344042f8537b77005cc4f342f40d0560008537b77005cc4f342f38c8537b77005cc4f342f05601f8537b77005cc4f342f05603288a8537b77006cb5cc4f342f8537b77006eb5cc4f342f0660007b77006eb5cc4f342f0668537b77006cb5cc4f342f0668537b77937006cb5cc4f342f0008537937006cb5cc4f342f8868537b77006cb5cc4f342f8537b77006eb5cc4f342f0dd0008537b76eb5cc4f342f0dd8537b77006cb5cc4f342f0568537b77006eb6cb5cc4f342f0008537b76eb6cb5cc4f342f85383f7b77006cb5cc4f342f00085383f7b76cb5cc4f342f00085383f7006cb5cc4f342f8858537b77006cb5cc4f342f00085383c7b77005cc4f342f0008857b77006cb5cc4f342f0000008857b77005cc4f342f8537b77006eb5cc4f342f0e50008537b77005cc4f342f0e50008537006eb5cc4f342f0e50000008537005cc4f342f0e58537b77006cb5cc4f342f0530008537b77005cc4f342f0538537b77006cb6c75cc4f342f0008537b77006c75cc4f342f8537b77006cb5cc4f342f0dd0008537b77005cc4f342f0dd0008537006cb5cc4f342f0dd8537b77006eb5cc4f342f0560008537b77005cc4f342f0560008537b76eb5cc4f342f0568537b77537006cb5cc4f342f0008537b77537005cc4f342f8537b77006cb5cc4f342f1998537b77006eb5cc4f342f0c80008537b77005cc4f342f0c88537b77006cb5cc4f342f33a8908538147b77005cc4f342f0008908537b77005cc4f342f8838537b77005cc4f342f0228538147b77005cc4f342f06c0008537b77005cc4f342f06c else (if page < 10 then 0x8537b77005cc4f342f0858537b77937005cc4f342f37689485383f7b77005cc4f342f0008948537b77005cc4f342f8868537b77005cc4f342f01185383f7b77005cc4f342f06f0008537b77005cc4f342f06f00083f7b77005cc4f342f06f0000007b77005cc4f342f06f8868537b77ab7005cc4f342f0008537b77ab7005cc4f342f0008868537ab7005cc4f342f0000008537ab7005cc4f342f88a85383f7b77005cc4f342f00088a8867b77005cc4f342f8868537b77005cc4f342f06685383f7b77005cc4f342f06600085383f7005cc4f342f06685383f7b77937005cc4f342f88685383f7b77005cc4f342f85384d83f7b77005cc4f342f85383f7b77005cc4f342f1f200085383f7b77004f342f1f20008537b77005cc4f342f1f20000008537b77004f342f1f28868537b77005cc4f342f00e85383f7b77005cc4f342f3ed00085383f7b77005cc4f33ed0008537b77005cc4f342f3ed0000008537b77005cc4f33ed88a8537b77005cc4f342f0dd00088a8537005cc4f342f0dd8537b77005cc4f342f0f00668537b77005cc4f342f0dd0660008537005cc4f342f0dd0668537b77937005cc4f342f0dd8868537b77005cc4f342f0dd8537b77005cc4f342f0f00dd0008537b75cc4f342f0f00dd8618537b77005cc4f342f0dd0008537cd7b77005cc4f342f8537b77127005cc4f342f0dd0008537b77006d25cc4f342f8537b77005cc4f342f0dd0110008537b77005cc4f342f0118537b77005cc4f342f0dd0d90008537b77005cc4f342f0d985383f7b77005cc4f342f0dd00085383f7b75cc4f342f0dd8537b77005cc4f346842f0dd0008537b77005cc4f346842f8537b77005cc4f342f3530dd0008537b77005cc4f342f34b8537b77005cc4f342f0dd0a48537b77005cc4f342f0dd0b888a8537b77005cc4f342f0568537b77005cc4f342f0930568537b77005cc4f342f0660560007b77005cc4f342f0660568537b77937005cc4f342f0560007b77937005cc4f342f0568537b77005cc4f342f0f00560008537b75cc4f342f0f00560007b77005cc4f342f0f0056 else 0x89488a8537b77005cc4f342f88a8537b77005cc4f342f0f300088a8537b75cc4f342f0f30008537b77005cc4f342f0f30000008537b75cc4f342f0f388a8537b77005cc4f342f00888a8537b77006f25cc4f342f00088a8537b76f25cc4f342f0008537b77006f25cc4f342f0000008537b76f25cc4f342f89088a8537b77005cc4f342f88a8537b77005cc4f342f20700088a8537b77004f342f2070008537b77005cc4f342f2070000008537b77004f342f20788a8537b77005cc4f342f00688a8537b77005cc4f342f41a00088a8537b77005cc4f341a0008537b77005cc4f342f41a0000008537b77005cc4f341a8537b77005cc4f342f0930660007b77005cc4f342f09306688a8537b77005cc4f342f06600088a8537b77005cc4f342f00088a7b77005cc4f342f0660008537b77937005cc4f342f8537b770e7005cc4f342f0660008537b770e7005cc4f342f8537b77006ec5cc4f342f0660008537b77006ce5cc4f342f8537b77005cc4f342f0660118537b77005cc4f342f0660538537b77005cc4f344342f0660008537b77005cc4f344342f8537b77005cc4f342f40c0660008537b77005cc4f342f3808537b77005cc4f342f0660228537b77005cc4f342f06603788a8537b77937005cc4f342f00088a7b77937005cc4f342f00000088a7937005cc4f342f8537b77937005cc4f342f0660008537b77005cc4f342f0660008537937005cc4f342f0668538397b77937005cc4f342f0008538397b77005cc4f342f8537b77937005cc4f342f0d98537b77937005cc4f342f08e0008537b77005cc4f342f08e8537b77937006c75cc4f342f8538087b77937005cc4f342f0008538087b77005cc4f342f8537b77937005cc4f342f1bf8537b77937005cc4f342f085)))) else 0
  | 8 => if page < 1 then 0x88a8537b77005cc4f342f0000008537b77005cc4f342f0660000008537b77937005cc4f342f00000085383f7b77005cc4f342f0000008537b77005cc4f342f0dd0000008537b77005cc4f342f0560000008537b77006cb5cc4f342f0000008538147b77005cc4f342f0000008537b77005cc4f342f1c40000008537b77005cc4f342f03c0000008537b77005cc4f342f37b0000008537b77647005cc4f342f0000008537b77005cc4f342f1a30000008537b77005cc4f342f0c10000008537b77005cc4f342f3450000008537b77005cc5934f342f0000008537b77005cc4f342f14d0000008537b77005cc4f342f2ec else 0
  | 9 => if page < 1 then 0x8537b77005cc4f342f else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 3
  | 4 => 186
  | 5 => 2191
  | 6 => 3543
  | 7 => 694
  | 8 => 18
  | 9 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 4096
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 12)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (12*(k+1)) i)

def bucketCount : ℕ → ℕ
  | 3 => 2
  | 4 => 130
  | 5 => 1473
  | 6 => 2505
  | 7 => 549
  | 8 => 20
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 7
  | 4 => 473
  | 5 => 5304
  | 6 => 9019
  | 7 => 1977
  | 8 => 73
  | 9 => 2
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
  | 4 => if page < 3 then (if page < 1 then 0x100080008000f00000003000000020001000200000000000000000022000200070009000400060009000e000000000007000200020002001a0004000600060003000300070001001600000002000e00050004000600080007000400000002000400030004000c000e00010003000000000006000200000000000000000000 else (if page < 2 then 0x800020009000100010001000e0005000f0018000400000000000200110002001400140006001000070004002300010000000000000002000a0005001000040005000000180000000b0002000300040014000600070008000f000500040007000000010020000f000000050000000500040002002c000c000000020003000b else 0x130029)) else 0
  | 5 => if page < 24 then (if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x80009001500000001000100030000000a0001000400290006000d000100020001000000000005000200000033000f00020003000300010004000000030000000000060006000900000004000400030004000300250007000100050000000200050001000000000004000e000c0000000b000e00000000000200090003 else (if page < 2 then 0x70000001c000000040000000b000200140005000b0002000800000003000e00030015000c00000007000400120002000d0000000100020009000000020000000000030006000a00020004000b0000000000030011000f0000000000040004000200060005000100020001000100030009000000030006000a000200020001 else 0x10003900010004002f00010000001300150000000a00110005000b00210002000b001700020002000000030001000900000002000d00000004000000060000000200000002000000010002000d001100060000000000030001000000020000000100000000003100000000000a00020003000a00090006000400090008)) else (if page < 4 then 0xa000d000a0001000800000005000e000100050002000b0001003a0011000a001a00100000000300070021000100050008000000040002000600000019000000000000000500000001000d000f000500000000000000000003000000040004000400020005000000000000000000040000000000000007000f000200010001 else (if page < 5 then 0x11000000190004002800000000000500000000000400020001000100030001000b0016000000000001000000040000000c000b00020006000000000004000e000900040007000900000001000a0005000300050005000000050000000200020009001b000400000001000300000000000f000200340002000d else 0x800000000000200330001001c000000030010005800000002000a00540007000d0003000100000002000700150002000000010002000c0003000000010006000e0000000a00000007000000000009000000000001000100030001000e000500000001000d000400050001000d00050000000d0010000f00000002001a0001))) else (if page < 9 then (if page < 7 then 0xb000300060005000000010002002800000000001d0001001e0001000000030004000b0000000a003a000600020004001700050004000000060006001b00110027001900060005000600110000000100070004000c0004000000010000000000000003000000000004000300000002000000010005000400010000001f0000 else (if page < 8 then 0x60001001700050003000000050000000a00000000001000000000000100010000000a00060000000700120005001200000000000a00080003000700000000000e000b00000002001d000000050002000100210000000e00010004000400030004000500130000000000080000000200050000000b002000150003000f0000 else 0xf0011000900070006000300090000000d00050001000e0003001f000000070001000000020001003c0007000200080002001100190002000600280000000500070006000f0004000400060002000e001100010000000300280007000300010002000900010014000200000000000500010000000000000011000900000002)) else (if page < 10 then 0x1000200000000000000020012000200020008000b000d00000000000b000100010000001500260005000e00020002001100080000002a000000000003000200290053000700020000000c000a00040000000d0001000d00010002000000260000001a000500050003000000020003001e0000001c00010001000100070001 else (if page < 11 then 0x46000300010006006800130003000800000000000300170003000000060005000500080007001e00000014000300000004000c0003000600030000000100070000002e00200008000800000007001d0007000f0003000b0007000f000000160000000000040000000c000000090028000000010002001a0001000600020003 else 0x700040000000f00030006000300060016001f0000000100040000000500010006000900040000000d000400260001006600060003000c000e0005000800070000000100020004000100010000000e000600090001001500050013000a0005000800010000000000040006000100000039000000250004000e0000000f000d)))) else (if page < 18 then (if page < 15 then (if page < 13 then 0x1300000002000000340002000900390006000700010034000300070004001700020020000800020003000e0008000000000007000d00030071000f00000003000d001900070000001000050024001900010000000000000001000e0002000c0005000c00000008000200010008000f0000001b000500020001000b00010002 else (if page < 14 then 0xa000900000000001100010003002d00050006000f0001001200420001000000050001001200060006000000000004000100000035000500040000000900010002000d000400130011000000130003000200230001000200020014001700250001000a00220000000300070000000400010015000d000000000002001e0038 else 0x3000100000000000100210006006e0018000000020005001e0003000400100003000100250041001e000000470002000200010008001800080001001f0001000a0001000300000000000d00aa001c0001000600020001000a000000000001000000040005000b000500090001002f0000001300000003000f00020002)) else (if page < 16 then 0x2000000010004000200000011000700170000000700010000000e00020011000100000001000c00100007000a005c001e000300010018000000000006001c005d0000001200080000000300020037000300000021001600000003000000000017001200000016001d0002004800020006000a000000000000000800010011 else (if page < 17 then 0xb0001000c0000001c00040019000f0012000100080072000000040011000c0015000000240003000f000d00030000000000010000000200230002000a0009000a000700000000000000000001003300800004002f000200000000000b0001002c0003000f0000000200080007000300130000000300000005005d000f001f else 0x32000d00000006001a0009000c000d00070022001f00000000002d0007000d00280058000d0017001b00300004000200000003000100210000001c000a000c0001000e0009000300000006000f000100060003000000060011000b0010001200010001000f003700090009001600000002003b002600100059000700410005))) else (if page < 21 then (if page < 19 then 0x1a0002000c0002000600000006000000080005000d00120005000a0006001e00030017000700260002003600000004000c0017000500040009000000010000000600100055000000060000001800020000001f00010015000100430068000500460001000b000600000017000700010006000200650000000b001f00160001 else (if page < 20 then 0x2000700050036003700060040000900100008000000000030000a000400290000000500010000004e003a000a0002001900000007002b000e00030001006c0010003000000027002e0012000d000b00050005002900160000000900000008002f00000002000a0001000300070003001c008a000d002800150000000a0000 else 0x1000b000200210004000100020038000100000006001800010001000b000e0005001900190006002100030015001e0028000d004400070000000100000010002700160002000000000015000f000500090000000300090000000c0005001d000000020002000c000e000600120004002c000000040010000e000300080029)) else (if page < 22 then 0x50002000d000000220004001800080000002b000b001600000000002d000000010002000700120005000800010007000400090036000100290032001e0012001100260003002a000b00010000000400270003000600000003000a000300030006000500020000002f000500070004000e001c000a0005000200070030004f else (if page < 23 then 0x2002f000200090000000f000000280006000a002d0006001100010032000b000200100013000a00040010000d0001000500070024000f000b003a003b002c00040034001f0001000f0001003d000000000001000000940001000600000000000d0052000d0038000300070000000d006a00210003000600000001003e0003 else 0x8))))) else 0
  | 6 => if page < 40 then (if page < 20 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x40007000200030001001b00020000000300000000000100000000000b0000000700090000000000150000000500010001000600060000000300060004000000020002000300000002002200000007000000000019000900000004000000020002000000320009000000000003000400040006000400020002000500000004 else 0x4000600000003001d000100010008000200050001000a0000000b00020002000c0006000100000005000000000000000300000007000300000001000200000003000200000005000a0006000100000000000100080006000000000008000000030001000200080002000b00000003000500010018000300010000) else (if page < 3 then 0x400110000000000020005000f00060003000200070002001c000b0005000b000200030000000500000011001c00010000000300020035000400020009000200020008000300000004000100000003000000020004001f0000000400010000000000020001000500000002000800000009000100120001000f000300020006 else (if page < 4 then 0x200070000000f000500040007000800030001000a00000002000c001e000700230000000000010004001300050002000400110000000200010001000500120001000a000000010004000000150002000400000004000500010003000f000300080006000000020000000a0013000e00090000000000000008000000000000 else 0xd00060000000d0002000600010000000000000000000700010006001e0008000a0007000a0002000c0000001500060015000500020002000000060004000600020001000000120003000500160000000a0004000200000016000100040000000000150010000000030003000000010003000000020009000400130009))) else (if page < 7 then (if page < 6 then 0x100040000001000010001000c0002000200070000000800050000000500000025004b00000003000900010000001800000002000f0000000400010000001000030000001000000002000f0001000c000100000000000000020001000a0006001b000400030017000d00090000000100000006000600080005000600000003 else 0x200190000000000020001000600040003000c000300030006000a001800100011000300000000000100120005002200000002000000060002000900080000000a0002000500030001000100070007000b0003000700000004000400010001000700010003000200000000000d000000050004000d0003000c00000001) else (if page < 8 then 0x24000400050003000000090002001d0001000100070000001c000500020001000b0001000700010002001e000900130002000a00020006000900050001000000060008000000000012000000010002000700000008000e000000010009002200000000000d00000003000900030004000b000000000001000d001200020004 else (if page < 9 then 0x70000000d0001003e000200000007000300000000000c00090001000300070001000100030001002300040030000000030000000d0000000000000000000b00020013000b0001000700050000000f0007000300060005000300000003000300000000000a0001000e00060000000100030002000200020006000200000006 else 0x40000000e00080027000c00100000000b00020005000000010003000100050000000c00020000000c000c00020000000d0005000900200000000200010005000b000000040001000a000000000010002b000000160001001000010000001c000200000001000d0000000b000c00000007000000000002000100070000000e)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0x7000100090006000200020013001d00250000000000150002000200140000003200000009001d00000000000000000000000500110003000a000100070002000300070000000100030004000700000000001600000000000800000000000d00160002000c001400040010000100000000000e000000000011000000000000 else 0x300220000001b00110002000700000000002d0044000600010007000d00110018000600020000000c00000003001e0000000100000003001c0004000000100007001b0010000b0008000700000009000000010000000600020005000100080009000500000000000900030001001b0003000c00000017000400000000) else (if page < 13 then 0x5000400040001000100010003000a00000000000300050003000000000004000a000a00070004000000060008000a000000150009000b0001000600000000000e000f00030000000b00000003000100010000000100000022000b0009000000180003000000090010000400020001001a0000000300000001000200000006 else (if page < 14 then 0x1000e0007000600080011000d000200000021000c0006000000090003000000000002000800060001000b0008000e00000004000d000e0008000400200004000a000f0000001700020003000900010008000a0008001c000e0001001c00000003001b000e001100000004000a000500000001000700110006000800000007 else 0x100150000000a002a00020006000000010001000600030000002600030000000300080006001400160000000100020000000000000005002600360003000000030006000300000003000300120000000700020002000e0003000a0001000c0000000000000000000100010001000c00000000000c000d0026000000020000))) else (if page < 17 then (if page < 16 then 0x300000000001e000c000100000011001000030006000200040019000000000000000a00000011000800000003000600000000000200000008000400010002000000040000000500000007000700110004000300010019000500020000000000030001000b0001001000030000000300000000000000020000000000060007 else 0x12000f001b00080001000f0025002100000003001b0007000400060002000b0005000b0000000300000006000500020000000900090007000d00160002000800020003002300200002000300020000000300200012002100000006000500010003000c00000005000d0000001a00070000001b00050020001c000100020000) else (if page < 18 then 0x1b0014000000000019000300180002000100060001006e0000000900020012001c0005000d000000040008000400070000000a00020038000d000600060005003300220002000100020000000500110002000100000003000000010002000800000000000100030004000100110006000a003200300000000f000000040004 else (if page < 19 then 0x700080001001c000e0004000000000004000300060000000000050005003f00150000000000080002000c0003000900020004000200000007001000270002001200010011000600100000000d000e000b0032000e0000000200040005000100070000001b0000002100000005000000030001000000100015000100060000 else 0x9000000010002000000010000000800010000001100010002000700000001002e000000090004001600000000000e002d00070002002f001f00070004000100040002000000060032000800120008001d000500010000000300090002000300000004000000020014000400020004001d0000000d0002000a000000000009))))) else (if page < 30 then (if page < 25 then (if page < 22 then (if page < 21 then 0xa000400030000000600000006001c000b0000005d000200090042000a00050018003a0000000000020002004900070002002c000700030003000100010017000400030000000200070006001100020001000a001a00180000000e001900040001001b00070003001d00090000003e0078000d000100030011000300010006 else 0x1002f00000000000700000000000300000002000600000002001a0011000b000200000001000b000900040004000000000000001f00020000002e00330033000000110002000000040000001000070001000100010000000000050010000800010002000300120002000000020007000b0019001100000006003900200000) else (if page < 23 then 0x30015000100000001000500110004000800280000000f000100000003000d00010003000700000006000c00030000000a00030009000100040007000c0000000000070009001c001a0024000500010021000f00020000000200010000001800030007001600010014000000010000000400010000000a000d00000001000a else (if page < 24 then 0xe000000000003000200010003001d0000001a001d00000002001c000600000001001e003700020000002300010017000800210000000e000e0000000000000011000000000000000300000002000500040007000000190011001700000009001200010000000700000004000b00170000001700200001000800070039000c else 0x30011000800000008000f0000001300000000001400080011000600010004001d00020005000200000010000b000800000028003b00020015000000020008000100110002000400000040000300010000000100010003002200140032000d000200290002000000000000001200280008001e000000000005000200050000))) else (if page < 27 then (if page < 26 then 0x100180017000c00040001000000010012000a000000040000000100070007000c00080003002e000300030000003a0000000d00010000000000130001000000080013000e001200030001000c00100000002c00040016000b00090017000b00050000001000000000001d000b00000002000d00050020001b00000042001a else 0x800400001000000120012000d004500040002000000210000000b003f0007001400000005000400090003001000080002000200080000001b00030001000c000500010001000e0000000100060002000100050006000500000002000500020004000a001c0001000000260000001500180025000200000008000b0008) else (if page < 28 then 0x1000310002005c000f000f00210029000100040007000a000d000b00000000002300000000000900000007000400000000000000040001000100000008000300100022000400000005000300060000000800020009000f00050017003c003d001c000c0001001a000f0004000700000014000700040013000500010000 else (if page < 29 then 0x500020001002100000001000600000000000100450006001300180008000e0000000100180002004e0017002c001400430001000500030006002600010000000c00000008001b0001000e00010000000b000100050008000000080005001b0004001d00010001000e0000000c00180000000a000200170000000300010003 else 0x300330000001c0002000300280039003000020050000f0000001f005a0000000b00010002000000070000001c000f0009000900070001000200110002000c00060002002c00200000000000540000002000030000000000000006000000040002001d00090000000000010003000900010000000000050029001c)))) else (if page < 35 then (if page < 32 then (if page < 31 then 0x5400140007000c006d0000004200020000000700010000001500000000001d000000410025000200190001001200090000000b0005000200070000000c00020019000e000000070047000800000002000000130003000a000200260007001800080000002a0000000c0000000000150010000000000003000500400007 else 0x10000000b000200020004000e0005000800080000000100010002001a001c001600080009000b00090001000300200023000000050001001900040005000000000000000c00040001000a0022000200140001000d0002000400030000000800100003002200010001004a0024004000000034000500030002000c00000009) else (if page < 33 then 0x50000000300090013001a000000010010000a001c000b001000020006000b0013000000020011000000010001007700140003000700000035000d0005000b000b001400050001002300000000005b000100070001000900000000000600020002000f0000000000020043000600270005001f000600010002002600010000 else (if page < 34 then 0x110004000000060000000e00030000001500090013000000000008001a000c0000000e000b005800000024000200030098001200000007000a001600270000002a0000001b0008000300010031001a002c000b000300000002001a000b0007007c0000000000070000008100070000000a00270008001a0001000f00030015 else 0x1e0008005c00140001001d00130001002b0001003e0003007d00550003000300210002000000040018000200080023000100060005000100040000000000000000000000560000000000270013000400040008000b000a00230004002b0025000500010006004e0000000200070001000e0000000300050004000100000002))) else (if page < 37 then (if page < 36 then 0x1b000000180044000c001d001d001200000007000200020000000d0015001b000e00230001000300150008003100060036000c0010001100340003002700110005001c00000003006d005800010002000000050003000c00000000002c0012000a00030002001d00180000001000030000000500000013000a000000010011 else 0x30000000c0001000300490000001d0017000e00020000001e0000003c00050004000e00170000000200040003004e00000003000c00030004000500620001000e0000000000030050000000090004000f000e000000160006001a00080012000100170002001b00060028000600060000001b000c00200007004b000c0001) else (if page < 38 then 0x35000100180037000500010003000d000500060001001700110000000600050001001500030007000d00110032000200020007003d0006003e000400070012002e000100060064000f000000340000000100080024000200260002000c0000001900120002003d0005000c000e001d0000000400000003001f001900190000 else (if page < 39 then 0x400590008009a000b0004001e000400010007002c00160008002c00490004002800010000003b00310001000100100002006e00000010000000060000000c001000000015000f000300000001006d000000000020000800130032000600060017000000040002003900070061006d00000001001e00210019000400080000 else 0x160000000b000200010001004200060028)))))) else 0
  | 7 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x2b0001000600000000000a0002000300040000000900000001000500190002000000020008000000010001000300000000001a000000010006000800000003000000050006000100010000000000000005000600030001000700390003000600020001000000010001000100020009000000090018000d000100030000000f else 0x3000000000004000500000005000400180004000700000001000100030000003300060004000d0008000100000000000000000008000500040002000b0001000f00000007000200020005000600060006001500000000000000000007000000010003000e0000000a0002000000050001000b00000005000900000001) else (if page < 3 then 0x9001e0000000500020012000700000002000a001000070003000c00060000000f0006001d000100040005002900170000000400050000000300000001000500010006000400010000000400010001001700050002000400000010000b000900010000000800040003001d000500100000000500050002000b000100000023 else 0x2000000000011000e00010004000200000013000d00070001000700000000000300000001000e000900010000000e0001000300200001002000000015000b000b0026000000070003001e0016000000010007000000000000000000000000000000010000001a00020004000c0009001800000015000d000a000800000000)) else (if page < 6 then (if page < 5 then 0xa000a000000020003000100000015000500010003000500070001000100060011000000020029000100000003000f000d0006000400000009000c000000020007000e001600010000000000030014000000000002001600210013000200010005000500120000001900150006000a00010003000600020004001200020002 else 0xa0004000100070000000900310008000c003c00320000000c0002000a00190000000000040000000200060005000b000a001800120004000100060005000a00220001000000010000000300090003000100030002000a000b0000002700000000000100190003000400390000000200030000000700460011000500020008) else (if page < 7 then 0x3000b000400000001001d001100230016000400100001000b000600020039001f0031000000070014000500030000000900030000003e00030016000800020000002b000900020003000000000001000c00070010000a0004003b000b00000000000c000000000000000000010005000e000800180026000c001100020004 else (if page < 8 then 0x3000200000000001400010001001200020007000b00020000000900000001000300050001000900040007000600050001000c000a000d00000005000000010040000400000006000c000b000500010022000000050000000700090006003c0000002f0010002100080001002100080009002200320002000e000400180010 else 0x16002d00060004001700080001001a00090013000c0001000b00200011000400050057000200020002000e0000000000000006000200060024000000000003000300030003000b0013)))) else 0
  | 8 => if page < 1 then 0x5000400000004000d00000000000a000500020002000f00040007000100000000000300020001 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x200010000000160022 else 0
  | 4 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x9420a500b7200000a700196027600000586012601500972053009a20100000004f000000000080200860719094800000b46000000000934000003460056002400000b5808260af0080800b803e700a00000084006b003130000000009000a380020004600000ab2083803160b2401360a5208b600a60a3006f6089002900000 else 0x68a09d40228019102d001f607f4078002660000060605d002c006e0000003800000000006a00170000007b60a8a085409600b20021008620270000005f00338051607c0067000d008d402c602d607c907b402e8060001a00000008009510912031500140b50000006160a2603c00a10043802b0000003c60318071b09c00b64) else (if page < 3 then 0x7a7097009200800000003d008320a64002504e601e60b2603600a9201f108f609b603560317048604580b380ac4030607700ad006260549098009b00476041602a602f00ab800c0000006a802600101000007e0000000000ac600000000001601110ae80ab00030018807710904000008100790066600000000014600000a24 else 0x13709c8009600000000000005a609f00b700060001001760656071002000b440b3001b70a32037a070809e2085602b403b6099000f10aea04c6050608d109a00ae003b108920206070003f602f2000007e2093002f405d8028003d1037601900a76082405b600f0012006d008b408e2039709780a620a060870000004400000)) else (if page < 6 then (if page < 5 then 0x3860820098800000527052602a00026005700210b520420094004f405960906005008e1016800000466069007d80959051400000ad2021600000298000007f602360b780040030900900a000000076107a108c206d60a1808500180025602f8025107c3098a03e002e002440000088607920000057607010aa003a0096607b0 else 0x910000009d001c6074006780a1200f60000007005e408a00556072009e80a740a400b9000e008d00b8a0000000000000000000002200000000009e008e809c20953000000000000032400000ac0000602860b40007608fa00c60000049608b00b94067a033a08e005c60925035a024008840760000007a501d6000001d10868) else (if page < 7 then 0xb32000007d2003607300a80053102f600000b60000000000636083003a804d6009107220a90000009d608c807a00b6609640af209270b8600000000000008c0044805660a600860000403200000064008d6000001e007d006920aa403c404280b0007c109920a200921054207500a8800c40336023006880b1008980314 else 0x7f00a040000000004a600000000000001a90000052501a804b006c009500000000000a1034a039609b4040601600880))) else 0
  | 5 => if page < 83 then (if page < 41 then (if page < 20 then (if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x620937d06da07fc43472000000005ec100001bd0674102880b503a0178e159870000000018602f122c1172f03924363a77295af0123901b100007d8425a17b0859d0685000003c7201b249380000602073204428268a791039e0000059827d6023f86ef0830065f0723487420b27049812f67cf00d30258300704813 else 0x5e50000047511b31191b00005b20704043a45a8023605fb176b087e08296185000007d980000000041e0566a52321ab0000000005e905c710c486ad02ac02320230986ea201187f216993d790000000032d0422731b81c61819000000d4300005b80532300006f3181363cfb6a2132ca80047312000029d9335b31d05de047d0) else (if page < 3 then 0x85c200005d4b00006d2602d10000691030804d7b4d5157cb7ed03e8212582be252a21d1027f118a8838937f40b367c3032306a502cf15842020779605a446460162005616c1034a441265b0420025c004734714930e12c204a706d705c424000535141826ed06fc05a0109b0000033b228702cd12de2276032105260000068c1 else (if page < 4 then 0x1fd921f2035334905e404f0936025392017a4142645046e010c74fb91d02344200000000000000002e900eb300004c2000000000163000007af474046ec0000065c545f105b100000000000000001fab000016705230034079063bb80182000000003ad27b28715320c04ba3000009606bd10000623002e705b67c107e220378 else 0x41c749115cf434006092022654605fa04d135f211cd84f107e504b290bc613c97c9287b40ef15ce6736016084b7b22f0415b14f858601ca06d3400006a104da0091058c46d14000060c0638153c2869000280d774ffb28d08860000047a4000009d000000560617400c886185cb00000588060415a640000000038a200000000))) else (if page < 7 then (if page < 6 then 0x79f04e4b7d86114074284de01f0221f06f91371472040c302c6026507cb01f906e197a0053e012ab32586cd077551016389212e0695101c33d8226c158f91b821780323a5bc04f00272203a01d3985d002583879079847101cf03e9b0b262791688159f2717b07c230c015e01fc326d956eb105026d30f3a479267c1466264f0 else 0x41b32966391063b0829077097f924266690048694f90638751d5089a34307db0329a01841300793078814bbb6b0b1f807926511b60615910202987c60db05c821a14275011262ce842d07a2a0b405b3007b2297635d617a036211e8033d009f8735037d91e961ac057905dd163d00ad60d803939201b78f82ff647b284b47e74) else (if page < 8 then 0x1e7b36385720517b56b92f566430305a0e0606c6000033947375000021b23d807e442aa0657167506370333033f02f3111d707aa34f04f8b01471c721a6021802d306428676084d4166024245d0072e62f79877825323ab07ec210918740000645a04e7a0b172b4160f4738649b10f402e21492479c232b8205822a52fc28542 else (if page < 9 then 0x81300000000073d34490000000001c145d5a2eb600007490000005e826a288e069f000005ae108e9250227e0814067311ac4088a1af80cf747325a205df100e0420004b461086c9044f255b06590126683f44f4903661250597800000000258459c44fe9082487c06f83000031e046901e3a4c3b11e46a7079000bf9019841b9 else 0x7d5266602381000000000ce176e1775062f11410818404d60d490d4b08e2677166a47f787e241be80e2067c07d900000334829f80000449200007b3404861170000000004fab3ac808a20000104226f200000470306868084c7015603a83223863510f260fd05af169b0010a0ca8612154427bb62190276812f33a0041105028)))) else (if page < 15 then (if page < 12 then (if page < 11 then 0x49720000053134400000743070d22fe8653000000d1046d446b223046e403bd0031815d000181f82600100007aa025e500004d6059006393534200007a401600000056b81bb000000000214808463b55066002167ff00000887600000036290767e40000639073905a496d16570464b051a90bf0086273296730556452542028 else 0x1ea50e66000000001bf22270161020275f81470071d084e4750169a1260500003c6045b07c202404362270003124633084b6000000001f3052ea88700e870000000000007bc063532de0000001580000000000c10000000087c4723671b06de0000049915d9788446c925d4020e24af04c807e76000000107d800a5448cb6d58) else (if page < 13 then 0x40206e7028e227206cf14e517b8a033273b166042fb82d5814d024102f32095a692180904ab00000158974121d6b7bc8222221184e2b4090772124916aa019a741f80b7879b159d27780017446506cc207202ed053402a5888e279896bb861207ad23f016ac122665ca8041000006dc13fd049a90000000010d66b9457384250 else (if page < 14 then 0x3e4000080006101000065d2000010805b522dd800003584453000003a81000000008846012803904e69076085f2801071d6356440800d4038225c2200e22f4a811053625288006085a00b64726027784b395a5032403b0b7a924ad803f17e4660f65630054054526b9636d137927763434026f82ee284d6782150397440 else 0x224200404dcb000010c0262b074663a061f0385401f17a66037286644ce07f6060f10fc14b49135000004a862d11544000003a9b7ab1463a50703b1011363e601d16851213e07a643e1225501f1809f27e9419c87b5818da0dc22cd04fcb18a503463f987ba4753033144d69495083082330277038f200007ec0000056067dd0))) else (if page < 17 then (if page < 16 then 0x6bc260b008c000000000000084d273621510000000001a400000620b00008780000000003b2173006422000000000000000000000000000000005bc233111cda000054c22e5000005ef17518245a0790000020004c99771801020c20000081864a307eba0432536084d011f742bb208b1ca213681f4043700000835816120000 else 0x88804b31835a294700000000000036b04a816ff14021083045684350000025b6373840b084b003d960d000004362000000003c500000516971b35a790f900200000000000000330141245e511987632100002f705658204238204d190000000000000252831264a13a247761461900000aa07aa72d905ab47fa65f0137c9) else (if page < 18 then 0x69616606000042265872820880347bd08580514b36c260f02a40137066e864404f7b07304ed90e361d125997657900000b1636e247c6175071d127182828567a1810000028f639e288a26620153029a0014047b0000064c0000000001a3043b875c07834773115a6521331b11f720000000000000c680138000039db342a7f30 else (if page < 19 then 0x81a03722032070b03d605fe60c40464232e80d9334e0133014604b4169501690000010630590124946b87e00472702f065655a7a497016887f5262872c9065e0000027380ff80ca00000145800000000325000000fb40000000025a6533075e14ea05a883ee1274613364e8b4b435c3675e27a810890012273f07a7283620000 else 0x142023087c4076201c405bf0510046a987713bf63390000000006f407e9687a238bb73405fe129f414781b3034116d2142c03c497de10000000019c076483bb003706a91071109205b90806088100d24218a1b6681207a582ee023f0515920913900697126d25a1084e245405d220bd2000062947e800160362000001fc15211))))) else (if page < 30 then (if page < 25 then (if page < 22 then (if page < 21 then 0x23a8000000006a001c415bb61ea86be05d604d9285d2466008010b600842735506f00000822b5c5142a241d10932793800004ba179427d00000000007c6457eb000020b422932dd0818019200e181b6402102f8056c600000000000052b249f00000000022802ba84c1979112b8165a01c662a7610b346e9012440db86302346 else 0x81b20b0170f115f82c0278443cb94deb728082c2582480e83f2950f04b024f39870076306801201374f978007c906af16610000013b03ae000000000559b42e100004ef90ea10000000025c70000000084b1000088405830040058093a26000068006c20064000006b29000002d00000000067e1000022e62fb03e2b25e110f0) else (if page < 23 then 0x31d400000000000038982e003ec85c691ff904f001c63ef12dc162425ea14a195bf134104cc72df02b2684e013f60a1816667ee072d500003e5026d877882764535338184b973d42000024b20fc22400110068c079501e281c314be4314860215ad884440000098b23262ce007e4000065b03ee319d70000000052b0 else (if page < 24 then 0x46f00000332000002ef200004f5b0b30838b00004e20278078361f920000058001444f297011471415207f8082d0663076283680752283c03094827269a028c45a8287146e720ed0112081e0739500007fe000000000771200003ea200007ba657f07304000068a167012bf006866a0121c025b14ec0419618141c580668 else 0x23920000001271800af121d73b986ca167f671823941336a045165914d5a80d435465a6039aa000020b62841000065000000452107f237e20000000000002fc814400000101000001da0000000000000342800000000000023d30d2000003eb200003b80000000000000629632803fa0000079c05f160000023600001cc00108))) else (if page < 27 then (if page < 26 then 0x50c8247085884e7844d10000808087204b7932b07d703f393a5174e13da000006fa74eb500005d493af85ce000d600007c620000000009982df8823037a4000068715a3859026a204d0766c7000031015b311e9563201f125c0154626d004e34624409440fa88640669267d0055766f047866c8945d67f427b901c0036e0 else 0x7d5020c577a04ddb00006a7141f259c0104078c0202b0b880000097700000000000000004ed06fc846c47064000023e00000000000000000000000000d9b0000451078503a211d89320a000040a67bf04b95367627090000270376c006d80000778437205e8066117a3253e2205200007a30000022915da98170000083707cc2) else (if page < 28 then 0x39982a900c01767070e12bb0595719080000000000003f701c380000859a7ce0000027c086d000000268764280165a681c590cb03eb0710271c000005a9878465c4043c066941b10524a585024ab0fe6000068b65d1260881730851477391c98134921640868288052204ec96700000000003e3019b034345e00 else (if page < 29 then 0x76e0039633e04a604460743277e02b5061b00000100664311ed000000196011880e243d25f3082c47f6806b60c2629702c5b0000138006b0225234702d70000074503d380000576b50182fc07c8431c85b725ff075d0235411065ea00a8800003ad05d8900005ba03ed10000463800003ffb000004a07a98000073a500000000 else 0x2c77000000003df0000080f00444664067817c760cd107f13e81432000005580000015185b703b720000259072400a211bf802e085a80c9028003e706f60037a630824d061507801116033c166e22da000007ed82d314f126cd67e0873c80000007620100bc06dd8000064d041a183c20000000052480150000019e042421371)))) else (if page < 35 then (if page < 32 then (if page < 31 then 0x2350626000007f386e0044184966000077300000000057f2000000007c7445a5065136a40000778206f1614035eb459010b00000000000000000298055416eb055d477a614c171e073a0000001124eeb0000184000000000433600000000000082e6000000007aa1395900008480000035b0603144484ec81030000086a42110 else 0x25d00000188000005d90340861c06b416e300000230005460dc800006228000088da76222d0100003f72000000003c996d31599000004e04000000000000000009110000638000000ab0313035604849044214a0202435018430105675f0000024380be678600c3648680000647025240606385804e65cc005c07fd04118) else (if page < 33 then 0x75b731ea07505bb47f140000681800002e300956205000001aa6000020c800004c606310000037b1000000003960068012001f817b00000086511b907b366dc7000079b6226a0240000035753450743439b233d8351800005dbb0030706622a000001d5b00003c2668c84c90000076f24e5a70d135b482a128f062120000 else (if page < 34 then 0x63a1708001c062570416857453b41c64719961888762231400007e1007d4634750d064f822ba04a202055728090524506ce224904828000083e236740000000083108440316881d080148291311848d0343870c149b38622000000000cc44fe81d2020901dc086e86ba463e104d0000079b41b2968a45090593a840481a80000 else 0x6ee068d820a913e6472517e0616135a039791ee259714c4101e004360de02f286ca000005371077209617a0800003cd2187a1a7208193ed300001cc244d41778000014d600005aab000000004d48000019c318a026d10a6871a235f84fd871c4575126e161510a607d2083306c7048397f22787111804f4b40588050))) else (if page < 38 then (if page < 36 then 0x289000000000000000001a20580b1790000000006b90000040f884f0445b00000000005816a021c860300000081417d03c3042b9071005f05f50661801a460110000000043800000617082170000000088214720000052d187f05aa97d4600000000000074d05600322a0000476200001d5874a90dc00646879882691d1a4248 else (if page < 37 then 0x28d2000000f623d022f4000000001d081fb13990301a094085347ea43954000074060000099008c3014b2630613173b76cd116e60000349a0052000000006d02348142e86df0613000000be100000000269425d4000024662310885200003d504bf71c5000000000000000004261000000007d4471170466707000004dc088a0 else 0x6e201a78196a0a705fc185e049328148000073d404a6499283e03f49480172a26ce15e701e622bd06d36326a3f5088b5383866b622202a89716122096f9511e84b577f8804b0526260a012b02da8571804804b1062b070603dc00892686138192cc66b8400004d3871e4256200001f43182826d0128688084df030f043306890)) else (if page < 39 then 0x65d000006391127000006250266640704604720646d87e1217b0000024c63f6019441f504da97ab905411bd214307c9811c73c486b4000007fc0683100007fb212a64cf47674080037026e34000000000170373000005d620000000036821bb1000030d00af00000324a3e4b5ff1148600005ad07e7070313fd67a6046000f50 else (if page < 40 then 0x13184bcb2c006a60412080200ec7193656482d29000005a041485e1003bb393001c81197492003e61fe100001c1204f834ca18700000214010b95309508013e454988022239112173b483950739100000c5003b284c074d258a8000052090000428286a021704a905009102669601a878390190a53f001d66e1b0000 else 0x84908150681242f63b90159862c818c01df2426777436db125d5244864c137825bd6103165c77f7270c4724200005ec000005cb6292700003378157842d642581e09213049092db100006991785888317e403ca25fe7263b429032c843102a5057e95f2263c06fa112f924f2531581a17010686012160000000006a000004cb5)))))) else (if page < 62 then (if page < 51 then (if page < 46 then (if page < 43 then (if page < 42 then 0x3e663be0413a672016b040c074a069d050083f62875223a276a4540943e40c192e4081817a44557839f1282087d05ca065d81b8054820726000000004ae9632972120000000000001c8047f000001e9100000000000005700e50670380a0195009e06bb25b6b6302748032006bc070f6000066a018e409893bf479c809386bf0 else 0x2f3606410360722050594d8b82c8267600e826e07a025f14006433696f510000796159f85d61364000004e0955a000007f00000077b316f110527c60578b00000a3000007bd60000641000002ee815b0377422f125a71da280361ad07e2027b0076625a01f6984a4106457001b604fdb2ea00b463bd1795184764dbb5c19330a) else (if page < 44 then 0x4b16820a0000140021e800006621000077650000000075a9830200002ad02250000034983070571200000a501f105f1100002c572a52000000000000841400006d2700005e81000015f00000839235da60c13a531373172012d100005be0000000000f805e607a70000068203414006638300000000064200000138868d21cc1 else (if page < 45 then 0x4e9b31ba0000660000004201710000000c863ec93154177000000000111600000000082600000000475071b12646394300441d1187d40b70000032887ae40cc075a347c4000021fa00004ef06d803a31000058e7000000000000000066c53f9a0000000060a405a80000000057b03f4b7d5800000000259300000000 else 0x81420b8073713298099a3520586743d055007a01313a42086f206ed270416d6870e0031614c0618200004dd9000016f02e6088880c0000967b3013766c306a4055e2370071c62f71000000005899000029b600000000000000005ae0000038c00000384055f826800701000000006631627661a174996d4421a9000078684ff9))) else (if page < 48 then (if page < 47 then 0x25707ae66f70020102b865504b000df625b400005678512174c3047608f00d901bf149c90d6030027e9034186d50067038e121a466506e224aeb3b404e4937525ba175e063f07051340a77b13dd20510377200c0238a3a4945a28344125270c62a884a0854d879f119645b8182e408505b692fea53884982586542a062108730 else 0x9e41c901f53665182702e42091688c243f8558973700556388b26b08418494b78106a303ae81e506d017e363a2072b46570226247e66d5302c0737725c025604bc96f00831859e03b575480770052226b10434480d636d266d03aa0340122640fe031c07ca147902ca61e21423279315a05038876d200005f28073635006480) else (if page < 49 then 0x30407f041d0026b228b063383a194dd05eb006304771873480d022d200000000431200000000000058932758000064916db03af942a854e8386027b17e64639935805e205d72790171e6176013a9000067097690000000001cd965804f8965114b556fb019cb069079e057b267e04db00272378050ab7ad4386a1da107214ff8 else (if page < 50 then 0x4640b200007614392000007078532147401227879462f3018878303c202e08705046186941488b722439700cf50000551b008022a785043bf06e36883000002a105be86601638532e0000000000000000000004324443058a2118311b02016019a02d21e90712064144829562682a2000023720f0673d61d2987a42fa88452 else 0x59b087e26ac025d103940b560000170032215d70000052922e711fe301e632ba1eda2ae179143d3a0fd811f007000bfb7c527eb087b800003b305c34731000005cd005d0000062908250793260907ac20c10688044e48858852825c500000000000036f233a901b012a94f922d6617c07b887851555931a80fc001a976a070d0)))) else (if page < 56 then (if page < 53 then (if page < 52 then 0x52c20818242882b000006a815e4123c07c50770300004dfb042845947df034b020b0236213a02480000082f47710000038488194000000004730717903d784f855390c91398221916d18502a749b436831ca30367f98232280307f2041e426c02e1032a439a800001b127520082577691d0a513088c000000000000074e31f88 else 0x1f2107a44a18017886007a282ba07c7032d8118977720ac06d123199781107b0000028d462556b60208853d058fb000073e5278100007b7a6c608502248645062dc06dd052905050102100007bd40ff017643db2000000004400000000002492591438e8000029e037e07a52277248f07fc600000f6061a0274088d86b306770) else (if page < 54 then 0x5ac200007d9280e06d62011038681ba0000033311dba1d245f70366275d83c561dda0000000037f91bf03a18398003f63cea1c204c02000007a200005bd47b782a70181644a86a8000006b623ba06060000035c97d103d00667002826d717b60615651922c084e1b6d40334a44ca24f05d20027851b785e26f812a380f07 else (if page < 55 then 0x76127e5476401ef41a4262e46e6a36d000002a4461e02fa03c541c605105295048331de222f2513403a655d679707ae0171062ab66b42f0206105b1016c65c6178400000000073d11b5084106bd070a02290226822d6202208a841c601c23e09766062d810204f6932705c981fb37e663f3b22e464415e0152c001201e415668 else 0x8446e902f60206a125a1cf675e865f10000000045e05a78596658121e1225403dea0c6038d071a03b784dc9000037c839c0457a09f06cc0150675c412a752d32284000017408454744200002a510f10345969e10000000060a600004e6b57401d527da024eb00000000850600002f983610000065c100000000728200005373))) else (if page < 59 then (if page < 57 then 0x82800e7062f9774906764cbb1e2082e037781df021502344317474f581f077c208c97270542000007cb463235be12a090cd0729071b400d0227817f65b06624075f801464d6b208943c85f413f807519789018d8698024aa67b100007916000026f979a04b6249644e0074c1000026f3000083f885b876d0000000001e941ffb else (if page < 58 then 0x2c1613d02ff041d008e340e00020314b16503b6463e074107f500fb34bd7404019907ca022607ad083a06b2b21d485f4012a6e48171136f070f44cfb77514a96433466d439b01d5085c0302a82b2203867405bd0616231f073142c2125b0211271d400000f30319a53a881964811656125f95060678088987688364209a15ef0 else 0x1468713403060a00291026040e126d110e6046d082111be23ed606367a90710869e0222b42380c80307674514e8961c1889a5750721064e475545b1236c822217f6267d281d13b206a9011a007e683608006373451eb1cb8528248892af865670c21000000a280405c946b7220c26b741679640128c6164643903e9923900000)) else (if page < 60 then 0x5ad12c053f194202851000006af7794047a647f82e390000000034d0455024066b8676f03ba915413254530b16404f795ed177f008604ac053f2046001f7369069203165091264e66690000059d487824665000062856b501d42799204c686f0129038f013b632c057a90ba00bd8044056126111251333840c18877287a0 else (if page < 61 then 0x58b00872303425c1227231d81ce072267e5600a00fb600007ea07594880a63321e220751145934a8298845f061e1293046c072d145b184602d4080705f0016d0028000003aca5cd433580da75b49735757ab3b604eab24e016c0694021541e585da00cc60000222807a061020b9006d900003290542209c000f40000000458b9 else 0x881249e914e001003b5001b509363d201c3079e23b51033006f687d675d24a594cd450c0568067a013910ad02ef0259420923fe922927cb675706b807aa57a1123c67f3260504fc8569018c62cc085aa2c362f78364185727ef05fb0498081004a4022a1305436600b965c7059280cf083b065b12c016e6881b0153182c05d10))))) else (if page < 72 then (if page < 67 then (if page < 64 then (if page < 63 then 0x54a041600000798b5df001b8699048720d992a622160782012b185400022283065736cf043d881a24913594064f281c054b07ba07f105f6006e015c002d84de946405d3000006d9023673ef71ea033ca66f84b2122a624a077b049d91a705e615cf074b968f10756747536526ba05f406ce062746c512ce9053845c021882bc7 else 0x70d866b00a6224146280447b2861410243e039c802e63fd17ea684a06d59306a01724efb5ee02fe01faa00b06f9316a84ceb658144c01db053c061605f8074ab3834036262b2459632a003143bc060b819c919707cd072c5182084243fb04e407b485ff903db37c03e8070900c7066e06f30611000000000779773975a408590) else (if page < 65 then 0x42a11e972ab03340231673e370200e421c102380071601414ad034a005f676e3285026070dd06970879223a50000000000001ce243c200006d2507d86ae827d16fd0000000000000000079c100a85f101340000000002b307f401b7003b97e3400003fa2741400000000000086503ba8258000006070256817f083d269c01ee0 else (if page < 66 then 0x51e531f866c073a10a903ab429c140fa26e3661256105f90045606980fb951203d7b6e422f1673b001f02a6025087332538a1da8404443606840626673365ff821a075f26c8b77527d3047703d98384483262be0078032087cc03524721450bb380202c17f282c862db026f003d600c34480468b46f60d0704302b0940116360 else 0x393b00006000000044d01830000000002e520000000042f756020eb962e04b8300007eb800346e50323874bb74f36680000048a900006c313760539007924aab82a0845034b26bb0191880281d2875092a4652a000003c045e3000ea38a0000032f14d58774049eb4b2b68e005aa54da5184014379db799009143cc23ab666c1))) else (if page < 69 then (if page < 68 then 0x1be0093454a20a802552000073a7729210e842f027e167f000006d20000000007f900000000064000000000025440ce05479000005b300000000000037f03a4805262120772339f785325e3126607f8246a37be034d84ca1355072d9608a00000000000026e95ee11e6020f45fe06f210cf119f785f888b13d9a2d3327a086ca else 0x6232000001921551485000826560774131107c00251041a51ea22f10000000001de000003974191a56d820a054ea80b07521715121791b4900002298000061b1681086606e804e3344311cba00000740353a78a13c108472520b00002020257300003a7932f025a40c5670f01a5669301bc0238673e140104c51124350e91558) else (if page < 70 then 0x6176097626066bc858612aa1742963180bb07ac068b00000000013e200000b1006e100002d803da20000091b5c84000000007b0218c411b7365074005520816040307e840000000042520000000084a27dc0000057301d044ecb86b4000065a10000000000003519000018980000000071f96a410000842621b04e712ea30090 else (if page < 71 then 0xb8a4fa900d4860800000000000043427a8400007b92407114b04100000068d04542062063450e780000714b1894009454fb501a6510000000004df972503380607118f600004f593c1288747f0600004d093a693b31000016804eb2115638f1092456a222125ce451cb77744a8778520000391915c6000045e200008820826b else 0x36c477335d580000000030a27ab30000484b2fe4849403b63a10598050427f5843a0369867e61eb40000000000006ce80000772060b2763819543e716cb01800000085ba123362700eb000006fa566820bb86fe0720040522cf06ab082414588026047c01a4a2a9107f0684100007302000000004ee969c1000068a014905d88)))) else (if page < 77 then (if page < 74 then (if page < 73 then 0x654100002f81000000001b8848eb4e580000321427524296380068a64d9576c456c057d061907af017462299000073f92cb08620000000000000690144b86cd42194556028e018b000004b1428a15f51853025a578a0000086f23f0048b200007fb0052000000a200000084a748901d47380138213797a7874021a484ee08500 else 0x1d7013c001a340603d66021400000000000087b0000041742c6482d407c0000038d70000346951f40e4803b3118b44ba444900003590332852850d387a8600000000066960102070616873c1783105180000000032e10ebb0000000070c000008760000000000000758177a40000304276242a2000000000000028e4123b27a1) else (if page < 75 then 0x4a945a9b7e8600001bc11b0074727de0630081b8000061d000006dd40b0037b07e30786227d0878422583870458088824cc452e867f447fb693100000ae6000061548560322888b7000086b000000000625162a98371507b2c46314500000000000066f200007bc2000000000000794800000d575b2901520000000045d40000 else (if page < 76 then 0x194084c81a9000746fb4545066a640a46c40073120d457c9084055c05e716ec43c064b8b361a00006d510f0084688680018024f813d60f79577025f80802000057d20ee625f288c80000158000005fd010a02fb2186849902286476061411ec22d00455b0fc8779060400e900a4077c017668710165134546520478424d2 else 0x6c051e74620302468b477d048916cc114b1000027c172025e11000076b479d9299723342c0402b03d64374456923468217111e723b25c9007a84d80438120c155721a1008988442355978b0197452f300000190179147f9877039f006d02c3772306802000038d6000000001b28000000006b3200008484000000005de1))) else (if page < 80 then (if page < 78 then 0x318868911db886913661736400005d38010438e0825167b000007c805a58000001a046217344541975313c3601ab82c656a04606014984962fd058106c5078d10dd600b47632385053aa6100324821e02c7159b27a5064a03d1b00003fc8029023e368c26aa170306ed8000043b200001864759079b000d73701317a68510000 else (if page < 79 then 0x7a465c500194592243f27795067100881b780cb679f4738401b48790000000004a697fa00142872446707f702c10000000000000000002a6106006504e607a9142e00000748b7b183334000000000000375003420be006003de87f480cb42e87062859f04d491d920d326c006ea0095052f100003d4054c05ff304e000006911 else 0x73b55d3a3a997b700132234201e4000000007701000000c20706000000000ea00782000000005f61000000003c8a58d236b2000070720000000060e15cf272b92ec061802f49000001d000000f321ae075640a1082d633ea72e52b1039c985987cc802704d280050858a427916b25c8008b012f201ca327a8294000083d009c1)) else (if page < 81 then 0x4b2000062204dab628101c113962a7100004b33000025001cf216d1000000002b660000457804066d304412000075506fa04f2b42114039050639d903c410001c824a50000079411590790487b2371682a8132030188674562059a0000056f0000000001540000075416d105dd072e408d200000d2600001a003bb97d403694 else (if page < 82 then 0x760112c06b7077706790813435a8011a4edb03512b9072a1106622ca13742f487fa413905dc06df946c2543972521036000043004753261b23522f302f00710137904e8047e1444030b2077082f028106ec6210200006d604af27a80765b10e2554679f638843e614565500b7e6064902b70746012f0875027f03ea006c15fe5 else 0x62f000002a8004c002b201f507a6641654b25f201bd84db94410000055e017c102b952762822855060e04a2b80c064e00000761000000000000062644ac86f1076822f500000671034b7000000006fc20000279000b60ca9631210762370654022a4885022d042c26aea0fb06a5129f0))))))) else 0
  | 6 => if page < 141 then (if page < 70 then (if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x9be0cf660000cbd0ca9101860000583884c64d904712c1e6000013a000001961cff000000000ba220000a39031b03b144a3800005a80dd30b8c20000d0520000ace000005760000000004c2000005cd600003b6675e97927024297405f800000000036660000891b3ce06bf00000299a00005af6079a38620c3800003488ce71 else 0x65c09ab06cf2d3b0b939a6610b10c40125803bc074000340c140a6c0ae30c1b0a1795252255413534a901ce03a6348c897c57de93f40b2a4373216179a3849a47a2b47f00000d3123b7020a69fb434a5d1c4bcf2000022e400008534d47072411ae1b470a688c5b09e480000a272316bcef0667608a4001a67045b745519bda0) else (if page < 3 then 0xc7a455e07f80d652baa19fa08f1091198c40b8c827f8060051f1000046425f5100289f1038e22100564112c8a565869080b9c2a065a64ae263f625926b0651792138a0f945483f9057901be0a314c398c7d58140495206b0c9904672d41185a6655107c82084609ba670cfe8b961a04092e2a193679271668ae015a650301431 else 0x25c00510ba200000aff1cc5009600000c5780b50c844295a0000af267ef16df61cf67e5a31604f694ce00000c8e0d978d52434a8000082600ee89200b779000000003a917bc4a7763b9000001ed09fd30ba8cf419390b6407f421ab25e7028cad7103751c3c01b20abb147a633d00706115135e02f742c703ff21740bce46288)) else (if page < 6 then (if page < 5 then 0x66b00740bff2c561a02001c0cb02b6600000000000000000290900009fb27b400690da88000007a6b2c0d32272e00000d0801550577079b308e13e81d658abd1d4da000000000000a92b00c0b0e5000000000000a241ce207570687800000000c830ce803f6603e08da66240b6e12670740873e08fe6a99b9637d7506868 else 0x33b468870000cda0adb19790d8a6000081d175a003323bd2000082c277607910c8360000a93200007990b8d04a22000066705b3400000000000007f10584a98431b8a6a1c261775657800cb0dad4adc100004862c5305fd600f806266ec298c0b89100000de05768d0384201371846e24b90af548a10d6d020a7514420803994) else (if page < 7 then 0x5777cab30022c6c0d066c5005d628f22d6f4697825000aa437706216ba50a635dcd6d0d8d9b6c7e1d9a04d78256200000000ceb400002320ae2423d48b4b92e0000028b15ec067d4307089db562016711a4166867b0079c183f894a6ae31b90010e0000000000000226aaeb15d64c79229a299d1000000000000257027f0d500 else 0x1709520d7ea0280c2c01d12bb151f744528b0f598701e380f116dc06d5260f60bb6935002709159749479d9012240c4d5e0000078246748b2f8a1a3b6c032240346ba51bab05c60bb707c8912c179470c280ca68acb9010683079305219ac712ff0c5e0bdc8c920c9e20a6162b1a1807de0bc9104a204d032a4392093c03a92))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x2424da146108371011b01dbb4dc8d590090900000bc1afa09c86afe0c590a8e623e6b581b2807bd1a790cc5117d600009b20d6b4c1603760d2a0c3100000d72000001e946c84000067c6904a00000000d1c615b0c7e7b5b03b61000021402fb0b651b79128320b6000000914ca70cb8100000000192045028f3076f138b531e1 else 0x825987e243606c11a7218afb37a4b4f000004980000048f6781000d2000050f200008624000049a600008976182a68147639000043d077a695001c207c5394610000d526d84600004d307900a8e458d1c3920000b43057478aa91a6243a825cb0000dc283e1044900b80730000001f20cb1061716650ac403642cf30a3241c12) else (if page < 11 then 0x59d0000000001fe84dfa0000abf00000dca6205200002360908098112d60666400001e7098303cb0add0a3d00060c40005b2000000000d9000006d807430c0a191201f846cb5caa14d0a56c301c338247328d6e0014a5910b3610000d890d360d7529250cb44abc0b48036404c7251c03f78d10019767694a148bcc00000 else 0x6b204a1205e2aee19e804bfa00528d8572c867c731c0b9e067d100004c0029da288869e8b061000028a6585142600c184f100000362064f074e05102ccb0cb010000713071e065843ad368e0bea15ce6d68032b02e823622c5e133c4660073a026dad1b414f69f805c2021f098122c9116160b707bc14788264bcbf0c5c40000)) else (if page < 14 then (if page < 13 then 0x320bb8b430b81366ac508a19bf162481c4306550000000008a2026e12b8099e000648c3923c0000000004fd4715114d678347276bf795dd04f4189a9c2b00c22b13051b29a10267425b0d16693b00000cc8000e0422200005fa42842000000005a103d8190b1372200000000d9c2cea44ccac0503b2631cbaf1043a01112d7d0 else 0x72f66c108600d7d1c8349da046800bd0a810b7908a2b1680d2e4bb8050c22d4aa254b1065f3605b326b105d16227a3d1642193204ed040c68c0951c8dbb0afd1ad808940c65137827b32374266d00e26000000001df097b0000028c0b773015019e000002dc01f11000036108371bc8297f09167271865c640b010a0d6c8) else (if page < 15 then 0x8605690d62137480000afc00000000074a0008824da0000a1fb0e2728c428a739e75bc49641025ab7f1ac1000001341b8e02d0866c221335ba302567b350000a74131ba1f00d9b000000000963000006900af460000000000004caa6a6195690000000000003dd2d8d67ea836440f92888031b6cce09760dd4036b00000c0f1 else (if page < 16 then 0xa2bb00004940a750c46000000000000050a20490b591000020e49f114970daf000002f303428c3403272ad4092606504a3a2000000006694dae02fc25ee0d390b1910000c5d8d9423a801379c0121560ad60a69029f0d1a613f230f52ef09e207ec09cd8c30662e0a7318456a2eb0716d9d4c9b1ca525f5012d5472a5b240000 else 0xcce1d2f49e719ef094c095e0c6c448a6c3c1d018378005c74f545d703082ca095df00c120000cf103472d690000070420000d644c431913000006ed8ae413d80b6f1249672580000000001d10000c4a83a23a76bc7e50000387039b422a8152071541896b09032b82a829d86a136bfa07bb819c1aca133127e401a385c68b6f0))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0xab91000000000df0a3924a3032106dd83b7195894d585380cc215245000003011127276908b408d0b7a185664e18220439a9373095d500000882dae4346391a80000c8f459209944209a17b00000d8108ae20ef46b780000a3940900a6060000d2c03a50a4e100008babb32077b600004ef0b3f022517762000027c6 else 0x5210d5a601484dd801d062a7d86652b44fc07b296cdbc7e0a1b1a9705f605ea80070a872672a4cd07630212666108f4260c406c08ad0cea0dc704ac056711443c6eb6a7950611087d2607ac296150a9078d03670bc88a740dc4033504ca184302a70ac112502aba004c0b2a626c4d31869187a6b3118027800008126aa3201c6) else (if page < 20 then 0x69a2aa908f609820288001aa973148c244d0b190ba6065441aa400003834cdd1a0d12d3152aa0000cf70a3e41d40000000000000000019987e01000039b89360033428b7aa2153123494d9165aa69b38d8800000a5519e902d100e6069e98490cc00b0742ee2adf192c035406f218c02bcd04c155dc000000a5188b1dd346b16 else 0x328a80873720d9d030d04ec8a2990bf047d2a2808674115086d03266cf64301a77d02930a1c018c06a210be0838456300fa44e4b73772040c27100003450000092109c803ea00000402675c017600000723ad9e465f1a567bf92000000001a320da6000000009d47b01000000000000011a085c105e63366ca0323a80000336a)) else (if page < 23 then (if page < 22 then 0xd4104a701dc08418062129409fe0505451d0470071baaf242bb1ac208fb295c7309a77e0710a67a41b8401c449f669b61fc800000f41d01a00007fb714070000000000005eb17cb94731c0600000ad660000c30059f0000000006298927258566f001a0107d619422b8a10e62261b720a7f1a35036e2a07161e3c0a06f6028f0 else 0xc2080f506ef46f188509a050b076bfb427dbbf200f2736d2858076d0bc71a079d1a430845b94b26000006770a590c750b77012206500b765b9b14e420000a3b01ac8a531d1b000002e56a3c001f16181bc749540a4703c3183c17744dc546fe8a12889883830c296b0c05418d78278e042e1a4f065202810ae601ff534424762) else (if page < 24 then 0x8d1053209782d1f84f229c8718c40e01962031a2cf7448181fe297511300ae2690b027504bc698000d30c4d0a36059906a205a6208a060313616bdb09480953473841020c61b9785767643f95ca096618cab6ab0900020519b2463516ae6c240c6c608627a10c3e05f00bfd0a9a4d3502e5a339889f9b8301ef2bcf016d6c8b8 else (if page < 25 then 0x4f580000c226508532ba68500000a9f070d47b70000085e4000032b64c6881f1d2205ac0000031389ce050b0000000001cb85e2853bb79f096510b480000d860a90000007df73280a514000000006858295000002270ad76858400006c6082a9d670d9506c20d0203380cde81c7713e72971db20b3914ef8cc707fc40b308902 else 0x55a071c000006c3140813652c4a27c64d4d8000062c05ba05371d4e095112d1945db9b9793389c0077d658600bf66d425300c4907d10011248d20000cae2cdf05ec92eba8f404a80c9d207c065a11e00a7b97ca091400981ce98000084763dc112c015a00000c181d281348aaf11cfe0d2800000b5d14b801ad084d60000)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0xd8c6c6b46bd864433ac08f919371dc714d10088aac80000012c31200a7005a5652403af23a641af86db8b51178b05d38a4b01aa200000000ad64531806e0259000002c823d4119444f4278505e789eb1b9a1818000000000a3269eb06a8905c69d09c746d9e0da70195a11d473598829000056e1cfb01b80ceb00000303279b1 else 0x3210ab401c231f070c0a9b84cf1c79091247db0bc6079d0d840b7619e3061c13b04a01248b03c50d930d894ca64088664e385e04ea0bc70a4a469d1659289d096704930b5d0c4d151e87ce1cb20477017a6c814899920611a40993965e092706f383928b8317ac91f3a2540c496572825d043e45cc04d91bcd1a30001db2460) else (if page < 29 then 0xab71000000000000cdb11670ab60a1605636a1893f6010f7431069908a1b344031e08dd0b5610ea8b84057205840ac004cb119baaa5294117e20350048e07420382087c28f207a7049b727a80000000089ab745615c0000047118d20000097a026208bc23aa30000c1613be07895000003827d601d915f69d892 else 0x5e1b4a12e06b413b5a11f560000762869c01fd000001da28e429450a641234a09b01ca61d8081d03a440000238a2b5221b03bd8db60000025d1d9601f4075309ca078520000b767349806462266000082380000d0a28929000022c027492240bc7600006e2a54440630658008c8bb00a91067e80000d0224e412108bd010a40)) else (if page < 32 then (if page < 31 then 0x18d61d680000295b8526000004e07fb0c4c118651c1849f00230adf036aa08424006520115907e302020c88629900310ae6112e15c1697a1000034b265b481b152f028e80a10b1d087a20cd086f0d110000000006f780000aaa160a200006e880000219088e063046c008dc4533600008ca991b840e601400000000000000000 else 0x339a9635337600009fb81eb85270a25038947ae034e8000086a15bf835999ec44e001b00b3f16940000005828f72000001eb0000000004a09737d612b4c10000dd5032028156c7840000b5f2541033f44c01b1700ed09bd0000000000000117903a45b0078821af2a4200e404fb036c4b00038182290af90cfa8000000000000) else (if page < 33 then 0x2416cf54ce8a2c06986bd51ad7421b800007520000000000ab208f133b0bc1000000000b3500961d90695c23fa2c2d000006960296b0000480264b4a3613f8013f600006706a3510000c3114c9100008c6396d600003c473bf007106f713ab0c9e1aeb0bd0047e0cae05b700120b9f0d8281420000024b2670000000000a6f0 else (if page < 34 then 0x9ef10cf1039854003922a862340400000000000069992de021e0000038806c901ca086f15f301cf0dce82e6a0000dcf41b98b880d291085032a02d70005680b00000375800000dc04420221b000009506aa6c7678ad200000000000000000000000097708d764eb0859646ca000000000076000005928ec03a3300002c9074c4 else 0xdba6dba4be9079445b490c3a52a827a22c81000065184e04352000002fe235764518038096507ea97969a17039e00000ba062f824841c8e5a9304a926ff84c5000000000751167ca866700000e5438a00b38c224c5a1b41100000ee2d14056313e962078a48981b004001dba7f54bf7bba800000000094b064e0ad909cb09d70)))))) else (if page < 52 then (if page < 43 then (if page < 39 then (if page < 37 then (if page < 36 then 0x5f607e002d000004dc100000000000085e10d265582082060a0695999f846195e8883b0719020d000006290baa00000c1c0b84196e432f09a9b529040b15d845349b2a03da0a9290e745e503a58bbc000000000ca887de83a108f820000018485560000c49437689be62d00bf103fa8000076a28441c8629fc07d71 else 0xa3e6db10a6b8261465f7cf5800006258b1f097f73aa02b0028a090c0d154b4d1a62066c800007087633000004af0c7f0cad80000c3b10000cb00671100005ba6d2c1b440aad03891acc031d0c4b08564000063103370000003d6000083d12b3224400000491196a95c941da07a5b4486000046020000000000422d04d8d00000) else (if page < 38 then 0x1d949a502c42abd078805f413a0427c41e6242a03712898a42579600a6a065e60000c0702c109a200000c0c16d28552997778a8033b893819cd0a3a026d089b10cc02010665405941fc0ab0180e07057b31127f2b73036e0519020b26f407ee00b16cfd6a45163a005b003b04390c2818a39025179708a48d2367490b03067e0 else 0x56706ef242f9d7e8b371872116b6a059b1197440d77a00008270292b89fb4da7000016516f8086960000d95602e0a12048609e514c406fe24aca76a0a5c4000057112ba0cf86011a3570b2d878c132a87b337746a86070400000d098460863312fa113d64ae033c07dc076b2b3602bc7d40106605170d8e6a3f932201f36c907)) else (if page < 41 then (if page < 40 then 0xcd300417812072b000000f6496f09141cda18050aa381e680000b9827b1085416f70b1710000135923330826000000007b435f2025f301b067f10000c5b180d9c9e07d9824807dc9843452e02242bc31c071213052b62c000b403484d3d0dd6264017740c7b0ca27221a3021d48603a00f108c6164d4cab10f380cd24b503802 else 0x34f065c472f46820ce4000003a006b300000000055e9c370284b19f649609d903452000062705d943360a9e47701d8a24a0600000000000000000bf13a158d41246b4bca00cab2f20000dad200003708000000001fe18208000056560000d8509647000056468748841559a89490cc203ab87de185180000b538c4404fe29772) else (if page < 42 then 0x96e245d03fb634a48cc851d4c0f0a654c9f2000099f48bf0cd712b444c446209dad800006911cf161330a586c1f56e0803706719607b51803af8491683898474000090f000000000206ad910b478d0d2458846c218d46050d66138834c5a19b637d931a1b0817212b6302870c411a7242cd027014e88b946c9b8bdb680c805d2 else 0xcaf2aea147427f126ca0acf1b1361fa20000d3007366dd68525388f5bbd04cf0000032e400001b4064940440c6f600000000000095d02bc094104150b1800118dc3667549429c6909d76928032c20500263475d7b65030445ad8566678128706db502bb012b86d3024b6bf013960845497c01342daf489e097a713f006c88784))) else (if page < 47 then (if page < 45 then (if page < 44 then 0xc0e2000095e687e0d5567e1084c44de86a0800004fa6447299e196111cb0ace19fd93f4177b4899b000096d0000047a00572c6d45a4150d1ce57530800005d400fa010672d24b23307381d0045f9679a8842703011c331c9aa2000007bb233113c3035f633c8a1991790164100006ce000002a900000d09a4b3006a0b067c600 else 0xaaa0657626f100000000457213e22c20000083d40000799747b60000c824000000005e9406b173d178a6a7c6000015f06ee814c1c6f41deac1f7000000009092d00000002852dd0646b29852000000000000000000000000000087310000c8a2d96677f8a110711ac4e01940a702d2346350b610c03072f00df856c9b227) else (if page < 46 then 0xb810a0e3a16187020e1087074c14c20258467f32d1d84b003af000000000b407c0d4a8527e9929e05e217f2b6da6000050903530a5500000bd108fa03ef6da404d502d5268341272203230a4553099e5c8e1b7714784000000002f08947000004df019a0bc800fe0528095a12b64c1805a600000000008c2298200005d205f70 else 0x1d897d0ae905661a060211000000000483a00000980000000003b20000000005f14000000008181cbc000009c709020db88361400006a34000032cac260755999724e40a098ab417e802a10a73434787907000097f6a40658f03190d630065613a63d900000d04036c835c0dc56878605c260d036b28bb04c3a3560bc400680)) else (if page < 49 then (if page < 48 then 0x142473d6523a7470d9d65232b5e400005ef04cd800007540000071ea70608be1dc10b2317cc020c86cc05222294a32aa0fc69a993fc0ba306e1022030c301fb20000b9b00000485092909711000090a074f07d7021f48a9b00006ed2bb2002101956c3610000be91006204160190baf032a6c9d0c59100003c90a16424f040d0 else 0x6d159d609e4264549c401ae81c1071f8c1147a80bae156814ca015d068b0714649b0bb264d6020a45a96db80a1a0b920ad0077803c1009d1c9c828db1e36bd1169d04df1311a54304e0121c2cb297375c8706110d7c049e647284eaad7f43464a1a9daf2000006162ab1d5e636920162ce1080a0db3090719ac721601a208922) else (if page < 50 then 0x1c10d40943700000000000000001f4426b39ba0c6a07bb4d832022211903294b250c8a0545957b8c2001de035d25c72d7a054d05359a07298079b4095c502f1395066f63db014a01c360104471041e09b904270b4202a4499d0acd1c4102cb0d4901cb265904eb15d723ee6ced0c0813dc02830aca05a20601138f12f4036d4 else (if page < 51 then 0xa0815fe69c296f480000b1b000001cc05fe000006a10b670aa70dbe000000000a6302f94a8700000209825caaac027b000006e280000d4500000000026e000003d10a7c4aa8400000000c961af3084f0bd6072223fc71da9dcf02daa25a1c3500000000098ab230415e0a0010000000084d0a8189e110d18a411a71519b811d3 else 0xa604016898210cc100005031db98b3a17cb89f71d304453a129055f000006b341b026e9099c200000000009284d49706c74085718a41a9d00f203cc0461b1a006ec0099088a804b23895dd000ae01402b870139078f04976b24056e074646d50a174c15056e78e4078200000797138b00000000050e06a3600005d580a500000))))) else (if page < 61 then (if page < 56 then (if page < 54 then (if page < 53 then 0x54fb1691a5f12b38cee08a3b1b7252d08a4ac9a07946be10395396f11e50ccd165a42833b6d0000066d45da07c203468d884543617884da034a0c800000035668290b7e0380ac05861500bc057c851c4b78106e6000000000012a0e400007f56268400007ef03d31000045d973c28d66667453400fb420e085e6239279602980 else 0x37a0c040000046f89392db909f50d8a00374c83124a69c111d9897e0bec0792053e45660105bcf07430039848a59b2e05d01d97ac390c940d5d7a640a5840130bf587c96d050004079c6c7c0182094b2c1d54330000022b08f705e32834120a19710d9e6ae113a892a005c30b5f073a4a7f026f7906328a47d41d290c421d164) else (if page < 55 then 0x6a8b0000b710d58000009f8200006e60000091c42ae078e600002e112fe50000000026f0b8f878048924ccc629b22132bef08850c1f1000000005d240000ab51dd26d9000000c1261f94000054d18752afc1a9760a77bab67db8000061f0000099204cba3140ca400000550247d053e60000dca406c957d89ec00000cd669a21 else 0x717b11700000cc600000c89ba0c70000076092c293400b498a08871034248990143522f0394021a415302a8092d83e7600004538ab81cdc4a7a07fa673195ab048f0a98633f04d1adbc6dbf072a1afb00000b0a10d709400bf227bc59440bd80ca545bc06f7264036ac90530726051816b443581c4a1d92660b29c1857f8a018)) else (if page < 58 then (if page < 57 then 0x5f77dbc069a01e5400003b1109150000a664c860b75070786c508f80131005b18d00a410000017d248124d9887f20000042054801c71532982b6db2258219af023327e1100000000000059c000004ab278304c2111e052d112a02272840027a09780d2b100001e880000000052e1b5208c6000004bb03ac488f8b7e1af2009e0 else 0xa809c1a185240dd6c871808039c42bc600001e8298bb0000b97441b638d1b4604f30b08083d8cd50dc305c2638c8076700507af0be314f121d18000020b96530000058305820000058d0b0f1ca500000318098318714483285c03242163100008fd2668453f900006a401c91bf28000000002b1a139672b93f7000002a528601) else (if page < 59 then 0x5c90062030f225f07ff200001e9100001b3026e23738aa941309d87026226521695304218489298182f70000883057a801e030ea8000b3a04910db2885908969a7265a08ba619724d2d1bd5878d105f10fd6b4219c388b893a9574165d8089e9c4a098060000a19034a2ab2099c40000cf8466ea0390c3b034fa28516f32 else (if page < 60 then 0x37617a3928c6557993d0aaf15c40ac414db03b109dc076969e603df60000d12480d05710000000009510a3169b00683621f1c3a072e65e30c6410d86aa9662101077266aa6561c7067011df2a83623c605c54e90dcb877904d00d6107c79487200004ef4da7100000000d07800000000d5d503f0c864ab117a91500457b1648b else 0x48781c898134bed0d2f000009fd1101751f012c20000616104d63d21000000003bc600008550ae71a172d8a4aba160b0000000000000000028b5d2f61d20d3e00000dcb080f051611950b5c000001efa2492dbd69e32490149226231b6e0a5e00be935384170b401d8e0c531dc64cf5282fbaec1c58085947160c33089c91e28)))) else (if page < 65 then (if page < 63 then (if page < 62 then 0xb5004ba0a7010000c1e07eb1b2f000000020494263c09b32000000005fb000009c84000071d48de05d6000003f000000000019c28461931846f1cc31573884709b7172203d7183209bb899cb4cc020169fa2c4205cb671a0435700000000464800004bf0aab133ba011004016cb210400000368233b62fd4033052f800005381 else 0xac9150228f521ea97c60cea64a3a0ff000000000000036322ed400003b50dbd049a00000a85000005337692182d239a13a6008e0bfa28209d0d04c989c6461603474a0e074c6904862009e380218bbf07e09b0b157e97893636183d070b0149121201f3b8554c6224400db62c0210670837717807150d3f676517de242d0a0d0) else (if page < 64 then 0x99909ff09da42380228075b10000000062080000d5e49ac100007f40a736000048212221db6896e0d8c0a890c9f07bd0bc005d500ff147805d90a0227f1000009c207018000000001410a0f02cf238f535b060300000161000009d4020a23f371bb840a1bcf8766874bb00001cb4128600000e680000d210b5104db4b7805599 else 0x4166226483379a7062c9000000003d4035940000d5a00000caf0bce01a70c8500000cb188e62d3f139305eb050202e4252660000000000005e3b00000000140521d44ac24379cd70000041c795a98b09a23b6f281880c62014b09b1659b851485ce1d6a051b1b6003dd008e4539b0000adb05c7634b0bad0000096f700000000)) else (if page < 67 then (if page < 66 then 0x196002c0dd604bb13c60ae40ceb6b0b0c73250d02794a1312aa0c1300b206bb0c0e0c840009031b2089a35c164306406323a9fe2000000004cc160211ab8135bb4e17e6600003f1115d6977530b00000000043a201f900009d300f212c3462d10000000053c2ac81893300009f300000ccd025b10000000000006fd2b134db70 else 0x36549f408b507c813ad02d820000caa055b08f0201884d186a48b1b10b6637f9771033ca7bbb3fc1433125e0c30420503a286d029b07906b8453422400007ab00000a12133c65c11000000f160829de20a708a3057515ba43fc4a1d000004e30dab019000000a7a1209035f400007dd82330000086e046d17c401440) else (if page < 68 then 0xbd5248c00000246a34c299642ce800001ae25b2008084ba162c881f0bd40aa500000bf1404880080dad01a50169074b900001163964531502d09000032a1000009020e70d0a0000026b221822cca679b000034346b620000000000006a969bb200003300cf4526a11bb29050d24892b80000a9809db472a08364000000000000 else (if page < 69 then 0xcb70054000007e00cbe03bb07f709f72046400009dd8a70613480000acf070280098672b9617012834862c72a0b08a5025983ba0b6809ae064a05ca64be85fc739b000000ba0cd61284038287250d4f0000033e086265de28c42a8c051c920a53598aa80a0b21bc821d2064171a8c450b12165366af1684075f49f604ee05e4a else 0xd3064a7ada60cf20c4713430c80662412d7a6de0d778434085a11730b3d000002322000000000000588000000000000032700000d0c681c1000016a0792200008110dd0432e0be70db12a50100000000dcd0bf30a4617e6432c8b3406b50000069f056b70000c7b673f10000515169e03124b1c09900060139b2993632c0d8d4))))))) else (if page < 105 then (if page < 87 then (if page < 78 then (if page < 74 then (if page < 72 then (if page < 71 then 0x749179e700000000c1200000000009d09a0839210fc2000000008e7200a010c76b7200001ca200001e10c77401a0000000a67590762250b26eb702a68b2357894d2062990f16b27051603005000093f355500f7600000ad644f89ad87a006a11000089c0a6898a5b00000000d156b2d273308e602d766e404b427c1076600778 else 0x6a504cf80c960702311227802da163e23a30726178b157392e508a0a17124430463900000d12cfd416601836544000008726000048640000000000001ff449b5cac9000042103ea6a2d93382a0d49ab700001b90733b3260db185c004a6027fa1f9081e04b6018b605c400000000aec0252aaa464dca04608b21000098406730) else (if page < 73 then 0xb290003281c049328c2077b0763267b028a572233b882a30c270422031a486207d1276c246a613e0c98093d1d5f08124ca749c97a8443b89cf31a16205e337501bc220701eb2972099c74111dcb21257315abd7080c15f186a563495b405918800008686307634b45cd45311725138445b40afd0c3a13c06d400208612301540 else 0xa9f173d40000af700000000050911f958522acb100000000b3017d5089eb9547079016409735b99000009d810000753197963fe07a9bbb3144e2b52640915291b2214d344db13702b2e2000089a01e2180b844789e509a3002a06be045b074622c021f0448d05df2a5d0081065d0b150b551518257c03e9057e0c0b0d6187181)) else (if page < 76 then (if page < 75 then 0x570700008a9976c0a191ad20cb5000002ee4aa6105a268a74bc00000bd412012db5233200f8640a05150cb4623eab491c0c0573036a0c320ce5500009b60896bc3d034e20000ac900000000067800000116032e80f624aa8d34002960c1a59002d91d9148ef2136017914a00c9716ff09150b3e10e123bb8247bb9e634d0a2d0 else 0x63406de10ec0000058b00000bf4012f057f0d4807cb01043854700005e686d3b8281718089cb0f0612b116610000991a0000c709b291d2b0000039c0245a21b20000d2618ee2343202f08d90d1e033f200000fc4aa81d660cc411a3000002b904f21000022508a01a4418727708093708b10b466000000000000c69698800000) else (if page < 77 then 0x2b700000873600007481d920a310aae075a1b3213b36690887153e800000cc3000007c099b50000000007ec90000ccc003f13b486306904232b2db58c6e900003092d1c03a11000000002e200b5451a000000000c7650000024024618b940000ade0755b8972b161ae206e7000001700c2f12d62247a49501016d7904f607364 else 0xce64305a00b09dd2207200000000cd2000000ef00f98000040d1a21ba6940000b9c00000244a00000000000046b086658e70d0c465f5a388000000000000000000002cf1ada130401e3900002772000085d06614d651bd44a3d43794bc111e6016c600005b1005a6ae15b0d11c614237c0910000000038600000000000000000))) else (if page < 82 then (if page < 80 then (if page < 79 then 0xb0f7000012170000059006f6114100008404d3300000000000004822671300005b181d48b37000005ae8000091c6000050059827cf50000039d4000000004e81b8c10000d8b67bf28d50a71054d40000723b9fd09a6000000b9011620272159100006744000000006f91bb24000086396702ad4192da00000000dd560000 else 0x5c827f299d1600000000000067819f900d7a126000000ee0000000000000000077d4000060099a1900005ed60000d882094000d0253026c08db7dac0701257a008702382ccc163e6981500006ba0a370021208804f590000b760000093a22c2299340000d431d780bc015c847b20b8611001a5c0801000009db0d9820000) else (if page < 81 then 0x1ba056a100003a400000000005867452acb01dfa00002d3aa1a154d75fe46d351dc100d4c2e0cf6027c7d0060000c679a4d9d604000000001d62000038e4a5800000db32b59050a151741e0292f2dce26e50c50187379cf06f2278737ec84f700000d9449fb0542834808b0b000000002bc2000000007291a140 else 0xce1127334562270294219fa47d80075656e586943c6805d32d2023d68300ac70d8c400000666a0a16b001aa0000000001854b601af011010d4921cd635580000679000006320aa2250152db1637127b87fa1cac346c83e060ab0a070acd04dda36d005600000a56104f0dac401eac218cc81b95920f20000829800000000c7f1)) else (if page < 84 then (if page < 83 then 0x142868032e6c5200000519245220000000000008670184459580000180081e1000038c60000ce000238db38c63019228b5220008029758854e0dc1455000000b201569200000000686000005250b16062786616c6a61bf082b000000300c7a6000092205f4649b13f219f8830200000d6065b5407200c32b4d09a788eb026d1 else 0x8061d3f03a5241103f20806061a0626075661102b7a0dbc4434170fa35f008e54e24188a3222bd205f240aa0d1a07fd17af47d900bb00ac843e01f327da052286d329837dc803680d328d8f67bc6ad013a38d5b8c29033521500abf1360456676f047aeb41a1bc9087a0d12061d00000c8469e10adc0cd810640d1508c0032ea) else (if page < 85 then 0x5d108bcb0000be4100000000000000006040a3a46ef000004b815134b7c09ff949060b11b10470220000856000000000391000000000000097a54678a1e082d043b98f50d441080043d40000bcb08c9b2339d25013d00eb017700c20be805ea0bd461710220187045fa6c1d767b4a824057600005f715b69bd300000bde07891 else (if page < 86 then 0x3a12842438f05cf0bea000002f327ac010d018a0c7116079a99991f068f18e225d2675e3b2257e586b170264ce41bb1109a16250000000002ec48030bf502a2834820000af6085a05de08ed45fd051202158d32022522fc5760068e909108e32703900001ff80000000007b02124da90c581bba03ab27f0b96751154ba36 else 0x46861fb028b494f00a81a84600008b392fa27a4400002c5a0000908252c88a7900000000000078f7c110000046f205a05a46d46083e422206fb0b39078a1000067315800bb17000000007e1937741ec002949f4100002af908f58f954127c8f661b05178bdc21af0c046d560026000006a9481621c3023d017e4c5663330cb52))))) else (if page < 96 then (if page < 91 then (if page < 89 then (if page < 88 then 0x2ba4a112a178349291e0a8a06ae0032000001a8047d15991534101d990691850000020020fc09c31c45158411dd003724071431188dba32098268800086479a100007ee185f100007b910000aa074f0879d30000bb505321c9d847b000005e396d706970cae8a8340000c2f700000462d90424e02ce06a30000000009ba10000 else 0xa5163e206fb21d30bf216099c6c1d641985068907d2068090b3965e4c810273021786506b902b8010d644c709fc8000097c152abc6024d080ea0000052a200000000cc902e748fa800000000dbd4b7c1c2207647468a3a838f0020c02b60bdb47b317120d701cd9187123ac2dd41000000000000db006eb00000000004706df1) else (if page < 90 then 0x4782181486a040c01c88bfb6d0f04810d808ab90cdd7a030ac307fc07b084f68a520000091a157d02c3095910000000000006fb8745432fb3e6165704df81da1081156a6810020f81dd83582000063f17a20daa68471c2803332ba404040960745580000000000000000000097e186d773e6000028203f108d1205f03d51 else 0x6110000000021c80000b200ae8101c801340000af50ab40a9e6ca60cd600000da30a02845e000008299000035d3c92484c1784074105d6691394b78cfa014c021ea7a139bc04b701361bee001f0b8b191906131d4a0b6900000ab80000056d00606b91030a050f1320049d0d1f2c01082192986d9f062309cc08c2944c14760)) else (if page < 93 then (if page < 92 then 0x7beb2ea88934dce0d421b041220200000000020000004ed2ba00d33634c880069469c7f53460446800000000477449d18959dc16299b3fa0ca580074a72594e07f305f9b865932909750ad301416af9135c470c19805d8726a709bf6d508bd3198145eb44540aa86b3c186f87f0961706bd2b7b050b18b1240d24cc820420000 else 0x7fd09fe831f21b70d8e44ca859a9a4b1b7005c91aed098366192ce66b2d000000000cd402b729671000000004670000049540000000038d030e0a8d01a420d628e200000000000007ed07c593522af440000aea0a6f18118ce700f5244194afa5da22bb46fa86be870e28023d84405500541730200007a50d87496d473979d50) else (if page < 94 then 0x11eb6bc138c23170bd715014d484565752426dd000009af800000000a2698fb86b962d4100000000546953600520585031e2da50000053c0469000000000000013c155a20000be0100007cd9a632a1e859a0db404e49033607806ed020b3c5f0000033100ce6ccb13a90023ac78038c0d1f007793bd0d6f6c08052186b680000 else (if page < 95 then 0x1fc24838721100007d686b547a840000d6b6b94477f00908000074605cd038907771000000008c7a3849c8f000002b4023b0dcc0084856b0b1e0000021114da600006be241363c51000000009ac639a0265070a000000d72c384ac60a1009ed4b9f600009cb80000438106d1000000000000056600000000000089700000cd01 else 0x18e820b47aaa00008ef058544d70c6195551b050720495b06803c87756d4795409b18e036b8239d220ba37e9000077c1d4b0c57000000000470800000000000035b200000000c90579112f00480002322200d5705f9940804c3000004cea665256406628654602862c403c460000828009f1a6960000014400000000000041b0)))) else (if page < 100 then (if page < 98 then (if page < 97 then 0xb2718ee020a08720bce6114050e241010b08b6b15ec878c777547c3032d0543437403a74a73555c43fd952b12af0bbe00000a091000000003a42000000005c7097041cd005d40000cd72559b0e505110000060e000003278000000000000000014801187a8f200000000b3810000bb303f58000000000000ad10000000009e00 else 0xcf47000028da636000000000000089b80000000012d100000b212ca000000000000035905ce03c2016f05e5107e6a9d785a403604a20474023504c809e010db08c5138c3a6662dd1db72b8a04ea1cb30c7f7c1704e60000000006c70c728989b3650ccd2b3c0abb054c00214000010000000ce30369000006831ab304459c5c6) else (if page < 99 then 0xab5091d037c08770ccd854f9a7d96f421fa317a400001e401f6414e60000334a2060b100bab414302e183a415e60d49883750000831732a26e0956100c66a28b5b843fb196558724940494176b106190349093a0d170d0c0d98022c26bc02890a3e0a20608f47fb61f21a1c128d078b600009aa640612092000021d000000000 else 0x9d56d2e6ca993e5097c700007860c38607f0409087600700a18806d01526d1e25f4074a653221ac06540c89932011b2804d203c092f0342098d05ac7065086842d5008c026e30000cd115a290816000054b0dc418ce6db7861e956506560019224d0c7823b3085b06ab6dd111ce10000bdd0b8b6c351a82653b970003491021a)) else (if page < 102 then (if page < 101 then 0x90e02dc2000054200cc255807df05e718673bf11be7118102c1a0d0069a866460000b9d0302986404c8423313008b2b064a9897100004ad028b02bf64ad68700360000008070a52200f05b893fe1d8b0ce51b0910a604b1200004a50000059e06f687dd268283a2096107c889181318131b48239bd5013d731a08c823fc60ef8 else 0x6061a19244415c80a1594c6a6e3042e0cf9200000000a173787100000000a0e939192f5a06100b0013a741e1bfc8bc30bce108967950000000144197549065860cb627e000007d303c7058a05a400000000000009f9915c80000487400008ab0000036f000000000000000005f0100009b80d64651e05e1484a0af38703b) else (if page < 103 then 0xe1100004e700000d700c9447b150000000082e00000c8d000006ea6ae5095a30198cb90772072d950460000000005518b3b000056f09171000000000000a0d394a400000000000000002c80cf76000075640f04c12483a00000a97417f087301b315c143907000000480000346200001e905d00c752c2a8be500000312983f1 else (if page < 104 then 0x5540c9f8bd9034c401d23b766f304f32d0f2240051400ad0d830a560995058b787341c6054c95254b129bac85023c6b0dca004308b701fa84cb0c21287054c0a0976280a000079a3b2e80000000000000000414713e6af00000017611cf1ba91b9e40000cb6600004e5a5ef181702c62cab02f70450033c27a8292ba00009090 else 0x41c0cfa26a66cbf1aff06ee1000032560000000068107386bac0232450f0bbb1b0c1b0705d86000001d338c459d90000000095d177a423210000000066c096c0ca31d40206a65f125948499045701f80da9431a834b64e34bb601b2261830cf0891056217b803762b113da208359c47099e474d8ae17b5b129d1b3d1b85029c7)))))) else (if page < 123 then (if page < 114 then (if page < 109 then (if page < 107 then (if page < 106 then 0xcbb03b003e6091990af096b04deac4808c99cd005b448bdb33a44b5a9488131165b66d00d6c05e2464b0d270c6807156b611894b717a5c580000000075d0dc008691a6e0c6d061d1b1a1b2391a615c96d8f038406cd52831cd80dcf60000ca10cec048940156000000008395325a66607eb00000caf819805e89969400002e30 else 0xbe404a1067a136301581c79484e7a122cf98d2d09b1112b08e305f21044411008c80b41978144e6178023790c90196f51ab473c81f70ae00510019897dd008360d1051f490549e703264ba0468625310d408b7313470135484c083b9dc9087b0722180908c196b40d4e24e914bd4d1601936b1236312c0e87ce80d6011e90676) else (if page < 108 then 0x5f768c142e4100002a88a6d0bdc08d05b21198e6c0d03d003ad43902973016209c53a45038d43f5010f6c950309011d06f986cbb237060f000001508191059881789a1a249c051a237346964895b44f02260b11174500c806f0890d247e8bc819c594fd0099181a053581840ccf1b05156f15a51d004c006c00453280aca6470 else 0x78581110366473f000000000db82dd240000000000008cf0cd640478c7d00000090389054e92beb026f45f623510bb41aa28a9a65e8418e001542caaba1811e31bd41d02c3f14ff0b5f80c102b612e600250ac2167e1736027c01ae003114622aef04660b33028e43c2108942680a55486b6bf8bbae048525844930652b0)) else (if page < 111 then (if page < 110 then 0x77a079815399d3104de03e515e0863b89f5745783ca01c9009f08e82d9249f78b5e000001c003e46ba10980200005810da04263019e2c930a711d0e6a6807f910af8233ba068c7c1ccc407500b72bf0000004e5b95e455611e1818700000000039f40f7044b0000070700000c9b38160709000005f743fd80000b8c053ab82a8 else 0xf39db42c772a712a1d44c6092618336c3606cd81ab0000072806fd005213e36a6c6d51bc1e4d86232b4cd90000026c16c309d675c502b94145602a44d8097816594a0102390c720b57065b0000084b05af4be2053613b6095f955d753d200005040b641b310a6104cda86605330000000000000a4f18fd8000050768e93b1a0) else (if page < 112 then 0x48256412aa4474a4cd102628c7a2c4919458b300849188c0612801b800000751000047c00000000039d00a00a0b1ca9336b119a952a4d539b2c406b60a300d027f90cfc0d1d20000a3961f6063e006f050a070e80c704f719ee0d74146a040c7c914c5d164e980d8000000000ca0bf6900005d96a3319e21d650b1416449d1e8 else (if page < 113 then 0x7fe29ea00ab610b69a0076e1a6b033b2aaf06762000050c190d038c187d046e06bd066560e80000001ca000020824c90c7300000117319ab4286000037c2c8e2ae70c5513dd8dd5449c96d204a4617fa2891606001801d545bd86e190e00814169875f1a7fa096962672d0e45fc04bd280f108b0cc4000000000482000003990 else 0x9640d8421b50528144a037247c4700009240834931c2b21029a600009f0108981b66afe13970d5a4c54089ba0000570000005f813454798008d438a400005c4638a637d030c8cac15a0041801b82a5c65ad000008fc4a7891321ade1d430a6001f413d2048a000008249cd7856080000000050d299a10290d54099c0000024c6)))) else (if page < 118 then (if page < 116 then (if page < 115 then 0x74d0d6f184a903880000dc04d6f06cb80000d1d02ec2a880d2007674d9c40000245100000000bf90000000005229000062f08b60000000a20000cde000004c81a660cf217e18da823ed000000000760884336d904c61731004c668e10000db9200009df8bf892518ca82a5a1cd513cd0c9b9000043200b5647021d9067f0b620 else 0x5f6800002030ad5069f136c97d04c7b400008df201721a21000053870000a5a0ab700000d56273e445301510000026604926687010f00000a330b54034484da2a1187ea075094f503ac85938175011316f502df8424086e99ff8d370ad3185101b887c319f123a947862bc2096776ad143c072900570cad23832874164c47480) else (if page < 117 then 0xd3f4a3803a2186623fc593f9d760c90000002e2600000874000000006fe0d1b60000000000001e20000054097b602300a0788e9117710000bac20000000037647ef551620911897323f800a807266fc68cb223c42bf08860b980d180ca4415b18c789d91c4c0c74445c624d1cb38abe024c76f6209a03a22bde100005e90a404 else 0x768409c10000bfeaad7073d013509d77ba711e42903175f0cf80cbb1000000000000000085000000c8808190c8d7183411c968d12b300000547912a138a1393b73804c77955000002a601a822f20c1a000006cd211b16f10671038a752c0a54000008e0191009f272e2a537000005bb07cf00000663064c985400e3100002bd0)) else (if page < 120 then (if page < 119 then 0x4a28653442c65f1b00003d603ff8234b5ce4a10100004f6486b0b53262d896317ada1566ccf0000086509bd8048000000000d19090c2a80007e1d4400160a4c04f0a8ff000009248b0e70000078100004050c4f000000000980411f7d681a9c0cb32a0b8b4e09be434510000000000006c4100004b2000007ad0000000008725 else 0xbb964715a6821902ab0046f0af8199f069300c00a7203334a4604c58a601c9b2aa30b43181300000000098100000b2b64870d230000024307ff01c50000000009c102c500000a8b08b724d9a0cd1d4c013b96fa00000b80081360000c7c50000caa3ae800000854500002eca7fe00000cdc0c8c1204aa70321f22f8b015a8532) else (if page < 121 then 0xc816a650add1b065d7b87cd0d554cac09a803de65da834a1cdd50688879005e04d4029b78fd0db0260e1982555f6d9c07b56515229c23eb645684160ab21dc340be8602645428327306046b1c8846440d76265f09af1b47267964772a7bb0e30d3a06e818fc09d149690d334628009367d888262dd3658a17421ce6043e62f60 else (if page < 122 then 0x794074968f90507745a09070923126fb4dd097677f690054c5d0648900000000501000005350523800007bf04f406ea02e80c694bb94a6e16a1800008960ba126b880bd14f88a48000001a1034e08950a439674627a18d3464607164d9549a407da19b96b7d0bf3195701b52a7743b915510c934d5b2c6b65b60b8b0 else 0x7be96c743db11270000000003900285091131630542992820000c82033905e200000407000e200009c78d130dbb22ad051b05a530ce768493182835853191bd0c5f2a971a500cb2394988f120000db086db00000172075b0c5600000c2100000346923e090569c2810591bb0bca0d600116134c0c38000005e4b67120284c760))))) else (if page < 132 then (if page < 127 then (if page < 125 then (if page < 124 then 0x7b4486c0b3807df6d9404790000000000c4600007941000019d0da2424c20000a142000066a0c6916c800531a6430000000021013ff043709df27c7093e01ee050c0cf145ff6d6910efa1de21d10b9f4a7046582dc6660f47ef7873528fa496617c480e105b68154240a544615a7b8a13cf000003ae410505cb0d03a31691570 else 0xc2a2d0b62b8876861d60b4b1a730000000005200d5c05683d5b037b0a49b5c10000026090000000047e24eb8ba344508b7d197004c9a48902230c2410000cdb088a5a751d3c0000000000000c116aad100002c96000055652dda00007fc626b000002c9a9dc44f94cdf4caa9000000002db60000d8f488123d11000000001246) else (if page < 126 then 0x31921868000000008891344400000000c7c7000025a062f10000d85200001b74887b0000000000008047201a00000220d7308ac9170a00000ef20000000000004ec0af3242b07010000054e139d8608031c1587454a1b6a0b7b10e62a571c6976268a556535101c9000000003f368bf9b8e1b3b0cb640000a03800009aa4 else 0x8f000000f264c769f704c28b8d1c9b064260f560000a5b15ff40000d3803a140920c510d8644c12c100d964cb218a6b000000006d18644b79329ee161f4214235d07836089000001d580a208ea2000035e400000000000000000000000014600d78a7694f72d42032f12a112fcb06e1983518f86f204e3116e08c62)) else (if page < 129 then (if page < 128 then 0x87f0000031aa6e1b0000000031a6000017483d5040f0b928c910ca72a032db48103055c6375aa6f83e408229c25049001bc09ce80000dcd439e2a96045e2000047a48f325e3117b431085b230a367e9000006d662ff4158023f4d5d1c9c204b00000316100004470144489f03209b5e61ef69bc400000000000073707161 else 0xc6a4c7a0cf05da00000009c036f66a0040306fd4a5d129144e38045017e0ba2844e04b91a499795620b8a16300a4268234104dc0c151cdc6c762472247d89d2900008e12000016504d847d990000cbc17e467620af807322be60cb12a31138e0b2c600109ea1dc5037880000000063800000a8f098fb0000c5722d8000000000) else (if page < 130 then 0x4d6a0000a9490f40cf9073c0000061406af6d7118bc9000053f000000000a19800001a28000000f2ba704620bb900000000000009f67c321bc5000000000cde224500f668bc09e405c2438b427b236e80000698069e10000cfb80000000000004582c0906aa0ce843d61a6290e726f790d50ce9221baa9f7231020b000005978 else (if page < 131 then 0x8d30cb76c7420000019a43d61a02dc060000000000005bf082c05be0b5800000b2b44c31000007d070d00000702022f8b020000057d9000000009f3948960000000041f02bea588200008b62cb60000000008d43c1d15ab839044e7a7d066ec8cca00000cc71bad112d21b321d7a000000003908a9e00000aa10000000005560 else 0x41000000dd10dc200b762d9a5f26d126a2202d96c05291d268c04fe00f000fb070509148cfd049e02633c87532505791836789d94657b040429700000136269bd6b000009c60b5a0d7f65ff0d2219304000075216771bdf006368e80998096c680981c4800007610000021d60000d671a34835721a602cd200000000b8fa4610)))) else (if page < 136 then (if page < 134 then (if page < 133 then 0x48d860208671c34170e04cb85664b5410a80d2422b718cd555d05cb439733422000072c244fa000086113374c8048e533a70000033a092a0c7701021982450842a710000213188f216e20106bfe800002e0065a033e4420069841bd2c23000000798144638a552d81eb07e98c29411c08a697210c19036124016938002168b49 else 0x101000038b10000c5711a2200000000a727000000006ec14f2064106480d0b058c032f93fb000000977c7d1796824a24be03162c5c0ce90230657e800000a762636979411cb23e43a327f860030310971917800da103455324058e11a96c695018a21c0c044b0e16fe4a1b07b30d8b4cb74406001008ea0810100000018bf6b) else (if page < 135 then 0x730573408af9af56965700000000462800008460000000000000d72163d82ac07dc88621223220e600000000b4c000000000000055b2a2a44cfa2eb032e279a634120000cba0c3f03014a3d60000a1a849c828a19858dc22b481d2011ea83ec0bba200002c600000aee046b53638d04236480c569de8c9c03d70a2d228617d69 else 0x67d00000000000008017243aca8095367e7816007240ada05c7495210e90488054d64596000022d8000000000000687287420000cb0800000000852080a9bff01049a35662200000bd9122a073b055671894aac104c2cf0143e7c7d7000077305d748e10b524b1f186b4000000000000744899b03400a64400009d0b00000000)) else (if page < 138 then (if page < 137 then 0x5db2000068f00000a3404fc423a066800000b4b0a9f5d519a0a96463cc1149a12b20000000002710d7020000000034d81364000041d000004a0200000000000045e80000000000005a70000029834e80557b84647e447a890000b4506d781fe0ce8603a6a3fbd24000009c300000c19178263a2978e13e77b741282154b194d1 else 0xcfe232886f02a2f110908cb0c6d676383c8071a914702374b0a005d03a4307a0c5c1983496d2b464ca903c86000000002b503850000066626ab75a3072e422f24306284108093580000000008df033880000018200000e02d0640000d6c260c6d708a1304cd1b3e0341400007a993700a15091b1ba90c331d2e0c5a03672cad0) else (if page < 139 then 0x643600008a2923620000b0d0134049200000c2f5a7370000d998af400000381ac82600009680000085860000538553d0d64087113d3081d6904414171ea298845bc69ed071d047511349d820dc60a950b9762e907ba016b432f22e3a95a2c9e8898184e0ab105876a61199d42f819cc155f49530cab9241835842e3682c73a39 else (if page < 140 then 0x76b079c000001f5a000000000000000000000000589098640350b4f1c0d642f02127c660b7f02ef43322a637bba8664000000000000020f00000b93b2f1287a13fb48e51c5d22ea0076116212d1b1053864179610ac02cf01601272000009ff2000000000082000000000000000052443a73a4a6803417cacdf6d9f4cfb200e8 else 0x1d50a1e2b8200000000000002f6aa714780667a0ca14a7e0853000000266843639f03ae05060dd205ea27b115ca4a6d135a02e624f3145c034022e40b5301b101f1000007a92c56400008f62639016080000cb6118d00000bd21653113807db92351000002b0596800002f44a58197b153a997260000)))))))) else 0
  | 7 => if page < 31 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0xc801ce10ea22721000013511f611d3112e80940060007a212c01232071103400704083807100d3115820d9014110a20267214031b5513b20cb1290600001b4710d600000000000000001c820000000013f10cc903d2000025510000068120a421610000290403b8000023d0000022002220000214d402c918d017b017c10000 else (if page < 2 then 0xe110000153224500f90000025310f69000017f500002a1029361b040000038200000df125c02a78000007d002e003b10c811e00235014440b7229100f301e18281200000903000017001912180028e020670d50090418371d90000016a00484124119901e7b06e412f20b310a2120f02496249424b717d612a11fd007741710 else 0x1644091006960b4116461af1250000c01024000000e008f81c18182701101234207121c008b014a912140e6604781b662836103413481215000013d42a800f9107701810026412e20e7001b60a8009801e7902d524c622d0000015d013d500001e402960000002c211401084064017b41920262008e1000000000d8118f0)) else (if page < 5 then (if page < 4 then 0x1b160000139a00002b101b670eb80000000005e00d780000000001c700000000179300000f24055005d01ed11a67031014611a7712b008500000000024e41d820e6409902a661f0019e01e821fc40350000014210e000fc014100480154220540000000015b91a5024201ac5000000001e02000000002a70000000001811 else 0x7312aa80522000023c02a82260007da1f4026401420183609f02a3407f108c016c00e21182021300e101cb01386080614e60000138407e81118156b112016101fb62900132003c01620000000000000000027b11436067111e010a629c006ca00000f4100000bc200001ee60000086023042927103000001ca0000000000388) else (if page < 6 then 0xd400000000013e00000224117901331000014b6083210d02ab0223100001c801b64000000001b2113c225f10270000011a010221cf008d20000226123b00aa010a00b2203a214a80000040024300181127002d407440bb01a9429f00000104300001b571eb20000000002c01ea212101e3001921f701dd8092618710b781df0 else 0x1ff10521047000000f061231000019700c0821901b951fa5176417a52056039200002670000024d411d112d1152100b013f30801000026800000000022e506a01da004181a360e361fb40501061214311db3000005b00000079a07ea199406d412210ce000d62306015017e60e0305a819f1167906800e201831000000000000))) else (if page < 11 then (if page < 9 then (if page < 8 then 0xdd0034122c42af02a4004e0018010c61fa61b7003a8078810570dd123901ea0134014f41ec014810a302250218127511b001c001c1005f00ff60d6905b420e018b00a4102c41a060ae00fa008722ae0240110550e3407d8174218212410269200001f84000000001d92164001b711a1131826d000001b1402b0045010741222 else 0x8c420000890089818671dd0000015a000002824000008c52820000010421df9000022c00000131208b2291828e106720000036100000a5707981d2411810c3629d112400da40c1006f8052028b112e102d11200023426b603510b800b1214d6000006500f68010013501f950b900000144106e2208824f008a8) else (if page < 10 then 0xd60145002a40d701be0283407ca0fd1283002a52711000000001a82000000862761062a231027e0023028c10a660000096624a00db0144608b412b81054000008240a710272078a2036117000f200a6158026101fc622a01a801fc0262601e005700d2000001ef6072200001bc300001e1121201e1003980e86000008740000 else 0x14c02970281020290ad71854270112c8126811b71f8108362661075a1df20df41ca810b00f71105617821d340000089200000e561bf010c000001c9000000000000000000000014606c000000bea1a110c400c0a1ee400000000021000000ca11c20000004a0027420901de91b9602c810b60cf1000020651bd000000eba0000)) else (if page < 13 then (if page < 12 then 0x2471000010321a01047214b102b2000004a80e3100000b1815201012107209b029e000000602052b02f00e46063005002321000019f001a1142413a200001b971950190400001f300d5117f71ab0000000000b60000013d005901b602a90114427f610d401701e0824310ed40360082018441d3303e008540e54226003711d00 else 0x3c208481c08017128f0000008e50000000001a0000000760fb017c601d00ad007d2227100001ab216810ff12b302b40203417721e2012c2057102a01f901b1020a61df111980e4423a1295612120620186621d0072519a00370000000001d40054b0cb00000149007c828800df31da22280045805a00e900000000024211501) else (if page < 14 then 0x2a60000013e2186107e203811d14000009d60000263422e1237004821de10ed600001aa20d80066200000d002890013603301f8608940e4116081b250f510f4707d602b10b280ae70d68184024c422301e64246007f410d12636149907580912269026a006f205da0ec0224022e71f80106008f307001b941c30052906c61300 else 0xf00da00b50019117d40252000008c20000157615e017451814000013602540000000001b8129462a2607162a3610621a7002c301e11df807f02a980000000004d014b4000020c114140000000016b023201fd511f40ad60000079112251e6600002720105200000f4500000862000011680da21fa406f0000022510ca61b27)))) else (if page < 23 then (if page < 19 then (if page < 17 then (if page < 16 then 0x244113d70936210003001374110412021da824e602d022d2029026672656241115c900401af720942151277002040391095024d007a60000000003621fd610e600001ef408d11e1229300a722aa003c812b200281b800000189023401f500b3007e61d981d8117b625f02291174708e41af510a4000010711a90120404aa else 0x17d011300de00000000003721ad0026007a71fb01d501ae610e00a10178423c100001d6002a2183000002806207726650bf81d301db01a9214e012d01ba0125118cb025018ab180604342a240b080de2205014f613b02a72173212610ae61e290d30119029540ac824b5188201720c340b400000000026460190189211f017f1) else (if page < 18 then 0x1be407b0198017e0108624a807060e600c2215590790036802000000000011910000000000000e761fe1000006a229b0127625302a5400000000244000000a9015901f292aa2064217c000000000011216e00aa6000000960b622040082829f10258295023e00a1110f4000007b41b34024a24e0270011c01fa70f7008141fa1 else 0x13e7155b074625a014510c841e900e741f910f000842127710c40af024a2000018e21b900d10162616242601268818341d040ec2000012a807242944080410640a7024d605f217541b4100200be81f971ad51794299027f00810000021b119101c471e2209090626000027c008aa0000082a23f009a0117213e510700cd81786)) else (if page < 21 then (if page < 20 then 0x22a10bfa14d029a0129000000de700001ae4214027e4126012500b6107410000000019b80ce100000504000008000a960a00000000000f400ea0227013d600000c5810911f760de506d6111204521d70000014801096000029400fe006521dd20000037803281404280020611b3611d01046000011002a641bf418c906611835 else 0x17a71001231426b40531163000000766000006e007c005801d72108109f21073024027f41ee0106126541851042008640f2107f80ee025d0149825b01e212710054a028012242a301242175014302934137600601d881825166912f022b10dc009020c7813e410b4252002920000125817e4000000000000171912801aa00bda) else (if page < 22 then 0x7fa17520c8605601ac112e000000ca0124514b0000005020ac00e260e301dc00000285006911aa604900cd902881ca91fd4000018e00dd30b00000000000000149213e615f80dd620752a0025711af00db200001500068a144023300000000008a2091519061511247013210e14078026a821e021f012111f640511 else 0x23161df31db925902580080a00182860088013082510072012a00fc61b201a10082110102400292502840000292125c10ff00dd41d2006321ac010400e24103614710b701ed4081a1041031800000c90278017a009c006101e281dd114161ec62ab60000280400001b6121a01dc201d10000000003f00a400ee200000b320ca4))) else (if page < 27 then (if page < 25 then (if page < 24 then 0x1de008180000000013d2119928700da60000025402e813f00000000000001b5114260000000007381574115807301235117803210f800a3100501bb4117126300914108010f000001650097014e40282134917622a461c5005300a671ad218b202940f2018d222f423b100301ad707500fb611500c9124810de60fa60a541160 else 0x2a9216900b681e5608e027e60b522981109002d2211008f00dc61aa427d01124208010500fd000221fd126d11a30185613c009000a500bc017800b3808341ba4174000001fd703b013020e1613010e80000006d028a01e5404b023a000000000000000001de3067010200462176614e118601a601d100a812682000025b1) else (if page < 26 then 0xdb42624000008080000000000001ef00de408302a200246113407d12840082200000dc4199602b5123026c0026200001ae0140126e007f21f7400001c6020a000000e5007b12ab40000248017601180069a000013f2000000001bb008c10df0000000000000000000000dd200000000249000002a440c701fa000000c681721 else 0x74010761e42221003581f6615f010631362000011e10e40273114021db1196008260df21b8516f004a216d0000010e412d800000e9210a1000000000000000026a21b450fe105c409110b010000000022f00b11000005510000033700000b4200000af118641eb019c00d410000000004f0122023800a561865000000001a57)) else (if page < 29 then (if page < 28 then 0x8d52644076008f405c00ef0000008f217910000000013101d690c1202b402200000153012b100000cc808f9139800001f1028b0000003a02a560690000014f00cf011b61e92128114c10000000012912a88000000001b3019d01b870000000001f0143404ca00001406000027900320217122b0188007d4000813a01f600e01 else 0xd7900000000124429d01ec4088200001b74039018461ac2229012d20f501fc103b21d801400065117a2001210b1181609e628c028262678090807e10714203020d0256026b01b402a0107e41ed008840dc2087029121ed60f8110002b001cc720b00b5802a12300172028d01540209617f008d40bd80e0224c003800f101a20) else (if page < 30 then 0x81617c4000018f21618146007c12010016022f603f61d120c4209d0177007e005100c2028a12ad01b91033620d106600e610b4807621e8027a020b1000000000000000000001d781709000000000ba022d8000008122a500000000005610e06185000001bc9208201c627411c880c500b21000023601cd0083a073225e00b10 else 0x80208e22b500d9209d40bb224b119302b2007f626981b0602f618a913f41ca226110f2604401b7611c112c10f3101202ac006a11c7011921e2318760b20147026f01dc8104412f8068619491569109422c61a400ab008d01b6518040e041b50265006b007a02818123802241bd417301330))))) else 0
  | 8 => if page < 2 then (if page < 1 then 0x1a00a7001400c100d10077002000990052008500a100280071005800120084001000d00076004000a40093009000a000c001010075000000e00016008101000000006600f00000000200460018003400860000008000e1007000000110008700500000006400a600b000a5000800300000002200360060009800b100440091 else 0x7400000000000000000092) else 0
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
  let slot := field targets k 16 ((h / b + shift) % slotCount k)
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

def checked (k i : Nat) := decide (pool k i).Nodup && Vector.packedClosed target negative goalColumns pool counts lookup steps k i
theorem root : pool 9 0 = raw := by decide +kernel

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
theorem chunk4x176 : span (checked 4) 10 176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 186 0 = true :=
  (@span_join (checked 4) 96 0 90 (@span_join (checked 4) 48 0 48 (@span_join (checked 4) 16 0 32 chunk4x0 (@span_join (checked 4) 16 16 16 chunk4x16 chunk4x32)) (@span_join (checked 4) 16 48 32 chunk4x48 (@span_join (checked 4) 16 64 16 chunk4x64 chunk4x80))) (@span_join (checked 4) 48 96 42 (@span_join (checked 4) 16 96 32 chunk4x96 (@span_join (checked 4) 16 112 16 chunk4x112 chunk4x128)) (@span_join (checked 4) 16 144 26 chunk4x144 (@span_join (checked 4) 16 160 10 chunk4x160 chunk4x176))))

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
theorem chunk5x704 : span (checked 5) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x720 : span (checked 5) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x736 : span (checked 5) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x752 : span (checked 5) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x768 : span (checked 5) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x784 : span (checked 5) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x800 : span (checked 5) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x816 : span (checked 5) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x832 : span (checked 5) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x848 : span (checked 5) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x864 : span (checked 5) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x880 : span (checked 5) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x896 : span (checked 5) 16 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x912 : span (checked 5) 16 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x928 : span (checked 5) 16 928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x944 : span (checked 5) 16 944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x960 : span (checked 5) 16 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x976 : span (checked 5) 16 976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x992 : span (checked 5) 16 992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1008 : span (checked 5) 16 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1024 : span (checked 5) 16 1024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1040 : span (checked 5) 16 1040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1056 : span (checked 5) 16 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1072 : span (checked 5) 16 1072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1088 : span (checked 5) 16 1088 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1104 : span (checked 5) 16 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1120 : span (checked 5) 16 1120 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1136 : span (checked 5) 16 1136 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1152 : span (checked 5) 16 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1168 : span (checked 5) 16 1168 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1184 : span (checked 5) 16 1184 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1200 : span (checked 5) 16 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1216 : span (checked 5) 16 1216 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1232 : span (checked 5) 16 1232 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1248 : span (checked 5) 16 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1264 : span (checked 5) 16 1264 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1280 : span (checked 5) 16 1280 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1296 : span (checked 5) 16 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1312 : span (checked 5) 16 1312 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1328 : span (checked 5) 16 1328 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1344 : span (checked 5) 16 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1360 : span (checked 5) 16 1360 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1376 : span (checked 5) 16 1376 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1392 : span (checked 5) 16 1392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1408 : span (checked 5) 16 1408 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1424 : span (checked 5) 16 1424 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1440 : span (checked 5) 16 1440 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1456 : span (checked 5) 16 1456 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1472 : span (checked 5) 16 1472 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1488 : span (checked 5) 16 1488 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1504 : span (checked 5) 16 1504 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1520 : span (checked 5) 16 1520 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1536 : span (checked 5) 16 1536 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1552 : span (checked 5) 16 1552 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1568 : span (checked 5) 16 1568 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1584 : span (checked 5) 16 1584 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1600 : span (checked 5) 16 1600 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1616 : span (checked 5) 16 1616 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1632 : span (checked 5) 16 1632 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1648 : span (checked 5) 16 1648 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1664 : span (checked 5) 16 1664 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1680 : span (checked 5) 16 1680 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1696 : span (checked 5) 16 1696 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1712 : span (checked 5) 16 1712 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1728 : span (checked 5) 16 1728 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1744 : span (checked 5) 16 1744 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1760 : span (checked 5) 16 1760 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1776 : span (checked 5) 16 1776 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1792 : span (checked 5) 16 1792 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1808 : span (checked 5) 16 1808 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1824 : span (checked 5) 16 1824 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1840 : span (checked 5) 16 1840 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1856 : span (checked 5) 16 1856 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1872 : span (checked 5) 16 1872 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1888 : span (checked 5) 16 1888 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1904 : span (checked 5) 16 1904 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1920 : span (checked 5) 16 1920 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1936 : span (checked 5) 16 1936 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1952 : span (checked 5) 16 1952 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1968 : span (checked 5) 16 1968 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1984 : span (checked 5) 16 1984 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2000 : span (checked 5) 16 2000 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2016 : span (checked 5) 16 2016 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2032 : span (checked 5) 16 2032 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2048 : span (checked 5) 16 2048 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2064 : span (checked 5) 16 2064 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2080 : span (checked 5) 16 2080 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2096 : span (checked 5) 16 2096 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2112 : span (checked 5) 16 2112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2128 : span (checked 5) 16 2128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2144 : span (checked 5) 16 2144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2160 : span (checked 5) 16 2160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2176 : span (checked 5) 15 2176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 2191 0 = true :=
  (@span_join (checked 5) 1088 0 1103 (@span_join (checked 5) 544 0 544 (@span_join (checked 5) 272 0 272 (@span_join (checked 5) 128 0 144 (@span_join (checked 5) 64 0 64 (@span_join (checked 5) 32 0 32 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 16 chunk5x32 chunk5x48)) (@span_join (checked 5) 32 64 32 (@span_join (checked 5) 16 64 16 chunk5x64 chunk5x80) (@span_join (checked 5) 16 96 16 chunk5x96 chunk5x112))) (@span_join (checked 5) 64 128 80 (@span_join (checked 5) 32 128 32 (@span_join (checked 5) 16 128 16 chunk5x128 chunk5x144) (@span_join (checked 5) 16 160 16 chunk5x160 chunk5x176)) (@span_join (checked 5) 32 192 48 (@span_join (checked 5) 16 192 16 chunk5x192 chunk5x208) (@span_join (checked 5) 16 224 32 chunk5x224 (@span_join (checked 5) 16 240 16 chunk5x240 chunk5x256))))) (@span_join (checked 5) 128 272 144 (@span_join (checked 5) 64 272 64 (@span_join (checked 5) 32 272 32 (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288) (@span_join (checked 5) 16 304 16 chunk5x304 chunk5x320)) (@span_join (checked 5) 32 336 32 (@span_join (checked 5) 16 336 16 chunk5x336 chunk5x352) (@span_join (checked 5) 16 368 16 chunk5x368 chunk5x384))) (@span_join (checked 5) 64 400 80 (@span_join (checked 5) 32 400 32 (@span_join (checked 5) 16 400 16 chunk5x400 chunk5x416) (@span_join (checked 5) 16 432 16 chunk5x432 chunk5x448)) (@span_join (checked 5) 32 464 48 (@span_join (checked 5) 16 464 16 chunk5x464 chunk5x480) (@span_join (checked 5) 16 496 32 chunk5x496 (@span_join (checked 5) 16 512 16 chunk5x512 chunk5x528)))))) (@span_join (checked 5) 272 544 272 (@span_join (checked 5) 128 544 144 (@span_join (checked 5) 64 544 64 (@span_join (checked 5) 32 544 32 (@span_join (checked 5) 16 544 16 chunk5x544 chunk5x560) (@span_join (checked 5) 16 576 16 chunk5x576 chunk5x592)) (@span_join (checked 5) 32 608 32 (@span_join (checked 5) 16 608 16 chunk5x608 chunk5x624) (@span_join (checked 5) 16 640 16 chunk5x640 chunk5x656))) (@span_join (checked 5) 64 672 80 (@span_join (checked 5) 32 672 32 (@span_join (checked 5) 16 672 16 chunk5x672 chunk5x688) (@span_join (checked 5) 16 704 16 chunk5x704 chunk5x720)) (@span_join (checked 5) 32 736 48 (@span_join (checked 5) 16 736 16 chunk5x736 chunk5x752) (@span_join (checked 5) 16 768 32 chunk5x768 (@span_join (checked 5) 16 784 16 chunk5x784 chunk5x800))))) (@span_join (checked 5) 128 816 144 (@span_join (checked 5) 64 816 64 (@span_join (checked 5) 32 816 32 (@span_join (checked 5) 16 816 16 chunk5x816 chunk5x832) (@span_join (checked 5) 16 848 16 chunk5x848 chunk5x864)) (@span_join (checked 5) 32 880 32 (@span_join (checked 5) 16 880 16 chunk5x880 chunk5x896) (@span_join (checked 5) 16 912 16 chunk5x912 chunk5x928))) (@span_join (checked 5) 64 944 80 (@span_join (checked 5) 32 944 32 (@span_join (checked 5) 16 944 16 chunk5x944 chunk5x960) (@span_join (checked 5) 16 976 16 chunk5x976 chunk5x992)) (@span_join (checked 5) 32 1008 48 (@span_join (checked 5) 16 1008 16 chunk5x1008 chunk5x1024) (@span_join (checked 5) 16 1040 32 chunk5x1040 (@span_join (checked 5) 16 1056 16 chunk5x1056 chunk5x1072))))))) (@span_join (checked 5) 544 1088 559 (@span_join (checked 5) 272 1088 272 (@span_join (checked 5) 128 1088 144 (@span_join (checked 5) 64 1088 64 (@span_join (checked 5) 32 1088 32 (@span_join (checked 5) 16 1088 16 chunk5x1088 chunk5x1104) (@span_join (checked 5) 16 1120 16 chunk5x1120 chunk5x1136)) (@span_join (checked 5) 32 1152 32 (@span_join (checked 5) 16 1152 16 chunk5x1152 chunk5x1168) (@span_join (checked 5) 16 1184 16 chunk5x1184 chunk5x1200))) (@span_join (checked 5) 64 1216 80 (@span_join (checked 5) 32 1216 32 (@span_join (checked 5) 16 1216 16 chunk5x1216 chunk5x1232) (@span_join (checked 5) 16 1248 16 chunk5x1248 chunk5x1264)) (@span_join (checked 5) 32 1280 48 (@span_join (checked 5) 16 1280 16 chunk5x1280 chunk5x1296) (@span_join (checked 5) 16 1312 32 chunk5x1312 (@span_join (checked 5) 16 1328 16 chunk5x1328 chunk5x1344))))) (@span_join (checked 5) 128 1360 144 (@span_join (checked 5) 64 1360 64 (@span_join (checked 5) 32 1360 32 (@span_join (checked 5) 16 1360 16 chunk5x1360 chunk5x1376) (@span_join (checked 5) 16 1392 16 chunk5x1392 chunk5x1408)) (@span_join (checked 5) 32 1424 32 (@span_join (checked 5) 16 1424 16 chunk5x1424 chunk5x1440) (@span_join (checked 5) 16 1456 16 chunk5x1456 chunk5x1472))) (@span_join (checked 5) 64 1488 80 (@span_join (checked 5) 32 1488 32 (@span_join (checked 5) 16 1488 16 chunk5x1488 chunk5x1504) (@span_join (checked 5) 16 1520 16 chunk5x1520 chunk5x1536)) (@span_join (checked 5) 32 1552 48 (@span_join (checked 5) 16 1552 16 chunk5x1552 chunk5x1568) (@span_join (checked 5) 16 1584 32 chunk5x1584 (@span_join (checked 5) 16 1600 16 chunk5x1600 chunk5x1616)))))) (@span_join (checked 5) 272 1632 287 (@span_join (checked 5) 128 1632 144 (@span_join (checked 5) 64 1632 64 (@span_join (checked 5) 32 1632 32 (@span_join (checked 5) 16 1632 16 chunk5x1632 chunk5x1648) (@span_join (checked 5) 16 1664 16 chunk5x1664 chunk5x1680)) (@span_join (checked 5) 32 1696 32 (@span_join (checked 5) 16 1696 16 chunk5x1696 chunk5x1712) (@span_join (checked 5) 16 1728 16 chunk5x1728 chunk5x1744))) (@span_join (checked 5) 64 1760 80 (@span_join (checked 5) 32 1760 32 (@span_join (checked 5) 16 1760 16 chunk5x1760 chunk5x1776) (@span_join (checked 5) 16 1792 16 chunk5x1792 chunk5x1808)) (@span_join (checked 5) 32 1824 48 (@span_join (checked 5) 16 1824 16 chunk5x1824 chunk5x1840) (@span_join (checked 5) 16 1856 32 chunk5x1856 (@span_join (checked 5) 16 1872 16 chunk5x1872 chunk5x1888))))) (@span_join (checked 5) 144 1904 143 (@span_join (checked 5) 64 1904 80 (@span_join (checked 5) 32 1904 32 (@span_join (checked 5) 16 1904 16 chunk5x1904 chunk5x1920) (@span_join (checked 5) 16 1936 16 chunk5x1936 chunk5x1952)) (@span_join (checked 5) 32 1968 48 (@span_join (checked 5) 16 1968 16 chunk5x1968 chunk5x1984) (@span_join (checked 5) 16 2000 32 chunk5x2000 (@span_join (checked 5) 16 2016 16 chunk5x2016 chunk5x2032)))) (@span_join (checked 5) 64 2048 79 (@span_join (checked 5) 32 2048 32 (@span_join (checked 5) 16 2048 16 chunk5x2048 chunk5x2064) (@span_join (checked 5) 16 2080 16 chunk5x2080 chunk5x2096)) (@span_join (checked 5) 32 2112 47 (@span_join (checked 5) 16 2112 16 chunk5x2112 chunk5x2128) (@span_join (checked 5) 16 2144 31 chunk5x2144 (@span_join (checked 5) 16 2160 15 chunk5x2160 chunk5x2176))))))))

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
theorem chunk6x896 : span (checked 6) 16 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x912 : span (checked 6) 16 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x928 : span (checked 6) 16 928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x944 : span (checked 6) 16 944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x960 : span (checked 6) 16 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x976 : span (checked 6) 16 976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x992 : span (checked 6) 16 992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1008 : span (checked 6) 16 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1024 : span (checked 6) 16 1024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1040 : span (checked 6) 16 1040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1056 : span (checked 6) 16 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1072 : span (checked 6) 16 1072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1088 : span (checked 6) 16 1088 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1104 : span (checked 6) 16 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1120 : span (checked 6) 16 1120 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1136 : span (checked 6) 16 1136 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1152 : span (checked 6) 16 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1168 : span (checked 6) 16 1168 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1184 : span (checked 6) 16 1184 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1200 : span (checked 6) 16 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1216 : span (checked 6) 16 1216 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1232 : span (checked 6) 16 1232 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1248 : span (checked 6) 16 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1264 : span (checked 6) 16 1264 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1280 : span (checked 6) 16 1280 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1296 : span (checked 6) 16 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1312 : span (checked 6) 16 1312 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1328 : span (checked 6) 16 1328 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1344 : span (checked 6) 16 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1360 : span (checked 6) 16 1360 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1376 : span (checked 6) 16 1376 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1392 : span (checked 6) 16 1392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1408 : span (checked 6) 16 1408 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1424 : span (checked 6) 16 1424 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1440 : span (checked 6) 16 1440 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1456 : span (checked 6) 16 1456 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1472 : span (checked 6) 16 1472 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1488 : span (checked 6) 16 1488 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1504 : span (checked 6) 16 1504 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1520 : span (checked 6) 16 1520 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1536 : span (checked 6) 16 1536 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1552 : span (checked 6) 16 1552 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1568 : span (checked 6) 16 1568 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1584 : span (checked 6) 16 1584 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1600 : span (checked 6) 16 1600 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1616 : span (checked 6) 16 1616 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1632 : span (checked 6) 16 1632 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1648 : span (checked 6) 16 1648 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1664 : span (checked 6) 16 1664 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1680 : span (checked 6) 16 1680 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1696 : span (checked 6) 16 1696 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1712 : span (checked 6) 16 1712 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1728 : span (checked 6) 16 1728 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1744 : span (checked 6) 16 1744 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1760 : span (checked 6) 16 1760 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1776 : span (checked 6) 16 1776 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1792 : span (checked 6) 16 1792 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1808 : span (checked 6) 16 1808 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1824 : span (checked 6) 16 1824 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1840 : span (checked 6) 16 1840 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1856 : span (checked 6) 16 1856 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1872 : span (checked 6) 16 1872 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1888 : span (checked 6) 16 1888 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1904 : span (checked 6) 16 1904 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1920 : span (checked 6) 16 1920 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1936 : span (checked 6) 16 1936 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1952 : span (checked 6) 16 1952 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1968 : span (checked 6) 16 1968 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x1984 : span (checked 6) 16 1984 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2000 : span (checked 6) 16 2000 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2016 : span (checked 6) 16 2016 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2032 : span (checked 6) 16 2032 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2048 : span (checked 6) 16 2048 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2064 : span (checked 6) 16 2064 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2080 : span (checked 6) 16 2080 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2096 : span (checked 6) 16 2096 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2112 : span (checked 6) 16 2112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2128 : span (checked 6) 16 2128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2144 : span (checked 6) 16 2144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2160 : span (checked 6) 16 2160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2176 : span (checked 6) 16 2176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2192 : span (checked 6) 16 2192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2208 : span (checked 6) 16 2208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2224 : span (checked 6) 16 2224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2240 : span (checked 6) 16 2240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2256 : span (checked 6) 16 2256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2272 : span (checked 6) 16 2272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2288 : span (checked 6) 16 2288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2304 : span (checked 6) 16 2304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2320 : span (checked 6) 16 2320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2336 : span (checked 6) 16 2336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2352 : span (checked 6) 16 2352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2368 : span (checked 6) 16 2368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2384 : span (checked 6) 16 2384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2400 : span (checked 6) 16 2400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2416 : span (checked 6) 16 2416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2432 : span (checked 6) 16 2432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2448 : span (checked 6) 16 2448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2464 : span (checked 6) 16 2464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2480 : span (checked 6) 16 2480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2496 : span (checked 6) 16 2496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2512 : span (checked 6) 16 2512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2528 : span (checked 6) 16 2528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2544 : span (checked 6) 16 2544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2560 : span (checked 6) 16 2560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2576 : span (checked 6) 16 2576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2592 : span (checked 6) 16 2592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2608 : span (checked 6) 16 2608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2624 : span (checked 6) 16 2624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2640 : span (checked 6) 16 2640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2656 : span (checked 6) 16 2656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2672 : span (checked 6) 16 2672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2688 : span (checked 6) 16 2688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2704 : span (checked 6) 16 2704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2720 : span (checked 6) 16 2720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2736 : span (checked 6) 16 2736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2752 : span (checked 6) 16 2752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2768 : span (checked 6) 16 2768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2784 : span (checked 6) 16 2784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2800 : span (checked 6) 16 2800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2816 : span (checked 6) 16 2816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2832 : span (checked 6) 16 2832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2848 : span (checked 6) 16 2848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2864 : span (checked 6) 16 2864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2880 : span (checked 6) 16 2880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2896 : span (checked 6) 16 2896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2912 : span (checked 6) 16 2912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2928 : span (checked 6) 16 2928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2944 : span (checked 6) 16 2944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2960 : span (checked 6) 16 2960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2976 : span (checked 6) 16 2976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x2992 : span (checked 6) 16 2992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3008 : span (checked 6) 16 3008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3024 : span (checked 6) 16 3024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3040 : span (checked 6) 16 3040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3056 : span (checked 6) 16 3056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3072 : span (checked 6) 16 3072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3088 : span (checked 6) 16 3088 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3104 : span (checked 6) 16 3104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3120 : span (checked 6) 16 3120 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3136 : span (checked 6) 16 3136 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3152 : span (checked 6) 16 3152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3168 : span (checked 6) 16 3168 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3184 : span (checked 6) 16 3184 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3200 : span (checked 6) 16 3200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3216 : span (checked 6) 16 3216 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3232 : span (checked 6) 16 3232 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3248 : span (checked 6) 16 3248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3264 : span (checked 6) 16 3264 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3280 : span (checked 6) 16 3280 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3296 : span (checked 6) 16 3296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3312 : span (checked 6) 16 3312 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3328 : span (checked 6) 16 3328 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3344 : span (checked 6) 16 3344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3360 : span (checked 6) 16 3360 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3376 : span (checked 6) 16 3376 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3392 : span (checked 6) 16 3392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3408 : span (checked 6) 16 3408 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3424 : span (checked 6) 16 3424 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3440 : span (checked 6) 16 3440 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3456 : span (checked 6) 16 3456 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3472 : span (checked 6) 16 3472 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3488 : span (checked 6) 16 3488 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3504 : span (checked 6) 16 3504 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3520 : span (checked 6) 16 3520 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x3536 : span (checked 6) 7 3536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 3543 0 = true :=
  (@span_join (checked 6) 1776 0 1767 (@span_join (checked 6) 880 0 896 (@span_join (checked 6) 432 0 448 (@span_join (checked 6) 208 0 224 (@span_join (checked 6) 96 0 112 (@span_join (checked 6) 48 0 48 (@span_join (checked 6) 16 0 32 chunk6x0 (@span_join (checked 6) 16 16 16 chunk6x16 chunk6x32)) (@span_join (checked 6) 16 48 32 chunk6x48 (@span_join (checked 6) 16 64 16 chunk6x64 chunk6x80))) (@span_join (checked 6) 48 96 64 (@span_join (checked 6) 16 96 32 chunk6x96 (@span_join (checked 6) 16 112 16 chunk6x112 chunk6x128)) (@span_join (checked 6) 32 144 32 (@span_join (checked 6) 16 144 16 chunk6x144 chunk6x160) (@span_join (checked 6) 16 176 16 chunk6x176 chunk6x192)))) (@span_join (checked 6) 112 208 112 (@span_join (checked 6) 48 208 64 (@span_join (checked 6) 16 208 32 chunk6x208 (@span_join (checked 6) 16 224 16 chunk6x224 chunk6x240)) (@span_join (checked 6) 32 256 32 (@span_join (checked 6) 16 256 16 chunk6x256 chunk6x272) (@span_join (checked 6) 16 288 16 chunk6x288 chunk6x304))) (@span_join (checked 6) 48 320 64 (@span_join (checked 6) 16 320 32 chunk6x320 (@span_join (checked 6) 16 336 16 chunk6x336 chunk6x352)) (@span_join (checked 6) 32 368 32 (@span_join (checked 6) 16 368 16 chunk6x368 chunk6x384) (@span_join (checked 6) 16 400 16 chunk6x400 chunk6x416))))) (@span_join (checked 6) 224 432 224 (@span_join (checked 6) 112 432 112 (@span_join (checked 6) 48 432 64 (@span_join (checked 6) 16 432 32 chunk6x432 (@span_join (checked 6) 16 448 16 chunk6x448 chunk6x464)) (@span_join (checked 6) 32 480 32 (@span_join (checked 6) 16 480 16 chunk6x480 chunk6x496) (@span_join (checked 6) 16 512 16 chunk6x512 chunk6x528))) (@span_join (checked 6) 48 544 64 (@span_join (checked 6) 16 544 32 chunk6x544 (@span_join (checked 6) 16 560 16 chunk6x560 chunk6x576)) (@span_join (checked 6) 32 592 32 (@span_join (checked 6) 16 592 16 chunk6x592 chunk6x608) (@span_join (checked 6) 16 624 16 chunk6x624 chunk6x640)))) (@span_join (checked 6) 112 656 112 (@span_join (checked 6) 48 656 64 (@span_join (checked 6) 16 656 32 chunk6x656 (@span_join (checked 6) 16 672 16 chunk6x672 chunk6x688)) (@span_join (checked 6) 32 704 32 (@span_join (checked 6) 16 704 16 chunk6x704 chunk6x720) (@span_join (checked 6) 16 736 16 chunk6x736 chunk6x752))) (@span_join (checked 6) 48 768 64 (@span_join (checked 6) 16 768 32 chunk6x768 (@span_join (checked 6) 16 784 16 chunk6x784 chunk6x800)) (@span_join (checked 6) 32 816 32 (@span_join (checked 6) 16 816 16 chunk6x816 chunk6x832) (@span_join (checked 6) 16 848 16 chunk6x848 chunk6x864)))))) (@span_join (checked 6) 448 880 448 (@span_join (checked 6) 224 880 224 (@span_join (checked 6) 112 880 112 (@span_join (checked 6) 48 880 64 (@span_join (checked 6) 16 880 32 chunk6x880 (@span_join (checked 6) 16 896 16 chunk6x896 chunk6x912)) (@span_join (checked 6) 32 928 32 (@span_join (checked 6) 16 928 16 chunk6x928 chunk6x944) (@span_join (checked 6) 16 960 16 chunk6x960 chunk6x976))) (@span_join (checked 6) 48 992 64 (@span_join (checked 6) 16 992 32 chunk6x992 (@span_join (checked 6) 16 1008 16 chunk6x1008 chunk6x1024)) (@span_join (checked 6) 32 1040 32 (@span_join (checked 6) 16 1040 16 chunk6x1040 chunk6x1056) (@span_join (checked 6) 16 1072 16 chunk6x1072 chunk6x1088)))) (@span_join (checked 6) 112 1104 112 (@span_join (checked 6) 48 1104 64 (@span_join (checked 6) 16 1104 32 chunk6x1104 (@span_join (checked 6) 16 1120 16 chunk6x1120 chunk6x1136)) (@span_join (checked 6) 32 1152 32 (@span_join (checked 6) 16 1152 16 chunk6x1152 chunk6x1168) (@span_join (checked 6) 16 1184 16 chunk6x1184 chunk6x1200))) (@span_join (checked 6) 48 1216 64 (@span_join (checked 6) 16 1216 32 chunk6x1216 (@span_join (checked 6) 16 1232 16 chunk6x1232 chunk6x1248)) (@span_join (checked 6) 32 1264 32 (@span_join (checked 6) 16 1264 16 chunk6x1264 chunk6x1280) (@span_join (checked 6) 16 1296 16 chunk6x1296 chunk6x1312))))) (@span_join (checked 6) 224 1328 224 (@span_join (checked 6) 112 1328 112 (@span_join (checked 6) 48 1328 64 (@span_join (checked 6) 16 1328 32 chunk6x1328 (@span_join (checked 6) 16 1344 16 chunk6x1344 chunk6x1360)) (@span_join (checked 6) 32 1376 32 (@span_join (checked 6) 16 1376 16 chunk6x1376 chunk6x1392) (@span_join (checked 6) 16 1408 16 chunk6x1408 chunk6x1424))) (@span_join (checked 6) 48 1440 64 (@span_join (checked 6) 16 1440 32 chunk6x1440 (@span_join (checked 6) 16 1456 16 chunk6x1456 chunk6x1472)) (@span_join (checked 6) 32 1488 32 (@span_join (checked 6) 16 1488 16 chunk6x1488 chunk6x1504) (@span_join (checked 6) 16 1520 16 chunk6x1520 chunk6x1536)))) (@span_join (checked 6) 112 1552 112 (@span_join (checked 6) 48 1552 64 (@span_join (checked 6) 16 1552 32 chunk6x1552 (@span_join (checked 6) 16 1568 16 chunk6x1568 chunk6x1584)) (@span_join (checked 6) 32 1600 32 (@span_join (checked 6) 16 1600 16 chunk6x1600 chunk6x1616) (@span_join (checked 6) 16 1632 16 chunk6x1632 chunk6x1648))) (@span_join (checked 6) 48 1664 64 (@span_join (checked 6) 16 1664 32 chunk6x1664 (@span_join (checked 6) 16 1680 16 chunk6x1680 chunk6x1696)) (@span_join (checked 6) 32 1712 32 (@span_join (checked 6) 16 1712 16 chunk6x1712 chunk6x1728) (@span_join (checked 6) 16 1744 16 chunk6x1744 chunk6x1760))))))) (@span_join (checked 6) 880 1776 887 (@span_join (checked 6) 432 1776 448 (@span_join (checked 6) 208 1776 224 (@span_join (checked 6) 96 1776 112 (@span_join (checked 6) 48 1776 48 (@span_join (checked 6) 16 1776 32 chunk6x1776 (@span_join (checked 6) 16 1792 16 chunk6x1792 chunk6x1808)) (@span_join (checked 6) 16 1824 32 chunk6x1824 (@span_join (checked 6) 16 1840 16 chunk6x1840 chunk6x1856))) (@span_join (checked 6) 48 1872 64 (@span_join (checked 6) 16 1872 32 chunk6x1872 (@span_join (checked 6) 16 1888 16 chunk6x1888 chunk6x1904)) (@span_join (checked 6) 32 1920 32 (@span_join (checked 6) 16 1920 16 chunk6x1920 chunk6x1936) (@span_join (checked 6) 16 1952 16 chunk6x1952 chunk6x1968)))) (@span_join (checked 6) 112 1984 112 (@span_join (checked 6) 48 1984 64 (@span_join (checked 6) 16 1984 32 chunk6x1984 (@span_join (checked 6) 16 2000 16 chunk6x2000 chunk6x2016)) (@span_join (checked 6) 32 2032 32 (@span_join (checked 6) 16 2032 16 chunk6x2032 chunk6x2048) (@span_join (checked 6) 16 2064 16 chunk6x2064 chunk6x2080))) (@span_join (checked 6) 48 2096 64 (@span_join (checked 6) 16 2096 32 chunk6x2096 (@span_join (checked 6) 16 2112 16 chunk6x2112 chunk6x2128)) (@span_join (checked 6) 32 2144 32 (@span_join (checked 6) 16 2144 16 chunk6x2144 chunk6x2160) (@span_join (checked 6) 16 2176 16 chunk6x2176 chunk6x2192))))) (@span_join (checked 6) 224 2208 224 (@span_join (checked 6) 112 2208 112 (@span_join (checked 6) 48 2208 64 (@span_join (checked 6) 16 2208 32 chunk6x2208 (@span_join (checked 6) 16 2224 16 chunk6x2224 chunk6x2240)) (@span_join (checked 6) 32 2256 32 (@span_join (checked 6) 16 2256 16 chunk6x2256 chunk6x2272) (@span_join (checked 6) 16 2288 16 chunk6x2288 chunk6x2304))) (@span_join (checked 6) 48 2320 64 (@span_join (checked 6) 16 2320 32 chunk6x2320 (@span_join (checked 6) 16 2336 16 chunk6x2336 chunk6x2352)) (@span_join (checked 6) 32 2368 32 (@span_join (checked 6) 16 2368 16 chunk6x2368 chunk6x2384) (@span_join (checked 6) 16 2400 16 chunk6x2400 chunk6x2416)))) (@span_join (checked 6) 112 2432 112 (@span_join (checked 6) 48 2432 64 (@span_join (checked 6) 16 2432 32 chunk6x2432 (@span_join (checked 6) 16 2448 16 chunk6x2448 chunk6x2464)) (@span_join (checked 6) 32 2480 32 (@span_join (checked 6) 16 2480 16 chunk6x2480 chunk6x2496) (@span_join (checked 6) 16 2512 16 chunk6x2512 chunk6x2528))) (@span_join (checked 6) 48 2544 64 (@span_join (checked 6) 16 2544 32 chunk6x2544 (@span_join (checked 6) 16 2560 16 chunk6x2560 chunk6x2576)) (@span_join (checked 6) 32 2592 32 (@span_join (checked 6) 16 2592 16 chunk6x2592 chunk6x2608) (@span_join (checked 6) 16 2624 16 chunk6x2624 chunk6x2640)))))) (@span_join (checked 6) 448 2656 439 (@span_join (checked 6) 224 2656 224 (@span_join (checked 6) 112 2656 112 (@span_join (checked 6) 48 2656 64 (@span_join (checked 6) 16 2656 32 chunk6x2656 (@span_join (checked 6) 16 2672 16 chunk6x2672 chunk6x2688)) (@span_join (checked 6) 32 2704 32 (@span_join (checked 6) 16 2704 16 chunk6x2704 chunk6x2720) (@span_join (checked 6) 16 2736 16 chunk6x2736 chunk6x2752))) (@span_join (checked 6) 48 2768 64 (@span_join (checked 6) 16 2768 32 chunk6x2768 (@span_join (checked 6) 16 2784 16 chunk6x2784 chunk6x2800)) (@span_join (checked 6) 32 2816 32 (@span_join (checked 6) 16 2816 16 chunk6x2816 chunk6x2832) (@span_join (checked 6) 16 2848 16 chunk6x2848 chunk6x2864)))) (@span_join (checked 6) 112 2880 112 (@span_join (checked 6) 48 2880 64 (@span_join (checked 6) 16 2880 32 chunk6x2880 (@span_join (checked 6) 16 2896 16 chunk6x2896 chunk6x2912)) (@span_join (checked 6) 32 2928 32 (@span_join (checked 6) 16 2928 16 chunk6x2928 chunk6x2944) (@span_join (checked 6) 16 2960 16 chunk6x2960 chunk6x2976))) (@span_join (checked 6) 48 2992 64 (@span_join (checked 6) 16 2992 32 chunk6x2992 (@span_join (checked 6) 16 3008 16 chunk6x3008 chunk6x3024)) (@span_join (checked 6) 32 3040 32 (@span_join (checked 6) 16 3040 16 chunk6x3040 chunk6x3056) (@span_join (checked 6) 16 3072 16 chunk6x3072 chunk6x3088))))) (@span_join (checked 6) 224 3104 215 (@span_join (checked 6) 112 3104 112 (@span_join (checked 6) 48 3104 64 (@span_join (checked 6) 16 3104 32 chunk6x3104 (@span_join (checked 6) 16 3120 16 chunk6x3120 chunk6x3136)) (@span_join (checked 6) 32 3152 32 (@span_join (checked 6) 16 3152 16 chunk6x3152 chunk6x3168) (@span_join (checked 6) 16 3184 16 chunk6x3184 chunk6x3200))) (@span_join (checked 6) 48 3216 64 (@span_join (checked 6) 16 3216 32 chunk6x3216 (@span_join (checked 6) 16 3232 16 chunk6x3232 chunk6x3248)) (@span_join (checked 6) 32 3264 32 (@span_join (checked 6) 16 3264 16 chunk6x3264 chunk6x3280) (@span_join (checked 6) 16 3296 16 chunk6x3296 chunk6x3312)))) (@span_join (checked 6) 112 3328 103 (@span_join (checked 6) 48 3328 64 (@span_join (checked 6) 16 3328 32 chunk6x3328 (@span_join (checked 6) 16 3344 16 chunk6x3344 chunk6x3360)) (@span_join (checked 6) 32 3376 32 (@span_join (checked 6) 16 3376 16 chunk6x3376 chunk6x3392) (@span_join (checked 6) 16 3408 16 chunk6x3408 chunk6x3424))) (@span_join (checked 6) 48 3440 55 (@span_join (checked 6) 16 3440 32 chunk6x3440 (@span_join (checked 6) 16 3456 16 chunk6x3456 chunk6x3472)) (@span_join (checked 6) 32 3488 23 (@span_join (checked 6) 16 3488 16 chunk6x3488 chunk6x3504) (@span_join (checked 6) 16 3520 7 chunk6x3520 chunk6x3536))))))))

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
theorem chunk7x160 : span (checked 7) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x176 : span (checked 7) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x192 : span (checked 7) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x208 : span (checked 7) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x224 : span (checked 7) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x240 : span (checked 7) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x256 : span (checked 7) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x272 : span (checked 7) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x288 : span (checked 7) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x304 : span (checked 7) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x320 : span (checked 7) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x336 : span (checked 7) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x352 : span (checked 7) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x368 : span (checked 7) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x384 : span (checked 7) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x400 : span (checked 7) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x416 : span (checked 7) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x432 : span (checked 7) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x448 : span (checked 7) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x464 : span (checked 7) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x480 : span (checked 7) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x496 : span (checked 7) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x512 : span (checked 7) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x528 : span (checked 7) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x544 : span (checked 7) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x560 : span (checked 7) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x576 : span (checked 7) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x592 : span (checked 7) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x608 : span (checked 7) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x624 : span (checked 7) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x640 : span (checked 7) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x656 : span (checked 7) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x672 : span (checked 7) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x688 : span (checked 7) 6 688 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 694 0 = true :=
  (@span_join (checked 7) 352 0 342 (@span_join (checked 7) 176 0 176 (@span_join (checked 7) 80 0 96 (@span_join (checked 7) 32 0 48 (@span_join (checked 7) 16 0 16 chunk7x0 chunk7x16) (@span_join (checked 7) 16 32 32 chunk7x32 (@span_join (checked 7) 16 48 16 chunk7x48 chunk7x64))) (@span_join (checked 7) 48 80 48 (@span_join (checked 7) 16 80 32 chunk7x80 (@span_join (checked 7) 16 96 16 chunk7x96 chunk7x112)) (@span_join (checked 7) 16 128 32 chunk7x128 (@span_join (checked 7) 16 144 16 chunk7x144 chunk7x160)))) (@span_join (checked 7) 80 176 96 (@span_join (checked 7) 32 176 48 (@span_join (checked 7) 16 176 16 chunk7x176 chunk7x192) (@span_join (checked 7) 16 208 32 chunk7x208 (@span_join (checked 7) 16 224 16 chunk7x224 chunk7x240))) (@span_join (checked 7) 48 256 48 (@span_join (checked 7) 16 256 32 chunk7x256 (@span_join (checked 7) 16 272 16 chunk7x272 chunk7x288)) (@span_join (checked 7) 16 304 32 chunk7x304 (@span_join (checked 7) 16 320 16 chunk7x320 chunk7x336))))) (@span_join (checked 7) 176 352 166 (@span_join (checked 7) 80 352 96 (@span_join (checked 7) 32 352 48 (@span_join (checked 7) 16 352 16 chunk7x352 chunk7x368) (@span_join (checked 7) 16 384 32 chunk7x384 (@span_join (checked 7) 16 400 16 chunk7x400 chunk7x416))) (@span_join (checked 7) 48 432 48 (@span_join (checked 7) 16 432 32 chunk7x432 (@span_join (checked 7) 16 448 16 chunk7x448 chunk7x464)) (@span_join (checked 7) 16 480 32 chunk7x480 (@span_join (checked 7) 16 496 16 chunk7x496 chunk7x512)))) (@span_join (checked 7) 80 528 86 (@span_join (checked 7) 32 528 48 (@span_join (checked 7) 16 528 16 chunk7x528 chunk7x544) (@span_join (checked 7) 16 560 32 chunk7x560 (@span_join (checked 7) 16 576 16 chunk7x576 chunk7x592))) (@span_join (checked 7) 48 608 38 (@span_join (checked 7) 16 608 32 chunk7x608 (@span_join (checked 7) 16 624 16 chunk7x624 chunk7x640)) (@span_join (checked 7) 16 656 22 chunk7x656 (@span_join (checked 7) 16 672 6 chunk7x672 chunk7x688))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x16 : span (checked 8) 2 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 18 0 = true :=
  (@span_join (checked 8) 16 0 2 chunk8x0 chunk8x16)

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

end PEqualNP.Outside.L_meta_12316_aux

open PEqualNP.Outside.L_meta_12316_aux

theorem PEqualNP.Outside.L_meta_12316 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
