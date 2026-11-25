import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12270_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4269866496 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [4,5]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.or, [3,6]⟩,
  ⟨.and, [1,2]⟩,
  ⟨.and, [0,9]⟩,
  ⟨.or, [0,7]⟩,
  ⟨.and, [8,10]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.and, [3,13]⟩,
  ⟨.and, [11,14]⟩,
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

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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

theorem columns_valid (rows : List Nat) (length : rows.length = 41) (w : W) : Valid rows (columns rows w) := by
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
theorem full_bit {rows : List Nat} (length : rows.length = 41) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 2624 := by omega
  have val : fullLanes = 2^2624-1 := by decide +kernel
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

theorem valid_not {rows : List Nat} (length : rows.length = 41) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 41) (bounds : ∀ r ∈ rows, r < 64)
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

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 41) {s : List W}
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

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 41) (xs : List Columns)
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
    (length : rows.length = 41) (bounds : ∀ r ∈ rows, r < 64)
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
    (length : rows.length = 41) (bounds : ∀ r ∈ rows, r < 64)
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

end SignedFrontier.SmallCert.Minor0

namespace SignedFrontier.SmallCert.Minor2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xaaaeaefeaaaeaefe
def negative : List Nat := [0, 8, 12, 14, 16, 20, 22, 24, 26, 28, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,4,12),(0xffff0000ffff0000,4,20)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xf8f8f8f8f8f8f8f8f500f500f500f500f4f4f4f4f4f4f4f4f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f0f0fafaf0f0fafaf0f0f0f0f0f0f0f0f050f050f050f050f000f000f000f000eeeeeeeeeeeeeeeeeecceecceecceeccececececececececdd00dd00dd00dd00dcdcdcdcdcdcdcdcd0d0d0d0d0d0d0d0cececececececececcccfcfcccccfcfccccceeeecccceeeecccccccccccccccccc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00ff00cc00ff00cc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0aeaeaeaeaeaeaeaeaaaaaaaaaaaaaaaaaa00aa00aa00aa00a0a0a0a0a0a0a0a08c8c8c8c8c8c8c8c8888888888888888770077007700770070707070707070705f005f005f005f0055550000555500005500ff005500ff00550055005500550054545454545454545050f0f05050f0f050505050505050504c4c4c4c4c4c4c4c4444cccc4444cccc44444444444444443300330033003300303030303030303022222222222222220f00ff000f00ff000f000f000f000f000e0e0e0e0e0e0e0e0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a040404040404040400fc00fc00fc00fc00f0f0f000f0f0f000cccccc00cccccc0000fff00000fff00000ff000000ff000000fcfc0000fcfc0000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa0000000000000000 else 0xffffff00ffffff00fffff000fffff000ffffaaaaffffaaaaffffaa00ffffaa00ffffa0a0ffffa0a0ffff8888ffff8888ffff3300ffff3300ffff2222ffff2222ffff0a0affff0a0affff00aaffff00aaffff0000ffff0000fff0fff0fff0fff0fff0f0f0fff0f0f0ffccffccffccffccffccccccffccccccffaaffaaffaaffaaff00ff00ff00ff00ff00f000ff00f000ff005500ff005500ff000000ff000000fefefefefefefefefcfcfcfcfcfcfcfcfcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafaf0faf0faf0faf0) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1b1c3448270d09b1a2f001052e00599a30094d50041338016439400c0c90030224009085 else 0
  | 4 => if page < 2 then (if page < 1 then 0x8811a301e404be808bd0113a021f403de806dd00d7a01a74032e8061d00bfa0177404dd8083b0103601fec03cd8077b00eb602c3c057780acf0155e02a3c053780a4f0145e0283c048b808f7010ae01f5c038d8067700c760167402be8055700a3a013ec025e8043d007ee00f6c01db80377006ae00cf4018d802fb005ba00af4014e80217003ba006f400ce8015d00236003f400678008f else 0x22c1cc4839af11b121560b6cd76cdaf0575e51ecc63ca356886aad8d5609a9d73473868f04bea217cb62f9645f35cbad097c9a2f36c53904a66b9469a2952e5333866620ccc1199ae31a68654b8ccc1159) else 0
  | 5 => if page < 1 then 0xb3f9df99f95f8df89f83f6ff6df53f4df47f45f41f35f2ff29f27f25f23f1ff19f17f0bf07f05f03f89d6dd83baef3572fb29d19d else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x35 else 0
  | 4 => if page < 1 then 0x9c27 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 11
  | 4 => 98
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
  | 3 => 5
  | 4 => 43
  | 5 => 17
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 18
  | 4 => 168
  | 5 => 60
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 3
  | 4 => 6
  | 5 => 6
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 5
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x4c00 else 0
  | 4 => if page < 1 then 0x41810890081047c00433c0cc21811000093010800410034830c0009003082081 else 0
  | 5 => if page < 1 then 0x7201c510008705104400025a else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1230140038686522414160 else 0
  | 4 => if page < 3 then (if page < 1 then 0x96a0ad9800be00aa4d00788d124e525c4aac7a00580800b000b700640000000200000000b956820084c04f607f7e0188004c9e72917054458c46402621bd3f31 else (if page < 2 then 0x3e382da2181fba85061b689a620e1e0000000000b1005300240048042723bf155e163b923900003387000000433500740a00767c000000005a008a50ab000036 else 0x28998ea69c8694902ac21cb62247a8b2a46c3c6a800db8667d49002eb493119d000000aeafbc6e3d)) else 0
  | 5 => if page < 1 then 0x7e44e330ce9a268678b802608a2f46dd600003851580f862a880181a130612048114000089e1d0e017182049c3600599005200008 else 0
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
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 11 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 11 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 98 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 98 0 = true :=
  chunk4x0

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

end SignedFrontier.SmallCert.Minor2

namespace SignedFrontier.SmallCert.Minor3

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xeaaafffeeaaafffe
def negative : List Nat := [0, 16, 18, 20, 22, 24, 26, 28]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,2,18)] (by decide +kernel) (by decide +kernel)

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

end SignedFrontier.SmallCert.Minor3

namespace SignedFrontier.SmallCert.Minor6

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x8080fffe8080fffe
def negative : List Nat := [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xffffff00ffffff00ffffaaaaffffaaaaffff0f00ffff0f00ffff0000ffff0000fff0fff0fff0fff0ffeeffeeffeeffeeffccffccffccffccffaaffaaffaaffaaffaaff00ffaaff00ff88ff88ff88ff88ff0fff00ff0fff00ff0aff0aff0aff0aff00ffaaff00ffaaff00ff00ff00ff00ff000f00ff000f00ff000000ff000000f7f0f7f0f7f0f7f0f5f0f5f0f5f0f5f0f3f3f3f0f3f3f3f0f3f3f0f0f3f3f0f0f3f2f3f2f3f2f3f2f3f0fff0f3f0fff0f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f1f0f1f0f1f0f1f0f0f0fffaf0f0fffaf0f0fff0f0f0fff0f0f0fafaf0f0fafaf0f0f3f0f0f0f3f0f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeddccddccddccddcccfcccfcccfcccfccccccffccccccffccccccccccccccccccafaaafaaafaaafaaaf00af00af00af00aaaaffaaaaaaffaaaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000aaaa0000aa00ff00aa00ff00aa00aa00aa00aa00a0aaa0aaa0aaa0aa8a8a8a8a8a8a8a8a88aa88aa88aa88aa8888aaaa8888aaaa88888888888888883f003f003f003f000f0f0f000f0f0f000f0f00000f0f00000f0a0f0a0f0a0f0a0f00ff000f00ff000f000f000f000f000a0a0a0a0a0a0a0a030003000300030000ff000000ff000000aa00aa00aa00aa0000ffaa0000ffaa0000ff000000ff000000aaaa0000aaaa00000f0000000f000000000000000000 else 0xffffffaaffffffaa) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x2e41194f4652f2e49539234a48cb9214e87d005f3016cc05730154c0533013cc04d3012cc0473 else 0
  | 4 => if page < 1 then 0x382d6847f391f5ec64df135ec4cd3136ec44e5073fc19d70760166c053b0146c04bb0126c081701fdc07b701d5c071701bdc06d701adc0697019dc063700e5c037700d5c031e00bf802b700978023e0087801d7006dc01770055c0137003dc0097001dc0037014cc04b3 else 0
  | 5 => if page < 1 then 0x1fffeff1fc3f0fd6fa9f3fe67c9f91f1be2fc3f85ffefc5c9b877 else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x25 else 0
  | 4 => if page < 1 then 0x25 else 0
  | 5 => if page < 1 then 0x17 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 17
  | 4 => 47
  | 5 => 19
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
  | 3 => 12
  | 4 => 29
  | 5 => 16
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 43
  | 4 => 114
  | 5 => 61
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 4
  | 4 => 5
  | 5 => 5
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
  | 3 => if page < 1 then 0x1a7002103920 else 0
  | 4 => if page < 1 then 0x80882042c649046008000014410000620822 else 0
  | 5 => if page < 1 then 0x4122f001a200d4008221 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1c720024607000597a4808116c22212c007854010031517100290010440c2000393c005064830904680061 else 0
  | 4 => if page < 2 then (if page < 1 then 0x943400014005c27a8500364000015802b010782e2700000000133080d81803c0006018403d171e768104800000540020848398024688b192400598c800235c000aa22d3a4000c8b0 else 0x108f2004f1b000a14500131a826238f8b15492b22001b000008022a680026320009a3080298a414000f0e820a2c0004700d0a7403d805f309) else 0
  | 5 => if page < 1 then 0x32452040625100004371834c6800447412003309008813082850004180001863004200235c300c70580000008a10004960823854592248786a6b908b00 else 0
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
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 17 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 17 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 47 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 47 0 = true :=
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

end SignedFrontier.SmallCert.Minor6

namespace SignedFrontier.SmallCert.Minor7

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

end SignedFrontier.SmallCert.Minor7

namespace SignedFrontier.SmallCert.Minor8

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x8880fffe8880fffe
def negative : List Nat := [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,0,8),(0xffff0000ffff0000,1,17)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xfff0fffafff0fffafff0fff0fff0fff0fff0ff00fff0ff00fff0f3f0fff0f3f0fff03330fff03330fff00000fff00000ffa0ffa0ffa0ffa0ff33ff00ff33ff00ff30ff30ff30ff30ff22ff22ff22ff22ff00fff0ff00fff0ff00ffaaff00ffaaff00ff00ff00ff00fbf0fbf0fbf0fbf0fafafafafafafafafaf0fff0faf0fff0f0f0f0f0f0f0f0f0f0f03030f0f03030f0f000f0f0f000f0f0f00000f0f00000f000f000f000f000eeeeeeeeeeeeeeeeddddccccddddccccdddcdddcdddcdddcdcdcdcdcdcdcdcdccccfcccccccfccccccceccceccceccceccccfffcccccfffcccccfcfcccccfcfccccceeeecccceeeeccccccccccccccccbbb0bbb0bbb0bbb0b0b0b0b0b0b0b0b0aaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa00aaaaaa00aaaaaa000aaaaa000aaaaa0000aaaa0000aaa2aaa2aaa2aaa2aaa0fff0aaa0fff0aaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0a0f0a0f0a0f0a0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0a0a088aa88aa88aa88aa888a888a888a888a8888aaaa8888aaaa88888888888888883333000033330000333033303330333030f030f030f030f03030303030303030222222222222222200ff000000ff000000f0f0f000f0f0f000f000f000f000f000aa00aa00aa00aa000f0000000f0000000a000a000a000a0000fff00000fff00000f0f00000f0f00000aaaa0000aaaa0000000000000000 else 0xfffffff0fffffff0fffff0f0fffff0f0ffffaaaaffffaaaaffff0000ffff0000fffafffafffafffafff3fff0fff3fff0fff2fff2fff2fff2) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xf950f800f94c407ca2203e4f101f26880f92c407c92203e47101f22880f8ec807c72403e37201f19900f8bc80845a403e25201f11900f88480010660008130003f98001f4c000f26000773000329800184c000826000313 else 0
  | 4 => if page < 1 then 0x119f4e2be9c47d384fa6f9d4df319be5937cae6f954df1a9be2d37c4e6a87f1f0f9be1d37c366f85cdf0a9be1337c1e6f834df059be0937c0e6f814df0198053d009fa011f4022e807d700f6e01cdc038b806f700dae01adc034b805db00b7600fec01df0039e0057600a6c012f0021e003360046c007d807d3 else 0
  | 5 => if page < 1 then 0x8bf89f7df63f59f57f55f35f27f1ff1df17f15f13f0ff0df05f03f7d70fb7d3 else 0
  | 6 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x33 else 0
  | 4 => if page < 1 then 0x27 else 0
  | 5 => if page < 1 then 0x19 else 0
  | 6 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 28
  | 4 => 51
  | 5 => 21
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
  | 3 => 13
  | 4 => 26
  | 5 => 15
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 47
  | 4 => 93
  | 5 => 54
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 6
  | 4 => 6
  | 5 => 4
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 7
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x310899e200404044042 else 0
  | 4 => if page < 1 then 0x19a0401ccd0e00c0001282c4186102040181001 else 0
  | 5 => if page < 1 then 0x5a0c560e0c40a04 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xc6380b1528625024aa494000000116112b94804481b301c5959a001b9a400bda104c0ce353004e9f18 else 0
  | 4 => if page < 2 then (if page < 1 then 0x5ab4002d4cbc00321f801b04a8c0ac21232ac8940f38741aa6c28a7c9e4000789ca22bb034a044451558663d903c6492880951007ba43300be268e5000057db6 else 0x4870356c79869862840000008c00c4100054815e7268b8) else 0
  | 5 => if page < 1 then 0xe181851880005403360016347001b204888005014404e889482a514004c089e0bc1d0229623184098ec93003a64bc8 else 0
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
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 28 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 28 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 51 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 51 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 21 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 21 0 = true :=
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

end SignedFrontier.SmallCert.Minor8

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfe80fe00fe008000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 32, 33, 34, 35, 36, 37, 38, 39, 40, 48, 49, 50, 51, 52, 53, 54, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,14,15),(0xcccccccccccccccc,13,15),(0xf0f0f0f0f0f0f0f0,11,15),(0xff00ff00ff00ff00,7,15),(0xffff0000ffff0000,9,25),(0xffffffff00000000,9,41)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xcccccccc00000000afaf000000000000af00af0000000000aaff000000000000aaaaaaaa00000000aaaaaa0000000000aaaa888800000000aaaa0a0a00000000aaaa00aa00000000aaaa000000000000aa88aa8800000000aa0aaa0a00000000aa00ff0000000000aa00aaaa00000000aa00aa0000000000aa00000000000000a8a8a8a8000000008a8a8a8a0000000088aa88aa000000008888aaaa0000000088888888000000008888000000000000880088000000000080808080000000003f3f0000000000003f003f00000000002a2a2a2a000000000fff0000000000000f0f0f00000000000f0f0a0a000000000f0f0000000000000f0a0f0a000000000f00ff00000000000f000f00000000000f000000000000000e0e0e0e000000000aaa0aaa000000000a0aaaaa000000000a0a0a0a000000000a0a0000000000000a000a0000000000080808080000000003030000000000000300030000000000020202020000000000ff00aa0000000000ff00000000000000ee00ee0000000000aaaaaa0000000000aa00aa0000000000aa0000000000000088008800000000000f000000000000000a000a000000000000ffaa000000000000ff00000000000000eeee000000000000aaaa000000000000aa0000000000000088880000000000000f000000000000000a0a00000000000000aa0000000000000000 else (if page < 2 then 0xaa00aa00aa000000aa008800aa008800aa000a00aa000a00aa0000aaaa000000aa000000ff000000aa000000aa00aa00aa000000aa000000aa00000000000000a800a800a800a8008a008a008a008a00880088888888880088008800aa00aa008800880088008800880000008800000080008000800080003f0000003f0000002a002a002a002a000f000f000f0000000f000a000f000a000f00000f0f0000000f000000ff0000000f0000000f0000000f000000000000000e000e000e000e000a000a0a0a0a0a000a000a00aa00aa000a000a000a000a000a0000000a00000008000800080008000300000003000000020002000200020000ffff000000000000ffcc0000ffcc0000ffaaffaaffaa0000ff00ff00ff000000ff000000ff000000ff00000000000000eeeeeeeeeeee0000cccc0000cccc0000aaaaff00ffaa0000aaaacccceeee0000aaaaaaaaaaaa0000aaaa0000aaaa0000aa00aa00aa00000088888888888800000f000f000f0000000a0a0a0a0a0a000000aa00aa00aa00000000ffffff0000000000ffffaaaa00000000ffff000000000000ffccffcc00000000ffaaffaa00000000ffaa000000000000ff88ff8800000000ff0f000000000000ff00ff0000000000ff00aa0000000000ff000f0000000000ff00000000000000fcfcfcfc00000000eeeeeeee00000000eeee000000000000ee00ee00 else 0xa0a08080a0a08080a0a02020a0a02020a0a000a0a0a000a0a0a0000aaaa00000a0a00000f0f00000a0a00000a0a0a0a0a0a00000a0a00000a0a0000000000000a080a080a080a080a020a020a020a020a000a00aa00aa000a000a000f000f000a000a000a0a0a0a0a000a000a000a000a0000000a0000000888088808880888080a080a080a080a0808080888888888080808080a0a0a0a08080808080808080808000008080000080008000800080007070000070700000700070007000700030f0000030f0000030303030303000003030300030303000303020203030202030300000f0f0000030300000303000003030000000000000302030203020302030003000f000f0003000300030003000300000003000000020a020a020a020a020202020a0a0a0a0202020202020202020200000202000002000200020002000101000001010000010001000100010000ffffff0000000000ff00ff00ff000000ff00ff00aa00aa00ff00ff0000000000ff00aaffffaaaa00ff00aa00ff00aa00ff0000ffff000000ff0000aaffaaaa00ff000000ff000000ff000000aa000000ff0000000f000000ff00000000000000fc00fc00fc00fc00ee00eeeeeeeeee00ee00ee00ee00ee00ee000000ee000000cc00cc00cc00cc00af000000af000000aa00aaffff00aa00aa00aacceeccee00aa00aaaaaaaaaa00aa00aa00aa00aa)) else (if page < 4 then 0xfff0000ffff00000fff00000fff00000fff0000000000000faf00aa0faf00aa0f0fffff000000000f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f00ffffff000f0f0f000f0f0f000f0f0a0affffaaaa0f0f0a0a0f0f0a0a0f0f0000ffff00000f0f0000ff0fff000f0f0000afafaaaa0f0f00000f0f00000f0f00000f0000000f0f00000a0a00000f0f0000030300000f0f0000000f00000f0f0000000000000f0c0f0c0f0c0f0c0f0a0f0affaaffaa0f0a0f0a0f0a0f0a0f0a00000f0a00000f080f080f080f080f0300000f0300000f000f00ffff0f000f000f00ff00ff000f000f00afaaafaa0f000f000f000f000f000f000f0000000f000a000f000a000f0003000f0003000f000000ff0000000f0000000f0f00000f0000000f000f000f0000000f0000000f000000000000000eee0eee0eee0eee0e0e0e0eeeeeeeee0e0e0e0e0e0e0e0e0e0e00000e0e00000e000e000e000e000c0c0c0c0c0c0c0c0b0b0b000b0b0b000b0b00000b0b00000b000b000b000b000aff0a0a0aff0a0a0ace0ace0ace0ace0aaa0aaaaaaaaaaa0aaa0aaa8aaa8aaa0aaa0aaa0aaaaaaa0aaa0aaa0aaa0aaa0aaa00000aaa00000a0f00000a0f00000a0a0a0affff0a0a0a0a0a0aff0aff0a0a0a0a0acececece0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a000a0a0a00 else (if page < 5 then 0x88880000aaaa00008888000088888888888800008888000088880000000000008880888088808880880888088808880888008800aa00aa0088008800888888888800880088008800880000008800000080aa80aa80aa80aa808880888088808880808080888888888080808080808080808000008080000080008000800080007fff00007fff00007f7f00007f7f00007f007f007f007f007777777700000000770077007700770070707070707070705f005f005f005f0055ff55ff0000000055555555000000005555550055555500555544445555444455550000555500005544554455445544550055005500550050f050f050f050f050505050505050504c4c4c4c4c4c4c4c44444444444444443fff00003fff00003f3f3f3f3f3f00003f3f3f003f3f3f003f3f2a2a3f3f2a2a3f3f0f0f333300003f3f00003f3f00003f3f0000000000003f2a3f2a3f2a3f2a3f0f33003f0f33003f003f003f003f003f0000003f0000003333333333003300333333330000000033333300333333003333000033330000330033003300330030f030f030f030f030303030f0f0f0f030303030303030302f2f2f002f2f2f002f2f22222f2f22222f222f222f222f222aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a2a2a00002a2a00002a002a002a002a0022222222222222220fff0fff0fff00000fff0aaa0fff0aaa0fff00ff0f0f0000 else 0xaaaa00000a0a0000aaaa000000aa0000aaaa000000000000aaa0aaa0aaa0aaa0aa88aa88ffccffccaa88aa88aaaaaaaaaa88aa88aa88aa88aa880000aa880000aa22aa22aa22aa22aa0aaa0aaa0aaa0aaa0a0000aa0a0000aa00aaaaaa00aaaaaa00aa00ffffaa00aa00aa00ff00ff00aa00aa00eecceeccaa00aa00aaaaaaaaaa00aa00aa00aa00aa00aa00aa000000aa008800aa008800aa000a00aa000a00aa000000ff000000aa000000aaaa0000aa000000aa00aa00aa000000aa000000aa00000000000000a8fca8fca8fca8fca8a8a8a8fcfcfcfca8a8a8a8a8a8a8a8a8a80000a8a80000a800a800a800a800a2a2a2a2a2a2a2a2a0aaa0aaa0aaa0aaa0a0aaaaa0a0aaaaa0a0a0a0f0f0f0f0a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a0008f8f88888f8f88888f8f00008f8f00008f888f888f888f888f008f008f008f008aaa8aaa8aaa8aaa8a8a8a8a8a8a8a8a8a8a8a008a8a8a008a8a00008a8a00008a0a8a0a8a0a8a0a8a008a008a008a0088ff888888ff888888ff000088ff000088f888f888f888f888aa88aa88aa88aa88aa000088aa000088888888ffff888888888888ff88ff8888888888f8f8f8f888888888aaaaaaaa888888888888888888888888888800008888888800000000888888008888880088888080888880808888080888880808888800888888008888880000ffff0000))) else (if page < 9 then (if page < 7 then 0xc000c000c000c000bfaabfaabfaabfaabbbbaaaabbbbaaaabbaabbaabbaabbaab0b0b0b0b0b0b0b0afafafafafaf0000afafafaf00000000afafaf00afafaf00afafaaaaafafaaaaafaf8c8cafaf8c8cafaf0f0faaaa0000afaf0000afaf0000afaf000000000000afaaafaaafaaafaaafaa0f00afaa0f00af8caf8caf8caf8caf0faa00af0faa00af0f0000af0f0000af00af00af00af00af000000af000000aeeeaeeeaeeeaeeeaeaeaeaeaeaeaeaeaeae0c0caeae0c0cae0cae0cae0cae0caaffaaffaaff0000aaffaaffaaaaaaaaaaffaaaaaaffaaaaaaff88ccaaff88ccaaff00ffaaaa0000aaff0000aaff0000aaff000000000000aaeeaaeeaaeeaaeeaaee00ccaaee00ccaaaaffff00000000aaaaeeeeaaaaeeeeaaaaaaaaffffaaaaaaaaaaaaffaaffaaaaaaaaaaeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa88888888aaaaaaaa00aa00aaaaaaaaaa0000aaaaaaaaaaaa00000000aaaaaa88aaaaaa88aaaaaa0aaaaaaa0aaaaaaa00ffffff00aaaaaa00aaaaaa00aaaa8888ffffccccaaaa8888aaaa8888aaaa2222aaaa2222aaaa0a0aaaaaaaaaaaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000ffff0000aaaa0000ffaaff00aaaa0000eeeeccccaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa0000aa000000aaaa000088880000 else (if page < 8 then 0xf000f000f000f000f0000000f0000000efefeeeeefefeeeeefeeefeeefeeefeeeeffeeeeeeffeeeeeefeeefeeefeeefeeeeeeeeeffffeeeeeeeeeeeeffeeffeeeeeeeeeefefefefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeee0e0eeeee0e0eeeecccceeeecccceeeeaaaaeeeeaaaaeeeeaaaacccc0000eeee0e0eeeee0e0eeeee00eeeeee00eeeeee0000eeeeeeeeeeee0000eeee0000eeee000000000000eee0eee0eee0eee0eecceecceecceecceeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00ee0eee0eee0eee0eee00ee00eeeeeeeeee00ee00ee00ee00ee000000ee000000eaeaeaeaeaeaeaeaeaeac0c0eaeac0c0eac0eac0eac0eac0eaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0dd00dd00dd00dd00dcdcdcdcdcdcdcdccececececececececcffccccccffccccccfcccfcccfcccfccceecceecceecceeccccffff00000000ccccccccffffccccccccccccfcfcfcfccccccccceeeeeeeecccccccccccccccccccccccccccc0000cccccccccc00cc00cccccccc44444444cccccccc00000000cccccc00cccccc00cccc0000ffff0000cccc0000cccc0000ccc0ccc0ccc0ccc0cc44cc44cc44cc44cc00cc00cccccccccc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0c0c00000c0c00000 else 0xff000f00ff000f00ff000000ffff0000ff000000ffaaaaaaff000000ff00ff00ff000000ff000000ff000000aa000000ff0000000f000000ff00000000000000fefefefefefefefefefeeeeefefeeeeefeeefeeefeeefeeefcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0fafaf0f0fafaf0f0faf0faf0faf0faf0faf0faf0faf0f0f0faf0f2f0faf0f2f0faf0f0f0faf0f0f0f8f8f8f8f8f8f8f8f5f50000f5f50000f500f500f500f500f4f4f4f4f4f4f4f4f3f3f0f0f3f3f0f0f3f0f3f0f3f0f3f0f300f300f300f300f2f2f2f2f2f2f2f2f2f2f222f2f2f222f2f2f200f2f2f200f2f0f2f0f2f0f2f0f0fff0fff0f0f0f0f0fff0f0f0fff0f0f0ff0000f0ff0000f0fcf0fcf0fcf0fcf0faf0faf0faf0faf0f0ffff00000000f0f0f0f0fffff0f0f0f0f0f0fcfcfcfcf0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0f03030f0f03030f0f00000ffff0000f0f00000f0f0f0f0f0f00000f0f00000f0f0000000000000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f080f080f080f080f030f030f030f030f000ff00f000ff00f000f000f0f0f0f0)) else (if page < 10 then 0xffff00aa00aa00aaffff0000ffffff00ffff0000ffffaaaaffff0000ffff0000ffff0000ff000000ffff0000aaaa0000ffff000055550000ffff00000f0f0000ffff000000ff0000ffff000000000000fffefffefffefffefff0fff0fff0fff0fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffaaffeeffaaffeeeeeeffeeeeeeffeaffeaffeaffeaffccffccffccffccffccffcc00000000ffcc0000ffcc0000ffc0c0c0ffc0c0c0ffafffaaffafffaaffaeffaeffaeffaeffaaffaaffffffaaffaaffaaffeeffeeffaaffaaffaaffaaffaaffaaffaa0000ffaaffaa00000000ffaaff00ffaaff00ffaacc88ffaacc88ffaaaaaaffaaaaaaffaaaaaaff000000ffaa0f0affaa0f0affaa0000ffaaffaaffaa0000ffaa0000ffaa000000000000ff88ff88ff88ff88ff888888ff888888ff880000ff880000ff80ff80ff80ff80ff550000ff550000ff2aff2aff2aff2aff0fff0fff0f0000ff0fff0f00000000ff0fff00ff0fff00ff0faa0aff0faa0aff0f0f0fff000000ff0f0000ff0f0000ff0f000000000000ff0aff0aff0aff0aff0a0a0aff0a0a0aff00ffff00000000ff00ff00ffffff00ff00ff00ffaaffaaff00ff00ff00ff00ff00ff00ff000000ff00ff00aa00aa00ff00ff0055005500ff00ff000000ff00ff00ff0000000000ff00aa00ffffaaaaff00aa00ff00aa00ff005500ff005500 else (if page < 11 then 0xffffffff0f000f00ffffffff0a0a0a0affffffff00ff0000ffffffff00cc00ccffffffff00aa00aaffffffff0000aaaaffffffff00000000ffffffeeffffffeeffffffaaffffffaaffffffaaffffff00ffffffaaffffaaaaffffffaaffaaffaaffffff88ffffff88ffffff0fffffff00ffffff0affffff0affffff00ffffffaaffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffefefffffefefffff0f0fffff0f0ffffeeeeffffeeeeffffeeeeffffaaaaffffeeeeeeeeeeeeffffeeaaffffeeaaffffeaeaffffeaeaffffccccffffccccffffccccffff0000ffffafafffffaaaaffffafaaffffafaaffffaeaeffffaeaeffffaaffffffaaaaffffaaeeffffaaeeffffaaaaffffffaaffffaaaaffffeeeeffffaaaaffffaaaaffffaaaaffff0000ffffaaaaff00aa00ffffaaaacccc8888ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00aa00aa00ffff8888ffff8888ffff888888888888ffff8800ffff8800ffff8080ffff8080ffff3f00ffff3f00ffff3333ffff0000ffff2a2affff2a2affff0f0fffff0000ffff0f0fff000f00ffff0f0faaaa0a0affff0f0f00000000ffff0f00ffff0f00ffff0f000f000f00ffff0aaaffff0aaaffff0a0affff0a0affff0a0a0a0a0a0affff00ffffff0000ffff00ffaaaa00aaffff00ccffff00ccffff00aaffff00aa else 0xffffffffffffffaaffffffffffffff00ffffffffffffeeeeffffffffffffaaaaffffffffffffaa00ffffffffffff8888ffffffffffff0f00ffffffffffff0a0affffffffffff00aaffffffffffff0000ffffffffff00ff00ffffffffff000000fffffffff0f0f0f0ffffffffccccccccffffffffcccc0000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffff88888888ffffffff80008000ffffffff77770000ffffffff33330000ffffffff0f0f0000)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 5 => if page < 2 then (if page < 1 then 0xb31b43ece6ccf8898dea1e637a87983e9d5557cb31557a7b556e83155e9cd557c72555f1c4557c7d94bf1fb51fc7d547f1f451fc7c547f1f051fc79147f1e051fc7d944f1f64fbcb313d3ece4f0f8d11be5613eba75cf5e5d63d79584f5e9553d7a704a6e5c129798788fad5523ee87881e9f61d7cb385a3ece14cf8784f6d5513deab8423eae0acf00228ec0089fb0021eec00877b0021cec00b15f002c37c00663e00197f800643e0018ff800637e00189f8005ebe00154f8004bef0010aec003d7b000d1ec00333e000cbf80032be else 0xb3a767d9473000b3a76878b002ce9d9553800b31f651dc0027b7d947b000831f651f8001f651cf5e0007d94723ec001f651c4f70000026a8d39000009cdd7e40000222747900000b321e6c000027b87ab00000b32853c00002cea10f00000b31e83c00002ce79cf) else 0
  | 6 => if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x28fe50fc95f923f237e45fc83f903f1f7e3dfc79f8ebf1cfe38fc6ff8d7f1a7e33fc65f8c7f187e2ffc5df8b7f167e2bfc55f8a7f147e27fc4df897f127e23fc45f883f0ffe1dfc39f86ff0d7e18fc2ff85bf0afe14fc27f84bf087e0ffc1bf833f05fe0afc13f81ff02fe04fc07f80bf00ff8dfaf3f557e else (if page < 2 then 0xabfeabfa9fea3fa7fe9bfa5fe93fa3fe87fa0fe7ff9dfe73f9bfe67f98fe5ff96fe47f8efe33f8bfe23f86fe13f83fe0bf80fdfff7efdf7f7cfdeff7afde3f77fddbf75fdd3f73fdcbf71fdc3f6ffdbbf6dfdb3f6bfda7f68fd9ff66fd93f63fd8bf61fd7bf5afd63f57fd53f53fd4bf else 0x827f02fe03fc03f7f7efdfdf9fbdbf7a7ef1fde1fbbbf76feecfdd7fba3f737ee4fdc7fb87f707edffdbdfb77f6e7edbfdb5fb63f6bfed6fda9fb4ff687ecffd9dfb37f64fec8fd8ffb1bf62fec4fd85fb07f607ebffd7dfaf7f5e7ebbfd75fae3f5bfeb6fd6bfad3f59feb2fd63fac3f57feaefd5bfab3f)) else (if page < 5 then (if page < 4 then 0xb5ff6afed3fda3fb3ff66fecbfd8ffb17f5afeb3fd63fabff55fea7fd4bfa8ff50fe9ffd3bfa6ff4cfe97fd2bfa4ff46fe89fd0ffa17f41fe7ffcfbf9eff3cfe77fcebf9cff38fe6ffcdbf9aff34fe67fccbf98ff30fe5dfcb7f8eff1cfe37fc6bf8cff18fe2ffc5bf8aff14fe27fc27f847f07fe0dfc17f else 0x8d7f7f7f7f3f7eff7ebf7e7f7e3f7dff7dbf7d3f7c3f7bff7b3f7aff7abf7a7f79ff79bf78ff78bf787f783f77bf777f773f76ff76bf6fbf6ebf6e3f6dbf6d7f6cff6c7f6c3f6bff6bbf6b7f6b3f6aff6a7f6a3f69ff693f68ff687f67ff63bf633f617f613f607f603f5fff5fbf5eff5e3f5dbf5d7f5cff5c7f5bbf5b7f5b3f) else (if page < 6 then 0xad7fad3facffacbfac7fac3faaffaa3fa9ffa9bfa97fa8bfa87fa83fa7ffa7bfa77fa73fa67fa63fa57fa53fa4ffa4bfa47fa43fa3ffa37fa2ffa2bfa1ffa1bfa13fa0bf9fff9d7f9c3f9bff9bbf9a7f9a3f99ff99bf997f993f987f97ff97bf977f96ff96bf967f95ff957f953f947f943f93bf933f90bf8f7f8ebf8e7f8dbf else 0x834427c60109f11c427de30efe6a83bf99d0efeb303b7ec90edfb003b7ebd0edfaf03b7eac0edf9b03b7e6b0eef94c3b7e4b0edf8cc3b7dd20edf7243bf5c60efd6343bf9880efe5e43bf9550efe4983bf9230efe3ec3b7cf50efb3a43becc90efe2543b7c5f0eef16c3b7c4f0edf1303b7c430edf90c367c470d9fb18317d910c7e4a0317ece0adfb102b7e430adf4b02b7c600adf11c2b7ece039f1800e7d82022f0ec087de351fc6a947f2344cb98d106e400b5ff002d5fc00b4ff002d2fc00b47f002d0fc00b3ff002b8fc00adbf))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x55480f929203730c80f894203722480dece1e6f5bc79fa5a1cf75bc73f92b1cf7b204f7df613df6444f7d4713df3dc4f7cc213df90c4e7e1e137ba544dbe88136fa144dbebb135f98c4d7e5c136f94c4d7de8136f6d04dbda2136f5e44df955137e4f44dbcfe136f39c4dec79136fb384b7eca12dfa904b7e7612df8d04b7dca12df71c4b7dc112df3dc4b7cef12df3484b7c6012df1344b7d47125f87847eec011dfaf8477eba11dfa58477e8911df7c8477db911df678477d7d11df55447f94511df138477d82112fb38427e43109f else 0x724c2f5c830af634c2f98b30be60cc2f97930be554c2f94d30be520c2f93230be4a8c2f92a30bb498c2f92530be48cc2f92130bb47cc2f91030bd434c2ed0c30bb42cc2ecfa30bb3d4c2ece930bb7fcb9ece02e7b8a4b2ed5d2cbe51cb2f9212cbb478b2fa252b3b7fcaced2a2b3b380aced4727bd3089eed4726be5bc94de432437a6c8fbdf623ef6088fbd4723ef3bc8fbcc223ef8788dee9a236fa308dbe4623776188dbd55237e3c88dbc9323777fc87ddf6207e5bc81f8c2207e7b480f9aa203eb00807e4720378b480ddc8202f) else (if page < 10 then 0x81ce7edc739fb704e7ed0f39fb3bce7ed47397b7fce2de21383b878e0ee14383b848e0eec1381f840e0ee0b383b828e0ee08383b81ce0ee06383b764e0edbb383b618e0bd5e383b574e0ed5c383b4c8e0ed06383b3e8e0ecf3383b3a8e0edff357b380d5edff333ea6cc9f96f327e574c9f95b327e51cc9f922327e994c3f9ff30fb608c3f95d30fe51cc3f92430fe980c2f9bd30be6f0c2f99c30be8c8c2ee2f30bb864c2ee1730bb84cc2eecc309fb04c27e7b30af9acc2be1030bb830c2ee0a30bb814c2ee0230bb800c2edff30bb else 0x8ed3dbd6f4f7e79537f65a4df78b132ee254cbb5bd32f9c3463d70118bdc345376fd14de3441bb8b106edc341bd70906f54741be4c906f9ff3fefb38febdfe3faf7fcfaed5d3ebbb2cf5eec83d7b8b0f5ee0d3d7b7d8f5ed913d7b574f5ed473d7b8d0f3ee0d3cfb7fcf3eeaf3caf7fcf2ed823caf8acefee1e3bfb868efee163bfbab8efbe8e3bef9ecefbe633bdf970efbe0f3bfb838efee043bfb808efee003bfb7fcefedbb3bfb654eff9863bef5e4eff9123bfd3e4efecf83bfb7fceaeece39fbaa8e7eea439fb9d8e7ee3439fb)) else (if page < 13 then (if page < 12 then 0x86d6feec55bdfb016f7e475bf79016fde2d5bf77616fddc85bef6596ff98d5bfe62d6ff9885bfe61d6ff9835bfe5f56ff9795bfea5568bd6f593e7fd56face557eabd55fa9b557e9d955fa65557e8ed55f982557e5bd55fa2c537e5bd4dfa2c523e5bd48fa3451fd8c547f62f51fd8b947f61f51fd78d47f5d551fd75147f5d051fdb31477ec251dfb01477e7b51ef9c947be5851ef83147ee0951ef80d47edaa51fd65947f98d51fe62947f98851fe5f147f97951fe5dd47f97651fe5c147f96151fe55547f947502fb393dbe934f6f else 0xa163bbe7d8eef9ea3bbe788eef91a3bdecc7d9fb01f67e7b7daf9c9f6bece7a2f8ede8bece6d2f8edb4bece68afb298dfac8637e8d18df9f6637e8b18bfac8623eabd86bea461af9b586be3b61af8d186bdf660fea5582f9f360be6a982f9a660be68182faae60afa8d82be8c60afa0d82be8160af9ed82be6c609f9ad82be4f60af8f982be3060af73182f5c860af65582f99460be63582fa3b5f6fb3979faaa5e7ea6d79fa765e7e8b179fa075e7e60979f9825dbe60970fa625bfe9696ff9b75bfe6a96ff99c5bfe6696ffa265bfb) else (if page < 14 then 0x8954730ba7fd4730ba70d4730bc7094730bc51d2a30ba51d0e30bc70d0b30b95750b30ba51d0b30ba51ce030ba478e030ba51cd230bc7d9472b3c8d1472b39b3991234f7d947237cb3a76200f8d1c120397d9471cfc90d82134f6096f136e7d947137c81ce0136b6456f11de7d94711fc6084d11cfb3aaf0ecfb39c70ecf8d1c10ef9b388d0ecf8ec600ecf1805c0ecfb38590ecf7d9470afc8d14730b8002738b3b002748abb002aa8a7b0022c887b0022c883b002ce87bb002af87bb002aa87bb0027687bb0027487bb0023b87bb0022c853b002aa84bb002ccb21f002cdb1df002ceb19f002cdb01f002c8b01f002ceafdf002ceaf9f0029b9eef002bb9d9f002c0995f002ce972f002ca972f002a4972f00276972f0027693ef0028c8eef else 0xb3a76994fb3a767d8fb3acd608fb39ca608fb3a765bcf989825bf6b39825beea55825bee8ed825beeb39f651fcabdf651fcaa9f651fca4df651fc9d9f651fc9d1f651fc969f651fc8edf651fc895f651fc81df651fc7fdf651fcb3a7651cf8d16f51fc7956f51fc9696f51f670d6f51fc7d9474f7c7d9474dfc7d9474cbc8d1474cb98d1c146398d1c1453970dc145358d1c141b981dff3fab81dff3beb7d9473bfc835ff38b3b3a76380fb3a07382b81dff38337d95d383a7fd5d38335bd5d383a7d947383c7fd5d327ab3a76308f7fd5d30ba8d14730bc7594730bc8d14730ba8b14730ba)))) else 0
  | 7 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x3cff3cbf3bff3abf39ff38bf383f367f357f327f30ff30bf2e7f2cbf2b3f28bf27bf26bf253f243f23ff237f22bf21ff207f203f1e7f1cff1abf197f177f15bf13ff13bf137f12ff11ff113f10bf0eff0dbf0c7f0aff087f07bf067f047f03bf023f01bf87bbb31fb01f9eef972f637e61af5e7e557e3d7b39fb23ef13df12df else 0x997f98bf983f973f96bf94bf93ff937f92bf927f91ff907f8fff8fbf8f3f8eff8e3f8dff7dbf7b7f7a3f78ff77ff777f6dff6d3f6cbf6b7f6abf697f68bf683f673f66ff66bf65bf637f62ff623f61ff61bf60ff60bf5f7f5e7f5dbf5cbf5c3f5bff5a3f593f557f537f523f51ff4f7f4dff4cbf463f453f41bf3fbf3ebf3d7f) else (if page < 3 then 0x51cc2f92030bb42cc2ece030bb90c8fbeaf2377b388dbe3b236f99480dd6f203e48880f9222037abc4f7eaf136fb384d7e76136f90c4d7d82136f2344dbc60135f9944b7ecd11df9d8477e4311f7644477c9211f7248477c4d11dfb383b7ec80edf90c3b7d910efe49c3bf9270edf1803b7c470edfb3a763df651fc002d6fc00b53f002cefc00adff002affc00abbf002adfc00aa7f0029bfc00a6bf00297fc00a57f00293fc00a33f00288fc00a17f00283fc00a03f0027efc009f7f0027bfc009ebf00278fc009dff00276fc009c7f else (if page < 4 then 0x13436fc3b0dbf5bc31fc470c7f0ec31fd470aff0ec2bfecb087f3bc21fc4d087fb2c1efce007bf11c1efecb067f30819fc3b067fb3411fc8d047f13411fecd03bf2000efc3b03bfb3808fc47023fb3806fc3b01bfb3acd7ecd9eefb3a767e65972fabe3bdeaf8eefb323b7e768eefabd8dfa9b60beb3982be9b60af8ed82be6d5e7e9956ffa655bf76096ffa3451fd7d947f56f51feabcf5eeaa3bfbb00ef7e153bdf81cefbdff3bfb994e7ee74383b81ce0edff3837574e0ecef383b758c2f63430bb8b0c2edff30bb708c2f55d30be else 0x51c47fcf711ff3bc47fce011ff30847fc9211ff23447fc8011ff18047fc5c11ff13447fe3b113f13444fc47113f7d842fece0effb343bfeca0effb203bfeaf0effa903bfe9b0eff9f43bfe790eff9d83bfe6d0eff9943bfe490eff9143bfe430eff8ec3bfe340eff7d83bfdcf0eff72c3bfdca0eff71c3bfdc30eff7043bfd910eff6083bfd6f0eff51c3bfd270eff4903bfd220eff4783bfcf70eff3bc3bfce00eff3483bfcc20eff2483bfc8d0eff2143bfc800eff1803bfc5c0eff1643bfc550eff1343bfc470eff0fc3bfd820dbf))) else (if page < 8 then (if page < 6 then 0x38080fcd2203f30880fc8d203f21480fd821e7f23479fc801e7f51c73fc801cff9d06afcef1abf2346afe74197f30865fc80197f9d85dfe7615bfabc4ffe9b13bfb384dfecd137fb204dfeaf137fa6c4dfe76137f9944dfe4a137f9104dfe43137f8ec4dfdf6137f6704dfd92137f6444dfd82137f5bc4dfd47137f3dc4dfcef137f3804dfcc2137f2484dfc8d137f2004dfc60137f9944bfece11ffb3447fec811ffabc47fe9b11ff9f847fe7711ff9d847fe6511ff90c47fe3b11ff7d847fd9b11ff64c47fd9111ff60847fd6f11ff else (if page < 7 then 0x380b2fcc22cbf51cacfcc22b3f8d0a2fcef28bf8d09efce027bf8d09afcc226bfb3894fe9b243f90c8ffece237fb348dfec8237faf48dfeaf237fa6c8dfe76237f9948dfe4b237f90c8dfe3b237f7d88dfda5237f6448dfd82237f5d08dfd6f237f51c8dfcf7237f3bc8dfce0237f3088dfc92237f9d88afc8d22bf7d887fe43207fb3880feaf203fa9080fe9b203fa0080fe76203f9b480fe65203f95880fe3b203f8d080fdf6203f74c80fdc7203f71480fdc3203f70480fd82203f5bc80fd47203f49080fd22203f47880fcef203f else 0x994e0fe3b383f8b0e0fe18383f81ce0fdff383f7d8e0fdb2383f608e0fd6f383f580e0fd5d383f51ce0fd0f383f438e0fcef383f8ecd9fcef367f380d9fdf6357f7fcc9fe0d30ffb38c2feaf30bfaa8c2fea430bfa6cc2fe8530bf9d8c2fe7430bf9b4c2fe6530bf934c2fe3b30bf8d0c2fe2c30bf890c2fe2330bf81cc2fdff30bf7d8c2fdd630bf71cc2fdc330bf708c2fdc130bf608c2fd6f30bf574c2fd4730bf490c2fd2230bf480c2fd0f30bf438c2fd0b30bf40cc2fcef30bf380c2fcd230bf608b9fcef2e7f308b9fd6f2cbf)) else (if page < 9 then 0x8ed47fe2c51ff89547fe0751ff7fd47fdf651ff60947fd6f51ff57547fd824f7f51d3dfd6f4dff51d37fd474cbf70518fdc1453f70506fdff3fbfb38fafeaf3d7fa6cf3fe0d3cbfb38effecd3bffb2ceffec83bffb00effeaf3bffaa8effe9b3bff9d8effe743bff994effe523bff90ceffe3b3bff8b0effe153bff834effe073bff804effdff3bff7d8effdb73bff644effd823bff5bceffd5f3bff574effd473bff444effd0f3bff3dceffe763abf3bceafe6539ff834e2fece383fabce0feaa383fa6ce0fe88383f9d8e0fe74383f else (if page < 10 then 0xa6df6fe767dbf9d1f6fe717dbf995f6fe3b7dbf8ddf6fe2c7dbf7d9e8fdf677ffb3996feaf637fa918bfece60bfb3582feca60bfb2182fec760bfabd82fea460bfa6d82fe7660bf9b582fe6560bf98982fe4360bf8ed82fe3460bf7d982fdee60bf72982fdc760bf64582fe765f7f6097dfe6d5e7fb396ffeaf5bffa916ffe9b5bffa556ffe765bff9b56ffe655bff8ed6ffe345bff7d96ffde55bff71d6ffdc35bff6096ffe3b5a3f60968fd6f5a3f8d164fece51ffabd47feaa51ffa6d47fe9351ff9d947fe7451ff99547fe5a51ff else 0x2d6b3bfb52cefed6abffb3aaffecdabffadeaffed4a6ffb3a9bfecda6ffb2a9bfec8a6ffade9bfeafa6ffaa69bfea4a6ffb367bfec89ebfb3a76feaf9dbfab676fe9b9dbfa5e76fece997fade65feaf997fa9265fe9b997f9da65fe71997f9b665fe65973fb3a47fe9b907fb3a3bfecd8effb323bfec88effabe3bfe9b8eff9da3bfe658eff9823bfe438eff9da38fe3b8e3fb39f6feaf7dbfaa9f6fea97dbf)))) else 0
  | 8 => if page < 1 then 0xb3bfabffa6ff9dbf997f8eff7dbf60bf5bff51ff3bff383f30bf237f203f137f11ff0eff else 0
  | 9 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 5 => if page < 1 then 0x17435 else 0
  | 6 => if page < 1 then 0x49124350d4350d4350d4350842107c1f0741f else 0
  | 7 => if page < 1 then 0x350d4350d4350d4350d43508421 else 0
  | 8 => if page < 1 then 0x21 else 0
  | 9 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 5 => 82
  | 6 => 947
  | 7 => 689
  | 8 => 18
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
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 6)

def bucketCount : ℕ → ℕ
  | 5 => 39
  | 6 => 399
  | 7 => 550
  | 8 => 20
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 5 => 145
  | 6 => 1434
  | 7 => 1982
  | 8 => 73
  | 9 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 5 => 5
  | 6 => 8
  | 7 => 7
  | 8 => 4
  | 9 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 5 => 11
  | 6 => 14
  | 7 => 14
  | 8 => 9
  | 9 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 5 => if page < 1 then 0x1c42980c363c023803208446014649fe03000270b80440400 else 0
  | 6 => if page < 7 then (if page < 3 then (if page < 1 then 0x507000d0501030d0302050200060d050a0300020200010305030105020b0008040c060202000007000001090000040501060c02000401020f2004000d051403 else (if page < 2 then 0x22d000901020402060000180004000f0002030508091d07080c06072b021000090c00000502011a1d060006001201000302030a03020009000a000607090100 else 0x4b040b09001c060403000103002302000309010700000326000300000024060003082e1037121215020004100911010003000201012b07000000060304092801)) else (if page < 5 then (if page < 4 then 0x2010100140000034b04001a0e1d06001d02010302000304030000010c0300001d0f7c0301000801002e1612000305040b1a073c091700050223000204000004 else 0x10001002b04162b1f1616003c02030a14035c000622040d0128010a000212131d0d240007000002000b010101130528010007000d1802000226161045020706) else (if page < 6 then 0xc1304090415040404070000000231180222080206052d05041c380a022c17000602270404040029030826190b389000322e004302020d0f161c001f0f1a else 0x3c0e0c0a43010b2e1501002b190000))) else 0
  | 7 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0xe18701001c00b083c8030604085160c181040020a181000202001810a247005824281020960020001160000002020c00400183004c24004 else 0x20c708220038706205801a0001a00c038306201800054f810408182085c0800000509000019400147000230008000040102042011e20083) else (if page < 3 then 0xc0858c0c5c081002c00514540830000084001400008095860204a12000409120a020900945840008f0d040c082000010214087861c00e85 else 0x6000820e0c080001c000020400c101400000000011c340071218910022848304640180010c161660000002030760440010e100820094004)) else (if page < 6 then (if page < 5 then 0x5800e02581811e14e85140c00a00007a62c0951d12242be16143910a004281e04005000c1810e08081540038d0000a0100005861a6c880 else 0x1208081e02010136000830a009ba0a0400802080ac0c000841a004833a14a000e0012f00014000600003be945800234084020cf000a00480) else (if page < 7 then 0x6670100045810e6228188563811b020021e0204400265c483006419c0800000004410790240802002f8e042d221001c0150460f003029284 else (if page < 8 then 0x41d9020c0c8000e166820228a8c14601a506cc02e0814002269411364e9300002c00402000028e0c5212814f0000140832cfc427008c015 else 0xfa0000190000a0300e41124a08087164c9a3d208000080410a00c000a041c204)))) else 0
  | 8 => if page < 1 then 0x5404d00a522f47100321 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 5 => if page < 3 then (if page < 1 then 0x2207a0802a1703300304009407c5e10f09f000170441600989982321210800400000144000370762b04522422652427818842cfe9d90003a5218b8901000819a8410069400d03d4001381cc2f40009600036030070491070 else (if page < 2 then 0x8c8d218a1d19914080005a000de1c40208f0000000322a0000788000e828258192500584004d01800000008058000000040000fa8000002a4508003c0943149100000001856a000640a41b41c09a3109a0878000785ac0d0 else 0x39054038058276033140c83d6014e80f902b5610c0001b0)) else 0
  | 6 => if page < 23 then (if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x1f42490b1c19611700ab097c32871cdb014a34208539e04f8df40591a0291e004d93728d600a3e5c01621f20000218a2f6e6d037acf80ed97d46278eb82ac096640009ec0000441c00025c20c808068f47f99a605262f5066040001141941be4a1d079800008b432f6e3040006fe6bba else 0xc8b640b88f5421a633d07e800b8a29c00000000000000ab20000000ab2085000025d85701cd0e0800000000cc6708318800016800000000000000039400000000c66466b34ba5c0000002acd43fdc000aa8a0b8a602cc43ae0af074863d0551b430a200d900182520e7c00808142d20) else (if page < 3 then 0x88d378822929f89742e78ddc08f2b2c5641000000000003a90003361ea808000002f210500901c9151bbd9c04709312c5538063c076c17a00e022f406021e800c2cb500037f4a4000004f421e03e9ab32a3876a000037e00645ea06f439508c40126eb433f0c48000000021a04bc0042 else (if page < 4 then 0x6582ec8e3c332657852a10001b1200000000000000c31965000027d6000211222c000000000006e400000003ac00288000e8200000304c9600026700540d7000000007c44000bdc00000000000e4c00003140000179ad708b63240754592100000009dc81d201433270003868aec3790 else 0x62800007fc84204a00230b662555499b74050826b5800f8d0a724ba83098e2100010208ec654a49013881d9b9f83c208e43d640005c12fa0004018141038a4000000077820712086630ab601a0998800000002f2ac9abb6990000018417900000000000247000015544e41b00ac13592))) else (if page < 8 then (if page < 6 then 0x7240b09ce8267852c11aa0986b1234c0272e1821c45c91d74dac03e0a58d7851cc21a4b920f605302a16e9407c064c2d68b0a64a041c09155cc3a605383600c4c095287c2eb8a4c121a19130d40000390b6696f03be1c1176872616005174a82725022157d00000db329e763026ca362 else (if page < 7 then 0xd0808e79be002050218100002e0a5360620000058333da5108d403d0e601cc1dc427802b41951194017278a2b66de825e25426b60e1c195079e27e4e8012c461c1301716280641aabb459c1a22da418600801bb0bf01e46c009034c6c3470bc42c44a0ca5d27502b622b929d909017f1 else 0xdee1cb00a8070034c77002cc1da0a6c10a8ac40e80cc57040121258955003c84f02f839d83800c5c6380b6280a16f85a42958ec840608d1168418b41242d01a081e34b102b902a175e041635a23f44000d3c2b94db42141e462698d5c9441a8c96617b00356cce99d0c001840e902a99)) else (if page < 9 then 0x8910000070f4196405d0000026a52592dd0000383000000007e4000000038e90002a81000000098a00009824f380002db4050454600015d095a4996b4c48f9dd58000aba589077c87223ae89a80003936d609ba57e8634a1e5b7602d02d21b71334acb49010a70a79967c2260335af00 else (if page < 10 then 0x77467a07181a70d841cf22a4185017c1ee283c04a236076604352bb8d742c6825410b077c0fc195ca8940c025b48585340a90f1c4848660bbfc974186c2360c9941b8aa0f441a7a7681c440786ba22991a210000372356200033608d9a860c3d80007ec30606f0010000016710001aa9 else 0x1d66d0602d02b03a900c4036ae6426105580572d409331e8c009026e0a1058009c4182554430062a04450a003d6000035839406402fb13e5d2b87e5a8b4970aa725ec2f6034432a7796a35ae2817e06948a513dc1b50b0ea7c2b303a1076171d1a8e0940bcc53708942cab8b82910)))) else (if page < 17 then (if page < 14 then (if page < 12 then 0x4f82098d140a29b68222adc90866dfc1f31390141893415f0b7d2812d72314346e84e0ec80f801b81b70b0403f0e2e32c9a1c02c126006a01462b024ee39e03ca9ce0d6cb4d1d182e6878dafd0054f0b897e2b2263c79b01282348afc25a08d900002742e13b542bb2cdc5a00c310dd0 else (if page < 13 then 0x6882c38b8131a019aa67251416989c0546874d7a809781dd043832e0af84b90bd26ad9d4c9ad043dd8306780e6015c272000000002008000a9e25b090938987d80c009000c32759e2428cc18a4b75000059816c0c6438487c822b80000b602192ed8a58273006a391000015110842da4 else 0xd2c349113a3152b3436c00b99f76cc5de10af425511b06af48f858d07b408d1ad40000ce431f50000000e142e29000362000000000001b202c91256db832d8366000032980002903af021000000000000b045d96000294015422525f04486af880002302650000281064e4c140002010)) else (if page < 15 then 0x1f80104000045184008800231d7c2579ae191c016c2c7404445287d034210000d209a4900900020405221aa23d0323414028a433de3f000037d47c0202000000009d03101174400024c3ab00000c162fd80081bc00006cc0000af034a05601a217dc1764424072035459a04593b10 else (if page < 16 then 0x580557416883306083882d284000bb8007074078c00380000d006c6a224c000904432948a800000039640003ac1000000021c40000000282000000067000000001c8a5b41ba097c62c13f864f0e9c0f28cb92ea80003214df9159600031e1cf216e47a00000030000082809f6765dd10 else 0x1fc3480cc0618192d30f40441b80e4212e06d839206382e00339ab305480216a48188000007e000000008700920000000000013113145af0b96000000000000000830c082c30b1472219b804c19b40e13b7c03b07f4dc407ac063000000001a06320700793291c4d920003720))) else (if page < 20 then (if page < 18 then 0x7da30aad6200003a41ef11582b4200020812fc1e082f61c30ec00670b0016100002660d48ad41461000032180000002be02984000deeac90818400000000d02e240006642af6c7c0292664705000015b435025c826853297f0000000020d630180005ad9201a108b1000000000000000 else (if page < 19 then 0xa869ae200000006b080008dab297b201a3071db150a9a425007a75523b611562180b50885b65013407561ed07603602390b8c98c448e943066c0000476b5189d41fe4a10000004d00000001977b7932b70494441ae825004fe34e058e5b403c639d064424452044aa007656a0d448000 else 0xc0d2230590136074d2b96310aa41addab403042d8880c2d104498000000373038e40b00002ca949d99705d594a007e00009c547a6a882950d708000315ab70abc016051c7350279b960962e150d1c40005944ec8a319a90000000001000006a0b0900001711000000000000008382b87)) else (if page < 21 then 0x54c00000002b00ba62b2047eb160b908000629aaa8000053090c37c01ac000044c400000000000001a40c39800031c80009f68000c1c4000000228008980009a028d8b39000000000000003381a2c2d302f066966b48745bbc0000dbc30889204bb8c2cac9408461904a43451bf81629 else (if page < 22 then 0xe7013a003c624684c0b79cec2cf0e74b4c0430349000000000002290d3400002680d006ac0000421e2202fa00001dd046012cc0009fe2408dec2e0872a5dc1c802858d6617700000a38e8823718c2a3680ac0058dd93277000217100039a08e813500904fb084025c05682ab83a8a460 else 0xcb10001e904b48de00000ee01c4781053c4df110c46d0ad5a5309b1a6949382a50a68a4500d00da1cdc1c10))))) else 0
  | 7 => if page < 31 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x4bc2811a1810e55c00d0081409e719ad67627013a108c18d649dd75930c92c678011a74995d7004011a02a406a47a606c478c8c508aca0a849818306cc4d709b51d02a5d98016289e1485011f443919244580bb15d8a0410e618262a80ab0618138440809662380492a6c18844991c50 else (if page < 2 then 0x3ac59e2695830600000000000000000000041499f234480005648000aac261274a8000000000093c0c700001ad4a08000057d91a604423f00fa55d040994345a521c2419d09050869731781221a600f023bc50c25c08a815501d7404e430449c1f80645880026411f5 else 0x10a65109ed13c05a441667808a018040a6194da6c000017604e040000191a54a4c0cd831d10126a415c6514041800018a33f4559056205e65e525408145f6457026a415969207fd12761f4000000000309dc148050521d982405877d81a3679e29007bc16b127184c86e101300000700)) else (if page < 5 then (if page < 4 then 0x17d8000579847043822b06284a3416657f2600aa97499c4a303c1976135a66042c553064511f00a818c45fd1e908410277a605be09f821b40001e517a5229076804e0898125046c239124596f0a541c922945dc24c125540000000984073915468217dca46068425140380b468b42122 else 0x57582422b4120600012070000000088800000000000001e509284000a9c8c728f01d609719dc04c15956682126686c0a717740a112592ad083e18e135820e17092a8179063907991127000137108e2220000000000012b40001181104a3300bc000065420f391540000000000) else (if page < 6 then 0x96d0220248000067440006640000000000086667b00c9143059d026038826343b1c0000121ff00644f384204ae696c0f102b8000000000009d1a2c0a08a6944b940000f619316102a40a0a0b111a414a068986160a41a01151a2c2828096115580003002886a6d1f7400029b64498000 else 0x1a1a59439441e028d5f2804045677a486b1944a4413f101b17b00e50020022aa806990234673660c4f11828a3c1000197430425809b823d093da5206bc06a6a7c202100000005162ad100029c17e41c0096053f173595005751df014d1de853800006c440008c5951155c8000a691582))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x9a498f100013a04b9d0712880d2281600007f0400074800001020cc00000000000000056807d60001e5273c08c183d0fa14789ab648024c428c1300620a7e24c1d95409017702bc29c09fa04287a19a215149c8008a12d004a54c01711cc0aa00c6158829740cc4c904d00e3083c0456 else 0x870247880c559848523f12ac51f2141d98516c1bd03e4aab600000000c00a5000849216e90fe09c91740588400067626223245306910000000000003e24000095080228d80000001a340000c20000000020e01514a800b076c5f42074000003924728e55ac17ae24542fa82b1a1d20f2) else (if page < 10 then 0x74c1aa07f520180000a609e1115177925004ed800031180009f6283000028404f2000000000009fc418100000000c425700001912a68000026c15b64ad800000007013d048818082400a58400073690b00001de01ec0860751a3828180f007660e310b80f6023400000c89fa8ab81bf0 else 0x57c165600021308c1800000000000002a505e4243832a226483e6780678544028dc00000000a18ee27f030a96e421c1810590000047802f60199cb06d400000002af063c13f8a58038080c09d100010d2000092221440009b1000097928c648940000001fd06399e364fca432a2c1551)) else (if page < 13 then (if page < 12 then 0x731a0c466065300000f2b3cc14368480077624919032200007984d51000000000000005f180007d40000674044600c800000001403a804b800023b06751e7082c1a7167c15d18401ca12404000aa80d4600010a415de0d09ec84f630202003529ab144800002bc5d1188c00e64549e8a else 0x7341f1499c0891629a4201e8121042d556807c0a004cc17803f1aa8535407996b82ab40001d549d422e977580006000000aa464c694d01909c451b400008a00001b0611c9c61abd9de20001e161691d9000000005e0688463922830001d8a36d2a46a242180145d7a0a3814464ee9531) else (if page < 14 then 0xa501a2439812270ec1ab49b423e800023408a0683889219535f825915ec84365080000a0c97105391a642d82a60aa41a2090a17d0844d39017c07f6802146093440007d023e2171801078ea9109282592000000038011124251f447f601609b58cc81f05930904a7024715d101dc0e10 else 0x2e4541685a079846000844740ac05601cca4f624d0674aaf43d013b173e0ec150422f67045ac07f80091115c00000013e10ec8ba089417c429c000054828187aa596093ca11134605056c853e076443f24254e8028566549f00c4a884db1048593e2a71a190531a6a12fd231748c06c6)))) else (if page < 23 then (if page < 19 then (if page < 17 then (if page < 16 then 0x41d44e41d017d23e8113053c4d84558271037c185045c22186290a172fc00003da1c9093d15644e00ca084d00000001dda7c89e969a98cf040d25e66c060c04280000a71573244022119e80cd0a3401a0744a2246ed9e2a00012e09c5cde09fc8348000269044080004ac90b7a2025d0 else 0x6d810975099f219a040860102740810013264824886d020e09c55b802b060525005ab0054168069100000b99f7134902758909ba06f0108000017b0940a2c89209ef2a5c87d407464f3a911ef837415363d891c732c1ca056847211b821d064426a07546068658569679811b262019b0) else (if page < 18 then 0x61da461799a6a793c66007f01fb017915b092580004259f707d89ce070c1f2429d935091a0d2004140009640410739149186ce63109421f13650000000115405201c000011010e068104d80307a5c414280d6b0069c10a646da1f3914865400006f077847e0166c3f067800008120251 else 0x6981311868000085827f5a302a11844836a300a0793d650307c055349a9590008e56a0a38676080498a00000206a3c13c256d088043045b4a711cd199192f141821b8254065059522e826813d229015628350000854663014a9758578269627de6802a85ee053108e188211c219d1155)) else (if page < 21 then (if page < 20 then 0x25468912a45a911ac238015861e015009d52f014812d5884109c65c433802f4000221250922d870c93f043c91c07900bc445844f01d80c6024c0b2041dc5a64389bf43905796a6467a28a24e701892800598172a3dc25319ea1e9a4ac18c076028a029d0cc991c21700d657f051c1c02 else 0x16506c0000034215c400000004a42a95000000036c40001398dc04540a100f2184479e80006c800002f6000000000003784000991c00085a40000000000000229349c48104a02a9634c07c0000272100013c123c247141866979dc638473c89f05144e9048822d29051fb140da5a6) else (if page < 22 then 0x272014d91969bc21b27799fd29a556e0a9c0a805b414060000000000000069e1a7200000007c41e2000027f46b41ff2880104087c866a55c0b708a441499c98b30898e4e2a5c2219465df750488232a88a4309bc4b0058018b23fd1f2000003424fa0000000000052c172880d0000 else 0x88e000000024103fd8fd09d5000027811a23f000008e526b065c18d000000907f8400000023f20000000275c00089840009e84585722194100000007cc1fe89b1800030a19c0000000045023608d09ca80002986a20694268c000000000008d8800034d0000a004000959a6408a62635))) else (if page < 27 then (if page < 25 then (if page < 24 then 0x32c80007c9400000000005584000a8c0fb054055917b400000001a51058400047c59d66e598c22504b906998000375067000003a99c9c210494400095480d21fc01112b9033005d00007a2000052198b03261000070400000023a0000000000023f8624000098c90e10a0000058c0000 else 0x34428705b00dd69c950f481896b00001dea00016a15a407117558b10000000000008b100000000001fa086e400036d80420000000aa50db076200008824000000033236197c10e20c302600e74684a70700029562d40db70300c400000d40000000000019e80001f540dc1eab6500382) else (if page < 26 then 0x13846060001602a299670000000000000009c140005cc0000351131079c46200000000851203200000000000db5a8817e28e4800000022704415c605385fb800001760b4000060d9c400001e38368252623d08f60959a18435229225813204ee12620001c64955800004ad6080000f29 else 0x23208f90bd061c04608000eb05984c3825c2480a48608004e04805542451930130112a59da0f08ee017028c44dc0ec5aa1c986a4c8f329d1266165980017a010d52081a80610800089028f100019874440ff04b105810f023500001e8400006178f200009881820874d81688895b1)) else (if page < 29 then (if page < 28 then 0x39d9c984ed208278428507a05d4014a23e0766816441c1024964d566041c32051105b600000004bd46d28d452d18a6400074021f499408a1000000000022a912080009f404022c040003e41d4400009111d42110000064a000000087451a44f4000000028c112040000000c8018d08b0 else 0x12c94d06c1101071c11d2445d386054a4b09b085012d00e21ab001706844334728914756894e60481dc831e298489e6210a71dad6604988646956e668099267ae9065271157896d9e2863825a078c22802742a3243c2656601040078d13b069424508451274175813157d06040002571) else (if page < 30 then 0x84c4a2100025a100007802f82550000035b00012f759461331751d260002756048400044d862697800005ce00004b889847a0a5a42e025f06800058424957151c5050691a5967b4670067e1db0000196487200004300000a7803680001a4000000000000a3143415a85f90000 else 0x5241f008dd05f4584156a9994ed0a551c547e10204a785bb7544237095918036dda15036426020b017c075421f050114f04eca188a69a9d0579111670414847f885444b021247d2195295827349e4287649d524000019a07081861a2914003659601000195100024e00002667))))) else 0
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


def goalColumns : Nat := 0xfe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000fe80fe00fe008000
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xc0c0c0c0c0c0c0c0 0xdf69e65d61c6ffebee7de3ce 4 6
    pinBase [0x0,0xc0c0c0c0c0c0c0c0,0x8080808080808080,0xc0c0c0c0c0c0c0c0,0xc0c0c0c0c0c0c0c0,0xc000c000c000c000,0xc0c00000c0c00000,0xc0c0c0c000000000,0x4040404040404040,0x0,0x0,0xc000c000c000c0,0xc0c00000c0c0,0xc0c0c0c0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xa0a0a0a0a0a0a0a0 0xdf59e55d51c5ffdbed7dd3cd 4 6
    pinBase [0x0,0xa0a0a0a0a0a0a0a0,0xa0a0a0a0a0a0a0a0,0x8080808080808080,0xa0a0a0a0a0a0a0a0,0xa000a000a000a000,0xa0a00000a0a00000,0xa0a0a0a000000000,0x0,0x2020202020202020,0x0,0xa000a000a000a0,0xa0a00000a0a0,0xa0a0a0a0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0x8888888888888888 0xdf39e35d31c3ffbbeb7db3cb 4 6
    pinBase [0x0,0x8888888888888888,0x8888888888888888,0x8888888888888888,0x8080808080808080,0x8800880088008800,0x8888000088880000,0x8888888800000000,0x0,0x0,0x808080808080808,0x88008800880088,0x888800008888,0x88888888] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xffff000000000000 0xe39ebbf3dfbfc31cb3d35db7 4 6
    pinBase [0x0,0xffff000000000000,0xaaaa000000000000,0xcccc000000000000,0xf0f0000000000000,0xff00000000000000,0xffff000000000000,0xffff000000000000,0x5555000000000000,0x3333000000000000,0xf0f000000000000,0xff000000000000,0x0,0x0] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xff000000ff00 0xa29aabb2dbaf20928b30d38f 4 6
    pinBase [0x0,0xff000000ff00,0xaa000000aa00,0xcc000000cc00,0xf0000000f000,0xff000000ff00,0x0,0xff0000000000,0x550000005500,0x330000003300,0xf0000000f00,0x0,0xff000000ff00,0xff00] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 : CutCertificate target :=
  makeCutCertificate target Minor0.target 0xff00ff00 0x61969b71d79f20928b30d38f 4 6
    pinBase [0x0,0xff00ff00,0xaa00aa00,0xcc00cc00,0xf000f000,0xff00ff00,0xff000000,0x0,0x55005500,0x33003300,0xf000f00,0x0,0xff00,0xff00ff00] Minor0.raw Minor0.nonzero (@Minor0.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x55555555aaaaaaaa 0x9aedbe1cf5df92cd3c14d55d8aacba0cb4db828c38049459 5 7
    pinBase [0x0,0x55555555aaaaaaaa,0xaaaaaaaa,0x4444444488888888,0x50505050a0a0a0a0,0x55005500aa00aa00,0x55550000aaaa0000,0x5555555500000000,0x5555555500000000,0x1111111122222222,0x50505050a0a0a0a,0x55005500aa00aa,0x55550000aaaa,0xaaaaaaaa] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xf0f0f0ff0f0f0f0 0x8ebcfb1cf5df8aacba18e59e869c7914d55d828c3810c51c 5 7
    pinBase [0x0,0xf0f0f0ff0f0f0f0,0xa0a0a0aa0a0a0a0,0xc0c0c0cc0c0c0c0,0xf0f0f0f0,0xf000f00f000f000,0xf0f0000f0f00000,0xf0f0f0f00000000,0x505050550505050,0x303030330303030,0xf0f0f0f00000000,0xf000f00f000f0,0xf0f0000f0f0,0xf0f0f0f0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x5555aaaa5555aaaa 0x59edbe1cf9ef51cd3c14d96d49acba0cb8eb418c38049869 5 7
    pinBase [0x0,0x5555aaaa5555aaaa,0xaaaa0000aaaa,0x4444888844448888,0x5050a0a05050a0a0,0x5500aa005500aa00,0x5555000055550000,0x5555aaaa00000000,0x5555000055550000,0x1111222211112222,0x5050a0a05050a0a,0x5500aa005500aa,0xaaaa0000aaaa,0x5555aaaa] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut16 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0x3333cccc3333cccc 0x55dd7d1cf9ef51cd3c18e9ae459c790cb8eb418c3808a8aa 5 7
    pinBase [0x0,0x3333cccc3333cccc,0x2222888822228888,0xcccc0000cccc,0x3030c0c03030c0c0,0x3300cc003300cc00,0x3333000033330000,0x3333cccc00000000,0x1111444411114444,0x3333000033330000,0x3030c0c03030c0c,0x3300cc003300cc,0xcccc0000cccc,0x3333cccc] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut17 : CutCertificate target :=
  makeCutCertificate target Minor2.target 0xf0ff0f00f0ff0f0 0x4dbcfb1cf9ef49acba18e9ae459c7914d96d418c3810c92c 5 7
    pinBase [0x0,0xf0ff0f00f0ff0f0,0xa0aa0a00a0aa0a0,0xc0cc0c00c0cc0c0,0xf0f00000f0f0,0xf00f0000f00f000,0xf0f00000f0f0000,0xf0ff0f000000000,0x505505005055050,0x303303003033030,0xf0f00000f0f0000,0xf00f0000f00f0,0xf0f00000f0f0,0xf0ff0f0] Minor2.raw Minor2.nonzero (@Minor2.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xf0f0f0f0f0f0f0f0 0x31cb3c35db7d39ebbe3dfbff1149341559751969b61d79f7 5 7
    pinBase [0x0,0xf0f0f0f0f0f0f0f0,0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000,0x5050505050505050,0x3030303030303030,0x0,0xf000f000f000f0,0xf0f00000f0f0,0xf0f0f0f0] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut22 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xcccccccccccccccc 0x29aaba2dbafb39ebbe3dfbff0928b20d38f31969b61d79f7 5 7
    pinBase [0x0,0xcccccccccccccccc,0x8888888888888888,0xcccccccccccccccc,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000,0x4444444444444444,0x0,0xc0c0c0c0c0c0c0c,0xcc00cc00cc00cc,0xcccc0000cccc,0xcccccccc] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut23 : CutCertificate target :=
  makeCutCertificate target Minor8.target 0xaaaaaaaaaaaaaaaa 0x259a792dbafb35db7d3dfbff0518710d38f31559751d79f7 5 7
    pinBase [0x0,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0x8888888888888888,0xa0a0a0a0a0a0a0a0,0xaa00aa00aa00aa00,0xaaaa0000aaaa0000,0xaaaaaaaa00000000,0x0,0x2222222222222222,0xa0a0a0a0a0a0a0a,0xaa00aa00aa00aa,0xaaaa0000aaaa,0xaaaaaaaa] Minor8.raw Minor8.nonzero (@Minor8.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xffff0000ffff 0x8288698aa8eb92c96d9ae9ef00804908a0cb10c14d18e1cf 5 7
    pinBase [0x0,0xffff0000ffff,0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0x0,0xffff00000000,0x555500005555,0x333300003333,0xf0f00000f0f,0xff000000ff,0xffff0000ffff,0xffff] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut25 : CutCertificate target :=
  makeCutCertificate target Minor3.target 0xffffffff 0x41845949a4db51c55d59e5df00804908a0cb10c14d18e1cf 5 7
    pinBase [0x0,0xffffffff,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0x0,0x55555555,0x33333333,0xf0f0f0f,0xff00ff,0xffff,0xffffffff] Minor3.raw Minor3.nonzero (@Minor3.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut32 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xffffffff00000000 0xa29aabb2dbafe39ebbf3dfbf8218a39259a7c31cb3d35db7 5 7
    pinBase [0x0,0xffffffff00000000,0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000,0xffffffff00000000,0x5555555500000000,0x3333333300000000,0xf0f0f0f00000000,0xff00ff00000000,0xffff00000000,0x0] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut33 : CutCertificate target :=
  makeCutCertificate target Minor6.target 0xffff0000ffff0000 0x61969b71d79fe39ebbf3dfbf411493515597c31cb3d35db7 5 7
    pinBase [0x0,0xffff0000ffff0000,0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff0000ffff0000,0xffff000000000000,0x5555000055550000,0x3333000033330000,0xf0f00000f0f0000,0xff000000ff0000,0x0,0xffff0000] Minor6.raw Minor6.nonzero (@Minor6.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut34 : CutCertificate target :=
  makeCutCertificate target Minor7.target 0xff00ff00ff00ff00 0x3ce34c2ca2487de75c6da658beeb6caeaa68ffef7cefae78 5 7
    pinBase [0x0,0xff00ff00ff00ff00,0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff00ff00ff00ff00,0xff000000ff000000,0xff00ff0000000000,0x5500550055005500,0x3300330033003300,0xf000f000f000f00,0x0,0xff000000ff00,0xff00ff00] Minor7.raw Minor7.nonzero (@Minor7.lower)
    (covers := by decide +kernel) (pats := by decide +kernel)
    (stock := by decide +kernel) (goalEq := by decide +kernel)

def selectCut : Nat → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 13 => cut12
  | 15 => cut14
  | 16 => cut15
  | 17 => cut16
  | 18 => cut17
  | 22 => cut21
  | 23 => cut22
  | 24 => cut23
  | 25 => cut24
  | 26 => cut25
  | 33 => cut32
  | 34 => cut33
  | 35 => cut34
  | _ => cut0

def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 5 => if page < 2 then (if page < 1 then 0x1450000010000000000c1080080080000145041041041041000000104000104041040004104041104101005041046000 else 0x40001041000104145) else 0
  | 6 => if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x441041041041041040c41031041041020c30c3104101041101041101044101041041044104104041104104041104041 else (if page < 2 then 0x410410410410410410410410410441041001451460850c51451450830030c5141041041141041141041044104104101 else 0x40085145084084081041042041142041041141041041041041001085040181041041041141041041181041040040041)) else (if page < 5 then (if page < 4 then 0x1451851420820810c10c10c00c30c30430c30c00010050c00c50400c00c5041041140140141041041041041041040041 else 0x410410410410400010011401410850401410410810000421420421421420820031451440c41040c41030c21450000c0) else (if page < 6 then 0x820c41040420420420820820821031040c31040411021041041010810420820821431821450c3141142185004104101 else 0x441020821040841040c31840831021020c20821020821031040c21041041840c40c41041041020410420440c4104044))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x820850851430c31001001001001041041451451451401451451030c40830c2082084103004104104186104006104104 else 0x1001001041041041081042041041041041041041042041041041041144100100100004104100104040180082085083) else (if page < 10 then 0x41041041181041041002046045041082042041041041046082082082082082082081042041041040040040001041001 else 0x1430c3041081041041041041045145041042041042041041044144041041101102084082045041102041041045041141)) else (if page < 13 then (if page < 12 then 0x850851420c30050c21461431420400020020020810c10c10410410810410030400430010c10000c20410c2001043143 else 0x1041041000400451451451040000421030c40801020820841021041030c51021031031041410c50410c21450c2082082) else (if page < 14 then 0x410410410410410410411001420c41401460041040841041030410410410000400400411041040841041021430c5144 else 0x50041051451450000430010c00410400830c30c3041041041141046145041042042001041041)))) else 0
  | 7 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x59959659a5965806964165965968586596576984235966598586586995d842184f3cf6618615995996226175d6599858 else 0x6196188d66566618588996996565d85d85d85985985986186186218978a261a40d5e361a6105975d75d0000640019596) else (if page < 3 then 0x1659669965962361889965969965962169a69a6a184d68d6186a165784d65065a65041a6228965966a2861658659657 else (if page < 4 then 0x66102184084f5993d684f5a18596618e18618618616586596598906506576180175c0892596496616596596596596596 else 0x1a02301a8e36a36996615da69a34001886168062185a00062185a00000d61861861861a00001868001868001869a690))) else (if page < 8 then (if page < 6 then 0x8c06238d06630235966565a365989065a69965901965a64065969900069900069901961a69a8c08616a36a302185a023 else (if page < 7 then 0x5960165965965968506998c06596598d98d90190196630006630236595da0230188c08d88e30188c08e3018618618600 else 0x8e35965960160235960008d665659700f000580616016018580596596596616000596618598618580016616596416580)) else (if page < 9 then 0x1800001761861000000000000086240f6405805994996560160195965925960160190165800195995983c08d6016016 else (if page < 10 then 0x6000176005d85d78624590006106594190184006406100196194170230180008d88c0600023619400580000600000600 else 0x2186266389064001841941984d6596596406230180188d8850663640659663663659000017)))) else 0
  | 8 => if page < 1 then 0x0 else 0
  | 9 => if page < 1 then 0x0 else 0
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

theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 82 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 82 0 = true :=
  chunk5x0

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
theorem chunk6x896 : span (checked 6) 51 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 947 0 = true :=
  (@span_join (checked 6) 448 0 499 (@span_join (checked 6) 224 0 224 (@span_join (checked 6) 112 0 112 chunk6x0 chunk6x112) (@span_join (checked 6) 112 224 112 chunk6x224 chunk6x336)) (@span_join (checked 6) 224 448 275 (@span_join (checked 6) 112 448 112 chunk6x448 chunk6x560) (@span_join (checked 6) 112 672 163 chunk6x672 (@span_join (checked 6) 112 784 51 chunk6x784 chunk6x896))))

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
theorem chunk7x672 : span (checked 7) 17 672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 689 0 = true :=
  (@span_join (checked 7) 336 0 353 (@span_join (checked 7) 112 0 224 chunk7x0 (@span_join (checked 7) 112 112 112 chunk7x112 chunk7x224)) (@span_join (checked 7) 224 336 129 (@span_join (checked 7) 112 336 112 chunk7x336 chunk7x448) (@span_join (checked 7) 112 560 17 chunk7x560 chunk7x672)))

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

end PEqualNP.Outside.L_meta_12270_aux

open PEqualNP.Outside.L_meta_12270_aux

theorem PEqualNP.Outside.L_meta_12270 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
