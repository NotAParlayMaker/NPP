import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10920

namespace OneNot10920
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def original (x : Fin 7→Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def wires : List Gate := [⟨.or, [0, 1]⟩,⟨.or, [3, 4]⟩,⟨.or, [0, 6]⟩,⟨.or, [4, 6]⟩,⟨.or, [7, 2]⟩,⟨.or, [7, 3]⟩,⟨.and, [9, 8]⟩,⟨.and, [10, 11]⟩,⟨.and, [5, 12]⟩,⟨.or, [13, 14]⟩,⟨.or, [16, 15]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def witness : Circuit := ⟨wires,17⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem eleven : wires.length=11 ∧ (∀ g∈wires,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) := by
  constructor
  · rfl
  · intro g hg
    simp only [wires,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem witnessCorrect : ∀ x : Fin 7→Bool,witness.eval (List.ofFn x)=original x := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def monotone (gs : List Gate) := ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def fits (C : Circuit) := ∀ x : Fin 7→Bool,C.eval (List.ofFn x)=original x
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def oneNot (gs : List Gate) := (∀ g∈gs,(g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) ∧
  (∀ i j : Fin gs.length,(gs.get i).op=.not → (gs.get j).op=.not → i=j)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def Replacement (C : Circuit) := ∃ D : Circuit,monotone D.gates ∧ D.gates.length≤C.gates.length ∧ fits D
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem large (C : Circuit) (big : 11≤C.gates.length) : Replacement C :=
  ⟨witness,eleven.2,(eleven.1.le.trans big),witnessCorrect⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem noNot (C : Circuit) (legal : oneNot C.gates) (ok : fits C) (none : ∀ g∈C.gates,g.op≠.not) : Replacement C := by
  refine ⟨C,?_,le_rfl,ok⟩
  intro g hg
  obtain ⟨ops,len⟩ := legal.1 g hg
  exact ⟨ops.imp_right (fun x=>x.resolve_right (none g hg)),len⟩
end OneNot10920

namespace FreeAIG
abbrev Fn (α : Type*) := α → Bool
def neg {α} (f : Fn α) : Fn α := fun x => !(f x)
def meet {α} (a b : Fn α) : Fn α := fun x => a x && b x

inductive Avail {α : Type*} (S : Set (Fn α)) : Fn α → Prop where
  | src {f} : f∈S → Avail S f
  | const (b : Bool) : Avail S (fun _ => b)
  | neg {f} : Avail S f → Avail S (FreeAIG.neg f)

inductive Has {α : Type*} : Set (Fn α) → Nat → Fn α → Prop where
  | done {S k f} : Avail S f → Has S k f
  | step {S k a b f} : Avail S a → Avail S b → Has (insert (meet a b) S) k f → Has S (k+1) f

theorem Avail.lift {α : Type*} {S T : Set (Fn α)} (h : ∀g∈S,Avail T g) {f} (p : Avail S f) :
    Avail T f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Avail.extend {α : Type*} {S : Set (Fn α)} {a f} (p : Avail S f) :
    Avail (insert a S) f := p.lift (fun _ hs=>.src (Set.mem_insert_of_mem _ hs))

theorem Avail.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {f} (p : Avail S f) : Avail T (f∘φ) := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Has.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {k f} (p : Has S k f) : Has T k (f∘φ) := by
  induction p generalizing T with
  | done hp => exact .done (hp.map φ h)
  | @step S k a b f ha hb _ ih =>
    apply Has.step (ha.map φ h) (hb.map φ h)
    apply ih
    rintro g (rfl|hg)
    · exact .src (Set.mem_insert _ _)
    · exact (h g hg).extend

def Inputs {n} : Set (Fn (Fin n→Bool)) := {g | ∃ i : Fin n,g=fun x=>x i}

end FreeAIG

namespace FreeAIG
theorem meetFalseR {α} (a : Fn α) : meet a (fun _=>false)=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueR {α} (a : Fn α) : meet a (fun _=>true)=a := by funext x;simp [meet]
theorem meetFalseL {α} (b : Fn α) : meet (fun _=>false) b=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueL {α} (b : Fn α) : meet (fun _=>true) b=b := by funext x;simp [meet]

def Restricted {α} (φ : α→α) (f : Fn α) := f∘φ=f ∨ ∃ b : Bool, f∘φ=fun _=>b

theorem Avail.restricted {α : Type*} {φ : α→α} {S : Set (Fn α)}
    (h : ∀g∈S,Restricted φ g) {f} (p : Avail S f) : Restricted φ f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact Or.inl rfl
  | @neg g _ ih =>
    rcases ih with eq|⟨b,eq⟩
    · exact Or.inl (congrArg FreeAIG.neg eq)
    · exact Or.inr ⟨!b,congrArg FreeAIG.neg eq⟩

theorem Has.save {α : Type*} {S T : Set (Fn α)} (φ : α→α) (mapS : ∀g∈S,Avail T (g∘φ))
    (good : ∀g∈S,Restricted φ g) {k f} (p : Has S k f) (hn : ¬Restricted φ f) :
    ∃ t, t+1≤k ∧ Has T t (f∘φ) := by
  induction p generalizing T with
  | done hp => exact (hn (hp.restricted good)).elim
  | @step S k a b f ha hb tail ih =>
    have ma := ha.map φ mapS
    have mb := hb.map φ mapS
    have finish (cheap : Avail T ((meet a b)∘φ)) : ∃ t, t+1≤k+1 ∧ Has T t (f∘φ) := by
      refine ⟨k,le_rfl,tail.map φ ?_⟩
      rintro g (rfl|hg)
      · exact cheap
      · exact mapS g hg
    rcases ha.restricted good with ea|⟨ba,ea⟩
    · rcases hb.restricted good with eb|⟨bb,eb⟩
      · have join : (meet a b)∘φ=meet a b := congrArg₂ meet ea eb
        obtain ⟨t,ht,sm⟩ := ih (T:=insert (meet (a∘φ) (b∘φ)) T) (by
          rintro g (rfl|hg)
          · exact .src (Set.mem_insert _ _)
          · exact (mapS g hg).extend) (by
          rintro g (rfl|hg)
          · exact Or.inl join
          · exact good g hg) hn
        exact ⟨t+1,by omega,.step ma mb sm⟩
      · apply finish
        change Avail T (meet (a∘φ) (b∘φ))
        rw [eb]
        cases bb
        · rw [meetFalseR];exact .const false
        · rw [meetTrueR];exact ma
    · apply finish
      change Avail T (meet (a∘φ) (b∘φ))
      rw [ea]
      cases ba
      · rw [meetFalseL];exact .const false
      · rw [meetTrueL];exact mb

theorem fixSave {n} (f : Fn (Fin n→Bool)) (i : Fin n) (b : Bool)
    (dep : ∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∃ x x', f (Function.update x i b) ≠ f (Function.update x' i b))
    {k} (p : Has Inputs k f) :
    ∃ t, t+1≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ : (Fin n→Bool)→(Fin n→Bool) := fun x=>Function.update x i b
  have other {j : Fin n} (ne : j≠i) : ((fun x : Fin n→Bool=>x j)∘φ)=(fun x=>x j) := by
    funext x;simp [φ,ne]
  have same : ((fun x : Fin n→Bool=>x i)∘φ)=(fun _=>b) := by funext x;simp [φ]
  apply p.save φ
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j;rw [same];exact .const b
    · rw [other e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j; exact Or.inr ⟨b,same⟩
    · exact Or.inl (other e)
  · rintro (eq|⟨v,eq⟩)
    · obtain ⟨x,h⟩ := dep
      exact h (congrFun eq x)
    · obtain ⟨x,x',h⟩ := nc
      exact h ((congrFun eq x).trans (congrFun eq x').symm)
end FreeAIG

namespace FreeAIG
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def price : GateOp → Nat | .not => 0 | _ => 1
def binaryCount : List Gate → Nat
  | [] => 0
  | g::gs => price g.op + binaryCount gs

theorem leLength (gs : List Gate) : binaryCount gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem notDiscount {gs : List Gate} (h : ∃ g∈gs,g.op=.not) : binaryCount gs+1≤gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := h
    rcases List.mem_cons.mp hu with rfl|hg
    · simpa [binaryCount,op,price] using leLength gs
    · have hlt := ih ⟨u,hg,op⟩
      cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem Has.bump {α : Type*} {S : Set (Fn α)} {k f} (p : Has S k f) : Has S (k+1) f := by
  induction p with
  | done h => exact .done h
  | step a b _ ih => exact .step a b ih

def applied {α} (g : Gate) (state : List (Fn α)) : Fn α := fun x =>
  g.op.eval (g.inputs.map (fun i => (state.getD i (fun _=>false)) x))
def run {α} (gs : List Gate) (state : List (Fn α)) : List (Fn α) :=
  gs.foldl (fun s g=>s++[applied g s]) state

theorem availGet {α : Type*} {S : Set (Fn α)} {st : List (Fn α)} (hs : ∀f∈st,Avail S f)
    (i : Nat) : Avail S (st.getD i (fun _=>false)) := by
  by_cases h : i<st.length
  · rw [List.getD_eq_getElem _ _ h]; exact hs _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact .const false

theorem Has.same {α : Type*} {S T : Set (Fn α)} {k f} (p : Has S k f) (h : ∀g∈S,Avail T g) :
    Has T k f := p.map id h

theorem gateCost {α : Type*} {S : Set (Fn α)} (g : Gate) (st : List (Fn α))
    (old : ∀f∈st,Avail S f)
    (legal : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    {f k} (tail : ∀ T : Set (Fn α), (∀ a∈st,Avail T a) → Avail T (applied g st) → Has T k f) :
    Has S (price g.op + k) f := by
  have base (A : Avail S (applied g st)) : Has S k f := tail S old A
  have ext (a : Fn α) : ∀u∈st,Avail (insert a S) u := fun u hu=>(old u hu).extend
  obtain ⟨op,len⟩ := legal
  cases g with | mk opg ins =>
  change opg=.and ∨ opg=.or ∨ opg=.not at op
  change ins.length≤2 at len
  match ins,len with
  | [],_ =>
    have free := base (Avail.const (opg.eval []))
    rcases op with rfl|rfl|rfl <;> simp [price,Nat.add_comm] <;> first | exact free.bump | exact free
  | [i],_ =>
    let a := st.getD i (fun _=>false)
    have ha : Avail S a := availGet old i
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · have e : applied ⟨.or,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · simpa [price] using base ha.neg
  | [i,j],_ =>
    let a := st.getD i (fun _=>false)
    let b := st.getD j (fun _=>false)
    have ha : Avail S a := availGet old i
    have hb : Avail S b := availGet old j
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i,j]⟩ st=meet a b := by funext x;simp [applied,a,b,meet,GateOp.eval]
      have h := tail (insert (meet a b) S) (ext _) (e ▸ Avail.src (Set.mem_insert _ _))
      simpa [price,Nat.add_comm] using Has.step ha hb h
    · have e : applied ⟨.or,[i,j]⟩ st=neg (meet (neg a) (neg b)) := by
        funext x;simp [applied,a,b,meet,neg,GateOp.eval]
      have h := tail (insert (meet (neg a) (neg b)) S) (ext _)
        (e ▸ (Avail.src (Set.mem_insert _ _)).neg)
      simpa [price,Nat.add_comm] using Has.step ha.neg hb.neg h
    · simpa [price] using base ha.neg

theorem listAIG {α : Type*} (gs : List Gate) (legal : ∀g∈gs,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (st : List (Fn α)) (S : Set (Fn α)) (old : ∀f∈st,Avail S f) (o) :
    Has S (binaryCount gs) ((run gs st).getD o (fun _=>false)) := by
  induction gs generalizing st S with
  | nil => exact .done (availGet old o)
  | cons g gs ih =>
    apply gateCost g st old (legal g (by simp))
    intro T prev h
    apply ih (fun u hu=>legal u (by simp [hu])) (st++[applied g st]) T
    intro u hu
    rcases List.mem_append.mp hu with u0|u1
    · exact prev u u0
    · have eq := List.mem_singleton.mp u1;exact eq ▸ h

theorem mapRun {α} (gs : List Gate) (st : List (Fn α)) (x : α) :
    (run gs st).map (fun a=>a x) =
    gs.foldl (fun s g=>s++[g.op.eval (g.inputs.map (fun j=>s.getD j false))]) (st.map (fun a=>a x)) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [run,List.foldl_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_cancel_left_eq]
    congr 2
    unfold applied
    congr 1
    apply List.map_congr_left
    intro i _
    exact (List.getD_map st (fun _=>false) (n:=i) (fun a : Fn α=>a x)).symm

theorem circuitAIG {n} (C : Circuit) (legal : ∀g∈C.gates,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    Has Inputs (binaryCount C.gates) (fun x : Fin n→Bool=>C.eval (List.ofFn x)) := by
  let st : List (Fn (Fin n→Bool)) := List.ofFn (fun i x=>x i)
  have h := listAIG C.gates legal st Inputs (by
    intro f hf
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp hf
    exact .src ⟨i,eq.symm⟩) C.output
  convert h using 1
  funext x
  have hst : st.map (fun a=>a x)=List.ofFn x := by simp [st,List.map_ofFn,Function.comp_def]
  have eq := mapRun C.gates st x
  rw [hst] at eq
  change (C.wires (List.ofFn x)).getD C.output false=_
  rw [show C.wires (List.ofFn x)=(run C.gates st).map (fun a=>a x) from eq.symm]
  exact List.getD_map _ (fun _=>false) (n:=C.output) (fun a : Fn (Fin n→Bool)=>a x)

end FreeAIG

namespace OneNot10920
open FreeAIG PEqualNP.CircuitLowerBounds

def guard (x : Fin 5 → Bool) : Bool :=
  if x 1 then x 3 || x 4 || (x 0 && x 2)
  else x 0 || x 2 || (x 3 && x 4)

def fixedOne (x : Fin 7 → Bool) := original (Function.update x 1 false)
def sample (m : Nat) (i : Fin 7) := m.testBit i.val
def signedInput (x : Fin 5 → Bool) : Fin 7 → Bool := ![x 0,false,x 1,x 2,x 3,!(x 1),x 4]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
theorem signedCore {k : Nat} (h : Has Inputs k original) :
    ∃ t, t+1 ≤ k ∧ Has Inputs t guard := by
  have changes : original (Function.update (sample 18) 1 false) ≠ original (sample 18) := by decide +kernel
  have nc : original (Function.update (sample 0) 1 false) ≠ original (Function.update (sample 9) 1 false) := by decide +kernel
  obtain ⟨t,sz,hfixed⟩ := fixSave original 1 false ⟨sample 18,changes⟩ ⟨sample 0,sample 9,nc⟩ h
  have mp : ∀ f∈(@Inputs 7), Avail Inputs (f ∘ signedInput) := by
    rintro f ⟨i,rfl⟩
    fin_cases i
    · exact .src ⟨0,rfl⟩
    · exact .const false
    · exact .src ⟨1,rfl⟩
    · exact .src ⟨2,rfl⟩
    · exact .src ⟨3,rfl⟩
    · exact .neg (.src ⟨1,rfl⟩)
    · exact .src ⟨4,rfl⟩
  have small : Has Inputs t (fixedOne ∘ signedInput) := hfixed.map signedInput mp
  have eq : fixedOne ∘ signedInput = guard := funext (by decide +kernel)
  exact ⟨t,sz,eq ▸ small⟩

theorem sufficient (core : ∀ t,Has Inputs t guard → 9 ≤ t) (C : Circuit)
    (legal : ∀ g∈C.gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (sem : fits C) : Replacement C := by
  by_cases contains : ∃ g∈C.gates,g.op=.not
  · have h := circuitAIG (n:=7) C legal
    rw [funext sem] at h
    obtain ⟨t,sz,small⟩ := signedCore h
    have bound := core t small
    have strict := notDiscount contains
    exact large C (by omega)
  · refine ⟨C,?_,le_rfl,sem⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h=>h.elim Or.inr (fun h=>(contains ⟨g,hg,h⟩).elim)),len⟩
end OneNot10920

namespace OneNot10920
open FreeAIG
abbrev Five := Fin 5 → Bool
abbrev Four := Fin 4 → Bool
def outer (i : Fin 5) : Prop := i ≠ 1
def assignment (m : Fin 32) (i : Fin 5) := m.val.testBit i.val

theorem witnessTable : ∀ i j : Fin 5, i≠j → ∀ b : Bool, ∃ m : Fin 32,
    guard (Function.update (Function.update (assignment m) j true) i b) ≠
    guard (Function.update (Function.update (assignment m) j false) i b) := by decide +kernel

theorem allCofactorDepend (i j : Fin 5) (different : i≠j) (b : Bool) :
    ∃ x : Five, guard (Function.update (Function.update x j true) i b) ≠
      guard (Function.update (Function.update x j false) i b) := by
  obtain ⟨m,h⟩ := witnessTable i j different b
  exact ⟨assignment m,h⟩

def permutation (v : Fin 5) : Fin 5 → Fin 5 :=
  if v=0 then ![4,1,3,2,0] else if v=2 then ![3,1,4,0,2] else if v=3 then ![0,1,2,4,3]
  else id
def phase (v i : Fin 5) : Bool := decide ((v=0 ∨ v=2) ∧ i=1)
def permuteInput (v : Fin 5) (x : Five) (i : Fin 5) : Bool :=
  if phase v i then !(x (permutation v i)) else x (permutation v i)

theorem permInverse : ∀ v i, permutation v (permutation v i)=i := by decide +kernel
theorem permSelected : ∀ v, outer v → permutation v v=4 ∧ phase v v=false := by
  unfold outer
  decide +kernel
theorem permLast : ∀ v, outer v → permutation v 4=v ∧ phase v 4=false := by
  unfold outer
  decide +kernel
theorem renamingKeepsGuard : ∀ v x, guard (permuteInput v x)=guard x := by decide +kernel
theorem renamingKeepsFix : ∀ v, outer v → ∀ b x,
    guard (Function.update (permuteInput v x) v b)=guard (Function.update x 4 b) := by
  unfold outer
  decide +kernel
theorem renamingAllowed (v : Fin 5) : ∀ f∈(@Inputs 5), Avail Inputs (f ∘ permuteInput v) := by
  rintro f ⟨i,rfl⟩
  cases h : phase v i
  · simpa [Function.comp_def,permuteInput,h] using
      (Avail.src (S:=Inputs) (f:=fun x : Five => x (permutation v i)) ⟨permutation v i,rfl⟩)
  · have eq : (fun x : Five => x i) ∘ permuteInput v = FreeAIG.neg (fun x : Five => x (permutation v i)) := by
      funext x
      simp [Function.comp_def,FreeAIG.neg,permuteInput,h]
    rw [eq]
    exact .neg (.src ⟨permutation v i,rfl⟩)

def insertLast (b : Bool) (x : Four) : Five := ![x 0,x 1,x 2,x 3,b]
def lowHalf (x : Four) := if x 1 then x 3 || (x 0 && x 2) else x 0 || x 2
def highHalf (x : Four) := x 0 || x 1 || x 2 || x 3
def tableRow (m : Fin 16) (i : Fin 4) := m.val.testBit i.val
theorem lowBranch : ∀ x, guard (insertLast false x)=lowHalf x := by decide +kernel
theorem highBranch : ∀ x, guard (insertLast true x)=highHalf x := by decide +kernel
theorem lowWord : ∀ m : Fin 16, lowHalf (tableRow m)=(0xfeb2 : Nat).testBit m.val := by decide +kernel
theorem highWord : ∀ m : Fin 16, highHalf (tableRow m)=(0xfffe : Nat).testBit m.val := by decide +kernel

end OneNot10920

namespace GuardPair
abbrev T := BitVec 16
abbrev P := T × T
def base : List P := [(43690,43690),(52428,52428),(61680,61680),(65280,65280)]
def z0 : T := 65202
def z1 : T := 65534
inductive Lit (s : List P) : P → Prop where
  | src {p} : p ∈ s → Lit s p
  | zero : Lit s (0,0)
  | neg {p} : Lit s p → Lit s (~~~p.1,~~~p.2)
  | clamp {p} : Lit s p → (b:Bool) → Lit s (p.1,if b then 65535 else 0)
inductive Run : Nat → List P → P → Prop where
  | done {s p} : Lit s p → Run 0 s p
  | step {k s a b p} : Lit s a → Lit s b → Run k ((a.1 &&& b.1,a.2 &&& b.2)::s) p → Run (k+1) s p
end GuardPair

namespace Wide
open GuardPair (P T)
inductive Lit (s : List P) : P → Prop where
  | src {p} : p ∈ s → Lit s p
  | zero : Lit s (0,0)
  | neg {p} : Lit s p → Lit s (~~~p.1,~~~p.2)
  | clamp {p} : Lit s p → (b:Bool) → Lit s (p.1,if b then 65535 else 0)
  | clamp0 {p} : Lit s p → (b:Bool) → Lit s (if b then 65535 else 0,p.2)
inductive Run : Nat → List P → P → Prop where
  | done {s p} : Lit s p → Run 0 s p
  | step {k s a b p} : Lit s a → Lit s b → Run k ((a.1 &&& b.1,a.2 &&& b.2)::s) p → Run (k+1) s p
end Wide

namespace K4Core
abbrev T := BitVec 16
def tgt : T := 65256
def neg (x:T) := ~~~x
def sat (s:List T) : List T := 0 :: 65535 :: (s ++ s.map neg)
def combs (s:List T) := (sat s).flatMap fun a => (sat s).map fun b => a &&& b
inductive Reach : Nat → List T → T → Prop where
  | done {s z} : z∈sat s → Reach 0 s z
  | step {k s g z} : g∈combs s → Reach k (g::s) z → Reach (k+1) s z

theorem src {s t : List T} (h : ∀ x∈s, x∈t) {x} (hx : x∈sat s) : x∈sat t := by
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at hx ⊢
  rcases hx with h0|h1|h2|⟨y,hy,he⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl (h _ h2)))
  · exact Or.inr (Or.inr (Or.inr ⟨y,h y hy,he⟩))

theorem negmem {s : List T} {x} (h : x∈sat s) : neg x∈sat s := by
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at h ⊢
  rcases h with rfl|rfl|h|⟨y,hy,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr ⟨_,h,rfl⟩))
  · exact Or.inr (Or.inr (Or.inl (by simpa [neg] using hy)))

theorem ext {a:T} {s:List T} {x} (h : x∈sat (a::s)) : x∈sat s ∨ x=a ∨ x=neg a := by
  simpa [sat,List.mem_append, or_assoc, or_left_comm, or_comm] using h

theorem meetmem {s:List T} {a b} (ha:a∈sat s) (hb:b∈sat s) : a &&& b ∈ combs s := by
  exact List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

def fits (v p n : T) : Bool := v &&& p == p && v &&& n == 0

def clash (s : List T) (p n:T) : Bool :=
  let chosen := s.filter fun x => x &&& p == p
  chosen.any fun a => chosen.any fun b => a &&& b &&& n == 0

def one (s : List T) (p n:T) := clash s p n || clash s n p

def two (s : List T) (p n:T) : Bool :=
  let l := sat s
  l.any fun a => ((a &&& p == p) && one l p (a &&& n)) ||
                  ((a &&& n == n) && one l n (a &&& p))

theorem clash_of (s:List T) {a b p n:T} (ha:a∈s) (hb:b∈s)
    (hf:fits (a &&& b) p n=true) : clash s p n=true := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq] at hf
  have hpa : a &&& p = p := by
    calc
      a &&& p = a &&& (a &&& b &&& p) := congrArg (a &&& ·) hf.1.symm
      _ = (a &&& a) &&& b &&& p := by ac_rfl
      _ = p := by simpa using hf.1
  have hpb : b &&& p = p := by
    calc
      b &&& p = b &&& (a &&& b &&& p) := congrArg (b &&& ·) hf.1.symm
      _ = a &&& (b &&& b) &&& p := by ac_rfl
      _ = p := by simpa using hf.1
  simp only [clash,List.any_eq_true,List.mem_filter,beq_iff_eq]
  exact ⟨a,⟨ha,hpa⟩,b,⟨hb,hpb⟩,hf.2⟩

theorem neg_eq_all (x p:T) : neg x &&& p = p ↔ x &&& p = 0 := by
  constructor <;> intro h <;> ext i hi
  all_goals
    have hh := congrArg (fun z : T => z[i]) h
    simp [neg] at hh ⊢
    cases h₁:x[i] <;> cases h₂:p[i] <;> simp_all

theorem fits_neg_iff (a p n:T) : fits (neg a) p n=true ↔ fits a n p=true := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq,neg_eq_all]
  have h := neg_eq_all (neg a) n
  simp only [neg,BitVec.not_not] at h
  change (_ ∧ ~~~a &&& n = 0) ↔ _
  rw [←h, and_comm]

theorem fitMeet (a b p n:T) (hf:fits (a &&& b) p n=true) :
    a &&& p = p ∧ fits b p (a &&& n)=true := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq] at hf ⊢
  have f : ∀ u v:T, u &&& v &&& p = p → u &&& p=p := by
    intro u v hp
    calc
      u &&& p = u &&& (u &&& v &&& p) := congrArg (u &&& ·) hp.symm
      _ = (u &&& u) &&& v &&& p := by ac_rfl
      _ = p := by simpa using hp
  exact ⟨f a b hf.1, f b a (by rw [BitVec.and_comm b a]; exact hf.1),
    (by calc
          b &&& (a &&& n) = a &&& b &&& n := by ac_rfl
          _ = 0 := hf.2)⟩

theorem srcOne {s:List T} {z p n:T} (hz:z∈sat s) (hf:fits z p n=true) :
    one (sat s) p n=true := by
  unfold one
  rw [Bool.or_eq_true]
  apply Or.inl
  exact clash_of _ hz hz (by simpa using hf)

theorem newOne {s:List T} {g z p n:T} (hg:g∈combs s) (hz:z∈sat (g::s))
    (hf:fits z p n=true) : one (sat s) p n=true := by
  rcases ext hz with old|rfl|rfl
  · exact srcOne old hf
  all_goals
    obtain ⟨a,ha,hh⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
  · unfold one
    rw [Bool.or_eq_true]
    exact Or.inl (clash_of _ ha hb hf)
  · unfold one
    rw [Bool.or_eq_true]
    exact Or.inr (clash_of _ ha hb ((fits_neg_iff _ _ _).mp hf))

theorem fac {s:List T} {g x y:T} (hx:x∈sat (g::s)) (hy:y∈sat (g::s)) :
    ∃ a∈sat s, ∃ b∈sat (g::s), x &&& y=a &&& b := by
  rcases ext hx with h|p
  · exact ⟨x,h,y,hy,rfl⟩
  rcases ext hy with h|q
  · exact ⟨y,h,x,hx,BitVec.and_comm _ _⟩
  have hw : BitVec.allOnes 16 ∈ sat s := by simp [sat,show BitVec.allOnes 16 = 65535 by rfl]
  refine ⟨_,hw,x &&& y,?_,BitVec.allOnes_and.symm⟩
  rcases p with rfl|rfl <;> rcases q with rfl|rfl <;> simp [neg,sat,BitVec.and_comm]

theorem two_from {s:List T} {g x p n:T} (hg:g∈combs s) (hx:x∈sat (g::s))
    (h : fits x p n=true) : two s p n=true := by
  have hw : BitVec.allOnes 16 ∈ sat s := by simp [sat,show BitVec.allOnes 16 = 65535 by rfl]
  simp only [two,List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
  exact ⟨_,hw,Or.inl ⟨BitVec.allOnes_and,by change one (sat s) p (BitVec.allOnes 16 &&& n)=true; rw [BitVec.allOnes_and]; exact newOne hg hx h⟩⟩

theorem two_from_prod {s:List T} {g x y p n:T} (hg:g∈combs s)
    (hx:x∈sat (g::s)) (hy:y∈sat (g::s)) (h:fits (x &&& y) p n=true) :
    two s p n=true := by
  obtain ⟨a,ha,b,hb,e⟩ := fac hx hy
  rw [e] at h
  obtain ⟨hp,hf⟩ := fitMeet a b p n h
  simp only [two,List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
  exact ⟨a,ha,Or.inl ⟨hp,newOne hg hb hf⟩⟩

theorem two_swap {s:List T} {p n:T} : two s p n = two s n p := by
  simp only [two,Bool.or_comm]

theorem two_all {s:List T} {g h z p n:T} (hg:g∈combs s) (hh:h∈combs (g::s))
    (hz:z∈sat (h::g::s)) (hf:fits z p n=true) : two s p n=true := by
  rcases ext hz with old|rfl|rfl
  · exact two_from hg old hf
  all_goals
    obtain ⟨a,ha,ww⟩ := List.mem_flatMap.mp hh
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ww
  · exact two_from_prod hg ha hb hf
  · rw [two_swap]
    exact two_from_prod hg ha hb ((fits_neg_iff _ _ _).mp hf)
def pack {n:Nat} (f : Fin n→Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem pack_get {n:Nat} (f : Fin n→Bool) (i:Fin n) : (pack f)[i.val] = f i := by
  have h : (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i := by
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp
  exact h

def ren (π: Fin 16→Fin 16) (x:T) : T := pack fun i => x[(π i).val]

theorem ren_get (π) (x:T) (i:Nat) (hi:i<16) :
    (ren π x)[i] = x[(π ⟨i,hi⟩).val] := pack_get _ ⟨i,hi⟩

theorem ren_meet (π) (x y:T) : ren π (x &&& y) = ren π x &&& ren π y := by
  ext i hi
  simp only [ren_get,BitVec.getElem_and]

theorem ren_neg (π) (x:T) : ren π (neg x) = neg (ren π x) := by
  ext i hi
  simp only [ren_get,neg,BitVec.getElem_not]

theorem transfer {s t:List T} {k} {π : Fin 16→Fin 16}
    (h:∀ x∈sat s,ren π x∈sat t) {z} (hs:Reach k s z) : Reach k t (ren π z) := by
  induction hs generalizing t with
  | done hx => exact .done (h _ hx)
  | @step k s g z hg _ ih =>
    obtain ⟨a,ha,hh⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
    apply Reach.step (meetmem (h _ ha) (h _ hb))
    apply ih
    intro x hx
    rcases ext hx with old|rfl|rfl
    · exact src (fun v hv => List.mem_cons_of_mem _ hv) (h _ old)
    · rw [ren_meet]
      simp [sat]
    · rw [ren_neg,ren_meet]
      apply negmem
      simp [sat]
def finish (s:List T) : Bool := (combs s).any fun g => two (g::s) tgt (neg tgt)
theorem finishLower {s:List T} (h:finish s=false) : ¬Reach 3 s tgt := by
  intro hr
  cases hr with | step hg h1 =>
    cases h1 with | step hh h2 =>
      cases h2 with | step hi h3 =>
        cases h3 with | done hz =>
          have t := two_all hh hi hz (by decide : fits tgt tgt (neg tgt)=true)
          have f : finish s = true := List.any_eq_true.mpr ⟨_,hg,t⟩
          simp_all
end K4Core

namespace GuardInput
open OneNot10920 FreeAIG
open GuardPair (P T)
def raw (i : Fin 5) : Fn Five := fun x=>x i
def signed (i : Fin 5) (s : Bool) : Fn Five := if s then FreeAIG.neg (raw i) else raw i

theorem signs {a : Fn Five} (h : Avail Inputs a) :
    (∃b:Bool,a=fun _=>b) ∨ ∃i s,a=signed i s := by
  induction h with
  | src h => obtain ⟨i,rfl⟩ := h;exact Or.inr ⟨i,false,rfl⟩
  | const b => exact Or.inl ⟨b,rfl⟩
  | @neg f _ ih =>
    rcases ih with ⟨b,rfl⟩|⟨i,s,rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · refine Or.inr ⟨i,!s,?_⟩
      funext x;cases s <;> simp [signed,FreeAIG.neg]

theorem trivialLeft {a b : Fn Five} (ha : ∃c:Bool,a=fun _=>c) (hb : Avail Inputs b) :
    Avail Inputs (meet a b) := by
  obtain ⟨c,rfl⟩ := ha
  cases c
  · exact .const false
  · have e : meet (fun _=>true) b=b := by funext x;simp [meet]
    exact e ▸ hb

theorem trivialRight {a b : Fn Five} (ha : Avail Inputs a) (hb : ∃c:Bool,b=fun _=>c) :
    Avail Inputs (meet a b) := by
  have e : meet a b=meet b a := by funext x;simp [meet,Bool.and_comm]
  rw [e];exact trivialLeft hb ha

theorem trivialSame (i : Fin 5) (a b : Bool) : Avail Inputs (meet (signed i a) (signed i b)) := by
  have h : Avail Inputs (raw i) := .src ⟨i,rfl⟩
  have idem (f : Fn Five) : meet f f=f := by funext x;simp [meet]
  cases a <;> cases b <;> simp [signed,idem]
  · exact h
  · have eq : meet (raw i) (FreeAIG.neg (raw i)) = fun _=>false := by funext x;simp [meet,FreeAIG.neg]
    rw [eq];exact .const false
  · have eq : meet (FreeAIG.neg (raw i)) (raw i) = fun _=>false := by funext x;simp [meet,FreeAIG.neg]
    rw [eq];exact .const false
  · exact h.neg

def test (v : Fin 5) (b : Bool) (m : Fin 16) : Five := permuteInput v (insertLast b (tableRow m))
def mask (v : Fin 5) (b : Bool) (f : Fn Five) : T := K4Core.pack (fun m=>f (test v b m))
def pair (v : Fin 5) (f : Fn Five) : P := (mask v false f,mask v true f)
theorem maskNeg (v b f) : mask v b (FreeAIG.neg f) = ~~~mask v b f := by
  ext i hi
  rw [BitVec.getElem_not]
  change (K4Core.pack _)[(⟨i,hi⟩:Fin 16).val]=!(K4Core.pack _)[(⟨i,hi⟩:Fin 16).val]
  rw [K4Core.pack_get,K4Core.pack_get];rfl
theorem maskMeet (v b f g) : mask v b (FreeAIG.meet f g) = mask v b f &&& mask v b g := by
  ext i hi
  rw [BitVec.getElem_and]
  change (K4Core.pack _)[(⟨i,hi⟩:Fin 16).val]=
    ((K4Core.pack _)[(⟨i,hi⟩:Fin 16).val] && (K4Core.pack _)[(⟨i,hi⟩:Fin 16).val])
  rw [K4Core.pack_get,K4Core.pack_get,K4Core.pack_get];rfl

set_option maxRecDepth 12000 in
theorem packFalse : ∀v:Fin 5,pair v (fun _=>false)=(0,0) := by decide +kernel
set_option maxRecDepth 12000 in
theorem packTrue : ∀v:Fin 5,pair v (fun _=>true)=(65535,65535) := by decide +kernel
set_option maxRecDepth 12000 in
theorem packVar : ∀v:Fin 5,outer v→pair v (raw v)=(0,65535) := by unfold outer;decide +kernel
set_option maxRecDepth 12000 in
theorem packOther : ∀v:Fin 5,outer v→∀i:Fin 5,i≠v→pair v (raw i)∈GuardPair.base ∨
    (~~~(pair v (raw i)).1,~~~(pair v (raw i)).2)∈GuardPair.base := by unfold outer;decide +kernel
set_option maxRecDepth 12000 in
theorem packGuard : ∀v:Fin 5,outer v→pair v guard=(GuardPair.z0,GuardPair.z1) := by unfold outer;decide +kernel

def stable (v j : Fin 5) (b : Bool) (f : Fn Five) : Prop := ∀x : Five,
  f (Function.update (Function.update x v true) j b)=f (Function.update (Function.update x v false) j b)
theorem rawStable (v j i : Fin 5) (b : Bool) (h : i≠v) : stable v j b (raw i) := by
  intro x
  by_cases a : i=j <;> simp [raw,Function.update,a,h]

theorem signedDies (v j : Fin 5) (b c : Bool) : stable v j c (meet (signed v b) (signed j c)) := by
  intro x;cases c <;> simp [signed,raw,FreeAIG.neg,meet]

theorem swappedDies (v j : Fin 5) (b c : Bool) : stable v j c (meet (signed j c) (signed v b)) := by
  intro x;cases c <;> simp [signed,raw,FreeAIG.neg,meet]

theorem guardMoves (v j : Fin 5) (b : Bool) (ne : v≠j) : ¬stable v j b guard := by
  obtain ⟨x,h⟩ := allCofactorDepend j v ne.symm b
  exact fun g=>h (g x)
end GuardInput

namespace Wide
open GuardPair (P T)
open FreeAIG

theorem Lit.lift {s t : List P} (map : ∀w∈s,Lit t w) {p} (h : Lit s p) : Lit t p := by
  induction h with
  | src m => exact map _ m
  | zero => exact .zero
  | neg _ ih => exact .neg ih
  | clamp _ b ih => exact .clamp ih b
  | clamp0 _ b ih => exact .clamp0 ih b

theorem Lit.extend {s : List P} {p q} (h : Lit s p) : Lit (q::s) p :=
  h.lift (fun _ m=>.src (List.mem_cons_of_mem _ m))

theorem Run.lift {s t : List P} (map : ∀w∈s,Lit t w) {k p} (h : Run k s p) : Run k t p := by
  induction h generalizing t with
  | done h => exact .done (h.lift map)
  | step a b _ ih =>
    apply Run.step (a.lift map) (b.lift map)
    apply ih
    rintro w (hw : w∈_::_)
    rcases List.mem_cons.mp hw with rfl|m
    · exact .src List.mem_cons_self
    · exact (map _ m).extend

theorem Run.pad {s k p} (h : Run k s p) : Run (k+1) s p :=
  .step .zero .zero (h.lift (fun _ m=>.src (List.mem_cons_of_mem _ m)))
theorem Run.padTo {s k n p} (h : Run k s p) (le : k≤n) : Run n s p := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction d with | zero=>exact h | succ d ih=>exact ih.pad

def inverted (p : P) : P := (~~~p.1,~~~p.2)
def prod (p q : P) : P := (p.1 &&& q.1,p.2 &&& q.2)
def choiceWord : P := (0,65535)
theorem Lit.rawMeetL {s p} (hp : Lit s p) (u : P) (raw : u=choiceWord ∨ u=inverted choiceWord) :
    Lit s (prod u p) := by
  rcases raw with rfl|rfl
  · have e : prod choiceWord p = (0,p.2) := Prod.ext BitVec.zero_and BitVec.allOnes_and
    rw [e];exact hp.clamp0 false
  · have e : prod (inverted choiceWord) p = (p.1,0) := Prod.ext BitVec.allOnes_and BitVec.zero_and
    rw [e];exact hp.clamp false

theorem Lit.rawMeetR {s p} (hp : Lit s p) (u : P) (raw : u=choiceWord ∨ u=inverted choiceWord) :
    Lit s (prod p u) := by simpa only [prod,BitVec.and_comm] using hp.rawMeetL u raw

structure Encoding (α : Type*) where
  word : Fn α → P
  off : word (fun _=>false)=(0,0)
  on : word (fun _=>true)=(65535,65535)
  neg : ∀f,word (FreeAIG.neg f)=inverted (word f)
  meet : ∀f g,word (FreeAIG.meet f g)=prod (word f) (word g)

theorem available {α} (E : Encoding α) {S s} (map : ∀f∈S,Lit s (E.word f)) {f} (h : Avail S f) :
    Lit s (E.word f) := by
  induction h with
  | src h => exact map _ h
  | const b =>
    cases b
    · rw [E.off];exact .zero
    · rw [E.on];exact Lit.neg (.zero (s:=s))
  | neg _ ih => rw [E.neg];exact .neg ih

theorem run {α} (E : Encoding α) {S s} (map : ∀f∈S,Lit s (E.word f)) {k f} (h : Has S k f) :
    Run k s (E.word f) := by
  induction h generalizing s with
  | done h => exact (Run.done (available E map h)).padTo (Nat.zero_le _)
  | @step S k a b f ha hb _ ih =>
    apply Run.step (available E map ha) (available E map hb)
    apply ih
    rintro g (rfl|m)
    · rw [E.meet];exact .src List.mem_cons_self
    · exact (map g m).extend

def delta (e : P) := e=choiceWord ∨ e=inverted choiceWord

theorem deltaNeg {x} (d : delta x) : delta (inverted x) := by
  rcases d with rfl|rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

structure Stable {α} (good : Fn α→Prop) : Prop where
  const : ∀b,good (fun _=>b)
  neg : ∀f,good f → good (FreeAIG.neg f)
  meet : ∀f g,good f → good g → good (FreeAIG.meet f g)

theorem classify {α} (E : Encoding α) {good} (st : Stable good) {S}
    (all : ∀f∈S,good f ∨ delta (E.word f)) {f} (h : Avail S f) : good f ∨ delta (E.word f) := by
  induction h with
  | src m => exact all _ m
  | const b => exact Or.inl (st.const b)
  | neg _ ih =>
    rcases ih with g|d
    · exact Or.inl (st.neg _ g)
    · exact Or.inr (E.neg _ ▸ deltaNeg d)

theorem save {α} (E : Encoding α) {good} (st : Stable good) {S s}
    (map : ∀f∈S,Lit s (E.word f)) (all : ∀f∈S,good f ∨ delta (E.word f))
    {k f} (h : Has S k f) (bad : ¬good f) (notRaw : ¬delta (E.word f)) :
    ∃u,u+1≤k ∧ Run u s (E.word f) := by
  induction h generalizing s with
  | done ha => exact ((classify E st all ha).elim bad notRaw).elim
  | @step S k a b f ha hb tail ih =>
    have la := available E map ha
    have lb := available E map hb
    have cheap (h : Lit s (E.word (FreeAIG.meet a b))) : ∃u,u+1≤k+1 ∧ Run u s (E.word f) :=
      ⟨k,le_rfl,run E (S:=insert (meet a b) S) (by
        rintro g (rfl|m)
        · exact h
        · exact map g m) tail⟩
    rcases classify E st all ha with ga|da
    · rcases classify E st all hb with gb|db
      · obtain ⟨u,le,h⟩ := ih (s:=(prod (E.word a) (E.word b))::s) (by
          rintro g (rfl|m)
          · rw [E.meet];exact .src List.mem_cons_self
          · exact (map g m).extend) (by
            rintro g (rfl|m)
            · exact Or.inl (st.meet _ _ ga gb)
            · exact all g m) bad notRaw
        exact ⟨u+1,by omega,.step la lb h⟩
      · apply cheap;rw [E.meet];exact la.rawMeetR _ db
    · apply cheap;rw [E.meet];exact lb.rawMeetL _ da

end Wide

namespace GuardInput
open OneNot10920 FreeAIG
open GuardPair (P T)

def encoder (v : Fin 5) : Wide.Encoding Five where
  word := pair v
  off := packFalse v
  on := packTrue v
  neg f := Prod.ext (maskNeg v false f) (maskNeg v true f)
  meet f g := Prod.ext (maskMeet v false f g) (maskMeet v true f g)

theorem allRaw (v : Fin 5) (out : outer v) :
    ∀ f∈(@Inputs 5),Wide.Lit GuardPair.base (pair v f) := by
  rintro f ⟨i,rfl⟩
  change Wide.Lit _ (pair v (raw i))
  by_cases hi : i=v
  · subst i;rw [packVar v out];exact Wide.Lit.clamp (.zero) true
  · rcases packOther v out i hi with m|m
    · exact .src m
    · have h := Wide.Lit.neg (Wide.Lit.src m);simpa using h

theorem selected (v : Fin 5) (out : outer v) (b : Bool) : Wide.delta (pair v (signed v b)) := by
  cases b
  · exact Or.inl (packVar v out)
  · exact Or.inr (((encoder v).neg _).trans (congrArg Wide.inverted (packVar v out)))

theorem stableLaws (v j : Fin 5) (c : Bool) : Wide.Stable (stable v j c) := by
  refine ⟨fun b _=>rfl,fun f gf x=>congrArg Bool.not (gf x),?_⟩
  intro f g hf hg x
  exact congrArg₂ Bool.and (hf x) (hg x)

theorem remaining (v j : Fin 5) (out : outer v) (vj : v≠j) (c : Bool) (g : Fn Five)
    (cheap : Wide.Lit GuardPair.base (pair v g)) (dies : stable v j c g)
    {k} (tail : Has (insert g Inputs) k guard) :
    ∃ u, u+1≤k ∧ Wide.Run u GuardPair.base (GuardPair.z0,GuardPair.z1) := by
  have mp : ∀ f∈insert g Inputs,Wide.Lit GuardPair.base ((encoder v).word f) := by
    rintro f (rfl|h)
    · exact cheap
    · exact allRaw v out f h
  have rel : ∀f∈insert g Inputs,stable v j c f ∨ Wide.delta ((encoder v).word f) := by
    rintro f (rfl|⟨i,rfl⟩)
    · exact Or.inl dies
    · by_cases hi : i=v
      · subst i;exact Or.inr (selected v out false)
      · exact Or.inl (rawStable v j i c hi)
  obtain ⟨u,le,chain⟩ := Wide.save (encoder v) (stableLaws v j c) mp rel tail
    (guardMoves v j c vj) (by
      change ¬Wide.delta (pair v guard)
      rw [packGuard v out]
      unfold Wide.delta
      decide +kernel)
  exact ⟨u,le,(packGuard v out) ▸ chain⟩

theorem pairFromFirst {k m} {i j : Fin 5} {a b : Bool} (sz : m+1≤k) (ne : i≠j)
    (tail : Has (insert (meet (signed i a) (signed j b)) Inputs) m guard) :
    ∃ u,u+2≤k ∧ Wide.Run u GuardPair.base (GuardPair.z0,GuardPair.z1) := by
  have lit (v y : Fin 5) (o : outer v) (s : Bool) : Wide.Lit GuardPair.base (pair v (signed y s)) := by
    apply Wide.available (encoder v) (allRaw v o)
    have rawY : Avail Inputs (raw y) := .src ⟨y,rfl⟩
    cases s
    · exact rawY
    · exact rawY.neg
  by_cases h : outer i
  · have c : Wide.Lit GuardPair.base (pair i (meet (signed i a) (signed j b))) := by
      change Wide.Lit _ ((encoder i).word _)
      rw [(encoder i).meet]
      exact (lit i j h b).rawMeetL _ (selected i h a)
    obtain ⟨u,le,r⟩ := remaining i j h ne b _ c (signedDies i j a b) tail
    exact ⟨u,by omega,r⟩
  · have o : outer j := by unfold outer at h ⊢;omega
    have c : Wide.Lit GuardPair.base (pair j (meet (signed i a) (signed j b))) := by
      change Wide.Lit _ ((encoder j).word _)
      rw [(encoder j).meet]
      exact (lit j i o a).rawMeetR _ (selected j o b)
    obtain ⟨u,le,r⟩ := remaining j i o ne.symm a _ c (swappedDies j i b a) tail
    exact ⟨u,by omega,r⟩
end GuardInput

namespace GuardInput
open FreeAIG OneNot10920

private theorem guardNotLiteral : ¬Avail Inputs guard := by
  intro h
  rcases signs h with ⟨b,e⟩|⟨i,s,e⟩
  · have table : ∀ b : Bool, ∃ x : Five, guard x ≠ b := by decide +kernel
    obtain ⟨x,q⟩ := table b
    exact q (congrFun e x)
  · have table : ∀ i : Fin 5, ∀ s : Bool, ∃ x : Five, guard x ≠ signed i s x := by decide +kernel
    obtain ⟨x,q⟩ := table i s
    exact q (congrFun e x)

private theorem eraseCheap {k : Nat} {g : Fn Five} (hg : Avail Inputs g)
    (h : Has (insert g Inputs) k guard) : Has Inputs k guard := by
  apply h.map id
  rintro f (rfl|hf)
  · exact hg
  · exact .src hf

theorem firstRaw {k : Nat} (h : Has Inputs k guard) :
    ∃ (m : Nat) (i j : Fin 5) (si sj : Bool), m+1 ≤ k ∧ i≠j ∧
      Has (insert (meet (signed i si) (signed j sj)) Inputs) m guard := by
  induction k with
  | zero =>
    cases h with
    | done hav => exact (guardNotLiteral hav).elim
  | succ k ih =>
    cases h with
    | done hav => exact (guardNotLiteral hav).elim
    | @step _ _ a b _ ha hb tail =>
      have skip (hg : Avail Inputs (meet a b)) :
          ∃ (m : Nat) (i j : Fin 5) (si sj : Bool), m+1 ≤ k+1 ∧ i≠j ∧
            Has (insert (meet (signed i si) (signed j sj)) Inputs) m guard := by
        obtain ⟨m,i,j,x,y,sz,ne,endp⟩ := ih (eraseCheap hg tail)
        exact ⟨m,i,j,x,y,by omega,ne,endp⟩
      rcases signs ha with hc|⟨i,si,rfl⟩
      · exact skip (trivialLeft hc hb)
      rcases signs hb with hc|⟨j,sj,rfl⟩
      · exact skip (trivialRight ha hc)
      by_cases eq : i=j
      · subst j; exact skip (trivialSame i si sj)
      · exact ⟨k,i,j,si,sj,le_rfl,eq,tail⟩
end GuardInput

namespace Wide
open GuardPair (P T)
def ConstLow (p : P) : Prop := p.1=0 ∨ p.1=65535

theorem Lit.tightOrConst {s p} (h : Lit s p) : GuardPair.Lit s p ∨ ConstLow p := by
  induction h with
  | src hs => exact Or.inl (.src hs)
  | zero => exact Or.inl .zero
  | neg _ ih =>
    rcases ih with hp|hz
    · exact Or.inl (.neg hp)
    · right
      rcases hz with z|z
      · exact Or.inr (by change ~~~_ = _; rw [z]; rfl)
      · exact Or.inl (by change ~~~_ = _; rw [z]; rfl)
  | clamp _ b ih =>
    rcases ih with hp|hz
    · exact Or.inl (.clamp hp b)
    · exact Or.inr hz
  | clamp0 _ b _ =>
    cases b
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem firstSrc {s : List P} {p : P} (hs : p∈s) : p.1∈K4Core.sat (s.map Prod.fst) :=
  by simp only [K4Core.sat,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨p,hs,rfl⟩)))

theorem Lit.low {s p} (h : Lit s p) {pool : List T} (src : ∀ q ∈ s, q.1∈K4Core.sat pool) :
    p.1∈K4Core.sat pool := by
  induction h with
  | src hs => exact src _ hs
  | zero => exact List.mem_cons_self
  | neg _ ih => exact K4Core.negmem ih
  | clamp _ _ ih => exact ih
  | clamp0 _ b _ => cases b <;> simp [K4Core.sat]

theorem Run.low {k s p} (h : Run k s p) (pool : List T) (src : ∀ q∈s, q.1∈K4Core.sat pool) :
    K4Core.Reach k pool p.1 := by
  induction h generalizing pool with
  | done h => exact .done (h.low src)
  | @step k s a b p ha hb _ ih =>
    let g := a.1 &&& b.1
    refine K4Core.Reach.step (K4Core.meetmem (ha.low src) (hb.low src)) (ih (g::pool) ?_)
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hm
    · simp [K4Core.sat,g]
    · exact K4Core.src (fun _ hx=>List.mem_cons_of_mem _ hx) (src q hm)

private theorem deleteIfAvail {k : Nat} {s : List P} {a b p : P} (h : Run k ((a.1 &&& b.1,a.2 &&& b.2)::s) p)
    (hg : a.1 &&& b.1 ∈ K4Core.sat (s.map Prod.fst)) : K4Core.Reach k (s.map Prod.fst) p.1 := by
  apply h.low
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hm
  · exact hg
  · exact firstSrc hm

theorem Run.dichotomy {k s p} (h : Run k s p) :
    GuardPair.Run k s p ∨ ConstLow p ∨
    ∃ u, u < k ∧ K4Core.Reach u (s.map Prod.fst) p.1 := by
  induction h with
  | done hl =>
    rcases hl.tightOrConst with hn|hc
    · exact Or.inl (.done hn)
    · exact Or.inr (Or.inl hc)
  | @step k s a b p ha hb hr ih =>
    have alow := ha.low (fun _ hm=>firstSrc hm)
    have blow := hb.low (fun _ hm=>firstSrc hm)
    by_cases skips : a.1 &&& b.1 ∈ K4Core.sat (s.map Prod.fst)
    · exact Or.inr (Or.inr ⟨k,by omega,deleteIfAvail hr skips⟩)
    have notA : ¬ConstLow a := by
      rintro (z|z)
      · apply skips
        rw [z]
        change (0#16) &&& _ ∈ _
        rw [BitVec.zero_and]
        exact List.mem_cons_self
      · apply skips
        rw [z]
        change BitVec.allOnes 16 &&& _ ∈ _
        rwa [BitVec.allOnes_and]
    have notB : ¬ConstLow b := by
      rintro (z|z)
      · apply skips
        rw [z]
        change _ &&& (0#16) ∈ _
        rw [BitVec.and_zero]
        exact List.mem_cons_self
      · apply skips
        rw [z]
        change _ &&& BitVec.allOnes 16 ∈ _
        rwa [BitVec.and_allOnes]
    rcases ih with hn|hc|⟨u,hu,small⟩
    · exact Or.inl (.step (ha.tightOrConst.resolve_right notA) (hb.tightOrConst.resolve_right notB) hn)
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨u+1,by omega,.step (K4Core.meetmem alow blow) small⟩)

theorem narrowSix
    (lowSix : ∀ {u}, K4Core.Reach u [43690,52428,61680,65280] GuardPair.z0 → 6 ≤ u)
    (h : Run 6 GuardPair.base (GuardPair.z0,GuardPair.z1)) :
    GuardPair.Run 6 GuardPair.base (GuardPair.z0,GuardPair.z1) := by
  rcases h.dichotomy with hn|hc|⟨u,hu,small⟩
  · exact hn
  · have n : ¬ConstLow (GuardPair.z0,GuardPair.z1) := by unfold ConstLow; decide +kernel
    exact (n hc).elim
  · have n := lowSix small
    omega
end Wide

namespace OneNot10920
open FreeAIG

theorem wideSix {k} (h : Has Inputs k guard) (small : k≤8) :
    Wide.Run 6 GuardPair.base (GuardPair.z0,GuardPair.z1) := by
  obtain ⟨m,i,j,a,b,sz,ne,tail⟩ := GuardInput.firstRaw h
  obtain ⟨u,save,t⟩ := GuardInput.pairFromFirst sz ne tail
  exact t.padTo (by omega)

theorem coreFromPair
    (lowSix : ∀ {u}, K4Core.Reach u [43690,52428,61680,65280] GuardPair.z0 → 6 ≤ u)
    (imp : ¬GuardPair.Run 6 GuardPair.base (GuardPair.z0,GuardPair.z1))
    (k : Nat) (h : Has Inputs k guard) : 9 ≤ k := by
  by_contra! small
  exact imp (Wide.narrowSix lowSix (wideSix h (by omega)))

end OneNot10920

namespace K4Orbit
open K4Core
def stages3 : List (List T) := [
  [43690,52428,61680,65280],
  [170,43690,52428,61680,65280],
  [34952,43690,52428,61680,65280],
  [43690,52428,61166,61680,65280],
  [10,170,43690,52428,61680,65280],
  [10,43690,52428,61680,65280,65520],
  [136,170,43690,52428,61680,65280],
  [136,34952,43690,52428,61680,65280],
  [170,204,43690,52428,61680,65280],
  [170,2570,43690,52428,61680,65280],
  [170,3084,43690,52428,61680,65280],
  [170,3840,43690,52428,61680,65280],
  [170,21760,43690,52428,61680,65280],
  [170,34952,43690,52428,61680,65280],
  [170,43520,43690,52428,61680,65280],
  [170,43690,49344,52428,61680,65280],
  [170,43690,52224,52428,61680,65280],
  [170,43690,52292,52428,61680,65280],
  [170,43690,52428,52462,61680,65280],
  [170,43690,52428,61166,61680,65280],
  [170,43690,52428,61680,64764,65280],
  [170,43690,52428,61680,65280,65450],
  [170,43690,52428,61680,65280,65484],
  [238,43690,52428,61166,61680,65280],
  [2730,43690,52428,61440,61680,65280],
  [32896,34952,43690,52428,61680,65280],
  [34952,41120,43690,52428,61680,65280],
  [34952,43690,52428,61166,61680,65280],
  [34952,43690,52428,61440,61680,65280],
  [34952,43690,52428,61680,63736,65280],
  [34952,43690,52428,61680,64250,65280],
  [34952,43690,52428,61680,65280,65520],
  [43176,43690,52428,61680,64764,65280],
  [43690,52428,61166,61680,64250,65280],
  [43690,52428,61166,61680,65278,65280],
  [43690,52428,61166,61680,65280,65520],
  [2,10,170,43690,52428,61680,65280],
  [2,10,43690,52428,61680,65280,65520],
  [2,170,43690,52428,61680,64764,65280],
  [2,43690,52428,61680,64764,65280,65532],
  [8,10,170,43690,52428,61680,65280],
  [8,10,43690,52428,61680,65280,65520],
  [8,136,170,43690,52428,61680,65280],
  [8,136,34952,43690,52428,61680,65280],
  [8,170,3084,43690,52428,61680,65280],
  [8,34952,43690,52428,61680,65280,65520],
  [10,12,43690,52428,61680,65280,65520],
  [10,34,170,43690,52428,61680,65280],
  [10,136,170,43690,52428,61680,65280],
  [10,160,170,43690,52428,61680,65280],
  [10,170,204,43690,52428,61680,65280],
  [10,170,240,43690,52428,61680,65280],
  [10,170,2570,43690,52428,61680,65280],
  [10,170,3084,43690,52428,61680,65280],
  [10,170,3840,43690,52428,61680,65280],
  [10,170,8738,43690,52428,61680,65280],
  [10,170,12336,43690,52428,61680,65280],
  [10,170,13056,43690,52428,61680,65280],
  [10,170,17476,43690,52428,61680,65280],
  [10,170,20560,43690,52428,61680,65280],
  [10,170,21760,43690,52428,61680,65280],
  [10,170,34952,43690,52428,61680,65280],
  [10,170,41120,43690,52428,61680,65280],
  [10,170,43520,43690,52428,61680,65280],
  [10,170,43680,43690,52428,61680,65280],
  [10,170,43690,49344,52428,61680,65280],
  [10,170,43690,52224,52428,61680,65280],
  [10,170,43690,52292,52428,61680,65280],
  [10,170,43690,52420,52428,61680,65280],
  [10,170,43690,52428,52430,61680,65280],
  [10,170,43690,52428,52462,61680,65280],
  [10,170,43690,52428,61166,61680,65280],
  [10,170,43690,52428,61440,61680,65280],
  [10,170,43690,52428,61520,61680,65280],
  [10,170,43690,52428,61680,61690,65280],
  [10,170,43690,52428,61680,64250,65280],
  [10,170,43690,52428,61680,64764,65280],
  [10,170,43690,52428,61680,65280,65290],
  [10,170,43690,52428,61680,65280,65450],
  [10,170,43690,52428,61680,65280,65484],
  [10,170,43690,52428,61680,65280,65520],
  [10,204,43690,52428,61680,65280,65520],
  [10,240,43530,43690,52428,61680,65280],
  [10,240,43690,52428,61680,65280,65520],
  [10,250,43690,52428,61680,64250,65280],
  [10,8738,43690,52428,61680,65280,65520],
  [10,12336,43690,52428,61680,65280,65520],
  [10,13104,43690,52428,61680,65280,65520],
  [10,17476,43690,52428,61680,65280,65520],
  [10,20560,43690,52428,61680,65280,65520],
  [10,21840,43690,52428,61680,65280,65520],
  [10,34952,43690,52428,61680,65280,65520],
  [10,41120,43690,52428,61680,65280,65440],
  [10,41120,43690,52428,61680,65280,65520],
  [10,43680,43690,52428,61680,65280,65520],
  [10,43690,49344,52428,61680,65280,65520],
  [10,43690,52416,52428,61680,65280,65520],
  [10,43690,52420,52428,61680,65280,65520],
  [10,43690,52428,52430,61680,65280,65520],
  [10,43690,52428,61166,61680,65280,65520],
  [10,43690,52428,61440,61680,65280,65520],
  [10,43690,52428,61680,61690,65280,65520],
  [10,43690,52428,61680,64250,65280,65520],
  [10,43690,52428,61680,64764,65280,65520],
  [10,43690,52428,61680,65280,65520,65530],
  [10,43690,52428,61680,65280,65520,65532],
  [14,238,43690,52428,61166,61680,65280],
  [14,43690,52428,61166,61680,65280,65520],
  [42,170,43690,49344,52428,61680,65280],
  [42,10794,43690,49344,52428,61680,65280],
  [42,43690,49344,52428,61680,65280,65472],
  [128,136,170,43690,52428,61680,65280],
  [128,136,34952,43690,52428,61680,65280],
  [128,170,43690,49344,52428,61680,65280],
  [128,32896,34952,43690,52428,61680,65280],
  [136,160,170,43690,52428,61680,65280],
  [136,170,204,43690,52428,61680,65280],
  [136,170,240,43690,52428,61680,65280],
  [136,170,2570,43690,52428,61680,65280],
  [136,170,3084,43690,52428,61680,65280],
  [136,170,3840,43690,52428,61680,65280],
  [136,170,8738,43690,52428,61680,65280],
  [136,170,12336,43690,52428,61680,65280],
  [136,170,13056,43690,52428,61680,65280],
  [136,170,17476,43690,52428,61680,65280],
  [136,170,20560,43690,52428,61680,65280],
  [136,170,21760,43690,52428,61680,65280],
  [136,170,34952,43690,52428,61680,65280],
  [136,170,41120,43690,52428,61680,65280],
  [136,170,43520,43690,52428,61680,65280],
  [136,170,43554,43690,52428,61680,65280],
  [136,170,43690,49344,52428,61680,65280],
  [136,170,43690,52224,52428,61680,65280],
  [136,170,43690,52292,52428,61680,65280],
  [136,170,43690,52428,52462,61680,65280],
  [136,170,43690,52428,61166,61680,65280],
  [136,170,43690,52428,61440,61680,65280],
  [136,170,43690,52428,61520,61680,65280],
  [136,170,43690,52428,61552,61680,65280],
  [136,170,43690,52428,61680,61688,65280],
  [136,170,43690,52428,61680,61690,65280],
  [136,170,43690,52428,61680,64250,65280],
  [136,170,43690,52428,61680,64764,65280],
  [136,170,43690,52428,61680,65280,65416],
  [136,170,43690,52428,61680,65280,65450],
  [136,170,43690,52428,61680,65280,65484],
  [136,170,43690,52428,61680,65280,65520],
  [136,240,34952,43690,52428,61680,65280],
  [136,2056,34952,43690,52428,61680,65280],
  [136,2570,34952,43690,52428,61680,65280],
  [136,3840,34952,43690,52428,61680,65280],
  [136,8738,34952,43690,52428,61680,65280],
  [136,8738,43690,52428,61680,65280,65314],
  [136,8874,43690,52224,52428,61680,65280],
  [136,12336,34952,43690,52428,61680,65280],
  [136,13056,34952,43690,52428,61680,65280],
  [136,28784,34952,43690,52428,61680,65280],
  [136,30464,34952,43690,52428,61680,65280],
  [136,32896,34952,43690,52428,61680,65280],
  [136,34816,34952,43690,52428,61680,65280],
  [136,34952,41120,43690,52428,61680,65280],
  [136,34952,43520,43690,52428,61680,65280],
  [136,34952,43554,43690,52428,61680,65280],
  [136,34952,43690,52428,61166,61680,65280],
  [136,34952,43690,52428,61440,61680,65280],
  [136,34952,43690,52428,61552,61680,65280],
  [136,34952,43690,52428,61680,61688,65280],
  [136,34952,43690,52428,61680,63736,65280],
  [136,34952,43690,52428,61680,64250,65280],
  [136,34952,43690,52428,61680,65280,65416],
  [136,34952,43690,52428,61680,65280,65450],
  [136,34952,43690,52428,61680,65280,65520],
  [136,43656,43690,52428,61680,65280,65484],
  [138,170,12336,43690,52428,61680,65280],
  [138,12336,35466,43690,52428,61680,65280],
  [138,12336,43690,52428,61680,65280,65328],
  [168,170,43690,52428,61680,64764,65280],
  [168,252,43690,52428,61680,64764,65280],
  [168,43176,43690,52428,61680,64764,65280],
  [170,204,238,43690,52428,61680,65280],
  [170,204,240,43690,52428,61680,65280],
  [170,204,2570,43690,52428,61680,65280],
  [170,204,3840,43690,52428,61680,65280],
  [170,204,8738,43690,52428,61680,65280],
  [170,204,12336,43690,52428,61680,65280],
  [170,204,13056,43690,52428,61680,65280],
  [170,204,34952,43690,52428,61680,65280],
  [170,204,41120,43690,52428,61680,65280],
  [170,204,43520,43690,52428,61680,65280],
  [170,204,43554,43690,52428,61680,65280],
  [170,204,43690,43758,52428,61680,65280],
  [170,204,43690,52428,61166,61680,65280],
  [170,204,43690,52428,61440,61680,65280],
  [170,204,43690,52428,61488,61680,65280],
  [170,204,43690,52428,61680,61690,65280],
  [170,204,43690,52428,61680,64250,65280],
  [170,204,43690,52428,61680,65280,65450],
  [170,204,43690,52428,61680,65280,65520],
  [170,238,43690,52428,52462,61680,65280],
  [170,238,43690,52428,61166,61680,65280],
  [170,252,43690,52428,61680,64764,65280],
  [170,2570,2730,43690,52428,61680,65280],
  [170,2570,8738,43690,52428,61680,65280],
  [170,2570,12336,43690,52428,61680,65280],
  [170,2570,17476,43690,52428,61680,65280],
  [170,2570,20560,43690,52428,61680,65280],
  [170,2570,34952,43690,52428,61680,65280],
  [170,2570,41120,43690,52428,61680,65280],
  [170,2570,43690,49344,52428,61680,65280],
  [170,2570,43690,50372,52428,61680,65280],
  [170,2570,43690,52428,52462,61680,65280],
  [170,2570,43690,52428,61166,61680,65280],
  [170,2570,43690,52428,61440,61680,65280],
  [170,2570,43690,52428,61520,61680,65280],
  [170,2570,43690,52428,61680,61690,65280],
  [170,2570,43690,52428,61680,64250,65280],
  [170,2570,43690,52428,61680,64764,65280],
  [170,2570,43690,52428,61680,65280,65520],
  [170,2730,43690,52428,61440,61680,65280],
  [170,2730,43690,52428,61520,61680,65280],
  [170,3084,3246,43690,52428,61680,65280],
  [170,3084,12336,43690,52428,61680,65280],
  [170,3084,13056,43690,52428,61680,65280],
  [170,3084,34952,43690,52428,61680,65280],
  [170,3084,41120,43690,52428,61680,65280],
  [170,3084,41634,43690,52428,61680,65280],
  [170,3084,43520,43690,52428,61680,65280],
  [170,3084,43690,44718,52428,61680,65280],
  [170,3084,43690,52428,61166,61680,65280],
  [170,3084,43690,52428,61440,61680,65280],
  [170,3084,43690,52428,61520,61680,65280],
  [170,3084,43690,52428,61680,61690,65280],
  [170,3084,43690,52428,61680,64250,65280],
  [170,3084,43690,52428,61680,64764,65280],
  [170,3084,43690,52428,61680,65280,65520],
  [170,3086,43690,52428,52462,61680,65280],
  [170,3212,43690,52428,61520,61680,65280],
  [170,3276,43690,52428,61440,61680,65280],
  [170,3598,43690,52428,61166,61680,65280],
  [170,3840,4010,43690,52428,61680,65280],
  [170,3840,20560,43690,52428,61680,65280],
  [170,3840,34952,43690,52428,61680,65280],
  [170,3840,41120,43690,52428,61680,65280],
  [170,3840,41130,43690,52428,61680,65280],
  [170,3840,43520,43690,52428,61680,65280],
  [170,3840,43690,44970,52428,61680,65280],
  [170,3840,43690,49344,52428,61680,65280],
  [170,3840,43690,49356,52428,61680,65280],
  [170,3840,43690,52224,52428,61680,65280],
  [170,3840,43690,52292,52428,61680,65280],
  [170,3840,43690,52428,52462,61680,65280],
  [170,3840,43690,52428,53196,61680,65280],
  [170,3840,43690,52428,61166,61680,65280],
  [170,3840,43690,52428,61440,61680,65280],
  [170,3840,43690,52428,61520,61680,65280],
  [170,3840,43690,52428,61680,61690,65280],
  [170,3840,43690,52428,61680,64250,65280],
  [170,3840,43690,52428,61680,64764,65280],
  [170,3840,43690,52428,61680,65280,65450],
  [170,3840,43690,52428,61680,65280,65484],
  [170,3840,43690,52428,61680,65280,65520],
  [170,3850,43690,52428,61680,65280,65450],
  [170,3852,43690,52428,61680,65280,65484],
  [170,10794,43690,49344,52428,61680,65280],
  [170,16128,43690,49344,52428,61680,65280],
  [170,17612,43520,43690,52428,61680,65280],
  [170,19532,41120,43690,52428,61680,65280],
  [170,21588,43690,52428,61680,64764,65280],
  [170,21760,21930,43690,52428,61680,65280],
  [170,21760,34952,43690,52428,61680,65280],
  [170,21760,35020,43690,52428,61680,65280],
  [170,21760,43520,43690,52428,61680,65280],
  [170,21760,43690,49344,52428,61680,65280],
  [170,21760,43690,52428,52462,61680,65280],
  [170,21760,43690,52428,61166,61680,65280],
  [170,21760,43690,52428,61680,64764,65280],
  [170,21760,43690,52428,61680,65280,65450],
  [170,21828,43690,52428,61680,65280,65484],
  [170,24320,41120,43690,52428,61680,65280],
  [170,32896,34952,43690,52428,61680,65280],
  [170,32896,43690,49344,52428,61680,65280],
  [170,34816,34952,43690,52428,61680,65280],
  [170,34816,43520,43690,52428,61680,65280],
  [170,34816,43690,52224,52428,61680,65280],
  [170,34816,43690,52292,52428,61680,65280],
  [170,34952,34986,43690,52428,61680,65280],
  [170,34952,41120,43690,52428,61680,65280],
  [170,34952,43520,43690,52428,61680,65280],
  [170,34952,43690,49344,52428,61680,65280],
  [170,34952,43690,52224,52428,61680,65280],
  [170,34952,43690,52292,52428,61680,65280],
  [170,34952,43690,52428,52462,61680,65280],
  [170,34952,43690,52428,61166,61680,65280],
  [170,34952,43690,52428,61440,61680,65280],
  [170,34952,43690,52428,61520,61680,65280],
  [170,34952,43690,52428,61680,61690,65280],
  [170,34952,43690,52428,61680,63736,65280],
  [170,34952,43690,52428,61680,64250,65280],
  [170,34952,43690,52428,61680,64764,65280],
  [170,34952,43690,52428,61680,65280,65416],
  [170,34952,43690,52428,61680,65280,65450],
  [170,34952,43690,52428,61680,65280,65484],
  [170,34952,43690,52428,61680,65280,65520],
  [170,34986,43690,52428,52462,61680,65280],
  [170,43176,43690,52428,61680,64764,65280],
  [170,43520,43690,49344,52428,61680,65280],
  [170,43520,43690,52224,52428,61680,65280],
  [170,43520,43690,52292,52428,61680,65280],
  [170,43520,43690,52428,52462,61680,65280],
  [170,43520,43690,52428,61132,61680,65280],
  [170,43520,43690,52428,61166,61680,65280],
  [170,43520,43690,52428,61680,64764,65280],
  [170,43520,43690,52428,61680,65280,65450],
  [170,43520,43690,52428,61680,65280,65484],
  [170,43656,43690,52428,61680,65280,65484],
  [170,43690,49152,49344,52428,61680,65280],
  [170,43690,49152,52224,52428,61680,65280],
  [170,43690,49216,49344,52428,61680,65280],
  [170,43690,49216,52292,52428,61680,65280],
  [170,43690,49344,49386,52428,61680,65280],
  [170,43690,49344,52224,52428,61680,65280],
  [170,43690,49344,52292,52428,61680,65280],
  [170,43690,49344,52428,52462,61680,65280],
  [170,43690,49344,52428,60138,61680,65280],
  [170,43690,49344,52428,61166,61680,65280],
  [170,43690,49344,52428,61680,64764,65280],
  [170,43690,49344,52428,61680,65280,65450],
  [170,43690,49344,52428,61680,65280,65472],
  [170,43690,49344,52428,61680,65280,65484],
  [170,43690,49352,52428,61680,61690,65280],
  [170,43690,51400,52428,61680,64250,65280],
  [170,43690,52224,52292,52428,61680,65280],
  [170,43690,52224,52394,52428,61680,65280],
  [170,43690,52224,52428,52462,61680,65280],
  [170,43690,52224,52428,61098,61680,65280],
  [170,43690,52224,52428,61166,61680,65280],
  [170,43690,52224,52428,61440,61680,65280],
  [170,43690,52224,52428,61520,61680,65280],
  [170,43690,52224,52428,61680,61690,65280],
  [170,43690,52224,52428,61680,64250,65280],
  [170,43690,52224,52428,61680,64752,65280],
  [170,43690,52224,52428,61680,64764,65280],
  [170,43690,52224,52428,61680,65280,65450],
  [170,43690,52224,52428,61680,65280,65484],
  [170,43690,52224,52428,61680,65280,65520],
  [170,43690,52292,52428,52462,61680,65280],
  [170,43690,52292,52428,61166,61680,65280],
  [170,43690,52292,52428,61520,61680,65280],
  [170,43690,52292,52428,61680,61690,65280],
  [170,43690,52292,52428,61680,64250,65280],
  [170,43690,52292,52428,61680,64756,65280],
  [170,43690,52292,52428,61680,64764,65280],
  [170,43690,52292,52428,61680,65280,65348],
  [170,43690,52292,52428,61680,65280,65450],
  [170,43690,52292,52428,61680,65280,65484],
  [170,43690,52292,52428,61680,65280,65520],
  [170,43690,52360,52428,61680,65280,65450],
  [170,43690,52416,52428,61680,65280,65520],
  [170,43690,52428,52462,61166,61680,65280],
  [170,43690,52428,52462,61680,61690,65280],
  [170,43690,52428,52462,61680,64250,65280],
  [170,43690,52428,52462,61680,64764,65280],
  [170,43690,52428,52462,61680,64766,65280],
  [170,43690,52428,52462,61680,65280,65450],
  [170,43690,52428,52462,61680,65280,65484],
  [170,43690,52428,52462,61680,65280,65518],
  [170,43690,52428,52462,61680,65280,65520],
  [170,43690,52428,60928,61166,61680,65280],
  [170,43690,52428,60996,61166,61680,65280],
  [170,43690,52428,61166,61680,64250,65280],
  [170,43690,52428,61166,61680,64764,65280],
  [170,43690,52428,61166,61680,65278,65280],
  [170,43690,52428,61166,61680,65280,65450],
  [170,43690,52428,61166,61680,65280,65484],
  [170,43690,52428,61166,61680,65280,65518],
  [170,43690,52428,61166,61680,65280,65520],
  [170,43690,52428,61680,64512,64764,65280],
  [170,43690,52428,61680,64596,64764,65280],
  [170,43690,52428,61680,64764,64766,65280],
  [170,43690,52428,61680,64764,65278,65280],
  [170,43690,52428,61680,64764,65280,65450],
  [170,43690,52428,61680,64764,65280,65484],
  [170,43690,52428,61680,64764,65280,65532],
  [170,43690,52428,61680,65280,65348,65484],
  [170,43690,52428,61680,65280,65450,65484],
  [170,43690,52428,61680,65280,65450,65518],
  [170,43690,52428,61680,65280,65484,65518],
  [170,43690,52428,61680,65280,65484,65520],
  [170,43690,52428,61680,65280,65484,65532],
  [234,43690,49344,52428,60138,61680,65280],
  [238,3598,43690,52428,61166,61680,65280],
  [238,34952,43690,52428,61166,61680,65280],
  [238,41120,43690,52428,61166,61680,65280],
  [238,43520,43690,52428,61166,61680,65280],
  [238,43690,43758,52428,61166,61680,65280],
  [238,43690,52428,57568,61166,61680,65280],
  [238,43690,52428,60928,61166,61680,65280],
  [238,43690,52428,61166,61440,61680,65280],
  [238,43690,52428,61166,61456,61680,65280],
  [238,43690,52428,61166,61680,61694,65280],
  [238,43690,52428,61166,61680,64250,65280],
  [238,43690,52428,61166,61680,65278,65280],
  [238,43690,52428,61166,61680,65280,65450],
  [238,43690,52428,61166,61680,65280,65518],
  [238,43690,52428,61166,61680,65280,65520],
  [238,43690,52428,61680,65280,65450,65518],
  [254,43690,52428,61166,61680,65278,65280],
  [682,43690,52428,61680,64512,64764,65280],
  [2184,2730,43690,52428,61440,61680,65280],
  [2184,34952,43690,52428,61440,61680,65280],
  [2730,3276,43690,52428,61440,61680,65280],
  [2730,34952,43690,52428,61440,61680,65280],
  [2730,40960,41120,43690,52428,61680,65280],
  [2730,40960,43690,52428,61440,61680,65280],
  [2730,41120,43690,52428,61440,61680,65280],
  [2730,43690,49152,52428,61440,61680,65280],
  [2730,43690,49344,52428,61440,61680,65280],
  [2730,43690,50244,52428,61440,61680,65280],
  [2730,43690,52428,52974,61440,61680,65280],
  [2730,43690,52428,61166,61440,61680,65280],
  [2730,43690,52428,61440,61520,61680,65280],
  [2730,43690,52428,61440,61680,64170,65280],
  [2730,43690,52428,61440,61680,64250,65280],
  [2730,43690,52428,61440,61680,64716,65280],
  [2730,43690,52428,61440,61680,64764,65280],
  [2730,43690,52428,61440,61680,65280,65520],
  [2810,43690,52428,61440,61680,64250,65280],
  [3822,43690,52428,61166,61440,61680,65280],
  [4080,43690,52428,61440,61680,65280,65520],
  [10922,43690,49152,49344,52428,61680,65280],
  [32768,32896,34952,43690,52428,61680,65280],
  [32768,34952,43690,52428,61440,61680,65280],
  [32896,34816,34952,43690,52428,61680,65280],
  [32896,34952,41120,43690,52428,61680,65280],
  [32896,34952,43520,43690,52428,61680,65280],
  [32896,34952,43690,52428,61166,61680,65280],
  [32896,34952,43690,52428,61440,61680,65280],
  [32896,34952,43690,52428,61680,63736,65280],
  [32896,34952,43690,52428,61680,64250,65280],
  [32896,34952,43690,52428,61680,65280,65408],
  [32896,34952,43690,52428,61680,65280,65416],
  [32896,34952,43690,52428,61680,65280,65450],
  [32896,34952,43690,52428,61680,65280,65520],
  [34944,34952,43690,52428,61680,65280,65520],
  [34944,43680,43690,52428,61680,65280,65520],
  [34952,41120,43176,43690,52428,61680,65280],
  [34952,41120,43520,43690,52428,61680,65280],
  [34952,41120,43690,49344,52428,61680,65280],
  [34952,41120,43690,52224,52428,61680,65280],
  [34952,41120,43690,52428,60652,61680,65280],
  [34952,41120,43690,52428,61166,61680,65280],
  [34952,41120,43690,52428,61680,64764,65280],
  [34952,41120,43690,52428,61680,65280,65416],
  [34952,41120,43690,52428,61680,65280,65450],
  [34952,41120,43690,52428,61680,65280,65484],
  [34952,43176,43690,52428,61680,63736,65280],
  [34952,43176,43690,52428,61680,64764,65280],
  [34952,43680,43690,52428,61680,65280,65520],
  [34952,43690,52428,57568,61166,61680,65280],
  [34952,43690,52428,61166,61440,61680,65280],
  [34952,43690,52428,61166,61680,63736,65280],
  [34952,43690,52428,61166,61680,64250,65280],
  [34952,43690,52428,61166,61680,65278,65280],
  [34952,43690,52428,61166,61680,65280,65520],
  [34952,43690,52428,61440,61680,63624,65280],
  [34952,43690,52428,61440,61680,63736,65280],
  [34952,43690,52428,61440,61680,64250,65280],
  [34952,43690,52428,61568,61680,65280,65416],
  [34952,43690,52428,61600,61680,65280,65450],
  [34952,43690,52428,61680,63736,64250,65280],
  [34952,43690,52428,61680,63736,65280,65416],
  [34952,43690,52428,61680,63736,65280,65450],
  [34952,43690,52428,61680,63736,65280,65520],
  [34952,43690,52428,61680,63736,65280,65528],
  [34952,43690,52428,61680,64250,64764,65280],
  [34952,43690,52428,61680,64250,65278,65280],
  [34952,43690,52428,61680,64250,65280,65450],
  [34952,43690,52428,61680,64250,65280,65484],
  [34952,43690,52428,61680,64250,65280,65520],
  [34952,43690,52428,61680,64250,65280,65530],
  [34952,43690,52428,61680,65280,65520,65528],
  [34952,43690,52428,61680,65280,65520,65530],
  [43176,43690,52428,60652,61680,64764,65280],
  [43176,43690,52428,61166,61680,64764,65280],
  [43176,43690,52428,61680,64512,64764,65280],
  [43176,43690,52428,61680,64764,65278,65280],
  [43176,43690,52428,61680,64764,65280,65448],
  [43176,43690,52428,61680,64764,65280,65450],
  [43176,43690,52428,61680,64764,65280,65484],
  [43176,43690,52428,61680,64764,65280,65532],
  [43688,43690,52428,61680,64764,65280,65532],
  [43690,52428,60138,61166,61680,64250,65280],
  [43690,52428,61152,61166,61680,65280,65520],
  [43690,52428,61166,61680,64250,64764,65280],
  [43690,52428,61166,61680,64250,65278,65280],
  [43690,52428,61166,61680,64250,65280,65450],
  [43690,52428,61166,61680,64250,65280,65484],
  [43690,52428,61166,61680,64250,65280,65518],
  [43690,52428,61166,61680,65278,65280,65518],
  [43690,52428,61166,61680,65278,65280,65520],
  [43690,52428,61166,61680,65278,65280,65534],
  [43690,52428,61166,61680,65280,65520,65534]]
def permDigits : List Nat := [18364758544493064720,18364683486789906960,18355225778678027280,18336085189344794640,18355113192123290640,18336047660493215760,18297203519274627360,18297128461571469600,18152560703022715200,17863200012815733120,18152448116467978560,17863162483964154240,18282904370552071200,18263763781218838560,18147794320115196480,17858433629908214400,18119083436115347520,17848863335241598080,18282773019571545120,18263707487941470240,18147662969134670400,17858377336630846080,18119064671689558080,17848844570815808640]
def moves : List (List Nat) := [
  [0,65706,201392332,268501232,33622538,234949644,302059264,134292002,335622192,369177344,604062788,671174736,704730368,166024,67281056,100837888,43690,402833600,436390912,52428,257774,537063424,61680,67369722,402914556,65280,100925354,436469708,537133040],
  [65536,262154,67371042,393352,67502240,65706,524492,67633392,592394,658444,724736,67707426,67776560,67842816,604718148,671830096,808192,886920,68001952,961024,109226,1032384,1100800,1166404,117964,1232110,1306350,68218880,68284496,127216,68350202,68418298,1375484,130816,1441706,1507276,68616176],
  [131072,458888,852138,202178764,269418736,34015240,34408970,235736076,302976768,135143970,336605232,370160384,604914756,672157776,705713408,538472560,572028672,1671296,35227648,166024,1745056,35301888,174762,203079872,236637184,183500,1830638,1896448,192752,1964280,2030330,203357436,196352,35520392,35585962,236912588,2097136],
  [196608,1245354,202571980,1507566,269746416,34802186,236129292,35065358,303304448,537202704,570757376,135602722,336998448,370553600,605373508,672550992,706106624,1804424,69116064,102672896,240298,404668608,438225920,249036,270590176,304147968,257774,538963968,258288,2226938,203554044,2293502,261888,35782570,237109196,35848174,2359280],
  [262144,2359298,2621448,262154,3080226,3145864,3211424,262314,3277004,3342576,3410442,3476492,3542784,3613218,3682352,3748608,3818564,3887184,3953920,4032648,4104352,4172288,4237984,305834,4309184,4377600,4443204,4508868,314572,4574414,4639982,4714222,4780032,4845648,323824,4911354,4979450,5045500,327424,5111562,5177258,5242828,5308400],
  [327680,2424834,2686984,327690,3014668,5243050,5308620,5439728,38799882,38865932,38997760,5579298,5648432,39203584,5714736,5784644,5853264,39408896,5920080,5998728,6135968,39692800,6204064,371370,6275264,39832576,6343872,6409412,380108,6474958,6549230,6615040,389360,6680826,6748922,6814972,392960,40238858,40304554,40370124,393200,6881274,6946812],
  [393216,2752520,3145738,70320162,7274624,393352,7536800,393386,7602380,7667952,7735818,7801868,7868160,7938594,8007728,8073984,8143940,8212560,8279296,8358024,8429728,8497664,8563234,436906,8634560,8702976,8768580,445644,8834286,8908526,8974336,9039952,9105520,454896,9171192,9236730,9304826,9370876,458496,9437064,9502634,9568204,9633776],
  [458752,2818056,7340160,458888,8323242,209649868,9634032,9701384,9767434,211094540,9834240,9904674,10104880,10171136,211240004,211439696,211506432,10252400,10319616,10387584,10455040,493704,10526880,10594816,10660386,502442,211861696,211930112,211995716,511180,10743534,10809344,10874992,520432,10940664,11008248,11074298,212401404,524032,11141000,11206570,212533196,11272176],
  [524288,3276810,204603404,70451234,405995588,7602312,74776736,524458,410321088,524492,11731182,11796720,11864586,213191692,11931392,12001826,12070960,12137216,213337156,213405776,213472512,12224648,12296352,12364288,12429858,567978,12495598,213631168,213699584,213765188,576716,213830894,12578542,12644352,12709936,214036560,585968,12775674,214102268,12843770,214170876,589568,12910506,214237132,12976112],
  [589824,3407882,70713378,7733384,75038880,589994,11862220,79102192,104268290,41289736,108595712,592394,13175466,45419532,112660224,13247010,13316144,46871296,13386820,13455440,47011072,13535368,13607072,47163904,633514,13680832,13747396,47238144,47303748,642252,13815022,47369934,13889262,13955072,14020688,651504,14086394,47576320,14154490,14220540,655104,47644426,47710122,47775692,14286832],
  [655360,2883592,3473418,238354444,70778914,7798920,75104416,78446754,655530,213188812,79167728,439878660,242681864,45419018,444206080,447548420,658444,14421166,448270080,80421410,14495792,14562048,449528900,249450576,249386240,14649480,14721184,14787234,14854656,699050,14921390,249741504,249613312,249678916,707788,249810158,15003374,15069184,15134800,717040,15200506,250016512,15268602,15334652,720640,250085132,250216362,250150860,15400944],
  [720896,3538954,70844450,7864456,75169952,721066,11927756,79233264,305791744,507184384,310118912,112658954,511511552,448269324,724736,15667114,147530274,81670192,315372288,652100676,15749200,516773120,15829128,15900832,15966378,16034304,764586,16101290,16171200,16236748,16305152,16370756,773324,16436462,16502732,16576238,16642048,16707664,782576,16773370,16841466,16907516,786176,16973738,17039308,17104880],
  [786432,3932170,71041058,8257672,75366560,786602,213450956,280559856,708576512,46991882,249367564,516755200,775688448,147661346,350040112,583873280,712918016,649675844,780029952,750342224,808192,17585578,17664136,17729740,84779168,84844784,17803776,830122,17875136,722324480,722390084,838860,17943790,722591180,18018030,789442560,789508176,848112,85061882,789706224,85129978,18087164,851712,18153386,722665420,789774320],
  [851968,3997706,71172130,8323208,75497632,852138,12189900,79364336,43321352,13502986,14617612,15798016,80683554,81801264,82981632,619988036,687362128,17650944,84570224,85358336,18317440,18450432,886920,18712746,18784416,18852352,895658,18923712,18992128,19057732,904396,19123438,19197678,19263488,19329104,913648,19394810,19462392,19528442,19594492,917248,19660680,19726250,19791820,19857392],
  [917504,4128778,71237666,8454280,75563168,917674,12320972,79429872,110561792,47122954,14814220,15994624,177676800,147792418,81932336,83112704,620577860,17384652,687689808,84496624,17782016,18515968,18843784,85630976,85958816,961024,961194,20037824,20106240,20171844,969932,20237550,20311756,20377326,87224320,87289936,979184,87355642,87423728,87489274,20446460,982784,20512682,20578252,87687152],
  [983040,4259850,71368738,7077930,7405696,8585352,75694240,983210,412287168,213582028,280690928,13634058,249695244,16125696,80749090,17246762,350367792,83243776,17317632,613826624,619791428,686903376,17847552,18382976,18909320,86024352,20032000,1026730,20692992,20824128,1032384,20955370,21023744,21089348,1035468,21155054,21228266,21294830,88141824,88207440,1044720,88273146,88406778,21363964,1048320,21430186,21495744,21561292,88670192],
  [1048576,4325386,71827490,8650888,76021920,1048746,213647564,79692016,47188490,446303232,249564172,16256768,81011234,81404586,82128944,82653424,83702528,647709696,619856964,687231056,722294016,18581504,18974856,86352032,20097536,1092266,20758528,21020864,1100800,21744708,21810346,1101004,21875950,21950122,22015726,22081536,22147152,1110256,22212858,22280954,22346992,22412540,1113856,22478762,22544332,22609904],
  [1114112,4390922,71893026,408027204,8716424,76087456,1114282,213713100,281084144,47254026,447613956,249629708,16322304,81076770,81470122,82194480,82587824,83768064,619922500,687296592,722359552,18647040,19040392,86417568,20163072,1157802,20889664,21086400,21744640,1166404,1166540,22662382,22736622,89255936,22802512,1175792,22868218,22936314,23002356,23067900,1179392,23134020,23199658,23265228,23330800],
  [1179648,4587530,71958562,8781960,76284064,1179818,213778636,12976366,79823088,13765130,249760780,15404046,16387840,177742336,81142306,548352016,82260016,83833600,620053572,687558736,17913088,19105928,19892394,86483104,20228608,1223338,21151936,88719584,21875712,22662212,1232076,1232110,23523054,89321472,89976912,1241328,23589114,23657210,23723260,23788798,1244928,23855018,23920588,23986158,24051696],
  [1245184,4653066,72024098,8847496,76349600,1245354,12517580,13041902,79888624,13830666,14945292,15601166,16518912,542511120,576262400,81207842,82325552,83899136,620905540,688083024,17978624,19171464,86614176,20359680,1288874,21283008,22006784,22727748,1297612,23514350,88793312,24112640,24178244,1306350,89387008,90042448,1306864,90763514,24247034,24313084,24379134,1310464,24444842,24510412,24575982,24641520],
  [1310720,2490370,4980746,72089634,9306248,76415136,11534504,1310890,214106316,281215216,13107452,106234370,307757824,14158346,15272972,16846592,81273378,82391088,83964672,620512324,687624272,17519700,18044160,19564680,86679712,19966120,20425216,1354410,21348544,22400000,23055428,1363148,23710958,24309486,89518080,90173520,1372400,90829050,91421434,24706048,24771668,1375484,24837374,24903422,1376000,24969130,25034700,92143600,25100284],
  [1376256,5111818,72220706,408092740,475201616,9437320,76546208,1376426,12845260,79954160,47647242,250153996,16912128,17108746,148316706,350826544,84030208,84226850,621036612,688148560,18109696,19695752,86810784,20490752,1419946,21414080,22465536,23186500,23383176,1428684,23842030,24440558,89583616,90304592,90501280,1437936,90960122,91552506,24968444,1441536,1441706,25231308,25296878,92340208,92405754],
  [1441792,5177354,72351778,273743920,9502856,76677280,1441962,214171852,80019696,47712778,250088460,16977664,17174284,81338914,82456624,84161280,620774468,687951952,722621696,18175300,19761288,86941856,20556288,20621960,1485482,21545152,22531072,23252036,1494220,23907566,24506094,89714688,90435664,90566848,1503472,91156730,91749114,25033980,1507072,25165636,25231274,1507276,25362414,25427952,25493500],
  [1507328,6946830,72613922,408158276,13041834,214368460,280035552,1507566,281542896,49154570,250481676,25562638,319491840,542576656,576327936,151331362,352727088,387265280,621102148,688279632,722818304,25659528,25731232,25799168,1551018,25864942,227066048,227134464,1559756,227200238,25944288,26013184,1568494,26079232,26144784,1569008,26210558,26278650,227605756,26345214,1572608,26410922,227737548,26476526,26542064],
  [1572864,77136032,14287018,216858828,285802736,141361698,26740872,110692864,47843850,1575594,250416140,26873036,319360768,151462434,547106816,352989232,386544384,621298756,748507136,689328208,722883840,26970248,27107328,27173024,60729856,1616554,27246592,27312320,27378756,60869632,1625292,27447022,27520750,1634304,27586640,1634544,61142272,27654826,27720442,27786444,27852028,1638144,61276074,61407180,27918320],
  [1638400,7471232,10354824,18284714,219611340,286785776,43976712,51972618,253299724,322637568,152707618,127674922,354103344,389821184,622478404,463227980,689655888,725374208,563966064,597653248,330137344,28213248,1671296,28346368,1673352,28418208,28486144,1682090,229753024,229821440,1690828,28569326,28635136,1700080,28702968,28769018,230096124,1703680,28835712,28901256,28966826,230293452,29032432],
  [1703936,10485896,77594784,18743466,220201164,287310064,44107784,52365834,253824012,322965248,144777248,153035298,354496560,390083328,624051268,463359052,691163216,726684928,530603776,564031600,597718784,28409984,62031872,1738888,162701312,1745056,29206696,29272576,1747626,29343936,29412352,1756364,29486316,29552366,96530432,1765616,96598264,96664314,29621500,1769216,29687688,96796576,29753258,29818828,96927728],
  [1769472,10682504,19136682,220463308,25624814,289734896,44238856,52693514,254020620,59182606,323292928,543428624,576983296,154673698,358035504,391590656,624444484,693588048,727143680,564946534,564752496,598308608,28541056,62097408,1804424,29532320,63089152,1813162,230867136,264424448,1821900,30073056,63630848,1830638,30142464,1831152,30210296,30276346,231603452,30342910,1834752,63766408,63831978,265158604,63897582,30408688],
  [1835008,10748040,19202218,220528844,288424176,44304392,26806408,52759050,26938026,254086156,228265164,321982208,154214946,547631104,556085296,589640448,623985732,748965888,757420112,790975744,563703808,563834992,597391104,28278784,28606592,62162944,1869960,565485568,96510112,130066944,1878698,766820352,432062656,465619968,1887436,30142190,1896448,1896688,30472328,30537976,567409322,30604026,768736460,231931132,1900288,64094088,64159658,265486284,567017456],
  [1900544,10944648,19398826,220725452,289603824,293929208,106693122,442237956,309200640,44632072,53152266,254479372,323424000,154477090,357445680,391394048,624247876,692998224,726947072,564490352,598177536,28672128,62425088,1935496,96575648,29862056,63220224,1944234,432128192,231196872,264555520,1952972,30207726,30535680,1962224,64223232,1964280,30800634,232127740,1965824,30867336,30932906,232259532,30998512,31064056],
  [1966080,11010184,19464362,220856524,289669360,92799226,442303492,509543680,44697608,53217802,254610444,323489536,154542626,357511216,159986226,391459584,624510020,693522512,727209216,564555888,564818546,598243072,28737664,62490624,2001032,96641184,63285760,2009770,230932672,231262408,264686592,2018508,30273262,30601216,2027760,30800120,64289280,2030330,31128828,31194878,2031360,64487304,31260586,31326156,31391728,31457274],
  [2031616,2949128,5963786,207290380,11206792,19792042,221118668,289800432,44763144,53348874,254675980,323358464,154608162,357773360,391328512,562901808,624378948,693325904,726881536,764237136,564359280,597915392,564885360,28999808,62556160,29067392,2066568,96903328,130460160,29993632,2075306,432455872,466013184,231328960,2084044,30404334,567013376,2093296,30996728,31390458,232717564,2096896,64552840,64946090,266272716,2097136,31522808,31588346,232914940],
  [2097152,11665576,19923114,222953676,290062576,428540156,106824194,308282112,44828680,54135306,258214924,325390080,145498144,154804770,358887472,392508160,628048964,695160912,629953620,729306368,731338496,29919368,97034400,129804288,2140328,130656768,2140842,432718016,466930688,2149580,31649004,31715054,567603200,2158832,98760952,98827002,31783936,2161916,31850238,2162432,31915944,31981482,32047052,99155952,32112636],
  [2162688,24182954,225575116,26214638,292684016,93323514,442893316,510067968,57936394,259329036,59903502,326962944,543559696,577179904,158605858,360001584,160576050,394081024,629163076,696275024,730027264,30247048,97362080,131901952,2206378,433766592,233031880,467586048,2215116,300146912,32238314,334032384,2223854,568258560,2224368,401144320,2226938,32374012,32440062,2227968,32505770,32571340,32636910,99680240,99745786],
  [2228224,24314026,225640652,26280174,293273840,26607870,304546048,58067466,259394572,59969038,327028480,543690768,577310976,159457826,360853552,160772658,394539776,629228612,696406096,630543444,730092800,30312584,98279584,132098560,2271914,433832128,467651584,2280652,300277984,334097920,2289390,568455168,2289904,32439034,233766140,334167552,2293502,2293504,66191274,267517900,32702446,32767984,32833534],
  [2293760,6488074,207814668,7012366,24576170,225902796,26476782,293339376,58133002,259460108,60034574,326897408,543363088,576917760,543887632,159130146,561459248,595014400,563360560,628900932,762794064,796349696,764695888,30378120,98410656,131967488,166177440,2337450,433963200,467520512,635948224,2346188,300409056,333966848,32304864,2354926,567275520,2355440,99678970,435223804,32767742,2359040,133234602,468778956,66322414,2359280,569638906,770965500,32899070]]
def state (i : Nat) : List T := stages3.getD i []
def perm (j : Nat) (i : Fin 16) : Fin 16 :=
  ⟨((permDigits.getD j 0) >>> (4*i.val)) % 16, Nat.mod_lt _ (by decide)⟩
def word (m : Nat) : T := BitVec.ofNat 16 m
def dest (m : Nat) := (m/65536)%512
def movePerm (m : Nat) := perm (m/33554432)
def limit (i : Nat) := if i<1 then 4 else if i<4 then 36 else 502

def works (s : List T) (n m : Nat) : Bool :=
  decide (dest m<n) && (ren (movePerm m) tgt == tgt) &&
  (sat (word m::s)).all (fun x=>decide (ren (movePerm m) x ∈ sat (state (dest m))))
def norm (g : T) := if g[0] then neg g else g

def cert (i : Nat) : Bool :=
  let ms := moves.getD i []
  ms.all (works (state i) (limit i)) &&
  (combs (state i)).all (fun g=>ms.any (fun m=>word m == norm g))

theorem enclose {s : List T} {g : T} : ∀ x∈sat (g::s), x∈sat (norm g::s) := by
  intro x hx
  by_cases e : g[0]=true
  · rw [norm,ite_eq_left e]
    rcases K4Core.ext hx with h|eq|eq
    · exact src (fun t ht=>List.mem_cons_of_mem _ ht) h
    · rw [eq]
      have hh := negmem (x:=neg g) (s:=neg g::s) (by simp [sat])
      simpa [neg] using hh
    · simp [eq,sat]
  · simpa [norm,e] using hx

theorem follow {k i} (hc : cert i=true) (hr : Reach (k+1) (state i) tgt) :
    ∃ j, j<limit i ∧ Reach k (state j) tgt := by
  simp only [cert,Bool.and_eq_true,List.all_eq_true] at hc
  cases hr with | @step _ s g z hg tail =>
    obtain ⟨m,member,hm⟩ := List.any_eq_true.mp (hc.2 g hg)
    have good := hc.1 m member
    simp only [works,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at good
    have eq : word m=norm g := beq_iff_eq.mp hm
    have h := transfer (π:=movePerm m) (t:=state (dest m)) (by
      intro x hx
      apply good.2 x
      rw [eq]
      exact enclose x hx) tail
    exact ⟨dest m,good.1.1,good.1.2 ▸ h⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check0 : cert 0=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check1 : cert 1=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check2 : cert 2=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check3 : cert 3=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check4 : cert 4=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check5 : cert 5=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check6 : cert 6=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check7 : cert 7=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check8 : cert 8=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check9 : cert 9=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check10 : cert 10=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check11 : cert 11=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check12 : cert 12=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check13 : cert 13=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check14 : cert 14=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check15 : cert 15=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check16 : cert 16=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check17 : cert 17=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check18 : cert 18=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check19 : cert 19=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check20 : cert 20=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check21 : cert 21=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check22 : cert 22=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check23 : cert 23=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check24 : cert 24=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check25 : cert 25=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check26 : cert 26=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check27 : cert 27=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check28 : cert 28=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check29 : cert 29=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check30 : cert 30=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check31 : cert 31=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check32 : cert 32=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check33 : cert 33=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check34 : cert 34=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check35 : cert 35=true := by decide +kernel
theorem checked (i : Fin 36) : cert i.val=true := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem orbitLower (last : ∀s∈stages3,¬Reach 3 s tgt) :
    ¬ Reach 6 [43690,52428,61680,65280] tgt := by
  intro h
  change Reach 6 (state 0) tgt at h
  obtain ⟨j,hj,r⟩ := follow check0 h
  change j<4 at hj
  obtain ⟨v,hv,q⟩ := follow (checked ⟨j,by omega⟩) r
  have v36 : v<36 := by simp [limit,hj] at hv;split_ifs at hv <;> omega
  obtain ⟨u,hu,e⟩ := follow (checked ⟨v,v36⟩) q
  have u502 : u<502 := by unfold limit at hu;split_ifs at hu <;> omega
  have um : u<stages3.length := by change u<502;exact u502
  have mem : state u ∈ stages3 := by rw [state,List.getD_eq_getElem _ _ um];exact List.getElem_mem _
  exact last (state u) mem e
end K4Orbit

namespace GuardPair
open K4Core K4Orbit
def variants : List T := [60156,60666,61356,61386,63726,64440,64482,64984,64996,65166,65202,65236]
def finishAt (s:List T) (t:T) := (combs s).any fun g => two (g::s) t (neg t)
theorem fromTail {s : List T} {z:T} (hr:Reach 3 s z) : finishAt s z=true := by
  cases hr with | step hg h1 =>
    cases h1 with | step hh h2 =>
      cases h2 with | step hi h3 =>
        cases h3 with | done hz =>
          have hfit : fits z z (K4Core.neg z)=true := by simp [fits,K4Core.neg,BitVec.and_comm]
          exact List.any_eq_true.mpr ⟨_,hg,two_all hh hi hz hfit⟩
theorem renVariant (i : Fin 24) : ∀t∈variants,ren (perm i.val) t ∈ variants := by
  have num : ∀ j:Fin 24, variants.all (fun t=>decide (ren (perm j.val) t∈variants))=true := by decide +kernel
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp (num i)) t ht)
def bounded (i:Nat) : Bool := (moves.getD i []).all (fun m=>decide (m/33554432<24))
theorem allBounded (i:Fin 36) : bounded i.val=true := by
  revert i
  decide +kernel
theorem followAny {k i z} (hi:i<36) (hz:z∈variants) (run:Reach (k+1) (state i) z) :
    ∃ j, j<limit i ∧ ∃ v∈variants, Reach k (state j) v := by
  have hc := checked ⟨i,hi⟩
  simp only [cert,Bool.and_eq_true,List.all_eq_true] at hc
  cases run with | @step _ s g z hg tail =>
    obtain ⟨m,member,hm⟩ := List.any_eq_true.mp (hc.2 g hg)
    have good := hc.1 m member
    simp only [works,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at good
    have eq : word m=norm g := beq_iff_eq.mp hm
    have r := transfer (π:=movePerm m) (t:=state (dest m)) (by
      intro x hx
      apply good.2 x
      rw [eq]
      exact enclose x hx) tail
    have bp := (List.all_eq_true.mp (allBounded ⟨i,hi⟩)) m member
    exact ⟨dest m,good.1.1,_,renVariant ⟨_,of_decide_eq_true bp⟩ _ hz,r⟩

theorem monoReach {s t:List T} (hs:∀ x∈sat s,x∈sat t) {k z} (r:Reach k s z) : Reach k t z := by
  induction r generalizing t with
  | done h => exact .done (hs _ h)
  | @step k s g z hg pending ih =>
    obtain ⟨a,ha,hh⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
    apply Reach.step (meetmem (hs _ ha) (hs _ hb))
    apply ih
    intro x hx
    rcases K4Core.ext hx with old|rfl|rfl
    · exact src (fun y hy=>List.mem_cons_of_mem _ hy) (hs _ old)
    · simp [sat]
    · apply negmem; simp [sat]

theorem padOne {s:List T} {k z} (r:Reach k s z) : Reach (k+1) s z := by
  have h : (0:T)∈sat s := by simp [sat]
  apply Reach.step (meetmem h h)
  exact monoReach (fun _ hx => src (fun y hy=>List.mem_cons_of_mem _ hy) hx) r

theorem pad {s:List T} {k t z} (h:k≤t) (r:Reach k s z) : Reach t s z := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact r
  | succ d ih => exact padOne (ih (by omega))
end GuardPair

namespace GuardLowFast
open K4Core
def targets : List T := [60156,60666,61356,61386,63726,64440,64482,64984,64996,65166,65202,65236]
def noTwo (s : List T) : Bool := targets.all fun t=> !(two s t (neg t))
end GuardLowFast

namespace GuardLowFast
open K4Core
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool0 : List (List T) := [[43690,52428,61680,65280],[170,43690,52428,61680,65280],[34952,43690,52428,61680,65280],[43690,52428,61166,61680,65280],[10,170,43690,52428,61680,65280],[10,43690,52428,61680,65280,65520],[136,170,43690,52428,61680,65280],[136,34952,43690,52428,61680,65280],[170,204,43690,52428,61680,65280],[170,2570,43690,52428,61680,65280],[170,3084,43690,52428,61680,65280],[170,3840,43690,52428,61680,65280],[170,21760,43690,52428,61680,65280],[170,34952,43690,52428,61680,65280],[170,43520,43690,52428,61680,65280],[170,43690,49344,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check0 : pool0.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool1 : List (List T) := [[170,43690,52224,52428,61680,65280],[170,43690,52292,52428,61680,65280],[170,43690,52428,52462,61680,65280],[170,43690,52428,61166,61680,65280],[170,43690,52428,61680,64764,65280],[170,43690,52428,61680,65280,65450],[170,43690,52428,61680,65280,65484],[238,43690,52428,61166,61680,65280],[2730,43690,52428,61440,61680,65280],[32896,34952,43690,52428,61680,65280],[34952,41120,43690,52428,61680,65280],[34952,43690,52428,61166,61680,65280],[34952,43690,52428,61440,61680,65280],[34952,43690,52428,61680,63736,65280],[34952,43690,52428,61680,64250,65280],[34952,43690,52428,61680,65280,65520]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check1 : pool1.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool2 : List (List T) := [[43176,43690,52428,61680,64764,65280],[43690,52428,61166,61680,64250,65280],[43690,52428,61166,61680,65278,65280],[43690,52428,61166,61680,65280,65520],[2,10,170,43690,52428,61680,65280],[2,10,43690,52428,61680,65280,65520],[2,170,43690,52428,61680,64764,65280],[2,43690,52428,61680,64764,65280,65532],[8,10,170,43690,52428,61680,65280],[8,10,43690,52428,61680,65280,65520],[8,136,170,43690,52428,61680,65280],[8,136,34952,43690,52428,61680,65280],[8,170,3084,43690,52428,61680,65280],[8,34952,43690,52428,61680,65280,65520],[10,12,43690,52428,61680,65280,65520],[10,34,170,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check2 : pool2.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool3 : List (List T) := [[10,136,170,43690,52428,61680,65280],[10,160,170,43690,52428,61680,65280],[10,170,204,43690,52428,61680,65280],[10,170,240,43690,52428,61680,65280],[10,170,2570,43690,52428,61680,65280],[10,170,3084,43690,52428,61680,65280],[10,170,3840,43690,52428,61680,65280],[10,170,8738,43690,52428,61680,65280],[10,170,12336,43690,52428,61680,65280],[10,170,13056,43690,52428,61680,65280],[10,170,17476,43690,52428,61680,65280],[10,170,20560,43690,52428,61680,65280],[10,170,21760,43690,52428,61680,65280],[10,170,34952,43690,52428,61680,65280],[10,170,41120,43690,52428,61680,65280],[10,170,43520,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check3 : pool3.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool4 : List (List T) := [[10,170,43680,43690,52428,61680,65280],[10,170,43690,49344,52428,61680,65280],[10,170,43690,52224,52428,61680,65280],[10,170,43690,52292,52428,61680,65280],[10,170,43690,52420,52428,61680,65280],[10,170,43690,52428,52430,61680,65280],[10,170,43690,52428,52462,61680,65280],[10,170,43690,52428,61166,61680,65280],[10,170,43690,52428,61440,61680,65280],[10,170,43690,52428,61520,61680,65280],[10,170,43690,52428,61680,61690,65280],[10,170,43690,52428,61680,64250,65280],[10,170,43690,52428,61680,64764,65280],[10,170,43690,52428,61680,65280,65290],[10,170,43690,52428,61680,65280,65450],[10,170,43690,52428,61680,65280,65484]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check4 : pool4.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool5 : List (List T) := [[10,170,43690,52428,61680,65280,65520],[10,204,43690,52428,61680,65280,65520],[10,240,43530,43690,52428,61680,65280],[10,240,43690,52428,61680,65280,65520],[10,250,43690,52428,61680,64250,65280],[10,8738,43690,52428,61680,65280,65520],[10,12336,43690,52428,61680,65280,65520],[10,13104,43690,52428,61680,65280,65520],[10,17476,43690,52428,61680,65280,65520],[10,20560,43690,52428,61680,65280,65520],[10,21840,43690,52428,61680,65280,65520],[10,34952,43690,52428,61680,65280,65520],[10,41120,43690,52428,61680,65280,65440],[10,41120,43690,52428,61680,65280,65520],[10,43680,43690,52428,61680,65280,65520],[10,43690,49344,52428,61680,65280,65520]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check5 : pool5.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool6 : List (List T) := [[10,43690,52416,52428,61680,65280,65520],[10,43690,52420,52428,61680,65280,65520],[10,43690,52428,52430,61680,65280,65520],[10,43690,52428,61166,61680,65280,65520],[10,43690,52428,61440,61680,65280,65520],[10,43690,52428,61680,61690,65280,65520],[10,43690,52428,61680,64250,65280,65520],[10,43690,52428,61680,64764,65280,65520],[10,43690,52428,61680,65280,65520,65530],[10,43690,52428,61680,65280,65520,65532],[14,238,43690,52428,61166,61680,65280],[14,43690,52428,61166,61680,65280,65520],[42,170,43690,49344,52428,61680,65280],[42,10794,43690,49344,52428,61680,65280],[42,43690,49344,52428,61680,65280,65472],[128,136,170,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check6 : pool6.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool7 : List (List T) := [[128,136,34952,43690,52428,61680,65280],[128,170,43690,49344,52428,61680,65280],[128,32896,34952,43690,52428,61680,65280],[136,160,170,43690,52428,61680,65280],[136,170,204,43690,52428,61680,65280],[136,170,240,43690,52428,61680,65280],[136,170,2570,43690,52428,61680,65280],[136,170,3084,43690,52428,61680,65280],[136,170,3840,43690,52428,61680,65280],[136,170,8738,43690,52428,61680,65280],[136,170,12336,43690,52428,61680,65280],[136,170,13056,43690,52428,61680,65280],[136,170,17476,43690,52428,61680,65280],[136,170,20560,43690,52428,61680,65280],[136,170,21760,43690,52428,61680,65280],[136,170,34952,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check7 : pool7.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool8 : List (List T) := [[136,170,41120,43690,52428,61680,65280],[136,170,43520,43690,52428,61680,65280],[136,170,43554,43690,52428,61680,65280],[136,170,43690,49344,52428,61680,65280],[136,170,43690,52224,52428,61680,65280],[136,170,43690,52292,52428,61680,65280],[136,170,43690,52428,52462,61680,65280],[136,170,43690,52428,61166,61680,65280],[136,170,43690,52428,61440,61680,65280],[136,170,43690,52428,61520,61680,65280],[136,170,43690,52428,61552,61680,65280],[136,170,43690,52428,61680,61688,65280],[136,170,43690,52428,61680,61690,65280],[136,170,43690,52428,61680,64250,65280],[136,170,43690,52428,61680,64764,65280],[136,170,43690,52428,61680,65280,65416]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check8 : pool8.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool9 : List (List T) := [[136,170,43690,52428,61680,65280,65450],[136,170,43690,52428,61680,65280,65484],[136,170,43690,52428,61680,65280,65520],[136,240,34952,43690,52428,61680,65280],[136,2056,34952,43690,52428,61680,65280],[136,2570,34952,43690,52428,61680,65280],[136,3840,34952,43690,52428,61680,65280],[136,8738,34952,43690,52428,61680,65280],[136,8738,43690,52428,61680,65280,65314],[136,8874,43690,52224,52428,61680,65280],[136,12336,34952,43690,52428,61680,65280],[136,13056,34952,43690,52428,61680,65280],[136,28784,34952,43690,52428,61680,65280],[136,30464,34952,43690,52428,61680,65280],[136,32896,34952,43690,52428,61680,65280],[136,34816,34952,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check9 : pool9.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool10 : List (List T) := [[136,34952,41120,43690,52428,61680,65280],[136,34952,43520,43690,52428,61680,65280],[136,34952,43554,43690,52428,61680,65280],[136,34952,43690,52428,61166,61680,65280],[136,34952,43690,52428,61440,61680,65280],[136,34952,43690,52428,61552,61680,65280],[136,34952,43690,52428,61680,61688,65280],[136,34952,43690,52428,61680,63736,65280],[136,34952,43690,52428,61680,64250,65280],[136,34952,43690,52428,61680,65280,65416],[136,34952,43690,52428,61680,65280,65450],[136,34952,43690,52428,61680,65280,65520],[136,43656,43690,52428,61680,65280,65484],[138,170,12336,43690,52428,61680,65280],[138,12336,35466,43690,52428,61680,65280],[138,12336,43690,52428,61680,65280,65328]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check10 : pool10.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool11 : List (List T) := [[168,170,43690,52428,61680,64764,65280],[168,252,43690,52428,61680,64764,65280],[168,43176,43690,52428,61680,64764,65280],[170,204,238,43690,52428,61680,65280],[170,204,240,43690,52428,61680,65280],[170,204,2570,43690,52428,61680,65280],[170,204,3840,43690,52428,61680,65280],[170,204,8738,43690,52428,61680,65280],[170,204,12336,43690,52428,61680,65280],[170,204,13056,43690,52428,61680,65280],[170,204,34952,43690,52428,61680,65280],[170,204,41120,43690,52428,61680,65280],[170,204,43520,43690,52428,61680,65280],[170,204,43554,43690,52428,61680,65280],[170,204,43690,43758,52428,61680,65280],[170,204,43690,52428,61166,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check11 : pool11.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool12 : List (List T) := [[170,204,43690,52428,61440,61680,65280],[170,204,43690,52428,61488,61680,65280],[170,204,43690,52428,61680,61690,65280],[170,204,43690,52428,61680,64250,65280],[170,204,43690,52428,61680,65280,65450],[170,204,43690,52428,61680,65280,65520],[170,238,43690,52428,52462,61680,65280],[170,238,43690,52428,61166,61680,65280],[170,252,43690,52428,61680,64764,65280],[170,2570,2730,43690,52428,61680,65280],[170,2570,8738,43690,52428,61680,65280],[170,2570,12336,43690,52428,61680,65280],[170,2570,17476,43690,52428,61680,65280],[170,2570,20560,43690,52428,61680,65280],[170,2570,34952,43690,52428,61680,65280],[170,2570,41120,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check12 : pool12.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool13 : List (List T) := [[170,2570,43690,49344,52428,61680,65280],[170,2570,43690,50372,52428,61680,65280],[170,2570,43690,52428,52462,61680,65280],[170,2570,43690,52428,61166,61680,65280],[170,2570,43690,52428,61440,61680,65280],[170,2570,43690,52428,61520,61680,65280],[170,2570,43690,52428,61680,61690,65280],[170,2570,43690,52428,61680,64250,65280],[170,2570,43690,52428,61680,64764,65280],[170,2570,43690,52428,61680,65280,65520],[170,2730,43690,52428,61440,61680,65280],[170,2730,43690,52428,61520,61680,65280],[170,3084,3246,43690,52428,61680,65280],[170,3084,12336,43690,52428,61680,65280],[170,3084,13056,43690,52428,61680,65280],[170,3084,34952,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check13 : pool13.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool14 : List (List T) := [[170,3084,41120,43690,52428,61680,65280],[170,3084,41634,43690,52428,61680,65280],[170,3084,43520,43690,52428,61680,65280],[170,3084,43690,44718,52428,61680,65280],[170,3084,43690,52428,61166,61680,65280],[170,3084,43690,52428,61440,61680,65280],[170,3084,43690,52428,61520,61680,65280],[170,3084,43690,52428,61680,61690,65280],[170,3084,43690,52428,61680,64250,65280],[170,3084,43690,52428,61680,64764,65280],[170,3084,43690,52428,61680,65280,65520],[170,3086,43690,52428,52462,61680,65280],[170,3212,43690,52428,61520,61680,65280],[170,3276,43690,52428,61440,61680,65280],[170,3598,43690,52428,61166,61680,65280],[170,3840,4010,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check14 : pool14.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool15 : List (List T) := [[170,3840,20560,43690,52428,61680,65280],[170,3840,34952,43690,52428,61680,65280],[170,3840,41120,43690,52428,61680,65280],[170,3840,41130,43690,52428,61680,65280],[170,3840,43520,43690,52428,61680,65280],[170,3840,43690,44970,52428,61680,65280],[170,3840,43690,49344,52428,61680,65280],[170,3840,43690,49356,52428,61680,65280],[170,3840,43690,52224,52428,61680,65280],[170,3840,43690,52292,52428,61680,65280],[170,3840,43690,52428,52462,61680,65280],[170,3840,43690,52428,53196,61680,65280],[170,3840,43690,52428,61166,61680,65280],[170,3840,43690,52428,61440,61680,65280],[170,3840,43690,52428,61520,61680,65280],[170,3840,43690,52428,61680,61690,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check15 : pool15.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool16 : List (List T) := [[170,3840,43690,52428,61680,64250,65280],[170,3840,43690,52428,61680,64764,65280],[170,3840,43690,52428,61680,65280,65450],[170,3840,43690,52428,61680,65280,65484],[170,3840,43690,52428,61680,65280,65520],[170,3850,43690,52428,61680,65280,65450],[170,3852,43690,52428,61680,65280,65484],[170,10794,43690,49344,52428,61680,65280],[170,16128,43690,49344,52428,61680,65280],[170,17612,43520,43690,52428,61680,65280],[170,19532,41120,43690,52428,61680,65280],[170,21588,43690,52428,61680,64764,65280],[170,21760,21930,43690,52428,61680,65280],[170,21760,34952,43690,52428,61680,65280],[170,21760,35020,43690,52428,61680,65280],[170,21760,43520,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check16 : pool16.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool17 : List (List T) := [[170,21760,43690,49344,52428,61680,65280],[170,21760,43690,52428,52462,61680,65280],[170,21760,43690,52428,61166,61680,65280],[170,21760,43690,52428,61680,64764,65280],[170,21760,43690,52428,61680,65280,65450],[170,21828,43690,52428,61680,65280,65484],[170,24320,41120,43690,52428,61680,65280],[170,32896,34952,43690,52428,61680,65280],[170,32896,43690,49344,52428,61680,65280],[170,34816,34952,43690,52428,61680,65280],[170,34816,43520,43690,52428,61680,65280],[170,34816,43690,52224,52428,61680,65280],[170,34816,43690,52292,52428,61680,65280],[170,34952,34986,43690,52428,61680,65280],[170,34952,41120,43690,52428,61680,65280],[170,34952,43520,43690,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check17 : pool17.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool18 : List (List T) := [[170,34952,43690,49344,52428,61680,65280],[170,34952,43690,52224,52428,61680,65280],[170,34952,43690,52292,52428,61680,65280],[170,34952,43690,52428,52462,61680,65280],[170,34952,43690,52428,61166,61680,65280],[170,34952,43690,52428,61440,61680,65280],[170,34952,43690,52428,61520,61680,65280],[170,34952,43690,52428,61680,61690,65280],[170,34952,43690,52428,61680,63736,65280],[170,34952,43690,52428,61680,64250,65280],[170,34952,43690,52428,61680,64764,65280],[170,34952,43690,52428,61680,65280,65416],[170,34952,43690,52428,61680,65280,65450],[170,34952,43690,52428,61680,65280,65484],[170,34952,43690,52428,61680,65280,65520],[170,34986,43690,52428,52462,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check18 : pool18.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool19 : List (List T) := [[170,43176,43690,52428,61680,64764,65280],[170,43520,43690,49344,52428,61680,65280],[170,43520,43690,52224,52428,61680,65280],[170,43520,43690,52292,52428,61680,65280],[170,43520,43690,52428,52462,61680,65280],[170,43520,43690,52428,61132,61680,65280],[170,43520,43690,52428,61166,61680,65280],[170,43520,43690,52428,61680,64764,65280],[170,43520,43690,52428,61680,65280,65450],[170,43520,43690,52428,61680,65280,65484],[170,43656,43690,52428,61680,65280,65484],[170,43690,49152,49344,52428,61680,65280],[170,43690,49152,52224,52428,61680,65280],[170,43690,49216,49344,52428,61680,65280],[170,43690,49216,52292,52428,61680,65280],[170,43690,49344,49386,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check19 : pool19.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool20 : List (List T) := [[170,43690,49344,52224,52428,61680,65280],[170,43690,49344,52292,52428,61680,65280],[170,43690,49344,52428,52462,61680,65280],[170,43690,49344,52428,60138,61680,65280],[170,43690,49344,52428,61166,61680,65280],[170,43690,49344,52428,61680,64764,65280],[170,43690,49344,52428,61680,65280,65450],[170,43690,49344,52428,61680,65280,65472],[170,43690,49344,52428,61680,65280,65484],[170,43690,49352,52428,61680,61690,65280],[170,43690,51400,52428,61680,64250,65280],[170,43690,52224,52292,52428,61680,65280],[170,43690,52224,52394,52428,61680,65280],[170,43690,52224,52428,52462,61680,65280],[170,43690,52224,52428,61098,61680,65280],[170,43690,52224,52428,61166,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check20 : pool20.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool21 : List (List T) := [[170,43690,52224,52428,61440,61680,65280],[170,43690,52224,52428,61520,61680,65280],[170,43690,52224,52428,61680,61690,65280],[170,43690,52224,52428,61680,64250,65280],[170,43690,52224,52428,61680,64752,65280],[170,43690,52224,52428,61680,64764,65280],[170,43690,52224,52428,61680,65280,65450],[170,43690,52224,52428,61680,65280,65484],[170,43690,52224,52428,61680,65280,65520],[170,43690,52292,52428,52462,61680,65280],[170,43690,52292,52428,61166,61680,65280],[170,43690,52292,52428,61520,61680,65280],[170,43690,52292,52428,61680,61690,65280],[170,43690,52292,52428,61680,64250,65280],[170,43690,52292,52428,61680,64756,65280],[170,43690,52292,52428,61680,64764,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check21 : pool21.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool22 : List (List T) := [[170,43690,52292,52428,61680,65280,65348],[170,43690,52292,52428,61680,65280,65450],[170,43690,52292,52428,61680,65280,65484],[170,43690,52292,52428,61680,65280,65520],[170,43690,52360,52428,61680,65280,65450],[170,43690,52416,52428,61680,65280,65520],[170,43690,52428,52462,61166,61680,65280],[170,43690,52428,52462,61680,61690,65280],[170,43690,52428,52462,61680,64250,65280],[170,43690,52428,52462,61680,64764,65280],[170,43690,52428,52462,61680,64766,65280],[170,43690,52428,52462,61680,65280,65450],[170,43690,52428,52462,61680,65280,65484],[170,43690,52428,52462,61680,65280,65518],[170,43690,52428,52462,61680,65280,65520],[170,43690,52428,60928,61166,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check22 : pool22.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool23 : List (List T) := [[170,43690,52428,60996,61166,61680,65280],[170,43690,52428,61166,61680,64250,65280],[170,43690,52428,61166,61680,64764,65280],[170,43690,52428,61166,61680,65278,65280],[170,43690,52428,61166,61680,65280,65450],[170,43690,52428,61166,61680,65280,65484],[170,43690,52428,61166,61680,65280,65518],[170,43690,52428,61166,61680,65280,65520],[170,43690,52428,61680,64512,64764,65280],[170,43690,52428,61680,64596,64764,65280],[170,43690,52428,61680,64764,64766,65280],[170,43690,52428,61680,64764,65278,65280],[170,43690,52428,61680,64764,65280,65450],[170,43690,52428,61680,64764,65280,65484],[170,43690,52428,61680,64764,65280,65532],[170,43690,52428,61680,65280,65348,65484]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check23 : pool23.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool24 : List (List T) := [[170,43690,52428,61680,65280,65450,65484],[170,43690,52428,61680,65280,65450,65518],[170,43690,52428,61680,65280,65484,65518],[170,43690,52428,61680,65280,65484,65520],[170,43690,52428,61680,65280,65484,65532],[234,43690,49344,52428,60138,61680,65280],[238,3598,43690,52428,61166,61680,65280],[238,34952,43690,52428,61166,61680,65280],[238,41120,43690,52428,61166,61680,65280],[238,43520,43690,52428,61166,61680,65280],[238,43690,43758,52428,61166,61680,65280],[238,43690,52428,57568,61166,61680,65280],[238,43690,52428,60928,61166,61680,65280],[238,43690,52428,61166,61440,61680,65280],[238,43690,52428,61166,61456,61680,65280],[238,43690,52428,61166,61680,61694,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check24 : pool24.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool25 : List (List T) := [[238,43690,52428,61166,61680,64250,65280],[238,43690,52428,61166,61680,65278,65280],[238,43690,52428,61166,61680,65280,65450],[238,43690,52428,61166,61680,65280,65518],[238,43690,52428,61166,61680,65280,65520],[238,43690,52428,61680,65280,65450,65518],[254,43690,52428,61166,61680,65278,65280],[682,43690,52428,61680,64512,64764,65280],[2184,2730,43690,52428,61440,61680,65280],[2184,34952,43690,52428,61440,61680,65280],[2730,3276,43690,52428,61440,61680,65280],[2730,34952,43690,52428,61440,61680,65280],[2730,40960,41120,43690,52428,61680,65280],[2730,40960,43690,52428,61440,61680,65280],[2730,41120,43690,52428,61440,61680,65280],[2730,43690,49152,52428,61440,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check25 : pool25.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool26 : List (List T) := [[2730,43690,49344,52428,61440,61680,65280],[2730,43690,50244,52428,61440,61680,65280],[2730,43690,52428,52974,61440,61680,65280],[2730,43690,52428,61166,61440,61680,65280],[2730,43690,52428,61440,61520,61680,65280],[2730,43690,52428,61440,61680,64170,65280],[2730,43690,52428,61440,61680,64250,65280],[2730,43690,52428,61440,61680,64716,65280],[2730,43690,52428,61440,61680,64764,65280],[2730,43690,52428,61440,61680,65280,65520],[2810,43690,52428,61440,61680,64250,65280],[3822,43690,52428,61166,61440,61680,65280],[4080,43690,52428,61440,61680,65280,65520],[10922,43690,49152,49344,52428,61680,65280],[32768,32896,34952,43690,52428,61680,65280],[32768,34952,43690,52428,61440,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check26 : pool26.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool27 : List (List T) := [[32896,34816,34952,43690,52428,61680,65280],[32896,34952,41120,43690,52428,61680,65280],[32896,34952,43520,43690,52428,61680,65280],[32896,34952,43690,52428,61166,61680,65280],[32896,34952,43690,52428,61440,61680,65280],[32896,34952,43690,52428,61680,63736,65280],[32896,34952,43690,52428,61680,64250,65280],[32896,34952,43690,52428,61680,65280,65408],[32896,34952,43690,52428,61680,65280,65416],[32896,34952,43690,52428,61680,65280,65450],[32896,34952,43690,52428,61680,65280,65520],[34944,34952,43690,52428,61680,65280,65520],[34944,43680,43690,52428,61680,65280,65520],[34952,41120,43176,43690,52428,61680,65280],[34952,41120,43520,43690,52428,61680,65280],[34952,41120,43690,49344,52428,61680,65280]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check27 : pool27.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool28 : List (List T) := [[34952,41120,43690,52224,52428,61680,65280],[34952,41120,43690,52428,60652,61680,65280],[34952,41120,43690,52428,61166,61680,65280],[34952,41120,43690,52428,61680,64764,65280],[34952,41120,43690,52428,61680,65280,65416],[34952,41120,43690,52428,61680,65280,65450],[34952,41120,43690,52428,61680,65280,65484],[34952,43176,43690,52428,61680,63736,65280],[34952,43176,43690,52428,61680,64764,65280],[34952,43680,43690,52428,61680,65280,65520],[34952,43690,52428,57568,61166,61680,65280],[34952,43690,52428,61166,61440,61680,65280],[34952,43690,52428,61166,61680,63736,65280],[34952,43690,52428,61166,61680,64250,65280],[34952,43690,52428,61166,61680,65278,65280],[34952,43690,52428,61166,61680,65280,65520]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check28 : pool28.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool29 : List (List T) := [[34952,43690,52428,61440,61680,63624,65280],[34952,43690,52428,61440,61680,63736,65280],[34952,43690,52428,61440,61680,64250,65280],[34952,43690,52428,61568,61680,65280,65416],[34952,43690,52428,61600,61680,65280,65450],[34952,43690,52428,61680,63736,64250,65280],[34952,43690,52428,61680,63736,65280,65416],[34952,43690,52428,61680,63736,65280,65450],[34952,43690,52428,61680,63736,65280,65520],[34952,43690,52428,61680,63736,65280,65528],[34952,43690,52428,61680,64250,64764,65280],[34952,43690,52428,61680,64250,65278,65280],[34952,43690,52428,61680,64250,65280,65450],[34952,43690,52428,61680,64250,65280,65484],[34952,43690,52428,61680,64250,65280,65520],[34952,43690,52428,61680,64250,65280,65530]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check29 : pool29.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool30 : List (List T) := [[34952,43690,52428,61680,65280,65520,65528],[34952,43690,52428,61680,65280,65520,65530],[43176,43690,52428,60652,61680,64764,65280],[43176,43690,52428,61166,61680,64764,65280],[43176,43690,52428,61680,64512,64764,65280],[43176,43690,52428,61680,64764,65278,65280],[43176,43690,52428,61680,64764,65280,65448],[43176,43690,52428,61680,64764,65280,65450],[43176,43690,52428,61680,64764,65280,65484],[43176,43690,52428,61680,64764,65280,65532],[43688,43690,52428,61680,64764,65280,65532],[43690,52428,60138,61166,61680,64250,65280],[43690,52428,61152,61166,61680,65280,65520],[43690,52428,61166,61680,64250,64764,65280],[43690,52428,61166,61680,64250,65278,65280],[43690,52428,61166,61680,64250,65280,65450]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check30 : pool30.all noTwo = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def pool31 : List (List T) := [[43690,52428,61166,61680,64250,65280,65484],[43690,52428,61166,61680,64250,65280,65518],[43690,52428,61166,61680,65278,65280,65518],[43690,52428,61166,61680,65278,65280,65520],[43690,52428,61166,61680,65278,65280,65534],[43690,52428,61166,61680,65280,65520,65534]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem check31 : pool31.all noTwo = true := by decide +kernel
end GuardLowFast

namespace GuardPair
open K4Core K4Orbit GuardLowFast
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 32768 in
private theorem allGood : stages3.all noTwo = true := by
  change (pool0 ++ pool1 ++ pool2 ++ pool3 ++ pool4 ++ pool5 ++ pool6 ++ pool7 ++ pool8 ++ pool9 ++ pool10 ++ pool11 ++ pool12 ++ pool13 ++ pool14 ++ pool15 ++ pool16 ++ pool17 ++ pool18 ++ pool19 ++ pool20 ++ pool21 ++ pool22 ++ pool23 ++ pool24 ++ pool25 ++ pool26 ++ pool27 ++ pool28 ++ pool29 ++ pool30 ++ pool31).all noTwo = true
  simp only [List.all_append,GuardLowFast.check0,GuardLowFast.check1,GuardLowFast.check2,GuardLowFast.check3,GuardLowFast.check4,GuardLowFast.check5,GuardLowFast.check6,GuardLowFast.check7,GuardLowFast.check8,GuardLowFast.check9,GuardLowFast.check10,GuardLowFast.check11,GuardLowFast.check12,GuardLowFast.check13,GuardLowFast.check14,GuardLowFast.check15,GuardLowFast.check16,GuardLowFast.check17,GuardLowFast.check18,GuardLowFast.check19,GuardLowFast.check20,GuardLowFast.check21,GuardLowFast.check22,GuardLowFast.check23,GuardLowFast.check24,GuardLowFast.check25,GuardLowFast.check26,GuardLowFast.check27,GuardLowFast.check28,GuardLowFast.check29,GuardLowFast.check30,GuardLowFast.check31,Bool.and_self]
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 32768 in
private theorem noTail {s : List T} {t : T} (hs : s∈stages3) (ht : t∈variants) : ¬Reach 2 s t := by
  intro r
  have cs := List.all_eq_true.mp allGood s hs
  have nh := List.all_eq_true.mp cs t ht
  cases r with | step hg h1 =>
    cases h1 with | step hi h2 =>
      cases h2 with | done hz =>
        have hfit : fits t t (neg t)=true := by simp [fits,neg]
        have yes := two_all hg hi hz hfit
        simp [yes] at nh
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 32768 in
theorem variantLower {k : Nat} {t0 : T} (mem : t0 ∈ variants)
    (h : Reach k [43690,52428,61680,65280] t0) : 6 ≤ k := by
  by_contra! hk
  have five := pad (t:=5) (by omega) h
  change Reach 5 (state 0) t0 at five
  obtain ⟨i,hi,t,ht,r⟩ := followAny (by decide : 0 < 36) mem five
  change i < 4 at hi
  obtain ⟨j,hj,v,hv,q⟩ := followAny (by omega : i < 36) ht r
  have jb : j < 36 := by unfold limit at hj; split_ifs at hj <;> omega
  obtain ⟨l,hl,w,hw,u⟩ := followAny jb hv q
  have lb : l < 502 := by unfold limit at hl; split_ifs at hl <;> omega
  have leng : l < stages3.length := by change l < 502; exact lb
  have sl : state l ∈ stages3 := by rw [state,List.getD_eq_getElem _ _ leng];exact List.getElem_mem _
  exact noTail sl hw u
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 32768 in
theorem lowSix {k : Nat} (h : Reach k [43690,52428,61680,65280] z0) : 6 ≤ k :=
  variantLower (by decide +kernel : z0∈variants) h
end GuardPair

namespace GuardPair
inductive Confined (allowed : List T) : Nat → Nat → List P → P → Prop where
  | done {k s p} (h : Run k s p) : Confined allowed 0 k s p
  | step {n k s a b p} (ha : Lit s a) (hb : Lit s b)
    (mem : K4Orbit.norm (a.1 &&& b.1) ∈ allowed)
    (rest : Confined allowed n k ((a.1 &&& b.1,a.2 &&& b.2)::s) p) :
    Confined allowed (n+1) k s p
end GuardPair

namespace GuardPair
open K4Core K4Orbit
def R (i:Fin 24) (x:P) : P := (ren (perm i.val) x.1,ren (perm i.val) x.2)
def B (a b:P) : P := (a.1 &&& b.1,a.2 &&& b.2)
theorem rBin (i) (a b:P) : R i (B a b) = B (R i a) (R i b) := by
  simp [R,B,ren_meet]
theorem rz (i:Fin 24) : ren (perm i.val) 0=0 ∧ ren (perm i.val) 65535=65535 ∧ ren (perm i.val) z1=z1 := by
  revert i; decide +kernel
theorem rawFwd (i:Fin 24) : ∀ x∈base, R i x∈base := by
  have h : ∀j:Fin 24,base.all (fun x=>decide (R j x∈base))=true := by decide +kernel
  intro x hx
  exact of_decide_eq_true ((List.all_eq_true.mp (h i)) _ hx)
theorem rawBack (i:Fin 24) : ∀ x∈base, ∃y∈base, R i y=x := by
  have h : ∀j:Fin 24,base.all (fun x=>base.any (fun y=>R j y==x))=true := by decide +kernel
  intro x hx
  obtain ⟨y,hy,ey⟩ := List.any_eq_true.mp (List.all_eq_true.mp (h i) x hx)
  exact ⟨y,hy,beq_iff_eq.mp ey⟩

theorem mapLit {s t:List P} (i:Fin 24) (rel:∀x∈s,R i x∈t) {a} (h:Lit s a) : Lit t (R i a) := by
  induction h with
  | src mem => exact .src (rel _ mem)
  | zero => change Lit t (ren (perm i.val) 0,ren (perm i.val) 0); rw [(rz i).1]; exact .zero
  | @neg p _ ih =>
    change Lit t (ren (perm i.val) (K4Core.neg p.1),ren (perm i.val) (K4Core.neg p.2))
    rw [ren_neg,ren_neg]
    exact .neg ih
  | @clamp p _ b ih =>
    cases b
    · change Lit t (ren (perm i.val) p.1,ren (perm i.val) 0)
      rw [(rz i).1]; exact Lit.clamp ih false
    · change Lit t (ren (perm i.val) p.1,ren (perm i.val) 65535)
      rw [(rz i).2.1]; exact Lit.clamp ih true

theorem mapRun {s t:List P} (i:Fin 24) (rel:∀x∈s,R i x∈t) {k a} (h:Run k s a) : Run k t (R i a) := by
  induction h generalizing t with
  | done p => exact .done (mapLit i rel p)
  | @step k s a b p ha hb _ ih =>
    apply Run.step (mapLit i rel ha) (mapLit i rel hb)
    apply ih
    intro v hv
    rcases List.mem_cons.mp hv with rfl|old
    · exact List.mem_cons.mpr (Or.inl (rBin _ _ _))
    · exact List.mem_cons_of_mem _ (rel _ old)

inductive Hist : Nat → List P → Prop where
  | start : Hist 0 base
  | push {k s a b} : Hist k s → Lit s a → Lit s b → Hist (k+1) (B a b::s)

theorem mapHist (i:Fin 24) {k r} (h:Hist k r) : ∃ r', Hist k r' ∧
    (∀ x∈r, R i x∈r') ∧ ∀ y∈r', ∃x∈r, R i x=y := by
  induction h with
  | start => exact ⟨base,.start,rawFwd i,rawBack i⟩
  | @push k r a b _ ha hb ih =>
    obtain ⟨rs,hist,f,bk⟩ := ih
    refine ⟨_,.push hist (mapLit i f ha) (mapLit i f hb),?_,?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl|old
      · exact List.mem_cons.mpr (Or.inl (rBin _ _ _))
      · exact List.mem_cons_of_mem _ (f _ old)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl|old
      · exact ⟨_,List.mem_cons_self ..,rBin _ _ _⟩
      · obtain ⟨x,hx,e⟩ := bk _ old
        exact ⟨x,List.mem_cons_of_mem _ hx,e⟩

theorem appendHist {k r} (h:Hist k r) {allowed:List T}
    (cov:∀v∈r,norm v.1∈allowed) {l n z} (run:Confined allowed l n r z) :
    Confined allowed (k+l) n base z := by
  induction h generalizing l with
  | start => simpa using run
  | @push k s a b pending ha hb ih =>
    have q := ih (fun x hx=>cov x (List.mem_cons_of_mem _ hx))
      (Confined.step ha hb (cov _ (List.mem_cons_self ..)) run)
    rw [show k+1+l = k+(l+1) by omega]; exact q

theorem lowLit {s:List P} {t:List T} (inc:∀p∈s,p.1∈sat t) {x} (h:Lit s x) : x.1∈sat t := by
  induction h with
  | src p => exact inc _ p
  | zero => simp [sat]
  | neg _ ih => exact negmem ih
  | clamp _ _ ih => exact ih

theorem move {i g} (hi:i<36) (hg:g∈combs (state i)) :
    ∃ p:Fin 24,∃ j,j<limit i ∧ ∀ x∈sat (g::state i),ren (perm p.val) x∈sat (state j) := by
  have hc := checked ⟨i,hi⟩
  simp only [cert,Bool.and_eq_true,List.all_eq_true] at hc
  obtain ⟨m,hm,eg⟩ := List.any_eq_true.mp (hc.2 g hg)
  have good := hc.1 m hm
  simp only [works,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at good
  have bp := (List.all_eq_true.mp (allBounded ⟨i,hi⟩)) m hm
  refine ⟨⟨_,of_decide_eq_true bp⟩,dest m,good.1.1,?_⟩
  intro x hx
  apply good.2 x
  rw [beq_iff_eq.mp eg]
  exact enclose x hx

def AtState (i k n:Nat) (t:T) := ∃ r,Hist k r ∧ (∀x∈r,x.1∈sat (state i)) ∧ Run n r (t,z1)
theorem shift {i k n t} (hi:i<36) (h:AtState i k (n+1) t) (ht:t∈variants) :
    ∃j,j<limit i ∧ ∃u∈variants,AtState j (k+1) n u := by
  obtain ⟨s,old,inc,run⟩ := h
  cases run with | @step _ _ a b _ ha hb tail =>
    obtain ⟨p,j,hj,cov⟩ := move hi (meetmem (lowLit inc ha) (lowLit inc hb))
    obtain ⟨r,his,f,bk⟩ := mapHist p (Hist.push old ha hb)
    refine ⟨j,hj,_,renVariant p t ht,r,his,?_,?_⟩
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := bk _ hx
      apply cov
      rcases List.mem_cons.mp hy with rfl|old
      · simp [B,sat]
      · exact src (fun u hu =>List.mem_cons_of_mem _ hu) (inc _ old)
    · have q := mapRun p f tail
      simpa [R,(rz p).2.2] using q
end GuardPair

namespace GuardPair
open K4Core K4Orbit
theorem satBound {s t : List T} (inc:∀x∈s,x∈sat t) : ∀x∈sat s,x∈sat t := by
  intro x h
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at h
  rcases h with rfl|rfl|old|⟨y,hy,rfl⟩
  · simp [sat]
  · simp [sat]
  · exact inc _ old
  · exact negmem (inc _ hy)

theorem tailLow {s:List P} {w:List T} (inc:∀q∈s,q.1∈sat w) {k p} (r:Run k s p) :
    Reach k w p.1 := by
  induction r generalizing w with
  | done hh => exact .done (lowLit inc hh)
  | @step k s a b p ha hb _ ih =>
    apply Reach.step (meetmem (lowLit inc ha) (lowLit inc hb))
    apply ih
    intro q hq
    rcases List.mem_cons.mp hq with rfl|old
    · simp [sat]
    · exact src (fun x hx=>List.mem_cons_of_mem _ hx) (inc _ old)

theorem normNeg (x:T) : K4Orbit.norm (neg x)=K4Orbit.norm x := by
  unfold K4Orbit.norm
  cases h:x[0] <;> simp [neg,h]
def evenState (s:List T) : Bool := s.all fun x=>!(x.getLsbD 0)
set_option maxRecDepth 32768 in
theorem canonEven : stages3.all evenState=true := by decide +kernel
set_option maxRecDepth 32768 in
theorem normMem {i:Nat} (hi:i<502) {x:T} (h:x∈sat (state i)) : K4Orbit.norm x∈0::state i := by
  have leng : i<stages3.length := by change i<502;exact hi
  have mem : state i∈stages3 := by rw [state,List.getD_eq_getElem _ _ leng];exact List.getElem_mem _
  have even : ∀v∈state i,K4Orbit.norm v=v := by
    intro v hv
    have hs : evenState (state i)=true := List.all_eq_true.mp canonEven _ mem
    have bit : (!(v.getLsbD 0))=true := List.all_eq_true.mp hs v hv
    have low : v[0]=false := by
      change v.getLsbD 0=false
      cases eq:v.getLsbD 0 <;> simp_all
    simp [K4Orbit.norm,low]
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at h
  rcases h with rfl|rfl|old|⟨y,hy,rfl⟩
  · exact List.mem_cons_self ..
  · exact List.mem_cons_self ..
  · rw [even _ old];exact List.mem_cons_of_mem _ old
  · rw [normNeg,even _ hy];exact List.mem_cons_of_mem _ hy

set_option maxRecDepth 32768 in
theorem historySplit (r:Run 6 base (z0,z1)) :
    ∃i,i<502 ∧ ∃ t∈variants,Reach 3 (state i) t ∧ Confined (0::state i) 3 3 base (t,z1) := by
  have init : AtState 0 0 6 z0 := ⟨base,.start,(by
    have hr : base.all (fun x=>decide (x.1∈sat (state 0)))=true := by decide +kernel
    intro x hx;exact of_decide_eq_true (List.all_eq_true.mp hr x hx)),r⟩
  obtain ⟨j,hj,t,ht,r1⟩ := shift (by decide : 0<36) init (by decide +kernel : z0∈variants)
  change j<4 at hj
  obtain ⟨k,hk,u,hu,r2⟩ := shift (by omega : j<36) r1 ht
  have k36 : k<36 := by unfold limit at hk;split_ifs at hk <;>omega
  obtain ⟨i,hi,v,hv,r3⟩ := shift k36 r2 hu
  have bound : i<502 := by unfold limit at hi;split_ifs at hi <;>omega
  obtain ⟨s,pr,inc,tail⟩ := r3
  exact ⟨i,bound,v,hv,tailLow inc tail,
    appendHist pr (fun x hx=>normMem bound (inc x hx)) (.done tail)⟩
end GuardPair

namespace GuardDep
open K4Core
def Dep (u a b c : T) := ∀ i j:Fin 16, a[i.val]=a[j.val] → b[i.val]=b[j.val] →
  (c)[i.val]=(c)[j.val] → u[i.val]=u[j.val]

theorem dep_neg {u a b c} (h:Dep u a b c) : Dep (neg u) a b c := by
  intro i j x y z
  simp [neg,h i j x y z]

theorem dep0 {s:List T} {g z:T} (hg:g∈combs s) (hz:z∈sat (g::s)) :
    ∃a∈sat s,∃b∈sat s, ∀i j:Fin 16, a[i.val]=a[j.val] → b[i.val]=b[j.val] → z[i.val]=z[j.val] := by
  rcases K4Core.ext hz with h|rfl|rfl
  · exact ⟨z,h,z,h,fun _ _ x _ => x⟩
  all_goals
    obtain ⟨a,ha,w⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp w
    refine ⟨a,ha,b,hb,?_⟩
    intro i j hi hj
    simp [neg,hi,hj]

theorem dep2 {s:List T} {z:T} (r:Reach 2 s z) :
    ∃a∈sat s,∃b∈sat s,∃c∈sat s, Dep z a b c := by
  cases r with | @step _ _ g _ hg r =>
    cases r with | @step _ _ h _ hh r =>
      cases r with | done hz =>
        rcases K4Core.ext hz with old|rfl|rfl
        · obtain ⟨a,ha,b,hb,q⟩ := dep0 hg old
          exact ⟨a,ha,b,hb,b,hb,fun i j x y _=>q i j x y⟩
        all_goals
          obtain ⟨x,hx,w⟩ := List.mem_flatMap.mp hh
          obtain ⟨y,hy,rfl⟩ := List.mem_map.mp w
          obtain ⟨a,ha,z,hz,e⟩ := fac hx hy
          obtain ⟨b,hb,c,hc,q⟩ := dep0 hg hz
          refine ⟨a,ha,b,hb,c,hc,?_⟩
          rw [e]
          intro i j x y w
          simp [neg,x,q i j y w]

def E (x t:T) := ∀ i j:Fin 16, t[i.val]=t[j.val] → x[i.val]=x[j.val]
theorem reflE (x:T) : E x x := fun _ _ h=>h
theorem negE (x:T) : E (neg x) x := by
  intro i j h; simp [neg,h]
theorem oldOr {s:List T} {g x:T} (h:x∈sat (g::s)) : x∈sat s ∨ E x g := by
  rcases K4Core.ext h with old|rfl|rfl
  · exact Or.inl old
  · exact Or.inr (reflE _)
  · exact Or.inr (negE _)

theorem dep3 {s:List T} {z:T} (r:Reach 3 s z) :
    ∃a∈sat s,∃b∈sat s,∃g∈combs s,Dep z a b g := by
  cases r with | @step _ _ g _ hg r =>
    obtain ⟨a,ha,b,hb,c,hc,d⟩ := dep2 r
    have hz : (0:T)∈sat s := by simp [sat]
    rcases oldOr ha with ap|ae <;> rcases oldOr hb with bp|be <;> rcases oldOr hc with cp|ce
    · have gg : c∈combs s := by simpa using meetmem cp cp
      exact ⟨a,ap,b,bp,c,gg,d⟩
    · exact ⟨a,ap,b,bp,g,hg,fun i j x y w=>d i j x y (ce i j w)⟩
    · exact ⟨a,ap,c,cp,g,hg,fun i j x y w=>d i j x (be i j w) y⟩
    · exact ⟨a,ap,a,ap,g,hg,fun i j x _ w=>d i j x (be i j w) (ce i j w)⟩
    · exact ⟨b,bp,c,cp,g,hg,fun i j x y w=>d i j (ae i j w) x y⟩
    · exact ⟨b,bp,b,bp,g,hg,fun i j x _ w=>d i j (ae i j w) x (ce i j w)⟩
    · exact ⟨c,cp,c,cp,g,hg,fun i j x _ w=>d i j (ae i j w) (be i j w) x⟩
    · exact ⟨0,hz,0,hz,g,hg,fun i j _ _ w=>d i j (ae i j w) (be i j w) (ce i j w)⟩
end GuardDep

namespace GuardDep
open K4Core
def marks (w:List T) (f:T→Bool) : Nat := w.foldr (fun u t=>t*2+(f u).toNat) 0
theorem markGet (w:List T) (f:T→Bool) (i:Nat) (hi:i<w.length) :
    (marks w f).testBit i=f w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [marks,List.foldr_cons,List.getElem_cons_zero]
      cases e:f a <;> simp [e,Nat.testBit_zero]
    | succ i =>
      change ((marks l f)*2+(f a).toNat).testBit (i+1) = _
      rw [Nat.testBit_succ]
      have d : ((marks l f)*2+(f a).toNat)/2=marks l f := by cases f a <;> simp <;> omega
      rw [d]
      exact ih i (by simpa using hi)
abbrev ERow := Fin 16 × Fin 16 × Nat
def edges (ws:List T) : List ERow :=
  let rows := (List.finRange 16).map (fun i=>(i,marks ws (fun x=>x[i.val])))
  rows.flatMap fun a=>rows.filterMap fun b=>
    if a.1.val < b.1.val then some (a.1,b.1,a.2^^^b.2) else none
theorem edgeSound {ws:List T} {e:ERow} (he:e∈edges ws) (u:Nat) (hu:u<ws.length) :
    e.2.2.testBit u = (ws[u][e.1.val] != ws[u][e.2.1.val]) := by
  obtain ⟨a,ha,rest⟩ := List.mem_flatMap.mp he
  obtain ⟨b,hb,hbval⟩ := List.mem_filterMap.mp rest
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  split at hbval <;> simp_all only [Option.some.injEq,reduceCtorEq]
  subst e
  simp [Nat.testBit_xor,markGet,hu]
def agree (x:T) (e:ERow) := x[e.1.val] == x[e.2.1.val]
def trim (b:T) : List ERow→ Nat→Bool
  | [],k => k != 0
  | e::es,k => if k=0 then false else trim b es (if agree b e then k &&& e.2.2 else k)
theorem trimKeep {b:T} (es:List ERow) {u k:Nat} (hk:k.testBit u=true)
    (surv:∀e∈es,agree b e=true → e.2.2.testBit u=true) : trim b es k=true := by
  induction es generalizing k with
  | nil =>
    have ne : k≠0 := by intro h; simp [h] at hk
    simp [trim,ne]
  | cons e l ih =>
    have ne : k≠0 := by intro h; simp [h] at hk
    rw [trim,ite_eq_right_iff.mpr (fun h=>(ne h).elim)]
    apply ih
    · split <;> rename_i h
      · simp [Nat.testBit_and,hk,surv e (List.mem_cons_self ..) h]
      · exact hk
    · exact fun x hx=>surv x (List.mem_cons_of_mem _ hx)

def quick (s:List T) (t:T) : Bool :=
  let ws := combs s
  let initial := marks ws (fun _=>true)
  let es := (edges ws).filter fun e=>!(agree t e)
  let old := 0::s
  old.any fun a=>
    let left := es.filter (agree a)
    old.any fun b=>trim b left initial
theorem representative {s:List T} {x:T} (h:x∈sat s) : ∃a∈0::s,E x a := by
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at h
  rcases h with rfl|rfl|p|⟨y,hy,rfl⟩
  · exact ⟨0,List.mem_cons_self ..,reflE _⟩
  · exact ⟨0,List.mem_cons_self ..,negE 0⟩
  · exact ⟨_,List.mem_cons_of_mem _ p,reflE _⟩
  · exact ⟨_,List.mem_cons_of_mem _ hy,negE _⟩
theorem quickOf {s:List T} {t:T} (h:Reach 3 s t) : quick s t=true := by
  obtain ⟨a,ha,b,hb,c,hc,dep⟩ := dep3 h
  obtain ⟨u,hu,ua⟩ := representative ha
  obtain ⟨v,hv,vb⟩ := representative hb
  obtain ⟨idx,ib,eq⟩ := List.mem_iff_getElem.mp hc
  unfold quick
  refine List.any_eq_true.mpr ⟨u,hu,List.any_eq_true.mpr ⟨v,hv,?_⟩⟩
  apply trimKeep (u:=idx) _ (markGet _ (fun _=>true) idx ib)
  intro e he ve
  have el := List.mem_filter.mp he
  have info := List.mem_filter.mp el.1
  rw [edgeSound info.1 _ ib,eq]
  by_contra! no
  have ec : (c)[e.1.val]=(c)[e.2.1.val] := by simpa using no
  have same := dep _ _ (ua _ _ (beq_iff_eq.mp el.2)) (vb _ _ (beq_iff_eq.mp ve)) ec
  simpa [agree,same] using info.2
end GuardDep

namespace GuardAudit
open K4Core
open GuardPair (variants finishAt)
def winners : List (Nat × T) := [(68,65236),(75,65236),(108,65236),(109,65236),(110,65236),(209,65236),(215,65236),(269,64984),(270,63726),(273,63726),(294,64984),(324,65236),(325,65236),(332,60666),(338,60666),(353,64996),(368,65236),(371,65236),(379,65236),(391,63726),(397,63726),(408,64984),(411,64984),(422,64984),(425,64984),(459,63726),(459,65166),(460,63726),(462,65166),(464,63726),(464,64440),(464,64984),(464,65166),(467,65166),(471,63726),(475,65166)]
def valid (v:List T × Nat) : Bool :=
 variants.all fun t=>decide ((v.2,t)∈winners) || !GuardDep.quick v.1 t || !finishAt v.1 t
end GuardAudit

namespace GuardEnd
inductive Trace (allow : Nat → GuardPair.T → Prop) : Nat → List GuardPair.P → GuardPair.P → Prop where
  | done {s p} (h : GuardPair.Lit s p) : Trace allow 0 s p
  | step {k s a b p} (ha : GuardPair.Lit s a) (hb : GuardPair.Lit s b)
    (fresh : (a.1 &&& b.1) ∉ K4Core.sat (s.map Prod.fst))
    (ok : allow (k+1) (K4Orbit.norm (a.1 &&& b.1)))
    (hit : k=0 → K4Orbit.norm (a.1 &&& b.1)=K4Orbit.norm p.1)
    (rest : Trace allow k ((a.1 &&& b.1,a.2 &&& b.2)::s) p) :
    Trace allow (k+1) s p
end GuardEnd

namespace GuardEnd
open GuardPair
abbrev Block := T × List T

def project (x : T) : T := x &&& 279
def flipH (x : T) : T := ~~~x &&& 279

def pol (b : Bool) (x : T) := if b then ~~~x else x
def entry (b : Bool) (u : Block) : Block :=
  (pol b u.1,0::279::(if b then u.2.map flipH else u.2))

def literals (B : List Block) : List Block :=
  (((0,[0])::B).flatMap fun u=>[entry false u,entry true u])

def mult (u v : Block) : Block :=
  (u.1 &&& v.1, (u.2.flatMap fun x=>v.2.map fun y=>x &&& y).eraseDups)

def search (policy : Nat→T→Bool) (target : P) : Nat → List Block → Bool
  | 0,B => (literals B).any fun u=>u.1==target.1 && u.2.contains (project target.2)
  | n+1,B =>
    let lit := literals B
    let known := K4Core.sat (B.map Prod.fst)
    lit.any fun u=>lit.any fun v=>
      let g := u.1 &&& v.1
      if u.1≤v.1 ∧ g∉known ∧ policy (n+1) (K4Orbit.norm g)=true ∧
          (n=0 → K4Orbit.norm g=K4Orbit.norm target.1)
      then search policy target n (mult u v::B)
      else false

def seed : List Block := [(43690,[2]),(52428,[4]),(61680,[16]),(65280,[256])]
end GuardEnd

namespace GuardEnd
open GuardPair
def cases : List (Nat × T) := [(68,65236), (75,65236), (108,65236), (109,65236), (110,65236), (209,65236), (215,65236), (269,64984), (270,63726), (273,63726), (294,64984), (324,65236), (325,65236), (332,60666), (338,60666), (353,64996), (368,65236), (371,65236), (379,65236), (391,63726), (397,63726), (408,64984), (411,64984), (422,64984), (425,64984), (459,63726), (459,65166), (460,63726), (462,65166), (464,63726), (464,64440), (464,64984), (464,65166), (467,65166), (471,63726), (475,65166)]
def fourOK (i : Nat) (t : T) : List T := match i,t.toNat with
  | 68,65236 => [64250]
  | 75,65236 => [52420,64080]
  | 108,65236 => [61166,64250,64764]
  | 109,65236 => [61166,64250,64764]
  | 110,65236 => [61166,64250,64764]
  | 209,65236 => [64250]
  | 215,65236 => [50372,64080]
  | 269,64984 => [56712,61520,62960]
  | 270,63726 => [35054,61440]
  | 273,63726 => [35054,61440]
  | 294,64984 => [21760,63704]
  | 324,65236 => [42,65278]
  | 325,65236 => [42,65278]
  | 332,60666 => [21760]
  | 338,60666 => [21760]
  | 353,64996 => [2570]
  | 368,65236 => [34,8738,65268]
  | 371,65236 => [49344,65108]
  | 379,65236 => [49344,65108]
  | 391,63726 => [35054,61440,63736]
  | 397,63726 => [34952,61678]
  | 408,64984 => [65520]
  | 411,64984 => [65520]
  | 422,64984 => [546,65530]
  | 425,64984 => [546,2184,34952,62800,65530]
  | 459,63726 => [238,30464,63624]
  | 459,65166 => [3598,28784,63624]
  | 460,63726 => [238,1792,63488,65518]
  | 462,65166 => [240,28784,65416]
  | 464,63726 => [61166]
  | 464,64440 => [65520]
  | 464,64984 => [65520]
  | 464,65166 => [61166]
  | 467,65166 => [61166]
  | 471,63726 => [1792,65518]
  | 475,65166 => [240,28784,65416]
  | _,_ => []
def fiveOK (i : Nat) (t : T) : List T := match i,t.toNat with
  | 68,65236 => [64080]
  | 75,65236 => [52420,64080,65244]
  | 108,65236 => [65278]
  | 109,65236 => [65278]
  | 110,65236 => [65278]
  | 209,65236 => [64080]
  | 215,65236 => [50372,64080]
  | 269,64984 => [56712,61520,62800,63704]
  | 270,63726 => [35054,61440,61610,63692]
  | 273,63726 => [35054,61440]
  | 294,64984 => [21760,56712,62800,63704]
  | 324,65236 => [42,65108,65278]
  | 325,65236 => [42,65108,65278]
  | 332,60666 => [41200]
  | 338,60666 => [41210]
  | 353,64996 => [62880]
  | 368,65236 => [34,53456,61648,65268]
  | 371,65236 => [42,49344,65108]
  | 379,65236 => [42,49344,65108]
  | 391,63726 => [35054,61440,61678,63488,63624]
  | 397,63726 => [34952,35054,61678,63624]
  | 408,64984 => [62800]
  | 411,64984 => [62800]
  | 422,64984 => [546,65530]
  | 425,64984 => [546,2184,34952,62800,65530]
  | 459,63726 => [238,35054,61678,63624]
  | 459,65166 => [3598,36494,63624,65038]
  | 460,63726 => [238,1792,63488,65518]
  | 462,65166 => [112,65038]
  | 464,63726 => [238]
  | 464,64440 => [13104]
  | 464,64984 => [21840]
  | 464,65166 => [3598]
  | 467,65166 => [3598]
  | 471,63726 => [1792,65518]
  | 475,65166 => [112,65038]
  | _,_ => []
def numerical (i : Nat) (t : T) (k : Nat) (g : T) : Bool :=
  if 4≤k then (0 :: K4Orbit.state i).contains g else
  if k=3 then (fourOK i t).contains g else
  if k=2 then (fiveOK i t).contains g else true
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
def checkCase (i:Nat) (t:GuardPair.T) := search (numerical i t) (t,GuardPair.z1) 6 seed
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_68_65236 : checkCase 68 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_75_65236 : checkCase 75 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_108_65236 : checkCase 108 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_109_65236 : checkCase 109 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_110_65236 : checkCase 110 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_209_65236 : checkCase 209 65236=false := by decide +kernel
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_215_65236 : checkCase 215 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_269_64984 : checkCase 269 64984=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_270_63726 : checkCase 270 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_273_63726 : checkCase 273 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_294_64984 : checkCase 294 64984=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_324_65236 : checkCase 324 65236=false := by decide +kernel
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_325_65236 : checkCase 325 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_332_60666 : checkCase 332 60666=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_338_60666 : checkCase 338 60666=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_353_64996 : checkCase 353 64996=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_368_65236 : checkCase 368 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_371_65236 : checkCase 371 65236=false := by decide +kernel
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_379_65236 : checkCase 379 65236=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_391_63726 : checkCase 391 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_397_63726 : checkCase 397 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_408_64984 : checkCase 408 64984=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_411_64984 : checkCase 411 64984=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_422_64984 : checkCase 422 64984=false := by decide +kernel
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_425_64984 : checkCase 425 64984=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_459_63726 : checkCase 459 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_459_65166 : checkCase 459 65166=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_460_63726 : checkCase 460 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_462_65166 : checkCase 462 65166=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_464_63726 : checkCase 464 63726=false := by decide +kernel
end GuardEnd

namespace GuardEnd
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_464_64440 : checkCase 464 64440=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_464_64984 : checkCase 464 64984=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_464_65166 : checkCase 464 65166=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_467_65166 : checkCase 467 65166=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_471_63726 : checkCase 471 63726=false := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem check_475_65166 : checkCase 475 65166=false := by decide +kernel
end GuardEnd

namespace GuardEnd
open GuardPair
theorem projectNot (x : T) : project (~~~x)=flipH (project x) := by
  ext i hi
  simp only [project,flipH,BitVec.getElem_and,BitVec.getElem_not]
  cases (279:T)[i] <;> simp

theorem projectAnd (x y : T) : project (x &&& y)=project x &&& project y := by
  ext i hi
  simp only [project,BitVec.getElem_and]
  cases (279:T)[i] <;> simp

theorem polFlip (b : Bool) (x : T) : ~~~pol b x=pol (!b) x := by cases b <;> simp [pol]

theorem form {s p} (h : Lit s p) :
    ∃ q∈((0,0)::s), ∃ b : Bool, p.1=pol b q.1 ∧
      (p.2=pol b q.2 ∨ p.2=0 ∨ p.2=65535) := by
  induction h with
  | src m => exact ⟨_,List.mem_cons_of_mem _ m,false,rfl,Or.inl rfl⟩
  | zero => exact ⟨_,List.mem_cons_self,false,rfl,Or.inl rfl⟩
  | neg _ ih =>
    obtain ⟨q,m,b,lo,hi⟩ := ih
    refine ⟨q,m,!b,lo ▸ polFlip b _,?_⟩
    rcases hi with e|e|e
    · exact Or.inl (e ▸ polFlip b _)
    · exact Or.inr (Or.inr (congrArg (fun x : T=>~~~x) e))
    · exact Or.inr (Or.inl (congrArg (fun x : T=>~~~x) e))
  | clamp h b ih =>
    obtain ⟨q,m,c,lo,hi⟩ := ih
    refine ⟨q,m,c,lo,Or.inr ?_⟩
    cases b <;> simp

def Matches (u : Block) (p : P) : Prop := p.1=u.1 ∧ project p.2∈u.2

def Covers (B : List Block) (s : List P) : Prop :=
  s.map Prod.fst=B.map Prod.fst ∧ ∀p∈s,∃u∈B, Matches u p

theorem extract {B s} (c : Covers B s) {p} (h : Lit s p) :
    ∃u∈literals B,Matches u p := by
  obtain ⟨q,m,b,lo,hi⟩ := form h
  have v : ∃u∈((0,[0]):Block)::B, Matches u q := by
    rcases List.mem_cons.mp m with rfl|mem
    · exact ⟨_,List.mem_cons_self,rfl,List.mem_cons_self⟩
    · obtain ⟨u,hu,ok⟩ := c.2 q mem
      exact ⟨u,List.mem_cons_of_mem _ hu,ok⟩
  obtain ⟨u,hu,uq,uh⟩ := v
  refine ⟨entry b u,List.mem_flatMap.mpr ⟨_,hu,?_⟩,lo.trans (congrArg _ uq),?_⟩
  · cases b <;> simp
  · rcases hi with e|e|e
    · rw [e];cases b
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ uh)
      · apply List.mem_cons_of_mem _ (List.mem_cons_of_mem _ _)
        exact List.mem_map.mpr ⟨_,uh,(projectNot _).symm⟩
    · rw [e];exact List.mem_cons_self
    · rw [e];exact List.mem_cons_of_mem _ List.mem_cons_self

theorem multGood {u v : Block} {a b : P} (ha : Matches u a) (hb : Matches v b) :
    Matches (mult u v) (a.1 &&& b.1,a.2 &&& b.2) := by
  refine ⟨congrArg₂ (· &&& ·) ha.1 hb.1,?_⟩
  change project (a.2 &&& b.2) ∈ (_:List T).eraseDups
  rw [List.mem_eraseDups,projectAnd]
  exact List.mem_flatMap.mpr ⟨_,ha.2,List.mem_map.mpr ⟨_,hb.2,rfl⟩⟩

theorem extend {s B u p} (hs : Covers B s) (hp : Matches u p) : Covers (u::B) (p::s) := by
  refine ⟨by simp [hp.1,hs.1],?_⟩
  rintro q hq
  rcases List.mem_cons.mp hq with rfl|m
  · exact ⟨u,List.mem_cons_self,hp⟩
  · obtain ⟨w,hw,e⟩ := hs.2 q m
    exact ⟨w,List.mem_cons_of_mem _ hw,e⟩

theorem complete {policy : Nat→T→Bool} {target k s} (h : Trace (fun n g=>policy n g=true) k s target)
    {B} (cover : Covers B s) : search policy target k B=true := by
  induction h generalizing B with
  | done val =>
    obtain ⟨u,hu,l,r⟩ := extract cover val
    exact List.any_eq_true.mpr ⟨_,hu,by simp [l,r]⟩
  | @step n s a b p ha hb fresh ok hit tail ih =>
    obtain ⟨u,hu,ua⟩ := extract cover ha
    obtain ⟨v,hv,vb⟩ := extract cover hb
    have main {x y : Block} (hx : x∈literals B) (hy : y∈literals B) (order : x.1≤y.1)
        (fit : Matches (mult x y) (a.1 &&& b.1,a.2 &&& b.2)) :
        search policy p (n+1) B=true := by
      have eq : x.1 &&& y.1=a.1 &&& b.1 := fit.1.symm
      simp only [search,List.any_eq_true]
      refine ⟨x,hx,y,hy,?_⟩
      have gate : x.1 &&& y.1 ∉ K4Core.sat (B.map Prod.fst) := by rwa [eq,←cover.1]
      have next : policy (n+1) (K4Orbit.norm (x.1 &&& y.1))=true := by rwa [eq]
      have ends : n=0 → K4Orbit.norm (x.1 &&& y.1)=K4Orbit.norm p.1 := by rwa [eq]
      rw [if_pos ⟨order,gate,next,ends⟩]
      exact ih (extend cover fit)
    by_cases order : u.1≤v.1
    · exact main hu hv order (multGood ua vb)
    · apply main hv hu ((BitVec.le_total _ _).resolve_left order)
      have z := multGood vb ua
      simpa only [BitVec.and_comm b.1 a.1,BitVec.and_comm b.2 a.2] using z

theorem start : Covers seed base := by
  refine ⟨rfl,?_⟩
  intro p hp
  simp only [base,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  all_goals
    simp [seed,Matches,project]
end GuardEnd

namespace GuardEnd
open GuardPair
theorem checkedEnd {i : Nat} {t : T} (h : (i,t)∈cases) : checkCase i t=false := by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact check_68_65236
  · exact check_75_65236
  · exact check_108_65236
  · exact check_109_65236
  · exact check_110_65236
  · exact check_209_65236
  · exact check_215_65236
  · exact check_269_64984
  · exact check_270_63726
  · exact check_273_63726
  · exact check_294_64984
  · exact check_324_65236
  · exact check_325_65236
  · exact check_332_60666
  · exact check_338_60666
  · exact check_353_64996
  · exact check_368_65236
  · exact check_371_65236
  · exact check_379_65236
  · exact check_391_63726
  · exact check_397_63726
  · exact check_408_64984
  · exact check_411_64984
  · exact check_422_64984
  · exact check_425_64984
  · exact check_459_63726
  · exact check_459_65166
  · exact check_460_63726
  · exact check_462_65166
  · exact check_464_63726
  · exact check_464_64440
  · exact check_464_64984
  · exact check_464_65166
  · exact check_467_65166
  · exact check_471_63726
  · exact check_475_65166
theorem noFresh {i : Nat} {t : T} (hc : (i,t)∈cases)
    (h : Trace (fun k g=>numerical i t k g=true) 6 base (t,z1)) : False := by
  have hit := complete h start
  change checkCase i t=true at hit
  simp [checkedEnd hc] at hit
end GuardEnd

namespace GuardEnd
open GuardPair K4Core K4Orbit
private abbrev first (s : List P) := s.map Prod.fst
private def Lower (n : Nat) (s : List P) (p : P) := ∀ u, Reach u (first s) p.1 → n ≤ u

private theorem fstLit {s p} (h : Lit s p) : p.1∈sat (first s) := by
  induction h with
  | src hs =>
    simp only [sat,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨_,hs,rfl⟩)))
  | zero => exact List.mem_cons_self
  | neg _ ih => exact negmem ih
  | clamp _ _ ih => exact ih

private theorem fstRun {n s p} (h : Run n s p) : Reach n (first s) p.1 := by
  induction h with
  | done hp => exact .done (fstLit hp)
  | step ha hb _ ih => exact .step (meetmem (fstLit ha) (fstLit hb)) ih

private theorem fstConf {n k s p allowed} (h : Confined allowed n k s p) :
    Reach (n+k) (first s) p.1 := by
  induction h with
  | done hr => simpa using fstRun hr
  | step ha hb _ _ ih => simpa [Nat.succ_add] using Reach.step (meetmem (fstLit ha) (fstLit hb)) ih

private theorem normNeg (t : GuardPair.T) : K4Orbit.norm (neg t)=K4Orbit.norm t := by
  unfold K4Orbit.norm
  cases h : t[0] <;> simp [neg,h]

private theorem keepLower {k : Nat} {s : List P} {a b p : P} (h : Lower (k+1) s p) (ha : Lit s a) (hb : Lit s b) :
    Lower k ((a.1 &&& b.1,a.2 &&& b.2)::s) p := by
  intro u r
  have h' := h (u+1) (Reach.step (meetmem (fstLit ha) (fstLit hb)) r)
  omega

private theorem freshStep {k : Nat} {s : List P} {a b p : P} (h : Lower (k+1) s p)
    (tail : Reach k ((a.1 &&& b.1)::first s) p.1) : (a.1 &&& b.1) ∉ sat (first s) := by
  intro old
  have small : Reach k (first s) p.1 := monoReach (fun v hv=>by
    rcases K4Core.ext hv with prior|rfl|rfl
    · exact prior
    · exact old
    · exact negmem old) tail
  have := h k small
  omega

private theorem hits {k : Nat} {s : List P} {a b p : P} (h : Lower (k+1) s p)
    (tail : Reach k ((a.1 &&& b.1)::first s) p.1) (e : k=0) : K4Orbit.norm (a.1 &&& b.1)=K4Orbit.norm p.1 := by
  subst k
  cases tail with
  | done hp =>
    rcases K4Core.ext hp with ho|hg|hg
    · have := h 0 (Reach.done ho)
      omega
    · rw [hg]
    · rw [hg,normNeg]

private theorem tailFree {allow : Nat → GuardPair.T → Prop} {n s p} (h : Run n s p)
    (lb : Lower n s p) (openGate : ∀ k≤n, ∀ g, allow k g) : Trace allow n s p := by
  induction h with
  | done hp => exact .done hp
  | @step k s a b p ha hb tail ih =>
    have r := fstRun tail
    exact .step ha hb (freshStep (a:=a) (b:=b) lb r) (openGate _ le_rfl _) (hits (a:=a) (b:=b) lb r)
      (ih (keepLower lb ha hb) (fun u hu=>openGate u (by omega)))

private theorem confinedToTrace {allowed : List GuardPair.T} {n q s p} (h : Confined allowed n q s p)
    (lb : Lower (n+q) s p) :
    Trace (fun k g=>k≥q+1 → g∈allowed) (n+q) s p := by
  induction h with
  | done r =>
    simp only [Nat.zero_add] at lb ⊢
    exact tailFree r lb (fun k h g hg=>by omega)
  | @step n q s a b p ha hb mem tail ih =>
    have r := fstConf tail
    have l : Lower ((n+q)+1) s p := by simpa [Nat.succ_add] using lb
    rw [Nat.succ_add]
    exact .step ha hb (freshStep (a:=a) (b:=b) l r) (fun _=>mem) (hits (a:=a) (b:=b) l r) (ih (keepLower l ha hb))

theorem fromConfined {i : Nat} {t0 : GuardPair.T} (mem : t0 ∈ variants)
    (hr : Confined (0::state i) 3 3 base (t0,z1)) :
    Trace (fun k g=>k≥4 → g∈0::state i) 6 base (t0,z1) := by
  apply confinedToTrace hr
  intro k r
  exact variantLower mem r
end GuardEnd

namespace GuardEnd
open GuardPair hiding T
open K4Core K4Orbit
def cutFour (i : Nat) (t : T) :=
  (combs (state i)).all fun g =>
    !two (norm g::state i) t (neg t) || (fourOK i t).contains (norm g)
def cutFive (i : Nat) (t : T) :=
  (fourOK i t).all fun g =>
    (combs (g::state i)).all fun h =>
      !one (sat (norm h::g::state i)) t (neg t) || (fiveOK i t).contains (norm h)
def cutBase (i : Nat) := base.all fun p => (sat (state i)).contains p.1

end GuardEnd

namespace GuardEnd
open GuardPair hiding T
open K4Core K4Orbit

abbrev Account (s : List P) (bank : List T) := ∀ p∈s,p.1∈sat bank

theorem put {s : List P} {bank : List T} {p : P} (before : Account s bank) :
    Account (p::s) (norm p.1::bank) := by
  intro q h
  rcases List.mem_cons.mp h with rfl | rest
  · exact enclose _ (by simp [sat])
  · exact src (fun x hx=>List.mem_cons_of_mem _ hx) (before _ rest)

theorem putOld {s : List P} {bank : List T} {p : P} (before : Account s bank)
    (hm : norm p.1 ∈ 0::bank) : Account (p::s) bank := by
  intro q h
  rcases List.mem_cons.mp h with rfl | rest
  · have hnorm : norm q.1 ∈ sat bank := by
      rcases List.mem_cons.mp hm with e|h
      · rw [e];simp [sat]
      · simp [sat,h]
    unfold K4Orbit.norm at hnorm
    split at hnorm
    · simpa [neg] using negmem hnorm
    · exact hnorm
  · exact before _ rest

theorem lowRun {allow k s p bank} (r : Trace allow k s p) (inc : Account s bank) : Reach k bank p.1 := by
  induction r generalizing bank with
  | done hx => exact .done (GuardPair.lowLit inc hx)
  | @step k s a b p ha hb fr ok hit rest ih =>
    apply Reach.step (meetmem (GuardPair.lowLit inc ha) (GuardPair.lowLit inc hb))
    apply ih
    intro q h
    rcases List.mem_cons.mp h with rfl|old
    · simp [sat]
    · exact src (fun x hx=>List.mem_cons_of_mem _ hx) (inc _ old)

theorem lastTwo {s t} (h : Reach 2 s t) : two s t (neg t)=true := by
  cases h with | step a r =>
    cases r with | step b q =>
      cases q with | done x => exact two_all a b x (by simp [fits,neg])
theorem lastOne {s t} (h : Reach 1 s t) : one (sat s) t (neg t)=true := by
  cases h with | step a r =>
    cases r with | done x => exact newOne a x (by simp [fits,neg])

theorem strengthenTail (i : Nat) (t : T) (c4 : cutFour i t=true) (c5 : cutFive i t=true)
    {allow s} (inc : Account s (state i)) (r : Trace allow 3 s (t,z1)) :
    Trace (fun k g=>numerical i t k g=true) 3 s (t,z1) := by
  cases r with | @step _ _ a b _ ha hb fr _ hit rest =>
    let g := norm (a.1 &&& b.1)
    have hg := meetmem (GuardPair.lowLit inc ha) (GuardPair.lowLit inc hb)
    have inc' := put (p:=(a.1 &&& b.1,a.2 &&& b.2)) inc
    have small := lastTwo (lowRun rest inc')
    have m := List.all_eq_true.mp c4 _ hg
    have gmem : g∈fourOK i t := by simpa [g,small] using m
    refine .step ha hb fr (by simpa [numerical] using gmem) hit ?_
    cases rest with | @step _ _ x y _ hx hy fr2 _ hit2 fin =>
      have hh := meetmem (GuardPair.lowLit inc' hx) (GuardPair.lowLit inc' hy)
      have inc'' := put (p:=(x.1 &&& y.1,x.2 &&& y.2)) inc'
      have small2 := lastOne (lowRun fin inc'')
      have m2 := List.all_eq_true.mp (List.all_eq_true.mp c5 _ gmem) _ hh
      have hmem : norm (x.1 &&& y.1)∈fiveOK i t := by simpa [g,small2] using m2
      refine .step hx hy fr2 (by simpa [numerical] using hmem) hit2 ?_
      cases fin with | step aa bb fr3 _ hit3 done =>
        refine .step aa bb fr3 (by rfl) hit3 ?_
        cases done with | done hd => exact .done hd

theorem strengthenMore (i : Nat) (t : T) (c4 : cutFour i t=true) (c5 : cutFive i t=true)
    (n : Nat) {s} (inc : Account s (state i))
    (r : Trace (fun k g=>4≤k → g∈0::state i) (n+3) s (t,z1)) :
    Trace (fun k g=>numerical i t k g=true) (n+3) s (t,z1) := by
  induction n generalizing s with
  | zero => exact strengthenTail i t c4 c5 inc r
  | succ n ih =>
    cases r with | @step _ _ a b _ ha hb fr ok hit rest =>
      have sz : 4≤n+3+1 := by omega
      have hm := ok sz
      refine .step ha hb fr (by simpa [numerical,sz] using hm) hit ?_
      exact ih (putOld inc hm) rest

end GuardEnd

namespace GuardEnd
def cutsValid (p : Nat × GuardPair.T) := cutBase p.1 && cutFour p.1 p.2 && cutFive p.1 p.2
def batch0 : List (Nat × GuardPair.T) := [(68,65236), (75,65236), (108,65236)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass0 : batch0.all cutsValid = true := by decide +kernel
def batch1 : List (Nat × GuardPair.T) := [(109,65236), (110,65236), (209,65236)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass1 : batch1.all cutsValid = true := by decide +kernel
def batch2 : List (Nat × GuardPair.T) := [(215,65236), (269,64984), (270,63726)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass2 : batch2.all cutsValid = true := by decide +kernel
def batch3 : List (Nat × GuardPair.T) := [(273,63726), (294,64984), (324,65236)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass3 : batch3.all cutsValid = true := by decide +kernel
def batch4 : List (Nat × GuardPair.T) := [(325,65236), (332,60666), (338,60666)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass4 : batch4.all cutsValid = true := by decide +kernel
def batch5 : List (Nat × GuardPair.T) := [(353,64996), (368,65236), (371,65236)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass5 : batch5.all cutsValid = true := by decide +kernel
def batch6 : List (Nat × GuardPair.T) := [(379,65236), (391,63726), (397,63726)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass6 : batch6.all cutsValid = true := by decide +kernel
def batch7 : List (Nat × GuardPair.T) := [(408,64984), (411,64984), (422,64984)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass7 : batch7.all cutsValid = true := by decide +kernel
def batch8 : List (Nat × GuardPair.T) := [(425,64984), (459,63726), (459,65166)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass8 : batch8.all cutsValid = true := by decide +kernel
def batch9 : List (Nat × GuardPair.T) := [(460,63726), (462,65166), (464,63726)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass9 : batch9.all cutsValid = true := by decide +kernel
def batch10 : List (Nat × GuardPair.T) := [(464,64440), (464,64984), (464,65166)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass10 : batch10.all cutsValid = true := by decide +kernel
def batch11 : List (Nat × GuardPair.T) := [(467,65166), (471,63726), (475,65166)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem cutPass11 : batch11.all cutsValid = true := by decide +kernel
theorem allCut : cases.all cutsValid = true := by
  change (batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6 ++ batch7 ++ batch8 ++ batch9 ++ batch10 ++ batch11).all cutsValid=true
  simp only [List.all_append,cutPass0,cutPass1,cutPass2,cutPass3,cutPass4,cutPass5,cutPass6,cutPass7,cutPass8,cutPass9,cutPass10,cutPass11,Bool.and_self]
end GuardEnd

namespace GuardEnd
open GuardPair K4Core K4Orbit
theorem upgrade {i t} (hcase : (i,t)∈cases)
    (h : Trace (fun k g=>4≤k → g∈0::state i) 6 base (t,z1)) :
    Trace (fun k g=>numerical i t k g=true) 6 base (t,z1) := by
  have passed := List.all_eq_true.mp allCut _ hcase
  change (cutBase i && cutFour i t && cutFive i t)=true at passed
  simp only [Bool.and_eq_true] at passed
  apply strengthenMore i t passed.1.2 passed.2 3 _ h
  intro p hp
  simpa using List.all_eq_true.mp passed.1.1 p hp
end GuardEnd

namespace GuardPair
theorem fromClasses (cl : ∀ {i t},i<502 → t∈variants → K4Core.Reach 3 (K4Orbit.state i) t → (i,t)∈GuardAudit.winners) : ¬Run 6 base (z0,z1) := by
  intro r
  obtain ⟨i,hi,t,ht,lower,confined⟩ := historySplit r
  have hc : (i,t)∈GuardEnd.cases := by
    change (i,t)∈GuardAudit.winners
    exact cl hi ht lower
  exact GuardEnd.noFresh hc (GuardEnd.upgrade hc (GuardEnd.fromConfined ht confined))
end GuardPair

namespace GuardDep
open K4Core
open GuardPair (finishAt fromTail)
def shrink (b:T) : List ERow→Nat→Nat
  | [],k => k
  | e::es,k => if k=0 then 0 else shrink b es (if agree b e then k &&& e.2.2 else k)
theorem keepBit {b:T} (es:List ERow) {u k:Nat} (hk:k.testBit u=true)
    (surv:∀e∈es,agree b e=true → e.2.2.testBit u=true) : (shrink b es k).testBit u=true := by
  induction es generalizing k with
  | nil => exact hk
  | cons e l ih =>
    have ne : k≠0 := by intro h;simp [h] at hk
    rw [shrink,ite_eq_right_iff.mpr (fun h=>(ne h).elim)]
    apply ih
    · split <;> rename_i h
      · simp [Nat.testBit_and,hk,surv e (List.mem_cons_self ..) h]
      · exact hk
    · exact fun x hx=>surv x (List.mem_cons_of_mem _ hx)

def joined {α} (l:List α) (f:α→Nat) := l.foldr (fun x a=>f x ||| a) 0
theorem joinedBit {α} (l:List α) (f:α→Nat) {u} {x:α} (hx:x∈l) (h:(f x).testBit u=true) :
    (joined l f).testBit u=true := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    change (f a ||| joined l f).testBit u=true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp hx with rfl|old
    · simp [h]
    · simp [ih old]

def candidates (s:List T) (t:T) : Nat :=
  let ws := combs s
  let initial := marks ws (fun _=>true)
  let es := (edges ws).filter fun e=>!(agree t e)
  let old := 0::s
  joined old fun a=>
    let left := es.filter (agree a)
    joined old fun b=>shrink b left initial

theorem selected {s:List T} {a b t:T} {idx:Nat} (ib:idx<(combs s).length)
    (ha:a∈sat s) (hb:b∈sat s) (dep:Dep t a b (combs s)[idx]) : (candidates s t).testBit idx=true := by
  obtain ⟨u,hu,ua⟩ := representative ha
  obtain ⟨v,hv,vb⟩ := representative hb
  unfold candidates
  apply joinedBit _ _ hu
  apply joinedBit _ _ hv
  apply keepBit _ (markGet _ (fun _=>true) idx ib)
  intro e he ve
  have el := List.mem_filter.mp he
  have info := List.mem_filter.mp el.1
  rw [edgeSound info.1 _ ib]
  by_contra! no
  have ec : (combs s)[idx][e.1.val]=(combs s)[idx][e.2.1.val] := by simpa using no
  have same := dep _ _ (ua _ _ (beq_iff_eq.mp el.2)) (vb _ _ (beq_iff_eq.mp ve)) ec
  simpa [agree,same] using info.2

def usable (s:List T) (t:T) : List T :=
  let kept := candidates s t
  ((combs s).zipIdx.filter (fun gi=>kept.testBit gi.2)).map Prod.fst
theorem usableOf {s:List T} {a b c t:T} (ha:a∈sat s) (hb:b∈sat s) (hc:c∈combs s)
    (dep:Dep t a b c) : c∈usable s t := by
  obtain ⟨i,ib,eq⟩ := List.mem_iff_getElem.mp hc
  apply List.mem_map.mpr ⟨(c,i),?_,rfl⟩
  apply List.mem_filter.mpr
  constructor
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    rw [List.getElem?_eq_getElem ib,eq]
  · apply selected ib ha hb
    rw [eq];exact dep

theorem separateGate {s:List T} {g t:T} (r:Reach 2 (g::s) t) :
   (∃a∈sat s,∃b∈sat s,∃c∈sat s,Dep t a b c) ∨ (∃a∈sat s,∃b∈sat s,Dep t a b g) := by
  obtain ⟨a,ha,b,hb,c,hc,d⟩ := dep2 r
  have hz : (0:T)∈sat s := by simp [sat]
  rcases oldOr ha with ap|ae <;> rcases oldOr hb with bp|be <;> rcases oldOr hc with cp|ce
  · exact Or.inl ⟨a,ap,b,bp,c,cp,d⟩
  · exact Or.inr ⟨a,ap,b,bp,fun i j x y w=>d i j x y (ce i j w)⟩
  · exact Or.inr ⟨a,ap,c,cp,fun i j x y w=>d i j x (be i j w) y⟩
  · exact Or.inr ⟨a,ap,a,ap,fun i j x _ w=>d i j x (be i j w) (ce i j w)⟩
  · exact Or.inr ⟨b,bp,c,cp,fun i j x y w=>d i j (ae i j w) x y⟩
  · exact Or.inr ⟨b,bp,b,bp,fun i j x _ w=>d i j (ae i j w) x (ce i j w)⟩
  · exact Or.inr ⟨c,cp,c,cp,fun i j x _ w=>d i j (ae i j w) (be i j w) x⟩
  · exact Or.inr ⟨0,hz,0,hz,fun i j _ _ w=>d i j (ae i j w) (be i j w) (ce i j w)⟩

def pick3 (s:List T) (t:T) : Bool :=
  let ws := usable s t
  if ws.any (fun q=>decide (q∈sat s)) then finishAt s t
  else ws.any (fun q=>two (q::s) t (neg t))
theorem pick3Of {s:List T} {t:T} (h:Reach 3 s t) : pick3 s t=true := by
  change (if (usable s t).any (fun q=>decide (q∈sat s)) then finishAt s t else (usable s t).any (fun q=>two (q::s) t (neg t)))=true
  split <;> rename_i flag
  · exact fromTail h
  · cases h with | @step _ _ g _ hg r =>
      rcases separateGate r with old|⟨a,ha,b,hb,dep⟩
      · obtain ⟨a,ha,b,hb,c,hc,d⟩ := old
        have cc : c∈combs s := by simpa using meetmem hc hc
        exact (flag (List.any_eq_true.mpr ⟨c,usableOf ha hb cc d,decide_eq_true hc⟩)).elim
      · apply List.any_eq_true.mpr ⟨g,usableOf ha hb hg dep,?_⟩
        cases r with | step hh r' =>
          cases r' with | step hi r'' =>
            cases r'' with | done hz =>
              exact two_all hh hi hz (by simp [fits,neg])
end GuardDep

namespace GuardAudit
open K4Core
open GuardPair (variants)
def validFast (v:List T × Nat) := variants.all fun t=>decide ((v.2,t)∈winners) || !GuardDep.pick3 v.1 t
end GuardAudit

namespace GuardAudit
open K4Core
def point0 : List T × Nat := ([43690,52428,61680,65280],0)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item0 : validFast point0=true := by decide +kernel
def point1 : List T × Nat := ([170,43690,52428,61680,65280],1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item1 : validFast point1=true := by decide +kernel
def point2 : List T × Nat := ([34952,43690,52428,61680,65280],2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item2 : validFast point2=true := by decide +kernel
def point3 : List T × Nat := ([43690,52428,61166,61680,65280],3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item3 : validFast point3=true := by decide +kernel
def point4 : List T × Nat := ([10,170,43690,52428,61680,65280],4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item4 : validFast point4=true := by decide +kernel
def point5 : List T × Nat := ([10,43690,52428,61680,65280,65520],5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item5 : validFast point5=true := by decide +kernel
def point6 : List T × Nat := ([136,170,43690,52428,61680,65280],6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item6 : validFast point6=true := by decide +kernel
def point7 : List T × Nat := ([136,34952,43690,52428,61680,65280],7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item7 : validFast point7=true := by decide +kernel
def group0 : List (List T × Nat) := [point0,point1,point2,point3,point4,point5,point6,point7]
theorem pass0 : group0.all validFast=true := by simp only [group0,List.all_cons,List.all_nil,item0,item1,item2,item3,item4,item5,item6,item7,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point8 : List T × Nat := ([170,204,43690,52428,61680,65280],8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item8 : validFast point8=true := by decide +kernel
def point9 : List T × Nat := ([170,2570,43690,52428,61680,65280],9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item9 : validFast point9=true := by decide +kernel
def point10 : List T × Nat := ([170,3084,43690,52428,61680,65280],10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item10 : validFast point10=true := by decide +kernel
def point11 : List T × Nat := ([170,3840,43690,52428,61680,65280],11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item11 : validFast point11=true := by decide +kernel
def point12 : List T × Nat := ([170,21760,43690,52428,61680,65280],12)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item12 : validFast point12=true := by decide +kernel
def point13 : List T × Nat := ([170,34952,43690,52428,61680,65280],13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item13 : validFast point13=true := by decide +kernel
def point14 : List T × Nat := ([170,43520,43690,52428,61680,65280],14)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item14 : validFast point14=true := by decide +kernel
def point15 : List T × Nat := ([170,43690,49344,52428,61680,65280],15)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item15 : validFast point15=true := by decide +kernel
def group1 : List (List T × Nat) := [point8,point9,point10,point11,point12,point13,point14,point15]
theorem pass1 : group1.all validFast=true := by simp only [group1,List.all_cons,List.all_nil,item8,item9,item10,item11,item12,item13,item14,item15,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point16 : List T × Nat := ([170,43690,52224,52428,61680,65280],16)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item16 : validFast point16=true := by decide +kernel
def point17 : List T × Nat := ([170,43690,52292,52428,61680,65280],17)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item17 : validFast point17=true := by decide +kernel
def point18 : List T × Nat := ([170,43690,52428,52462,61680,65280],18)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item18 : validFast point18=true := by decide +kernel
def point19 : List T × Nat := ([170,43690,52428,61166,61680,65280],19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item19 : validFast point19=true := by decide +kernel
def point20 : List T × Nat := ([170,43690,52428,61680,64764,65280],20)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item20 : validFast point20=true := by decide +kernel
def point21 : List T × Nat := ([170,43690,52428,61680,65280,65450],21)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item21 : validFast point21=true := by decide +kernel
def point22 : List T × Nat := ([170,43690,52428,61680,65280,65484],22)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item22 : validFast point22=true := by decide +kernel
def point23 : List T × Nat := ([238,43690,52428,61166,61680,65280],23)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item23 : validFast point23=true := by decide +kernel
def group2 : List (List T × Nat) := [point16,point17,point18,point19,point20,point21,point22,point23]
theorem pass2 : group2.all validFast=true := by simp only [group2,List.all_cons,List.all_nil,item16,item17,item18,item19,item20,item21,item22,item23,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point24 : List T × Nat := ([2730,43690,52428,61440,61680,65280],24)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item24 : validFast point24=true := by decide +kernel
def point25 : List T × Nat := ([32896,34952,43690,52428,61680,65280],25)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item25 : validFast point25=true := by decide +kernel
def point26 : List T × Nat := ([34952,41120,43690,52428,61680,65280],26)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item26 : validFast point26=true := by decide +kernel
def point27 : List T × Nat := ([34952,43690,52428,61166,61680,65280],27)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item27 : validFast point27=true := by decide +kernel
def point28 : List T × Nat := ([34952,43690,52428,61440,61680,65280],28)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item28 : validFast point28=true := by decide +kernel
def point29 : List T × Nat := ([34952,43690,52428,61680,63736,65280],29)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item29 : validFast point29=true := by decide +kernel
def point30 : List T × Nat := ([34952,43690,52428,61680,64250,65280],30)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item30 : validFast point30=true := by decide +kernel
def point31 : List T × Nat := ([34952,43690,52428,61680,65280,65520],31)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item31 : validFast point31=true := by decide +kernel
def group3 : List (List T × Nat) := [point24,point25,point26,point27,point28,point29,point30,point31]
theorem pass3 : group3.all validFast=true := by simp only [group3,List.all_cons,List.all_nil,item24,item25,item26,item27,item28,item29,item30,item31,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point32 : List T × Nat := ([43176,43690,52428,61680,64764,65280],32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item32 : validFast point32=true := by decide +kernel
def point33 : List T × Nat := ([43690,52428,61166,61680,64250,65280],33)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item33 : validFast point33=true := by decide +kernel
def point34 : List T × Nat := ([43690,52428,61166,61680,65278,65280],34)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item34 : validFast point34=true := by decide +kernel
def point35 : List T × Nat := ([43690,52428,61166,61680,65280,65520],35)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item35 : validFast point35=true := by decide +kernel
def point36 : List T × Nat := ([2,10,170,43690,52428,61680,65280],36)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item36 : validFast point36=true := by decide +kernel
def point37 : List T × Nat := ([2,10,43690,52428,61680,65280,65520],37)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item37 : validFast point37=true := by decide +kernel
def point38 : List T × Nat := ([2,170,43690,52428,61680,64764,65280],38)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item38 : validFast point38=true := by decide +kernel
def point39 : List T × Nat := ([2,43690,52428,61680,64764,65280,65532],39)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item39 : validFast point39=true := by decide +kernel
def group4 : List (List T × Nat) := [point32,point33,point34,point35,point36,point37,point38,point39]
theorem pass4 : group4.all validFast=true := by simp only [group4,List.all_cons,List.all_nil,item32,item33,item34,item35,item36,item37,item38,item39,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point40 : List T × Nat := ([8,10,170,43690,52428,61680,65280],40)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item40 : validFast point40=true := by decide +kernel
def point41 : List T × Nat := ([8,10,43690,52428,61680,65280,65520],41)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item41 : validFast point41=true := by decide +kernel
def point42 : List T × Nat := ([8,136,170,43690,52428,61680,65280],42)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item42 : validFast point42=true := by decide +kernel
def point43 : List T × Nat := ([8,136,34952,43690,52428,61680,65280],43)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item43 : validFast point43=true := by decide +kernel
def point44 : List T × Nat := ([8,170,3084,43690,52428,61680,65280],44)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item44 : validFast point44=true := by decide +kernel
def point45 : List T × Nat := ([8,34952,43690,52428,61680,65280,65520],45)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item45 : validFast point45=true := by decide +kernel
def point46 : List T × Nat := ([10,12,43690,52428,61680,65280,65520],46)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item46 : validFast point46=true := by decide +kernel
def point47 : List T × Nat := ([10,34,170,43690,52428,61680,65280],47)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item47 : validFast point47=true := by decide +kernel
def group5 : List (List T × Nat) := [point40,point41,point42,point43,point44,point45,point46,point47]
theorem pass5 : group5.all validFast=true := by simp only [group5,List.all_cons,List.all_nil,item40,item41,item42,item43,item44,item45,item46,item47,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point48 : List T × Nat := ([10,136,170,43690,52428,61680,65280],48)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item48 : validFast point48=true := by decide +kernel
def point49 : List T × Nat := ([10,160,170,43690,52428,61680,65280],49)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item49 : validFast point49=true := by decide +kernel
def point50 : List T × Nat := ([10,170,204,43690,52428,61680,65280],50)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item50 : validFast point50=true := by decide +kernel
def point51 : List T × Nat := ([10,170,240,43690,52428,61680,65280],51)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item51 : validFast point51=true := by decide +kernel
def point52 : List T × Nat := ([10,170,2570,43690,52428,61680,65280],52)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item52 : validFast point52=true := by decide +kernel
def point53 : List T × Nat := ([10,170,3084,43690,52428,61680,65280],53)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item53 : validFast point53=true := by decide +kernel
def point54 : List T × Nat := ([10,170,3840,43690,52428,61680,65280],54)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item54 : validFast point54=true := by decide +kernel
def point55 : List T × Nat := ([10,170,8738,43690,52428,61680,65280],55)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item55 : validFast point55=true := by decide +kernel
def group6 : List (List T × Nat) := [point48,point49,point50,point51,point52,point53,point54,point55]
theorem pass6 : group6.all validFast=true := by simp only [group6,List.all_cons,List.all_nil,item48,item49,item50,item51,item52,item53,item54,item55,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point56 : List T × Nat := ([10,170,12336,43690,52428,61680,65280],56)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item56 : validFast point56=true := by decide +kernel
def point57 : List T × Nat := ([10,170,13056,43690,52428,61680,65280],57)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item57 : validFast point57=true := by decide +kernel
def point58 : List T × Nat := ([10,170,17476,43690,52428,61680,65280],58)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item58 : validFast point58=true := by decide +kernel
def point59 : List T × Nat := ([10,170,20560,43690,52428,61680,65280],59)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item59 : validFast point59=true := by decide +kernel
def point60 : List T × Nat := ([10,170,21760,43690,52428,61680,65280],60)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item60 : validFast point60=true := by decide +kernel
def point61 : List T × Nat := ([10,170,34952,43690,52428,61680,65280],61)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item61 : validFast point61=true := by decide +kernel
def point62 : List T × Nat := ([10,170,41120,43690,52428,61680,65280],62)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item62 : validFast point62=true := by decide +kernel
def point63 : List T × Nat := ([10,170,43520,43690,52428,61680,65280],63)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item63 : validFast point63=true := by decide +kernel
def group7 : List (List T × Nat) := [point56,point57,point58,point59,point60,point61,point62,point63]
theorem pass7 : group7.all validFast=true := by simp only [group7,List.all_cons,List.all_nil,item56,item57,item58,item59,item60,item61,item62,item63,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point64 : List T × Nat := ([10,170,43680,43690,52428,61680,65280],64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item64 : validFast point64=true := by decide +kernel
def point65 : List T × Nat := ([10,170,43690,49344,52428,61680,65280],65)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item65 : validFast point65=true := by decide +kernel
def point66 : List T × Nat := ([10,170,43690,52224,52428,61680,65280],66)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item66 : validFast point66=true := by decide +kernel
def point67 : List T × Nat := ([10,170,43690,52292,52428,61680,65280],67)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item67 : validFast point67=true := by decide +kernel
def point68 : List T × Nat := ([10,170,43690,52420,52428,61680,65280],68)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item68 : validFast point68=true := by decide +kernel
def point69 : List T × Nat := ([10,170,43690,52428,52430,61680,65280],69)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item69 : validFast point69=true := by decide +kernel
def point70 : List T × Nat := ([10,170,43690,52428,52462,61680,65280],70)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item70 : validFast point70=true := by decide +kernel
def point71 : List T × Nat := ([10,170,43690,52428,61166,61680,65280],71)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item71 : validFast point71=true := by decide +kernel
def group8 : List (List T × Nat) := [point64,point65,point66,point67,point68,point69,point70,point71]
theorem pass8 : group8.all validFast=true := by simp only [group8,List.all_cons,List.all_nil,item64,item65,item66,item67,item68,item69,item70,item71,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point72 : List T × Nat := ([10,170,43690,52428,61440,61680,65280],72)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item72 : validFast point72=true := by decide +kernel
def point73 : List T × Nat := ([10,170,43690,52428,61520,61680,65280],73)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item73 : validFast point73=true := by decide +kernel
def point74 : List T × Nat := ([10,170,43690,52428,61680,61690,65280],74)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item74 : validFast point74=true := by decide +kernel
def point75 : List T × Nat := ([10,170,43690,52428,61680,64250,65280],75)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item75 : validFast point75=true := by decide +kernel
def point76 : List T × Nat := ([10,170,43690,52428,61680,64764,65280],76)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item76 : validFast point76=true := by decide +kernel
def point77 : List T × Nat := ([10,170,43690,52428,61680,65280,65290],77)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item77 : validFast point77=true := by decide +kernel
def point78 : List T × Nat := ([10,170,43690,52428,61680,65280,65450],78)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item78 : validFast point78=true := by decide +kernel
def point79 : List T × Nat := ([10,170,43690,52428,61680,65280,65484],79)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item79 : validFast point79=true := by decide +kernel
def group9 : List (List T × Nat) := [point72,point73,point74,point75,point76,point77,point78,point79]
theorem pass9 : group9.all validFast=true := by simp only [group9,List.all_cons,List.all_nil,item72,item73,item74,item75,item76,item77,item78,item79,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point80 : List T × Nat := ([10,170,43690,52428,61680,65280,65520],80)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item80 : validFast point80=true := by decide +kernel
def point81 : List T × Nat := ([10,204,43690,52428,61680,65280,65520],81)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item81 : validFast point81=true := by decide +kernel
def point82 : List T × Nat := ([10,240,43530,43690,52428,61680,65280],82)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item82 : validFast point82=true := by decide +kernel
def point83 : List T × Nat := ([10,240,43690,52428,61680,65280,65520],83)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item83 : validFast point83=true := by decide +kernel
def point84 : List T × Nat := ([10,250,43690,52428,61680,64250,65280],84)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item84 : validFast point84=true := by decide +kernel
def point85 : List T × Nat := ([10,8738,43690,52428,61680,65280,65520],85)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item85 : validFast point85=true := by decide +kernel
def point86 : List T × Nat := ([10,12336,43690,52428,61680,65280,65520],86)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item86 : validFast point86=true := by decide +kernel
def point87 : List T × Nat := ([10,13104,43690,52428,61680,65280,65520],87)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item87 : validFast point87=true := by decide +kernel
def group10 : List (List T × Nat) := [point80,point81,point82,point83,point84,point85,point86,point87]
theorem pass10 : group10.all validFast=true := by simp only [group10,List.all_cons,List.all_nil,item80,item81,item82,item83,item84,item85,item86,item87,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point88 : List T × Nat := ([10,17476,43690,52428,61680,65280,65520],88)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item88 : validFast point88=true := by decide +kernel
def point89 : List T × Nat := ([10,20560,43690,52428,61680,65280,65520],89)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item89 : validFast point89=true := by decide +kernel
def point90 : List T × Nat := ([10,21840,43690,52428,61680,65280,65520],90)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item90 : validFast point90=true := by decide +kernel
def point91 : List T × Nat := ([10,34952,43690,52428,61680,65280,65520],91)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item91 : validFast point91=true := by decide +kernel
def point92 : List T × Nat := ([10,41120,43690,52428,61680,65280,65440],92)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item92 : validFast point92=true := by decide +kernel
def point93 : List T × Nat := ([10,41120,43690,52428,61680,65280,65520],93)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item93 : validFast point93=true := by decide +kernel
def point94 : List T × Nat := ([10,43680,43690,52428,61680,65280,65520],94)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item94 : validFast point94=true := by decide +kernel
def point95 : List T × Nat := ([10,43690,49344,52428,61680,65280,65520],95)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item95 : validFast point95=true := by decide +kernel
def group11 : List (List T × Nat) := [point88,point89,point90,point91,point92,point93,point94,point95]
theorem pass11 : group11.all validFast=true := by simp only [group11,List.all_cons,List.all_nil,item88,item89,item90,item91,item92,item93,item94,item95,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point96 : List T × Nat := ([10,43690,52416,52428,61680,65280,65520],96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item96 : validFast point96=true := by decide +kernel
def point97 : List T × Nat := ([10,43690,52420,52428,61680,65280,65520],97)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item97 : validFast point97=true := by decide +kernel
def point98 : List T × Nat := ([10,43690,52428,52430,61680,65280,65520],98)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item98 : validFast point98=true := by decide +kernel
def point99 : List T × Nat := ([10,43690,52428,61166,61680,65280,65520],99)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item99 : validFast point99=true := by decide +kernel
def point100 : List T × Nat := ([10,43690,52428,61440,61680,65280,65520],100)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item100 : validFast point100=true := by decide +kernel
def point101 : List T × Nat := ([10,43690,52428,61680,61690,65280,65520],101)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item101 : validFast point101=true := by decide +kernel
def point102 : List T × Nat := ([10,43690,52428,61680,64250,65280,65520],102)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item102 : validFast point102=true := by decide +kernel
def point103 : List T × Nat := ([10,43690,52428,61680,64764,65280,65520],103)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item103 : validFast point103=true := by decide +kernel
def group12 : List (List T × Nat) := [point96,point97,point98,point99,point100,point101,point102,point103]
theorem pass12 : group12.all validFast=true := by simp only [group12,List.all_cons,List.all_nil,item96,item97,item98,item99,item100,item101,item102,item103,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point104 : List T × Nat := ([10,43690,52428,61680,65280,65520,65530],104)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item104 : validFast point104=true := by decide +kernel
def point105 : List T × Nat := ([10,43690,52428,61680,65280,65520,65532],105)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item105 : validFast point105=true := by decide +kernel
def point106 : List T × Nat := ([14,238,43690,52428,61166,61680,65280],106)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item106 : validFast point106=true := by decide +kernel
def point107 : List T × Nat := ([14,43690,52428,61166,61680,65280,65520],107)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item107 : validFast point107=true := by decide +kernel
def point108 : List T × Nat := ([42,170,43690,49344,52428,61680,65280],108)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item108 : validFast point108=true := by decide +kernel
def point109 : List T × Nat := ([42,10794,43690,49344,52428,61680,65280],109)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item109 : validFast point109=true := by decide +kernel
def point110 : List T × Nat := ([42,43690,49344,52428,61680,65280,65472],110)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item110 : validFast point110=true := by decide +kernel
def point111 : List T × Nat := ([128,136,170,43690,52428,61680,65280],111)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item111 : validFast point111=true := by decide +kernel
def group13 : List (List T × Nat) := [point104,point105,point106,point107,point108,point109,point110,point111]
theorem pass13 : group13.all validFast=true := by simp only [group13,List.all_cons,List.all_nil,item104,item105,item106,item107,item108,item109,item110,item111,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point112 : List T × Nat := ([128,136,34952,43690,52428,61680,65280],112)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item112 : validFast point112=true := by decide +kernel
def point113 : List T × Nat := ([128,170,43690,49344,52428,61680,65280],113)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item113 : validFast point113=true := by decide +kernel
def point114 : List T × Nat := ([128,32896,34952,43690,52428,61680,65280],114)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item114 : validFast point114=true := by decide +kernel
def point115 : List T × Nat := ([136,160,170,43690,52428,61680,65280],115)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item115 : validFast point115=true := by decide +kernel
def point116 : List T × Nat := ([136,170,204,43690,52428,61680,65280],116)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item116 : validFast point116=true := by decide +kernel
def point117 : List T × Nat := ([136,170,240,43690,52428,61680,65280],117)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item117 : validFast point117=true := by decide +kernel
def point118 : List T × Nat := ([136,170,2570,43690,52428,61680,65280],118)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item118 : validFast point118=true := by decide +kernel
def point119 : List T × Nat := ([136,170,3084,43690,52428,61680,65280],119)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item119 : validFast point119=true := by decide +kernel
def group14 : List (List T × Nat) := [point112,point113,point114,point115,point116,point117,point118,point119]
theorem pass14 : group14.all validFast=true := by simp only [group14,List.all_cons,List.all_nil,item112,item113,item114,item115,item116,item117,item118,item119,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point120 : List T × Nat := ([136,170,3840,43690,52428,61680,65280],120)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item120 : validFast point120=true := by decide +kernel
def point121 : List T × Nat := ([136,170,8738,43690,52428,61680,65280],121)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item121 : validFast point121=true := by decide +kernel
def point122 : List T × Nat := ([136,170,12336,43690,52428,61680,65280],122)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item122 : validFast point122=true := by decide +kernel
def point123 : List T × Nat := ([136,170,13056,43690,52428,61680,65280],123)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item123 : validFast point123=true := by decide +kernel
def point124 : List T × Nat := ([136,170,17476,43690,52428,61680,65280],124)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item124 : validFast point124=true := by decide +kernel
def point125 : List T × Nat := ([136,170,20560,43690,52428,61680,65280],125)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item125 : validFast point125=true := by decide +kernel
def point126 : List T × Nat := ([136,170,21760,43690,52428,61680,65280],126)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item126 : validFast point126=true := by decide +kernel
def point127 : List T × Nat := ([136,170,34952,43690,52428,61680,65280],127)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item127 : validFast point127=true := by decide +kernel
def group15 : List (List T × Nat) := [point120,point121,point122,point123,point124,point125,point126,point127]
theorem pass15 : group15.all validFast=true := by simp only [group15,List.all_cons,List.all_nil,item120,item121,item122,item123,item124,item125,item126,item127,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point128 : List T × Nat := ([136,170,41120,43690,52428,61680,65280],128)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item128 : validFast point128=true := by decide +kernel
def point129 : List T × Nat := ([136,170,43520,43690,52428,61680,65280],129)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item129 : validFast point129=true := by decide +kernel
def point130 : List T × Nat := ([136,170,43554,43690,52428,61680,65280],130)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item130 : validFast point130=true := by decide +kernel
def point131 : List T × Nat := ([136,170,43690,49344,52428,61680,65280],131)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item131 : validFast point131=true := by decide +kernel
def point132 : List T × Nat := ([136,170,43690,52224,52428,61680,65280],132)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item132 : validFast point132=true := by decide +kernel
def point133 : List T × Nat := ([136,170,43690,52292,52428,61680,65280],133)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item133 : validFast point133=true := by decide +kernel
def point134 : List T × Nat := ([136,170,43690,52428,52462,61680,65280],134)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item134 : validFast point134=true := by decide +kernel
def point135 : List T × Nat := ([136,170,43690,52428,61166,61680,65280],135)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item135 : validFast point135=true := by decide +kernel
def group16 : List (List T × Nat) := [point128,point129,point130,point131,point132,point133,point134,point135]
theorem pass16 : group16.all validFast=true := by simp only [group16,List.all_cons,List.all_nil,item128,item129,item130,item131,item132,item133,item134,item135,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point136 : List T × Nat := ([136,170,43690,52428,61440,61680,65280],136)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item136 : validFast point136=true := by decide +kernel
def point137 : List T × Nat := ([136,170,43690,52428,61520,61680,65280],137)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item137 : validFast point137=true := by decide +kernel
def point138 : List T × Nat := ([136,170,43690,52428,61552,61680,65280],138)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item138 : validFast point138=true := by decide +kernel
def point139 : List T × Nat := ([136,170,43690,52428,61680,61688,65280],139)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item139 : validFast point139=true := by decide +kernel
def point140 : List T × Nat := ([136,170,43690,52428,61680,61690,65280],140)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item140 : validFast point140=true := by decide +kernel
def point141 : List T × Nat := ([136,170,43690,52428,61680,64250,65280],141)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item141 : validFast point141=true := by decide +kernel
def point142 : List T × Nat := ([136,170,43690,52428,61680,64764,65280],142)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item142 : validFast point142=true := by decide +kernel
def point143 : List T × Nat := ([136,170,43690,52428,61680,65280,65416],143)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item143 : validFast point143=true := by decide +kernel
def group17 : List (List T × Nat) := [point136,point137,point138,point139,point140,point141,point142,point143]
theorem pass17 : group17.all validFast=true := by simp only [group17,List.all_cons,List.all_nil,item136,item137,item138,item139,item140,item141,item142,item143,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point144 : List T × Nat := ([136,170,43690,52428,61680,65280,65450],144)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item144 : validFast point144=true := by decide +kernel
def point145 : List T × Nat := ([136,170,43690,52428,61680,65280,65484],145)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item145 : validFast point145=true := by decide +kernel
def point146 : List T × Nat := ([136,170,43690,52428,61680,65280,65520],146)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item146 : validFast point146=true := by decide +kernel
def point147 : List T × Nat := ([136,240,34952,43690,52428,61680,65280],147)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item147 : validFast point147=true := by decide +kernel
def point148 : List T × Nat := ([136,2056,34952,43690,52428,61680,65280],148)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item148 : validFast point148=true := by decide +kernel
def point149 : List T × Nat := ([136,2570,34952,43690,52428,61680,65280],149)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item149 : validFast point149=true := by decide +kernel
def point150 : List T × Nat := ([136,3840,34952,43690,52428,61680,65280],150)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item150 : validFast point150=true := by decide +kernel
def point151 : List T × Nat := ([136,8738,34952,43690,52428,61680,65280],151)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item151 : validFast point151=true := by decide +kernel
def group18 : List (List T × Nat) := [point144,point145,point146,point147,point148,point149,point150,point151]
theorem pass18 : group18.all validFast=true := by simp only [group18,List.all_cons,List.all_nil,item144,item145,item146,item147,item148,item149,item150,item151,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point152 : List T × Nat := ([136,8738,43690,52428,61680,65280,65314],152)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item152 : validFast point152=true := by decide +kernel
def point153 : List T × Nat := ([136,8874,43690,52224,52428,61680,65280],153)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item153 : validFast point153=true := by decide +kernel
def point154 : List T × Nat := ([136,12336,34952,43690,52428,61680,65280],154)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item154 : validFast point154=true := by decide +kernel
def point155 : List T × Nat := ([136,13056,34952,43690,52428,61680,65280],155)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item155 : validFast point155=true := by decide +kernel
def point156 : List T × Nat := ([136,28784,34952,43690,52428,61680,65280],156)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item156 : validFast point156=true := by decide +kernel
def point157 : List T × Nat := ([136,30464,34952,43690,52428,61680,65280],157)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item157 : validFast point157=true := by decide +kernel
def point158 : List T × Nat := ([136,32896,34952,43690,52428,61680,65280],158)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item158 : validFast point158=true := by decide +kernel
def point159 : List T × Nat := ([136,34816,34952,43690,52428,61680,65280],159)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item159 : validFast point159=true := by decide +kernel
def group19 : List (List T × Nat) := [point152,point153,point154,point155,point156,point157,point158,point159]
theorem pass19 : group19.all validFast=true := by simp only [group19,List.all_cons,List.all_nil,item152,item153,item154,item155,item156,item157,item158,item159,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point160 : List T × Nat := ([136,34952,41120,43690,52428,61680,65280],160)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item160 : validFast point160=true := by decide +kernel
def point161 : List T × Nat := ([136,34952,43520,43690,52428,61680,65280],161)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item161 : validFast point161=true := by decide +kernel
def point162 : List T × Nat := ([136,34952,43554,43690,52428,61680,65280],162)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item162 : validFast point162=true := by decide +kernel
def point163 : List T × Nat := ([136,34952,43690,52428,61166,61680,65280],163)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item163 : validFast point163=true := by decide +kernel
def point164 : List T × Nat := ([136,34952,43690,52428,61440,61680,65280],164)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item164 : validFast point164=true := by decide +kernel
def point165 : List T × Nat := ([136,34952,43690,52428,61552,61680,65280],165)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item165 : validFast point165=true := by decide +kernel
def point166 : List T × Nat := ([136,34952,43690,52428,61680,61688,65280],166)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item166 : validFast point166=true := by decide +kernel
def point167 : List T × Nat := ([136,34952,43690,52428,61680,63736,65280],167)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item167 : validFast point167=true := by decide +kernel
def group20 : List (List T × Nat) := [point160,point161,point162,point163,point164,point165,point166,point167]
theorem pass20 : group20.all validFast=true := by simp only [group20,List.all_cons,List.all_nil,item160,item161,item162,item163,item164,item165,item166,item167,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point168 : List T × Nat := ([136,34952,43690,52428,61680,64250,65280],168)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item168 : validFast point168=true := by decide +kernel
def point169 : List T × Nat := ([136,34952,43690,52428,61680,65280,65416],169)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item169 : validFast point169=true := by decide +kernel
def point170 : List T × Nat := ([136,34952,43690,52428,61680,65280,65450],170)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item170 : validFast point170=true := by decide +kernel
def point171 : List T × Nat := ([136,34952,43690,52428,61680,65280,65520],171)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item171 : validFast point171=true := by decide +kernel
def point172 : List T × Nat := ([136,43656,43690,52428,61680,65280,65484],172)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item172 : validFast point172=true := by decide +kernel
def point173 : List T × Nat := ([138,170,12336,43690,52428,61680,65280],173)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item173 : validFast point173=true := by decide +kernel
def point174 : List T × Nat := ([138,12336,35466,43690,52428,61680,65280],174)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item174 : validFast point174=true := by decide +kernel
def point175 : List T × Nat := ([138,12336,43690,52428,61680,65280,65328],175)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item175 : validFast point175=true := by decide +kernel
def group21 : List (List T × Nat) := [point168,point169,point170,point171,point172,point173,point174,point175]
theorem pass21 : group21.all validFast=true := by simp only [group21,List.all_cons,List.all_nil,item168,item169,item170,item171,item172,item173,item174,item175,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point176 : List T × Nat := ([168,170,43690,52428,61680,64764,65280],176)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item176 : validFast point176=true := by decide +kernel
def point177 : List T × Nat := ([168,252,43690,52428,61680,64764,65280],177)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item177 : validFast point177=true := by decide +kernel
def point178 : List T × Nat := ([168,43176,43690,52428,61680,64764,65280],178)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item178 : validFast point178=true := by decide +kernel
def point179 : List T × Nat := ([170,204,238,43690,52428,61680,65280],179)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item179 : validFast point179=true := by decide +kernel
def point180 : List T × Nat := ([170,204,240,43690,52428,61680,65280],180)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item180 : validFast point180=true := by decide +kernel
def point181 : List T × Nat := ([170,204,2570,43690,52428,61680,65280],181)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item181 : validFast point181=true := by decide +kernel
def point182 : List T × Nat := ([170,204,3840,43690,52428,61680,65280],182)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item182 : validFast point182=true := by decide +kernel
def point183 : List T × Nat := ([170,204,8738,43690,52428,61680,65280],183)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item183 : validFast point183=true := by decide +kernel
def group22 : List (List T × Nat) := [point176,point177,point178,point179,point180,point181,point182,point183]
theorem pass22 : group22.all validFast=true := by simp only [group22,List.all_cons,List.all_nil,item176,item177,item178,item179,item180,item181,item182,item183,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point184 : List T × Nat := ([170,204,12336,43690,52428,61680,65280],184)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item184 : validFast point184=true := by decide +kernel
def point185 : List T × Nat := ([170,204,13056,43690,52428,61680,65280],185)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item185 : validFast point185=true := by decide +kernel
def point186 : List T × Nat := ([170,204,34952,43690,52428,61680,65280],186)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item186 : validFast point186=true := by decide +kernel
def point187 : List T × Nat := ([170,204,41120,43690,52428,61680,65280],187)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item187 : validFast point187=true := by decide +kernel
def point188 : List T × Nat := ([170,204,43520,43690,52428,61680,65280],188)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item188 : validFast point188=true := by decide +kernel
def point189 : List T × Nat := ([170,204,43554,43690,52428,61680,65280],189)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item189 : validFast point189=true := by decide +kernel
def point190 : List T × Nat := ([170,204,43690,43758,52428,61680,65280],190)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item190 : validFast point190=true := by decide +kernel
def point191 : List T × Nat := ([170,204,43690,52428,61166,61680,65280],191)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item191 : validFast point191=true := by decide +kernel
def group23 : List (List T × Nat) := [point184,point185,point186,point187,point188,point189,point190,point191]
theorem pass23 : group23.all validFast=true := by simp only [group23,List.all_cons,List.all_nil,item184,item185,item186,item187,item188,item189,item190,item191,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point192 : List T × Nat := ([170,204,43690,52428,61440,61680,65280],192)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item192 : validFast point192=true := by decide +kernel
def point193 : List T × Nat := ([170,204,43690,52428,61488,61680,65280],193)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item193 : validFast point193=true := by decide +kernel
def point194 : List T × Nat := ([170,204,43690,52428,61680,61690,65280],194)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item194 : validFast point194=true := by decide +kernel
def point195 : List T × Nat := ([170,204,43690,52428,61680,64250,65280],195)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item195 : validFast point195=true := by decide +kernel
def point196 : List T × Nat := ([170,204,43690,52428,61680,65280,65450],196)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item196 : validFast point196=true := by decide +kernel
def point197 : List T × Nat := ([170,204,43690,52428,61680,65280,65520],197)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item197 : validFast point197=true := by decide +kernel
def point198 : List T × Nat := ([170,238,43690,52428,52462,61680,65280],198)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item198 : validFast point198=true := by decide +kernel
def point199 : List T × Nat := ([170,238,43690,52428,61166,61680,65280],199)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item199 : validFast point199=true := by decide +kernel
def group24 : List (List T × Nat) := [point192,point193,point194,point195,point196,point197,point198,point199]
theorem pass24 : group24.all validFast=true := by simp only [group24,List.all_cons,List.all_nil,item192,item193,item194,item195,item196,item197,item198,item199,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point200 : List T × Nat := ([170,252,43690,52428,61680,64764,65280],200)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item200 : validFast point200=true := by decide +kernel
def point201 : List T × Nat := ([170,2570,2730,43690,52428,61680,65280],201)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item201 : validFast point201=true := by decide +kernel
def point202 : List T × Nat := ([170,2570,8738,43690,52428,61680,65280],202)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item202 : validFast point202=true := by decide +kernel
def point203 : List T × Nat := ([170,2570,12336,43690,52428,61680,65280],203)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item203 : validFast point203=true := by decide +kernel
def point204 : List T × Nat := ([170,2570,17476,43690,52428,61680,65280],204)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item204 : validFast point204=true := by decide +kernel
def point205 : List T × Nat := ([170,2570,20560,43690,52428,61680,65280],205)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item205 : validFast point205=true := by decide +kernel
def point206 : List T × Nat := ([170,2570,34952,43690,52428,61680,65280],206)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item206 : validFast point206=true := by decide +kernel
def point207 : List T × Nat := ([170,2570,41120,43690,52428,61680,65280],207)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item207 : validFast point207=true := by decide +kernel
def group25 : List (List T × Nat) := [point200,point201,point202,point203,point204,point205,point206,point207]
theorem pass25 : group25.all validFast=true := by simp only [group25,List.all_cons,List.all_nil,item200,item201,item202,item203,item204,item205,item206,item207,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point208 : List T × Nat := ([170,2570,43690,49344,52428,61680,65280],208)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item208 : validFast point208=true := by decide +kernel
def point209 : List T × Nat := ([170,2570,43690,50372,52428,61680,65280],209)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item209 : validFast point209=true := by decide +kernel
def point210 : List T × Nat := ([170,2570,43690,52428,52462,61680,65280],210)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item210 : validFast point210=true := by decide +kernel
def point211 : List T × Nat := ([170,2570,43690,52428,61166,61680,65280],211)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item211 : validFast point211=true := by decide +kernel
def point212 : List T × Nat := ([170,2570,43690,52428,61440,61680,65280],212)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item212 : validFast point212=true := by decide +kernel
def point213 : List T × Nat := ([170,2570,43690,52428,61520,61680,65280],213)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item213 : validFast point213=true := by decide +kernel
def point214 : List T × Nat := ([170,2570,43690,52428,61680,61690,65280],214)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item214 : validFast point214=true := by decide +kernel
def point215 : List T × Nat := ([170,2570,43690,52428,61680,64250,65280],215)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item215 : validFast point215=true := by decide +kernel
def group26 : List (List T × Nat) := [point208,point209,point210,point211,point212,point213,point214,point215]
theorem pass26 : group26.all validFast=true := by simp only [group26,List.all_cons,List.all_nil,item208,item209,item210,item211,item212,item213,item214,item215,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point216 : List T × Nat := ([170,2570,43690,52428,61680,64764,65280],216)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item216 : validFast point216=true := by decide +kernel
def point217 : List T × Nat := ([170,2570,43690,52428,61680,65280,65520],217)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item217 : validFast point217=true := by decide +kernel
def point218 : List T × Nat := ([170,2730,43690,52428,61440,61680,65280],218)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item218 : validFast point218=true := by decide +kernel
def point219 : List T × Nat := ([170,2730,43690,52428,61520,61680,65280],219)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item219 : validFast point219=true := by decide +kernel
def point220 : List T × Nat := ([170,3084,3246,43690,52428,61680,65280],220)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item220 : validFast point220=true := by decide +kernel
def point221 : List T × Nat := ([170,3084,12336,43690,52428,61680,65280],221)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item221 : validFast point221=true := by decide +kernel
def point222 : List T × Nat := ([170,3084,13056,43690,52428,61680,65280],222)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item222 : validFast point222=true := by decide +kernel
def point223 : List T × Nat := ([170,3084,34952,43690,52428,61680,65280],223)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item223 : validFast point223=true := by decide +kernel
def group27 : List (List T × Nat) := [point216,point217,point218,point219,point220,point221,point222,point223]
theorem pass27 : group27.all validFast=true := by simp only [group27,List.all_cons,List.all_nil,item216,item217,item218,item219,item220,item221,item222,item223,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point224 : List T × Nat := ([170,3084,41120,43690,52428,61680,65280],224)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item224 : validFast point224=true := by decide +kernel
def point225 : List T × Nat := ([170,3084,41634,43690,52428,61680,65280],225)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item225 : validFast point225=true := by decide +kernel
def point226 : List T × Nat := ([170,3084,43520,43690,52428,61680,65280],226)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item226 : validFast point226=true := by decide +kernel
def point227 : List T × Nat := ([170,3084,43690,44718,52428,61680,65280],227)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item227 : validFast point227=true := by decide +kernel
def point228 : List T × Nat := ([170,3084,43690,52428,61166,61680,65280],228)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item228 : validFast point228=true := by decide +kernel
def point229 : List T × Nat := ([170,3084,43690,52428,61440,61680,65280],229)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item229 : validFast point229=true := by decide +kernel
def point230 : List T × Nat := ([170,3084,43690,52428,61520,61680,65280],230)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item230 : validFast point230=true := by decide +kernel
def point231 : List T × Nat := ([170,3084,43690,52428,61680,61690,65280],231)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item231 : validFast point231=true := by decide +kernel
def group28 : List (List T × Nat) := [point224,point225,point226,point227,point228,point229,point230,point231]
theorem pass28 : group28.all validFast=true := by simp only [group28,List.all_cons,List.all_nil,item224,item225,item226,item227,item228,item229,item230,item231,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point232 : List T × Nat := ([170,3084,43690,52428,61680,64250,65280],232)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item232 : validFast point232=true := by decide +kernel
def point233 : List T × Nat := ([170,3084,43690,52428,61680,64764,65280],233)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item233 : validFast point233=true := by decide +kernel
def point234 : List T × Nat := ([170,3084,43690,52428,61680,65280,65520],234)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item234 : validFast point234=true := by decide +kernel
def point235 : List T × Nat := ([170,3086,43690,52428,52462,61680,65280],235)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item235 : validFast point235=true := by decide +kernel
def point236 : List T × Nat := ([170,3212,43690,52428,61520,61680,65280],236)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item236 : validFast point236=true := by decide +kernel
def point237 : List T × Nat := ([170,3276,43690,52428,61440,61680,65280],237)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item237 : validFast point237=true := by decide +kernel
def point238 : List T × Nat := ([170,3598,43690,52428,61166,61680,65280],238)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item238 : validFast point238=true := by decide +kernel
def point239 : List T × Nat := ([170,3840,4010,43690,52428,61680,65280],239)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item239 : validFast point239=true := by decide +kernel
def group29 : List (List T × Nat) := [point232,point233,point234,point235,point236,point237,point238,point239]
theorem pass29 : group29.all validFast=true := by simp only [group29,List.all_cons,List.all_nil,item232,item233,item234,item235,item236,item237,item238,item239,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point240 : List T × Nat := ([170,3840,20560,43690,52428,61680,65280],240)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item240 : validFast point240=true := by decide +kernel
def point241 : List T × Nat := ([170,3840,34952,43690,52428,61680,65280],241)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item241 : validFast point241=true := by decide +kernel
def point242 : List T × Nat := ([170,3840,41120,43690,52428,61680,65280],242)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item242 : validFast point242=true := by decide +kernel
def point243 : List T × Nat := ([170,3840,41130,43690,52428,61680,65280],243)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item243 : validFast point243=true := by decide +kernel
def point244 : List T × Nat := ([170,3840,43520,43690,52428,61680,65280],244)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item244 : validFast point244=true := by decide +kernel
def point245 : List T × Nat := ([170,3840,43690,44970,52428,61680,65280],245)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item245 : validFast point245=true := by decide +kernel
def point246 : List T × Nat := ([170,3840,43690,49344,52428,61680,65280],246)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item246 : validFast point246=true := by decide +kernel
def point247 : List T × Nat := ([170,3840,43690,49356,52428,61680,65280],247)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item247 : validFast point247=true := by decide +kernel
def group30 : List (List T × Nat) := [point240,point241,point242,point243,point244,point245,point246,point247]
theorem pass30 : group30.all validFast=true := by simp only [group30,List.all_cons,List.all_nil,item240,item241,item242,item243,item244,item245,item246,item247,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point248 : List T × Nat := ([170,3840,43690,52224,52428,61680,65280],248)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item248 : validFast point248=true := by decide +kernel
def point249 : List T × Nat := ([170,3840,43690,52292,52428,61680,65280],249)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item249 : validFast point249=true := by decide +kernel
def point250 : List T × Nat := ([170,3840,43690,52428,52462,61680,65280],250)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item250 : validFast point250=true := by decide +kernel
def point251 : List T × Nat := ([170,3840,43690,52428,53196,61680,65280],251)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item251 : validFast point251=true := by decide +kernel
def point252 : List T × Nat := ([170,3840,43690,52428,61166,61680,65280],252)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item252 : validFast point252=true := by decide +kernel
def point253 : List T × Nat := ([170,3840,43690,52428,61440,61680,65280],253)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item253 : validFast point253=true := by decide +kernel
def point254 : List T × Nat := ([170,3840,43690,52428,61520,61680,65280],254)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item254 : validFast point254=true := by decide +kernel
def point255 : List T × Nat := ([170,3840,43690,52428,61680,61690,65280],255)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item255 : validFast point255=true := by decide +kernel
def group31 : List (List T × Nat) := [point248,point249,point250,point251,point252,point253,point254,point255]
theorem pass31 : group31.all validFast=true := by simp only [group31,List.all_cons,List.all_nil,item248,item249,item250,item251,item252,item253,item254,item255,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point256 : List T × Nat := ([170,3840,43690,52428,61680,64250,65280],256)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item256 : validFast point256=true := by decide +kernel
def point257 : List T × Nat := ([170,3840,43690,52428,61680,64764,65280],257)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item257 : validFast point257=true := by decide +kernel
def point258 : List T × Nat := ([170,3840,43690,52428,61680,65280,65450],258)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item258 : validFast point258=true := by decide +kernel
def point259 : List T × Nat := ([170,3840,43690,52428,61680,65280,65484],259)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item259 : validFast point259=true := by decide +kernel
def point260 : List T × Nat := ([170,3840,43690,52428,61680,65280,65520],260)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item260 : validFast point260=true := by decide +kernel
def point261 : List T × Nat := ([170,3850,43690,52428,61680,65280,65450],261)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item261 : validFast point261=true := by decide +kernel
def point262 : List T × Nat := ([170,3852,43690,52428,61680,65280,65484],262)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item262 : validFast point262=true := by decide +kernel
def point263 : List T × Nat := ([170,10794,43690,49344,52428,61680,65280],263)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item263 : validFast point263=true := by decide +kernel
def group32 : List (List T × Nat) := [point256,point257,point258,point259,point260,point261,point262,point263]
theorem pass32 : group32.all validFast=true := by simp only [group32,List.all_cons,List.all_nil,item256,item257,item258,item259,item260,item261,item262,item263,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point264 : List T × Nat := ([170,16128,43690,49344,52428,61680,65280],264)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item264 : validFast point264=true := by decide +kernel
def point265 : List T × Nat := ([170,17612,43520,43690,52428,61680,65280],265)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item265 : validFast point265=true := by decide +kernel
def point266 : List T × Nat := ([170,19532,41120,43690,52428,61680,65280],266)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item266 : validFast point266=true := by decide +kernel
def point267 : List T × Nat := ([170,21588,43690,52428,61680,64764,65280],267)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item267 : validFast point267=true := by decide +kernel
def point268 : List T × Nat := ([170,21760,21930,43690,52428,61680,65280],268)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item268 : validFast point268=true := by decide +kernel
def point269 : List T × Nat := ([170,21760,34952,43690,52428,61680,65280],269)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item269 : validFast point269=true := by decide +kernel
def point270 : List T × Nat := ([170,21760,35020,43690,52428,61680,65280],270)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item270 : validFast point270=true := by decide +kernel
def point271 : List T × Nat := ([170,21760,43520,43690,52428,61680,65280],271)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item271 : validFast point271=true := by decide +kernel
def group33 : List (List T × Nat) := [point264,point265,point266,point267,point268,point269,point270,point271]
theorem pass33 : group33.all validFast=true := by simp only [group33,List.all_cons,List.all_nil,item264,item265,item266,item267,item268,item269,item270,item271,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point272 : List T × Nat := ([170,21760,43690,49344,52428,61680,65280],272)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item272 : validFast point272=true := by decide +kernel
def point273 : List T × Nat := ([170,21760,43690,52428,52462,61680,65280],273)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item273 : validFast point273=true := by decide +kernel
def point274 : List T × Nat := ([170,21760,43690,52428,61166,61680,65280],274)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item274 : validFast point274=true := by decide +kernel
def point275 : List T × Nat := ([170,21760,43690,52428,61680,64764,65280],275)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item275 : validFast point275=true := by decide +kernel
def point276 : List T × Nat := ([170,21760,43690,52428,61680,65280,65450],276)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item276 : validFast point276=true := by decide +kernel
def point277 : List T × Nat := ([170,21828,43690,52428,61680,65280,65484],277)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item277 : validFast point277=true := by decide +kernel
def point278 : List T × Nat := ([170,24320,41120,43690,52428,61680,65280],278)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item278 : validFast point278=true := by decide +kernel
def point279 : List T × Nat := ([170,32896,34952,43690,52428,61680,65280],279)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item279 : validFast point279=true := by decide +kernel
def group34 : List (List T × Nat) := [point272,point273,point274,point275,point276,point277,point278,point279]
theorem pass34 : group34.all validFast=true := by simp only [group34,List.all_cons,List.all_nil,item272,item273,item274,item275,item276,item277,item278,item279,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point280 : List T × Nat := ([170,32896,43690,49344,52428,61680,65280],280)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item280 : validFast point280=true := by decide +kernel
def point281 : List T × Nat := ([170,34816,34952,43690,52428,61680,65280],281)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item281 : validFast point281=true := by decide +kernel
def point282 : List T × Nat := ([170,34816,43520,43690,52428,61680,65280],282)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item282 : validFast point282=true := by decide +kernel
def point283 : List T × Nat := ([170,34816,43690,52224,52428,61680,65280],283)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item283 : validFast point283=true := by decide +kernel
def point284 : List T × Nat := ([170,34816,43690,52292,52428,61680,65280],284)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item284 : validFast point284=true := by decide +kernel
def point285 : List T × Nat := ([170,34952,34986,43690,52428,61680,65280],285)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item285 : validFast point285=true := by decide +kernel
def point286 : List T × Nat := ([170,34952,41120,43690,52428,61680,65280],286)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item286 : validFast point286=true := by decide +kernel
def point287 : List T × Nat := ([170,34952,43520,43690,52428,61680,65280],287)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item287 : validFast point287=true := by decide +kernel
def group35 : List (List T × Nat) := [point280,point281,point282,point283,point284,point285,point286,point287]
theorem pass35 : group35.all validFast=true := by simp only [group35,List.all_cons,List.all_nil,item280,item281,item282,item283,item284,item285,item286,item287,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point288 : List T × Nat := ([170,34952,43690,49344,52428,61680,65280],288)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item288 : validFast point288=true := by decide +kernel
def point289 : List T × Nat := ([170,34952,43690,52224,52428,61680,65280],289)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item289 : validFast point289=true := by decide +kernel
def point290 : List T × Nat := ([170,34952,43690,52292,52428,61680,65280],290)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item290 : validFast point290=true := by decide +kernel
def point291 : List T × Nat := ([170,34952,43690,52428,52462,61680,65280],291)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item291 : validFast point291=true := by decide +kernel
def point292 : List T × Nat := ([170,34952,43690,52428,61166,61680,65280],292)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item292 : validFast point292=true := by decide +kernel
def point293 : List T × Nat := ([170,34952,43690,52428,61440,61680,65280],293)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item293 : validFast point293=true := by decide +kernel
def point294 : List T × Nat := ([170,34952,43690,52428,61520,61680,65280],294)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item294 : validFast point294=true := by decide +kernel
def point295 : List T × Nat := ([170,34952,43690,52428,61680,61690,65280],295)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item295 : validFast point295=true := by decide +kernel
def group36 : List (List T × Nat) := [point288,point289,point290,point291,point292,point293,point294,point295]
theorem pass36 : group36.all validFast=true := by simp only [group36,List.all_cons,List.all_nil,item288,item289,item290,item291,item292,item293,item294,item295,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point296 : List T × Nat := ([170,34952,43690,52428,61680,63736,65280],296)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item296 : validFast point296=true := by decide +kernel
def point297 : List T × Nat := ([170,34952,43690,52428,61680,64250,65280],297)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item297 : validFast point297=true := by decide +kernel
def point298 : List T × Nat := ([170,34952,43690,52428,61680,64764,65280],298)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item298 : validFast point298=true := by decide +kernel
def point299 : List T × Nat := ([170,34952,43690,52428,61680,65280,65416],299)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item299 : validFast point299=true := by decide +kernel
def point300 : List T × Nat := ([170,34952,43690,52428,61680,65280,65450],300)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item300 : validFast point300=true := by decide +kernel
def point301 : List T × Nat := ([170,34952,43690,52428,61680,65280,65484],301)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item301 : validFast point301=true := by decide +kernel
def point302 : List T × Nat := ([170,34952,43690,52428,61680,65280,65520],302)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item302 : validFast point302=true := by decide +kernel
def point303 : List T × Nat := ([170,34986,43690,52428,52462,61680,65280],303)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item303 : validFast point303=true := by decide +kernel
def group37 : List (List T × Nat) := [point296,point297,point298,point299,point300,point301,point302,point303]
theorem pass37 : group37.all validFast=true := by simp only [group37,List.all_cons,List.all_nil,item296,item297,item298,item299,item300,item301,item302,item303,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point304 : List T × Nat := ([170,43176,43690,52428,61680,64764,65280],304)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item304 : validFast point304=true := by decide +kernel
def point305 : List T × Nat := ([170,43520,43690,49344,52428,61680,65280],305)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item305 : validFast point305=true := by decide +kernel
def point306 : List T × Nat := ([170,43520,43690,52224,52428,61680,65280],306)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item306 : validFast point306=true := by decide +kernel
def point307 : List T × Nat := ([170,43520,43690,52292,52428,61680,65280],307)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item307 : validFast point307=true := by decide +kernel
def point308 : List T × Nat := ([170,43520,43690,52428,52462,61680,65280],308)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item308 : validFast point308=true := by decide +kernel
def point309 : List T × Nat := ([170,43520,43690,52428,61132,61680,65280],309)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item309 : validFast point309=true := by decide +kernel
def point310 : List T × Nat := ([170,43520,43690,52428,61166,61680,65280],310)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item310 : validFast point310=true := by decide +kernel
def point311 : List T × Nat := ([170,43520,43690,52428,61680,64764,65280],311)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item311 : validFast point311=true := by decide +kernel
def group38 : List (List T × Nat) := [point304,point305,point306,point307,point308,point309,point310,point311]
theorem pass38 : group38.all validFast=true := by simp only [group38,List.all_cons,List.all_nil,item304,item305,item306,item307,item308,item309,item310,item311,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point312 : List T × Nat := ([170,43520,43690,52428,61680,65280,65450],312)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item312 : validFast point312=true := by decide +kernel
def point313 : List T × Nat := ([170,43520,43690,52428,61680,65280,65484],313)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item313 : validFast point313=true := by decide +kernel
def point314 : List T × Nat := ([170,43656,43690,52428,61680,65280,65484],314)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item314 : validFast point314=true := by decide +kernel
def point315 : List T × Nat := ([170,43690,49152,49344,52428,61680,65280],315)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item315 : validFast point315=true := by decide +kernel
def point316 : List T × Nat := ([170,43690,49152,52224,52428,61680,65280],316)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item316 : validFast point316=true := by decide +kernel
def point317 : List T × Nat := ([170,43690,49216,49344,52428,61680,65280],317)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item317 : validFast point317=true := by decide +kernel
def point318 : List T × Nat := ([170,43690,49216,52292,52428,61680,65280],318)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item318 : validFast point318=true := by decide +kernel
def point319 : List T × Nat := ([170,43690,49344,49386,52428,61680,65280],319)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item319 : validFast point319=true := by decide +kernel
def group39 : List (List T × Nat) := [point312,point313,point314,point315,point316,point317,point318,point319]
theorem pass39 : group39.all validFast=true := by simp only [group39,List.all_cons,List.all_nil,item312,item313,item314,item315,item316,item317,item318,item319,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point320 : List T × Nat := ([170,43690,49344,52224,52428,61680,65280],320)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item320 : validFast point320=true := by decide +kernel
def point321 : List T × Nat := ([170,43690,49344,52292,52428,61680,65280],321)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item321 : validFast point321=true := by decide +kernel
def point322 : List T × Nat := ([170,43690,49344,52428,52462,61680,65280],322)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item322 : validFast point322=true := by decide +kernel
def point323 : List T × Nat := ([170,43690,49344,52428,60138,61680,65280],323)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item323 : validFast point323=true := by decide +kernel
def point324 : List T × Nat := ([170,43690,49344,52428,61166,61680,65280],324)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item324 : validFast point324=true := by decide +kernel
def point325 : List T × Nat := ([170,43690,49344,52428,61680,64764,65280],325)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item325 : validFast point325=true := by decide +kernel
def point326 : List T × Nat := ([170,43690,49344,52428,61680,65280,65450],326)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item326 : validFast point326=true := by decide +kernel
def point327 : List T × Nat := ([170,43690,49344,52428,61680,65280,65472],327)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item327 : validFast point327=true := by decide +kernel
def group40 : List (List T × Nat) := [point320,point321,point322,point323,point324,point325,point326,point327]
theorem pass40 : group40.all validFast=true := by simp only [group40,List.all_cons,List.all_nil,item320,item321,item322,item323,item324,item325,item326,item327,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point328 : List T × Nat := ([170,43690,49344,52428,61680,65280,65484],328)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item328 : validFast point328=true := by decide +kernel
def point329 : List T × Nat := ([170,43690,49352,52428,61680,61690,65280],329)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item329 : validFast point329=true := by decide +kernel
def point330 : List T × Nat := ([170,43690,51400,52428,61680,64250,65280],330)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item330 : validFast point330=true := by decide +kernel
def point331 : List T × Nat := ([170,43690,52224,52292,52428,61680,65280],331)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item331 : validFast point331=true := by decide +kernel
def point332 : List T × Nat := ([170,43690,52224,52394,52428,61680,65280],332)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item332 : validFast point332=true := by decide +kernel
def point333 : List T × Nat := ([170,43690,52224,52428,52462,61680,65280],333)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item333 : validFast point333=true := by decide +kernel
def point334 : List T × Nat := ([170,43690,52224,52428,61098,61680,65280],334)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item334 : validFast point334=true := by decide +kernel
def point335 : List T × Nat := ([170,43690,52224,52428,61166,61680,65280],335)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item335 : validFast point335=true := by decide +kernel
def group41 : List (List T × Nat) := [point328,point329,point330,point331,point332,point333,point334,point335]
theorem pass41 : group41.all validFast=true := by simp only [group41,List.all_cons,List.all_nil,item328,item329,item330,item331,item332,item333,item334,item335,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point336 : List T × Nat := ([170,43690,52224,52428,61440,61680,65280],336)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item336 : validFast point336=true := by decide +kernel
def point337 : List T × Nat := ([170,43690,52224,52428,61520,61680,65280],337)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item337 : validFast point337=true := by decide +kernel
def point338 : List T × Nat := ([170,43690,52224,52428,61680,61690,65280],338)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item338 : validFast point338=true := by decide +kernel
def point339 : List T × Nat := ([170,43690,52224,52428,61680,64250,65280],339)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item339 : validFast point339=true := by decide +kernel
def point340 : List T × Nat := ([170,43690,52224,52428,61680,64752,65280],340)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item340 : validFast point340=true := by decide +kernel
def point341 : List T × Nat := ([170,43690,52224,52428,61680,64764,65280],341)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item341 : validFast point341=true := by decide +kernel
def point342 : List T × Nat := ([170,43690,52224,52428,61680,65280,65450],342)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item342 : validFast point342=true := by decide +kernel
def point343 : List T × Nat := ([170,43690,52224,52428,61680,65280,65484],343)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item343 : validFast point343=true := by decide +kernel
def group42 : List (List T × Nat) := [point336,point337,point338,point339,point340,point341,point342,point343]
theorem pass42 : group42.all validFast=true := by simp only [group42,List.all_cons,List.all_nil,item336,item337,item338,item339,item340,item341,item342,item343,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point344 : List T × Nat := ([170,43690,52224,52428,61680,65280,65520],344)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item344 : validFast point344=true := by decide +kernel
def point345 : List T × Nat := ([170,43690,52292,52428,52462,61680,65280],345)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item345 : validFast point345=true := by decide +kernel
def point346 : List T × Nat := ([170,43690,52292,52428,61166,61680,65280],346)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item346 : validFast point346=true := by decide +kernel
def point347 : List T × Nat := ([170,43690,52292,52428,61520,61680,65280],347)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item347 : validFast point347=true := by decide +kernel
def point348 : List T × Nat := ([170,43690,52292,52428,61680,61690,65280],348)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item348 : validFast point348=true := by decide +kernel
def point349 : List T × Nat := ([170,43690,52292,52428,61680,64250,65280],349)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item349 : validFast point349=true := by decide +kernel
def point350 : List T × Nat := ([170,43690,52292,52428,61680,64756,65280],350)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item350 : validFast point350=true := by decide +kernel
def point351 : List T × Nat := ([170,43690,52292,52428,61680,64764,65280],351)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item351 : validFast point351=true := by decide +kernel
def group43 : List (List T × Nat) := [point344,point345,point346,point347,point348,point349,point350,point351]
theorem pass43 : group43.all validFast=true := by simp only [group43,List.all_cons,List.all_nil,item344,item345,item346,item347,item348,item349,item350,item351,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point352 : List T × Nat := ([170,43690,52292,52428,61680,65280,65348],352)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item352 : validFast point352=true := by decide +kernel
def point353 : List T × Nat := ([170,43690,52292,52428,61680,65280,65450],353)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item353 : validFast point353=true := by decide +kernel
def point354 : List T × Nat := ([170,43690,52292,52428,61680,65280,65484],354)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item354 : validFast point354=true := by decide +kernel
def point355 : List T × Nat := ([170,43690,52292,52428,61680,65280,65520],355)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item355 : validFast point355=true := by decide +kernel
def point356 : List T × Nat := ([170,43690,52360,52428,61680,65280,65450],356)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item356 : validFast point356=true := by decide +kernel
def point357 : List T × Nat := ([170,43690,52416,52428,61680,65280,65520],357)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item357 : validFast point357=true := by decide +kernel
def point358 : List T × Nat := ([170,43690,52428,52462,61166,61680,65280],358)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item358 : validFast point358=true := by decide +kernel
def point359 : List T × Nat := ([170,43690,52428,52462,61680,61690,65280],359)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item359 : validFast point359=true := by decide +kernel
def group44 : List (List T × Nat) := [point352,point353,point354,point355,point356,point357,point358,point359]
theorem pass44 : group44.all validFast=true := by simp only [group44,List.all_cons,List.all_nil,item352,item353,item354,item355,item356,item357,item358,item359,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point360 : List T × Nat := ([170,43690,52428,52462,61680,64250,65280],360)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item360 : validFast point360=true := by decide +kernel
def point361 : List T × Nat := ([170,43690,52428,52462,61680,64764,65280],361)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item361 : validFast point361=true := by decide +kernel
def point362 : List T × Nat := ([170,43690,52428,52462,61680,64766,65280],362)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item362 : validFast point362=true := by decide +kernel
def point363 : List T × Nat := ([170,43690,52428,52462,61680,65280,65450],363)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item363 : validFast point363=true := by decide +kernel
def point364 : List T × Nat := ([170,43690,52428,52462,61680,65280,65484],364)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item364 : validFast point364=true := by decide +kernel
def point365 : List T × Nat := ([170,43690,52428,52462,61680,65280,65518],365)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item365 : validFast point365=true := by decide +kernel
def point366 : List T × Nat := ([170,43690,52428,52462,61680,65280,65520],366)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item366 : validFast point366=true := by decide +kernel
def point367 : List T × Nat := ([170,43690,52428,60928,61166,61680,65280],367)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item367 : validFast point367=true := by decide +kernel
def group45 : List (List T × Nat) := [point360,point361,point362,point363,point364,point365,point366,point367]
theorem pass45 : group45.all validFast=true := by simp only [group45,List.all_cons,List.all_nil,item360,item361,item362,item363,item364,item365,item366,item367,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point368 : List T × Nat := ([170,43690,52428,60996,61166,61680,65280],368)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item368 : validFast point368=true := by decide +kernel
def point369 : List T × Nat := ([170,43690,52428,61166,61680,64250,65280],369)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item369 : validFast point369=true := by decide +kernel
def point370 : List T × Nat := ([170,43690,52428,61166,61680,64764,65280],370)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item370 : validFast point370=true := by decide +kernel
def point371 : List T × Nat := ([170,43690,52428,61166,61680,65278,65280],371)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item371 : validFast point371=true := by decide +kernel
def point372 : List T × Nat := ([170,43690,52428,61166,61680,65280,65450],372)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item372 : validFast point372=true := by decide +kernel
def point373 : List T × Nat := ([170,43690,52428,61166,61680,65280,65484],373)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item373 : validFast point373=true := by decide +kernel
def point374 : List T × Nat := ([170,43690,52428,61166,61680,65280,65518],374)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item374 : validFast point374=true := by decide +kernel
def point375 : List T × Nat := ([170,43690,52428,61166,61680,65280,65520],375)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item375 : validFast point375=true := by decide +kernel
def group46 : List (List T × Nat) := [point368,point369,point370,point371,point372,point373,point374,point375]
theorem pass46 : group46.all validFast=true := by simp only [group46,List.all_cons,List.all_nil,item368,item369,item370,item371,item372,item373,item374,item375,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point376 : List T × Nat := ([170,43690,52428,61680,64512,64764,65280],376)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item376 : validFast point376=true := by decide +kernel
def point377 : List T × Nat := ([170,43690,52428,61680,64596,64764,65280],377)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item377 : validFast point377=true := by decide +kernel
def point378 : List T × Nat := ([170,43690,52428,61680,64764,64766,65280],378)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item378 : validFast point378=true := by decide +kernel
def point379 : List T × Nat := ([170,43690,52428,61680,64764,65278,65280],379)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item379 : validFast point379=true := by decide +kernel
def point380 : List T × Nat := ([170,43690,52428,61680,64764,65280,65450],380)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item380 : validFast point380=true := by decide +kernel
def point381 : List T × Nat := ([170,43690,52428,61680,64764,65280,65484],381)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item381 : validFast point381=true := by decide +kernel
def point382 : List T × Nat := ([170,43690,52428,61680,64764,65280,65532],382)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item382 : validFast point382=true := by decide +kernel
def point383 : List T × Nat := ([170,43690,52428,61680,65280,65348,65484],383)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item383 : validFast point383=true := by decide +kernel
def group47 : List (List T × Nat) := [point376,point377,point378,point379,point380,point381,point382,point383]
theorem pass47 : group47.all validFast=true := by simp only [group47,List.all_cons,List.all_nil,item376,item377,item378,item379,item380,item381,item382,item383,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point384 : List T × Nat := ([170,43690,52428,61680,65280,65450,65484],384)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item384 : validFast point384=true := by decide +kernel
def point385 : List T × Nat := ([170,43690,52428,61680,65280,65450,65518],385)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item385 : validFast point385=true := by decide +kernel
def point386 : List T × Nat := ([170,43690,52428,61680,65280,65484,65518],386)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item386 : validFast point386=true := by decide +kernel
def point387 : List T × Nat := ([170,43690,52428,61680,65280,65484,65520],387)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item387 : validFast point387=true := by decide +kernel
def point388 : List T × Nat := ([170,43690,52428,61680,65280,65484,65532],388)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item388 : validFast point388=true := by decide +kernel
def point389 : List T × Nat := ([234,43690,49344,52428,60138,61680,65280],389)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item389 : validFast point389=true := by decide +kernel
def point390 : List T × Nat := ([238,3598,43690,52428,61166,61680,65280],390)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item390 : validFast point390=true := by decide +kernel
def point391 : List T × Nat := ([238,34952,43690,52428,61166,61680,65280],391)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item391 : validFast point391=true := by decide +kernel
def group48 : List (List T × Nat) := [point384,point385,point386,point387,point388,point389,point390,point391]
theorem pass48 : group48.all validFast=true := by simp only [group48,List.all_cons,List.all_nil,item384,item385,item386,item387,item388,item389,item390,item391,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point392 : List T × Nat := ([238,41120,43690,52428,61166,61680,65280],392)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item392 : validFast point392=true := by decide +kernel
def point393 : List T × Nat := ([238,43520,43690,52428,61166,61680,65280],393)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item393 : validFast point393=true := by decide +kernel
def point394 : List T × Nat := ([238,43690,43758,52428,61166,61680,65280],394)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item394 : validFast point394=true := by decide +kernel
def point395 : List T × Nat := ([238,43690,52428,57568,61166,61680,65280],395)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item395 : validFast point395=true := by decide +kernel
def point396 : List T × Nat := ([238,43690,52428,60928,61166,61680,65280],396)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item396 : validFast point396=true := by decide +kernel
def point397 : List T × Nat := ([238,43690,52428,61166,61440,61680,65280],397)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item397 : validFast point397=true := by decide +kernel
def point398 : List T × Nat := ([238,43690,52428,61166,61456,61680,65280],398)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item398 : validFast point398=true := by decide +kernel
def point399 : List T × Nat := ([238,43690,52428,61166,61680,61694,65280],399)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item399 : validFast point399=true := by decide +kernel
def group49 : List (List T × Nat) := [point392,point393,point394,point395,point396,point397,point398,point399]
theorem pass49 : group49.all validFast=true := by simp only [group49,List.all_cons,List.all_nil,item392,item393,item394,item395,item396,item397,item398,item399,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point400 : List T × Nat := ([238,43690,52428,61166,61680,64250,65280],400)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item400 : validFast point400=true := by decide +kernel
def point401 : List T × Nat := ([238,43690,52428,61166,61680,65278,65280],401)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item401 : validFast point401=true := by decide +kernel
def point402 : List T × Nat := ([238,43690,52428,61166,61680,65280,65450],402)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item402 : validFast point402=true := by decide +kernel
def point403 : List T × Nat := ([238,43690,52428,61166,61680,65280,65518],403)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item403 : validFast point403=true := by decide +kernel
def point404 : List T × Nat := ([238,43690,52428,61166,61680,65280,65520],404)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item404 : validFast point404=true := by decide +kernel
def point405 : List T × Nat := ([238,43690,52428,61680,65280,65450,65518],405)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item405 : validFast point405=true := by decide +kernel
def point406 : List T × Nat := ([254,43690,52428,61166,61680,65278,65280],406)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item406 : validFast point406=true := by decide +kernel
def point407 : List T × Nat := ([682,43690,52428,61680,64512,64764,65280],407)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item407 : validFast point407=true := by decide +kernel
def group50 : List (List T × Nat) := [point400,point401,point402,point403,point404,point405,point406,point407]
theorem pass50 : group50.all validFast=true := by simp only [group50,List.all_cons,List.all_nil,item400,item401,item402,item403,item404,item405,item406,item407,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point408 : List T × Nat := ([2184,2730,43690,52428,61440,61680,65280],408)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item408 : validFast point408=true := by decide +kernel
def point409 : List T × Nat := ([2184,34952,43690,52428,61440,61680,65280],409)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item409 : validFast point409=true := by decide +kernel
def point410 : List T × Nat := ([2730,3276,43690,52428,61440,61680,65280],410)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item410 : validFast point410=true := by decide +kernel
def point411 : List T × Nat := ([2730,34952,43690,52428,61440,61680,65280],411)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item411 : validFast point411=true := by decide +kernel
def point412 : List T × Nat := ([2730,40960,41120,43690,52428,61680,65280],412)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item412 : validFast point412=true := by decide +kernel
def point413 : List T × Nat := ([2730,40960,43690,52428,61440,61680,65280],413)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item413 : validFast point413=true := by decide +kernel
def point414 : List T × Nat := ([2730,41120,43690,52428,61440,61680,65280],414)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item414 : validFast point414=true := by decide +kernel
def point415 : List T × Nat := ([2730,43690,49152,52428,61440,61680,65280],415)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item415 : validFast point415=true := by decide +kernel
def group51 : List (List T × Nat) := [point408,point409,point410,point411,point412,point413,point414,point415]
theorem pass51 : group51.all validFast=true := by simp only [group51,List.all_cons,List.all_nil,item408,item409,item410,item411,item412,item413,item414,item415,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point416 : List T × Nat := ([2730,43690,49344,52428,61440,61680,65280],416)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item416 : validFast point416=true := by decide +kernel
def point417 : List T × Nat := ([2730,43690,50244,52428,61440,61680,65280],417)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item417 : validFast point417=true := by decide +kernel
def point418 : List T × Nat := ([2730,43690,52428,52974,61440,61680,65280],418)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item418 : validFast point418=true := by decide +kernel
def point419 : List T × Nat := ([2730,43690,52428,61166,61440,61680,65280],419)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item419 : validFast point419=true := by decide +kernel
def point420 : List T × Nat := ([2730,43690,52428,61440,61520,61680,65280],420)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item420 : validFast point420=true := by decide +kernel
def point421 : List T × Nat := ([2730,43690,52428,61440,61680,64170,65280],421)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item421 : validFast point421=true := by decide +kernel
def point422 : List T × Nat := ([2730,43690,52428,61440,61680,64250,65280],422)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item422 : validFast point422=true := by decide +kernel
def point423 : List T × Nat := ([2730,43690,52428,61440,61680,64716,65280],423)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item423 : validFast point423=true := by decide +kernel
def group52 : List (List T × Nat) := [point416,point417,point418,point419,point420,point421,point422,point423]
theorem pass52 : group52.all validFast=true := by simp only [group52,List.all_cons,List.all_nil,item416,item417,item418,item419,item420,item421,item422,item423,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point424 : List T × Nat := ([2730,43690,52428,61440,61680,64764,65280],424)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item424 : validFast point424=true := by decide +kernel
def point425 : List T × Nat := ([2730,43690,52428,61440,61680,65280,65520],425)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item425 : validFast point425=true := by decide +kernel
def point426 : List T × Nat := ([2810,43690,52428,61440,61680,64250,65280],426)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item426 : validFast point426=true := by decide +kernel
def point427 : List T × Nat := ([3822,43690,52428,61166,61440,61680,65280],427)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item427 : validFast point427=true := by decide +kernel
def point428 : List T × Nat := ([4080,43690,52428,61440,61680,65280,65520],428)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item428 : validFast point428=true := by decide +kernel
def point429 : List T × Nat := ([10922,43690,49152,49344,52428,61680,65280],429)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item429 : validFast point429=true := by decide +kernel
def point430 : List T × Nat := ([32768,32896,34952,43690,52428,61680,65280],430)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item430 : validFast point430=true := by decide +kernel
def point431 : List T × Nat := ([32768,34952,43690,52428,61440,61680,65280],431)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item431 : validFast point431=true := by decide +kernel
def group53 : List (List T × Nat) := [point424,point425,point426,point427,point428,point429,point430,point431]
theorem pass53 : group53.all validFast=true := by simp only [group53,List.all_cons,List.all_nil,item424,item425,item426,item427,item428,item429,item430,item431,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point432 : List T × Nat := ([32896,34816,34952,43690,52428,61680,65280],432)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item432 : validFast point432=true := by decide +kernel
def point433 : List T × Nat := ([32896,34952,41120,43690,52428,61680,65280],433)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item433 : validFast point433=true := by decide +kernel
def point434 : List T × Nat := ([32896,34952,43520,43690,52428,61680,65280],434)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item434 : validFast point434=true := by decide +kernel
def point435 : List T × Nat := ([32896,34952,43690,52428,61166,61680,65280],435)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item435 : validFast point435=true := by decide +kernel
def point436 : List T × Nat := ([32896,34952,43690,52428,61440,61680,65280],436)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item436 : validFast point436=true := by decide +kernel
def point437 : List T × Nat := ([32896,34952,43690,52428,61680,63736,65280],437)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item437 : validFast point437=true := by decide +kernel
def point438 : List T × Nat := ([32896,34952,43690,52428,61680,64250,65280],438)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item438 : validFast point438=true := by decide +kernel
def point439 : List T × Nat := ([32896,34952,43690,52428,61680,65280,65408],439)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item439 : validFast point439=true := by decide +kernel
def group54 : List (List T × Nat) := [point432,point433,point434,point435,point436,point437,point438,point439]
theorem pass54 : group54.all validFast=true := by simp only [group54,List.all_cons,List.all_nil,item432,item433,item434,item435,item436,item437,item438,item439,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point440 : List T × Nat := ([32896,34952,43690,52428,61680,65280,65416],440)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item440 : validFast point440=true := by decide +kernel
def point441 : List T × Nat := ([32896,34952,43690,52428,61680,65280,65450],441)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item441 : validFast point441=true := by decide +kernel
def point442 : List T × Nat := ([32896,34952,43690,52428,61680,65280,65520],442)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item442 : validFast point442=true := by decide +kernel
def point443 : List T × Nat := ([34944,34952,43690,52428,61680,65280,65520],443)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item443 : validFast point443=true := by decide +kernel
def point444 : List T × Nat := ([34944,43680,43690,52428,61680,65280,65520],444)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item444 : validFast point444=true := by decide +kernel
def point445 : List T × Nat := ([34952,41120,43176,43690,52428,61680,65280],445)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item445 : validFast point445=true := by decide +kernel
def point446 : List T × Nat := ([34952,41120,43520,43690,52428,61680,65280],446)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item446 : validFast point446=true := by decide +kernel
def point447 : List T × Nat := ([34952,41120,43690,49344,52428,61680,65280],447)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item447 : validFast point447=true := by decide +kernel
def group55 : List (List T × Nat) := [point440,point441,point442,point443,point444,point445,point446,point447]
theorem pass55 : group55.all validFast=true := by simp only [group55,List.all_cons,List.all_nil,item440,item441,item442,item443,item444,item445,item446,item447,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point448 : List T × Nat := ([34952,41120,43690,52224,52428,61680,65280],448)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item448 : validFast point448=true := by decide +kernel
def point449 : List T × Nat := ([34952,41120,43690,52428,60652,61680,65280],449)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item449 : validFast point449=true := by decide +kernel
def point450 : List T × Nat := ([34952,41120,43690,52428,61166,61680,65280],450)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item450 : validFast point450=true := by decide +kernel
def point451 : List T × Nat := ([34952,41120,43690,52428,61680,64764,65280],451)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item451 : validFast point451=true := by decide +kernel
def point452 : List T × Nat := ([34952,41120,43690,52428,61680,65280,65416],452)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item452 : validFast point452=true := by decide +kernel
def point453 : List T × Nat := ([34952,41120,43690,52428,61680,65280,65450],453)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item453 : validFast point453=true := by decide +kernel
def point454 : List T × Nat := ([34952,41120,43690,52428,61680,65280,65484],454)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item454 : validFast point454=true := by decide +kernel
def point455 : List T × Nat := ([34952,43176,43690,52428,61680,63736,65280],455)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item455 : validFast point455=true := by decide +kernel
def group56 : List (List T × Nat) := [point448,point449,point450,point451,point452,point453,point454,point455]
theorem pass56 : group56.all validFast=true := by simp only [group56,List.all_cons,List.all_nil,item448,item449,item450,item451,item452,item453,item454,item455,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point456 : List T × Nat := ([34952,43176,43690,52428,61680,64764,65280],456)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item456 : validFast point456=true := by decide +kernel
def point457 : List T × Nat := ([34952,43680,43690,52428,61680,65280,65520],457)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item457 : validFast point457=true := by decide +kernel
def point458 : List T × Nat := ([34952,43690,52428,57568,61166,61680,65280],458)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item458 : validFast point458=true := by decide +kernel
def point459 : List T × Nat := ([34952,43690,52428,61166,61440,61680,65280],459)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item459 : validFast point459=true := by decide +kernel
def point460 : List T × Nat := ([34952,43690,52428,61166,61680,63736,65280],460)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item460 : validFast point460=true := by decide +kernel
def point461 : List T × Nat := ([34952,43690,52428,61166,61680,64250,65280],461)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item461 : validFast point461=true := by decide +kernel
def point462 : List T × Nat := ([34952,43690,52428,61166,61680,65278,65280],462)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item462 : validFast point462=true := by decide +kernel
def point463 : List T × Nat := ([34952,43690,52428,61166,61680,65280,65520],463)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item463 : validFast point463=true := by decide +kernel
def group57 : List (List T × Nat) := [point456,point457,point458,point459,point460,point461,point462,point463]
theorem pass57 : group57.all validFast=true := by simp only [group57,List.all_cons,List.all_nil,item456,item457,item458,item459,item460,item461,item462,item463,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point464 : List T × Nat := ([34952,43690,52428,61440,61680,63624,65280],464)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item464 : validFast point464=true := by decide +kernel
def point465 : List T × Nat := ([34952,43690,52428,61440,61680,63736,65280],465)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item465 : validFast point465=true := by decide +kernel
def point466 : List T × Nat := ([34952,43690,52428,61440,61680,64250,65280],466)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item466 : validFast point466=true := by decide +kernel
def point467 : List T × Nat := ([34952,43690,52428,61568,61680,65280,65416],467)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item467 : validFast point467=true := by decide +kernel
def point468 : List T × Nat := ([34952,43690,52428,61600,61680,65280,65450],468)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item468 : validFast point468=true := by decide +kernel
def point469 : List T × Nat := ([34952,43690,52428,61680,63736,64250,65280],469)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item469 : validFast point469=true := by decide +kernel
def point470 : List T × Nat := ([34952,43690,52428,61680,63736,65280,65416],470)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item470 : validFast point470=true := by decide +kernel
def point471 : List T × Nat := ([34952,43690,52428,61680,63736,65280,65450],471)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item471 : validFast point471=true := by decide +kernel
def group58 : List (List T × Nat) := [point464,point465,point466,point467,point468,point469,point470,point471]
theorem pass58 : group58.all validFast=true := by simp only [group58,List.all_cons,List.all_nil,item464,item465,item466,item467,item468,item469,item470,item471,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point472 : List T × Nat := ([34952,43690,52428,61680,63736,65280,65520],472)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item472 : validFast point472=true := by decide +kernel
def point473 : List T × Nat := ([34952,43690,52428,61680,63736,65280,65528],473)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item473 : validFast point473=true := by decide +kernel
def point474 : List T × Nat := ([34952,43690,52428,61680,64250,64764,65280],474)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item474 : validFast point474=true := by decide +kernel
def point475 : List T × Nat := ([34952,43690,52428,61680,64250,65278,65280],475)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item475 : validFast point475=true := by decide +kernel
def point476 : List T × Nat := ([34952,43690,52428,61680,64250,65280,65450],476)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item476 : validFast point476=true := by decide +kernel
def point477 : List T × Nat := ([34952,43690,52428,61680,64250,65280,65484],477)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item477 : validFast point477=true := by decide +kernel
def point478 : List T × Nat := ([34952,43690,52428,61680,64250,65280,65520],478)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item478 : validFast point478=true := by decide +kernel
def point479 : List T × Nat := ([34952,43690,52428,61680,64250,65280,65530],479)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item479 : validFast point479=true := by decide +kernel
def group59 : List (List T × Nat) := [point472,point473,point474,point475,point476,point477,point478,point479]
theorem pass59 : group59.all validFast=true := by simp only [group59,List.all_cons,List.all_nil,item472,item473,item474,item475,item476,item477,item478,item479,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point480 : List T × Nat := ([34952,43690,52428,61680,65280,65520,65528],480)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item480 : validFast point480=true := by decide +kernel
def point481 : List T × Nat := ([34952,43690,52428,61680,65280,65520,65530],481)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item481 : validFast point481=true := by decide +kernel
def point482 : List T × Nat := ([43176,43690,52428,60652,61680,64764,65280],482)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item482 : validFast point482=true := by decide +kernel
def point483 : List T × Nat := ([43176,43690,52428,61166,61680,64764,65280],483)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item483 : validFast point483=true := by decide +kernel
def point484 : List T × Nat := ([43176,43690,52428,61680,64512,64764,65280],484)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item484 : validFast point484=true := by decide +kernel
def point485 : List T × Nat := ([43176,43690,52428,61680,64764,65278,65280],485)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item485 : validFast point485=true := by decide +kernel
def point486 : List T × Nat := ([43176,43690,52428,61680,64764,65280,65448],486)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item486 : validFast point486=true := by decide +kernel
def point487 : List T × Nat := ([43176,43690,52428,61680,64764,65280,65450],487)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item487 : validFast point487=true := by decide +kernel
def group60 : List (List T × Nat) := [point480,point481,point482,point483,point484,point485,point486,point487]
theorem pass60 : group60.all validFast=true := by simp only [group60,List.all_cons,List.all_nil,item480,item481,item482,item483,item484,item485,item486,item487,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point488 : List T × Nat := ([43176,43690,52428,61680,64764,65280,65484],488)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item488 : validFast point488=true := by decide +kernel
def point489 : List T × Nat := ([43176,43690,52428,61680,64764,65280,65532],489)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item489 : validFast point489=true := by decide +kernel
def point490 : List T × Nat := ([43688,43690,52428,61680,64764,65280,65532],490)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item490 : validFast point490=true := by decide +kernel
def point491 : List T × Nat := ([43690,52428,60138,61166,61680,64250,65280],491)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item491 : validFast point491=true := by decide +kernel
def point492 : List T × Nat := ([43690,52428,61152,61166,61680,65280,65520],492)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item492 : validFast point492=true := by decide +kernel
def point493 : List T × Nat := ([43690,52428,61166,61680,64250,64764,65280],493)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item493 : validFast point493=true := by decide +kernel
def point494 : List T × Nat := ([43690,52428,61166,61680,64250,65278,65280],494)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item494 : validFast point494=true := by decide +kernel
def point495 : List T × Nat := ([43690,52428,61166,61680,64250,65280,65450],495)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item495 : validFast point495=true := by decide +kernel
def group61 : List (List T × Nat) := [point488,point489,point490,point491,point492,point493,point494,point495]
theorem pass61 : group61.all validFast=true := by simp only [group61,List.all_cons,List.all_nil,item488,item489,item490,item491,item492,item493,item494,item495,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core
def point496 : List T × Nat := ([43690,52428,61166,61680,64250,65280,65484],496)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item496 : validFast point496=true := by decide +kernel
def point497 : List T × Nat := ([43690,52428,61166,61680,64250,65280,65518],497)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item497 : validFast point497=true := by decide +kernel
def point498 : List T × Nat := ([43690,52428,61166,61680,65278,65280,65518],498)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item498 : validFast point498=true := by decide +kernel
def point499 : List T × Nat := ([43690,52428,61166,61680,65278,65280,65520],499)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item499 : validFast point499=true := by decide +kernel
def point500 : List T × Nat := ([43690,52428,61166,61680,65278,65280,65534],500)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item500 : validFast point500=true := by decide +kernel
def point501 : List T × Nat := ([43690,52428,61166,61680,65280,65520,65534],501)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem item501 : validFast point501=true := by decide +kernel
def group62 : List (List T × Nat) := [point496,point497,point498,point499,point500,point501]
theorem pass62 : group62.all validFast=true := by simp only [group62,List.all_cons,List.all_nil,item496,item497,item498,item499,item500,item501,Bool.and_self]
end GuardAudit

namespace GuardAudit
open K4Core K4Orbit
open GuardPair (variants finishAt fromTail)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem fastCertified : stages3.zipIdx.all validFast=true := by
  change (group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 ++ group8 ++ group9 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 ++ group16 ++ group17 ++ group18 ++ group19 ++ group20 ++ group21 ++ group22 ++ group23 ++ group24 ++ group25 ++ group26 ++ group27 ++ group28 ++ group29 ++ group30 ++ group31 ++ group32 ++ group33 ++ group34 ++ group35 ++ group36 ++ group37 ++ group38 ++ group39 ++ group40 ++ group41 ++ group42 ++ group43 ++ group44 ++ group45 ++ group46 ++ group47 ++ group48 ++ group49 ++ group50 ++ group51 ++ group52 ++ group53 ++ group54 ++ group55 ++ group56 ++ group57 ++ group58 ++ group59 ++ group60 ++ group61 ++ group62).all validFast=true
  simp only [List.all_append,pass0,pass1,pass2,pass3,pass4,pass5,pass6,pass7,pass8,pass9,pass10,pass11,pass12,pass13,pass14,pass15,pass16,pass17,pass18,pass19,pass20,pass21,pass22,pass23,pass24,pass25,pass26,pass27,pass28,pass29,pass30,pass31,pass32,pass33,pass34,pass35,pass36,pass37,pass38,pass39,pass40,pass41,pass42,pass43,pass44,pass45,pass46,pass47,pass48,pass49,pass50,pass51,pass52,pass53,pass54,pass55,pass56,pass57,pass58,pass59,pass60,pass61,pass62,Bool.and_self]
set_option maxRecDepth 32768 in
theorem fastClassify {i t} (hi:i<502) (ht:t∈variants) (h:Reach 3 (state i) t) : (i,t)∈winners := by
  have leng : i<stages3.length := by change i<502; exact hi
  have mem : (state i,i)∈stages3.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    rw [state,List.getD_eq_getElem _ _ leng,List.getElem?_eq_getElem leng]
  have v := List.all_eq_true.mp (List.all_eq_true.mp fastCertified _ mem) _ ht
  have q := GuardDep.pick3Of h
  simpa [q] using v
end GuardAudit

namespace GuardPair
theorem noPair : ¬Run 6 base (z0,z1) := fromClasses GuardAudit.fastClassify
end GuardPair

namespace OneNot10920
open FreeAIG PEqualNP.CircuitLowerBounds
theorem positive (C : Circuit) (lg : ∀g∈C.gates,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) (sem : fits C) : Replacement C :=
  sufficient (coreFromPair GuardPair.lowSix GuardPair.noPair) C lg sem
end OneNot10920

end PEqualNP.Outside.L_meta_10920

theorem PEqualNP.Outside.L_meta_10920 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  obtain ⟨D,hm,hs,hf⟩ := PEqualNP.Outside.L_meta_10920.OneNot10920.positive ⟨gates,o⟩ legal computes
  exact ⟨D.gates,D.output,hm,hs,hf⟩
