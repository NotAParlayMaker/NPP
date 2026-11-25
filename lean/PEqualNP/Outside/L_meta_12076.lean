import Mathlib
import PEqualNP.Defs

-- The proof uses two finite cofactor certificates and an explicit monotone circuit.

namespace PEqualNP.Outside.L_meta_12076

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

def PinPattern {α : Type*} (φ : Bool→α→α) (g : Fn α) : Prop :=
  (∀ b,g∘φ b=g) ∨ ∃ q : Bool,∀ b,g∘φ b=(fun _=>decide (b≠q))

theorem PinPattern.restrict {α : Type*} {φ : Bool→α→α} {g : Fn α}
    (h : PinPattern φ g) (b : Bool) : Restricted (φ b) g := by
  rcases h with same|⟨q,eq⟩
  · exact .inl (same b)
  · exact .inr ⟨_,eq b⟩

theorem Avail.pattern {α : Type*} {φ : Bool→α→α} {S : Set (Fn α)} {g : Fn α}
    (h : ∀ f∈S,PinPattern φ f) (a : Avail S g) : PinPattern φ g := by
  induction a with
  | src hs=>exact h _ hs
  | const v=>exact .inl (fun _=>rfl)
  | @neg f orig ih=>
    rcases ih with same|⟨q,eq⟩
    · exact .inl (fun b=>congrArg FreeAIG.neg (same b))
    · refine .inr ⟨!q,?_⟩
      intro v
      have z:=congrArg FreeAIG.neg (eq v)
      cases q <;> cases v <;> exact z

theorem Has.saveTwo {α : Type*} {S : Set (Fn α)} {k : Nat} {f : Fn α}
    (p : Has S k f) (φ : Bool→α→α) {T : Bool→Set (Fn α)}
    (maps : ∀ v g,g∈S → Avail (T v) (g∘φ v))
    (shapes : ∀g∈S,PinPattern φ g) (nontrivial : ∀v,¬Restricted (φ v) f) :
    ∃ v t,t+2≤k ∧ Has (T v) t (f∘φ v) := by
  induction p generalizing T with
  | done last=>exact (nontrivial false ((last.pattern shapes).restrict false)).elim
  | @step S k a b f ha hb tail ih=>
    have finish (v : Bool) (dead : (meet a b)∘φ v=(fun _=>false)) :
        ∃ v t,t+2≤k+1 ∧ Has (T v) t (f∘φ v) := by
      obtain ⟨q,sz,net⟩:=tail.save (T:=T v) (φ v) (by
        rintro g (rfl|m)
        · rw [dead];exact .const false
        · exact maps _ _ m) (by
        rintro g (rfl|m)
        · exact .inr ⟨false,dead⟩
        · exact (shapes _ m).restrict v) (nontrivial v)
      exact ⟨v,q,by omega,net⟩
    rcases ha.pattern shapes with sa|⟨v,eq⟩
    · rcases hb.pattern shapes with sb|⟨v,eq⟩
      · obtain ⟨v,q,sz,net⟩:=ih (T:=fun v=>insert (meet (a∘φ v) (b∘φ v)) (T v))
          (by intro v g m;rcases m with rfl|m
              · exact .src (Set.mem_insert _ _)
              · exact (maps _ _ m).extend)
          (by rintro g (rfl|m)
              · exact .inl (fun v=>congrArg₂ meet (sa v) (sb v))
              · exact shapes _ m) nontrivial
        exact ⟨v,q+1,by omega,.step (ha.map _ (maps v)) (hb.map _ (maps v)) net⟩
      · apply finish v
        change meet (a∘φ v) (b∘φ v) = _
        rw [eq v];simp [meetFalseL,meetFalseR]
    · apply finish v
      change meet (a∘φ v) (b∘φ v) = _
      rw [eq v];simp [meetFalseL,meetFalseR]

theorem pinTwo {n} (f : Fn (Fin n→Bool)) (i : Fin n)
    (dep : ∀b,∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∀b,∃ x y,f (Function.update x i b) ≠ f (Function.update y i b))
    {k} (p : Has Inputs k f) :
    ∃ b t,t+2≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ := fun (b : Bool) (x : Fin n→Bool)=>Function.update x i b
  have own (b : Bool) : ((fun x : Fin n→Bool=>x i)∘φ b)=(fun _=>b) := by funext x;simp [φ]
  have other (j : Fin n) (h : j≠i) (b : Bool) : ((fun x : Fin n→Bool=>x j)∘φ b)=(fun x=>x j) := by
    funext x;simp [φ,h]
  apply p.saveTwo (T:=fun _=>Inputs) φ
  · rintro b _ ⟨j,rfl⟩
    by_cases e:j=i
    · subst j;rw [own];exact .const b
    · rw [other j e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e:j=i
    · subst j
      exact .inr ⟨false,fun b=>by cases b <;> exact own _⟩
    · exact .inl (other j e)
  · intro b
    rintro (same|⟨v,eq⟩)
    · obtain ⟨x,h⟩:=dep b
      exact h (congrFun same x)
    · obtain ⟨x,y,h⟩:=nc b
      exact h ((congrFun eq x).trans (congrFun eq y).symm)

end FreeAIG

namespace Upper12076
open PEqualNP.CircuitLowerBounds

def index (x : Fin 6 → Bool) : ℕ := ∑ i : Fin 6, if x i then 2^(i : ℕ) else 0
def target (x : Fin 6 → Bool) := Nat.testBit (4269860864 * 2^32 + 4269834240) (index x)
def gates : List Gate := [⟨.and, [2, 1]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [8, 5]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [15, 16]⟩]
def circuit : Circuit := ⟨gates, 17⟩

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem size : circuit.size = 12 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem correct : ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) = target x := by
  decide +kernel

end Upper12076

namespace Upper12076
open FreeAIG

def table5 (w : Nat) (x : Fin 5→Bool) :=
  Nat.testBit w (∑ i:Fin 5,if x i then 2^i.val else 0)
def cofactor (v : Bool) := table5 (if v then 4269860864 else 4269834240)

theorem originalBoth {k} (h : Has Inputs k target) :
    ∃ (b : Bool) (t : Nat),t+2≤k ∧ Has Inputs t (cofactor b) := by
  have changes : ∀ b : Bool, ∃ x : Fin 6→Bool, target (Function.update x 5 b) ≠ target x := by
    decide +kernel
  have varies : ∀ b : Bool, ∃x y : Fin 6→Bool,
      target (Function.update x 5 b) ≠ target (Function.update y 5 b) := by
    decide +kernel
  obtain ⟨v,n,small,net⟩:=pinTwo target 5 changes varies h
  let extend : (Fin 5→Bool)→(Fin 6→Bool) := fun x=>Fin.snoc x v
  have sources : ∀g∈(Inputs : Set (Fn (Fin 6→Bool))),Avail Inputs (g∘extend) := by
    rintro g ⟨i,rfl⟩
    refine Fin.lastCases ?_ (fun j=>?_) i
    · change Avail Inputs (fun x : Fin 5→Bool=>Fin.snoc (α:=fun _=>Bool) x v (Fin.last 5))
      simp only [Fin.snoc_last]
      exact .const v
    · simpa [extend,Function.comp_def] using (Avail.src (S:=Inputs) (show (fun y : Fin 5→Bool=>y j)∈Inputs from ⟨j,rfl⟩))
  have eq : ((fun x=>target (Function.update x 5 v))∘extend) = cofactor v := by
    funext y
    exact (show ∀v:Bool,∀x:Fin 5→Bool, target (Function.update (Fin.snoc x v) 5 v)=cofactor v x
      from by decide +kernel) v y
  exact ⟨v,n,small,eq ▸ net.map extend sources⟩

theorem fromTwo
    (lo : ∀{k},Has Inputs k (table5 4269834240) → 9 ≤ k)
    (hi : ∀{k},Has Inputs k (table5 4269860864) → 9 ≤ k)
    {k : Nat} (net : Has Inputs k target) : 11≤k := by
  obtain ⟨v,t,small,h⟩:=originalBoth net
  cases v
  · have low:=lo h
    omega
  · have high:=hi h
    omega

end Upper12076

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

namespace Upper12076
open FreeAIG PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem completeFromSigned
    (lower : ∀ {k : Nat}, Has Inputs k target → 11 ≤ k)
    (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧
      ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = target x := by
  obtain ⟨C,legal,len,ok⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hc := circuitAIG (n := 6) C (by simpa [FanInTwo] using legal)
    rw [funext ok] at hc
    have minimum := lower hc
    have discount := notDiscount hn
    have budget : C.gates.length ≤ s := len
    exact ⟨circuit, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C,?_,len,ok⟩
    intro g hg
    obtain ⟨ops,arity⟩ := legal g hg
    exact ⟨ops.imp_right (fun z => z.resolve_right (fun ng => hn ⟨g,hg,ng⟩)),arity⟩
end Upper12076

namespace K4Core
def pack {n:Nat} (f : Fin n→Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem pack_get {n:Nat} (f : Fin n→Bool) (i:Fin n) : (pack f)[i.val] = f i := by
  have h : (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i := by
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp
  exact h

end K4Core

namespace LiveAIG
abbrev W := BitVec 128
abbrev R := Fin 128
abbrev X := Fin 7→Bool
def signed (w : W) (s : Bool) := if s then ~~~w else w
def norm (w : W) := signed w w[0]
def made (a b : W) (s t : Bool) := norm (signed a s &&& signed b t)
def drop (s : List W) (a : W) (keep : Bool) := if keep then s else s.erase a
def after (s : List W) (a b g : W) (ka kb : Bool) := g :: drop (drop s a ka) b kb
def row (r : R) (i : Fin 7) := r.val.testBit i.val
def word (f : X→Bool) : W := K4Core.pack fun r=>f (row r)
def inputs : List W := (List.finRange 7).map fun i=>word (fun x=>x i)
def depends (f : X→Bool) := ∀ i : Fin 7, ∃ r q : R, (∀ j : Fin 7,j≠i → row r j=row q j) ∧ f (row r)≠f (row q)

inductive Run (t : W) : List W→Nat→Nat→Prop where
  | done : Run t [norm t] 0 0
  | gate {s n c} (a b : W) (sa sb ka kb : Bool) (left : a∈s) (right : b∈s) (different : a≠b)
      (nz : made a b sa sb ≠ 0) (newWord : made a b sa sb ∉ s)
      (rest : Run t (after s a b (made a b sa sb) ka kb) n c) :
      Run t s (n+1) (c+ka.toNat+kb.toNat)

theorem signedTwice (w : W) (b : Bool) : signed (signed w b) b=w := by cases b <;> simp [signed]
theorem orient (w : W) : signed (norm w) w[0]=w := signedTwice w w[0]
theorem normNeg (w : W) : norm (~~~w)=norm w := by
  unfold norm
  cases h:w[0] <;> simp [signed,h]
theorem normEq (x y : W) (k : norm x=norm y) : x=y ∨ x= ~~~y := by
  cases a:x[0] <;> cases b:y[0] <;> simp [norm,signed,a,b] at k
  · exact Or.inl k
  · exact Or.inr k
  · right; rw [←k];simp
  · exact Or.inl k

def agree (s : List W) (r q : R) := ∀w∈s,w[r.val]=w[q.val]
theorem dropSubset (s : List W) (a : W) (b : Bool) : ∀x∈drop s a b,x∈s := by
  cases b
  · exact fun _ h=>List.mem_of_mem_erase h
  · exact fun _ h=>h
theorem signedCong {w : W} (b : Bool) {r q : R} (h : w[r.val]=w[q.val]) :
    (signed w b)[r.val]=(signed w b)[q.val] := by cases b <;> simp [signed,h]
theorem agreeRun {s n c t} (rt : Run t s n c) {r q : R} (same : agree s r q) : t[r.val]=t[q.val] := by
  induction rt with
  | done =>
    have e := same (norm t) List.mem_cons_self
    have e' := signedCong t[0] e
    rwa [orient] at e'
  | @gate s n c a b sa sb ka kb ha hb _ _ _ tail ih =>
    apply ih
    intro w mem
    rcases List.mem_cons.mp mem with rfl|old
    · apply signedCong
      have x:=signedCong sa (same a ha)
      have y:=signedCong sb (same b hb)
      simp only [BitVec.getElem_and,x,y]
    · exact same w (dropSubset _ _ _ _ (dropSubset _ _ _ _ old))

theorem dropLength {s : List W} {a : W} (h:a∈s) (keep : Bool) :
    (drop s a keep).length+1=s.length+keep.toNat := by
  cases keep
  · have pos := List.length_pos_of_mem h
    simp [drop,h,List.length_erase_of_mem];omega
  · simp [drop]

theorem rightStays {s : List W} {a b : W} (hb:b∈s) (ne:a≠b) (k : Bool) : b∈drop s a k := by
  cases k <;> simp [drop,hb,ne.symm]

theorem balance {s n c t} (r : Run t s n c) : s.length+c=n+1 := by
  induction r with
  | done=>rfl
  | @gate s n c a b sa sb ka kb ha hb ne _ _ tail ih =>
    have da:=dropLength ha ka
    have db:=dropLength (rightStays hb ne ka) kb
    simp only [after,List.length_cons] at ih
    omega

theorem wordBit (f : X→Bool) (r : R) : (word f)[r.val]=f (row r) := K4Core.pack_get _ r
theorem wordNeg (f : X→Bool) : word (FreeAIG.neg f)= ~~~word f := by
  ext j hj
  rw [BitVec.getElem_not]
  exact (wordBit _ ⟨j,hj⟩).trans (congrArg Bool.not (wordBit f ⟨j,hj⟩)).symm
theorem wordAnd (f g : X→Bool) : word (FreeAIG.meet f g)=word f &&& word g := by
  ext j hj
  rw [BitVec.getElem_and,show (word f)[j]=f (row ⟨j,hj⟩) from wordBit f ⟨j,hj⟩,
    show (word g)[j]=g (row ⟨j,hj⟩) from wordBit g ⟨j,hj⟩]
  exact wordBit _ ⟨j,hj⟩

theorem rawNorm : ∀i:Fin 7,norm (word (fun x=>x i))=word (fun x=>x i) := by decide +kernel
theorem uniqueInputs : inputs.Nodup := by decide +kernel
theorem inputLength : inputs.length=7 := by simp [inputs]
end LiveAIG

namespace LiveAIG

def Pivot (t:W) (s:List W) (x:W) (r:R) : Prop :=
  ∃q:R,t[r.val]≠t[q.val] ∧ ∀w∈s,w≠x → w[r.val]=w[q.val]

private theorem madeCom (u v:W) (a b:Bool) : made u v a b=made v u b a := by
  unfold made;rw [BitVec.and_comm]

private theorem newPivot {t x g s r} {d:List W} (h:Pivot t s x r)
    (old:∀w∈d,w∈s ∧ w≠x) : Pivot t (g::d) g r := by
  obtain ⟨q,diff,agree⟩ := h
  refine ⟨q,diff,?_⟩
  intro w hmem neq
  rcases List.mem_cons.mp hmem with head|tail
  · exact (neq head).elim
  · exact agree _ (old _ tail).1 (old _ tail).2

private theorem forceOther {t u v:W} {s d:List W} {r:R} {a b:Bool} {k c}
    (pv:Pivot t s u r) (vm:v∈s) (vu:v≠u) (keep:∀w∈d,w∈s ∧ w≠u)
    (rest:Run t (made u v a b::d) k c) : (signed v b)[r.val]=true := by
  obtain ⟨q,tw,base⟩ := pv
  have other := signedCong b (base v vm vu)
  by_contra! no
  have zero:(signed v b)[r.val]=false := by cases h:(signed v b)[r.val] <;> simp_all
  have zero':(signed v b)[q.val]=false := other.symm.trans zero
  apply tw (agreeRun rest ?_)
  intro x hx
  rcases List.mem_cons.mp hx with rfl|old
  · apply signedCong
    simp only [BitVec.getElem_and,zero,zero',Bool.and_false]
  · exact base x (keep _ old).1 (keep _ old).2

private theorem signedDiff {u:W} {p n:R} (s:Bool) (h:u[p.val]≠u[n.val]) :
    (signed u s)[p.val]≠(signed u s)[n.val] := by
  cases s <;> simpa [signed] using h
private theorem resultDiff {u v:W} {p n:R} {a b:Bool}
    (d:u[p.val]≠u[n.val]) (pp:(signed v b)[p.val]=true) (nn:(signed v b)[n.val]=true) :
    (made u v a b)[p.val]≠(made u v a b)[n.val] := by
  have inner : (signed u a &&& signed v b)[p.val]≠(signed u a &&& signed v b)[n.val] := by
    simpa only [BitVec.getElem_and,pp,nn,Bool.and_true] using signedDiff a d
  exact signedDiff _ inner

private def mappedPivot (x u v g:W) := if x=u ∨ x=v then g else x

private theorem trackPivot {t u v x:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (vm:v∈s) (ne:u≠v) (xm:x∈s)
    (hd:∀w,w∈d ↔ w∈s ∧ w≠u ∧ w≠v)
    (px:Pivot t s x p) (nx:Pivot t s x n) (diff:x[p.val]≠x[n.val])
    (rest:Run t (made u v a b::d) k c) :
    let g := made u v a b
    let y := mappedPivot x u v g
    y∈g::d ∧ Pivot t (g::d) y p ∧ Pivot t (g::d) y n ∧ y[p.val]≠y[n.val] := by
  dsimp only
  have left : ∀w∈d,w∈s∧w≠u := fun w m=>⟨((hd w).mp m).1,((hd w).mp m).2.1⟩
  have right : ∀w∈d,w∈s∧w≠v := fun w m=>⟨((hd w).mp m).1,((hd w).mp m).2.2⟩
  by_cases one:x=u
  · subst x
    simp only [mappedPivot,eq_self, true_or,ite_true]
    exact ⟨List.mem_cons_self ..,newPivot px left,newPivot nx left,resultDiff diff
      (forceOther px vm ne.symm left rest) (forceOther nx vm ne.symm left rest)⟩
  by_cases two:x=v
  · subst x
    simp only [mappedPivot,eq_self,or_true,ite_true]
    have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
    have dp := resultDiff (a:=b) diff (forceOther px um ne right r') (forceOther nx um ne right r')
    rw [madeCom v u b a] at dp
    exact ⟨List.mem_cons_self ..,newPivot px right,newPivot nx right,dp⟩
  simp only [mappedPivot,one,two,or_self,ite_false]
  have stay {r:R} (pv:Pivot t s x r) : Pivot t (made u v a b::d) x r := by
    obtain ⟨q,tw,z⟩ := pv
    refine ⟨q,tw,?_⟩
    intro w hw neq
    rcases List.mem_cons.mp hw with rfl|old
    · apply signedCong
      simp only [BitVec.getElem_and,signedCong a (z u um (Ne.symm one)),signedCong b (z v vm (Ne.symm two))]
    · exact z _ ((hd _).mp old).1 neq
  exact ⟨List.mem_cons_of_mem _ ((hd _).mpr ⟨xm,one,two⟩),stay px,stay nx,diff⟩

private theorem clashBoth {t u v:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (ne:u≠v) (right:∀w∈d,w∈s∧w≠v)
    (vp:Pivot t s v p) (vn:Pivot t s v n) (ud:u[p.val]≠u[n.val])
    (rest:Run t (made u v a b::d) k c) : False := by
  have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
  exact signedDiff a ud ((forceOther vp um ne right r').trans (forceOther vn um ne right r').symm)

private theorem mainPivot {t s k cost} (run:Run t s k cost) : cost=0 → s.Nodup →
    ∀(x y:W) (p n:R), x∈s → y∈s → x≠y → Pivot t s x p → Pivot t s x n →
      Pivot t s y p → Pivot t s y n → x[p.val]≠x[n.val] → y[p.val]≠y[n.val] → False := by
  induction run with
  | done =>
    intro _ _ x y p n hx hy neq
    simp only [List.mem_singleton] at hx hy
    exact (neq (hx.trans hy.symm)).elim
  | @gate s k cost u v a b ka kb um vm ne nz newWord rest ih =>
    intro eq nd x y p n xm ym xy xp xn yp yn xd yd
    have zero : cost=0 ∧ ka=false ∧ kb=false := by
      cases ka <;> cases kb <;> simp_all [Bool.toNat]
    obtain ⟨rfl,rfl,rfl⟩ := zero
    let d := (s.erase u).erase v
    let g := made u v a b
    have hd : ∀w,w∈d ↔ w∈s ∧ w≠u ∧ w≠v := by
      intro w
      rw [show d=(s.erase u).erase v by rfl,(nd.erase u).mem_erase_iff,nd.mem_erase_iff]
      tauto
    have rr : Run t (g::d) k 0 := rest
    have nd' : (g::d).Nodup := by
      apply List.nodup_cons.mpr
      exact ⟨fun h=>newWord ((hd _).mp h).1,(nd.erase u).erase v⟩
    have l := trackPivot um vm ne xm hd xp xn xd rr
    have r := trackPivot um vm ne ym hd yp yn yd rr
    apply ih rfl nd' _ _ p n l.1 r.1 _ l.2.1 l.2.2.1 r.2.1 r.2.2.1 l.2.2.2 r.2.2.2
    by_cases hx:x=u ∨ x=v <;> by_cases hy:y=u ∨ y=v
    · exfalso
      rcases hx with e|e <;> rcases hy with f|f
      · exact xy (e.trans f.symm)
      · subst x;subst y
        exact clashBoth um ne (fun w h=>⟨((hd w).mp h).1,((hd w).mp h).2.2⟩) yp yn xd rr
      · subst x;subst y
        exact clashBoth um ne (fun w h=>⟨((hd w).mp h).1,((hd w).mp h).2.2⟩) xp xn yd rr
      · exact xy (e.trans f.symm)
    · simp only [mappedPivot,hx,hy,ite_true,ite_false]
      exact fun h=>newWord (h ▸ ym)
    · simp only [mappedPivot,hx,hy,ite_true,ite_false]
      exact fun h=>newWord (h ▸ xm)
    · simpa only [mappedPivot,hx,hy,ite_false] using xy

theorem dualPivot {t:W} {s:List W} {k:Nat} {a b:W} {p n:R} (run:Run t s k 0)
    (nd:s.Nodup) (ha:a∈s) (hb:b∈s) (different:a≠b)
    (ap:Pivot t s a p) (an:Pivot t s a n) (bp:Pivot t s b p) (bn:Pivot t s b n)
    (ad:a[p.val]≠a[n.val]) (bd:b[p.val]≠b[n.val]) : False :=
  mainPivot run rfl nd a b p n ha hb different ap an bp bn ad bd

private theorem singleAux {t s k cost} (run:Run t s k cost) : cost=0 → s.Nodup →
    ∀(x:W) (p n:R),x∈s → Pivot t s x p → Pivot t s x n → x[p.val]≠x[n.val] →
      t[p.val]≠t[n.val] := by
  induction run with
  | done =>
    intro _ _ x p n xm _ _ diff same
    have eq : x=norm t := by simpa using xm
    subst x
    exact diff (signedCong _ same)
  | @gate s k cost u v a b ka kb um vm ne nz newWord rest ih =>
    intro eq nd x p n xm xp xn xd
    have zero : cost=0 ∧ ka=false ∧ kb=false := by
      cases ka <;> cases kb <;> simp_all [Bool.toNat]
    obtain ⟨rfl,rfl,rfl⟩ := zero
    let d := (s.erase u).erase v
    let g := made u v a b
    have hd : ∀w,w∈d ↔ w∈s ∧ w≠u ∧ w≠v := by
      intro w
      rw [show d=(s.erase u).erase v by rfl,(nd.erase u).mem_erase_iff,nd.mem_erase_iff]
      tauto
    have rr : Run t (g::d) k 0 := rest
    have nd' : (g::d).Nodup := List.nodup_cons.mpr ⟨fun h=>newWord ((hd _).mp h).1,(nd.erase u).erase v⟩
    have l := trackPivot um vm ne xm hd xp xn xd rr
    exact ih rfl nd' _ p n l.1 l.2.1 l.2.2.1 l.2.2.2

theorem singlePivot {t:W} {s:List W} {k:Nat} {a:W} {p n:R} (run:Run t s k 0)
    (nd:s.Nodup) (ha:a∈s) (ap:Pivot t s a p) (an:Pivot t s a n)
    (ad:a[p.val]≠a[n.val]) : t[p.val]≠t[n.val] :=
  singleAux run rfl nd a p n ha ap an ad
end LiveAIG

namespace LiveAIG.Many
private theorem madeCom (u v:W) (a b:Bool) : made u v a b=made v u b a := by
  unfold made;rw [BitVec.and_comm]

private theorem newPivot {t x g s r} {d:List W} (h:Pivot t s x r)
    (old:∀w∈d,w∈s ∧ w≠x) : Pivot t (g::d) g r := by
  obtain ⟨q,diff,agree⟩ := h
  refine ⟨q,diff,?_⟩
  intro w hmem neq
  rcases List.mem_cons.mp hmem with head|tail
  · exact (neq head).elim
  · exact agree _ (old _ tail).1 (old _ tail).2

private theorem forceOther {t u v:W} {s d:List W} {r:R} {a b:Bool} {k c}
    (pv:Pivot t s u r) (vm:v∈s) (vu:v≠u) (keep:∀w∈d,w∈s ∧ w≠u)
    (rest:Run t (made u v a b::d) k c) : (signed v b)[r.val]=true := by
  obtain ⟨q,tw,base⟩ := pv
  have other := signedCong b (base v vm vu)
  by_contra! no
  have zero:(signed v b)[r.val]=false := by cases h:(signed v b)[r.val] <;> simp_all
  have zero':(signed v b)[q.val]=false := other.symm.trans zero
  apply tw (agreeRun rest ?_)
  intro x hx
  rcases List.mem_cons.mp hx with rfl|old
  · apply signedCong
    simp only [BitVec.getElem_and,zero,zero',Bool.and_false]
  · exact base x (keep _ old).1 (keep _ old).2

private theorem signedDiff {u:W} {p n:R} (s:Bool) (h:u[p.val]≠u[n.val]) :
    (signed u s)[p.val]≠(signed u s)[n.val] := by
  cases s <;> simpa [signed] using h
private theorem resultDiff {u v:W} {p n:R} {a b:Bool}
    (d:u[p.val]≠u[n.val]) (pp:(signed v b)[p.val]=true) (nn:(signed v b)[n.val]=true) :
    (made u v a b)[p.val]≠(made u v a b)[n.val] := by
  have inner : (signed u a &&& signed v b)[p.val]≠(signed u a &&& signed v b)[n.val] := by
    simpa only [BitVec.getElem_and,pp,nn,Bool.and_true] using signedDiff a d
  exact signedDiff _ inner

private def mappedPivot (x u v g:W) := if x=u ∨ x=v then g else x

private theorem clashBoth {t u v:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (ne:u≠v) (right:∀w∈d,w∈s∧w≠v)
    (vp:Pivot t s v p) (vn:Pivot t s v n) (ud:u[p.val]≠u[n.val])
    (rest:Run t (made u v a b::d) k c) : False := by
  have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
  exact signedDiff a ud ((forceOther vp um ne right r').trans (forceOther vn um ne right r').symm)

def witness (t:W) (s:List W) (p n:R) (x:W) : Prop :=
  x∈s ∧ Pivot t s x p ∧ Pivot t s x n ∧ x[p.val]≠x[n.val]

private theorem transfer {t u v x : W} {s d : List W} {p n : R} {a b : Bool} {k c}
    (um:u∈s) (vm:v∈s) (ne:u≠v) (old:∀w∈d,w∈s)
    (other:∀w∈s,w≠u → w≠v → w∈d)
    (consumed:x=u → u∉d) (consumed':x=v → v∉d)
    (h:witness t s p n x) (rr:Run t (made u v a b::d) k c) :
    witness t (made u v a b::d) p n (mappedPivot x u v (made u v a b)) := by
  obtain ⟨xm,xp,xn,xd⟩:=h
  by_cases one:x=u
  · subst x
    have left : ∀w∈d,w∈s∧w≠u := fun w m=>⟨old w m,fun e=> consumed rfl (e ▸ m)⟩
    exact ⟨by simp [mappedPivot],by simpa [mappedPivot] using newPivot (g:=made u v a b) xp left,
      by simpa [mappedPivot] using newPivot (g:=made u v a b) xn left,by
      simpa [mappedPivot] using resultDiff (a:=a) xd (forceOther xp vm ne.symm left rr) (forceOther xn vm ne.symm left rr)⟩
  by_cases two:x=v
  · subst x
    have right : ∀w∈d,w∈s∧w≠v := fun w m=>⟨old w m,fun e=>consumed' rfl (e ▸ m)⟩
    have rr' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
    have de:=resultDiff (a:=b) xd (forceOther xp um ne right rr') (forceOther xn um ne right rr')
    rw [madeCom v u b a] at de
    exact ⟨by simp [mappedPivot],by simpa [mappedPivot] using newPivot (g:=made u v a b) xp right,
      by simpa [mappedPivot] using newPivot (g:=made u v a b) xn right,by simpa [mappedPivot] using de⟩
  have stay {r:R} (pv:Pivot t s x r) : Pivot t (made u v a b::d) x r := by
    obtain ⟨q,diff,z⟩:=pv
    refine ⟨q,diff,?_⟩
    intro w hw neq
    rcases List.mem_cons.mp hw with rfl|mem
    · apply signedCong
      simp only [BitVec.getElem_and,signedCong a (z u um (Ne.symm one)),signedCong b (z v vm (Ne.symm two))]
    · exact z _ (old _ mem) neq
  simpa [witness,mappedPivot,one,two] using
    (show x∈made u v a b::d ∧ Pivot t (made u v a b::d) x p ∧ Pivot t (made u v a b::d) x n ∧ x[p.val]≠x[n.val]
      from ⟨List.mem_cons_of_mem _ (other x xm one two),stay xp,stay xn,xd⟩)

theorem count {t s k c} (run:Run t s k c) (nd:s.Nodup) (p n:R) (P:Finset W)
    (good:∀x∈P,witness t s p n x) : P.card≤c+1 := by
  induction run generalizing P with
  | done =>
    have sub : P ⊆ {norm t} := fun x hx=>by simpa using (good x hx).1
    simpa using Finset.card_le_card sub
  | @gate s k c u v a b ka kb um vm ne nz fresh rest ih =>
    let d:=drop (drop s u ka) v kb
    let g:=made u v a b
    let K : Finset W := (if ka then {u} else ∅) ∪ (if kb then {v} else ∅)
    let U:=P \ K
    have hd : ∀w,w∈d ↔ w∈s ∧ (w=u → ka=true) ∧ (w=v → kb=true) := by
      intro w
      cases ka <;> cases kb <;> simp [d,drop,(nd.erase u).mem_erase_iff,nd.mem_erase_iff] <;> tauto
    have old : ∀w∈d,w∈s := fun w h1=>(hd w).mp h1 |>.1
    have other : ∀w∈s,w≠u → w≠v → w∈d := fun w hw e f=>(hd w).mpr ⟨hw,fun z=>(e z).elim,fun z=>(f z).elim⟩
    have spent {x} (h:x∈U) : (x=u → u∉d) ∧ (x=v → v∉d) := by
      have out:= (Finset.mem_sdiff.mp h).2
      constructor
      · rintro rfl mem
        have eq:=((hd _).mp mem).2.1 rfl
        exact out (by simp [K,eq])
      · rintro rfl mem
        have eq:=((hd _).mp mem).2.2 rfl
        exact out (by simp [K,eq])
    have preserves {x} (hx:x∈U) := transfer um vm ne old other (spent hx).1 (spent hx).2
      (good x (Finset.mem_sdiff.mp hx).1) rest
    have injective : Set.InjOn (fun x=>mappedPivot x u v g) (↑U : Set W) := by
      intro x hx y hy e
      by_contra xy
      have wx:=good x (Finset.mem_sdiff.mp hx).1
      have wy:=good y (Finset.mem_sdiff.mp hy).1
      by_cases X:x=u ∨ x=v <;> by_cases Y:y=u ∨ y=v
      · rcases X with rfl|rfl <;> rcases Y with e'|e'
        · exact xy e'.symm
        · subst y
          exact clashBoth um ne (fun w m=>⟨old w m,fun q=>(spent hy).2 rfl (q ▸ m)⟩)
            wy.2.1 wy.2.2.1 wx.2.2.2 rest
        · subst y
          exact clashBoth um ne (fun w m=>⟨old w m,fun q=>(spent hx).2 rfl (q ▸ m)⟩)
            wx.2.1 wx.2.2.1 wy.2.2.2 rest
        · exact xy e'.symm
      · simp only [mappedPivot,X,Y,ite_true,ite_false] at e
        apply fresh
        change g ∈ s
        rw [e];exact wy.1
      · simp only [mappedPivot,X,Y,ite_true,ite_false] at e
        apply fresh
        change g ∈ s
        rw [←e];exact wx.1
      · exact xy (by simpa [mappedPivot,X,Y] using e)
    have nd' : (g::d).Nodup := by
      refine List.nodup_cons.mpr ⟨fun h=>fresh (old _ h),?_⟩
      cases ka <;> cases kb <;> simp [d,drop,nd,nd.erase u,nd.erase v,(nd.erase u).erase v]
    have hsize:=ih nd' (U.image (fun x=>mappedPivot x u v g)) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
      exact preserves hx)
    rw [Finset.card_image_of_injOn injective] at hsize
    have sub : P ⊆ U ∪ K := by intro x hx; by_cases h:x∈K <;> simp [U,h,hx]
    have diff := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have card : K.card≤ka.toNat+kb.toNat := by
      cases ka <;> cases kb <;> simp [K,ne,Bool.toNat]
    omega
end LiveAIG.Many

namespace LiveAIG

def mixed (t m : W) : Bool := (m &&& t != 0) && (m &&& ~~~t != 0)
def split (t : W) (cells : List W) (w : W) : List W :=
  cells.flatMap fun m => [m &&& w, m &&& ~~~w].filter (mixed t)
def classes (t : W) (remaining : List W) : List W :=
  remaining.foldl (split t) [~~~0]
def accept (t : W) (cells : List W) (w : W) : Bool :=
  cells.all fun m => !mixed t (m &&& w) && !mixed t (m &&& ~~~w)

theorem someRow {m : W} (nonzero : m ≠ 0) : ∃ r : R, m[r.val]=true := by
  by_contra! none
  apply nonzero
  ext j hj
  simpa using none ⟨j,hj⟩

theorem mixedRows {t m : W} (h : mixed t m=true) :
    ∃ p q : R, m[p.val]=true ∧ m[q.val]=true ∧ t[p.val]=true ∧ t[q.val]=false := by
  simp [mixed] at h
  obtain ⟨p,hp⟩:=someRow h.1
  obtain ⟨q,hq⟩:=someRow h.2
  simp at hp hq
  exact ⟨p,q,hp.1,hq.1,hp.2,hq.2⟩

def coherent (cells : List W) (seen : List W) : Prop :=
  ∀ m∈cells, ∀ p q : R, m[p.val]=true → m[q.val]=true → agree seen p q

theorem splitCoherent {t w cells seen} (h : coherent cells seen) :
    coherent (split t cells w) (w::seen) := by
  intro child cm p q hp hq
  obtain ⟨m,mm,sub⟩:=List.mem_flatMap.mp cm
  have parts : child=m &&& w ∨ child=m &&& ~~~w := by
    simpa using (List.mem_filter.mp sub).1
  rcases parts with rfl|rfl
  all_goals
    simp at hp hq
    intro z zm
    rcases List.mem_cons.mp zm with rfl|zm
    · exact hp.2.trans hq.2.symm
    · exact h m mm p q hp.1 hq.1 z zm

theorem foldCoherent (t : W) (suffix : List W) {cells seen}
    (h : coherent cells seen) :
    coherent (suffix.foldl (split t) cells) (suffix++seen) := by
  induction suffix generalizing cells seen with
  | nil => simpa using h
  | cons w ws ih =>
    have stable := ih (splitCoherent (t:=t) (w:=w) h)
    intro m hm p q hp hq z hz
    apply stable m hm p q hp hq z
    simp only [List.cons_append,List.mem_cons,List.mem_append] at hz ⊢
    tauto

theorem classesCoherent (t : W) (s : List W) : coherent (classes t s) s := by
  have initial : coherent [~~~0] [] := by intro m hm p q hp hq z hz; simp at hz
  simpa [classes] using foldCoherent t s initial

theorem acceptOfAgree {t w : W} {s : List W}
    (dep : ∀ p q : R, agree (w::s) p q → t[p.val]=t[q.val]) :
    accept t (classes t s) w=true := by
  apply List.all_eq_true.mpr
  intro m hm
  have cell := classesCoherent t s m hm
  have pure (z : W) (side : ∀ p q : R, z[p.val]=true → z[q.val]=true → w[p.val]=w[q.val]) :
      mixed t (m &&& z)=false := by
    cases test : mixed t (m &&& z) with
    | false => rfl
    | true =>
      obtain ⟨p,q,hp,hq,tp,tq⟩:=mixedRows test
      simp at hp hq
      have agreeAll : agree (w::s) p q := by
        intro v vm
        rcases List.mem_cons.mp vm with rfl|vm
        · exact side p q hp.2 hq.2
        · exact cell p q hp.1 hq.1 v vm
      have same := dep p q agreeAll
      simp [tp,tq] at same
  have pos:=pure w (fun p q hp hq=> hp.trans hq.symm)
  have neg:=pure (~~~w) (by intro p q hp hq; simp at hp hq; exact hp.trans hq.symm)
  simp [pos,neg]

theorem runAccept {t w : W} {remaining : List W} {n c : Nat}
    (h : Run t (w::remaining) n c) : accept t (classes t remaining) w=true :=
  acceptOfAgree fun _ _ same => agreeRun h same

end LiveAIG

namespace LiveAIG

def unionWords (xs:List W) : W := xs.foldr (fun x y=>x|||y) 0
theorem inUnion {xs:List W} {r:R} (h:(unionWords xs)[r.val]=true) : ∃m∈xs,m[r.val]=true := by
  induction xs with
  | nil => simp [unionWords] at h
  | cons x xs ih =>
    change (x|||unionWords xs)[r.val]=true at h
    rw [BitVec.getElem_or,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨x,List.mem_cons_self ..,h⟩
    · obtain ⟨m,hm,q⟩ := ih h
      exact ⟨m,List.mem_cons_of_mem _ hm,q⟩

def pivotMask (t:W) (s:List W) (a:W) : W :=
  unionWords ((classes t (s.erase a)).filter (mixed t))
theorem pivotAt {t s a r} (h:(pivotMask t s a)[r.val]=true) : Pivot t s a r := by
  obtain ⟨m,mem,mr⟩ := inUnion h
  obtain ⟨cell,mix⟩ := List.mem_filter.mp mem
  obtain ⟨p,n,mp,mn,tp,tn⟩ := mixedRows mix
  have coh {u:R} (um:m[u.val]=true) : ∀w∈s,w≠a → w[r.val]=w[u.val] := by
    intro w ws ne
    exact classesCoherent t (s.erase a) m cell r u mr um w (by simpa [ne] using ws)
  cases tr:t[r.val] with
  | true => exact ⟨n,by simp [tr,tn],coh mn⟩
  | false => exact ⟨p,by simp [tr,tp],coh mp⟩

def corners (rows a b:W) : Bool :=
  ((rows &&& a &&& b != 0) && (rows &&& ~~~a &&& ~~~b != 0)) ||
  ((rows &&& a &&& ~~~b != 0) && (rows &&& ~~~a &&& b != 0))
private theorem cornerRows {rows a b:W} (h:corners rows a b=true) :
    ∃p n:R,rows[p.val]=true ∧ rows[n.val]=true ∧ a[p.val]≠a[n.val] ∧ b[p.val]≠b[n.val] := by
  simp only [corners,Bool.or_eq_true,Bool.and_eq_true,bne_iff_ne] at h
  rcases h with h|h
  all_goals
    obtain ⟨p,hp⟩ := someRow h.1
    obtain ⟨n,hn⟩ := someRow h.2
    simp only [BitVec.getElem_and,BitVec.getElem_not,Bool.and_eq_true,Bool.not_eq_true'] at hp hn
    refine ⟨p,n,hp.1.1,hn.1.1,?_,?_⟩ <;> simp [hp.1.2,hn.1.2,hp.2,hn.2]

def dualColumns (t:W) (s:List W) (a b:W) : Bool :=
  corners (pivotMask t s a &&& pivotMask t s b) a b
theorem dualBlock {t s k a b} (nd:s.Nodup) (ha:a∈s) (hb:b∈s) (ne:a≠b)
    (bad:dualColumns t s a b=true) (h:Run t s k 0) : False := by
  obtain ⟨p,n,hp,hn,ad,bd⟩ := cornerRows bad
  simp only [BitVec.getElem_and,Bool.and_eq_true] at hp hn
  exact dualPivot h nd ha hb ne (pivotAt hp.1) (pivotAt hn.1)
    (pivotAt hp.2) (pivotAt hn.2) ad bd

def pivotWords (t:W) (s:List W) : List (W×W) := s.map (fun a=>(a,pivotMask t s a))
def pairExists (xs:List (W×W)) : Bool :=
  xs.any fun x=>xs.any fun y=>x.1.toNat<y.1.toNat && corners (x.2&&&y.2) x.1 y.1
def allBlocked (t:W) (s:List W) : Bool := pairExists (pivotWords t s)
theorem allBlockedSound {t s k} (nd:s.Nodup) (bad:allBlocked t s=true) (h:Run t s k 0) : False := by
  obtain ⟨x,hx,bad⟩ := List.any_eq_true.mp bad
  obtain ⟨y,hy,pair⟩ := List.any_eq_true.mp bad
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  obtain ⟨lt,pair⟩ := Bool.and_eq_true_iff.mp pair
  have less : a.toNat<b.toNat := of_decide_eq_true lt
  exact dualBlock nd ha hb (fun eq=> (Nat.ne_of_lt less) (congrArg BitVec.toNat eq)) pair h

def hintBlocked (t:W) (s:List W) (byte:Nat) : Bool :=
  match s[byte % 16]?,s[(byte/16) % 16]? with
  | some a,some b => a != b && dualColumns t s a b
  | _,_ => false
theorem hintBlockedSound {t s k byte} (nd:s.Nodup) (bad:hintBlocked t s byte=true) (h:Run t s k 0) : False := by
  unfold hintBlocked at bad
  split at bad <;> rename_i hm hn
  · obtain ⟨ne,pair⟩ := Bool.and_eq_true_iff.mp bad
    exact dualBlock nd (List.mem_of_getElem? hm) (List.mem_of_getElem? hn) (bne_iff_ne.mp ne) pair h
  all_goals contradiction

def guardZero (bad:List W→Bool) (s:List W) (budget:Nat) : Bool :=
  if budget=0 ∧ s.Nodup then !(bad s) else true
theorem guardZeroSound {t:W} {bad:List W→Bool}
    (sound:∀{s k},s.Nodup → bad s=true → Run t s k 0 → False)
    {s k c b} (h:Run t s k c) (budget:c≤b) : guardZero bad s b=true := by
  unfold guardZero
  split <;> rename_i f
  · have z:c=0 := by omega
    subst c
    cases v:bad s with
    | false => rfl
    | true => exact (sound f.2 v h).elim
  · rfl

def allowAllPivot (t:W) := guardZero (allBlocked t)
def allowHint (t:W) (hint:List W→Nat) := guardZero (fun s=>hintBlocked t s (hint s))
theorem allowAllPivotSound {t s k c b} (h:Run t s k c) (bound:c≤b) : allowAllPivot t s b=true :=
  guardZeroSound allBlockedSound h bound
theorem allowHintSound {t s k c b} (hint:List W→Nat) (h:Run t s k c) (bound:c≤b) : allowHint t hint s b=true :=
  guardZeroSound (fun nd bad tr=>hintBlockedSound nd bad tr) h bound
end LiveAIG

namespace LiveAIG

def literalAt (w:W) (r:R) := if w[r.val] then w else ~~~w
theorem litEq {w:W} {r q:R} (atq:(literalAt w r)[q.val]=true) : w[r.val]=w[q.val] := by
  cases val:w[r.val] <;> simp [literalAt,val] at atq <;> simp [val,atq]
theorem litNe {w:W} {r q:R} (atq:(~~~literalAt w r)[q.val]=true) : w[r.val]≠w[q.val] := by
  cases val:w[r.val] <;> simp [literalAt,val] at atq <;> simp [val,atq]

def sameMask (a b:W) (r:R) (s:List W) : W :=
  s.foldr (fun w m=>if w=a ∨ w=b then m else m&&&literalAt w r) (~~~0)
theorem keptEqual {a b:W} {r q:R} {s:List W} (h:(sameMask a b r s)[q.val]=true) :
    ∀w∈s,w≠a → w≠b → w[r.val]=w[q.val] := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    change (if x=a ∨ x=b then sameMask a b r xs else sameMask a b r xs&&&literalAt x r)[q.val]=true at h
    by_cases e:x=a ∨ x=b
    · rw [ite_eq_left e] at h
      intro w wm wa wb
      rcases List.mem_cons.mp wm with rfl|old
      · exact (e.elim wa wb).elim
      · exact ih h _ old wa wb
    · rw [ite_eq_right e,BitVec.getElem_and,Bool.and_eq_true] at h
      intro w wm wa wb
      rcases List.mem_cons.mp wm with rfl|old
      · exact litEq h.2
      · exact ih h.1 _ old wa wb

def localPivots (t:W) (s:List W) (a b:W) (r:R) :=
  let pool:=sameMask a b r s &&& ~~~literalAt t r
  let u:=literalAt a r
  let v:=literalAt b r
  (pool &&& ~~~u &&& v != 0) && (pool &&& u &&& ~~~v != 0)
theorem localSound {t s a b r} (h:localPivots t s a b r=true) : Pivot t s a r ∧ Pivot t s b r := by
  simp only [localPivots,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨q,hq⟩ := someRow h.1
  obtain ⟨v,hv⟩ := someRow h.2
  simp only [BitVec.getElem_and,Bool.and_eq_true] at hq hv
  constructor
  · refine ⟨q,litNe hq.1.1.2,?_⟩
    intro w wm wa
    by_cases eq:w=b
    · subst w;exact litEq hq.2
    · exact keptEqual hq.1.1.1 w wm wa eq
  · refine ⟨v,litNe hv.1.1.2,?_⟩
    intro w wm wb
    by_cases eq:w=a
    · subst w;exact litEq hv.1.2
    · exact keptEqual hv.1.1.1 w wm eq wb

def anchor (code:Nat) : R := ⟨code % 128,Nat.mod_lt _ (by decide)⟩
def anchored (t:W) (s:List W) (a b:W) (code:Nat) :=
  let p := anchor code
  let n := anchor (code/128)
  a[p.val] != a[n.val] && b[p.val] != b[n.val] && localPivots t s a b p && localPivots t s a b n
theorem anchorSound {t s a b c k} (nd:s.Nodup) (aa:a∈s) (bb:b∈s) (ne:a≠b)
    (bad:anchored t s a b c=true) (run:Run t s k 0) : False := by
  simp only [anchored,Bool.and_eq_true,bne_iff_ne] at bad
  obtain ⟨ap,bp⟩ := localSound bad.1.2
  obtain ⟨an,bn⟩ := localSound bad.2
  exact dualPivot run nd aa bb ne ap an bp bn bad.1.1.1 bad.1.1.2

def anchorHint (t:W) (s:List W) (code:Nat) :=
  match s[code % 16]?,s[(code/16) % 16]? with
  | some a,some b => a != b && anchored t s a b (code/256)
  | _,_ => false
theorem anchorHintSound {t s k code} (nd:s.Nodup) (bad:anchorHint t s code=true) (h:Run t s k 0) : False := by
  unfold anchorHint at bad
  split at bad <;> rename_i hm hn
  · obtain ⟨ne,pair⟩ := Bool.and_eq_true_iff.mp bad
    exact anchorSound nd (List.mem_of_getElem? hm) (List.mem_of_getElem? hn) (bne_iff_ne.mp ne) pair h
  all_goals contradiction
end LiveAIG

namespace LiveAIG

def canon (s : List W) := s.insertionSort (fun a b=>a.toNat≤b.toNat)
def flags : List Bool := [false,true]
def phaseKids (t : W) (s : List W) (budget : Nat) (a b : W) (ka kb : Bool) :
    List (List W × Nat) :=
  let spent := ka.toNat+kb.toNat
  if spent≤budget then
    let left := drop (drop s a ka) b kb
    let cells := classes t left
    flags.flatMap fun sa=>flags.filterMap fun sb=>
      let g:=made a b sa sb
      if g != 0 && !s.contains g && accept t cells g then
        some (canon (g::left),budget-spent) else none
  else []
def children (t : W) (s : List W) (budget : Nat) : List (List W × Nat) :=
  s.flatMap fun a=>s.flatMap fun b=>
    if a.toNat<b.toNat then flags.flatMap fun ka=>flags.flatMap fun kb=>phaseKids t s budget a b ka kb else []

theorem dropPerm {s u : List W} (p : s.Perm u) (a : W) (k : Bool) :
    (drop s a k).Perm (drop u a k) := by
  cases k
  · exact List.Perm.erase a p
  · exact p

theorem runPerm {t s n c} (rt : Run t s n c) {u} (perm : s.Perm u) : Run t u n c := by
  induction rt generalizing u with
  | done =>
    have single := List.perm_singleton.mp perm.symm
    rw [single]
    exact .done
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh _ ih =>
    apply Run.gate a b sa sb ka kb (perm.mem_iff.mp ha) (perm.mem_iff.mp hb) ne nz
      (fun m=>fresh (perm.mem_iff.mpr m))
    exact ih ((dropPerm (dropPerm perm a ka) b kb).cons _)

theorem canonRun {t s n c} (rt : Run t s n c) : Run t (canon s) n c :=
  runPerm rt (List.perm_insertionSort _ _).symm

theorem swapAfter (s : List W) (a b : W) (sa sb ka kb : Bool) :
    after s a b (made a b sa sb) ka kb = after s b a (made b a sb sa) kb ka := by
  unfold after made
  rw [BitVec.and_comm (signed a sa) (signed b sb)]
  cases ka <;> cases kb <;> simp [drop,List.erase_comm a b]

theorem hasFlag (b : Bool) : b∈flags := by cases b <;> simp [flags]
theorem childOf {t s n c budget a b sa sb ka kb}
    (ha : a∈s) (hb : b∈s) (lt : a.toNat<b.toNat)
    (nz : made a b sa sb ≠ 0) (fresh : made a b sa sb ∉ s)
    (run : Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound : c+ka.toNat+kb.toNat≤budget) :
    ∃p∈children t s budget, Run t p.1 n c ∧ c≤p.2 := by
  let g:=made a b sa sb
  let remaining:=drop (drop s a ka) b kb
  let spent:=ka.toNat+kb.toNat
  have spentOk : spent≤budget := by dsimp [spent];omega
  have checked : accept t (classes t remaining) g=true := runAccept run
  refine ⟨(canon (g::remaining),budget-spent),?_,canonRun run,by dsimp [spent];omega⟩
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos lt]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold phaseKids
  rw [if_pos spentOk]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if g != 0 && !s.contains g && accept t (classes t remaining) g then
      some (canon (g::remaining),budget-spent) else none) = some _
  have avoid : g∉s := fresh
  have val : g≠0 := nz
  simp [avoid,checked]
  exact val

theorem continueRun {t s n c budget} (rt : Run t s (n+1) c) (bound : c≤budget) :
    ∃p∈children t s budget, ∃d≤p.2, Run t p.1 n d := by
  cases rt with
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh rest =>
    have ext : ∃p∈children t s budget, Run t p.1 n c ∧ c≤p.2 := by
      have diff : a.toNat≠b.toNat := fun h=>ne (BitVec.eq_of_toNat_eq h)
      rcases lt_or_gt_of_ne diff with lt|gt
      · exact childOf ha hb lt nz fresh rest bound
      · have eq : made a b sa sb=made b a sb sa := by unfold made; rw [BitVec.and_comm]
        rw [swapAfter] at rest
        exact childOf hb ha gt (eq ▸ nz) (eq ▸ fresh) rest (by omega)
    obtain ⟨p,m,r,b⟩:=ext
    exact ⟨p,m,c,b,r⟩

theorem runStep {t s n c budget} (rt : Run t s n c) (bound : c≤budget) :
    norm t∈s ∨ ∃k, n=k+1 ∧ ∃p∈children t s budget, ∃d≤p.2, Run t p.1 k d := by
  cases n with
  | zero => cases rt; exact Or.inl List.mem_cons_self
  | succ k => exact Or.inr ⟨k,rfl,continueRun rt bound⟩

def searchWith (t : W) (allow : List W→Nat→Bool) : Nat→List W→Nat→Bool
  | 0,s,_=>s.contains (norm t)
  | n+1,s,b=>s.contains (norm t) || (allow s b && (children t s b).any fun p=>searchWith t allow n p.1 p.2)

theorem searchSound {t : W} {allow : List W→Nat→Bool}
    (pass : ∀ {s k c b}, Run t s k c → c≤b → allow s b=true)
    {s k c fuel budget} (run : Run t s k c) (depth : k≤fuel) (bound : c≤budget) :
    searchWith t allow fuel s budget=true := by
  induction fuel generalizing s k c budget with
  | zero =>
    have z : k=0 := by omega
    subst k
    cases run
    simp [searchWith]
  | succ n ih =>
    rcases runStep run bound with endNow|⟨k',rfl,p,pm,d,db,child⟩
    · simp [searchWith,endNow]
    · have allows:=pass run bound
      have kept : (children t s budget).any (fun z=>searchWith t allow n z.1 z.2)=true := List.any_eq_true.mpr ⟨p,pm,ih child (by omega) db⟩
      simp [searchWith,allows,kept]

end LiveAIG

namespace LiveAIG.SparseConflicts
abbrev Board := BitVec 4096
def stripe (i : Nat) : Board := BitVec.ofNat 4096 ((2^4096-1)/(2^(2^i)+1))
def differences (p n : Board) (d : Nat) := (p &&& (n >>> d)) ||| (n &&& (p >>> d))

structure Column where
  w : W
  stride : Nat
  low : Board
  single : Board

structure Rules where
  a0 : Bool
  a1 : Bool
  b0 : Bool
  b1 : Bool
  eq : Bool
  ne : Bool

def restrictions (p n : Board) (a b : Column) : Rules :=
  let s0:=a.single &&& b.low
  let s1:=a.single &&& ~~~b.low
  let t0:=b.single &&& a.low
  let t1:=b.single &&& ~~~a.low
  let lo:=a.low &&& b.low
  let mid:=(~~~a.low) &&& b.low
  ⟨s0 != 0,s1 != 0,t0 != 0,t1 != 0,
   differences p n (b.stride+a.stride) &&& lo != 0,
   differences p n (b.stride-a.stride) &&& mid != 0⟩

def legal (r : Rules) (ka kb sa sb : Bool) :=
  (ka || ((!r.a0 || sb) && (!r.a1 || !sb))) &&
  (kb || ((!r.b0 || sa) && (!r.b1 || !sa))) &&
  (ka || kb || ((!r.eq || sa == sb) && (!r.ne || sa != sb)))

def options (s : List W) (budget : Nat) (a b : W) (rules : Rules) (ka kb : Bool) :=
  let spent:=ka.toNat+kb.toNat
  if spent≤budget then
    let left:=drop (drop s a ka) b kb
    flags.flatMap fun sa=>flags.filterMap fun sb=>
      if legal rules ka kb sa sb then
        let g:=made a b sa sb
        if g != 0 && !s.contains g then some (canon (g::left),budget-spent) else none
      else none
  else []

def transpose (r : Rules) : Rules := ⟨r.b0,r.b1,r.a0,r.a1,r.eq,r.ne⟩

end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def Point (t : W) (s : List W) (a b : W) (x y u v : Bool) : Prop :=
  ∃ p q : R, t[p.val] ≠ t[q.val] ∧ a[p.val]=x ∧ b[p.val]=y ∧ a[q.val]=u ∧ b[q.val]=v ∧
    ∀w∈s,w≠a → w≠b → w[p.val]=w[q.val]

def Justified (t : W) (s : List W) (a b : W) (r : Rules) : Prop :=
  (r.a0=true → Point t s a b false false true false) ∧
  (r.a1=true → Point t s a b false true true true) ∧
  (r.b0=true → Point t s a b false false false true) ∧
  (r.b1=true → Point t s a b true false true true) ∧
  (r.eq=true → Point t s a b false false true true) ∧
  (r.ne=true → Point t s a b true false false true)

def distinguishes (ka kb sa sb x y u v : Bool) : Bool :=
  (ka && (x != u)) || (kb && (y != v)) || (((x != sa) && (y != sb)) != ((u != sa) && (v != sb)))

theorem onePass {t s a b x y u v sa sb ka kb k c} (nd:s.Nodup)
    (pt : Point t s a b x y u v) (run : Run t (after s a b (made a b sa sb) ka kb) k c) :
    distinguishes ka kb sa sb x y u v=true := by
  obtain ⟨p,q,tar,ax,by',au,bv,other⟩ := pt
  by_contra fail
  have no : distinguishes ka kb sa sb x y u v = false := by simpa using fail
  simp only [distinguishes,Bool.or_eq_false_iff,bne_eq_false_iff_eq] at no
  apply tar (agreeRun run ?_)
  intro w hm
  rcases List.mem_cons.mp hm with rfl|tail
  · apply signedCong
    have evalBit (z:W) (sg:Bool) (row:R) : (signed z sg)[row.val]=(z[row.val] != sg) := by
      cases sg <;> simp [signed]
    simp only [BitVec.getElem_and,evalBit,ax,by',au,bv]
    exact no.2
  · have old:=dropSubset _ _ _ _ (dropSubset _ _ _ _ tail)
    by_cases wa:w=a
    · subst w
      by_cases keep:ka=true
      · rw [keep] at no
        simpa [ax,au] using no.1.1
      · have cut : ka=false := by simpa using keep
        have inList := dropSubset _ _ _ _ tail
        rw [cut] at inList
        exact ((nd.mem_erase_iff.mp inList).1 rfl).elim
    by_cases wb:w=b
    · subst w
      by_cases keep:kb=true
      · rw [keep] at no
        simpa [by',bv] using no.1.2
      · have cut : kb=false := by simpa using keep
        have kept : (drop s a ka).Nodup := by cases ka <;> simp [drop,nd,nd.erase]
        rw [cut] at tail
        exact ((kept.mem_erase_iff.mp tail).1 rfl).elim
    exact other w old wa wb

theorem allPass : ∀a0 a1 b0 b1 eq ne ka kb sa sb : Bool,
    (a0=true → distinguishes ka kb sa sb false false true false=true) →
    (a1=true → distinguishes ka kb sa sb false true true true=true) →
    (b0=true → distinguishes ka kb sa sb false false false true=true) →
    (b1=true → distinguishes ka kb sa sb true false true true=true) →
    (eq=true → distinguishes ka kb sa sb false false true true=true) →
    (ne=true → distinguishes ka kb sa sb true false false true=true) →
    legal ⟨a0,a1,b0,b1,eq,ne⟩ ka kb sa sb=true := by decide +kernel

theorem legalSound {t s a b sa sb ka kb k c} {r : Rules} (nd:s.Nodup)
    (data : Justified t s a b r) (run : Run t (after s a b (made a b sa sb) ka kb) k c) :
    legal r ka kb sa sb=true := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩:=data
  exact allPass _ _ _ _ _ _ _ _ _ _ (fun h=>onePass nd (h1 h) run) (fun h=>onePass nd (h2 h) run)
    (fun h=>onePass nd (h3 h) run) (fun h=>onePass nd (h4 h) run)
    (fun h=>onePass nd (h5 h) run) (fun h=>onePass nd (h6 h) run)
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts
abbrev CubeTag := Fin 4096

def Realizes (s : List W) (index : W → Nat) (r : R) (x : Nat) :=
  ∀w∈s,w[r.val]=x.testBit (index w)

def Cover (t : W) (s : List W) (index : W → Nat) (p n : Board) :=
  ∀u : CubeTag, (p[u.val]=true → ∃r:R, t[r.val]=true ∧ Realizes s index r u.val) ∧
    (n[u.val]=true → ∃r:R, t[r.val]=false ∧ Realizes s index r u.val)

def Opp (p n : Board) (u v : CubeTag) := (p[u.val]=true ∧ n[v.val]=true) ∨ (n[u.val]=true ∧ p[v.val]=true)

theorem findHit {p n mask:Board} {d:Nat} (bad : (differences p n d &&& mask) != 0) :
    ∃u v : CubeTag,mask[u.val]=true ∧ v.val=u.val+d ∧ Opp p n u v := by
  have any : ∃ u : CubeTag,(differences p n d &&& mask)[u.val]=true := by
    by_contra! none
    apply (bne_iff_ne.mp bad)
    ext j hj
    simpa using none ⟨j,hj⟩
  obtain ⟨u,atU⟩:=any
  simp only [BitVec.getElem_and,Bool.and_eq_true] at atU
  have bits:=atU.1
  simp only [differences,BitVec.getElem_or,Bool.or_eq_true,BitVec.getElem_and,Bool.and_eq_true,
    BitVec.getElem_ushiftRight_eq_decide_getElem,decide_eq_true_eq] at bits
  rcases bits with ⟨pos,z,neg⟩|⟨neg,z,pos⟩
  · exact ⟨u,⟨d+u.val,z⟩,atU.2,Nat.add_comm ..,Or.inl ⟨pos,neg⟩⟩
  · exact ⟨u,⟨d+u.val,z⟩,atU.2,Nat.add_comm ..,Or.inr ⟨neg,pos⟩⟩

def changeMask (i j : Nat) (a b : Bool) := (if a then 2^i else 0) ^^^ (if b then 2^j else 0)

theorem changeBit (i j k : Nat) (a b : Bool) :
    (changeMask i j a b).testBit k = ((a && (i==k)) != (b && (j==k))) := by
  cases a <;> cases b <;> simp [changeMask,Nat.testBit_xor,Nat.testBit_two_pow] <;> grind

theorem emitPoint {t s index p n a b i j da db x y} {u v : CubeTag}
    (cov:Cover t s index p n) (ia:index a=i) (ib:index b=j) (ij:i≠j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (both:Opp p n u v) (atA:u.val.testBit i=x) (atB:u.val.testBit j=y)
    (jump:v.val=u.val ^^^ changeMask i j da db) :
    Point t s a b x y (x != da) (y != db) := by
  have rows : ∃r q : R, t[r.val] ≠ t[q.val] ∧ Realizes s index r u.val ∧ Realizes s index q v.val := by
    rcases both with ⟨h,k⟩|⟨h,k⟩
    · obtain ⟨r,rs,good⟩:=(cov u).1 h
      obtain ⟨q,qs,after⟩:=(cov v).2 k
      exact ⟨r,q,by simp [rs,qs],good,after⟩
    · obtain ⟨r,rs,good⟩:=(cov u).2 h
      obtain ⟨q,qs,after⟩:=(cov v).1 k
      exact ⟨r,q,by simp [rs,qs],good,after⟩
  obtain ⟨r,q,tar,raw,last⟩:=rows
  refine ⟨r,q,tar,by simpa [ia,atA] using raw a aa,by simpa [ib,atB] using raw b bb,?_,?_,?_⟩
  · rw [last a aa,ia,jump,Nat.testBit_xor,changeBit,atA]
    simp [beq_eq_false_iff_ne.mpr (Ne.symm ij)]
  · rw [last b bb,ib,jump,Nat.testBit_xor,changeBit,atB]
    simp [beq_eq_false_iff_ne.mpr ij]
  · intro w wm wa wb
    have ni:index w≠i:=fun h=>wa (uniq w wm a aa (h.trans ia.symm))
    have nj:index w≠j:=fun h=>wb (uniq w wm b bb (h.trans ib.symm))
    rw [raw w wm,last w wm,jump,Nat.testBit_xor,changeBit]
    simp [beq_eq_false_iff_ne.mpr (Ne.symm ni),beq_eq_false_iff_ne.mpr (Ne.symm nj)]
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts
abbrev Idx := Fin 12
abbrev Tag := Fin 4096

abbrev indexGeometry (i : Idx) (u : Tag) :=
  (stripe i.val)[u.val] = !(u.val.testBit i.val) ∧
  (u.val.testBit i.val = false → u.val + 2^i.val = u.val ^^^ 2^i.val ∧ u.val + 2^i.val < 4096) ∧
  (u.val.testBit i.val = true → u.val - 2^i.val = u.val ^^^ 2^i.val ∧ 2^i.val ≤ u.val)
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def valueBand (j : Idx) (value : Bool) : Board := if value then ~~~stripe j.val else stripe j.val

variable (geom : ∀i : Idx,∀u : Tag,indexGeometry i u)

include geom in
theorem atBand {u:Tag} {j:Idx} {v:Bool} (h : (valueBand j v)[u.val]=true) : u.val.testBit j.val=v := by
  have z := (geom j u).1
  cases v with
  | false =>
    change (stripe j.val)[u.val]=true at h
    rw [z] at h
    simpa only [Bool.not_eq_true'] using h
  | true =>
    change (~~~stripe j.val)[u.val]=true at h
    rw [BitVec.getElem_not,z] at h
    simpa only [Bool.not_not] using h

theorem complementCoord {i j : Idx} (ne : i≠j) (x:Nat) :
    (x ^^^ 2^i.val).testBit j.val = x.testBit j.val := by
  have n:i.val≠j.val:=fun h=>ne (Fin.ext h)
  simp [Nat.testBit_xor,Nat.testBit_two_pow,n,Ne.symm n]

include geom in
theorem singleMaterial {t s index p n a b} {i j:Idx} {v:Bool}
    (cov:Cover t s index p n) (ia:index a=i.val) (ib:index b=j.val) (ij:i≠j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (hit : (differences p n (2^i.val) &&& stripe i.val &&& valueBand j v) != 0) :
    Point t s a b false v true v := by
  rw [BitVec.and_assoc] at hit
  obtain ⟨u,z,part,off,rows⟩:=findHit hit
  simp only [BitVec.getElem_and,Bool.and_eq_true] at part
  have atI : u.val.testBit i.val=false := by simpa [(geom i u).1] using part.1
  have atJ := atBand geom part.2
  have jump : z.val=u.val ^^^ changeMask i.val j.val true false := by
    simpa [changeMask] using off.trans ((geom i u).2.1 atI).1
  exact (by simpa using emitPoint cov ia ib (fun h=>ij (Fin.ext h)) aa bb uniq rows atI atJ jump)

theorem flipPoint {t s a b x y u v} (h : Point t s a b x y u v) : Point t s b a y x v u := by
  obtain ⟨r,q,op,ax,by',au,bv,rest⟩:=h
  exact ⟨r,q,op,by',ax,bv,au,fun w wm wb wa=>rest w wm wa wb⟩

include geom in
theorem bothMaterial {t s index p n a b} {i j:Idx} {v:Bool}
    (cov:Cover t s index p n) (ia:index a=i.val) (ib:index b=j.val) (ij:i<j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (hit : (differences p n (if v then 2^j.val-2^i.val else 2^j.val+2^i.val) &&&
      (valueBand i v &&& stripe j.val)) != 0) : Point t s a b v false (!v) true := by
  obtain ⟨u,z,part,off,rows⟩:=findHit hit
  simp only [BitVec.getElem_and,Bool.and_eq_true] at part
  have atI := atBand geom part.1
  have atJ : u.val.testBit j.val=false := by simpa [(geom j u).1] using part.2
  have ne : i≠j := ne_of_lt ij
  have n : i.val ≠ j.val := fun h=>ne (Fin.ext h)
  have upper : 2^i.val ≤ 2^j.val := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt ij)
  have jump : z.val=u.val ^^^ changeMask i.val j.val true true := by
    cases v with
    | false =>
      obtain ⟨first,bd⟩ := (geom i u).2.1 atI
      let m : Tag := ⟨u.val+2^i.val,bd⟩
      have x : m.val=u.val ^^^ 2^i.val := first
      have low:m.val.testBit j.val=false := by rw [x,complementCoord ne];exact atJ
      have second:=((geom j m).2.1 low).1
      simp [changeMask,←Nat.xor_assoc,←x,←second] at *
      omega
    | true =>
      obtain ⟨first,le⟩ := (geom i u).2.2 atI
      let m : Tag := ⟨u.val-2^i.val,lt_of_le_of_lt (Nat.sub_le ..) u.isLt⟩
      have x : m.val=u.val ^^^ 2^i.val := first
      have low:m.val.testBit j.val=false := by rw [x,complementCoord ne];exact atJ
      have second:=((geom j m).2.1 low).1
      simp [changeMask,←Nat.xor_assoc,←x,←second] at *
      omega
  simpa using emitPoint cov ia ib n aa bb uniq rows atI atJ jump
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def denseSig (s : List W) (r:R) : Nat := s.foldr (fun w acc=>Nat.bit (w[r.val]) acc) 0

def denseWords (s : List W) : List R → Board
  | [] => 0
  | r::rs=> ((1 : Board) <<< denseSig s r) ||| denseWords s rs

def stateBoards (t : W) (s : List W) :=
  let rs:=List.finRange 128
  (denseWords s (rs.filter fun r=>t[r.val]),denseWords s (rs.filter fun r=> !t[r.val]))

theorem signatureColumn {s : List W} {w : W} (wm : w∈s) (r:R) :
    (denseSig s r).testBit (s.idxOf w)=w[r.val] := by
  induction s with
  | nil => simp at wm
  | cons a xs ih=>
    change (Nat.bit (a[r.val]) (denseSig xs r)).testBit ((a::xs).idxOf w)=w[r.val]
    by_cases same:w=a
    · subst w;simp
    · have old : w∈xs := (List.mem_cons.mp wm).resolve_left same
      rw [List.idxOf_cons_ne _ (Ne.symm same),Nat.testBit_bit_succ]
      exact ih old

theorem denseHit {s rows} {i:CubeTag} (hit : (denseWords s rows)[i.val]=true) :
    ∃ r∈rows,denseSig s r=i.val := by
  induction rows with
  | nil=> simp [denseWords] at hit
  | cons a xs ih=>
    simp only [denseWords,BitVec.getElem_or,Bool.or_eq_true] at hit
    rcases hit with current|other
    · refine ⟨a,by simp,?_⟩
      rw [BitVec.getElem_shiftLeft] at current
      have two := Bool.and_eq_true_iff.mp current
      have little : i.val - denseSig s a < 4096 := lt_of_le_of_lt (Nat.sub_le ..) i.isLt
      have one : ((1 : Board)[i.val-denseSig s a]'little) = decide (i.val-denseSig s a=0) := BitVec.getElem_one little
      rw [one] at two
      simp at two
      omega
    · obtain ⟨r,rm,val⟩:=ih other
      exact ⟨r,by simp [rm],val⟩

theorem denseCover (t : W) (s : List W) : Cover t s (fun w=>s.idxOf w) (stateBoards t s).1 (stateBoards t s).2 := by
  intro u
  constructor <;> intro h
  · obtain ⟨r,rm,tag⟩:=denseHit h
    refine ⟨r,(List.mem_filter.mp rm).2,fun w wm=>?_⟩
    rw [←tag,signatureColumn wm]
  · obtain ⟨r,rm,tag⟩:=denseHit h
    refine ⟨r,by simpa using (List.mem_filter.mp rm).2,fun w wm=>?_⟩
    rw [←tag,signatureColumn wm]
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def entry (p n : Board) (w:W) (i:Nat) : Column :=
  ⟨w,2^i,stripe i,differences p n (2^i) &&& stripe i⟩

theorem fromMasks (geom : ∀i:Idx,∀u:Tag,indexGeometry i u) {t s index p n a b} {i j:Idx}
    (cov:Cover t s index p n) (ia:index a=i.val) (ib:index b=j.val) (ij:i<j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z) :
    Justified t s a b (restrictions p n (entry p n a i.val) (entry p n b j.val)) := by
  have first := @singleMaterial geom t s index p n a b i j
  have second := @singleMaterial geom t s index p n b a j i
  have dbl := @bothMaterial geom t s index p n a b i j
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact fun hit=>first (v:=false) cov ia ib (ne_of_lt ij) aa bb uniq hit
  · exact fun hit=>first (v:=true) cov ia ib (ne_of_lt ij) aa bb uniq hit
  · exact fun hit=>flipPoint (second (v:=false) cov ib ia (ne_of_gt ij) bb aa uniq hit)
  · exact fun hit=>flipPoint (second (v:=true) cov ib ia (ne_of_gt ij) bb aa uniq hit)
  · exact fun hit=>dbl (v:=false) cov ia ib ij aa bb uniq hit
  · exact fun hit=>dbl (v:=true) cov ia ib ij aa bb uniq hit

theorem reversePoint {t s a b x y u v} (h : Point t s a b x y u v) : Point t s a b u v x y := by
  obtain ⟨p,q,op,ax,by',au,bv,rest⟩:=h
  exact ⟨q,p,Ne.symm op,au,bv,ax,by',fun w wm wa wb=>(rest w wm wa wb).symm⟩

theorem transposeRules {t s a b r} (j:Justified t s a b r) : Justified t s b a (transpose r) := by
  obtain ⟨j1,j2,j3,j4,j5,j6⟩:=j
  exact ⟨fun h=>flipPoint (j3 h),fun h=>flipPoint (j4 h),fun h=>flipPoint (j1 h),fun h=>flipPoint (j2 h),
    fun h=>flipPoint (j5 h),fun h=>reversePoint (flipPoint (j6 h))⟩

def ruleFor (p n : Board) (a b : Column) :=
  if a.stride < b.stride then restrictions p n a b else transpose (restrictions p n b a)

def candidateChildren (s : List W) (budget : Nat) (index : W→Nat) (p n : Board) :=
  let ws:=s.map fun w=>entry p n w (index w)
  ws.flatMap fun a=>ws.flatMap fun b=>
    if a.w.toNat < b.w.toNat then
      let r:=ruleFor p n a b
      flags.flatMap fun ka=>flags.flatMap fun kb=>options s budget a.w b.w r ka kb
    else []

def verifiedChildren (t : W) (s : List W) (budget : Nat) :=
  if s.length ≤ 12 ∧ s.Nodup then
    let (p,n):=stateBoards t s
    candidateChildren s budget (fun w=>s.idxOf w) p n
  else children t s budget

end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def checkGeometry (i u : Nat) :=
  let b:=u.testBit i
  let d:=2^i
  let z:=u ^^^ d
  ((stripe i).getLsbD u == !b) &&
    (if b then (u-d == z) && decide (d≤u) else (u+d == z) && decide (u+d<4096))

def checkIndex (i : Nat) := (List.range 4096).all (checkGeometry i)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem allGeometric : (List.range 12).all checkIndex=true := by decide +kernel

theorem geometryFast (i : Idx) (u : Tag) : indexGeometry i u := by
  have hi := List.all_eq_true.mp allGeometric i.val (List.mem_range.mpr i.isLt)
  have hu := List.all_eq_true.mp hi u.val (List.mem_range.mpr u.isLt)
  cases b : u.val.testBit i.val <;> simpa [indexGeometry,checkGeometry,b,BitVec.getLsbD_eq_getElem] using hu
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

theorem ruleForTrue {t s index p n a b} (cov:Cover t s index p n)
    (bounds:∀w∈s,index w<12) (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (aa:a∈s) (bb:b∈s) (ne:a≠b) :
    Justified t s a b (ruleFor p n (entry p n a (index a)) (entry p n b (index b))) := by
  let i : Idx := ⟨index a,bounds a aa⟩
  let j : Idx := ⟨index b,bounds b bb⟩
  have nn : index a ≠ index b := fun h=>ne (uniq a aa b bb h)
  by_cases ij:index a < index b
  · have pw : 2^index a < 2^index b := Nat.pow_lt_pow_right (by decide) ij
    unfold ruleFor
    split <;> rename_i choice
    · exact fromMasks geometryFast cov (i:=i) (j:=j) rfl rfl ij aa bb uniq
    · exact (choice pw).elim
  · have ji:index b < index a := by omega
    have pw : ¬2^index a < 2^index b := by
      have := Nat.pow_lt_pow_right (by decide : 1 < 2) ji
      omega
    unfold ruleFor
    split <;> rename_i choice
    · exact (pw choice).elim
    · exact transposeRules (fromMasks geometryFast cov (i:=j) (j:=i) rfl rfl ji bb aa uniq)

theorem candidateOf {t s index p n a b sa sb ka kb k c budget} (nd:s.Nodup)
    (cov:Cover t s index p n) (bounds:∀w∈s,index w<12) (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (aa:a∈s) (bb:b∈s) (lt:a.toNat<b.toNat) (nz:made a b sa sb≠0) (fresh:made a b sa sb∉s)
    (run:Run t (after s a b (made a b sa sb) ka kb) k c) (bound:c+ka.toNat+kb.toNat≤budget) :
    ∃q∈candidateChildren s budget index p n, Run t q.1 k c ∧ c≤q.2 := by
  let A:=entry p n a (index a)
  let B:=entry p n b (index b)
  have ne : a≠b := by intro h;subst b;omega
  have pass:=legalSound nd (ruleForTrue cov bounds uniq aa bb ne) run
  let spent:=ka.toNat+kb.toNat
  let rest:=drop (drop s a ka) b kb
  have paid : spent≤budget := by dsimp [spent];omega
  refine ⟨(canon (made a b sa sb::rest),budget-spent),?_,canonRun run,by dsimp [spent];omega⟩
  unfold candidateChildren
  refine List.mem_flatMap.mpr ⟨A,List.mem_map.mpr ⟨a,aa,rfl⟩,List.mem_flatMap.mpr ⟨B,List.mem_map.mpr ⟨b,bb,rfl⟩,?_⟩⟩
  have vals : A.w.toNat < B.w.toNat := lt
  rw [if_pos vals]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold options
  rw [if_pos paid]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if legal (ruleFor p n A B) ka kb sa sb then
    if made a b sa sb != 0 && !s.contains (made a b sa sb) then some _ else none else none) = some _
  simp [A,B,pass,fresh,rest,spent]
  exact ⟨nz,rfl⟩

theorem continueFast {t s n c budget} (rt:Run t s (n+1) c) (bound:c≤budget) :
    ∃q∈verifiedChildren t s budget,∃d≤q.2,Run t q.1 n d := by
  unfold verifiedChildren
  split <;> rename_i cond
  · obtain ⟨small,nd⟩:=cond
    have bounds : ∀w∈s,s.idxOf w<12 := fun w h=>lt_of_lt_of_le (List.idxOf_lt_length_of_mem h) small
    have uniq : ∀w∈s,∀z∈s,s.idxOf w=s.idxOf z → w=z := by
      intro w h z m eq
      have hw:=List.getElem_idxOf (x:=w) (xs:=s) (List.idxOf_lt_length_of_mem h)
      have hz:=List.getElem_idxOf (x:=z) (xs:=s) (List.idxOf_lt_length_of_mem m)
      rw [←hw,←hz];simp [eq]
    cases rt with
    | @gate _ _ c' a b sa sb ka kb aa bb ne nz fresh rest =>
      have out : ∃ q∈candidateChildren s budget (fun w=>s.idxOf w) (stateBoards t s).1 (stateBoards t s).2,
          Run t q.1 n c' ∧ c'≤q.2 := by
        have non : a.toNat≠b.toNat:=fun h=>ne (BitVec.eq_of_toNat_eq h)
        rcases lt_or_gt_of_ne non with l|l
        · exact candidateOf nd (denseCover t s) bounds uniq aa bb l nz fresh rest bound
        · have eq : made a b sa sb=made b a sb sa := by unfold made;rw [BitVec.and_comm]
          rw [swapAfter] at rest
          exact candidateOf nd (denseCover t s) bounds uniq bb aa l (eq ▸ nz) (eq ▸ fresh) rest (by omega)
      obtain ⟨q,mem,rr,db⟩:=out
      exact ⟨q,mem,c',db,rr⟩
  · exact continueRun rt bound
theorem runStepFast {t s n c budget} (rt : Run t s n c) (bound : c≤budget) :
    norm t∈s ∨ ∃k,n=k+1 ∧ ∃p∈verifiedChildren t s budget,∃d≤p.2,Run t p.1 k d := by
  cases n with
  | zero => cases rt;exact Or.inl List.mem_cons_self
  | succ k=>exact Or.inr ⟨k,rfl,continueFast rt bound⟩
end LiveAIG.SparseConflicts

namespace LiveAIG.InputSym

def bank (i : Fin 6) : Nat := ![0xfac688,0xf9ab08,0xf74650,0xf59d10,0xef2a60,0xee9ca0] i
def digit (i : Fin 6) (j : Nat) := (bank i >>> (3*j)) % 8
def rowIndex (i : Fin 6) (r : Nat) := r/8*8 + digit i (r % 8)
def stripe : W := 0x01010101010101010101010101010101
def channel (w : W) (src dst : Nat) := ((w >>> src) &&& stripe) <<< dst

def move (i : Fin 6) (w : W) : W :=
  channel w (digit i 0) 0 |||
  channel w (digit i 1) 1 |||
  channel w (digit i 2) 2 |||
  channel w (digit i 3) 3 |||
  channel w (digit i 4) 4 |||
  channel w (digit i 5) 5 |||
  channel w (digit i 6) 6 |||
  channel w (digit i 7) 7

theorem cardStripe : ∀(r : R) (d : Fin 8),
    (!decide (r.val<d.val) && stripe.getLsbD (r.val-d.val)) = decide (r.val % 8=d.val) := by
  decide +kernel

theorem atChannel (w : W) (src : Nat) (d : Fin 8) (r : R) :
    (channel w src d.val).getLsbD r.val =
      if r.val % 8=d.val then w.getLsbD (r.val/8*8+src) else false := by
  simp only [channel, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    r.isLt, decide_true, Bool.true_and]
  rw [Bool.and_comm (w.getLsbD _) _, ←Bool.and_assoc, cardStripe]
  by_cases h:r.val % 8=d.val
  · simp [h, show src+(r.val-d.val)=r.val/8*8+src by omega]
  · simp [h]

theorem bit_move (i : Fin 6) (w : W) (r : R) :
    (move i w).getLsbD r.val = w.getLsbD (rowIndex i r.val) := by
  have eq (k : Nat) (hk : k<8) : (channel w (digit i k) k).getLsbD r.val =
      if r.val % 8=k then w.getLsbD (r.val/8*8+digit i k) else false :=
    atChannel w (digit i k) ⟨k,hk⟩ r
  simp only [move,BitVec.getLsbD_or]
  rw [eq 0 (by decide)]
  rw [eq 1 (by decide)]
  rw [eq 2 (by decide)]
  rw [eq 3 (by decide)]
  rw [eq 4 (by decide)]
  rw [eq 5 (by decide)]
  rw [eq 6 (by decide)]
  rw [eq 7 (by decide)]
  have bound := Nat.mod_lt r.val (by decide : 0<8)
  generalize h : r.val % 8 = j at *
  interval_cases j <;> simp_all [rowIndex]

theorem inv : ∀i : Fin 6, ∃j : Fin 6, ∀r:R, rowIndex i (rowIndex j r.val)=r.val := by
  decide +kernel
theorem indexBound : ∀i : Fin 6, ∀r:R, rowIndex i r.val<128 := by decide +kernel
theorem indexOrigin : ∀i : Fin 6, rowIndex i 0=0 := by decide +kernel

theorem moveInj (i : Fin 6) : Function.Injective (move i) := by
  intro w z same
  obtain ⟨j,ij⟩:=inv i
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  let r' : R := ⟨rowIndex j r, indexBound j ⟨r,hr⟩⟩
  have h:=congrArg (fun u : W=>u.getLsbD r'.val) same
  change (move i w).getLsbD r'.val=(move i z).getLsbD r'.val at h
  rw [bit_move i w r', bit_move i z r'] at h
  have sameRow : rowIndex i (rowIndex j r)=r := ij ⟨r,hr⟩
  change w.getLsbD (rowIndex i (rowIndex j r))=z.getLsbD (rowIndex i (rowIndex j r)) at h
  rwa [sameRow] at h

theorem moveZero (i : Fin 6) : move i 0=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [bit_move i 0 ⟨r,hr⟩]
  simp

theorem moveAnd (i : Fin 6) (w z : W) : move i (w &&& z)=move i w &&& move i z := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [bit_move i _ ⟨r,hr⟩, BitVec.getLsbD_and, BitVec.getLsbD_and, bit_move i w ⟨r,hr⟩, bit_move i z ⟨r,hr⟩]

theorem moveNeg (i : Fin 6) (w : W) : move i (~~~w) = ~~~(move i w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [bit_move i _ ⟨r,hr⟩]
  simp only [BitVec.getLsbD_not, indexBound i ⟨r,hr⟩, hr, decide_true, Bool.true_and]
  rw [bit_move i w ⟨r,hr⟩]

theorem moveSigned (i : Fin 6) (w : W) (s : Bool) : move i (signed w s)=signed (move i w) s := by
  cases s
  · rfl
  · exact moveNeg i w

theorem moveNorm (i : Fin 6) (w : W) : move i (norm w)=norm (move i w) := by
  have h : (move i w)[0]=w[0] := by
    have eq:=bit_move i w 0
    simpa only [Fin.val_zero, indexOrigin, BitVec.getLsbD_eq_getElem (by decide : 0<128)] using eq
  simp only [norm,moveSigned,h]

theorem moveMade (i : Fin 6) (a b : W) (sa sb : Bool) :
    move i (made a b sa sb)=made (move i a) (move i b) sa sb := by
  simp only [made,moveNorm,moveAnd,moveSigned]

theorem mappedDrop (i : Fin 6) (s : List W) (a : W) (k : Bool) :
    (drop s a k).map (move i)=drop (s.map (move i)) (move i a) k := by
  cases k
  · exact List.map_erase (moveInj i) _
  · rfl

theorem mapRun (i : Fin 6) {t s n c} (r : Run t s n c) :
    Run (move i t) (s.map (move i)) n c := by
  induction r with
  | done=>simpa only [List.map_cons, List.map_nil, moveNorm] using (Run.done (t:=move i t))
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh _ ih=>
    have injective:=moveInj i
    have nz' : made (move i a) (move i b) sa sb≠0 := by
      rw [←moveMade, ←moveZero i]
      exact fun e=>nz (injective e)
    have fresh' : made (move i a) (move i b) sa sb∉s.map (move i) := by
      rintro el
      obtain ⟨w,mem,e⟩:=List.mem_map.mp el
      rw [←moveMade] at e
      exact fresh (injective e ▸ mem)
    apply Run.gate _ _ sa sb ka kb (List.mem_map_of_mem ha) (List.mem_map_of_mem hb)
      (fun e=>ne (injective e)) nz' fresh'
    simpa only [after,List.map_cons,mappedDrop,moveMade] using ih

theorem closedRun (i : Fin 6) {t s n c} (r : Run t s n c) (fixed : move i t=t) :
    Run t (canon (s.map (move i))) n c := by
  exact fixed ▸ canonRun (mapRun i r)

theorem keeps12122 : ∀i : Fin 6, move i 0xfee8e880fe008000fee8e880fe008000 =
    0xfee8e880fe008000fee8e880fe008000 := by decide +kernel

end LiveAIG.InputSym

namespace FivesDag
open LiveAIG LiveAIG.Many LiveAIG.SparseConflicts LiveAIG.InputSym
abbrev State := List W × Nat
abbrev Next := Nat → Option State
abbrev Levels := Nat → Next
abbrev Hints := Nat → Nat → Nat
abbrev Reader := Nat→Nat→Nat×Nat

theorem pairWitness {t s a b w} (aa:a∈s) (bb:b∈s) (h : anchored t s a b w=true) :
    witness t s (anchor w) (anchor (w/128)) a ∧ witness t s (anchor w) (anchor (w/128)) b := by
  simp only [anchored,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨pa,pb⟩:=localSound h.1.2
  obtain ⟨na,nb⟩:=localSound h.2
  exact ⟨⟨aa,pa,na,h.1.1.1⟩,⟨bb,pb,nb,h.1.1.2⟩⟩

def triple (t : W) (s : List W) (h : Nat) :=
  match s[h % 16]?,s[(h/16) % 16]?,s[(h/256) % 16]? with
  | some a,some b,some c=>
    a != b && a != c && b != c && anchored t s a b (h/4096) && anchored t s a c (h/4096)
  | _,_,_=>false

theorem tripleSound {t s h n budget} (nd : s.Nodup) (hit : triple t s h=true)
    (small : budget≤1) (run : Run t s n budget) : False := by
  unfold triple at hit
  split at hit <;> try contradiction
  rename_i a b c ha hb hc
  simp only [Bool.and_eq_true,bne_iff_ne] at hit
  obtain ⟨⟨⟨⟨ab,ac⟩,bc⟩,first⟩,second⟩:=hit
  obtain ⟨wa,wb⟩:=pairWitness (List.mem_of_getElem? ha) (List.mem_of_getElem? hb) first
  obtain ⟨_,wc⟩:=pairWitness (List.mem_of_getElem? ha) (List.mem_of_getElem? hc) second
  let P : Finset W := {a,b,c}
  have size : P.card=3 := by simp [P,ab,ac,bc]
  have bound:=count run nd (anchor (h/4096)) (anchor ((h/4096)/128)) P (by
    intro v m
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with rfl|rfl|rfl
    · exact wa
    · exact wb
    · exact wc)
  omega

def cuts (t : W) (p : State) (z : Nat) :=
  if z<4161536 then p.2==0 && anchorHint t p.1 z
  else decide (p.2≤1) && triple t p.1 (z-4161536)

def Dead (t : W) (p : State) := ∀{n c}, c≤p.2 → ¬Run t p.1 n c

theorem cutsSound {t p z} (nd : p.1.Nodup) (yes : cuts t p z=true) : Dead t p := by
  intro n c small run
  unfold cuts at yes
  split at yes
  · obtain ⟨zero,bad⟩:=Bool.and_eq_true_iff.mp yes
    have zb := eq_of_beq zero
    have : c=0 := by omega
    subst c
    exact anchorHintSound nd bad run
  · obtain ⟨b,bad⟩:=Bool.and_eq_true_iff.mp yes
    exact tripleSound nd bad (small.trans (of_decide_eq_true b)) run

def symIdx (z : Nat) : Fin 6 := ⟨(z-2) % 6,by omega⟩
def shifted (i : Fin 6) (p : State) : State := (canon (p.1.map (move i)),p.2)
def tag (t : W) (next : Next) (p : State) (z : Nat) :=
  if 32768≤z then decide p.1.Nodup && cuts t p (z-32768)
  else next ((z-2)/6)==some (shifted (symIdx z) p)

def checks (t : W) (read : Reader) (next : Next) : List State → Nat → Bool
  | [],_=>true
  | p::ps,n=>let b:=read p.2 n
             tag t next p b.1 && checks t read next ps b.2
def checked (t : W) (read : Reader) (next : Next) (s : List W) (b h : Nat) :=
  !(s.contains (norm t)) && checks t read next (verifiedChildren t s b) h

theorem witness {t read next ps h} {p:State} (check : checks t read next ps h=true) (mem:p∈ps) :
    ∃z, tag t next p z=true := by
  induction ps generalizing h with
  | nil=>simp at mem
  | cons a ps ih=>
    simp only [checks,Bool.and_eq_true] at check
    rcases List.mem_cons.mp mem with rfl|m
    · exact ⟨_,check.1⟩
    · exact ih check.2 m

theorem checkedSound {t read next s b h} (fixed : ∀i : Fin 6, move i t = t)
    (check : checked t read next s b h=true) (later : ∀j p,next j=some p → Dead t p) : Dead t (s,b) := by
  intro n c cap run
  simp only [checked,Bool.and_eq_true,Bool.not_eq_true'] at check
  rcases runStepFast run cap with hit|⟨k,_,p,mem,d,bd,child⟩
  · simpa [hit] using check.1
  · obtain ⟨z,ok⟩:=witness check.2 mem
    unfold tag at ok
    split at ok
    · obtain ⟨nd,yes⟩:=Bool.and_eq_true_iff.mp ok
      exact cutsSound (of_decide_eq_true nd) yes bd child
    · exact later _ _ (eq_of_beq ok) bd (closedRun (symIdx z) child (fixed _))

def site (t : W) (read : Reader) (levels : Levels) (hints : Hints) (k i : Nat) : Bool :=
  match levels k i with
  | none=>true
  | some p=>checked t read (levels (k+1)) p.1 p.2 (hints k i)
def block (t : W) (read : Reader) (levels : Levels) (hints : Hints) (width k b : Nat) :=
  (List.range width).all fun i=>site t read levels hints k (width*b+i)

theorem groupSound {t read levels hints width k size}
    (fixed : ∀i : Fin 6, move i t = t)
    (pos : 0<width)
    (bounded : ∀{i p},levels k i=some p → i<size)
    (next : ∀ j p,levels (k+1) j=some p → Dead t p)
    (groups : ∀b, b<(size+width-1)/width → block t read levels hints width k b=true) :
    ∀ i p, levels k i=some p → Dead t p := by
  intro i p eq
  have lt := bounded eq
  have bb : i/width < (size+width-1)/width := by
    have inc : i/width*width+width ≤ size+width-1 := by
      have := Nat.div_mul_le_self i width
      omega
    have one : (i/width+1)*width ≤ size+width-1 := by simpa [Nat.add_mul] using inc
    exact (Nat.le_div_iff_mul_le pos).mpr one
  have yes:=List.all_eq_true.mp (groups _ bb) (i % width) (List.mem_range.mpr (Nat.mod_lt _ pos))
  have ii : width*(i/width)+i % width=i := Nat.div_add_mod i width
  simp only [ii,site,eq] at yes
  intro n c cap run
  exact checkedSound fixed yes next cap run

end FivesDag

namespace LiveAIG
open FreeAIG
private theorem normZero : norm 0=0 := by decide +kernel
private theorem zeroSide {u : W} (h : norm u=0) (v : W) : norm (u&&&v)=0 ∨ norm (u&&&v)=norm v := by
  rcases normEq u 0 (h.trans normZero.symm) with rfl|rfl
  · left;have eq : (0:W) &&& v=0 := by ext i hi;simp
    rw [eq];exact normZero
  · right;change norm (BitVec.allOnes 128 &&& v)=norm v;rw [BitVec.allOnes_and]
private theorem equalSide {u v : W} (h : norm u=norm v) : norm (u&&&v)=0 ∨ norm (u&&&v)=norm v := by
  rcases normEq u v h with rfl|rfl
  · right;rw [BitVec.and_self]
  · left;rw [BitVec.not_and_self];exact normZero

def Represents (S : Set (Fn X)) (A : Finset W) := ∀g∈S,norm (word g)=0 ∨ norm (word g)∈A
theorem availRep {S A} (rep : Represents S A) {g} (av : Avail S g) : norm (word g)=0 ∨ norm (word g)∈A := by
  induction av with
  | src m => exact rep _ m
  | const b => left; cases b <;> decide +kernel
  | neg _ ih => simpa [wordNeg,normNeg] using ih

theorem operands (u v : W) (A : Finset W) (hu : norm u=0 ∨ norm u∈A) (hv : norm v=0 ∨ norm v∈A)
    (nz : norm (u&&&v)≠0) (nf : norm (u&&&v)∉A) :
    norm u∈A ∧ norm v∈A ∧ norm u≠norm v ∧ norm u≠0 ∧ norm v≠0 := by
  have unu : norm u≠0 := by
    intro e
    have eq: norm (u&&&v)=norm v := (zeroSide e v).resolve_left nz
    rcases hv with v0|vm
    · exact nz (eq.trans v0)
    · exact nf (eq ▸ vm)
  have vnu : norm v≠0 := by
    intro e
    have x:=zeroSide e u
    rw [BitVec.and_comm] at x
    have eq:=x.resolve_left nz
    exact nf (eq ▸ hu.resolve_left unu)
  have um:=hu.resolve_left unu
  have vm:=hv.resolve_left vnu
  exact ⟨um,vm,fun e=>nf ((equalSide e).resolve_left nz ▸ vm),unu,vnu⟩

def Trim (A : Finset W) (k : Nat) (t : W) : Prop :=
  ∃ U : Finset W, U⊆A ∧ 0∉U ∧ ∃ n≤k,∃ c,∀s : List W,s.Nodup → s.toFinset=U → Run t s n c

private theorem dropDedup {s : List W} (nd : s.Nodup) (w : W) (k : Bool) : (drop s w k).Nodup := by
  cases k
  · exact nd.erase w
  · exact nd

private theorem inDrop {s : List W} (nd : s.Nodup) (w x : W) (k : Bool) :
    x∈drop s w k ↔ x∈s ∧ (k=true ∨ x≠w) := by
  cases k <;> simp [drop,nd.mem_erase_iff,and_comm]

private theorem arrange (V : Finset W) (g a b : W) (s : List W) (nd : s.Nodup)
    (eq : s.toFinset=insert a (insert b V)) (new : g∉s) :
    let ka := decide (a∈V)
    let kb := decide (b∈V)
    let dest := after s a b g ka kb
    dest.Nodup ∧ dest.toFinset=insert g V := by
  dsimp only
  have dn:=dropDedup nd a (decide (a∈V))
  have dnn:=dropDedup dn b (decide (b∈V))
  constructor
  · apply List.nodup_cons.mpr
    exact ⟨fun m=>new (dropSubset _ _ _ _ (dropSubset _ _ _ _ m)),dnn⟩
  · ext x
    have ex : x∈s ↔ x=a ∨ x=b ∨ x∈V := by
      rw [←List.mem_toFinset]
      rw [eq]
      simp
    simp only [after,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,inDrop dn,inDrop nd,
      decide_eq_true_eq,ex]
    grind

theorem trim {S : Set (Fn X)} {k : Nat} {f : Fn X} (p : Has S k f) (A : Finset W)
    (rep : Represents S A) (nz : norm (word f)≠0) : Trim A k (word f) := by
  classical
  induction p generalizing A with
  | @done S k f h =>
    have mf := (availRep rep h).resolve_left nz
    refine ⟨{norm (word f)},by simpa using mf,by simpa only [Finset.mem_singleton] using (Ne.symm nz),0,Nat.zero_le _,0,?_⟩
    intro s nd eq
    have eq' : s=[norm (word f)] := by
      have sz : s.length=1 := by simpa [List.toFinset_card_of_nodup nd] using congrArg Finset.card eq
      obtain ⟨w,rfl⟩ := List.length_eq_one_iff.mp sz
      simpa using eq
    rw [eq'];exact .done
  | @step S k f g z hf hg tail ih =>
    let u:=word f
    let v:=word g
    let w:=norm (u&&&v)
    have ex : norm (word (meet f g))=w := by rw [wordAnd]
    have rep' : Represents (insert (meet f g) S) (insert w A) := by
      rintro x (rfl|hx)
      · exact Or.inr (ex ▸ Finset.mem_insert_self ..)
      · exact (rep x hx).imp_right (Finset.mem_insert_of_mem)
    obtain ⟨U,inA,valid,n,cap,c,uses⟩ := ih (insert w A) rep' nz
    by_cases ss : U⊆A
    · exact ⟨U,ss,valid,n,by omega,c,uses⟩
    have picked : w∈U ∧ w∉A := by
      by_contra! no
      apply ss
      intro t mt
      rcases Finset.mem_insert.mp (inA mt) with eq|old
      · subst t;exact no mt
      · exact old
    have w0 : w≠0 := fun e=>valid (e ▸ picked.1)
    obtain ⟨ua,va,ne,uz,vz⟩ := operands u v A (availRep rep hf) (availRep rep hg) w0 picked.2
    let V:=U.erase w
    let a:=norm u
    let b:=norm v
    have sub : V⊆A := by
      intro x hx
      obtain ⟨diff,m⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (inA m)).resolve_left diff
    have pre : insert a (insert b V) ⊆ A := Finset.insert_subset ua (Finset.insert_subset va sub)
    have good : 0∉insert a (insert b V) := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨Ne.symm uz,Ne.symm vz,fun h=>valid (Finset.mem_of_mem_erase h)⟩
    let ka:=decide (a∈V)
    let kb:=decide (b∈V)
    refine ⟨_,pre,good,n+1,by omega,c+ka.toNat+kb.toNat,?_⟩
    intro s nd eq
    have ga : a∈s := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_self ..)
    have gb : b∈s := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have fresh : w∉s := fun hh=>picked.2 (pre (eq ▸ List.mem_toFinset.mpr hh))
    have wm : made a b u[0] v[0]=w := by simp [made,a,b,orient,w]
    apply Run.gate a b u[0] v[0] ka kb ga gb ne (wm ▸ w0) (wm ▸ fresh)
    rw [wm]
    obtain ⟨nd',newSet⟩:=arrange V w a b s nd eq fresh
    apply uses _ nd'
    exact newSet.trans (Finset.insert_erase picked.1)
end LiveAIG

namespace LiveAIG
open FreeAIG

def liveInitial (t : W) (s : List W) : Bool :=
  match s with
  | []=>false
  | a::rest=>accept t (classes t rest) a

theorem initialOk {t : W} {s : List W} {n c : Nat} (run : Run t s n c) : liveInitial t s=true := by
  cases s with
  | nil=>
    cases run with
    | gate _ _ _ _ _ _ h _ _ _ _ _=>simp at h
  | cons w rest=>exact runAccept run

def initialSearch (t : W) (A : List W) (max : Nat) (allow : List W→Nat→Bool) : Bool :=
  A.sublists.any fun s=>liveInitial t s && searchWith t allow max s (max+1-s.length)

theorem initialSearchSound {S : Set (Fn X)} {f : Fn X} {A : List W} {k max : Nat}
    (allow : List W→Nat→Bool)
    (ok : ∀ {s n c budget}, Run (word f) s n c → c≤budget → allow s budget=true)
    (h : Has S k f) (rep : Represents S A.toFinset) (proper : norm (word f)≠0)
    (distinct : A.Nodup) (small : k ≤ max) : initialSearch (word f) A max allow=true := by
  classical
  obtain ⟨U,sub,_,n,sz,c,applyRun⟩:=trim h A.toFinset rep proper
  let s:= A.filter (fun w=> decide (w∈U))
  have setEq : s.toFinset=U := by
    ext w
    change w∈(A.filter (fun w=>decide (w∈U))).toFinset ↔ w∈U
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun hw=>⟨List.mem_toFinset.mp (sub hw),hw⟩⟩
  have run := applyRun s (distinct.filter _) setEq
  have lengths:=balance run
  apply List.any_eq_true.mpr
  refine ⟨s,List.mem_sublists.mpr List.filter_sublist,?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨initialOk run,searchSound ok run (by omega) (by omega)⟩

end LiveAIG

namespace Zero12077
open FreeAIG LiveAIG
def cut (x : X) (i : Fin 5) : Bool := x ⟨i.val, by omega⟩
def val (y : Fin 5 → Bool) : Bool := Nat.testBit 0xfe808000 (∑i : Fin 5, if y i then 2^i.val else 0)
def f : X → Bool := val ∘ cut
def t : W := 0xfe808000fe808000fe808000fe808000
def A : List W := inputs.take 5
def S : Set (Fn X) := {g | ∃ i : Fin 5,g=fun x=>cut x i}
set_option maxRecDepth 65536 in
theorem wordF : word f=t := by decide +kernel
theorem compile {k : Nat} (h : Has Inputs k val) :
    ∃ n≤k,∃c,Run t A n c := by
  classical
  have p : Has S k f := h.map cut (by
    rintro g ⟨i,rfl⟩;exact .src ⟨i,rfl⟩)
  have rep : Represents S A.toFinset := by
    rintro g ⟨i,rfl⟩;right;revert i;decide +kernel
  have nz : norm (word f)≠0 := by rw [wordF];decide +kernel
  obtain ⟨U,sub,_,n,small,c,ok⟩:=trim p A.toFinset rep nz
  let s:=A.filter (fun w=>decide (w∈U))
  have eq : s.toFinset=U := by
    ext w
    change w∈(A.filter (fun w=>decide (w∈U))).toFinset ↔ w∈U
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun hw=>⟨List.mem_toFinset.mp (sub hw),hw⟩⟩
  have nd : A.Nodup := by decide +kernel
  have r:=ok s (nd.filter _) eq
  rw [wordF] at r
  have valid := initialOk r
  have all : A.sublists.all (fun xs=> !liveInitial t xs || xs==A)=true := by decide +kernel
  have one:=List.all_eq_true.mp all s (List.mem_sublists.mpr List.filter_sublist)
  have se : s=A := by simpa [valid] using one
  exact ⟨n,small,c,se ▸ r⟩

end Zero12077

namespace Zero12077Data
open LiveAIG
def repeated (x : Nat) : W := BitVec.ofNat 128 (x * 18446744073709551617)
def raw : List W := [repeated 0xaaaaaaaaaaaaaaaa,repeated 0xcccccccccccccccc,repeated 0xf0f0f0f0f0f0f0f0,repeated 0xff00ff00ff00ff00,repeated 0xffff0000ffff0000]
def anchors : Array Nat := #[1326420,1879841,1881906,1326403,1716035,1879875,1881872,1326693,1457235,33747472,33747745,1326676,1719380,1521490,1716018,1457252,1784386,33780513,1719363,1521507,1881905,33780240,1554256,1784403,1716032,1521472,1814336,1881889,1879858,1781552,1814337,1521506,1781586,1881888,1881904,1554257,1716034,1781553,1879857,1816896,1816897,1879874,33748018,1326642,1521473,1521491,1784385,1816914,1879824,1455954,1522275,1816913,1881923,1554785,1879873,33780786,1326164,1455955,1457218,1554224,1554258,1554786,1716052,1781587,1455972,1457236,1521489,1554273,1554784,1781569,1781570,1781571,1814352,1814353,1879840,1326180,1326640,1390402,1455953,1457202,1522258,1522274,1554272,1683232,1716001,1716033,1784402,1881921]
def decodeStep (_childBudget stream : Nat) : Nat × Nat :=
  let tag:=stream % 4
  let tail:=stream / 4
  if tag < 2 then (tag,tail) else if tag=2 then (2+tail % 4096,tail/4096) else
    let head:=tail % 4
    if head<3 then (anchors[head]?.getD 0,tail/4) else
      (anchors[3+(tail/4) % 256]?.getD 0,tail/1024)
def words0 : Array Nat := #[0xaaaa0000aaaa,0xff000000ff00,0xffaa0000ffaa,0xaa00aa00aa00aa,0xaaaaaa00aaaaaa,0xff000000ff0000,0xff00aa00ff00aa,0x202020202020202,0x300030003000300,0x300ff000300ff00,0x303000003030000,0x3ff000003ff0000,0x808080808080808,0xa000a000a000a00,0xa0a00000a0a0000,0xa0a0a0a0a0a0a0a,0xa0aaaaa0a0aaaaa,0xaaa0aaa0aaa0aaa,0xb0a0b0a0b0a0b0a,0xb0b0a0a0b0b0a0a,0xe0e0e0e0e0e0e0e,0xf0000000f000000,0xf000f000f000f00,0xf00ff000f00ff00,0xf0a0f0a0f0a0f0a,0xf0f00000f0f0000,0xf0f0a0a0f0f0a0a,0xf0f0f000f0f0f00,0xf0ff0f00f0ff0f0,0xff00ff00ff00ff0,0xfff00000fff0000,0x2a2a2a2a2a2a2a2a]
def words1 : Array Nat := #[0x2e2e2e2e2e2e2e2e,0x3030303030303030,0x3c3c3c3c3c3c3c3c,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x8080808080808080,0x8282828282828282,0x8888888888888888,0x8888aaaa8888aaaa,0x88aa88aa88aa88aa,0x8a888a888a888a88,0x8a8a88888a8a8888,0x8a8a8a8a8a8a8a8a,0x8c8c8c8c8c8c8c8c,0x8e8e8e8e8e8e8e8e,0xa0a0a0a0a0a0a0a0,0xa2a2a2a2a2a2a2a2,0xa8a8a8a8a8a8a8a8,0xaa000000aa000000,0xaa00aa00aa00aa00,0xaa00aaaaaa00aaaa,0xaa00ff00aa00ff00,0xaa0aaa0aaa0aaa0a,0xaa888888aa888888,0xaa88aa88aa88aa88,0xaaaa0000aaaa0000,0xaaaa00aaaaaa00aa,0xaaaa0a0aaaaa0a0a,0xaaaa8888aaaa8888,0xaaaaaa00aaaaaa00,0xaaaaeeeeaaaaeeee]
def words2 : Array Nat := #[0xaaaaffaaaaaaffaa,0xaaeeaaeeaaeeaaee,0xaaff0000aaff0000,0xaaffaaaaaaffaaaa,0xaeaeaeaeaeaeaeae,0xaf00af00af00af00,0xafaaafaaafaaafaa,0xafaf0000afaf0000,0xafafaaaaafafaaaa,0xb0b0b0b0b0b0b0b0,0xbabababababababa,0xc0c0c0c0c0c0c0c0,0xc4c4c4c4c4c4c4c4,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcececececececece,0xdcdcdcdcdcdcdcdc,0xeaeaeaeaeaeaeaea,0xee00ee00ee00ee00,0xeeaaeeaaeeaaeeaa,0xeeee0000eeee0000,0xeeeeaaaaeeeeaaaa,0xeeeeeeeeeeeeeeee,0xf000f000f000f000,0xf0f00000f0f00000,0xf2f0f2f0f2f0f2f0,0xf2f2f0f0f2f2f0f0,0xf2f2f2f2f2f2f2f2,0xf4f4f4f4f4f4f4f4,0xf6f6f6f6f6f6f6f6,0xfaf0f0f0faf0f0f0,0xfafafafafafafafa]
def words3 : Array Nat := #[0xfcfcfcfcfcfcfcfc,0xfe00fe00fe00fe00,0xfefe0000fefe0000,0xfefefefefefefefe,0xff000000ff000000,0xff00aa00ff00aa00,0xffaa0000ffaa0000,0xffaaaaaaffaaaaaa,0xffaaffaaffaaffaa,0xffffaaaaffffaaaa,0xffffff00ffffff00]
def wordBlocks : Array (Array Nat) := #[words0,words1,words2,words3]
def extraWord (i : Nat) : W := repeated (((wordBlocks[i/32]?).getD #[])[i % 32]?.getD 0)
def extras : Nat → Nat → List W
  | 0,_=>[]
  | k+1,n=>extraWord (n % 128) :: extras k (n / 128)
def decodeState (n : Nat) : List W × Nat :=
  let used:=(n/8) % 64
  let base:=raw.zipIdx.filterMap fun (w,i)=>if used.testBit i then some w else none
  (canon (base++extras ((n/512) % 8) (n/4096)),n % 8)
def m0b0 : Array Nat := #[0xfc]
def m0 : Array (Array Nat) := #[m0b0]
def m1b0 : Array Nat := #[0x2fa,0x12fa,0x32fa,0x52fa,0xf2fa,0x162fa,0x192fa,0x282fa,0x342fa,0x3a2fa,0x562fa,0x642fa,0x682fa,0x692fa,0x6a2fa]
def m1 : Array (Array Nat) := #[m1b0]
def m2b0 : Array Nat := #[0x320f4f8,0x2ba84f8,0x2c284f8,0x32284f8,0x27344f8,0x32564f8,0x1280479,0x1d01479,0x12034b9,0x42f9,0x1a054b9,0x72f9,0x82f9,0xa2f9,0xc2f9,0xd2f9,0xe2f9,0xb0f4d9,0xc8f4d9,0x108f4d9,0x118f4d9,0x140f4f1,0x180f4f1,0x260f4e9,0x2b8f4d9,0x2c0f4d9,0xf2f9,0x2f8f4d9,0x300f4d9,0x278f4e9,0x102f9,0x112f9]
def m2b1 : Array Nat := #[0x142f9,0x152f9,0xc964d9,0x18164d9,0x2b964b9,0x2c164d9,0x162f9,0x172f9,0x182f9,0x18194d9,0x2b994d9,0x2c19479,0x192f9,0x1a2f9,0x1b2f9,0x1e2f9,0x1f2f9,0x262f9,0x1a284f1,0x1d284f1,0x282f9,0x2b284e9,0x30284e9,0x292f9,0x2a2f9,0x2d2f9,0x322f9,0x332f9,0x1d344f1,0x32344b9,0x342f9,0x34344b9]
def m2b2 : Array Nat := #[0x352f9,0x362f9,0x372f9,0x392f9,0x323a479,0x3a2f9,0x34ba479,0x3b2f9,0x3c2f9,0x3d2f9,0x3e2f9,0x3f2f9,0x402f9,0x412f9,0x422f9,0x432f9,0x442f9,0x452f9,0x462f9,0x472f9,0x482f9,0x512f9,0x522f9,0x532f9,0x542f9,0x552f9,0x562f9,0x632f9,0x672f9,0x227a,0x62ba,0x182da]
def m2b3 : Array Nat := #[0x1a2da,0x1b2da,0x2b284e2,0x2d2f2,0x392f2,0x3d2f2,0x3e2f2,0x356443a,0x652ba,0x6627a,0x5b2da]
def m2 : Array (Array Nat) := #[m2b0,m2b1,m2b2,m2b3]
def m3b0 : Array Nat := #[0x92f8,0xb2f8,0x1a264f0,0x1d264f0,0x139a286e0,0x192b286e0,0x192734638,0x32524b8,0x3254478,0x25884c9,0x258a4c9,0x18140f6c1,0x170f4e1,0x280f4c9,0x248f4d1,0x250f4d1,0x122d9,0x132d9,0x14144e1,0x18964d1,0x18994d1,0x1c279,0x1d2b9,0x301f4c9,0x202e9,0x25a24c9,0x222d9,0x30224c9,0x30264c9,0x2e284c9,0x22284e1,0x29284e1]
def m3b1 : Array Nat := #[0x29a84e1,0x2a284e1,0x2aa84e1,0x2b284e1,0x31a84e1,0x2b2f1,0x2c2f1,0x26ad4e1,0x272d4e1,0x2d2f1,0x27ad4e1,0x2b2d4e1,0x302d4e1,0x191d34631,0x3334439,0x382f1,0x32ba439,0x323e439,0x612b9,0x62279,0x592d9,0x5a2d9,0x5b2d9,0x5e2d9,0x323e432]
def m3 : Array (Array Nat) := #[m3b0,m3b1]
def m4b0 : Array Nat := #[0x31a64c1,0x30274c1,0x30a84a1,0x3128461,0x2ea84c1,0x2e2d4c1,0x2f2e1]
def m4 : Array (Array Nat) := #[m4b0]
def m5b0 : Array Nat := #[0x30a6481,0x3126441]
def m5 : Array (Array Nat) := #[m5b0]
def m6 : Array (Array Nat) := #[]
def m7 : Array (Array Nat) := #[]
def mLevels : Array (Array (Array Nat)) := #[m0,m1,m2,m3,m4,m5,m6,m7]
def h0b0 : Array Nat := #[0x54804a006810a052809200480ea04c807a01080d2050809600280e204a807e00e80ca03f807201a80b604e809e00080da048808600c80c203d807601880ae03c806e01980aa]
def h0 : Array (Array Nat) := #[h0b0]
def h1b0 : Array Nat := #[0xbbbb34f0efbbb18f18fbb18fb09fb09f01f3bf02f54f1df2cf2cf30fb02f02f0ef02483bc3bec0bc0bc0bc77c53c53c53c27c27c27c27ec3bc4beeeec1bc4bc1fc3bc63c63eec71a1b583bc3bc27c27eec7121b383bc3bc0bc3bc67a,0x1edc1fc9fc9fc1fdeedcd3c0ba7bb7b09fb09f34f02c9c9bc0bccfcc3cb3cb3cc3ec0bec0bcd3c0aa702f02f02f53f14f14f14f09f09f09f09f707f06f707f06f77bb1cc86ba0ef0ef09f09fbb1ca86b20ef0ef02f02fbb1c886aa0ef0ef,0x702f02f727f07f710f19f7710f02f7b26f26f33f70cf02f0cf1cf3af10f32fb02f02f02f702f02f07f03081fc1fc73c43c43c43c33c33c33c33ddc0bc0bc1bc1bc1fc1fdc1fc1bddc0bc0bc74a19181fc1fc33c33c0bc0bc74218f81fc1fc0bc1fc5d2,0x1edc9fc1fc1fc9fdeeddeedc9fc102b26fb33f70cf02f0cf27f03e8cbcebcebccbec0bec0bdc0bc0bc0bc9fc0f24ef2ff2ff2ff0cf0cf0cf0cf707f06f707f06f77bb1de861207f07f0cf0cf02f02f1dc860a07f07f02f02f02f02f1da860207f07f,0x37cbfc53c002304f14f1df06c825a1bf04f10f1cf066824208f04f14f46f1bf04f2ff40f04f04f04f04f0a881ca310f14f14f1cf10f10f10f04f04f04f0a281e207d821204f04f04f04f07581fa0df1df04f04f12f1f783bc1821cf1cf04f04f06f1eb81fc16a04f0a2887604f04f04f04f0ae822a1e28566042815227d895604f08484e6,0x7bb73bb70cc837a7b7034836206f07f08f04fb46f704f19f32f04f04f04f04f0688352310fb3cf710f10f10f04f04f04f04f066834a04f04f04f04f77bb12f1d883bc31a70d885e2706f06f04f04f04f04f1ee854e048817204f04f04f04f1ec854604a816a,0x7bb73b7028840a12f0ef7bb70cc83f208f04fb30f704f19f40f04f04f04f04f06e83e2310fb14f710f10f10f04f04f04f04f06c83da04f04f04f04f7102868a77bb06f18a81fc31a312f12f04f04f04f04f1fa853604e818a04f04f04f04f1f8852e0508182,0x5f0cf09f0128c13c27c03248f04f0cf006807c13c27c27c3de134807c13c33c33c34e12e813c13c13c13c5120808c27c27c27c3e6132807c33c33c33c35612c813c13c13c13c51a07e813c13c13c4fa0878502085893201f09f09f09f12f07f0ef07f01f0cf0cf0cf06f0ef07f0ef04f04f04f04f2028492054849a04f087827e04f0858276,0x2c0bc0bec0f216eac43cc7c06619f10f02f1cfb3df31f018867c33c0bc33c73cf7c43c026b02f02f02f0ff85a2b02f02f17a836e06f07f1cf10f10f10f09584b60cf0cf0cf0cf09384b2b02f02f02f12f11d83bc58a02f0db839e1cf10f10f10f20e82fe05a83bc33c33c33c33c8320bd816e0ef02f07f07f,0x2c0bc0bec0aa198ac53c27c77c67cf3c0bc072b09f09f09f01f3bf02f01a877cefcf3c03eb02f02f1a4841612f0efb02f02f02f0e185a21df14f14f14f09b84ce09f09f09f09f09984ca02f105842eb02f02f02f06f0ed81fc58a1df14f02f02f21a82e606081fc27c27c0bc0bc8620b7818607f02f0ef0ef,0x5f0cf09f01e8c13c27d17c5fc13c33d3fcc13c27c27c1bc14a07f210807c13c33c33c1bc13207f204813c13c13c13c88a0468302160807c13c27c27c07c13c33c33c13c13c13c13c2b2149813c2760a38c27c27c27c07c33c33c33c13c13c13c13c2b6148813c27e0a5813c13c13c28e13e82961408932,0x1ddc1bc1fc1bc1fc9aa707f07f707f07f03f7703f0ef19c9ddc0fc1fc5ca03f7703f22c831a03a859a03f11fb1ff0ef19a9c47dc7fc1fc5c21ef11f11f1ff22a831e0388592021801200280567bbb0ef1989edec1fc5ba7bbb2288326036858a01f8016000804e01e800e001804a,0x777707f06f06f07f07f06f22e89da7777707f07f18f772df7772df06f0f081fc65a06f06f23a89727772df0bf01fb01f701f701f06f0f181fc65206f06f23b896a701f741f21f01f1cf41f7bbbb0e781bedec1fc5ea06f06f21f01f1cf1cf01f01f01f01f,0xb0ef0ef7b3706f07f0ef12f0ef12f23489c27bb7733306f10e83bc6ea12f12f240898a00f3b03f730af03f733306f10f83bc6e212f12f241898203f01fb01f701f11f1ff3333310b84bceec3bc69212f12f73bb33333333,0x1c1fc1fdc1fc1fdddc1fc1bc1fc1bc9aa77703f06f11481fc70206f06f24689a203f7703f77703f705f705f06f11581fc6fa06f06f247899a03f0ffb0ff705f705f24f25f25f24f7b7b06f11781fc6f206f06f24989927bbb7b7b2bf0df0df0df05f05f05f05f]
def h1 : Array (Array Nat) := #[h1b0]
def h2b0 : Array Nat := #[0xdfb19f315f22f303f7718f03f733703f,0xffc23c3fc83cc3fc4fdc04221f01f7b,0x10bc23c17c6fcc17c5fdc05a03f705f7,0x3fec67c07cc47c8fcc23c07ab77b0bf733,0x24806205f7bb05f05fb3,0x3fdc0c2702a9cdcd7c2fcc2fc23c07a,0xbc0beec0bc0bc0bc0bc206,0x2f02fbb09f09f702f14f02f09f02fbb02fbbb02f02f02f02f,0xbc0bddc0bc0bc0bc0bc21e,0xbbbb3308f08f77b7777b301f308f01f301f3bb,0x2f02f19f19f26f26fbbbb3efb02f02f02fb02f02f02f02f02f02f,0x333377337733331448cc51633,0xcccc0da3333717f33313f33333333,0xcccc0f23333317f713f3333333333,0x3737333303f733703f3333330f98cc3de,0xeccccc0fdcccc4fccccccccc4e612f33,0xc2bcccccdddccccccccccc4fe06f33,0xcc6fccc2bccccccc6fcccdcccccc1d233333306f,0xccc37c2bcccccccccdcc2bcccccc1ea33333306f,0x23c57c23ce7ccccc57c23c83c23ccccccc16a33330588cccc246,0x47cc47cccccc13a33333304d8cccc27a,0xc6fcc83c23c6fc23c83ccccc10a33333317f313f33333330b68cccc3da,0x30df30af33333317f313f3330d38cccc2ca3306f,0x30df30af3333333303f17f3303f13f333310b8cc51633,0xbc67c57c57ccc23c23ccc2bc83dc2bddc2bc4fc2bc2bc4fdc3b60af0af,0x53eccce7c57c23c23ccc6fc6fc0fdc63ec37c5fc37c37c5fdc3ce0df0df,0x30df30af3333333303f733713f333333333314583e633,0x30df30af3333333306f333310b8cc34e,0xc57cc2bccccccccccc10a33331468cccc41633,0x30df30af3333333318f733713f3333330f98cc2ca,0x2f19f23f05f0df0df77b0df05f05f77b3777b303f3b01f05fb05f05f7,0x31fb11fb03fbbbb0af0af0ff03f77b713f7332df3701f0ff01f7bb]
def h2b1 : Array Nat := #[0xc6fcc2bccccccccccccc1b203f17f33713f33333333331458cccccc51e,0xb7b73333303f703f703f33333333,0x37337333333373373333333306f,0xd13ccabcccc67ddccccd0fccc2bccccccc0e233,0x37bb333303f7703f303f06f,0xb7337771bf23f19f3303f7703f703f17f11fbb,0x37b777333303f03f33703f7733333333,0xb7b72af2ef39f4bf703f73701f703f3701f05f01f05f373b,0x73b773773333333303f03f33703f337733333333,0xd13ccabccc03ececccccc37c2bcccccccc0fa33,0xb77b3318f03f11fb703f3377703f13f0af0af0af,0x37bb333303f7703f303f06f,0xb77b373333703f703f33700f33333333,0x73b773773333333303f03f33703f337733333333,0x73b773773333333303f03f33703f337733333333,0xb7b715f21f15f52f701f703f7300f03f3701fb01f01f3b3b,0xc6fcc83c23c6fc23c83ccccc22a3333333303f17fb08f711f7b3333330fb8cccccc3e633,0xc05a3010823c05208f00e8cccc2a230128c03233330aa8cccc2b203f7b77b7b333333,0x9bc8fcdbc06205f05f2ef3ff1bf08f21f33305f05f01f01f0c29dc17c87ddcdbc03205f05f01f01f05f706f,0x27c47c07c07c07c06a21f42f09f320f08f3301f01f01f01f0ce807c27c0feeec07c04a01f01f01f01fbb12f,0x7c07c07c17cccc07cc17ccccccc34a03f7b77b7b33333333,0xc07cc17ccc03cc07c07c2fcc17c17ccccccccccc28233,0x321f32ef33321f32ef33330d88cccc10a330958cccc2a233,0x1f05f301f01f05f3301f01f77b77b7b301f308f01f3b301f01f,0x1fbbb3b3301f01f03f7b77b7b301f308f01f373bb,0x7c07c07c17ccc03cc07c07c2fcc17c17ccccccccccc40a05780fc07ec07dedeccccccccccc51633,0x3b3b333373b7737b3333333333,0x1f08f08f08f02fb02fbb08f373714a81bec23c07cecc52e06fbb,0xbec0bec43a02fbb02f777723f7b02f7b02fb18fb11fbb7bb06f,0xbc0bcc7c09631f02480bc0beec43ab02f777723f23fb02f7b06fb02f7b12f18fb11fb77,0x2fbbbb02f770af0af05f05f7bbb02f330af3b01f05fbb77,0x2fb02fb11487fec17eeec0bec0bec21e77]
def h2b2 : Array Nat := #[0x2fbbb7701f4df05f05f7bbb737b318f3b01f05fbb77,0x2fb02f02fb02f0af0af0af36f7b7b02f3373701f05fbb373b,0x2f19f2af05f0af19f770af0af05f05f719fb08f733b30af3b01f05fb05f77,0x1f05f701f01f01f701f705f08f01f08f08f01f01f01f01f701fb01f737b301f308f01f3b377,0xbc0bc0bc0a202f02680bc0beec43ab02f7b18f18f11f11fb02f7706fb02f7706f7723f7bb,0x2fbb02f7bbb01f0df01f01f02f37b7b373701f01f01f7bb,0x2fb02fb120857ec07ec0beeec0bec206bb,0x2fb7bbb0df0df0af0ff737b7b7b373701f0ff01f7bb,0x9fb1ffb03fbbb01f0df0ff0ff03f33b7b7b373701f0ff01f7bb,0x1fb03fbbb0bfbbb08f01f08f08f01f01f01f01f03f3bb7b7b301f308f01f301f3bb,0xbec0bec49a7bbb7b7b2bf0df0df0df05f05f05f05f73bb737b30df30df305f305f77,0x737b737b333333337b3b333333,0x2f02f737b07f737b3333333302f02f7b3b333333,0x73bb737b333333333b77333333,0x2fb02f37b7b373701f01f01f7b02f02f02f01f43f01f01f33bb,0x73bb02f02f737b07f333333333b02f02f77333333,0xcdcec07dcdc17ccccccccccc3e200f301f01f0bf305f05f333333333305b82d233,0x11f1ef11f0af2af2ef77b08f11f370af3b01f05f01f05f0af1ef0af21f11f2af337b,0x3373b01f7370af33733306f3333330618382301f30af33333333,0x14f47f09f1df15f21f14f377708f00f73701fb01f01f01f14f01f47f11f15f33bb,0x3373b01f7370af33733306f333333067839a301f30af33333333,0x73701f73705f33333333333333,0xfbc0aa0af13f700a9cd7c07ccdcc0fc17c07c83c4fc07edc17c17c07c4fc4fccdec17c17c17c17c2ea,0x1cdc07dcdc17ccccccccccccc1bc03ecc17ccccccccc302,0x27c0c209f45f09f370049cd7cdcc0fc07c27c07c5fc07c07ec07c07c27c07c5fcceec07c07c07c07c31a,0x1cec07dcdc17ccccccccccccc4bcc07dc17ccccccccc332,0x1cdc07dcdc17ccccccccccccccccc34a,0x77ce3dcdc5fc1fc4ca0af0bf73713f07f12c8cccccccc36e3333330d98cccc362,0xb773b706f7737b712f73330af706f11e9cccc2fdc1bc472bb7737bb771af22f0bf0bf,0x7bb7726f02f33f1df2cf2cf30f702f02f02f1df14f14f14f09f09f09f09f77bb77bb09f09fbb02f02fbb,0x7bb7b15fb15f0af15f1af20fb02fb02f0af15f1af1af0af15f15f15f77bb77bb15f20f02f02f02f02f02f02f,0x777703f08f703f708f703f00f3b15f7371ff33337733773333333333]
def h2b3 : Array Nat := #[0x777703f08f703f708f703f00f3b15f7371ff33337733773333333333,0x777703f08f703f708f703f00f3b15f7371ff33337733773333333333,0xdfc17c3fc07a00f30ff17f13f305f13f00f301f01f040831a0bf305f05f03a82ea33330d881b20bf01f01f01f0bf01f05f05f333308e82b2309a829a,0x1ef05f0ff1ef00f30ff17f13f305f13f0bf01f01f01f07983c20bf01f05f05f07383aa3333108812a0bf01f01f01f0bf01f05f05f333333330fc815e,0x77771ef7717f77713f0bf01f01f01f701f705f06f06f08f01f08f08f701f01f01f701f705f08f01f08f08f01f01f01f01f,0x3fbb03f03f08fb03f03f08f05f03f03f01fb01f12f12f0bf01f05f05f08f01f08f08f03fbbb0bfbbb08f01f08f08f01f01f01f01f,0x1dddc1fc1bc1fc1bc54203f7703f77703f03f0ffb0ff705f705f24f25f25f24f7bbb7b7b2bf0df0df0df05f05f05f05f,0x707f07f77703f07f12a81bc1bc55203f7703f70ff70ff07f12881bc1bc54a1ef11f11f1ff24f25f25f24f7b7b07f12681bc1bc5427bbb2bf0df0df0df0ff0ff0ff0ff,0x1eedc03cec0fdcc2bc0fc0fc07ec07dc07c47c7fccccdceec3bc48212f12f73bb33333333,0x1dddc03cdcb7dcdcb7c2fc07ec07dc07dc17ccccdceedcdec1fc45206f06f33333333,0x7bb700f3b17f7305f13f0bf01fb01f701f05f05f333373bb73bb333305f83f6333305182c2]
def h2 : Array (Array Nat) := #[h2b0,h2b1,h2b2,h2b3]
def h3b0 : Array Nat := #[0x4af,0xbf,0x16f00f00f77,0x1af00f00f03f03f,0xb37f,0x4cf18f700f16f51f00f,0xb7b0ff,0x777,0x7718f,0xf00f22f00f00f29f00f00f00f00f,0xf00f00f22f29f00f00f00f00f00f,0xf22f00f29f00f00f00f00f00f00f,0xfdc0fddc03ddc03dc092,0x1dc03dc09e700f,0xfdc0fdddc03dc08a700f,0x1dc03dc086700f,0xf00f00f00f,0xf00f00f00f,0x3c8bc03ca7c03c03c03c03c6bc03c5bc03c03c03c03c03c03dc092,0x3f7703f00f00f00f00f,0x703f03f700f00f00f00f,0x0,0x0,0x3c6bc03c5bc03c03c03c03c03c03c03dc09e00f00f,0xf1af00f16f00f00f00f00f00f00f00f00f,0xfdc0fddc03ddc03dc06e,0x7777,0x1c03ddc03dc01a,0x3c6bc03c5bc03c6bc03c5bc03c03c03c03c00200f00f00f00f,0xf0bf00f16f00f00f00f00f77,0xf0bf00f16f00f00f00f00f77,0x19f729f16f22f16f0bf00f00f00f70bf16f16f0bf7]
def h3b1 : Array Nat := #[0xf0bf00f16f00f00f00f00f77,0xb18f0ff17f01f00f29f16f00f00f0bfb0bf1af0bf7,0xf0bf00f16f00f00f00f00f77,0xf0bf00f16f00f00f00f00f77,0x6fc5fc03c6bc04a29f16f00f16f00c803c03c03c03c03c03c03c03c002,0x70bf71ef00f700f7,0x70bf71ef00f00f00f7,0x77700f0bf700f700f7,0xb03f01f7700f00f700f7,0x70bf71ef00f700f7,0xbf0bf0bf37f00f00f00f00f77,0xf0bf00f16f00f00f00f00f77,0xf1af00f16f7700f00f00f00f,0xb02f777723f7b02f7b18fb11fbb7bb06f,0xbb77,0x70bf71ef16f22f0bf7,0xbbbb,0x7b7b2bf70df70ff0ff0ff0ff7b0df0df0ff0ff77,0x3c03c03c03c03e00f00f00f00f00d803c03c03c03c032,0x3c03c03c03c05600f00f00f00f013803c03c03c03c04a,0x700f700f,0x700f700f,0x700f700f,0x700f00f00f,0x3f7703f1ef11f11f1ff24f25f25f24f7bbb2bf0df0df0df0ff0ff0ff0ff]
def h3 : Array (Array Nat) := #[h3b0,h3b1]
def h4b0 : Array Nat := #[0x22f1af28f50f006927ce3ca3ce3c00228f28f,0x0,0x1ca3dca3c002,0x63ca3c63c6bc01a,0x0,0x0,0x0]
def h4 : Array (Array Nat) := #[h4b0]
def h5b0 : Array Nat := #[0x0,0x0]
def h5 : Array (Array Nat) := #[h5b0]
def h6 : Array (Array Nat) := #[]
def h7 : Array (Array Nat) := #[]
def hLevels : Array (Array (Array Nat)) := #[h0,h1,h2,h3,h4,h5,h6,h7]
def lengths : Array Nat := #[1,15,107,57,7,2,0,0]
def levelSize (level : Nat) : Nat := lengths[level]?.getD 0

def blockGet (all : Array (Array (Array Nat))) (level id : Nat) : Option Nat := do
  let base←all[level]?
  let slab←base[id/32]?
  slab[id % 32]?

def stateAt (level id : Nat) : Option (List W × Nat) :=
  if id < levelSize level then (blockGet mLevels level id).map decodeState else none

def hintAt (level id : Nat) : Nat := (blockGet hLevels level id).getD 0
end Zero12077Data

namespace Zero12077
open LiveAIG FivesDag Zero12077Data
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sym : ∀i, InputSym.move i t=t := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group5_0 : block t decodeStep stateAt hintAt 16 5 0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem layer5 : ∀i p,stateAt 5 i=some p → Dead t p := by
  apply groupSound (width:=16) (size:=2) (read:=decodeStep) (hints:=hintAt) sym (by decide)
  · intro i p eq
    have h:i<levelSize 5 := by by_contra! bad;simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · intro j p h
    have emp : levelSize 6=0 := by decide
    simp [stateAt,emp] at h
  · intro b hb
    change b<1 at hb
    interval_cases b
    · exact group5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group4_0 : block t decodeStep stateAt hintAt 16 4 0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem layer4 : ∀i p,stateAt 4 i=some p → Dead t p := by
  apply groupSound (width:=16) (size:=7) (read:=decodeStep) (hints:=hintAt) sym (by decide)
  · intro i p eq
    have h:i<levelSize 4 := by by_contra! bad;simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact layer5
  · intro b hb
    change b<1 at hb
    interval_cases b
    · exact group4_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group3_0 : block t decodeStep stateAt hintAt 16 3 0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group3_1 : block t decodeStep stateAt hintAt 16 3 1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group3_2 : block t decodeStep stateAt hintAt 16 3 2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group3_3 : block t decodeStep stateAt hintAt 16 3 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem layer3 : ∀i p,stateAt 3 i=some p → Dead t p := by
  apply groupSound (width:=16) (size:=57) (read:=decodeStep) (hints:=hintAt) sym (by decide)
  · intro i p eq
    have h:i<levelSize 3 := by by_contra! bad;simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact layer4
  · intro b hb
    change b<4 at hb
    interval_cases b
    · exact group3_0
    · exact group3_1
    · exact group3_2
    · exact group3_3
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_0 : block t decodeStep stateAt hintAt 16 2 0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_1 : block t decodeStep stateAt hintAt 16 2 1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_2 : block t decodeStep stateAt hintAt 16 2 2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_3 : block t decodeStep stateAt hintAt 16 2 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_4 : block t decodeStep stateAt hintAt 16 2 4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_5 : block t decodeStep stateAt hintAt 16 2 5=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group2_6 : block t decodeStep stateAt hintAt 16 2 6=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem layer2 : ∀i p,stateAt 2 i=some p → Dead t p := by
  apply groupSound (width:=16) (size:=107) (read:=decodeStep) (hints:=hintAt) sym (by decide)
  · intro i p eq
    have h:i<levelSize 2 := by by_contra! bad;simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact layer3
  · intro b hb
    change b<7 at hb
    interval_cases b
    · exact group2_0
    · exact group2_1
    · exact group2_2
    · exact group2_3
    · exact group2_4
    · exact group2_5
    · exact group2_6
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group1_0 : block t decodeStep stateAt hintAt 16 1 0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem layer1 : ∀i p,stateAt 1 i=some p → Dead t p := by
  apply groupSound (width:=16) (size:=15) (read:=decodeStep) (hints:=hintAt) sym (by decide)
  · intro i p eq
    have h:i<levelSize 1 := by by_contra! bad;simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact layer2
  · intro b hb
    change b<1 at hb
    interval_cases b
    · exact group1_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem group0_0 : block t decodeStep stateAt hintAt 16 0 0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem layer0 : ∀i p,stateAt 0 i=some p → Dead t p := by
  apply groupSound (width:=16) (size:=1) (read:=decodeStep) (hints:=hintAt) sym (by decide)
  · intro i p eq
    have h:i<levelSize 0 := by by_contra! bad;simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact layer1
  · intro b hb
    change b<1 at hb
    interval_cases b
    · exact group0_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem lower {k} (h : FreeAIG.Has FreeAIG.Inputs k val) : 9≤k := by
  by_contra! small
  obtain ⟨n,cap,c,run⟩ := compile h
  have len : A.length=5 := by decide +kernel
  have b := balance run
  have root : stateAt 0 0=some (A,4) := by decide +kernel
  rw [len] at b
  exact layer0 0 _ root (by omega) run
end Zero12077

namespace FiveOne12076Data
open LiveAIG
def repeated (x : Nat) : W := BitVec.ofNat 128 (x * 18446744073709551617)
def raw : List W := [repeated 0xaaaaaaaaaaaaaaaa,repeated 0xcccccccccccccccc,repeated 0xf0f0f0f0f0f0f0f0,repeated 0xff00ff00ff00ff00,repeated 0xffff0000ffff0000]
def tokens0 : Array Nat := #[0x62e71,0x33771,0xc2e71,0x182779,0x1ab59,0x302779,0xc2e67,0x73771,0x62b59,0x32b59,0x3b771,0x282979,0x132c6f,0x183379,0x142979,0x16296f,0x6296f,0x92e6b,0x11ac6f,0x14aa6f,0x2aa6f,0x152a6f,0x63771,0x242975,0x32e71,0x10a979,0x242979,0x92a5b,0xb296f,0xe3771,0x13296f,0x222c6f]
def tokens1 : Array Nat := #[0x52a6f,0xaaa6f,0x162c6f,0x2ab71,0x143575,0x24,0x4b771,0xc295d,0x112d6d,0x123673,0x142c75,0x182773,0x212c6f,0xc,0x18,0x30,0x9c,0xa8,0x6a96f,0xa3575,0x112c75,0x113673,0x14a96f,0x1c296f,0x282a79,0x0,0x6,0x14,0x20,0x28,0x2c,0x34]
def tokens2 : Array Nat := #[0x38,0x42,0x4e,0x54,0x56,0x5a,0x60,0x90,0xf0,0x120,0x1e0,0x1f8,0x4aa6f,0x52d71,0x72c6f,0x8ab6b,0xc2779,0xd296f,0x12a96f,0x15296f,0x222975,0x4,0x8,0x10,0x1a,0x1c,0x32,0x36,0x3a,0x3c,0x3e,0x46]
def tokens3 : Array Nat := #[0x48,0x4a,0x52,0x58,0x64,0x66,0x68,0x6c,0x70,0x72,0x74,0x78,0x7a,0x7e,0x80,0x84,0x8c,0x94,0x98,0x9e,0xa0,0xa4,0xaa,0xac,0xb6,0xc2,0xc6,0xce,0xd2,0xde,0xec,0xfc]
def tokens4 : Array Nat := #[0x100,0x104,0x10e,0x112,0x118,0x11c,0x124,0x128,0x12c,0x134,0x138,0x13c,0x140,0x14a,0x14e,0x154,0x158,0x15c,0x160,0x164,0x170,0x17e,0x180,0x192,0x198,0x1a4,0x1b0,0x1bc,0x1c8,0x1ca,0x1d4,0x1d6]
def tokens5 : Array Nat := #[0x1da,0x1f0,0x1f4,0x204,0x208,0x20c,0x210,0x1ac6f,0x1b771,0x32d71,0x6ac6f,0x8a773,0x92773,0x92b6b,0xa2d71,0xb2a6f,0xca96f,0x10ab6d,0x122d6d,0x12aa6f,0x142e67,0x142e6b,0x182e67,0x20aa6f,0x212c73]
def tokenTable : Array (Array Nat) := #[tokens0,tokens1,tokens2,tokens3,tokens4,tokens5]
def decodeStep (_b stream : Nat) : Nat × Nat :=
  let k:=stream % 256
  ((((tokenTable[k/32]?).getD #[])[k % 32]?.getD 0),stream/256)
def words0 : Array Nat := #[0xaaaa0000aaaa,0xff000000ff00,0xffaa0000ffaa,0x88008800880088,0xaa000000aa0000,0xaa00aa00aa00aa,0xaaaaaa00aaaaaa,0xff000000ff0000,0xa0a0a0a0a0a0a0a,0xa0aaaaa0a0aaaaa,0xaaa0aaa0aaa0aaa,0xf000f000f000f00,0xf0a0f0a0f0a0f0a,0xf0f00000f0f0000,0xf0f0f000f0f0f00,0xf0ff0f00f0ff0f0,0xfff00000fff0000,0x2a2a2a2a2a2a2a2a,0x3c3c3c3c3c3c3c3c,0x3f3f00003f3f0000,0x8080808080808080,0x8888000088880000,0x8888888888888888,0x8888aaaa8888aaaa,0x88aa88aa88aa88aa,0x8a8a8a8a8a8a8a8a,0xa0a0a0a0a0a0a0a0,0xa8a8a8a8a8a8a8a8,0xaa00aa00aa00aa00,0xaa00aaaaaa00aaaa,0xaa0aaa0aaa0aaa0a,0xaa80aa80aa80aa80]
def words1 : Array Nat := #[0xaa88aa00aa88aa00,0xaa88aa88aa88aa88,0xaaaa0000aaaa0000,0xaaaa00aaaaaa00aa,0xaaaa0a0aaaaa0a0a,0xaaaa8888aaaa8888,0xaaaaaa00aaaaaa00,0xaaff0000aaff0000,0xafaf0000afaf0000,0xc0c0c0c0c0c0c0c0,0xeeee0000eeee0000,0xeeeeeeeeeeeeeeee,0xf0f00000f0f00000,0xff000000ff000000,0xff0f0000ff0f0000,0xff880000ff880000,0xff88ff88ff88ff88,0xffaa0000ffaa0000,0xffaaff00ffaaff00,0xffaaffaaffaaffaa,0xffffaaaaffffaaaa,0xffffff00ffffff00]
def wordBlocks : Array (Array Nat) := #[words0,words1]
def extraWord (i : Nat) : W := repeated (((wordBlocks[i/32]?).getD #[])[i % 32]?.getD 0)
def extras : Nat → Nat → List W
  | 0,_=>[]
  | k+1,n=>extraWord (n % 64) :: extras k (n / 64)
def decodeState (n : Nat) : List W × Nat :=
  let used:=(n/8) % 64
  let base:=raw.zipIdx.filterMap fun (w,i)=>if used.testBit i then some w else none
  (canon (base++extras ((n/512) % 8) (n/4096)),n % 8)
def m0b0 : Array Nat := #[0xfc]
def m0 : Array (Array Nat) := #[m0b0]
def m1b0 : Array Nat := #[0x2fa,0x12fa,0x52fa,0x72fa,0x82fa,0xb2fa,0xd2fa,0x162fa,0x1c2fa,0x222fa,0x2b2fa,0x2d2fa,0x332fa,0x342fa,0x352fa]
def m1 : Array (Array Nat) := #[m1b0]
def m2b0 : Array Nat := #[0xb164f8,0x881479,0x32f9,0x42f9,0x62f9,0x92f9,0xa2f9,0x68b4d9,0xb0b4d9,0x102f9,0x112f9,0x132f9,0x142f9,0x152f9,0x7164f1,0x162f9,0x172f9,0x182f9,0x192f9,0x1b2f9,0x89c4f1,0x1d2f9,0x1e2f9,0x212f9,0xb62479,0x222f9,0x232f9,0x242f9,0x252f9,0x262f9,0x272f9,0x282f9]
def m2b1 : Array Nat := #[0x2a2f9,0x2e2f9,0x302f9,0x312f9,0x322f9,0x227a,0xc2da,0xe2da,0xad64e2,0x212f2,0xd22472,0x262f2,0x3127a]
def m2 : Array (Array Nat) := #[m2b0,m2b1]
def m3b0 : Array Nat := #[0xb0f459,0xa524c9,0x1f2f1,0x202f1,0x2f279]
def m3 : Array (Array Nat) := #[m3b0]
def m4 : Array (Array Nat) := #[]
def mLevels : Array (Array (Array Nat)) := #[m0,m1,m2,m3,m4]
def h0b0 : Array Nat := #[0x31252d6f7560566a725d3c6674615568715e59646d403f453042396747412e466c5c2f446b5b5a43]
def h0 : Array (Array Nat) := #[h0b0]
def h1b0 : Array Nat := #[0x202001d0701160d0100160201010d0d0d003802383529293500020207b0070700020202102402020d0d020200070a000002020a0a070701010202128e07070d0d0202138d0707020788,0x200071d1d07010808011d3b0008020101080d0d1d5700ae021b20292935000202021d2d00020202102402020d0d020200070a00070a01010808128c0707090d0d0d138b0707020202020f8a0707,0x20200090808090008020916080b0b000b020b1f170b0b000202020002020f370f0f101702020b0b0202000002020a970725000f1e0909020212830c580b0b02021382152e020f0f,0x2001d07071d010808010008020101080b0b000b020b20170b0b0002020200020202101702020b0b020200070a00070a0101020212810c3e0b0b02021380153d020202020f7f0f25,0x20200030517280005021f220c33b22428001f022c0505050500020202000202020505020c360c0c05050202000002020a95070c0000020212120c0c050c1205050202137d0c0c020c78,0x1080801010508012246010801220c0c2201081628091f082c050505052263010816080917081705050505224305050505010105050a94070c010c12010c1205050505137c0c0c050505050f7b0c0c,0x1080801010801aa4e0a0701050801220c0108161b091f081b0505050501081608092708270505050505050505014e890101050512120c0c010a0a05050505137a0c0c050505050f790c0c,0x2020003050d39000502b8060d0b0b000b020b4477050505050002020200020202453105050202050502365313154a000202020a7007300002020298072e0705050202126e0c4705530f021515,0x20200162717540017021f16270b0b000b020b1f170b0b000202020f480002020f371e0f101702020f760b0b02020f31000202020a69070c02370f1f17020212620c070b0b020213421507020f0f,0x202002d49090808090008020906080d0d0038021bb4b6b53a00020232510a074b000202026548102402020d0d020202510f000202029a0c250c09080202125f0c730d0d020213411530020707,0xe0b0d4c03050db11a050bb7060d0d0d0a0f0796060b0b0b0a0f071305050505120f0c7e060d0b0b060b0b0b05050505051515060d0d0d1a0b0b0b05050505050f13050505153613134a,0x100000a070a070007070007070101010407870401000404010104120c40130109012607860420002614092010b3153f0f14204d2301000000074901000000010000001e0f2f0ca71000004c100000,0x1000001321c0a0f07999ba601000001000f0f01090904010900040a0c0f85521e9ca2040900040109161a011a001a0a150f84521e9da1041a001a2c541a1a01000000000f1e0000000f0f1e1e2c1000001a100000,0x707010000010a07070a01000001010101110a0c079001010111180100a8010601060a15078f010601061806002611062b2b000f0a00000007320a0a4b010000001110000006060000,0x707000707000001070a070a010100040a0c07930a0a9ea50101010404010004010e000e0a1507920a0a9fa40109010e040e000e14200e0e010000000a0f07910a0aa0a30100000001000000341000000e0e0000]
def h1 : Array (Array Nat) := #[h1b0]
def h2b0 : Array Nat := #[0x502b0e2b004f1109110911060000,0x202000208020d020202020002020202070202,0x900000001040000000403040000000e0000,0x20000000001000103040000030e00000000,0x3000300010100000101000003030000030300000000,0x2002a000000040010000e00010400000401000003110000030e00000000,0x100000016000600010100000101000003040000030600000000,0x2a2a08080908030303030300030300031c0300,0x80103030108a9192a08030301010701040104,0x801080101080108010401040001010401000606060606000600,0x3000e00000004000300030001040000040e000003030000030300000000,0x208090800161b23000202020004000000012301060103060300000000,0x3000e0000000100000004000000030303030000,0x200060000000200040000000309000006060000,0xe000200000e03002100000002040009000e0e0000000021,0x6000000000303002101000000040000000303000003030000,0x6000000000003000300010000000400000003030000030300000000,0x300010000000100000003030000030300000000,0x6001800000003000300010000000400000003030000030300000000,0x3000300010000000100000003030000030300000000,0x20002000002010009000e00000201000a0200000000000a,0x2000000010010000e00010000000100000003010000030e00000000,0x19000000040010000e00010000000400000003010000030e00000000,0x60018000000040000000303000003030000010000000400000003030000030300000000,0x2020000000201000a00020100000201001c09004d000000,0x200000201000a000002000100000003090000030600000000,0x1000000010000000100000003090000030600000000,0x2000100000033000600010000000100000003090000030600000000,0x100000003000300010000000100000003030000030300000000,0x20001000000010000001110000006060000010000000100000003100000030600000000,0x2000200010000000301000006060000000200000000,0x1b100d23061b10060101000301090100030603060610100603030000]
def h2b1 : Array Nat := #[0x904090409060109000303010304060903000106060903030000,0x400040000010104010101040104010e14060303000001000000,0x401000004072f00000101000409040a3c0406000304041c000e04040100000004042100000404,0x1000001010000010109090401010904010606060106060601000000010000000101,0x1010000011c0001000100000101000409010a3e0106000e04010a3d0100000001010a00000101,0x802010014021b2014142800020202102402020d0d02020000020201010808090d0d0d02020202,0x1010101010801190914011901080108091908190303030301010103010103030303030303030303,0x1010101010801190914011901080108091908190303030301010103010103030303030303030303,0x140000145003ad4f18030034140606061406000e1c2103030303180000001800000003030000033b21,0x40000040403090404030004140606060406000eaf210303030318000000040000000303000003030000,0x1000001070a010101111801003401060106180600261106acab003a0a010000001133000006060000,0x1000001070a0101010404010004010601060406000e11060e0e01000000010000001110000006060000,0x10000010109090404090004010606060406000e11060e0e01000000010000001c1c1110000006060000]
def h2 : Array (Array Nat) := #[h2b0,h2b1]
def h3b0 : Array Nat := #[0x4010101,0x23010123,0x9040404,0x40104,0x4040404]
def h3 : Array (Array Nat) := #[h3b0]
def h4 : Array (Array Nat) := #[]
def hLevels : Array (Array (Array Nat)) := #[h0,h1,h2,h3,h4]
def lengths : Array Nat := #[1,15,45,5,0]
def levelSize (level : Nat) : Nat := lengths[level]?.getD 0

def blockGet (all : Array (Array (Array Nat))) (level id : Nat) : Option Nat := do
  let base←all[level]?
  let slab←base[id/32]?
  slab[id % 32]?

def stateAt (level id : Nat) : Option (List W × Nat) :=
  if id < levelSize level then (blockGet mLevels level id).map decodeState else none

def hintAt (level id : Nat) : Nat := (blockGet hLevels level id).getD 0
end FiveOne12076Data

namespace LiveAIG.InputSym
open SparseConflicts
theorem knownBasic {t s n c budget a b sa sb ka kb}
    (ha : a∈s) (hb : b∈s) (lt : a.toNat<b.toNat)
    (nz : made a b sa sb ≠ 0) (fresh : made a b sa sb ∉ s)
    (run : Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound : c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb), budget-(ka.toNat+kb.toNat))∈children t s budget := by
  let g:=made a b sa sb
  let remaining:=drop (drop s a ka) b kb
  let spent:=ka.toNat+kb.toNat
  have spentOk : spent≤budget := by dsimp [spent];omega
  have checked : accept t (classes t remaining) g=true := runAccept run
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos lt]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold phaseKids
  rw [if_pos spentOk]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if g != 0 && !s.contains g && accept t (classes t remaining) g then
      some (canon (g::remaining),budget-spent) else none) = some _
  have avoid : g∉s := fresh
  have val : g≠0 := nz
  simp [avoid,checked]
  exact ⟨val,rfl,rfl⟩

theorem knownSparse {t s index p n a b sa sb ka kb k c budget} (nd:s.Nodup)
    (cov:Cover t s index p n) (bounds:∀w∈s,index w<12) (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (aa:a∈s) (bb:b∈s) (lt:a.toNat<b.toNat) (nz:made a b sa sb≠0) (fresh:made a b sa sb∉s)
    (run:Run t (after s a b (made a b sa sb) ka kb) k c) (bound:c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb), budget-(ka.toNat+kb.toNat))∈candidateChildren s budget index p n := by
  let A:=entry p n a (index a)
  let B:=entry p n b (index b)
  have ne : a≠b := by intro h;subst b;omega
  have pass:=legalSound nd (ruleForTrue cov bounds uniq aa bb ne) run
  let spent:=ka.toNat+kb.toNat
  let rest:=drop (drop s a ka) b kb
  have paid : spent≤budget := by dsimp [spent];omega
  unfold candidateChildren
  refine List.mem_flatMap.mpr ⟨A,List.mem_map.mpr ⟨a,aa,rfl⟩,List.mem_flatMap.mpr ⟨B,List.mem_map.mpr ⟨b,bb,rfl⟩,?_⟩⟩
  have vals : A.w.toNat < B.w.toNat := lt
  rw [if_pos vals]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold options
  rw [if_pos paid]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if legal (ruleFor p n A B) ka kb sa sb then
    if made a b sa sb != 0 && !s.contains (made a b sa sb) then some _ else none else none) = some _
  simp [A,B,pass,fresh,rest,spent]
  exact ⟨nz,rfl⟩

theorem knownLT {t s n c a b sa sb ka kb budget}
    (ha:a∈s) (hb:b∈s) (lt:a.toNat<b.toNat) (nz:made a b sa sb≠0)
    (fresh:made a b sa sb∉s) (tail:Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound:c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb), budget-(ka.toNat+kb.toNat))∈verifiedChildren t s budget := by
  unfold verifiedChildren
  split <;> rename_i cond
  · obtain ⟨small,nd⟩:=cond
    have bounds : ∀w∈s,s.idxOf w<12 := fun w h=>lt_of_lt_of_le (List.idxOf_lt_length_of_mem h) small
    have uniq : ∀w∈s,∀z∈s,s.idxOf w=s.idxOf z → w=z := by
      intro w h z m eq
      have hw:=List.getElem_idxOf (x:=w) (xs:=s) (List.idxOf_lt_length_of_mem h)
      have hz:=List.getElem_idxOf (x:=z) (xs:=s) (List.idxOf_lt_length_of_mem m)
      rw [←hw,←hz];simp [eq]
    exact knownSparse nd (denseCover t s) bounds uniq ha hb lt nz fresh tail bound
  · exact knownBasic ha hb lt nz fresh tail bound

theorem known {t s n c a b sa sb ka kb budget}
    (ha:a∈s) (hb:b∈s) (ne:a≠b) (nz:made a b sa sb≠0)
    (fresh:made a b sa sb∉s) (tail:Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound:c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb),budget-(ka.toNat+kb.toNat))∈verifiedChildren t s budget := by
  have diff : a.toNat≠b.toNat:=fun h=>ne (BitVec.eq_of_toNat_eq h)
  rcases lt_or_gt_of_ne diff with low|high
  · exact knownLT ha hb low nz fresh tail bound
  · have e : made a b sa sb=made b a sb sa := by unfold made;rw [BitVec.and_comm]
    rw [swapAfter] at tail ⊢
    rw [Nat.add_comm ka.toNat kb.toNat]
    exact knownLT hb ha high (e ▸ nz) (e ▸ fresh) tail (by omega)

def born (s next : List W) := (next.find? (fun w=> !s.contains w)).getD 0

theorem freshBorn {s next : List W} {g : W} (fresh:g∉s) (one:g∈next)
    (subset : ∀w∈next,w=g∨w∈s) : born s next=g := by
  unfold born
  cases h : next.find? (fun w=> !s.contains w) with
  | none =>
    have no := List.find?_eq_none.mp h g one
    simp [fresh] at no
  | some v =>
    obtain same|old := subset v (List.mem_of_find?_eq_some h)
    · simpa [same]
    · have yes := List.find?_some h
      simp [old] at yes

theorem canonSubset {s : List W} {a b g : W} {ka kb : Bool} :
    ∀w∈canon (after s a b g ka kb),w=g ∨ w∈s := by
  intro w m
  have z:= (List.perm_insertionSort _ _).mem_iff.mp m
  rcases List.mem_cons.mp z with eq|old
  · exact .inl eq
  · exact .inr (dropSubset _ _ _ _ (dropSubset _ _ _ _ old))

end LiveAIG.InputSym

namespace LiveAIG.DirectLayers
open InputSym SparseConflicts
abbrev State := List W × Nat
abbrev Reader := Nat→Nat→Nat×Nat
abbrev Next := Nat→Option State

structure Setup where
  t : W
  fixed : ∀i,move i t=t
  cut : Nat→State→Nat→Bool
  sound : ∀{d p z n c},p.1.Nodup → cut d p z=true → n≤d → c≤p.2 → ¬Run t p.1 n c

def index (z : Nat) : Fin 6 := ⟨(z/2) % 6,by omega⟩
def shifted (i : Fin 6) (p : State) : State := (canon (p.1.map (move i)),p.2)
def tagOk (cfg : Setup) (next : Next) (d : Nat) (p : State) (z : Nat) :=
  if z % 2=0 then next (z/12)==some (shifted (index z) p)
  else cfg.cut d p (z/2)
def checks (cfg : Setup) (read : Reader) (next : Next) (d : Nat) : List State→Nat→Bool
  | [],_=>true
  | p::ps,n=>
    let bits:=read p.2 n
    tagOk cfg next d p bits.1 && checks cfg read next d ps bits.2
def checked (cfg : Setup) (read : Reader) (next : Next) (d : Nat) (s : List W) (b data : Nat) :=
  decide s.Nodup && !(s.contains (norm cfg.t)) && checks cfg read next d (verifiedChildren cfg.t s b) data

theorem aTag {cfg read next d ps n} (yes : checks cfg read next d ps n=true)
    {p} (mem:p∈ps) : ∃z,tagOk cfg next d p z=true := by
  induction ps generalizing n with
  | nil=>simp at mem
  | cons u us ih=>
    simp only [checks,Bool.and_eq_true] at yes
    rcases List.mem_cons.mp mem with rfl|old
    · exact ⟨_,yes.1⟩
    · exact ih yes.2 old

def Dead (cfg : Setup) (d : Nat) (p : State) : Prop :=
  ∀{n c : Nat},n≤d → c≤p.2 → ¬Run cfg.t p.1 n c

theorem checkedSound {cfg read next s b data d}
    (yes : checked cfg read next d s b data=true)
    (later : ∀j p,next j=some p → Dead cfg d p) : Dead cfg (d+1) (s,b) := by
  intro n c rem cap run
  simp only [checked,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at yes
  change Run cfg.t s n c at run
  change c≤b at cap
  cases run with
  | done=>simpa using yes.1.2
  | @gate s n c a h sa sh ka kh aa hh ne nz fresh tail=>
    let child:=canon (after s a h (made a h sa sh) ka kh)
    let p : State := (child,b-(ka.toNat+kh.toNat))
    have mem : p∈verifiedChildren cfg.t s b := known aa hh ne nz fresh tail cap
    obtain ⟨z,ok⟩:=aTag yes.2 mem
    have budget : c≤p.2 := by change c≤b-(ka.toNat+kh.toNat);omega
    have small : n≤d := by omega
    have rest : Run cfg.t child n c := canonRun tail
    unfold tagOk at ok
    split at ok
    · exact later _ _ (eq_of_beq ok) small budget (closedRun (index z) rest (cfg.fixed _))
    · have nd : child.Nodup := by
        apply (List.perm_insertionSort ..).nodup_iff.mpr
        apply List.nodup_cons.mpr
        refine ⟨fun old=>fresh (dropSubset _ _ _ _ (dropSubset _ _ _ _ old)),?_⟩
        have nds:=yes.1.1
        cases ka <;> cases kh <;> simp [drop,nds,nds.erase a,nds.erase h,(nds.erase a).erase h]
      exact cfg.sound nd ok small budget rest

end LiveAIG.DirectLayers

namespace LiveAIG.Strong
private theorem madeCom (u v:W) (a b:Bool) : made u v a b=made v u b a := by
  unfold made;rw [BitVec.and_comm]

private theorem newPivot {t x g s r} {d:List W} (h:Pivot t s x r)
    (old:∀w∈d,w∈s ∧ w≠x) : Pivot t (g::d) g r := by
  obtain ⟨q,diff,agree⟩ := h
  refine ⟨q,diff,?_⟩
  intro w hmem neq
  rcases List.mem_cons.mp hmem with head|tail
  · exact (neq head).elim
  · exact agree _ (old _ tail).1 (old _ tail).2

private theorem forceOther {t u v:W} {s d:List W} {r:R} {a b:Bool} {k c}
    (pv:Pivot t s u r) (vm:v∈s) (vu:v≠u) (keep:∀w∈d,w∈s ∧ w≠u)
    (rest:Run t (made u v a b::d) k c) : (signed v b)[r.val]=true := by
  obtain ⟨q,tw,base⟩ := pv
  have other := signedCong b (base v vm vu)
  by_contra! no
  have zero:(signed v b)[r.val]=false := by cases h:(signed v b)[r.val] <;> simp_all
  have zero':(signed v b)[q.val]=false := other.symm.trans zero
  apply tw (agreeRun rest ?_)
  intro x hx
  rcases List.mem_cons.mp hx with rfl|old
  · apply signedCong
    simp only [BitVec.getElem_and,zero,zero',Bool.and_false]
  · exact base x (keep _ old).1 (keep _ old).2

private theorem signedDiff {u:W} {p n:R} (s:Bool) (h:u[p.val]≠u[n.val]) :
    (signed u s)[p.val]≠(signed u s)[n.val] := by
  cases s <;> simpa [signed] using h
private theorem resultDiff {u v:W} {p n:R} {a b:Bool}
    (d:u[p.val]≠u[n.val]) (pp:(signed v b)[p.val]=true) (nn:(signed v b)[n.val]=true) :
    (made u v a b)[p.val]≠(made u v a b)[n.val] := by
  have inner : (signed u a &&& signed v b)[p.val]≠(signed u a &&& signed v b)[n.val] := by
    simpa only [BitVec.getElem_and,pp,nn,Bool.and_true] using signedDiff a d
  exact signedDiff _ inner

private def mappedPivot (x u v g:W) := if x=u ∨ x=v then g else x

private theorem clashBoth {t u v:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (ne:u≠v) (right:∀w∈d,w∈s∧w≠v)
    (vp:Pivot t s v p) (vn:Pivot t s v n) (ud:u[p.val]≠u[n.val])
    (rest:Run t (made u v a b::d) k c) : False := by
  have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
  exact signedDiff a ud ((forceOther vp um ne right r').trans (forceOther vn um ne right r').symm)

def witness (t:W) (s:List W) (p n:R) (x:W) : Prop :=
  x∈s ∧ Pivot t s x p ∧ Pivot t s x n ∧ x[p.val]≠x[n.val]

private theorem transfer {t u v x : W} {s d : List W} {p n : R} {a b : Bool} {k c}
    (um:u∈s) (vm:v∈s) (ne:u≠v) (old:∀w∈d,w∈s)
    (other:∀w∈s,w≠u → w≠v → w∈d)
    (consumed:x=u → u∉d) (consumed':x=v → v∉d)
    (h:witness t s p n x) (rr:Run t (made u v a b::d) k c) :
    witness t (made u v a b::d) p n (mappedPivot x u v (made u v a b)) := by
  obtain ⟨xm,xp,xn,xd⟩:=h
  by_cases one:x=u
  · subst x
    have left : ∀w∈d,w∈s∧w≠u := fun w m=>⟨old w m,fun e=> consumed rfl (e ▸ m)⟩
    exact ⟨by simp [mappedPivot],by simpa [mappedPivot] using newPivot (g:=made u v a b) xp left,
      by simpa [mappedPivot] using newPivot (g:=made u v a b) xn left,by
      simpa [mappedPivot] using resultDiff (a:=a) xd (forceOther xp vm ne.symm left rr) (forceOther xn vm ne.symm left rr)⟩
  by_cases two:x=v
  · subst x
    have right : ∀w∈d,w∈s∧w≠v := fun w m=>⟨old w m,fun e=>consumed' rfl (e ▸ m)⟩
    have rr' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
    have de:=resultDiff (a:=b) xd (forceOther xp um ne right rr') (forceOther xn um ne right rr')
    rw [madeCom v u b a] at de
    exact ⟨by simp [mappedPivot],by simpa [mappedPivot] using newPivot (g:=made u v a b) xp right,
      by simpa [mappedPivot] using newPivot (g:=made u v a b) xn right,by simpa [mappedPivot] using de⟩
  have stay {r:R} (pv:Pivot t s x r) : Pivot t (made u v a b::d) x r := by
    obtain ⟨q,diff,z⟩:=pv
    refine ⟨q,diff,?_⟩
    intro w hw neq
    rcases List.mem_cons.mp hw with rfl|mem
    · apply signedCong
      simp only [BitVec.getElem_and,signedCong a (z u um (Ne.symm one)),signedCong b (z v vm (Ne.symm two))]
    · exact z _ (old _ mem) neq
  simpa [witness,mappedPivot,one,two] using
    (show x∈made u v a b::d ∧ Pivot t (made u v a b::d) x p ∧ Pivot t (made u v a b::d) x n ∧ x[p.val]≠x[n.val]
      from ⟨List.mem_cons_of_mem _ (other x xm one two),stay xp,stay xn,xd⟩)

theorem countSigned {t s k c} (run:Run t s k c) (nd:s.Nodup) (p n:R) (P:Finset W)
    (good:∀x∈P,witness t s p n x) : P.card≤c+(decide (t[p.val]≠t[n.val])).toNat := by
  induction run generalizing P with
  | done =>
    have sub : P ⊆ {norm t} := fun x hx=>by simpa using (good x hx).1
    by_cases e : t[p.val]=t[n.val]
    · have empty : P=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have wx:=good x hx
        have xx : x=norm t := by simpa using wx.1
        exact wx.2.2.2 (xx ▸ signedCong _ e)
      simp [empty]
    · simpa [e] using Finset.card_le_card sub
  | @gate s k c u v a b ka kb um vm ne nz fresh rest ih =>
    let d:=drop (drop s u ka) v kb
    let g:=made u v a b
    let K : Finset W := (if ka then {u} else ∅) ∪ (if kb then {v} else ∅)
    let U:=P \ K
    have hd : ∀w,w∈d ↔ w∈s ∧ (w=u → ka=true) ∧ (w=v → kb=true) := by
      intro w
      cases ka <;> cases kb <;> simp [d,drop,(nd.erase u).mem_erase_iff,nd.mem_erase_iff] <;> tauto
    have old : ∀w∈d,w∈s := fun w h1=>(hd w).mp h1 |>.1
    have other : ∀w∈s,w≠u → w≠v → w∈d := fun w hw e f=>(hd w).mpr ⟨hw,fun z=>(e z).elim,fun z=>(f z).elim⟩
    have spent {x} (h:x∈U) : (x=u → u∉d) ∧ (x=v → v∉d) := by
      have out:= (Finset.mem_sdiff.mp h).2
      constructor
      · rintro rfl mem
        have eq:=((hd _).mp mem).2.1 rfl
        exact out (by simp [K,eq])
      · rintro rfl mem
        have eq:=((hd _).mp mem).2.2 rfl
        exact out (by simp [K,eq])
    have preserves {x} (hx:x∈U) := transfer um vm ne old other (spent hx).1 (spent hx).2
      (good x (Finset.mem_sdiff.mp hx).1) rest
    have injective : Set.InjOn (fun x=>mappedPivot x u v g) (↑U : Set W) := by
      intro x hx y hy e
      by_contra xy
      have wx:=good x (Finset.mem_sdiff.mp hx).1
      have wy:=good y (Finset.mem_sdiff.mp hy).1
      by_cases X:x=u ∨ x=v <;> by_cases Y:y=u ∨ y=v
      · rcases X with rfl|rfl <;> rcases Y with e'|e'
        · exact xy e'.symm
        · subst y
          exact clashBoth um ne (fun w m=>⟨old w m,fun q=>(spent hy).2 rfl (q ▸ m)⟩)
            wy.2.1 wy.2.2.1 wx.2.2.2 rest
        · subst y
          exact clashBoth um ne (fun w m=>⟨old w m,fun q=>(spent hx).2 rfl (q ▸ m)⟩)
            wx.2.1 wx.2.2.1 wy.2.2.2 rest
        · exact xy e'.symm
      · simp only [mappedPivot,X,Y,ite_true,ite_false] at e
        apply fresh
        change g ∈ s
        rw [e];exact wy.1
      · simp only [mappedPivot,X,Y,ite_true,ite_false] at e
        apply fresh
        change g ∈ s
        rw [←e];exact wx.1
      · exact xy (by simpa [mappedPivot,X,Y] using e)
    have nd' : (g::d).Nodup := by
      refine List.nodup_cons.mpr ⟨fun h=>fresh (old _ h),?_⟩
      cases ka <;> cases kb <;> simp [d,drop,nd,nd.erase u,nd.erase v,(nd.erase u).erase v]
    have hsize:=ih nd' (U.image (fun x=>mappedPivot x u v g)) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
      exact preserves hx)
    rw [Finset.card_image_of_injOn injective] at hsize
    have sub : P ⊆ U ∪ K := by intro x hx; by_cases h:x∈K <;> simp [U,h,hx]
    have diff := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have card : K.card≤ka.toNat+kb.toNat := by
      cases ka <;> cases kb <;> simp [K,ne,Bool.toNat]
    omega
theorem count {t s k c} (run:Run t s k c) (nd:s.Nodup) (p n:R) (P:Finset W)
    (good:∀x∈P,witness t s p n x) : P.card≤c+1 := by
  have h:=countSigned run nd p n P good
  cases e:(decide (t[p.val]≠t[n.val])) <;> simp [e,Bool.toNat] at h <;> omega
end LiveAIG.Strong

namespace LiveAIG.PivotCertificate

def chosen (s : List W) (mask : Nat) := s.filter (fun w=>mask.testBit (s.idxOf w))
def alone (t : W) (s : List W) (w : W) (r : R) :=
  (sameMask w w r s &&& ~~~literalAt t r) != 0
theorem aloneSound {t s w r} (hit : alone t s w r=true) : Pivot t s w r := by
  have h:=bne_iff_ne.mp hit
  obtain ⟨q,yes⟩:=someRow h
  simp only [BitVec.getElem_and,Bool.and_eq_true] at yes
  exact ⟨q,litNe yes.2,fun a m ne=>keptEqual yes.1 a m ne ne⟩

def tests (t : W) (s : List W) (p n : R) (w : W) :=
  w[p.val] != w[n.val] && alone t s w p && alone t s w n
def verify (t : W) (s : List W) (budget code : Nat) :=
  let p := anchor code
  let n := anchor (code/128)
  let xs := chosen s (code/16384)
  decide (budget+(decide (t[p.val]≠t[n.val])).toNat<xs.length) && xs.all (tests t s p n)

theorem verifySound {t s k c budget code} (ds : s.Nodup) (yes : verify t s budget code=true)
    (small : c≤budget) (run : Run t s k c) : False := by
  simp only [verify,Bool.and_eq_true,decide_eq_true_eq] at yes
  let xs:=chosen s (code/16384)
  have ns : xs.Nodup := ds.filter _
  have limit:=Strong.countSigned run ds (anchor code) (anchor (code/128)) xs.toFinset (by
    intro x mem
    have original : x∈xs := List.mem_toFinset.mp mem
    have inS:=List.mem_of_mem_filter original
    have check:=List.all_eq_true.mp yes.2 x original
    simp only [tests,Bool.and_eq_true,bne_iff_ne] at check
    exact ⟨inS,aloneSound check.1.2,aloneSound check.2,check.1.1⟩)
  rw [List.toFinset_card_of_nodup ns] at limit
  have gt : budget+(decide (t[(anchor code).val]≠t[(anchor (code/128)).val])).toNat<xs.length := yes.1
  omega

end LiveAIG.PivotCertificate

namespace FiveOne12076
open FreeAIG LiveAIG
def f (x : Fin 5 → Bool) : Bool := Nat.testBit 4269860864 (∑ i : Fin 5, if x i then 2^i.val else 0)
def cut (x : X) (i : Fin 5) : Bool := x ⟨i.val, by omega⟩
def padded : X → Bool := f ∘ cut
def t : W := 0xfe80e800fe80e800fe80e800fe80e800
theorem fixed : ∀i : Fin 6,InputSym.move i t=t := by decide +kernel
def A : List W := FiveOne12076Data.raw
def S : Set (Fn X) := {g | ∃ i : Fin 5,g=fun x=>cut x i}
set_option maxRecDepth 65536 in
theorem wordF : word padded=t := by decide +kernel
theorem compile {k : Nat} (h : Has Inputs k f) :
    ∃ n≤k,∃c,Run t A n c := by
  classical
  have p : Has S k padded := h.map cut (by
    rintro g ⟨i,rfl⟩;exact .src ⟨i,rfl⟩)
  have rep : Represents S A.toFinset := by
    rintro g ⟨i,rfl⟩;right;revert i;decide +kernel
  have nz : norm (word padded)≠0 := by rw [wordF];decide +kernel
  obtain ⟨U,sub,_,n,small,c,ok⟩:=trim p A.toFinset rep nz
  let s:=A.filter (fun w=>decide (w∈U))
  have eq : s.toFinset=U := by
    ext w
    change w∈(A.filter (fun w=>decide (w∈U))).toFinset ↔ w∈U
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun hw=>⟨List.mem_toFinset.mp (sub hw),hw⟩⟩
  have nd : A.Nodup := by decide +kernel
  have r:=ok s (nd.filter _) eq
  rw [wordF] at r
  have valid := initialOk r
  have all : A.sublists.all (fun xs=> !liveInitial t xs || xs==A)=true := by decide +kernel
  have one:=List.all_eq_true.mp all s (List.mem_sublists.mpr List.filter_sublist)
  have se : s=A := by simpa [valid] using one
  exact ⟨n,small,c,se ▸ r⟩

def cfg : DirectLayers.Setup where
  t := t
  fixed := fixed
  cut := fun _ p z=>PivotCertificate.verify t p.1 p.2 z
  sound := fun ds ok _ small run=>PivotCertificate.verifySound ds ok small run

end FiveOne12076

namespace LiveAIG.DirectLayers
abbrev Levels := Nat → Next
abbrev Hints := Nat → Nat → Nat

def site (cfg : Setup) (read : Reader) (levels : Levels) (hints : Hints) (d k i : Nat) : Bool :=
  match levels k i with
  | none=>true
  | some p=>checked cfg read (levels (k+1)) d p.1 p.2 (hints k i)
def block (cfg : Setup) (read : Reader) (levels : Levels) (hints : Hints) (d width k b : Nat) :=
  (List.range width).all fun i=>site cfg read levels hints d k (width*b+i)

theorem groupSound {cfg read levels hints width k d size}
    (pos : 0<width)
    (bounded : ∀{i p},levels k i=some p → i<size)
    (next : ∀ j p,levels (k+1) j=some p → Dead cfg d p)
    (groups : ∀b, b<(size+width-1)/width → block cfg read levels hints d width k b=true) :
    ∀ i p, levels k i=some p → Dead cfg (d+1) p := by
  intro i p eq
  have lt := bounded eq
  have bb : i/width < (size+width-1)/width := by
    have inc : i/width*width+width ≤ size+width-1 := by
      have := Nat.div_mul_le_self i width
      omega
    have one : (i/width+1)*width ≤ size+width-1 := by simpa [Nat.add_mul] using inc
    exact (Nat.le_div_iff_mul_le pos).mpr one
  have yes:=List.all_eq_true.mp (groups _ bb) (i % width) (List.mem_range.mpr (Nat.mod_lt _ pos))
  have ii : width*(i/width)+i % width=i := Nat.div_add_mod i width
  simp only [ii,site,eq] at yes
  intro n c hn hc
  exact checkedSound yes next hn hc

end LiveAIG.DirectLayers

namespace FiveOne12076
open LiveAIG DirectLayers FiveOne12076Data
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem bounded {lev i : Nat} {s : State} (h : stateAt lev i=some s) : i<levelSize lev := by
  unfold stateAt at h
  split at h
  · assumption
  · contradiction
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem level4 : ∀ i p,stateAt 4 i=some p → Dead cfg 4 p := by
  intro i p he
  have lt:=bounded he
  change i<0 at lt
  omega
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem block3 : block cfg decodeStep stateAt hintAt 4 48 3 0=true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem level3 : ∀ i p,stateAt 3 i=some p → Dead cfg 5 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=48) (size:=levelSize 3) (by decide) (@bounded 3) level4
  intro b hb
  have b0 : b=0 := by change b<1 at hb; omega
  subst b
  exact block3
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem block2 : block cfg decodeStep stateAt hintAt 5 48 2 0=true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem level2 : ∀ i p,stateAt 2 i=some p → Dead cfg 6 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=48) (size:=levelSize 2) (by decide) (@bounded 2) level3
  intro b hb
  have b0 : b=0 := by change b<1 at hb; omega
  subst b
  exact block2
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem block1 : block cfg decodeStep stateAt hintAt 6 48 1 0=true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem level1 : ∀ i p,stateAt 1 i=some p → Dead cfg 7 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=48) (size:=levelSize 1) (by decide) (@bounded 1) level2
  intro b hb
  have b0 : b=0 := by change b<1 at hb; omega
  subst b
  exact block1
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem block0 : block cfg decodeStep stateAt hintAt 7 48 0 0=true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem level0 : ∀ i p,stateAt 0 i=some p → Dead cfg 8 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=48) (size:=levelSize 0) (by decide) (@bounded 0) level1
  intro b hb
  have b0 : b=0 := by change b<1 at hb; omega
  subst b
  exact block0
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lower {k : Nat} (h : FreeAIG.Has FreeAIG.Inputs k f) : 9≤k := by
  by_contra! small
  obtain ⟨n,hn,c,run⟩:=compile h
  have bal:=balance run
  have sizeA : A.length=5 := by decide +kernel
  rw [sizeA] at bal
  have start : stateAt 0 0=some (A,4) := by decide +kernel
  exact level0 0 (A,4) start (by omega) (by show c≤4;omega) run
end FiveOne12076

namespace Upper12076

theorem signedEleven {k : Nat} (net : FreeAIG.Has FreeAIG.Inputs k target) : 11≤k :=
  fromTwo @Zero12077.lower @FiveOne12076.lower net

theorem replacement (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ s ∧
      ∀x : Fin 6→Bool,D.eval (List.ofFn x)=target x :=
  completeFromSigned @signedEleven s h

end Upper12076

end PEqualNP.Outside.L_meta_12076

theorem PEqualNP.Outside.L_meta_12076 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12076.Upper12076.replacement
