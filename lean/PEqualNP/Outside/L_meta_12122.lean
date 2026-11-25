import Mathlib
import PEqualNP.Defs

-- Signed gate lower bounds for complete graphs use the certificates from L-meta-10490.
-- The contributing proof credits L-meta-1674, L-meta-670 and L-meta-1667 (Apache-2.0).

namespace PEqualNP.Outside.L_meta_12122

namespace Upper12122
open PEqualNP.CircuitLowerBounds

def index (x : Fin 6 → Bool) : ℕ := ∑ i : Fin 6, if x i then 2^(i : ℕ) else 0
def target (x : Fin 6 → Bool) := Nat.testBit (4276676736 * 2^32 + 4261445632) (index x)
def gates : List Gate := [⟨.or, [0, 1]⟩, ⟨.and, [6, 2]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [9, 5]⟩, ⟨.and, [10, 3]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [11, 17]⟩]
def circuit : Circuit := ⟨gates, 18⟩

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem size : circuit.size = 13 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem correct : ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) = target x := by
  decide +kernel

def majFive (x : Fin 5 → Bool) : Bool :=
  decide (3 ≤ (List.ofFn x).count true)

set_option maxRecDepth 32768 in
theorem lastTrue : ∀ x : Fin 5 → Bool, target (Fin.lastCases true x) = majFive x := by
  decide +kernel

end Upper12122

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

namespace Upper12122
open FreeAIG PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem completeFromSigned
    (lower : ∀ {k : Nat}, Has Inputs k target → 12 ≤ k)
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
end Upper12122

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

namespace LiveAIG.FlatProjection
open FreeAIG
variable {B : Type*}

def read (σ : B → R) (w : W) : Fn B := fun x => w[(σ x).val]
def constant (f : Fn B) : Prop := ∃ b : Bool, f = (fun _ => b)
noncomputable def flat (σ : B → R) (w : W) : Bool := by
  classical
  exact decide (constant (read σ w))

theorem flat_spec (σ : B → R) (w : W) : flat σ w = true ↔ constant (read σ w) := by
  classical
  simp [flat]

theorem readSign (σ : B → R) (w : W) (b : Bool) :
    read σ (signed w b) = if b then neg (read σ w) else read σ w := by
  cases b <;> funext x <;> simp [signed,read,neg]

theorem readAnd (σ : B → R) (u v : W) : read σ (u &&& v) = meet (read σ u) (read σ v) := by
  funext x
  simp [read,meet]

theorem signAvail {σ : B → R} {w : W} {S : Set (Fn B)}
    (h : Avail S (read σ w)) (b : Bool) : Avail S (read σ (signed w b)) := by
  rw [readSign];cases b
  · exact h
  · exact .neg h

theorem flatSign {σ : B → R} {w : W} (b : Bool) (h : flat σ w=true) :
    flat σ (signed w b)=true := by
  obtain ⟨k,hk⟩ := (flat_spec _ _).mp h
  apply (flat_spec _ _).mpr
  rw [readSign,hk]
  cases b
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

theorem countDrop (p : W → Bool) {s : List W} {w : W} (hw : w∈s) (keep : Bool) :
    s.countP p = (drop s w keep).countP p + (p w && !keep).toNat := by
  cases keep
  · have h := (List.perm_cons_erase hw).countP_eq p
    simpa [drop,List.countP_cons, Bool.toNat, Nat.add_comm] using h
  · simp [drop]

theorem contract {σ : B → R} {a b : W} (sa sb : Bool) {S : Set (Fn B)}
    (ha : Avail S (read σ a)) (hb : Avail S (read σ b))
    (cheap : flat σ a=true ∨ flat σ b=true) :
    Avail S (read σ (made a b sa sb)) := by
  apply signAvail
  rw [readAnd]
  rcases cheap with left|right
  · obtain ⟨k,hk⟩ := (flat_spec _ _).mp (flatSign sa left)
    rw [hk];cases k
    · rw [meetFalseL];exact .const false
    · rw [meetTrueL];exact signAvail hb _
  · obtain ⟨k,hk⟩ := (flat_spec _ _).mp (flatSign sb right)
    rw [hk];cases k
    · rw [meetFalseR];exact .const false
    · rw [meetTrueR];exact signAvail ha _

theorem bothFlat {σ : B → R} {a b : W} (sa sb : Bool) (ha : flat σ a=true)
    (hb : flat σ b=true) : flat σ (made a b sa sb)=true := by
  apply flatSign
  obtain ⟨i,hi⟩ := (flat_spec _ _).mp (flatSign sa ha)
  obtain ⟨j,hj⟩ := (flat_spec _ _).mp (flatSign sb hb)
  apply (flat_spec _ _).mpr
  rw [readAnd,hi,hj]
  exact ⟨_,rfl⟩

theorem saves (σ : B → R) {S : Set (Fn B)} {t : W} {s : List W} {n c : Nat}
    (run : Run t s n c) (proper : ¬constant (read σ t))
    (src : ∀ w∈s, Avail S (read σ w)) :
    ∃ k, k+s.countP (flat σ)≤n ∧ Has S k (read σ t) := by
  induction run generalizing S with
  | done =>
    have z : flat σ (norm t)=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have again := flatSign t[0] h
      rw [orient] at again
      exact proper ((flat_spec _ _).mp again)
    refine ⟨0,by simp [List.countP_cons,z],.done ?_⟩
    have v := signAvail (src (norm t) List.mem_cons_self) t[0]
    rwa [orient] at v
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh tail ih =>
    let g := made a b sa sb
    let rest := drop (drop s a ka) b kb
    have old : ∀ w∈rest, w∈s := fun _ h=>dropSubset _ _ _ _ (dropSubset _ _ _ _ h)
    have ac := countDrop (flat σ) ha ka
    have bc := countDrop (flat σ) (rightStays hb ne ka) kb
    change (drop s a ka).countP (flat σ) = rest.countP (flat σ) + _ at bc
    have tally : (after s a b g ka kb).countP (flat σ) = rest.countP (flat σ) + (flat σ g).toNat := by
      simp [after,rest,List.countP_cons,Bool.toNat]
    by_cases cheap : flat σ a=true ∨ flat σ b=true
    · obtain ⟨k,sz,r⟩ := ih (S:=S) (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl|hv
        · exact contract sa sb (src a ha) (src b hb) cheap
        · exact src w (old w hv))
      change k+(after s a b g ka kb).countP (flat σ)≤n at sz
      rw [tally] at sz
      refine ⟨k,?_,r⟩
      have both : flat σ a=true → flat σ b=true → flat σ g=true := bothFlat sa sb
      cases aa : flat σ a <;> cases bb : flat σ b <;> cases ka <;> cases kb <;>
        simp_all only [Bool.and_true,Bool.and_false,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and,Bool.toNat_true,Bool.toNat_false] <;> omega
    · let u := signed a sa
      let v := signed b sb
      let H := meet (read σ u) (read σ v)
      obtain ⟨k,sz,r⟩ := ih (S:=insert H S) (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl|hv
        · apply signAvail
          rw [readAnd]
          exact .src (Set.mem_insert _ _)
        · exact (src w (old w hv)).extend)
      change k+(after s a b g ka kb).countP (flat σ)≤n at sz
      rw [tally] at sz
      have af : flat σ a = false := Bool.eq_false_iff.mpr (fun h=>cheap (.inl h))
      have bf : flat σ b = false := Bool.eq_false_iff.mpr (fun h=>cheap (.inr h))
      refine ⟨k+1,?_,.step (signAvail (src _ ha) sa) (signAvail (src _ hb) sb) r⟩
      simp [af,bf] at ac bc
      omega
end LiveAIG.FlatProjection

namespace LiveAIG.CofactorLoan
open FreeAIG
abbrev U := BitVec 32
abbrev B := Fin 32
abbrev Instr := U × U
abbrev Prog := List Instr

def obs (w : U) : Fn B := fun r => w[r.val]
def normU (w : U) := if w[0] then ~~~w else w
def raw : List U := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def basis (bank : List U) : Set (Fn B) := {f | ∃ w ∈ bank, f = obs w}
def flatU (w : U) := w == 0 || w == (~~~0 : U)
def offers (bank : List U) (w : U) := flatU w || bank.contains (normU w)

theorem obsZero : obs 0 = fun _ => false := by funext r;simp [obs]
theorem obsOnes : obs (~~~0 : U) = fun _ => true := by
  funext r
  exact (show ∀ x : B, obs (~~~0 : U) x = true from by decide +kernel) r

theorem obsNeg (w : U) : obs (~~~w) = FreeAIG.neg (obs w) := by
  funext r
  simp [obs,FreeAIG.neg]
theorem obsAnd (a b : U) : obs (a &&& b) = meet (obs a) (obs b) := by
  funext r
  simp [obs,meet]

theorem offerSound {bank : List U} {w : U} (h : offers bank w = true) :
    Avail (basis bank) (obs w) := by
  simp only [offers,flatU,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at h
  rcases h with (rfl|rfl)|m
  · rw [obsZero];exact .const false
  · rw [obsOnes];exact .const true
  · by_cases bit : w[0] = true
    · simp [normU,bit] at m
      have hm : Avail (basis bank) (obs (~~~w)) := .src ⟨_,m,rfl⟩
      have dbl : FreeAIG.neg (obs (~~~w)) = obs w := by
        rw [obsNeg];funext r;simp [FreeAIG.neg]
      exact dbl ▸ hm.neg
    · simp [normU,bit] at m
      exact .src ⟨_,m,rfl⟩

def derive (bank : List U) : Prog → Option (List U)
  | [] => some bank
  | (a,b)::ps => if offers bank a && offers bank b then
      derive (normU (a &&& b)::bank) ps else none

private theorem replay {bank out : List U} {ps : Prog} {k : Nat} {f : Fn B}
    (ok : derive bank ps = some out) (tail : Has (basis out) k f) :
    Has (basis bank) (k+ps.length) f := by
  induction ps generalizing bank with
  | nil => simp [derive] at ok;subst out;simpa using tail
  | cons ab ps ih =>
    rcases ab with ⟨a,b⟩
    simp only [derive] at ok
    split at ok
    next accept =>
      obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp accept
      have later := ih ok
      have mapped := later.map (T:=insert (meet (obs a) (obs b)) (basis bank)) id (by
        rintro _ ⟨w,hw,rfl⟩
        rcases List.mem_cons.mp hw with rfl|m
        · have g : Avail (insert (meet (obs a) (obs b)) (basis bank)) (obs (a &&& b)) := by
            rw [obsAnd];exact .src (Set.mem_insert _ _)
          by_cases bit : (a &&& b)[0] = true
          · simpa [normU,bit,obsNeg,Function.comp_def] using g.neg
          · simpa [normU,bit,Function.comp_def] using g
        · exact .src (Set.mem_insert_of_mem _ ⟨_,m,rfl⟩))
      exact Has.step (offerSound ha) (offerSound hb) mapped
    next => contradiction

structure Lens (t : W) where
  row : B → R
  image : W → U
  eqn : ∀ w, obs (image w) = FlatProjection.read row w
  proper : ¬FlatProjection.constant (FlatProjection.read row t)
  lower : ∀ {k}, Has (basis raw) k (FlatProjection.read row t) → 10 ≤ k

def reject {t : W} (lens : Lens t) (s : List W) (budget : Nat) (ps : Prog) : Bool :=
  match derive raw ps with
  | none => false
  | some out => s.all (fun w => offers out (lens.image w)) &&
    decide (s.length+budget+ps.length < 11+s.countP (fun w => flatU (lens.image w)))

theorem flatCount {t : W} (lens : Lens t) (s : List W) :
    s.countP (fun w => flatU (lens.image w)) ≤ s.countP (FlatProjection.flat lens.row) := by
  apply List.countP_mono_left
  intro w _ h
  apply (FlatProjection.flat_spec _ _).2
  rw [←lens.eqn]
  simp only [flatU,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with h|h <;> rw [h]
  · exact ⟨false,obsZero⟩
  · exact ⟨true,obsOnes⟩

theorem noRun {t : W} {lens : Lens t} {s : List W} {budget n c : Nat} {ps : Prog}
    (check : reject lens s budget ps = true) (cap : c ≤ budget) : ¬ Run t s n c := by
  intro h
  unfold reject at check
  split at check
  next => contradiction
  next out ok =>
    obtain ⟨all,short⟩ := Bool.and_eq_true_iff.mp check
    obtain ⟨k,hk,tail⟩ := FlatProjection.saves lens.row h lens.proper (S:=basis out) (by
      intro w m
      rw [←lens.eqn]
      exact offerSound (List.all_eq_true.mp all w m))
    have lb := lens.lower (replay ok tail)
    have bal := balance h
    have count := flatCount lens s
    have sz := of_decide_eq_true short
    omega

end LiveAIG.CofactorLoan

namespace LiveAIG.CofactorLoan
open FreeAIG FlatProjection

set_option maxHeartbeats 1000000 in
def sources {t} (l : Lens t) (s : List W) : Set (Fn B) :=
  basis raw ∪ {f | ∃ w ∈ s, f = read l.row w}
set_option maxHeartbeats 1000000 in
def flats {t} (l : Lens t) (s : List W) : Nat := s.countP (fun w => flatU (l.image w))
set_option maxHeartbeats 1000000 in
def bank {t} (l : Lens t) (s : List W) := raw ++ s.map (normU ∘ l.image)
set_option maxHeartbeats 1000000 in
def free {t} (l : Lens t) (s : List W) (g : W) := offers (bank l s) (l.image g)
set_option maxHeartbeats 1000000 in
def loss {t} (l : Lens t) (s child : List W) (g : W) : Bool :=
  decide (flats l s < (free l s g).toNat + flats l child)

set_option maxHeartbeats 1000000 in
def Tight {t} (l : Lens t) (s : List W) (remaining : Nat) : Prop :=
  ∀ {k}, Has (sources l s) k (read l.row t) → remaining ≤ k + flats l s

set_option maxHeartbeats 1000000 in
theorem own {t s w} (l : Lens t) (h : w∈s) : Avail (sources l s) (read l.row w) :=
  .src (Or.inr ⟨w,h,rfl⟩)

set_option maxHeartbeats 1000000 in
theorem normAvail {S : Set (Fn B)} {w : U} (h : Avail S (obs w)) : Avail S (obs (normU w)) := by
  cases e:w[0] <;> simp [normU,e,obsNeg]
  · exact h
  · exact h.neg

set_option maxHeartbeats 1000000 in
theorem free_sound {t s g} (l : Lens t) (h : free l s g = true) :
    Avail (sources l s) (read l.row g) := by
  rw [←l.eqn]
  apply (offerSound h).lift
  rintro _ ⟨w,hw,rfl⟩
  rcases List.mem_append.mp hw with m|m
  · exact .src (.inl ⟨w,m,rfl⟩)
  · obtain ⟨v,vm,rfl⟩ := List.mem_map.mp m
    apply normAvail
    rw [l.eqn]
    exact own l vm

set_option maxHeartbeats 1000000 in
private theorem sourceMap {t s child g} {l : Lens t} {Z : Set (Fn B)}
    (subset : ∀w∈child, w = g ∨ w∈s)
    (base : ∀ f∈sources l s, Avail Z f) (extra : Avail Z (read l.row g)) :
    ∀ f∈sources l child, Avail Z f := by
  intro f h
  rcases h with h | ⟨v,m,rfl⟩
  · exact base _ (.inl h)
  · rcases subset v m with rfl|old
    · exact extra
    · exact base _ (.inr ⟨_,old,rfl⟩)

set_option maxHeartbeats 1000000 in
theorem gateCost {t s child a b sa sb} (l : Lens t) (ha : a∈s) (hb : b∈s)
    (subset : ∀ w∈child, w = made a b sa sb ∨ w∈s) {k} {f : Fn B}
    (next : Has (sources l child) k f) :
    Has (sources l s) (k+(!free l s (made a b sa sb)).toNat) f := by
  let g := made a b sa sb
  by_cases cheap : free l s g = true
  · have map := sourceMap subset (fun x m => Avail.src m) (free_sound l cheap)
    simpa [g,cheap] using next.map (T:=sources l s) id map
  · have expensive : free l s g = false := Bool.eq_false_iff.mpr cheap
    have av1 := signAvail (own l ha) sa
    have av2 := signAvail (own l hb) sb
    let u := meet (read l.row (signed a sa)) (read l.row (signed b sb))
    have ex : Avail (insert u (sources l s)) (read l.row g) := by
      apply signAvail
      rw [readAnd]
      exact .src (Set.mem_insert _ _)
    have map := sourceMap subset (fun x m => Avail.src (Set.mem_insert_of_mem _ m)) ex
    have nn := next.map (T:=insert u (sources l s)) id map
    simpa [g,expensive] using Has.step av1 av2 nn

set_option maxHeartbeats 1000000 in
theorem preserve {t s child g d} {l : Lens t} (tight : Tight l s (d+1))
    (gate : ∀ {k}, Has (sources l child) k (read l.row t) →
      Has (sources l s) (k+(!free l s g).toNat) (read l.row t))
    (lower : flats l s ≤ (free l s g).toNat + flats l child) : Tight l child d := by
  intro k circuit
  have z := tight (gate circuit)
  cases eq:free l s g <;> simp [eq] at z lower <;> omega

set_option maxHeartbeats 1000000 in
theorem lost {t s child g d} {l : Lens t} (tight : Tight l s (d+1))
    (gate : ∀ {k}, Has (sources l child) k (read l.row t) →
      Has (sources l s) (k+(!free l s g).toNat) (read l.row t))
    (strict : loss l s child g = true) {n c} (rem : n ≤ d) : ¬Run t child n c := by
  intro run
  obtain ⟨k,save,prog⟩ := saves l.row run l.proper (fun w m => own l m)
  have count : flats l child ≤ child.countP (flat l.row) := flatCount l child
  have z := tight (gate prog)
  have cmp := of_decide_eq_true strict
  change flats l s < (free l s g).toNat + flats l child at cmp
  cases eq:free l s g <;> simp [eq] at z cmp <;> omega

set_option maxHeartbeats 1000000 in
theorem initial {t s} (l : Lens t) (hf : 1 ≤ flats l s)
    (hr : ∀ w∈s, offers raw (l.image w) = true) : Tight l s 11 := by
  intro k h
  have mapped := h.map (T:=basis raw) id (by
    intro f m
    rcases m with rawMem | ⟨w,mem,rfl⟩
    · exact .src rawMem
    · change Avail (basis raw) (read l.row w)
      rw [←l.eqn]
      exact offerSound (hr w mem))
  have := l.lower mapped
  omega

set_option maxHeartbeats 1000000 in
theorem permTight {t s s' d} {l : Lens t} (p : s'.Perm s) (h : Tight l s d) :
    Tight l s' d := by
  intro k net
  have f : flats l s' = flats l s := p.countP_eq _
  rw [f]
  apply h
  have equiv : sources l s' = sources l s := by
    ext u
    simp only [sources,Set.mem_union,Set.mem_ofPred_eq,p.mem_iff]
  rwa [←equiv]

end LiveAIG.CofactorLoan

namespace LiveAIG.CofactorLoan
open FreeAIG FlatProjection

set_option maxHeartbeats 1000000 in
theorem obsInject : Function.Injective obs := by
  intro x y h
  apply BitVec.eq_of_getElem_eq
  intro i hi
  exact congrFun h ⟨i,hi⟩

set_option maxHeartbeats 1000000 in
theorem normUNeg (w : U) : normU (~~~w) = normU w := by
  cases bit:w[0] <;> simp [normU,bit]

set_option maxHeartbeats 1000000 in
theorem normUIdem (w : U) : normU (normU w) = normU w := by
  unfold normU
  split <;> simp_all

set_option maxHeartbeats 1000000 in
theorem flatUNeg (w : U) : flatU (~~~w) = flatU w := by
  apply Bool.eq_iff_iff.mpr
  simp only [flatU,Bool.or_eq_true,beq_iff_eq,BitVec.not_eq_comm,BitVec.not_not]
  exact or_comm

set_option maxHeartbeats 1000000 in
theorem flatEquiv {t} (l : Lens t) (w : W) : flatU (l.image w) = flat l.row w := by
  apply Bool.eq_iff_iff.mpr
  rw [flat_spec,←l.eqn]
  simp only [flatU,Bool.or_eq_true,beq_iff_eq]
  constructor
  · rintro (e|e) <;> rw [e]
    · exact ⟨false,obsZero⟩
    · exact ⟨true,obsOnes⟩
  · rintro ⟨b,h⟩
    cases b
    · exact Or.inl (obsInject (h.trans obsZero.symm))
    · exact Or.inr (obsInject (h.trans obsOnes.symm))

set_option maxHeartbeats 1000000 in
theorem offerComplete {bank : List U} (normalized : ∀w∈bank, normU w = w)
    {f} (can : Avail (basis bank) f) : ∀z, obs z = f → offers bank z = true := by
  induction can with
  | src m =>
    obtain ⟨w,m,rfl⟩ := m
    intro z eq
    obtain rfl := obsInject eq
    simp [offers,normalized _ m,m]
  | const b =>
    intro z eq
    cases b
    · have e : z = 0 := obsInject (eq.trans obsZero.symm)
      simp [offers,flatU,e]
    · have e : z = ~~~0 := obsInject (eq.trans obsOnes.symm)
      simp [offers,flatU,e]
  | @neg f h ih =>
    intro z eq
    have same : obs (~~~z) = f := by
      rw [obsNeg,eq];funext r;simp [FreeAIG.neg]
    simpa [offers,normUNeg,flatUNeg] using ih (~~~z) same

set_option maxHeartbeats 1000000 in
private theorem bankNorm {t s} (l : Lens t) : ∀w∈bank l s, normU w=w := by
  intro w hw
  rcases List.mem_append.mp hw with r|r
  · have all : raw.all (fun v=>normU v == v) = true := by decide +kernel
    exact beq_iff_eq.mp (List.all_eq_true.mp all w r)
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp r
    exact normUIdem _

set_option maxHeartbeats 1000000 in
private theorem bankOwn {t s a} (l : Lens t) (m : a∈s) : Avail (basis (bank l s)) (read l.row a) := by
  rw [←l.eqn]
  apply offerSound
  have mem : normU (l.image a) ∈ bank l s :=
    List.mem_append_right _ (List.mem_map.mpr ⟨_,m,rfl⟩)
  simp [offers,mem]

set_option maxHeartbeats 1000000 in
theorem freeWhenFlat {t s a b sa sb} (l : Lens t) (ha : a∈s) (hb : b∈s)
    (one : flatU (l.image a) = true ∨ flatU (l.image b) = true) :
    free l s (made a b sa sb) = true := by
  simp only [flatEquiv] at one
  have can := contract sa sb (bankOwn l ha) (bankOwn l hb) one
  exact offerComplete (bankNorm l) can _ (l.eqn _)

set_option maxHeartbeats 1000000 in
theorem potential {t s a b} (l : Lens t) (ha : a∈s) (hb : b∈s) (ne : a≠b)
    (sa sb ka kb : Bool) :
    flats l s ≤ (free l s (made a b sa sb)).toNat + flats l (after s a b (made a b sa sb) ka kb) := by
  let p := fun w => flatU (l.image w)
  let g := made a b sa sb
  let rest := drop (drop s a ka) b kb
  have ac := countDrop p ha ka
  have bc := countDrop p (rightStays hb ne ka) kb
  change (drop s a ka).countP p = rest.countP p + _ at bc
  change s.countP p ≤ (free l s g).toNat + (g::rest).countP p
  rw [List.countP_cons]
  have cheap : p a=true ∨ p b=true → free l s g=true := freeWhenFlat l ha hb
  have both : p a=true → p b=true → p g=true := by
    simp only [p,flatEquiv,g];exact bothFlat sa sb
  cases aa : p a <;> cases bb : p b <;> cases ka <;> cases kb <;>
    simp_all [Bool.toNat] <;> omega

end LiveAIG.CofactorLoan

namespace LiveAIG.CofactorLoan
open FreeAIG FlatProjection

theorem afterSubset (s : List W) (a b g : W) (ka kb : Bool) :
    ∀ w∈after s a b g ka kb, w = g ∨ w∈s := by
  intro w mem
  rcases List.mem_cons.mp mem with e|m
  · exact Or.inl e
  · exact Or.inr (dropSubset _ _ _ _ (dropSubset _ _ _ _ m))

theorem gateTight {t s a b d} {l : Lens t} (tight : Tight l s (d+1))
    (ha : a∈s) (hb : b∈s) (ne : a≠b) (sa sb ka kb : Bool) :
    Tight l (after s a b (made a b sa sb) ka kb) d :=
  preserve tight (gateCost l ha hb (afterSubset _ _ _ _ _ _)) (potential l ha hb ne sa sb ka kb)

theorem gateLost {t s a b d} {l : Lens t} (tight : Tight l s (d+1))
    (ha : a∈s) (hb : b∈s) (sa sb ka kb : Bool)
    (bad : loss l s (after s a b (made a b sa sb) ka kb) (made a b sa sb) = true)
    {n c} (hn : n≤d) : ¬Run t (after s a b (made a b sa sb) ka kb) n c :=
  lost tight (gateCost l ha hb (afterSubset _ _ _ _ _ _)) bad hn

theorem canonGateTight {t s a b d} {l : Lens t} (tight : Tight l s (d+1))
    (ha : a∈s) (hb : b∈s) (ne : a≠b) (sa sb ka kb : Bool) :
    Tight l (canon (after s a b (made a b sa sb) ka kb)) d :=
  permTight (List.perm_insertionSort ..) (gateTight tight ha hb ne sa sb ka kb)

theorem canonGateLost {t s a b d} {l : Lens t} (tight : Tight l s (d+1))
    (ha : a∈s) (hb : b∈s) (sa sb ka kb : Bool)
    (bad : loss l s (canon (after s a b (made a b sa sb) ka kb)) (made a b sa sb) = true)
    {n c} (hn : n≤d) : ¬Run t (canon (after s a b (made a b sa sb) ka kb)) n c := by
  apply lost tight (gateCost l ha hb ?_) bad hn
  intro w m
  apply afterSubset s a b (made a b sa sb) ka kb
  exact (List.perm_insertionSort ..).mem_iff.mp m

end LiveAIG.CofactorLoan

namespace LiveAIG.SixLayers
open CofactorLoan InputSym SparseConflicts

abbrev State := List W × Nat
structure Setup where
  t : W
  f : Lens t
  e : Lens t
  fixed : ∀i, move i t=t
  symF : ∀ (i : Fin 6) {s d}, Tight f s d → Tight f (canon (s.map (move i))) d
  symE : ∀ (i : Fin 6) {s d}, Tight e s d → Tight e (canon (s.map (move i))) d
  cut : State → Nat → Bool
  sound : ∀ {p h n c}, p.1.Nodup → cut p h=true → c≤p.2 → ¬Run t p.1 n c
abbrev Reader := Nat→Nat→Nat×Nat
abbrev Next := Nat→Option State
def index (z : Nat) : Fin 6 := ⟨(z-2) % 6,by omega⟩
def shifted (i : Fin 6) (p : State) : State := (canon (p.1.map (move i)),p.2)
def tagOk (cfg : Setup) (next : Next) (s : List W) (p : State) (z : Nat) :=
  if z=0 then loss cfg.f s p.1 (born s p.1)
  else if z=1 then loss cfg.e s p.1 (born s p.1)
  else if 32768≤z then cfg.cut p (z-32768)
  else next ((z-2)/6)==some (shifted (index z) p)

def checks (cfg : Setup) (read : Reader) (next : Next) (s : List W) : List State→Nat→Bool
  | [],_=>true
  | p::ps,n=>
    let bits:=read p.2 n
    tagOk cfg next s p bits.1 && checks cfg read next s ps bits.2
def checked (cfg : Setup) (read : Reader) (next : Next) (s : List W) (b data : Nat) :=
  decide s.Nodup && !(s.contains (norm cfg.t)) && checks cfg read next s (verifiedChildren cfg.t s b) data

theorem aTag {cfg read next s ps n} (yes : checks cfg read next s ps n=true)
    {p} (mem:p∈ps) : ∃z,tagOk cfg next s p z=true := by
  induction ps generalizing n with
  | nil=>simp at mem
  | cons u us ih=>
    simp only [checks,Bool.and_eq_true] at yes
    rcases List.mem_cons.mp mem with rfl|old
    · exact ⟨_,yes.1⟩
    · exact ih yes.2 old

def Dead (cfg : Setup) (d : Nat) (p : State) : Prop :=
  Tight cfg.f p.1 d → Tight cfg.e p.1 d →
  ∀ {n c : Nat}, n≤d → c≤p.2 → ¬Run cfg.t p.1 n c

theorem checkedSound {cfg read next s b data d}
    (yes : checked cfg read next s b data=true)
    (later : ∀j p,next j=some p → Dead cfg d p) :
    Dead cfg (d+1) (s,b) := by
  intro hF hE n c rem cap run
  simp only [checked,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at yes
  change Run cfg.t s n c at run
  change c≤b at cap
  cases run with
  | done=>simpa using yes.1.2
  | @gate s n c a h sa sh ka kh aa hh ne nz fresh tail=>
    let g:=made a h sa sh
    let child:=canon (after s a h g ka kh)
    let p:State := (child,b-(ka.toNat+kh.toNat))
    have mem : p∈verifiedChildren cfg.t s b := known aa hh ne nz fresh tail cap
    obtain ⟨z,ok⟩:=aTag yes.2 mem
    have one : g∈child := (List.perm_insertionSort ..).mem_iff.mpr List.mem_cons_self
    have gate : born s child=g := freshBorn fresh one canonSubset
    have rest : Run cfg.t child n c := canonRun tail
    have small : n≤d := by omega
    have budget : c≤p.2 := by change c≤b-(ka.toNat+kh.toNat);omega
    unfold tagOk at ok
    split at ok
    · change loss cfg.f s child (born s child)=true at ok
      rw [gate] at ok
      exact canonGateLost hF aa hh sa sh ka kh ok small rest
    split at ok
    · change loss cfg.e s child (born s child)=true at ok
      rw [gate] at ok
      exact canonGateLost hE aa hh sa sh ka kh ok small rest
    split at ok
    · have nd : child.Nodup := by
        apply (List.perm_insertionSort ..).nodup_iff.mpr
        apply List.nodup_cons.mpr
        refine ⟨fun old=>fresh (dropSubset _ _ _ _ (dropSubset _ _ _ _ old)),?_⟩
        have nds:=yes.1.1
        cases ka <;> cases kh <;> simp [drop,nds,nds.erase a,nds.erase h,(nds.erase a).erase h]
      exact cfg.sound nd ok budget rest
    · have hf : Tight cfg.f child d := canonGateTight hF aa hh ne sa sh ka kh
      have he : Tight cfg.e child d := canonGateTight hE aa hh ne sa sh ka kh
      have tab := later _ _ (eq_of_beq ok)
      exact tab (cfg.symF (index z) hf) (cfg.symE (index z) he) small budget
        (closedRun (index z) rest (cfg.fixed _))

end LiveAIG.SixLayers

namespace LiveAIG.SixLayers
abbrev Levels := Nat → Next
abbrev Hints := Nat → Nat → Nat

def site (cfg : Setup) (read : Reader) (levels : Levels) (hints : Hints) (k i : Nat) : Bool :=
  match levels k i with
  | none=>true
  | some p=>checked cfg read (levels (k+1)) p.1 p.2 (hints k i)
def block (cfg : Setup) (read : Reader) (levels : Levels) (hints : Hints) (width k b : Nat) :=
  (List.range width).all fun i=>site cfg read levels hints k (width*b+i)

theorem groupSound {cfg read levels hints width k d size}
    (pos : 0<width)
    (bounded : ∀{i p},levels k i=some p → i<size)
    (next : ∀ j p,levels (k+1) j=some p → Dead cfg d p)
    (groups : ∀b, b<(size+width-1)/width → block cfg read levels hints width k b=true) :
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
  exact checkedSound yes next

end LiveAIG.SixLayers

namespace LiveAIG.CofactorLoan
open FreeAIG FlatProjection
theorem transport {t s child d} {l : Lens t} (φ : B → B)
    (target : (read l.row t) ∘ φ = read l.row t)
    (rawAccepted : ∀ f∈basis raw, Avail (sources l s) (f∘φ))
    (others : ∀ w∈child, ∃ v∈s, (read l.row w) ∘ φ = read l.row v)
    (fl : flats l s ≤ flats l child) (h : Tight l s d) : Tight l child d := by
  intro k prog
  have mapped := prog.map (T:=sources l s) φ (by
    intro f hf
    rcases hf with root|⟨w,mem,rfl⟩
    · exact rawAccepted _ root
    · obtain ⟨v,m,eq⟩ := others w mem
      rw [eq];exact own _ m)
  rw [target] at mapped
  have lower := h mapped
  omega
end LiveAIG.CofactorLoan

namespace LiveAIG.InputSym
open FreeAIG CofactorLoan FlatProjection

theorem bound32 : ∀i : Fin 6, ∀r:B, rowIndex i r.val<32 := by decide +kernel
def φ (i : Fin 6) (r : B) : B := ⟨rowIndex i r.val,bound32 i r⟩
def back (i : Fin 6) : Fin 6 := ![0,1,2,4,3,5] i
theorem φ_back : ∀i r, φ i (φ (back i) r)=r := by decide +kernel
theorem rawDigits : ∀i : Fin 6, ∀j : Fin raw.length,∃k : Fin raw.length,∀r:B,
    obs (raw.get j) (φ i r)=obs (raw.get k) r := by decide +kernel
theorem rawClosed (i : Fin 6) (w : U) (wm : w∈raw) :
      ∃v∈raw,∀r:B,obs w (φ i r)=obs v r := by
  obtain ⟨j,hj,rfl⟩:=List.getElem_of_mem wm
  obtain ⟨k,eq⟩:=rawDigits i ⟨j,hj⟩
  exact ⟨raw.get k, List.get_mem ..,eq⟩

theorem readMoved {l : B→R} (h : ∀i r,rowIndex i (l r).val=(l (φ i r)).val)
    (i : Fin 6) (w : W) : read l (move i w)=(read l w)∘φ i := by
  funext r
  change (move i w)[(l r).val] = w[(l (φ i r)).val]
  rw [← BitVec.getLsbD_eq_getElem, ←BitVec.getLsbD_eq_getElem, bit_move, h]

theorem flatRead {u v : U} {f : B→B} (h : obs v=obs u ∘ f) (fl : flatU u=true) :
    flatU v=true := by
  have inj : Function.Injective obs := by
    intro x y eq
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    have z:=congrFun eq (⟨r,hr⟩ : B)
    simpa only [obs,BitVec.getLsbD_eq_getElem hr] using z
  simp only [flatU,Bool.or_eq_true,beq_iff_eq] at fl ⊢
  rcases fl with rfl|rfl
  · left; apply inj; rw [h,obsZero];rfl
  · right;apply inj; rw [h,obsOnes];rfl

theorem transportSym {t} (l : Lens t)
    (comm : ∀i r,rowIndex i (l.row r).val=(l.row (φ i r)).val)
    (invariant : ∀i, move i t=t) (i : Fin 6) {s d} (good : Tight l s d) :
    Tight l (canon (s.map (move i))) d := by
  apply permTight (List.perm_insertionSort _ _)
  intro k net
  refine transport (l:=l) (child:=s.map (move i)) (φ (back i)) ?_ ?_ ?_ ?_ @good net
  · rw [←readMoved comm,invariant]
  · rintro f ⟨w,wm,rfl⟩
    obtain ⟨z,zm,eq⟩:=rawClosed (back i) w wm
    have ex : obs w ∘ φ (back i) = obs z := funext eq
    rw [ex]
    exact .src (.inl ⟨z,zm,rfl⟩)
  · rintro w m
    obtain ⟨v,vm,rfl⟩:=List.mem_map.mp m
    refine ⟨v,vm,?_⟩
    rw [readMoved comm]
    funext r
    simp only [Function.comp_apply,φ_back]
  · unfold flats
    rw [List.countP_map]
    apply List.countP_mono_left
    intro w _ hw
    exact flatRead (by rw [l.eqn,l.eqn,readMoved comm]) hw

end LiveAIG.InputSym

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

namespace MajorityFive
open FreeAIG LiveAIG
def cut (x : X) (i : Fin 5) : Bool := x ⟨i.val, by omega⟩
def f : X → Bool := Upper12122.majFive ∘ cut
def t : W := 0xfee8e880fee8e880fee8e880fee8e880
def A : List W := inputs.take 5
def S : Set (Fn X) := {g | ∃ i : Fin 5,g=fun x=>cut x i}
set_option maxRecDepth 65536 in
theorem wordF : word f=t := by decide +kernel
theorem compile {k : Nat} (h : Has Inputs k Upper12122.majFive) :
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

theorem flipRun {s n c} (r : Run t s n c) : Run (~~~t) s n c := by
  generalize eq:t=z at r ⊢
  induction r with
  | done => rw [←normNeg];exact .done
  | gate a b sa sb ka kb ha hb ne nz fresh rest ih =>
    exact .gate a b sa sb ka kb ha hb ne nz fresh ih
end MajorityFive

namespace CommonArchive
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096 ≤ marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def g13Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0x0,0x0),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g13C : List ColumnInfo := []
def g13A : List (List Nat) := [[],[50],[32],[32,48],[48,32],[48]]
def g13D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g13L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g13D3)
  | _ => emptyPacking
def g13I (_ _ : Nat) : Option (Nat × Nat) := none
def g13 : Forest := ⟨13,3,fun i => g13Y[i]?.getD (0,0),g13C,g13A,g13L,g13I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g13P3_0 : block g13 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g13B3 : block g13 3 0 1=true := g13P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g13T : checkedTables g13 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g13 0 0 0 = true)
  · exact (rfl : block g13 1 0 0 = true)
  · exact (rfl : block g13 2 0 0 = true)
  · exact g13B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g13G : graphValid g13 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low13 : Lower true (varsX 13) (graphGoal 13) 4 := lower_forest (g:=g13) (i:=0) (hints:=2) (before_sound [] baseKnown) g13G g13T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K13 := extendKnown [] 4 [(13,[]),(37,[83,67]),(41,[50,82,66]),(44,[32,16,49,81,65]),(69,[99,67,84]),(73,[50,98,66,84]),(76,[32,16,49,97,65,84]),(97,[82,99,66,67]),(100,[32,16,81,99,65,67]),(104,[48,16,82,97,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V13 : Known true K13 := extend_ok (m:=13) baseKnown low13 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[(0xdf7ec03c3ffe0fbefd80787ffc1f7dfb00f0ff,0x82040444444421040808888888420810111111),(0x0,0x0),(0x1fbf43c3c3fff03f7e878787ffe07efd0f0f0f,0x4080888888842081011111110841020222222),(0xe03fbc03fc3fffc07f7807f87fff80fef00ff0,0x8101111111084102022222221082040444444),(0x0,0x0),(0xffc03ffc003fffff807ff8007fffff00fff000,0x10202222222108204044444442104080888888),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := [(1,0,44,0,4),(4,0,41,0,4),(8,0,37,0,4),(32,0,13,0,4)]
def g45A : List (List Nat) := [[],[83],[50],[50,82],[82,50],[82],[32],[32,83],[32,48],[32,48,80],[32,80,48],[32,80],[48,32],[48,32,82],[48],[48,80],[48,82],[48,82,32],[80,32,50],[80,32],[80,48],[80],[80,50,32],[80,50]]
def g45D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8028023ea6a1221e12148110
def g45D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6090858702fd0910bd42443e48110
def g45H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x122
def g45D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd1027d10
def g45H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x101ce31400260006044c4007028
def g45D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3904f
def g45H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb23000000000028400000005400b84200000
def g45L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g45D3)
  | 4 => (3,2,2,0,0,5,0,g45D4)
  | 5 => (1,1,2,0,0,0,0,g45D5)
  | 6 => (1,0,2,0,0,0,0,g45D6)
  | _ => emptyPacking
def g45I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 3 0 5 1 0 g45H4
  | 5 => lookupWord 2 11 3 9 2 3 g45H5
  | 6 => lookupWord 1 17 0 9 0 5 g45H6
  | _ => fun _ => none
def g45 : Forest := ⟨45,6,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P3_0 : block g45 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B3 : block g45 3 0 2=true := g45P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P4_0 : block g45 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B4 : block g45 4 0 3=true := g45P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P5_0 : block g45 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B5 : block g45 5 0 1=true := g45P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P6_0 : block g45 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B6 : block g45 6 0 1=true := g45P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact g45B3
  · exact g45B4
  · exact g45B5
  · exact g45B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K13) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 7 := lower_forest (g:=g45) (i:=0) (hints:=2) (before_sound K13 V13) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K13 7 [(45,[]),(77,[101]),(101,[83,67,100]),(105,[50,82,66,100]),(108,[32,16,49,81,65,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V13 low45 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[(0xc0fc0fc0fdf81fbf7f03f7efec0007c00f83ff,0x82082082081041020208204040210842108421),(0x0,0x0),(0xff000fff01ffe03fbffc07f7f400f801f07c1f,0x4104104102082040410408080421084210842),(0xfffff00001ffffc03ffff807f81f003e007fe0,0x8208208204104080820810100842108421084),(0x0,0x0),(0xfffffffffe0000003ffffff803e0003fff8000,0x10410410408208101041020201084210842108),(0xffffffffffffffffc000000003ffffc0000000,0x20820820810410202082040402108421084210),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,7),(4,0,105,0,7),(8,0,101,0,7),(32,0,77,0,7),(64,0,45,0,7),(5,0,104,0,4),(9,0,100,0,4),(12,0,97,0,4),(33,0,76,0,4),(36,0,73,0,4),(40,0,69,0,4)]
def g109A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[50],[50,101],[50,82],[50,82,98],[50,98,82],[50,98],[82,50],[82,50,99],[82],[82,98],[82,99],[82,99,50],[98,50,83],[98,50],[98,82],[98],[98,83,50],[98,83],[32],[32,101],[32,83],[32,83,99],[32,99,83],[32,99],[32,48],[32,48,101],[32,48,80],[32,48,80,96],[32,48,96,80],[32,48,96],[32,80,48],[32,80,48,99],[32,80],[32,80,96],[32,80,99],[32,80,99,48],[32,96,48,83],[32,96,48],[32,96,80],[32,96],[32,96,83,48],[32,96,83],[48,32],[48,32,101],[48,32,82],[48,32,82,98],[48,32,98,82],[48,32,98],[48],[48,101],[48,80],[48,80,96],[48,96,80],[48,96],[48,82],[48,82,98],[48,82,32],[48,82,32,96],[48,82,96,32],[48,82,96],[48,98,82],[48,98],[48,98,32,80],[48,98,32],[48,98,80],[48,98,80,32],[80,32,50],[80,32,50,99],[80,32],[80,32,98],[80,32,99],[80,32,99,50],[80,48],[80,48,99],[80],[80,96],[80,99],[80,99,48],[80,50,32],[80,50,32,98],[80,50],[80,50,96],[80,50,98],[80,50,98,32],[80,98,48,50],[80,98,48],[80,98,50],[80,98,50,48],[80,98],[80,98,32],[96,32,50,83],[96,32,50],[96,32,82],[96,32],[96,32,83,50],[96,32,83],[96,48,83],[96,48],[96,80],[96],[96,83,48],[96,83],[96,50,32,82],[96,50,32],[96,50,80],[96,50],[96,50,82,32],[96,50,82],[96,82,48],[96,82,48,50],[96,82,50,48],[96,82,50],[96,82,32],[96,82]]
def g109D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x24180360709aa26498a40887805915350d2148110
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x104002820a04000000120808103df5df82d4b78d982a4854300c3874dc1654c91087b805d9544c910cb374d913148110ad183d913148110f81435093148110f43544c93148110f41544c93148110b6184d4d2148110e6364d4d2148110b638454d2148110e636454d2148110e616454d2148110b618550d2148110f415350d2148110
def g109H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7015c400053040d000
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41010204004040000748102040000c1d2040d221200c08103481002410805020c2008202041810904000241d003002420481440706057381801800a090605101c19cc144090805739216669825a9323e8c22a87216821fa7b1e6781d2711be681926317e5e16a531364a11a43106400e2370b62007a1502e0023fba2c7a92211f5d36354910a7ee8b1aa48856f7254d524423ebb4ca992215b5ca654c9108fee8b2a648863f74595324431e3a2ca992219edc1654c910a7ee8b2a648856f72595324423ebb6a8992218fd93544c910adae5aa2648847f76551324423ebb2a899221bc585604c910af2e9a9a408867b64d4d20442bdba2a6902219ed915348110cf2c8a9a408876b7254d20442f5b92a6902215e5d54348110de6c898a40886f1644c520443b9aa26290221dc5513148110fc2e498a40887e1424c520443f0a9a4290221f850d214811087ee8b2a64887c1324c520443b1a9a4290221d854d2148110
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x45064c1e6020001c1c1d702bc80000630c000018583240000000000006c600020058000000000000000000000000000048000000000000000000000000000000000f494000000000000000000300180000000c784000000000000000c028000000000000004061000002488f5ab0d83c0000000000000000000000031820001691e80300000000000000069f33195e4dc43d000010c00c4a4723c8de31b478c0002000000000000000000000000000003068e00e0002306000000000000000000086180001c080000c00440c800000000000cf1c00000e1000061cc0000000b180000395380000000692c0000000791800024f800000001003646080000000a010000185200000000000000000000002881318c00002500000000074900001406000000000001c65e80a0010c19f000800011c60000000286b01204a1504060100
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c3056623466107c019989809920e902152520ca5214144294a0c014288a428361144882414467083058228466143a5d30e0662d3a58700414333a414412202b3c348612199d20a2870d03a732414795e43886067e5de6f1935a94847d0436cb2240600dc00dfd8d524437d6354910bfd8d524437d5354910df995324437d654c910dfd51324437d544c910fe58132443f95348110fe50d204427d63d49109fd8d524427d654c910ded4d20443795348110fc4c520443e12148110
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34080d30c1089e804e014447c0000060041cd16c18a000fa86414f00ec8c60e57062e9a22e01120106836400000000f1e46813c00020000930e00002011a000020078004940820000000009c31c032a00c80c04806b5e2941cba2a43806f4f0b47c576474b21c8f830023000000001801a0000c0048000280314022b04d200210600000043d12321b4004010cb0029805e80900000e3888000183a00000000000c2e0382618c000040c2b003bed068da5000010028e78ba34558d2280480787200f29a3980080000000059e4201af668d3327f0703c017a185d08880002591564c8900300001412fc049000011a180001e78a00002802b4f03c015c0228000325194016c06b000000141638000000000080428c1c000049a1f120e3cca90c08000c0000d21c00001a42c00006713e00e000000345a000d0071023800000000b48500000c38a6706b012c001d711e00000000000000001ad0c2408930c155d14000a8ce08804914704108a0c13c1002
def g109D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4038da6690a3c8a142a70a5011a6690a20e30ba6694301030ba6694235a3f3015007f54910fe992217f52442faa4887e48110
def g109H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2002500c400000001e131250800000000000000010d0800000000000000024e1c000240440000000000000000000000034e224384000000000001430c00000000000143040000000000000000000000000000000000000000000000014e0ec088000000000001cf0a41abc0c2e01c0000000000000000809bc08c0000009400000003e1240000000000000000000203094002de24000000034028000140174208000000000000000000009e2c000040b8000000000000402c000000000000c3239e300000000000000000c0200001cf04000000000000000000001e2800000000000000000002c090000000021e34000000000000000000000002c004000000038120000000000000000000004e088031400c00000000000000000000000186040000000180400001810e001b43880000000000000000000000006a2400000000000000000000001c00004d200000000000000000000000000000da0a03a000000000000240365204000000000003d908000000024d0c0000000000000000000000000000000000000000000200a000000000000000000000000000000000801000000000000000000001c008000340bc0003ac1c00000000000000000001821c000381ac00000000000000000000803c000282200000000000000000810800000003838e0c24000000020084000000000000000000000000820f403800000000000000000000000000000000000120700510
def g109D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2d2720806fd10
def g109H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x920000000000000c02000000000000c0400000000000000000051401b000000000000000721000b12000ee0000000000000000e0b000000000000bc0000000000000000000401000000000000000000d11303000000200024610000000b22000bd00000001
def g109D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x219080bf
def g109H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4abed00091800000000524000c30000000000000000000000000200000000000004780000000170a5200000000000000000000000000000000033c0000000000000000000000
def g109L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g109D3)
  | 4 => (14,5,4,0,0,7,0,g109D4)
  | 5 => (38,4,4,0,0,10,0,g109D5)
  | 6 => (18,3,4,0,0,10,0,g109D6)
  | 7 => (5,2,4,0,0,8,0,g109D7)
  | 8 => (1,1,4,0,0,0,0,g109D8)
  | 9 => (1,0,4,0,0,0,0,g109D9)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 11 0 12 1 7 g109H4
  | 5 => lookupWord 16 167 4 15 4 7 g109H5
  | 6 => lookupWord 30 163 6 17 6 7 g109H6
  | 7 => lookupWord 17 263 2 16 5 7 g109H7
  | 8 => lookupWord 4 67 1 12 3 5 g109H8
  | 9 => lookupWord 2 53 0 11 0 7 g109H9
  | _ => fun _ => none
def g109 : Forest := ⟨109,9,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P3_0 : block g109 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B3 : block g109 3 0 2=true := g109P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 14=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_4 : block g109 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 38=true := (@block_merge g109 5 0 4 34 g109P5_0 g109P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_1 : block g109 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_7 : block g109 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 18=true := (@block_merge g109 6 0 1 17 g109P6_0 (@block_merge g109 6 1 6 11 g109P6_1 g109P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P7_0 : block g109 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P7_3 : block g109 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B7 : block g109 7 0 5=true := (@block_merge g109 7 0 3 2 g109P7_0 g109P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P8_0 : block g109 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B8 : block g109 8 0 1=true := g109P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P9_0 : block g109 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B9 : block g109 9 0 1=true := g109P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact g109B3
  · exact g109B4
  · exact g109B5
  · exact g109B6
  · exact g109B7
  · exact g109B8
  · exact g109B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 10 := lower_forest (g:=g109) (i:=0) (hints:=2) (before_sound K45 V45) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end CommonArchive

namespace LiveAIG.MinorTransfer
open CommonArchive
open FreeAIG
private theorem offer {B : Type} {S : Set (Fn B)} {pool : List (Wire B)} {f : Fn B}
    (ha : Avail S f) (supply : ∀ g∈S,Available true pool g) : Available true pool f := by
  induction ha with
  | src h => exact supply _ h
  | const b => exact .inr (.inl ⟨b,rfl⟩)
  | @neg g _ ih =>
    rcases ih with mem | ⟨b,hb⟩ | ⟨_,mem⟩
    · apply Or.inr;right;refine ⟨rfl,?_⟩
      have double : inv (FreeAIG.neg g) = g := by funext x;simp [inv,FreeAIG.neg]
      rwa [double]
    · subst g;exact .inr (.inl ⟨!b,rfl⟩)
    · exact .inl mem

private theorem extendReach {B : Type} {S : Set (Fn B)} {roots bank : List (Wire B)} {j k : Nat}
    {f : Fn B} (h : Has S k f) (p : Reach true roots j bank)
    (supply : ∀ g∈S, Available true bank g) :
    ∃ z ≤ j+k, ∃ out, Reach true roots z out ∧ Available true out f := by
  induction h generalizing j bank with
  | done hf => exact ⟨_,by omega,_,p,offer hf supply⟩
  | @step S k a b f ha hb tail ih =>
    have step := Reach.two false p (offer ha supply) (offer hb supply)
    obtain ⟨z,le,out,rep,av⟩ := ih step (by
      rintro g (rfl|hg)
      · exact .inl List.mem_cons_self
      · rcases supply g hg with m|con|⟨h,m⟩
        · exact .inl (List.mem_cons_of_mem _ m)
        · exact .inr (.inl con)
        · exact .inr (.inr ⟨h,List.mem_cons_of_mem _ m⟩))
    exact ⟨z,by omega,out,rep,av⟩

theorem imported {roots : List Sig} {T : Sig} {L : Nat} (bound : Lower true roots T L)
    {k : Nat} (run : Has {g | g∈roots.map observe} k (observe T)) : L≤k := by
  obtain ⟨z,le,out,r,h⟩ := extendReach (j:=0) run
    (Reach.start (roots:=roots.map observe)) (fun _ mem=>Or.inl mem)
  exact (bound _ _ r h).trans (by omega)

end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open CommonArchive
open FlatProjection FreeAIG

def scatter (codes : List Nat) (r : Row) : R :=
  Fin.ofNat 128 ((codes.zipIdx).foldl (fun a p =>
    let i := p.1
    let v := if i<2 then i==1 else (r.val.testBit (i/2-1)) != (i % 2==1)
    if v then a+2^p.2 else a) 0)

def flatWord (q : Sig) := q==zero || q==one
def cheapWord (roots : List Sig) (q : Sig) :=
  flatWord q || roots.contains q || roots.contains (CommonArchive.neg q)

private theorem oneBit (i : Row) : bit i one=true := by
  unfold bit one
  rw [BitVec.getLsbD_allOnes]
  simp

theorem flatWordSound {q : Sig} (h : flatWord q=true) : constant (observe q) := by
  simp only [flatWord,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with rfl|rfl
  · refine ⟨false,?_⟩;funext i;simp [observe,bit,zero]
  · refine ⟨true,?_⟩;funext i;exact oneBit i

theorem cheapWordSound {roots : List Sig} {q : Sig} (h : cheapWord roots q=true) :
    Avail {g | g∈roots.map observe} (observe q) := by
  simp only [cheapWord,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  rcases h with (hc|hm)|hn
  · obtain ⟨b,e⟩:=flatWordSound hc
    rw [e];exact .const b
  · exact .src (List.mem_map_of_mem hm)
  · have e : FreeAIG.neg (observe (CommonArchive.neg q)) = observe q := by
      rw [obs_neg];funext x;simp [FreeAIG.neg,inv]
    exact e ▸ Avail.neg (Avail.src (List.mem_map_of_mem hn))

def wordImage (σ : Row→R) (w : W) : Sig := table (read σ w)
def usable (σ : Row→R) (t : W) (s : List W) (roots : List Sig) (T : Sig) (L max : Nat) : Bool :=
  wordImage σ t == T && !flatWord T &&
    s.all (fun w=>cheapWord roots (wordImage σ w)) &&
    decide (max < L+s.countP (fun w=>flatWord (wordImage σ w)))

theorem excludes {σ : Row→R} {t : W} {s : List W} {roots : List Sig} {T : Sig} {L max n c : Nat}
    (bound : Lower true roots T L) (test : usable σ t s roots T L max=true) (small : n ≤ max) :
    ¬ Run t s n c := by
  intro run
  simp only [usable,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',List.all_eq_true,
    decide_eq_true_eq] at test
  obtain ⟨⟨⟨eq,proper⟩,src⟩,limit⟩:=test
  have idn (w : W) : observe (wordImage σ w)=read σ w := observe_table _
  have targetEq : read σ t=observe T := (idn t).symm.trans (congrArg observe eq)
  have nc : ¬constant (read σ t) := by
    rw [targetEq]
    rintro ⟨b,hb⟩
    have wrong : flatWord T=true := by
      cases b
      · have e : T=zero := bit_ext (fun i=>by
          have v:=congrFun hb i
          simpa [observe,bit,zero] using v)
        simp [flatWord,e]
      · have e : T=one := bit_ext (fun i=>by
          have v:=congrFun hb i
          exact v.trans (oneBit i).symm)
        simp [flatWord,e]
    simp_all
  obtain ⟨k,sp,hk⟩:=saves σ run nc (S:={g | g∈roots.map observe}) (by
    intro w hw
    rw [←idn w]
    exact cheapWordSound (src w hw))
  have lower:=imported bound (targetEq ▸ hk)
  have count : s.countP (fun w=>flatWord (wordImage σ w)) ≤ s.countP (flat σ) :=
    List.countP_mono_left (fun w _ h=> (flat_spec _ _).mpr (idn w ▸ flatWordSound h))
  omega
end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open CommonArchive
open FlatProjection

abbrev RowEntry := W × Sig

def findWord (m : List RowEntry) (w : W) : Sig :=
  match m.find? (fun e=>e.1==w) with
  | some e=>e.2
  | none=>zero

def wordsValid (σ : Row→R) (m : List RowEntry) :=
  ∀e∈m, read σ e.1=observe e.2

def knows (m : List RowEntry) (w : W) := m.any (fun e=>e.1==w)

theorem found {m : List RowEntry} {w : W} {σ : Row→R} (h : wordsValid σ m) (has : knows m w=true) :
    read σ w=observe (findWord m w) := by
  induction m with
  | nil=>simp [knows] at has
  | cons p ps ih=>
    by_cases eq:p.1=w
    · rw [←eq];simpa [findWord] using h p List.mem_cons_self
    · have diff : (p.1==w)=false := by simp [eq]
      have tail : knows ps w=true := by simpa [knows,diff] using has
      simpa [findWord,diff] using ih (fun _ mem=>h _ (List.mem_cons_of_mem _ mem)) tail

def signedQ (q : Sig) (b : Bool) := if b then ~~~q else q

theorem imageSigned {σ : Row→R} {a : W} {u : Sig} (h : read σ a=observe u) (b : Bool) :
    read σ (signed a b)=observe (signedQ u b) := by
  cases b
  · exact h
  · funext r
    have v:=congrFun h r
    simpa [FlatProjection.read,observe,bit,signed,signedQ] using congrArg Bool.not v

theorem imageAnd {σ : Row→R} {a b : W} {u v : Sig} (ha : read σ a=observe u) (hb : read σ b=observe v) :
    read σ (a&&&b)=observe (u&&&v) := by
  funext r
  simpa [FlatProjection.read,observe,bit] using congrArg₂ Bool.and (congrFun ha r) (congrFun hb r)

def gateQ (a b : W) (u v : Sig) (sa sb : Bool) : Sig :=
  signedQ (signedQ u sa &&& signedQ v sb) (signed a sa &&& signed b sb)[0]

theorem addValid {σ : Row→R} {m : List RowEntry} (h : wordsValid σ m)
    (a b : W) (sa sb : Bool) (h1 : knows m a=true) (h2 : knows m b=true) :
    wordsValid σ ((made a b sa sb,gateQ a b (findWord m a) (findWord m b) sa sb)::m) := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl|hz
  · exact imageSigned (imageAnd (imageSigned (found h h1) _) (imageSigned (found h h2) _)) _
  · exact h z hz

def fastTest (db : List RowEntry) (s : List W) (roots : List Sig) (L max : Nat) :=
  s.all (knows db) && s.all (fun w=>cheapWord roots (findWord db w)) &&
  decide (max<L+s.countP (fun w=>flatWord (findWord db w)))

theorem excludesFast {σ : Row→R} {t : W} {s : List W} {roots : List Sig} {T : Sig} {L max n c : Nat}
    {db : List RowEntry} (tableOk : wordsValid σ db)
    (target : read σ t = observe T) (proper : flatWord T=false)
    (bound : Lower true roots T L) (test : fastTest db s roots L max=true)
    (small : n ≤ max) : ¬Run t s n c := by
  apply excludes bound _ small (σ:=σ)
  have eqSig {w : W} {q : Sig} (h:read σ w=observe q) : wordImage σ w=q :=
    bit_ext (fun i=> (bit_table _ i).trans (congrFun h i))
  simp only [fastTest,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at test
  have ok (w : W) (hw : w∈s) : wordImage σ w = findWord db w := eqSig (found tableOk (test.1.1 w hw))
  have counted : s.countP (fun w=>flatWord (wordImage σ w)) = s.countP (fun w=>flatWord (findWord db w)) :=
    List.countP_congr (fun w hw=>by rw [ok w hw])
  simp only [usable,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq]
  refine ⟨⟨⟨eqSig target,by simp [proper]⟩,?_⟩,?_⟩
  · intro w hw;rw [ok w hw];exact test.1.2 w hw
  · rw [counted];exact test.2
end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open CommonArchive
open FlatProjection

def checked (σ : Row→R) (db : List RowEntry) := db.all (fun p=>wordImage σ p.1==p.2)

theorem checkedValid {σ : Row→R} {db : List RowEntry} (h : checked σ db=true) : wordsValid σ db := by
  intro p hp
  have e := beq_iff_eq.mp (List.all_eq_true.mp h p hp)
  exact (observe_table _).symm.trans (congrArg observe e)

theorem observation {σ : Row→R} {w : W} {q : Sig} (e : wordImage σ w=q) : read σ w=observe q :=
  (observe_table _).symm.trans (congrArg observe e)

structure Lens (t : W) where
  σ : Row → R
  db : List RowEntry
  roots : List Sig
  goal : Sig
  cost : Nat
  dbOk : wordsValid σ db
  target : read σ t=observe goal
  proper : flatWord goal=false
  bound : Lower true roots goal cost

def Lens.reject {t : W} (l : Lens t) (a b : W) (sa sb ka kb : Bool) (max : Nat) :=
  let g := made a b sa sb
  let q := gateQ a b (findWord l.db a) (findWord l.db b) sa sb
  knows l.db a && knows l.db b &&
    fastTest ((g,q)::l.db) (after inputs a b g ka kb) l.roots l.cost max

theorem Lens.rejects {t : W} (l : Lens t) {a b : W} {sa sb ka kb : Bool} {max n c : Nat}
    (h : l.reject a b sa sb ka kb max=true) (small : n ≤ max) :
    ¬Run t (after inputs a b (made a b sa sb) ka kb) n c := by
  simp only [Lens.reject,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,test⟩:=h
  exact excludesFast (addValid l.dbOk a b sa sb h1 h2) l.target l.proper l.bound test small

def rejected {t : W} (ls : List (Lens t)) (a b : W) (sa sb ka kb : Bool) (max : Nat) :=
  ls.any (fun l=>l.reject a b sa sb ka kb max)
theorem rejectedSound {t : W} {ls : List (Lens t)} {a b : W} {sa sb ka kb : Bool} {max n c : Nat}
    (ok : rejected ls a b sa sb ka kb max=true) (small : n ≤ max) :
    ¬Run t (after inputs a b (made a b sa sb) ka kb) n c := by
  obtain ⟨l,_,h⟩:=List.any_eq_true.mp ok
  exact l.rejects h small
end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open CommonArchive
open FlatProjection

structure Rule where
  off : W
  onMask : W
  image : Sig

def Rule.covers (σ : Row→R) (rule : Rule) : Bool :=
  (List.finRange 512).all fun r=>
    (if bit r rule.image then rule.onMask else rule.off)[(σ r).val]

def Rule.fits (rule : Rule) (w : W) : Bool :=
  (w &&& rule.off)==0 && ((~~~w) &&& rule.onMask)==0

theorem Rule.sound {σ : Row→R} {z : Rule} (h : z.covers σ=true) {w : W} (m : z.fits w=true) :
    read σ w=observe z.image := by
  funext r
  have seen := List.all_eq_true.mp h r (List.mem_finRange r)
  simp only [Rule.fits,Bool.and_eq_true,beq_iff_eq] at m
  have lo:=congrArg (fun a : W=>a[(σ r).val]) m.1
  have hi:=congrArg (fun a : W=>a[(σ r).val]) m.2
  simp only [BitVec.getElem_and,BitVec.getElem_not,BitVec.getElem_zero] at lo hi
  change w[(σ r).val]=bit r z.image
  cases v:bit r z.image <;> simp [v] at seen <;> simp_all

def selectImage (rules : List Rule) (w : W) : Sig :=
  ((rules.find? (fun z=>z.fits w)).map Rule.image).getD zero
def scanned (rules : List Rule) (w : W) := rules.any (fun z=>z.fits w)

theorem imageOfScan {σ : Row→R} {rules : List Rule}
    (ok : rules.all (Rule.covers σ)=true) {w : W} (h : scanned rules w=true) :
    read σ w=observe (selectImage rules w) := by
  induction rules with
  | nil=>simp [scanned] at h
  | cons z zs ih=>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    cases m:z.fits w
    · exact (by simpa [selectImage,m] using ih ok.2 (by simpa [scanned,m] using h))
    · simpa [selectImage,m] using Rule.sound ok.1 m

structure MaskLens (t : W) where
  lens : Lens t
  rules : List Rule
  ok : rules.all (Rule.covers lens.σ)=true

def MaskLens.reject {t : W} (p : MaskLens t) (s : List W) (budget : Nat) :=
  s.all (scanned p.rules) && s.all (fun w=>cheapWord p.lens.roots (selectImage p.rules w)) &&
    decide (s.length+budget < 1+p.lens.cost+s.countP (fun w=>flatWord (selectImage p.rules w)))

theorem MaskLens.noRun {t : W} {s : List W} {budget n c : Nat}
    (p : MaskLens t) (cert : p.reject s budget=true) (cap : c≤budget) : ¬Run t s n c := by
  intro run
  simp only [MaskLens.reject,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at cert
  have eq (w : W) (hw:w∈s) : wordImage p.lens.σ w=selectImage p.rules w :=
    bit_ext (fun i=>(bit_table _ i).trans (congrFun (imageOfScan p.ok (cert.1.1 w hw)) i))
  have cnt : s.countP (fun w=>flatWord (wordImage p.lens.σ w))=s.countP (fun w=>flatWord (selectImage p.rules w)) :=
    List.countP_congr (fun w hw=>by rw [eq w hw])
  apply excludes (σ:=p.lens.σ) p.lens.bound (max:=n) _ (Nat.le_refl _) run
  have targetEq : wordImage p.lens.σ t=p.lens.goal :=
    bit_ext (fun i=>(bit_table _ i).trans (congrFun p.lens.target i))
  simp only [usable,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq]
  refine ⟨⟨⟨targetEq,by simp [p.lens.proper]⟩,?_⟩,?_⟩
  · intro w hw;rw [eq w hw];exact cert.1.2 w hw
  · rw [cnt]
    have len:=balance run
    omega
end LiveAIG.MinorTransfer

namespace MajorityFive
open LiveAIG LiveAIG.MinorTransfer
open CommonArchive

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem core : Lower true (CommonArchive.varsX 45)
    (CommonArchive.graphGoal 45) 7 := by
  exact CommonArchive.low45

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m00 : MaskLens (~~~t) where
  lens := {
    σ := scatter [0, 3, 7, 9, 13, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0x55555555, 0x0, 0x0⟩, ⟨0x0, 0x55555555, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x44444444, 0x11111111, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0x50505050, 0x5050505, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0x55005500, 0x550055, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0x55550000, 0x5555, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x11111111, 0x44444444, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0x5050505, 0x50505050, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0x550055, 0x55005500, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0x5555, 0x55550000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m01 : MaskLens (~~~t) where
  lens := {
    σ := scatter [3, 0, 7, 9, 13, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0x33333333, 0x0, 0x0⟩, ⟨0x0, 0x33333333, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x22222222, 0x11111111, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0x30303030, 0x3030303, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0x33003300, 0x330033, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0x33330000, 0x3333, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x11111111, 0x22222222, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0x3030303, 0x30303030, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0x330033, 0x33003300, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0x3333, 0x33330000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m02 : MaskLens (~~~t) where
  lens := {
    σ := scatter [3, 7, 0, 9, 13, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xf0f0f0f, 0x0, 0x0⟩, ⟨0x0, 0xf0f0f0f, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0xa0a0a0a, 0x5050505, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0xc0c0c0c, 0x3030303, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xf000f00, 0xf000f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xf0f0000, 0xf0f, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x5050505, 0xa0a0a0a, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0x3030303, 0xc0c0c0c, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xf000f, 0xf000f00, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xf0f, 0xf0f0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m03 : MaskLens (~~~t) where
  lens := {
    σ := scatter [3, 7, 9, 0, 13, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xff00ff, 0x0, 0x0⟩, ⟨0x0, 0xff00ff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0xaa00aa, 0x550055, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0xcc00cc, 0x330033, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xf000f0, 0xf000f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xff0000, 0xff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x550055, 0xaa00aa, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0x330033, 0xcc00cc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xf000f, 0xf000f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xff, 0xff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m04 : MaskLens (~~~t) where
  lens := {
    σ := scatter [3, 7, 9, 13, 0, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xffff, 0x0, 0x0⟩, ⟨0x0, 0xffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0xaaaa, 0x5555, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0xcccc, 0x3333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xf0f0, 0xf0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xff00, 0xff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x5555, 0xaaaa, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0x3333, 0xcccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xf0f, 0xf0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xff, 0xff00, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m10 : MaskLens t where
  lens := {
    σ := scatter [1, 2, 6, 8, 12, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xaaaaaaaa, 0x0, 0x0⟩, ⟨0x0, 0xaaaaaaaa, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x22222222, 0x88888888, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0xa0a0a0a, 0xa0a0a0a0, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xaa00aa, 0xaa00aa00, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xaaaa, 0xaaaa0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x88888888, 0x22222222, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0xa0a0a0a0, 0xa0a0a0a, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xaa00aa00, 0xaa00aa, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xaaaa0000, 0xaaaa, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m11 : MaskLens t where
  lens := {
    σ := scatter [2, 1, 6, 8, 12, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xcccccccc, 0x0, 0x0⟩, ⟨0x0, 0xcccccccc, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x44444444, 0x88888888, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0xc0c0c0c, 0xc0c0c0c0, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xcc00cc, 0xcc00cc00, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xcccc, 0xcccc0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0x88888888, 0x44444444, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0xc0c0c0c0, 0xc0c0c0c, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xcc00cc00, 0xcc00cc, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xcccc0000, 0xcccc, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m12 : MaskLens t where
  lens := {
    σ := scatter [2, 6, 1, 8, 12, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xf0f0f0f0, 0x0, 0x0⟩, ⟨0x0, 0xf0f0f0f0, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x50505050, 0xa0a0a0a0, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0x30303030, 0xc0c0c0c0, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xf000f0, 0xf000f000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xf0f0, 0xf0f00000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0xa0a0a0a0, 0x50505050, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0xc0c0c0c0, 0x30303030, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xf000f000, 0xf000f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xf0f00000, 0xf0f0, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m13 : MaskLens t where
  lens := {
    σ := scatter [2, 6, 8, 1, 12, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xff00ff00, 0x0, 0x0⟩, ⟨0x0, 0xff00ff00, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x55005500, 0xaa00aa00, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0x33003300, 0xcc00cc00, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xf000f00, 0xf000f000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xff00, 0xff000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0xaa00aa00, 0x55005500, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0xcc00cc00, 0x33003300, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xf000f000, 0xf000f00, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xff000000, 0xff00, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def m14 : MaskLens t where
  lens := {
    σ := scatter [2, 6, 8, 12, 1, 0, 0]
    db := []
    dbOk := by intro e h;simp at h
    roots := CommonArchive.varsX 45
    goal := CommonArchive.graphGoal 45
    cost := 7
    target := observation (by decide +kernel)
    proper := by decide +kernel
    bound := core
  }
  rules := [⟨0xffff0000, 0x0, 0x0⟩, ⟨0x0, 0xffff0000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩, ⟨0x55550000, 0xaaaa0000, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩, ⟨0x33330000, 0xcccc0000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩, ⟨0xf0f0000, 0xf0f00000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩, ⟨0xff0000, 0xff000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩, ⟨0xaaaa0000, 0x55550000, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩, ⟨0xcccc0000, 0x33330000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩, ⟨0xf0f00000, 0xf0f0000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩, ⟨0xff000000, 0xff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
  ok := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def positive : List (MaskLens t) := [m10,m11,m12,m13,m14]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def dual : List (MaskLens (~~~t)) := [m00,m01,m02,m03,m04]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def hit (p : List W × Nat) :=
  positive.any (fun z=>z.reject p.1 p.2) || dual.any (fun z=>z.reject p.1 p.2)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem complete : (children t A 5).all hit=true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem lower {k : Nat} (h : FreeAIG.Has FreeAIG.Inputs k Upper12122.majFive) : 10 ≤ k := by
  by_contra! cap
  obtain ⟨n,le,c,run⟩:=compile h
  have len:=balance run
  have al : A.length=5 := by rfl
  rw [al] at len
  cases n with
  | zero=>omega
  | succ n=>
    obtain ⟨p,member,d,db,r⟩:=continueRun run (budget:=5) (by omega)
    have covered:=List.all_eq_true.mp complete p member
    simp only [hit,Bool.or_eq_true,List.any_eq_true] at covered
    rcases covered with ⟨z,_,e⟩|⟨z,_,e⟩
    · exact z.noRun e db r
    · exact z.noRun e db (flipRun r)
end MajorityFive

namespace ThresholdFour
open FreeAIG LiveAIG.MinorTransfer
open CommonArchive

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def four (x : Fin 5 → Bool) : Bool := decide (4 ≤ (List.ofFn x).count true)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def putZero (x : Fin 5 → Bool) : Fin 6 → Bool := Fin.insertNth (4 : Fin 6) false x

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cofactor : ∀ x, Upper12122.target (putZero x) = four x := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem negateOutput {α : Type} {S : Set (Fn α)} {k f}
    (h : Has S k f) : Has S k (FreeAIG.neg f) := by
  induction h with
  | done a => exact .done (.neg a)
  | step a b _ ih => exact .step a b ih

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def dualInput (roots : List Sig) (r : Row) (i : Fin 5) : Bool :=
  !(observe (roots.getD i.val 0) r)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fromClique {roots : List Sig} {goal : Sig}
    (mem : ∀ i : Fin 5, roots.getD i.val 0 ∈ roots)
    (eq : ∀ r : Row, (!(four (dualInput roots r))) = observe goal r)
    (clique : Lower true roots goal 10) {k} (h : Has Inputs k four) : 10 ≤ k := by
  apply imported clique
  have hm := h.map (T := {g | g ∈ roots.map observe}) (dualInput roots) (by
    rintro _ ⟨i,rfl⟩
    exact .neg (.src (List.mem_map.mpr ⟨_,mem i,rfl⟩)))
  have both := negateOutput hm
  have id : FreeAIG.neg (four ∘ dualInput roots) = observe goal := funext eq
  rwa [id] at both

end ThresholdFour

namespace ThresholdFour
open FreeAIG
open CommonArchive

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique : Lower true (CommonArchive.varsX 109)
    (CommonArchive.graphGoal 109) 10 := by
  exact CommonArchive.low109

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Has Inputs k four) : 10 ≤ k :=
  fromClique (by decide +kernel) (by decide +kernel) clique h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cofactorLower {k} (h : Has Inputs k (Upper12122.target ∘ putZero)) : 10 ≤ k := by
  have eq : Upper12122.target ∘ putZero = four := funext cofactor
  exact lower (eq ▸ h)

end ThresholdFour

namespace LiveAIG.SixLenses
open FreeAIG FlatProjection CofactorLoan

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def target : W := 0xfee8e880fe008000fee8e880fe008000
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def rowF (r : B) : R := ⟨32+r.val, by omega⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def rowE (r : B) : R := ⟨if r.val<16 then r.val else 16+r.val, by split <;> omega⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def imageF (w : W) : U := w.extractLsb' 32 32
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def imageE (w : W) : U := (w.extractLsb' 32 16) ++ (w.extractLsb' 0 16)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem eqF (w : W) : obs (imageF w) = read rowF w := by
  funext r
  simp [obs,imageF,FlatProjection.read,rowF,←BitVec.getLsbD_eq_getElem]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem eqE (w : W) : obs (imageE w) = read rowE w := by
  funext r
  change (((w.extractLsb' 32 16) ++ (w.extractLsb' 0 16)) : BitVec (16+16)).getLsbD r.val =
    w.getLsbD (if r.val<16 then r.val else 16+r.val)
  rw [BitVec.getLsbD_append]
  by_cases h:r.val<16
  · simp [h]
  · have sm : r.val-16<16 := by omega
    have eq : 32+(r.val-16) = 16+r.val := by omega
    simp [h,sm,eq]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def encode (x : Fin 5 → Bool) : B := ⟨(∑ i : Fin 5, if x i then 2^i.val else 0) % 32, by omega⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem baseRoots : ∀ g∈basis raw, Avail Inputs (g∘encode) := by
  rintro _ ⟨w,m,rfl⟩
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with rfl|rfl|rfl|rfl|rfl
  · exact .src ⟨0,funext (show ∀ x : Fin 5 → Bool, obs 0xaaaaaaaa (encode x) = x 0 from by decide +kernel)⟩
  · exact .src ⟨1,funext (show ∀ x : Fin 5 → Bool, obs 0xcccccccc (encode x) = x 1 from by decide +kernel)⟩
  · exact .src ⟨2,funext (show ∀ x : Fin 5 → Bool, obs 0xf0f0f0f0 (encode x) = x 2 from by decide +kernel)⟩
  · exact .src ⟨3,funext (show ∀ x : Fin 5 → Bool, obs 0xff00ff00 (encode x) = x 3 from by decide +kernel)⟩
  · exact .src ⟨4,funext (show ∀ x : Fin 5 → Bool, obs 0xffff0000 (encode x) = x 4 from by decide +kernel)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem proper {σ : B→R} (h : read σ target 0 ≠ read σ target 31) :
    ¬constant (read σ target) := by
  rintro ⟨b,e⟩
  exact h ((congrFun e 0).trans (congrFun e 31).symm)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def F : Lens target where
  row := rowF
  image := imageF
  eqn := eqF
  proper := proper (by decide +kernel)
  lower := by
    intro k h
    have sent := h.map encode baseRoots
    have same : (read rowF target) ∘ encode = Upper12122.majFive := by
      funext x
      exact (show ∀ y : Fin 5 → Bool, read rowF target (encode y) = Upper12122.majFive y from by decide +kernel) x
    rw [same] at sent
    exact MajorityFive.lower sent

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def E : Lens target where
  row := rowE
  image := imageE
  eqn := eqE
  proper := proper (by decide +kernel)
  lower := by
    intro k h
    have sent := h.map encode baseRoots
    have same : (read rowE target) ∘ encode = ThresholdFour.four := by
      funext x
      exact (show ∀ y : Fin 5 → Bool, read rowE target (encode y) = ThresholdFour.four y from by decide +kernel) x
    rw [same] at sent
    exact ThresholdFour.lower sent

end LiveAIG.SixLenses

namespace LiveAIG.SixLenses
open LiveAIG.InputSym CofactorLoan

theorem commF : ∀i r,rowIndex i (rowF r).val = (rowF (φ i r)).val := by decide +kernel
theorem commE : ∀i r,rowIndex i (rowE r).val = (rowE (φ i r)).val := by decide +kernel

theorem tightFSym (i : Fin 6) {s d} (prior:Tight F s d) :
    Tight F (canon (s.map (move i))) d := by
  intro k net
  exact transportSym F commF keeps12122 i @prior net

theorem tightESym (i : Fin 6) {s d} (prior:Tight E s d) :
    Tight E (canon (s.map (move i))) d := by
  intro k net
  exact transportSym E commE keeps12122 i @prior net

end LiveAIG.SixLenses

namespace LiveAIG.SixLayers
open Many InputSym SixLenses

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

def cuts (p : State) (z : Nat) :=
  if z<4161536 then p.2==0 && anchorHint target p.1 z
  else decide (p.2≤1) && triple target p.1 (z-4161536)

theorem cutsSound {p z n c} (nd : p.1.Nodup) (yes : cuts p z=true) (small : c≤p.2)
    (run : Run target p.1 n c) : False := by
  unfold cuts at yes
  split at yes
  · obtain ⟨zero,bad⟩:=Bool.and_eq_true_iff.mp yes
    have zb := eq_of_beq zero
    have : c=0 := by omega
    subst c
    exact anchorHintSound nd bad run
  · obtain ⟨b,bad⟩:=Bool.and_eq_true_iff.mp yes
    exact tripleSound nd bad (small.trans (of_decide_eq_true b)) run

def cfg : Setup where
  t := target
  f := F
  e := E
  fixed := keeps12122
  symF := @tightFSym
  symE := @tightESym
  cut := cuts
  sound := @cutsSound

end LiveAIG.SixLayers

namespace Dag12122Data
open LiveAIG
def repeated (x : Nat) : W := BitVec.ofNat 128 (x * 18446744073709551617)
def raw : List W := [repeated 0xaaaaaaaaaaaaaaaa,repeated 0xcccccccccccccccc,repeated 0xf0f0f0f0f0f0f0f0,repeated 0xff00ff00ff00ff00,repeated 0xffff0000ffff0000,repeated 0xffffffff00000000]
def anchors : Array Nat := #[406390,505479,407141,10184275,1285733,11233123,1293430,11232850,10184548,11233122,11220561,504672,823073,10184547,407156,11232851,10184259,11744848,406901,11744849,11753313,406868,407140,11220833,23701074,1252692,16839184,11753314,11220834,11744850,504688,22791491,823090,11744800,25912626,471922,11753312,407139,11233124,11753040,22660692,33616673,11220835,11744576,1881650,23701073,27473185,10180180,11220530,504673,11744784,1878800,471923,10184549,16839440,1284448,11220562,25912899,11744577,10180160,16839713,10180451,11745121,10184258,27473441,10184531,10180448,11220240,22660691,504674,10180178,24220993,27473458,10180452,1285955,1681201,10184002,10184242,10184272,24221264,10183986,11745122,11745120,30073904,25912625,1422160,11753041,1879362,31520050,10180177,10180179,11220560,23701075,24221265,407122,11220769,1881633,10184546,11220786,31520033,33715250,11232833,11744801,16839696,24352064,498033,11220832,11232849,11233090,11753315,24351793,33714976,10180163,10183984,24352066,25912882,30073632,30471184,26432816,26432817,1193552,1251953,1488242,1488498,10179904,10184003,11220529,11744560,30471489,1488225,11220000,11744562,11744834,23831874,26433090,30073906,30593824,1094467,1186915,1391170,1422194,10180145,10180419,10180449,10184274,11220563,11744817,22660418,22791218,22791474,22791747,23704896,24352338,25912609,25912643,26433073,27473202,472403,1419040,1422912,1880865,10180146,10180176,10180450,10184514,11220546,11232816,11233107,11743760,11744561,11745072,11752770,11753042,26432784,26433089,27473168,27473184,29946929,30471745,31519760,31634482,33714977,33715489,33715506,472625,10184273,10184545,11220512,11220513,11232835,11233121,11744544,11745073,22647856,22791760,23717186,25912353,25912898,26432800,26432833,26432834,27472912,30470928,30594097,31519777,31519794,31634465,33616672,33617219,33715233]
def decodeStep (_childBudget stream : Nat) : Nat × Nat :=
  let tag:=stream % 4
  let tail:=stream / 4
  if tag < 2 then (tag,tail) else if tag=2 then (2+tail % 4096,tail/4096) else
    let head:=tail % 4
    if head<3 then (anchors[head]?.getD 0,tail/4) else
      (anchors[3+(tail/4) % 256]?.getD 0,tail/1024)
def words0 : Array Nat := #[0x7f0000007f00,0xfeee0000feee,0xfefe0000fefe,0xffea0000ffea,0xffee0000ff00,0xffee0000ffee,0xfffe0000fffe,0x2000200020002,0x8000800080008,0xa000a000a000a,0xe000e000e000e,0x2a002a002a002a,0x80008000800080,0x88008800880088,0x8a008a008a008a,0xa800a800a800a8,0xaa00aa00aa00aa,0xaa00aaaaaaaaaa,0xae00ae00ae00ae,0xcc00cc00cc00cc,0xea00ea00ea00ea,0xee00ee00000000,0xee00ee00ee00ee,0xee00eeeeeeeeee,0xfc00fc00fc00fc,0xfe00fe00fe00fe,0xff008000ff0080,0xff7fff00000000,0x100010001000100,0x200020002000200,0x202020202020202,0x2020202aaaaaaaa]
def words1 : Array Nat := #[0x2020202eeeeeeee,0x2020202fefefefe,0x20a020a020a020a,0x2aa02aa02aa02aa,0x2aa02aaaaaaaaaa,0x300030003000300,0x3000300ff00ff00,0x3000300fffcfffc,0x302030203020302,0x3fc03fc03fc03fc,0x700070007000700,0x800080008000800,0x808080808080808,0x80a080a080a080a,0x888088808880888,0x8aa08aa08aa08aa,0xa000a000a000a00,0xa020a020a020a02,0xa080a080a080a08,0xa0a0a0a00000000,0xa0a0a0a0a0a0a0a,0xa0e0a0e0a0e0a0e,0xa2a0a2a0a2a0a2a,0xa8a0a8a0a8a0a8a,0xaaa0aaa0aaa0aaa,0xace0ace0ace0ace,0xafa0afa0afa0afa,0xb000b000b000b00,0xb0a0b0a0b0a0b0a,0xc0c0c0c0c0c0c0c,0xccc0ccc0ccc0ccc,0xe000e000e000e00]
def words2 : Array Nat := #[0xe0a0e0a0e0a0e0a,0xe0e0e0e00000000,0xe0e0e0e0e0e0e0e,0xe0e0e0eeeeeeeee,0xeee0eee0eee0eee,0xf000f000f000f00,0xf020f020f020f02,0xf080f080f080f08,0xf0a0f0a0f000f00,0xf0a0f0a0f0a0f0a,0xf0c0f0c0f0c0f0c,0xf0e0f0e0f000f00,0xf0e0f0e0f0e0f0e,0xf3c0f3c0f3c0f3c,0xfaa0faa0faa0faa,0xff00ff00ff00ff0,0x1100110011001100,0x1e1e1e1e1e1e1e1e,0x1f001f001f001f00,0x2222222222222222,0x2a002a002a002a00,0x2a0a2a0a2a0a2a0a,0x2a2a2a2a2a2a2a2a,0x2aaa2aaa2aaa2aaa,0x2e2e2e2e2e2e2e2e,0x2f002f002f002f00,0x2f222f222f222f22,0x3030303030303030,0x3300330033003300,0x3322332233223322,0x3c3c3c3c3c3c3c3c,0x3ccc3ccc3ccc3ccc]
def words3 : Array Nat := #[0x3cfc3cfc3cfc3cfc,0x3e3e3e3e3e3e3e3e,0x3f003f003f003f00,0x3f0c3f0c3f0c3f0c,0x3f2a3f2a3f2a3f2a,0x3f3c3f3c3f3c3f3c,0x3fc03fc03fc03fc0,0x4444444444444444,0x44cc44cc44cc44cc,0x4c4c4c4c4c4c4c4c,0x5050505050505050,0x50f050f050f050f0,0x5454545454545454,0x5500550055005500,0x5544554455445544,0x5550555055505550,0x55aa55aa55aa55aa,0x5a5a5a5a5a5a5a5a,0x5f005f005f005f00,0x6666666666666666,0x6a6a6a6a6a6a6a6a,0x6e666e666e666e66,0x6e6e6e6e6e6e6e6e,0x7070707070707070,0x7700770077007700,0x7a7a7a7a7a7a7a7a,0x7c7c7c7c7c7c7c7c,0x7f007f007f007f00,0x7fff7fff00000000,0x8000800080008000,0x8080808080808080,0x8088808880888088]
def words4 : Array Nat := #[0x80aa80aa80aa80aa,0x8282828282828282,0x8800880088008800,0x8808880888088808,0x8880888088808880,0x8888888888888888,0x88888888aaaaaaaa,0x888a888a888a888a,0x88a888a888a888a8,0x88aa88aa88aa88aa,0x88cc88cc88cc88cc,0x88f888f888f888f8,0x8a008a008a008a00,0x8a0a8a0a8a0a8a0a,0x8a888a888a888a88,0x8a8a8a8a8a8a8a8a,0x8aaa8aaa8aaa8aaa,0x8c8c8c8c8c8c8c8c,0x8f008f008f008f00,0x8f888f888f888f88,0x9898989898989898,0x9988998899889988,0x99aa99aa99aa99aa,0x9a9a9a9a9a9a9a9a,0xa000a000a000a000,0xa0a0a0a0a0a0a0a0,0xa0aaa0aaa0aaa0aa,0xa0f0a0f0a0f0a0f0,0xa2a0a2a0a2a0a2a0,0xa2a2a2a2a2a2a2a2,0xa2aaa2aaa2aaa2aa,0xa800a800a800a800]
def words5 : Array Nat := #[0xa888a888a888a888,0xa8a8a8a800000000,0xa8a8a8a8a8a8a8a8,0xa8a8a8a8fcfcfcfc,0xa8aaa8aaa8aaa8aa,0xa8fca8fca8fca8fc,0xaa00aa00aa00aa00,0xaa02aa02aa02aa02,0xaa08aa08aa08aa08,0xaa0aaa0aaa0aaa0a,0xaa22aa22aa22aa22,0xaa2aaa2aaa2aaa2a,0xaa5aaa5aaa5aaa5a,0xaa80aa80aa80aa80,0xaa88aa88aa88aa88,0xaa8aaa8aaa8aaa8a,0xaaa0aaa0aaa0aaa0,0xaaa8aaa8aa00aa00,0xaaa8aaa8aaa8aaa8,0xaaaeaaaeaaaeaaae,0xaaccaaccaaccaacc,0xaaeaaaeaaaeaaaea,0xaaeeaaeeaaeeaaee,0xaafaaafaaafaaafa,0xaafeaafeaafeaafe,0xab00ab00ab00ab00,0xabaaabaaabaaabaa,0xacacacacacacacac,0xae00ae00ae00ae00,0xae0cae0cae0cae0c,0xaeaaaeaaaeaaaeaa,0xaeaeaeaeaeaeaeae]
def words6 : Array Nat := #[0xaeeeaeeeaeeeaeee,0xaf00af00af00af00,0xaf50af50af50af50,0xaf8caf8caf8caf8c,0xafa0afa0afa0afa0,0xafaaafaaafaaafaa,0xafaeafaeafaeafae,0xb0b0b0b0b0b0b0b0,0xbcbcbcbcbcbcbcbc,0xbebebebebebebebe,0xbf00bf00bf00bf00,0xbfaabfaabfaabfaa,0xc000c000c000c000,0xc040c040c040c040,0xc0c0c0c0c0c0c0c0,0xc0c8c0c8c0c8c0c8,0xc0ccc0ccc0ccc0cc,0xc0eac0eac0eac0ea,0xc0f0c0f0c0f0c0f0,0xc4c4c4c4c4c4c4c4,0xcc00cc00cc00cc00,0xcc0ccc0ccc0ccc0c,0xcc44cc44cc44cc44,0xccc0ccc0ccc0ccc0,0xccc8ccc8ccc8ccc8,0xcceecceecceeccee,0xcececececececece,0xd0d0d0d0d0d0d0d0,0xdcdcdcdcdcdcdcdc,0xdd00dd00dd00dd00,0xe0e0e0e000000000,0xe0e0e0e0e0e0e0e0]
def words7 : Array Nat := #[0xe0e0e0e0eeeeeeee,0xe6e6e6e6e6e6e6e6,0xea00ea00ea00ea00,0xeaaaeaaaeaaaeaaa,0xeac0eac0eac0eac0,0xeaeaeaea00000000,0xeaeaeaeaeaeaeaea,0xeaeeeaee00000000,0xeaeeeaeeeaeeeaee,0xeaffeaff00000000,0xecececececececec,0xee00ee0000000000,0xee00ee00ee00ee00,0xee00ee00eeeeeeee,0xee0eee0eee0eee0e,0xee22ee22ee22ee22,0xee66ee66ee66ee66,0xeeaaeeaaeeaaeeaa,0xeeaeeeaeeeaeeeae,0xeecceecceecceecc,0xeee0eee0eee0eee0,0xeeeaeeea00000000,0xeeeaeeeaeeeaeeea,0xeeeeeeee00000000,0xeeeeeeeeeeeeeeee,0xeeefeeef00000000,0xeefeeefe00000000,0xeefeeefeeefeeefe,0xeeffeeff00000000,0xef00ef000f000f00,0xef00ef00ef00ef00,0xefaaefaaefaaefaa]
def words8 : Array Nat := #[0xefeeefee00000000,0xefeeefee0f000f00,0xefeeefeeefeeefee,0xefefefef00000000,0xefffefff00000000,0xf000f000f000f000,0xf030f030f030f030,0xf050f050f050f050,0xf070f070f070f070,0xf080f080f080f080,0xf0a0f0a0f0a0f0a0,0xf0c0f0c0f0c0f0c0,0xf0e0f0e0f0e0f0e0,0xf0f8f0f8f0f8f0f8,0xf0faf0faf0faf0fa,0xf0fcf0fcf0fcf0fc,0xf2f2f2f2f2f2f2f2,0xf300f300f300f300,0xf3f0f3f0f3f0f3f0,0xf500f500f500f500,0xf6f6f6f6f6f6f6f6,0xf700f700f700f700,0xf7f0f7f0f7f0f7f0,0xf8f0f8f0f8f0f8f0,0xf8f8f8f800000000,0xf8f8f8f8f8f8f8f8,0xfa00fa00fa00fa00,0xfaf0faf0faf0faf0,0xfafafafa00000000,0xfafafafafafafafa,0xfafffaff00000000,0xfc00fc00fc00fc00]
def words9 : Array Nat := #[0xfcccfcccfcccfccc,0xfcfcfcfc00000000,0xfcfcfcfcfcfcfcfc,0xfcfffcff00000000,0xfdfdfdfd00000000,0xfe00fe00fe00fe00,0xfeaafeaafeaafeaa,0xfeeefeee00000000,0xfeeefeeefeeefeee,0xfefefefe00000000,0xfefefefe02020202,0xfefefefef0f0f0f0,0xfefefefefefefefe,0xfefffeff00000000,0xff008000ff008000,0xff02ff02ff02ff02,0xff08ff08ff08ff08,0xff0aff0aff0aff0a,0xff0eff0eff0eff0e,0xff2aff2aff2aff2a,0xff70ff70ff70ff70,0xff80ff80ff80ff80,0xff88ff88ff88ff88,0xff8aff8aff8aff8a,0xffa8ffa8ffa8ffa8,0xffaaffaaffaaffaa,0xffaeffaeffaeffae,0xffc0ffc0ffc0ffc0,0xffccffccffccffcc,0xffeaffea00000000,0xffeaffeaffeaffea,0xffeeffee00000000]
def words10 : Array Nat := #[0xffeeffee11001100,0xffeeffeeff00ff00,0xffeeffeeffeeffee,0xffefffef00000000,0xfff0fff0fff0fff0,0xfffafffa00000000,0xfffafffafffafffa,0xfffcfffc00000000,0xfffcfffcfffcfffc,0xfffefffe00000000,0xfffefffefffefffe,0xffff0002ffff0002,0xffff0080ffff0080,0xffff0100ffff0100,0xffff8000ffff8000,0xffff8080ffff8080,0xffffff8000000000,0xffffff80ffffff80]
def wordBlocks : Array (Array Nat) := #[words0,words1,words2,words3,words4,words5,words6,words7,words8,words9,words10]
def extraWord (i : Nat) : W := repeated (((wordBlocks[i/32]?).getD #[])[i % 32]?.getD 0)
def extras : Nat → Nat → List W
  | 0,_=>[]
  | k+1,n=>extraWord (n % 512) :: extras k (n / 512)
def decodeState (n : Nat) : List W × Nat :=
  let used:=(n/8) % 64
  let base:=raw.zipIdx.filterMap fun (w,i)=>if used.testBit i then some w else none
  (canon (base++extras ((n/512) % 8) (n/4096)),n % 8)
def m0b0 : Array Nat := #[0x1fe]
def m0 : Array (Array Nat) := #[m0b0]
def m1b0 : Array Nat := #[0x103fc,0x343fc,0x453fc,0x853fc,0xa63fc,0xf83fc,0x1393fc]
def m1 : Array (Array Nat) := #[m1b0]
def m2b0 : Array Nat := #[0x20095fa,0x68095fa,0x288095fa,0x200d5fa,0x10a0d5fa,0x26105fa,0x68105fa,0x7a105fa,0x8a105fa,0xce105fa,0xda105fa,0x10a105fa,0x14c105fa,0x19c105fa,0x1a8105fa,0x1ac105fa,0x1b2105fa,0x1f0105fa,0x244105fa,0x272105fa,0x278105fa,0x1f0165fa,0x681e5fa,0x2441e5fa,0x8a255fa,0x244255fa,0x682c5fa,0x10a2c5fa,0x68305fa,0x8a305fa,0x14c305fa,0x7a345fa]
def m2b1 : Array Nat := #[0x8a345fa,0xa6345fa,0xb6345fa,0xb8345fa,0xd4345fa,0xda345fa,0x10a345fa,0x132345fa,0x14c345fa,0x19c345fa,0x1a6345fa,0x1a8345fa,0x1b4345fa,0x1f0345fa,0x20a345fa,0x226345fa,0x23a345fa,0x244345fa,0x262345fa,0x272345fa,0x278345fa,0x288345fa,0x20a385fa,0x1f0425fa,0xb8455fa,0x10a455fa,0x132455fa,0x134455fa,0x14c455fa,0x18a455fa,0x1f0455fa,0x20a455fa]
def m2b2 : Array Nat := #[0x23a455fa,0x272455fa,0x288455fa,0x272495fa,0x19c565fa,0x19c625fa,0x10a7e5fa,0x10a825fa,0x14c825fa,0x132855fa,0x14c855fa,0x1f0855fa,0x20a855fa,0x232855fa,0x23a855fa,0x26c855fa,0x272855fa,0x288855fa,0x244a25fa,0x1a8a65fa,0x1e6a65fa,0x1f0a65fa,0x244a65fa,0x272a65fa,0x278a65fa,0x278ae5fa,0x1f0ec5fa,0x23af85fa,0x258f85fa,0x272f85fa,0x284f85fa,0x288f85fa]
def m2b3 : Array Nat := #[0x279395fa,0x285395fa,0x93fb,0xd3fb,0xda105bb,0xda105f3,0x14c105f3,0x103fb,0x272105bb,0x163fb,0x1e3fb,0x253fb,0x2c3fb,0x303fb,0xd4345db,0x132345f3,0x343fb,0x23a345db,0x383fb,0x423fb,0x20a455bb,0x453fb,0x288455db,0x493fb,0x563fb,0x623fb,0x7e3fb,0x823fb,0x853fb,0x1f0855eb,0x893fb,0x8f3fb]
def m2b4 : Array Nat := #[0xa23fb,0xa63fb,0x272a65bb,0x272a65f3,0xa93fb,0xae3fb,0xb63fb,0xbf3fb,0xc13fb,0xc53fb,0xe63fb,0xec3fb,0xf13fb,0x1f0f74fb,0xf83fb,0x12c3fb,0x1313fb,0x1363fb,0x1393fb,0x1423fb,0x1f0855e4,0xf72fc]
def m2 : Array (Array Nat) := #[m2b0,m2b1,m2b2,m2b3,m2b4]
def m3b0 : Array Nat := #[0x19c0b5f9,0xee0d5f9,0x41426107b9,0x7c105f9,0xd2105f9,0x338da107b9,0x338da107f1,0x3394c107f1,0x19a105f9,0x19c105f9,0x4e59c107b9,0x19e105f9,0x1a0105f9,0x1a2105f9,0x1a6105f9,0x415a8107b9,0x19c145f9,0x3e1ee156f9,0x48a421f6f9,0x48a42266f9,0x10a2b5f9,0x214a62c7f1,0xa62c5f9,0xac2c5f9,0x214ee2c7d9,0xee2c5f9,0xf02c5f9,0xfc2c5f9,0x2750a2c7f1,0x10a2c5f9,0x4650a2c7d9,0x3e10a2c7e9]
def m3b1 : Array Nat := #[0x1f02c5f9,0x1122d5f9,0xd0305f9,0x10a305f9,0x19ca6347f1,0x214a6347f1,0x34ca6347e9,0xa6345f9,0x440a6347d9,0xac345f9,0xba345f9,0xd0345f9,0x264d2347f1,0xd2345f9,0x214d4347f1,0x244d4347f1,0x368d4347d9,0x214ee347d9,0xee345f9,0xf0345f9,0x264fc347f1,0xfc345f9,0x2650a347f1,0x34d0a347e9,0x10a345f9,0x4650a347d9,0x3690a347e9,0x3e10a347f1,0x112345f9,0x114345f9,0x11e345f9,0x122345f9]
def m3b2 : Array Nat := #[0x3a932347f1,0x1b2345f9,0x1b6345f9,0x1b8345f9,0x1d4345f9,0x278365f9,0xb8385f9,0x19c385f9,0x1a8385f9,0x240385f9,0x278385f9,0x3e1ee416f9,0x10a425f9,0xac455f9,0xfe455f9,0x4150a457b9,0x10a455f9,0x5110a457d9,0x112455f9,0x11c455f9,0x11e455f9,0x126455f9,0x33932457d9,0x10a475f9,0x10a495f9,0x4e59c497d9,0x214fc567f1,0x338fc567f1,0x10a565f9,0x3390a567f1,0x19c565f9,0x4899c567d9]
def m3b3 : Array Nat := #[0x1a6565f9,0x1a8565f9,0x1cc565f9,0x1f0565f9,0x244565f9,0x276565f9,0x278565f9,0x19c575f9,0x1a8575f9,0x10a625f9,0x1cc625f9,0x10a7b5f9,0x10a7e5f9,0x53d0a7e779,0x4650a7e7d9,0x3e10a7e7e9,0x11e7e5f9,0x1cc7e5f9,0x1f07e5f9,0x10a7f5f9,0x1347f5f9,0x19c805f9,0x116855f9,0x29932857f1,0x132855f9,0x46532857d9,0x3e132857f1,0x134855f9,0x136855f9,0x13a855f9,0x51160857f1,0x18e855f9]
def m3b4 : Array Nat := #[0x1be855f9,0x20a855f9,0x5120a857b9,0x5120a857d9,0x20c855f9,0x210855f9,0x212855f9,0x214855f9,0x21a855f9,0x21c855f9,0x220855f9,0x222855f9,0x224855f9,0x22a855f9,0x22c855f9,0x22e855f9,0x46630856f9,0x232855f9,0x236855f9,0x268855f9,0x288855f9,0x465f0857e9,0x288875f9,0x1a4895f9,0x20a895f9,0x224895f9,0x288895f9,0x20a8f5f9,0x23a8f5f9,0x2888f5f9,0x20a905f9,0x48a42a16f9]
def m3b5 : Array Nat := #[0x415a8a67b9,0x1aaa95f9,0x216ae5f9,0x21eb65f9,0x244e65f9,0x3e1eeeb6f9,0x4adf0f76f9,0x505f0f76f9,0x1f00257a,0x2580257a,0x1f00557a,0x2720557a,0x2840557a,0x73fa,0x83fa,0xde095f2,0x160095f2,0x20e095da,0x226095ba,0x93fa,0x262095ba,0x21c095da,0xa3fa,0xb3fa,0xc3fa,0xf00d5ba,0x3e10a0d7e2,0x1540d5f2,0xd3fa,0x26c0d5ba,0x1b20d5ea,0xe3fa]
def m3b6 : Array Nat := #[0xf3fa,0x30105ba,0x298da107b2,0xda105ba,0xda105f2,0x4e4da107b2,0xdc105f2,0xe0105ba,0xe0105f2,0xe4105ba,0x3e10a107e2,0x14c105f2,0x4e54c107b2,0x152105f2,0x15c105f2,0x4899c107ca,0x1ba105ba,0x1ee104fa,0x23e105ba,0x242104fa,0x103fa,0x262105ba,0x26c105ba,0x272105ba,0x16c105f2,0x123fa,0x143fa,0x1ee154fa,0xa0165ba,0xb8165ba,0x3e10a167e2,0x1ee164fa]
def m3b7 : Array Nat := #[0x20a165ba,0x163fa,0x272165ba,0x284165ba,0x1f0195ba,0x258195ba,0x193fa,0x1c3fa,0x1d3fa,0xd81e5f2,0x1441e5f2,0x4899c1e7ca,0x1a61e5ea,0x2421e4fa,0x2481e4fa,0x1e3fa,0x2201e5da,0x2421f4fa,0x223fa,0x233fa,0x4899c257ca,0x1a0255ea,0x23e255ba,0x242254fa,0x246254fa,0x253fa,0x224255da,0x242264fa,0x283fa,0x2a3fa,0x2b3fa,0xee2c5da]
def m3b8 : Array Nat := #[0x3e10a2c7e2,0x13a2c5f2,0x2c3fa,0x2322c5da,0x1b42c5ea,0x2d3fa,0x2e3fa,0x2f3fa,0xd6305da,0x134305f2,0x226305ba,0x303fa,0x262305ba,0x236305da,0x18a305f2,0x313fa,0x323fa,0x238334fa,0x94345da,0x264d4347d2,0xd4345da,0x474d4347d2,0xd6345da,0xd8345f2,0xde345f2,0xe2345da,0xe2345f2,0xee345da,0x3e10a347e2,0x132345f2,0x47532347d2,0x134345f2]
def m3b9 : Array Nat := #[0x13a345f2,0x144345f2,0x160345f2,0x4899c347ca,0x1b6345da,0x1ee344fa,0x20e345da,0x216345da,0x238344fa,0x242344fa,0x248344fa,0x343fa,0x21c345da,0x220345da,0x232345da,0x236345da,0x47638346da,0x23a345da,0x17e345f2,0x18a345f2,0x353fa,0x363fa,0x373fa,0xda385f2,0x130385f2,0x132385f2,0x14c385f2,0x383fa,0x393fa,0x3a3fa,0x3b3fa,0x3c3fa]
def m3b10 : Array Nat := #[0x3f3fa,0x403fa,0x1ee414fa,0x8a425da,0x3e10a427e2,0x1ee424fa,0x20a425da,0x423fa,0x23a425da,0x258425da,0x443fa,0x9e455ba,0x9e455da,0x3e10a457e2,0x47532457d2,0x136455da,0x1be455da,0x1ee454fa,0x20a455ba,0x5120a4579a,0x222455ba,0x234455ba,0x238454fa,0x23c454fa,0x453fa,0x262455ba,0x224455da,0x236455da,0x288455da,0x463fa,0x473fa,0x19c495da]
def m3b11 : Array Nat := #[0x493fa,0x23a495da,0x288495da,0x28c495da,0x1f04c5da,0x4c3fa,0x2724c5da,0x2844c5da,0x4e3fa,0x20a4f5ba,0x20a4f5da,0x4f3fa,0x2884f5ba,0x2884f5da,0x523fa,0x543fa,0x553fa,0xfc565f2,0x10a565f2,0x4899c567ca,0x563fa,0x573fa,0x583fa,0x593fa,0x5a3fa,0x19c5e5da,0x4899c5e7ca,0x5e3fa,0x2445e5da,0x198625ba,0x4899c627ca,0x1a8625ba]
def m3b12 : Array Nat := #[0x623fa,0x633fa,0x643fa,0x7b3fa,0x7d3fa,0x3e10a7e7e2,0x7e3fa,0x29e7e57a,0x2327e5da,0x7f3fa,0x803fa,0x3e10a827e2,0x823fa,0x26c825ba,0x1e6825ea,0x833fa,0x843fa,0x47532857d2,0x13a855f2,0x3e14c857e2,0x154855f2,0x160855f2,0x1ee854fa,0x230854fa,0x238854fa,0x853fa,0x29e8557a,0x1b2855ea,0x1b4855ea,0x1d4855ea,0x1e6855ea,0x3e1ee856ea]
def m3b13 : Array Nat := #[0x1f0855ea,0x3e1be857e2,0x3e1d8857e2,0x415f0857e2,0x465f0857e2,0x475f0857e2,0x4b1f0857e2,0x4d9f0857e2,0x4e5f0857e2,0x509f0857e2,0x511f0857e2,0x873fa,0x883fa,0x14c895f2,0x893fa,0x1f0895f2,0x8b3fa,0x8c3fa,0x8d3fa,0x8e3fa,0x8f3fa,0x1f08f5f2,0x903fa,0x923fa,0x933fa,0x9f3fa,0xa03fa,0x242a14fa,0x14ca25f2,0x242a24fa,0xa23fa,0x1f0a25f2]
def m3b14 : Array Nat := #[0x258a25f2,0xa43fa,0xa53fa,0x1baa65ba,0x1eea64fa,0x23ea65ba,0x242a64fa,0xa63fa,0x262a65ba,0x26ca65ba,0x272a65ba,0x18aa65f2,0x1e2a65f2,0x272a65f2,0xa73fa,0xa83fa,0xa93fa,0x272a95f2,0xab3fa,0xad3fa,0xae3fa,0x1f0ae5f2,0x272ae5f2,0x284ae5f2,0xaf3fa,0xb23fa,0x244b25f2,0x278b25f2,0x290b25f2,0xb33fa,0xb43fa,0xb53fa]
def m3b15 : Array Nat := #[0xb63fa,0xb83fa,0xb93fa,0xba3fa,0xbb3fa,0xbc3fa,0xbd3fa,0xbe3fa,0xbf3fa,0xc03fa,0xc13fa,0x272c15ba,0xc33fa,0xc43fa,0xc53fa,0xc63fa,0xca3fa,0xcb3fa,0xe23fa,0xe33fa,0xe43fa,0x1cce54fa,0xe63fa,0xe83fa,0x1eeeb4fa,0x1eeec4fa,0xec3fa,0x272ec5ba,0x284ec5ba,0xee3fa,0xef3fa,0xf13fa]
def m3b16 : Array Nat := #[0xf23fa,0xf43fa,0xf63fa,0x1f0f74fa,0x23af74fa,0x256f74fa,0x258f74fa,0x272f74fa,0x282f74fa,0x284f74fa,0x288f74fa,0x1f8f84fa,0x206f84fa,0x24af85ba,0x252f84fa,0x27ef84fa,0xf83fa,0xfb3fa,0xfe3fa,0xff3fa,0x1023fa,0x259255ba,0x1253fa,0x1263fa,0x1283fa,0x259294fa,0x12c3fa,0x12f3fa,0x1303fa,0x1313fa,0x1323fa,0x1333fa]
def m3b17 : Array Nat := #[0x1353fa,0x1363fa,0x1373fa,0x1383fa,0x27f394fa,0x1393fa,0x13a3fa,0x13e3fa,0x2853f4fa,0x1423fa,0x14a3fa,0x289315ba,0x2890e5da,0x245105da,0x245125da,0x237b,0x537b,0x193bb,0x4c3db,0x4f3bb,0x4f3db,0x19c5e5cb,0x5e3db,0x2445e5cb,0x3e1ee856e3,0x1f0855e3,0xb23f3,0xe52fb,0xf72fb,0xfc2fb,0x1032fb,0x1253bb]
def m3b18 : Array Nat := #[0x1292fb,0x13f2fb,0x14f37b]
def m3 : Array (Array Nat) := #[m3b0,m3b1,m3b2,m3b3,m3b4,m3b5,m3b6,m3b7,m3b8,m3b9,m3b10,m3b11,m3b12,m3b13,m3b14,m3b15,m3b16,m3b17,m3b18]
def m4b0 : Array Nat := #[0x29e00579,0x338bc107c9,0x1ee114f9,0x4899c147c9,0x7c3dd0a158e1,0x1ee174f9,0x29e1a579,0x484d81f6f1,0x914859c1f8c9,0x242244f9,0x914859c268c9,0x4863e266b9,0x214e62c7e1,0xe62c5e9,0x3e0e62c7e1,0x7c214ee2c9c1,0x3e0ee2c7e1,0x3e0fc2c7e1,0x3850a2c7e1,0x7c3dd0a2c8e1,0x3e10a2c7e1,0x8cbe10a2c9c1,0x29e2c579,0x214e6347e1,0xe6345f1,0x7c214ee349c1,0x264ee347d1,0xee345d9,0xf2345d9,0x3a8fc347e1,0x3dd0a346f1,0x3a90a347e1]
def m4b1 : Array Nat := #[0x8cbe10a349c1,0x53d3234771,0x29e34579,0x7c3dd0a418e1,0x214e6427e1,0x7c214ee429c1,0x8cbe10a429c1,0x4adee426d9,0x1ee434f9,0x214e6457e1,0x3e10a477e1,0x1ee4b4f9,0x10a4f5b9,0x10a4f5d9,0x338bc567c9,0xbc565d9,0x488bc567c9,0x214d2567e1,0x264d2567e1,0xec565f1,0x91338fc569c1,0x464fc567d1,0x913390a569c1,0x10a565f1,0x53d0a56771,0x4650a567d1,0x112565f1,0x11e565f1,0x9133944569c1,0x144565f1,0x914859c568c9,0x4899c567c9]
def m4b2 : Array Nat := #[0x1ca564f9,0x1ee564f9,0x242564f9,0x232565d9,0x489cc567c9,0x17e565f1,0x53d9c56771,0x4899c577c9,0x338fc5e7c9,0xfc5e5d9,0x488fc5e7c9,0x339025e7c9,0x1025e5d9,0x489025e7c9,0x3390a5e7c9,0x10a5e5e9,0x11e5e5e9,0x339445e7c9,0x3394c5e7c9,0x17e5e5d9,0x339925e7c9,0x1925e5d9,0x489925e7c9,0x3999c5e7c9,0x4e59c5e7c9,0x1cc5e5d9,0x489cc5e7c9,0xfc745f1,0x743f9,0x19c745f1,0x1cc745f1,0x214fc767e1]
def m4b3 : Array Nat := #[0x10a765e9,0x3e10a767e1,0x763f9,0x3e10a7b7e1,0x7c3dd0a7e8e1,0x3e10a7e7e1,0xa7be10a7e961,0x8cbe10a7e9c1,0x1ca7e4f9,0x1ee7e4f9,0x466307e6d9,0x2327e5d9,0x53e327e759,0x489cc7e7c9,0x475d47e7c9,0x3e10a7f7e1,0x4899c807c9,0x1cc805f1,0x4899c817c9,0x813f9,0x3e116857e1,0x44132857d1,0x8eba932859c1,0x138855f1,0x34d3a857e1,0x13a855f1,0x13c855f1,0x35d60857e1,0x29e85579,0x53e3285759,0x1c2855e9,0x53df085769]
def m4b4 : Array Nat := #[0x7c3ddbc858e1,0x8cbe1be859c1,0x3e1c2857e1,0x489cc857e1,0x7c3ddd6858e1,0x8cbe1ee858e1,0x95be1ee858e1,0xa0be1ee858e1,0x435f0857e1,0x451f0857e1,0x8cc61f0858e1,0x465f0857e1,0x16e885f1,0x138895f1,0x13a895f1,0x13a8f5f1,0x29e8f579,0x242a34f9,0xc83f9,0x29ee6579,0x505eeec6b9,0x1eeed4f9,0x1faf74f9,0x202f74f9,0x29ef8579,0x29f2e579,0x2a34f579,0x137a,0x320253a,0x3e10a02762,0x1ee0247a,0x24a0253a]
def m4b5 : Array Nat := #[0x2520247a,0x237a,0x337a,0x1ee0447a,0x980555a,0x3e10a05762,0x1ee0547a,0x2180555a,0x27e0547a,0x537a,0x637a,0x2181659a,0x3e10a197a2,0x1ee194ba,0x252194ba,0x193ba,0x202fa,0x212fa,0x4859c256ca,0x272fa,0x19c285ca,0x293ba,0x3dd0a426e2,0x24a4259a,0x238484da,0x1b0495ca,0x238494da,0x28a494da,0x1ee4b4da,0x3e10a4c7c2,0x1ee4c4da,0x27e4c4da]
def m4b6 : Array Nat := #[0x4c3da,0x4d3da,0x4f3ba,0x4f3da,0x513da,0x29e56572,0x4859c5e6ca,0x19c5e5ca,0x2425e4da,0x5e3da,0x48a425e6ca,0x2445e5ca,0x5f3ea,0x19c605ca,0x244615ca,0x244655ca,0x663ba,0x743f2,0x10a765e2,0x7c2fa,0x489cc7e7c2,0x4b1be857c2,0x1c2855e2,0x3ddd8856e2,0x1e0855e2,0x1e8855e2,0x1ec855e2,0x3e1ee856e2,0x4b1ee856e2,0x3f1f0856e2,0x40df0856e2,0x431f0857c2]
def m4b7 : Array Nat := #[0x461f0856e2,0x471f0856e2,0x495f0857a2,0x4a5f0856e2,0x4fdf0856e2,0x1f0855e2,0x53df085762,0x1ee864f2,0x1e6895e2,0x1ee8f4f2,0x2068f4f2,0x1d48f5e2,0x1f0945e2,0x1f0955e2,0x963f2,0x973f2,0x24aa25b2,0x220a25d2,0xac3f2,0x1eeae4f2,0x218ae5d2,0x27eae4f2,0x1b2ae5e2,0x242b14f2,0x23eb25b2,0x242b24f2,0x28eb24f2,0xb23f2,0xc23ba,0xe52fa,0xe72fa,0xe92fa]
def m4b8 : Array Nat := #[0xf52fa,0x24af74ba,0xf72fa,0xf92fa,0xfa2fa,0xfc2fa,0x1002fa,0x1032fa,0x1042fa,0x253254ba,0x1253ba,0x1272fa,0x1292fa,0x12a2fa,0x12d2fa,0x13d2fa,0x13f2fa,0x1402fa,0x1432fa,0x1492fa,0x14b37a,0x14c37a,0x14d37a,0x14e37a,0x14f37a,0x243104da,0x249104da,0x29f1955a]
def m4 : Array (Array Nat) := #[m4b0,m4b1,m4b2,m4b3,m4b4,m4b5,m4b6,m4b7,m4b8]
def m5b0 : Array Nat := #[0x3dd0a176e1,0x29e1b479,0x90b38d81f8c1,0x90c7d9c26889,0x53df02c761,0x53dd434761,0x7ba14ee428c1,0x8cbdd0a428c1,0x95bdd0a428c1,0x3dd0a436e1,0x338f4567c1,0x489ca566c9,0xa7c899c56941,0x53e3256751,0x53d9c5e749,0x29e5e559,0x53e445e749,0x488fc747c1,0x244745c9,0x4899c747c1,0x489cc747c1,0x10a755e1,0x464fc767c1,0x3dd0a766e1,0x10a765e1,0x53d0a76761,0x4650a767c1,0x232765c9,0x465f0767c1,0x489ca7e6c9,0x91399ca7e8c1,0x91485cc7e8c1]
def m5b1 : Array Nat := #[0x489cc7e7c1,0xa7c89cc7e941,0x489cc817c1,0x3ddc0856e1,0xa0bddd8858a1,0xa7be1ee85861,0x53df085761,0xa7c65f085941,0x29ee5479,0x29ef7479,0x2a32e539,0x2a14f479,0x53e3318659,0x29f19559,0x53e44e6749,0x53e3aea749,0x495be85782,0x495ee856a2,0x53e44e6742]
def m5 : Array (Array Nat) := #[m5b0,m5b1]
def m6b0 : Array Nat := #[0x2a12e439,0x53e44e5649,0xa7c89cce5841,0xa7c8a42e6841,0x53e44e6741]
def m6 : Array (Array Nat) := #[m6b0]
def m7 : Array (Array Nat) := #[]
def mLevels : Array (Array (Array Nat)) := #[m0,m1,m2,m3,m4,m5,m6,m7]
def h0b0 : Array Nat := #[0x5500550288032004807200550268036002806a021802a00880560055024803e000806201f802e006804e01e8026007804a]
def h0 : Array (Array Nat) := #[h0b0]
def h1b0 : Array Nat := #[0x15401541e6030807e055801541e2031807a05481b202b80aa04e801541ca03c8122270896225e899206780de024810e06680da025810a0000555507289c236c818605b80020138ca231d8932253818205a80060128c9a31b893625281222648c1a,0x15401544fa0c080ea114801544e20d280b2102849a0cc82ea0f6801544ca0de80920f084820d883aa2a68a522998a6a10e833e0c683920000555512c846a00682a23608cd624c8a3a1208a9a35584220fc821209c8cb22fd89f228883aa29a8ba6,0x1540015463204085ea25c8ae22c4898a0055188854203285aa182838a0c2857a0055186854a03085a2180838e0c0857217483560d3855a0000555517a8ae230a86322c48dc2170859209082c23388bde2828a4216e858a09282ba3368bd62848a3a,0x5500551e6855a052872200551e2857604486fa1d683ea0e686e200551e0857e04286f21d483ee0e486da1c283b60eb8bba29d8bc229b8de2000055551da868a01886aa3668b6a2528b8a1ce86720a286923408b522888b720ed8a762a383ae29b8a86,0x154015484616881621f380154842169815a1f2881210684121cb80015482a17d812230c8aee31289921ff84660f086f61fe845e0f186f20000555517d8aee2c187e614982d21b18d322b18a3a2e387e214782d61b08d2a2af8a3e2e2812226489aa,0x55005523a85d20708822000d3a000dfa5555234826a07e88723728a1a2768d0a228823a14a87c235a8a022b28c1200552308606068880222484aa110875e1218a862a7801548ba183819a1fe888a12b843a1d5848e2a38aa612384861c28a9e2ee8aa62f08de2,0x1555401541ca26a89c20055247864a011886a3738b2a2518c8a241861a07c88520055246864e00f88623728b2e24f8c82240861e07a884a23d84f213a87a6005518f8b062c7863e072882a2708c322c78c4a22f850e132878622e85061338782]
def h1 : Array (Array Nat) := #[h1b0]
def h2b0 : Array Nat := #[0x1540155dddc0155dddddddc0155ddc0bc8fc0bc0bddddddddc00015555c0bc1bdddc0bc0bc1bc1bc0bd0fa4269dddc17c17c0bc0bdc0bc0bc00015555c0bc1bd3fa702f06f777705f05f02f02f702f02f4d59c0bc0bd1a6,0x1540155dddc0155dddddddc0155ddddddc0bc8fc0bc0bddddc00015555ddc0bc0bc1bc1bc0bd0e242c9c0bc1bddddc17c47c0bc0bdc0bc0bc00015555c0bc1bdc0bc1bdc22777711f11f02f02f702f02f6cc9c0bc0bd90a,0x155540155c0bc0bc0155c0bc0bdddc0bc1bc0bc1bc0155dddc1bc17c0bc47ddddddddc0155ddc1bc0bc0bc1bc1bd06a4209dddddddddddc00015555c1bc53f3de706f14fd029c1bc53f422777721f21f06f06f706f06f,0x1540155dddc0155dddddddc0155ddc0bc8fc0bc0bddddddddc00015555c0bc1bddddc1bc1bc0bc0bdddc0bc0bc17c17c0bd1d24649c0bc0bc00015555c0bc1bd412777706f06f02f02f702f05f702f02f4cf9c0bc0bd0ce,0x1540155dddc0155dddddddc0155ddddddddddc17c17c17c17d1720000555577705f32f06f05f05f46e915a777706f00680bcdbdc17c17dc17c17c00015555c17c2bddddccc231e817c17dc17c17e5ea705f05f9789c17c17e522,0x15540155dddf37c032005577705f32f05f05f7777005577705f32f05f05f7777777700005555705f0af777706f19f02f27f705f05f777705f05f05f02f05f02f510933e00005555705f0af777711f3bf05f05f777705f05f05f05f05f05f5129346705f05f777705f05f02f02f05f05f05f05f54690d643391a2,0x55005577770055777777770055577702f23f02f02f77702f23f02f02f777700005555777702f02f06f06f02f02f4fe9386702f06f777705f05480bc0bdc0bc0bc00015555c0bc1bddddc0bc0bc1bc1bc0bc0bdc226e49dddc61a11f02f02f702f02f777702f02f02f02f02f02f02f02f762990a46990ca,0x1540155dddc0155ddddddc0bedfc1bc0bc0155ddc0bc8fc0bc0bddddddddc00015555dddc1bc1bc0bc0bdc0bc1bdc0bc0da777702f02f02f02f00005555702f06f777706f06f02f02f77773bf11f02f02f702f02f777702f02f02f02f02f02f02f02f76a997247b9052,0x550005577723f02f02f23f005577777777005577702f23f02f02f7777777700005555702f06f702f06f777705f04880bc0bddddc0bc0bc0bc0bc00015555c0bc1bddddc1bc1bc0bc0bddddcefc47c0bc0bdc0bc0bdc0bc0be1c2,0x1540155dddc0155dddddddc0155ddc17ccbc17c17dddddddc17c17c17c17c00015555dddc2bc0bc17c0bddddc1bc9fc0bc9fdc17c17dc17c17c00015555c17c2bddddc67c67c17c17ddddc17c17c17c17dc17c17dc17c17ddc6,0x155540155dddc0bc8fc8fc0bc0155dddc17ccbccbccbddddc00015555dc0bc8fc1bc0bd27a48c9dddc1bc0bc0bc0bddddc17c17c17c17c00015555c8fc0bddddc1bc0bc0bc0bddddc17c17c0bc0bdc1bc1bc00015555c0bc1bddddc1bc1bc0bc0bddddc17c17c0bc0bdc0bc0bdc0bc0be216,0x5500557777005577777777005577705f32f05f05f777777705f05f05f05f4bc800015555dddc17ccbc1bc17c0bc17d4124b79dddc1bc06602f36f705f05f705f05f00005555705f0af77773368c6a05f05f777705f05f05f05f05f05f9a2a5ea705f05f777705f05f02f02f05f05f05f05fa14a52243391a2,0x5500557777005577777777000055557702f23f06f02f4c89232777706f02f02f02f777705f05f05f05f00005555723f02f4929dddc1bc0bc0bc0bddddc17c17c17c17c00015555c0bc1beaf2777706f06f02f02f777705f05f02f02f,0x1540155dddc0155ddddddd7bc2bc1bc0bd36a00005555777719f36f27f36f70af05f702f02f005577703c807a02480aa77777777777719f27f36f36f00005555703c8dee777721f4ff11f3bf77774ff21f3bf11f777704e80c202f02f2c7887c00211fa23a57644a9142702a8c26,0x5550055777700d816a0005577705f32f0af05f777700005555732f05f777706f01380bcdbdc17c17c0155ddc17ccbc17c17ddddddddddddc17c0bc17c17c00015555c17c2bddddc87d3fc17c17ddddc17c17c17c17dc17c17ecda705f05f,0x1540155dddc00155dddc2bc17ddddc00015555dddc2bc17c17c17ddddc1bc17c0bc0c2702f02f005577705f32f05f05f7777777705f05f777705f05f05f05f00005555705f0af777721f3c9817c17dddc0bc0bc17c17c17d09e4649c17c17ed0a705f05f,0x1540155dddc00015555dddc2bc17c17c17ddddc1bc17c0bc10e0005577770af05f7777702f02f005577705f32f05f05f7777777705f05f05f05f777705f05f00005555705f0af77773d493fc17c17dc17c17eb8e77702f02f05f05f05f43f91d2705f05f,0x1540155dddc003ef00139a555577770af02f05f05f777706f05f02f19f005577777777705f05f0055577705f27f05f05f7777705f05f77705f05f05f05f4bc800015555c17c2bddddc53c53c17c17dc17c17efda777705f05f05f05f705f05f,0x55001a7c004f295555dddc0bc1bc1bc0bc0bc1bd21a4ec80155ddddc0bc0bc0155ddddc17c2bdddc0bd7bc2bc1bd36a005577706f02f06f06f777706f02f02f02f7777777700005555706f5ef777706f06f02f02f21f5ef06f06fc69afc640e9202777721f4ff06f06f77770af0af06f06f706f06f,0x5555000055550055777706f02f02f06f777706f02f02f06f005577770af05f05f05f77770af05f05f05f77770055702f06f4989dc0bc0bc1bc1bd27a4c89dddddddc00015555dddc53c53c1bc1bddddc2bc2bc1bc1bdc1bc1beb3a,0x55550055705f05f0055777706f02f05f19f77770055705f0af77705f05f0af0af7777005577770af05f02f02f0af0af4a493527770af05f0af0af777777770000555577770af0af02f02f17f17f0af0afcf6b2c643391a270af17f777721f4ff0af0af77770af0af0af0af0af0afd09aba670af0af,0x15540155dddc9fc67c003ef0014ea555577705f27f0af05f05f55294a277770af05f27f19f0055777705f32f7777705f05f0055777705f27f7777705f05f77705f05f05f05f534800015555c17c2bddddc53c53c67c67dc17c17ef72777705f05f05f05f777705f05f05f05f,0x55005577770055777777770055777777702f23f02f02f777700005555777706f06f02f02f702f06f77702f02f05f11f02f5a19622702f02f00293c006fc95555dddc1bc1bc0bc0bdc0bc1bdc3a702f11f702f02f6c69c0bc0bd832,0x55001a7c0058e95555dddc1bc0bc0bc1bc0155ddddc0bc0bc0155ddddc17c2bdddc0bc47c2bc1bd60a0055777777706f02f02f06f06f57695f277777777000fbc00c4b95555dddc87c87c1bc1bdc1bc87f272706f21fd0e9c1bc2bf43e706f06f,0x550005577723f02f02f23f005577777777005577777777777700005555702f06f702f06f77702f02f05f11f02f5dd96fa777702f02f02f02f00293c0080c95555c0bc1be002702f06f81c9c0bc47ddddc0bc0bc0bc0bdc0bc0bd912,0x55001a7c005ca95555ddc0bc1bc1bc0bc1bd4ae5c480155ddddc0bc0bc0155ddddc17c2bdddc0bc47c2bc1bd6e200557777777706f02f02f02f77777777000fbc00c4595555c1bc87dc1bc87f3e6706f21fd149c1bc2bf456777706f06f06f06f,0x1540155dddc0155dddddddc0155ddddddc0bc8fc0bc0bddddc00015555dddc1bc1bc0bc0bdc0bc1bdddc0bc0bc47c47c0bd8626089c0bc0bc00015555dddc1bc1bc0bc0bdc0bc1bdc52702f11f702f02f6c09c0bc0bd66a,0x1540155dddc0155dddddddc0155ddddddddddc2ea08082f207e980200005555777706f09c80bd67dddc2d209081bc25a0a2984a5fa9c2020869c1fa084800015555dddc2bcd3a05f0789c2d23669c2aa2f0a5ba70a88bba96c9c28a288a492,0x1540155dddc0155dddddddc0155ddddddc0bc8fc0bc0bddddc00015555ddc0bc0bc1bc1bc0bd92263c9c0bc1bddddc47c47c0bc0bdc0bc0bc00015555c0bc1bdc0bc1bdc6a777711f11f02f02f702f02f6ba9c0bc0bd0ca,0x15400155ddc8fc0bc0bc8fc0155dddddddc0155dddddddddddc00015555c0bc1bdc0bc1bddddc47c47c0bc0bdddc0bc0bc0bc0bc0bd952636800015555c0bc1bdfea702f06f8229dddc47c47c0bc0bdc0bc0bdc0bc0bd762,0x1540155dddc0155dddddddc00155ddc0bc8fc1bc0bddddddddc00015555c8fc0bdddc0bc8fc1bc0bc0bd93a6309dddc47c33218f45f702f02f00005555702f06fa939c0bc1bddddc17cede02f02f702f02fa0f9c0bc0be526,0x5500555777723f02f0055777777702f6af06f02f0055777777702f23f02f02f777700005555777706f06f02f02f702f06f702f11f777702f02f02f02f02f02f72c9b0200005555777706f06f02f02f702f06f777702f02f11f11f02f02f72e9b0a702f02f777702f02f02f02f02f02f02f02f7aa967259a9832]
def h2b1 : Array Nat := #[0x5500055577723f02f02f23f00557777777723f18f0055777777702f23f02f02f777700005555702f06f702f06f777711f11f02f02f777702f02f02f02f02f02f7329aea00005555777702f02f06f06f02f02f8169fea702f06f777711f11f02f02f702f02f777702f02f02f02f02f02f02f02f8409762432990a,0x55005577770055777777770055577777773ff3ff0d9837e77714f14f0d8837a00005555777706f11f02f18f77770f0839606f18c80bc21670e9b62714f19f70de85420000555577770af3bf05f4ef73ff3af77770f1839205f18d817c21270f9b6670df854677770f6821602f02f0f7817c21205f8b8983660c966a,0x15400155dddc0155dddddddabc63c63c1bc0155ddddddc63c37218f18f777700005555777711f11f18f18f718f11f718f06f777727f17489fc2160000555577770af11f05f18f718f11f777705f11f05f18f718f1549c63c63e316,0x5500557777000557776af18f18f6af77770055777777718f3ff18f18f777700005555718f11f777706f11f02f18f718f11f777702f16880bc63c00015555dddc2bc47c17c63dc63c47ddddc17c47c17c63dc63c786777718f18f02f02f18f05f18f05f8d19de261e95c2,0x15400015555dddc0bc8fc8fc0bc0155dddddddc0bc37223f119800015555dddc1bc0bc0bc0bddc0bc8fc1bc0bd9fa6729dddc67c9fc366114800015555dddc1bc0bc0bc0bdc8fc0bddddc64a17a89fc9fdc1bc1bc00015555dddc1bc1bc0bc0bdc0bc1bddddc65e17f80bc0bdc0bc0bdc0bc0be392,0x1540155dddc0155dddddddc00155ddc8fc8fc1bc0bdddc0bc8fc0bc0bddddc00015555c8fc0bddddc1bc0bc0bc0bddddc47c5ba02f02f706f06f00005555777706f06f02f02f702f06f777705f1fb80bc0bdc0bc0bdc0bc0be422,0x55005577770055777777770005577777773ff3ff114851277714f19f162837a6a8800015555dddc1bc4ca02f59f7777156849a06f12c80bc4fa7149a8a719f27f70de83aa0000555577770af344817c34a73ff3af777715c852a05f2f0817c2ba9a8a5ba71448b42777717484fa02f02f05f288817c2baa38a49259a9832,0x550055777700557777777700005555777706f02f02f02f7702f23f06f02f6b499ca777719f27f0df851200005555777706f02f02f02f723f02f6789dddc66210e821613e800015555dddc1bc1bc0bc0bdc0bc1be706777733d8bfa02f02f,0x55005577770055777777770005577702f23f06f02f77702f23f02f02f777700005555723f02f777702f23f06f02f02f02f71a9a12777711f102863d67dc0bc0bc00015555dddc0bc0bc1bc1bc0bc0beac2a939c0bc1bddddc17ce9602f02f702f02f777702f02f02f02f02f02f02f02fae0a526432990a,0x5500555777718f11f0055777777711f18f06f02f6d2800015555dddc47c63c63c47dc63c63dc0bc0bc0155ddddddc47c46611f11f7777777715f27f0f684fa00005555777721f21f11f11f711f21f777721f21f11f11f711f21fb5a9c47cb52,0x1540155dddc00155dddddddc1bc0bc00015555dddc47c63c63c47ddddc1bc63c0bc47dc0bc0bc0155ddddddc47c47e11f11f77770e4852a777719f27f0f684fa00005555777721f21f11f11f711f21f77702f02f21f11f11f5889822711f21fb729c47cbfa,0x1540155dddc00155ddc47c63c47c63ddddc00015555c63c63ddddc1bc63c0bc47dc63c63c0155ddddddc47cffc47c47ddddddddc1bc0bd67d67c00015555dddc2bc87c17c47dc47c87ddddc17c87c17c47ddddc47c47c0bc0bc17c87c17c47ed9aa2996b25f49c47cc1e,0x1540155dddc00015555dddc47c63c63c47ddddc1bc63c0bc47c00155dddddddc1bc0bdc0bc0bc0155ddddddc47c48211f11f777719f27f08585d277770f185720000555577770af21f05f11f711f21f711f21fa3b9ddc0bc0bc87c17c47d6866189c47ccf6,0x1540155dddc005ff001b7a5555777719f02f27f06f777706f27f02f15f00557777777770ea853c01555ddddddc67c9fc67c67dc9fc67dddc53c53c67c58a6a8800015555dddc2bc53c17c67dc67c53dc67c53ed76777705f3ab817c302719f19f,0x154001555ddc1bc0bc1bc0bc00015555c0bc0bdc0bc0bc0155dddddddc0bc47ddddc47c63c63c47c0155ddddddc1bc0bc1bc1bddddc1bc0bc0bc0bddddc00015555dddc53c53c1bc1bdc1bc53dc1bc53efd6777721f21f06f06f706f06f,0x15400015555c0bc0bc0155dddc1bc0bddddc1bc0bc0bc1bc0155dddddddc47c63c63c47ddddc0155dddc0bc0bddddc1bc0bc0bc0bdddc1bc0bc1bc1bddddc00015555ddc0bc0bc53c1bc1bd0b263c9c1bc53f2ba706f14f777721f21f06f06f706f06f,0x1540069f001bc25555777706f02f02f06f00005555777706f02f02f06f00557777777706f18f02f11f777706f18f02f11f00557777702f06f67d9dc0bc0bc1bc1bd9fa6b49dddc00015555dddc53c53c1bc1bddddc87c87c1bc1bdc1bc1be712,0x55001a7c006f695555dddc1bc0bc0bc1bc00155ddddc0bc0bc0155ddddc63c63dddc0bc47c63c1bdb4a00557777777706f02f02f02f06f06f68a9b1a77706f02f06f06f777700005555777721f21f06f06f777706f06f02f02f21f21f06f06fc9cadd659a9832706f21f777706f06f0af21f06f06fd0fa906706f06f,0x155540155c0bc0bc0155dddc1bc0bc0bc1bddddc1bc0bc0155dddc47c63c63c47ddddddddc0155dddc1bc0bc0bc0bddddc0bc0bdddc1bc0bc1bc1bddddc00015555c1bc53ee0677702f02f14f06f06f4389922706f14f77770af21f06f06f706f06f,0x155540155c0bc0bc0155dddc1bc0bc0bc1bddddc0155dddc67c3f218f11f7777777700555702f06f77702f02f06f06f77706f02f06f06f777700005555706f14fb939dddc53c53c1bc1bdc1bc53ddddc2bcec606f06f706f06f,0x155540155c63c63c0155dddc1bc0bc63c47c63c47d9b26ea9dddc0155c63c63dddc63c47c63c47ddddc0155dddc67c9fc0bc0bdddddddc47cffc47c47ddddc00015555dddc47c47c0bc0bc5fc87c2bc47f39ab8d903a6609dddc5fc87c2bc47dc47c87ddddc2bc87c2bc47dc47cde6,0x55550055702f02f0055702f02f77702f06f02f06f0055777706f18f02f11f777777770055777706f02f02f02f06f06f6909b32777777706f02f06f06f777700005555777706f06f02f02f14f14f06f06fcf7ae66432990a777706f06f14f14f06f06fd02ae1e706f14f777721f21f06f06f706f06f,0x15400155ddc1bc0bc1bc0bc00015555c0bc0bdc0bc0bc0155dddddddddddc6da0d0897c97c01555dddc1bc1bddddc1bc1bdddc1bc0bc0bc1bc1bd8d67509dddc00015555dddc53c53c1bc1bddddc53c53c1bc1bdc1bc53efee77774ff21f06f06f706f06f,0x15401555dddc9fc67c005ff001e7a5555777719f02f27f06f77719f27f06f27f19f7b695ea0055777777773bf4ef74ef14f00557777777719f27f727f19f77714f14f19f3bf798800015555dddc53c53c67c67dc67c2bdc67c53e9e2777705f4ff05f3bf777719f19f19f19f,0x55000557776af18f18f6af000557776af18f18f6af7777005577777777777700005555718f11f777718f18f06f11f02f18f81c9f72718f11f777702f1ec80bc63c00015555c63c47dc63c47ddddc63c63c17c47c17c63e0767de9dddc17c7b605f18f777718f18f02f02f18f05f18f05f900991a644975a,0x15400155ddc08a1da879a02880155dddddddc0155ddddddddddc53c67cefd3bdf3a00005555777706f45f02f45f777706f45f02f45f719f27f74ef4ef0000555571da8c1a71e68de2777705f2e4817c352777705f2e2817c34a77771fe875202f02f05f2b2817c1e2a50a4da5ee97d2,0x5500055577723f02f02f23f00557777777723f20480155ddddddc0bc8fc1bc0bdf52777700005555777706f02f02f02f723f02f77773bf1d093bd17dc0bc0bc00015555c0bc1bdc0bc1bddddcd262ec80bc0bddddc0bc0bc0bc0bdc0bc0bee3a,0x550005577723f02f02f23f0055777777770055777702f02f777706f02f777700005555777706f02f02f02f777706f02f02f02f777719f27f4ef1d49c0bc0bc00015555c0bc1bdc0bc1bddddce5e38b80bc0bdddc0bc0bc0bc0bc0bd7026369c0bc0bee52,0x550005577723f02f02f23f0055777777770005577702f23f06f02f7777777700005555723f02f777702f23f06f02f02f02f8229d3e777711f1a7863d17dc0bc0bc00015555c0bc1bdc0bc1bddddc17ce4e02f02f777702f02f02f02f02f02fac2a83e777702f02f02f02f02f02f02f02fb7ca5265d8990a,0x15400155ddc8fc0bc0bc8fc0155dddddddc00015555dddc1bc0bc0bc0bddddc1bc0bc0bc0bddddc67c9fd3bc7d20055777702f02f777706f02f7777702f02f00005555702f06f702f06f777705f39980bc0bdc0bc0be85677702f02f02f02f02f5df9952,0x550005577727f19f19f27f0017fc007e695555dddc67c0bc9fc1bddddc9fc67c1bc9fc0bc67de4a7e080155ddddddddd3bc53c0155ddddddddc9fc67dddc53c53c67cefdf3a00005555719f14f719f14f777719f19f02f02f05f14f05f19fc78aa4256a9e02777705f4ff05f19f777705f19f05f19f,0x5555000557706f02f06f02f7f2924200005555702f02f49c80155dddc47c63c63c47ddddddddc47c63c63c47c0155dddc1bc0bc0bc0bddddddddc1bc0bc0bc0bddddc00015555c1bc53eb4a777721f21f06f06f777706f06f06f06f]
def h2b2 : Array Nat := #[0x55001a7c0080495555dddc0bc1bc1bc0bc0bc1bd4be7fe800155ddc0bc1bc1bc0bdc0bc0bc0155dddddddc1bc63c0bc47ddddc0155ddddc0bc1bdddc0bc0bc1bc1bdf52777700005555706f14f777706f06f02f02f14f14f06f06fcf7ad125d8990a706f14f777721f21f06f06f777706f06f06f06f06f06fd17a86e,0x55550055702f02f00055777706f02f02f06f77702f06f06f02f0055777719f4ef18f11f777777770055702f06f77702f02f06f06f7777777700005555706f14fb389c1bc53dc1bc53ddddc2bce7e06f06f777706f06f06f06f,0x55550055702f02f496800015555dc0bc1bc0bc1bd28a7f280155dddc1bc63c0bc47ddddddddc1bc63c0bc47c0155dddc1bc0bc0bc0bddddddddc1bc0bc0bc0bddddc00015555c1bc53eb02777721f21f06f06f777706f06f06f06f,0x155540155c0bc0bc001555ddc1bc0bc1bc1bc0be14a41f9dddc1bc0bc0155dddc67e57c63c47ddddddddc0bc85a0055702f06f77702f02f06f06f777706f02f777700005555706f14fafc9dddc53c53c1bc1bdc1bc53ddddc2bce1e06f06f777706f06f06f06f,0x55005577770055777777723a843223b842a8b2800015555dddc97a36f0098dbdc4321129c42a110801555dddddddc4ae22f9dddc4a622e9ddc9320998dbc24e22297f68a6800015555dddcdd621f000847ddddc87d33c47cefddddd3fc87cefc47dc932369af1272228a2e,0x550055777718f11f0055777718f11f77711f18f11f18f8f4800015555ddc63c47c47c63c47d1668ee9c63c63dc63c63c0155dddddddddddddddc9f209f8dbcdbc00015555c47c87ddddc87c87c47c47ddddc87c87c47c47dc47c87f32677773578afa11f11f,0x1540155dddc0155dddddddc0155ddddddddddca6a13b8a72139a47a00005555777770f45f36f45f777294889a2aa917c28a930a2aa713b8506713984fe00005528e95599c977770af282817c97dc89a2389c87a22aa2ba721c88a28ac9c28a0ae9832,0x1540155dddc0155dddddddc0155ddddddddddc17c17c17c17e50a0000555577705f32f0af05f05f94ea3ca777715f45f59f45f705f05f705f05f00005555732f05f777735a89ba078897dc17c17dd66705f05f7579c17c17d1a2,0x55005577770055777777770005577705f32f0af05f7777777700005555732f05f777715f95f45f61f77705f05f05f05f05f9549d4e705f05f00005555732f05f8fe9dddc1bc9d202f36f705f05f705f05f75d9c17c17d90e,0x55005577770055777777770055577772078b2a7778cfa0f2dd85129669ddd9fc53cb72145a59e0000555577770af278817c97de83d1bddddcb5e230817c8aa05f288a6ba8ae9c512150800015555dddc1bc9ea02f59f77772d688ca06f22c80bca269afa2c2714f27f71458546777705f05f0ae8a2202f0af80bca26a74983660ca492,0x550055777700557777777700055577705f32f0af05f777746f2ca9ddc17c17c17c17e5ca00005555732f05f777736c86be0d2897ddddc17c17c17c17c17c17e6d27599c17c17c00015555dddc17ccbc1bc17c0bc17eada8fe9dddc1bc92a02f36f705f05f705f05f777705f05f05f05f02f05f02f05faf8990e468a522,0x5500557777000fbc0098495555dddc2bc17c17c17ddddc2bc17c722300800015555dddc2bc17c17c17ddddc2bc17c5922de9c17c17c00015555dddc2bc17c17c17ddddcebd1bc58a2dc9c17c17ddc17c17c17c17dade6b5800015555dddc2bc17c17c17ddddcf7225c83022ac9c17c17e39a705f05f705f05f,0x15400155ddcc321da8c4a02e800015555c76a1e09c0ba03a80155dddddddddddc2bc17c97c97c0155dddddddddddc2bc17c97c97dddd9fc53d3fcefe74a00005555777721f3df06f3df777721f3df06f3df77770af05f25f25f21f3df06f3dfbbca27a624a462714f19f73bf3bf,0x55000d8200262a5555777793f05f06482bc01555ddddc2ba0b480155dddddddc2bc17c97c97ddddc5622d880155dddddddcebd1bc17c17ddddc55a2d69ddcdfa1838e02181a76200005555777721f28081bc57dc8e2250a2f27770b48a5225081bcaaa612a4c27183866e71818666,0x550022fc0099095555dddcebc17d1bc2bc0155ddddc5423ff0055777777770af05f25f25f7777000557777746f3af7773ff8cf3af2dda59a7773af14f3af3af9de800015555dddc87cebc1bc57dd1bcebe322777721f25681bcab6714f19f73af3af,0x55550055705f05f0055777793f20a80123249dddc0155dddc2bc17c17c17ddddc17c17ddddc0155dddc2bc17c17c17ddddc17c17dddddddc2bc2bc2bc2be7aa00005555705f0af9049ddc17c17c2bc1bc2bd1ba94e9dddc87c98a06f70f70af0af70af0af,0x155540155c17c17c0155dddcebc84246f32a9dddc0155dddc2bc17c17c17ddddddddc0155c17c2bdddc17c17c2bc2bdddddddc2bc2bc2bc2be7c200005555705f0af90a9dddc5fc2bc1bc2bddddeefc9a206f70f70af0af70af0af,0x155540155c0ea04080155c7821e69ddc10230c879a31280155dddc2bc17d1bd1bc86a2f6a0fa9809dddddddc0155dddcebc97c17c17c86e2f4a0fe97e9ddddddddddd9fc53d3fcefe7f200005555777793f25f05f05f17f3df06f3dfceea442414a582777717f3df06f3df777721f3df06f3df714f19f73bf3bf,0x1540069f0029ba5555777706f02f02f06f00557777702f02f00557777705f0af77702f5ef0af06f9c9801555dddc1bc1bdddc1bc0bc0bc87c1bea0257c9dddc87c1bddddc2bc2bc00015555dddd7bc1bc1bc1bdc0bc1bdeb6777721f06f06f06f77770af0af0af0af706f06f,0x5550055777705e8f020005577705f32f0af05f777700005555732f05f777706f1b480bcdbdc17c17c00155ddc17ccbc2bc17ddddddddddddc17c0bc17c17c17c17eb2275d800015555ccbc17ddddc87c6d611fabf777705f05f05f05f05f05faca9d7e777705f02f05f05f05f05f05f05fbdc9916643a522705f05f,0x55005577770000555577770af02f05f05f777706f05f02f19f00555777705f05f7777705f05f0005577705f32f0af05f7777777705f05f02f02f777705f05f00005555732f05f777721f1bb847c97dc17c17dd9677705f05f05f05f05f64fa552705f05f,0x1540155dddc003ef002a62555577770af02f05f05f777706f05f02f19f005577777777705f05f0005577705f27f0af05f7777705f05f77705f05f05f05f972800015555c9fc17ddddc53c67c67c67dc17c17ddc6777705f05f05f05f705f05f,0x55001a7c00aa495555dddc0bc1bc1bc0bc0bc1bd50ea9e80155ddddc0bc0bc0155ddddc17c2bdddc0bd7bc2bc1be7560005577706f02f5ef06f777706f02f02f02f06f06f7a7a9a27777777700005555702f06f777706f02f02f02f21f06f06f06fc939efe570a95a777721f06f06f06f77770af0af0af0af706f06f,0x1555400015555c0bc0bc0155dddc1bc0bc0bc1bddddc1bc0bc0bc1bc0155dddc2bc17c17c17ddddc2bc17c17c17ddddc00015555c0bc1bddc0bc0bc1bc1bdfd64c89dddc53c1bc1bc1bddddc2bc2bc2bc2bc00015555c0bc1be216702f06f777714f06f06f06f77770af0af0af0af706f06f,0x55550055705f05f0055777706f02f05f19f77770055705f0af77705f05f0af0af77770005577770af05f02f02f7770af05f17f0af7777777700005555705f0af8739c17c2bddddc87c70611f98f77770af0af0af0af70af0af,0x55550055705f05f0055777706f02f05f3cc9dddc0155c17c2bdddc17c17c2bc2bddddc001555ddc2bc17c0bc5fc2bec2a4219dddc5fc2bddddcebcbd677770af0af00005555705f0af8439dddc5fc2bc2bc2bddddc87c68e11f98f77770af0af0af0af70af0af,0x15540155dddc67c53c003ef002f5a555577705f19f0af05f05fbe8972277770af05f06f14f00005555719f05f777714f19f19f14f705f05f54680155dddc17ccbdddddc17c17ddddc17c17c17c17c0155dddc17c67dddddc17c17ddddc17c17c17c17dddc17c17c17c17e732,0x550022fc00c1995555dddc53c17c67c2bc0155ddddc67c67c005cf0030625555777714f06f19f14f77770af05f19f14f14f15f06f14fc9c967a59caf12777719f14f14f15f06f14f7b0a9fa0055777777770af05f19f25f3af14f7b1a9f2777773af3af005557777719f14f77719f19f14f14f9df9c67c53dddcebcebc53cebe77a,0x154008bf00315255aff554fc25dddc17c2bc2bc17c17c2bd562c4e80155ddddc67c67c005cf0030925555777714f06f0af0af705f0af59e9ddc67c53c2bc1bc53dedaa8480155ddddc17c2bdec6777770af0af00557777705f0af7b39ddddc2bc2bdddc2bc2bc2bc2be792,0x55550055705f05f0055777714f19f19f14f777700173c00c2a95555dddc2bc17c17c17c53c1bc2bc2bf3da5da90d6bfa9dddc17c17c53c1bc2bc2bd532be29dddc53c2bc1bc53c0155dddc2bc17c17c17c2bc2be11eb009ddddddddc2bc2bc01555c17c2bdddc17c17c2bc2bdddddc2bc2bdddc2bc2bc2bc2be7c2,0x3ef00316a557df554ff240155c17c17c0155dddc2bc67c17c53c67c2be162b209dddc005cf0030da5555705f0af5da9ddc17c17c2bc2bc2bd54abe89dddc53c2bc67c53c0155c17c2be11e7777777770af0af0055705f0af8499ddddddddc2bc2bdddc2bc2bc2bc2be7da,0x55550055719f19f0055719f19f77719f14f19f14f00173c00c3c95555dddc2bc17c67c53c53c67c1bc53f3f25ec9112c069dddc53c1bc67c53ddddc53c67c1bc53c0155dddc2bc17cefd1bdddddddddcefcefc0155dddc53c67c17c17dddddddddc67c53dddcefd9fc53d3fe7f2]
def h2b3 : Array Nat := #[0x555500005555777714f0af06f17f17f0af0af17fcf690d6433b31a005570af0af70af0af0055777717f06f0af14f777717f11f26f4ff7777005570af17f777717f0af0af0af17f17f84dac1a7770af0af17f17f77770055777714f0af06f06f17f17f84fac1270af17f7770af0af17f17f77777777,0x17f0033625526f55500a400015555c2bc2bd0d6005570af0af54c9c2bc2bc0155dddc53c1bc2bc53c5fc53e192b269dddc53c67c67c53ddddc0155c2bc5fdddc2bc2bc2bc5fc53e14eb0c9dddddddc0155c2bc53e13e70af14f7770af0af14f14f77777777,0x55005506f02f02f06f00550af05f05f05f06f05f02f11f005506f02f02f02f06f02f02f02f05f05f05f05f0000555506f438b2ba06f43ead1205f05f02f02fb30ac4e40e905202f420abe6,0x55005506f02f02f06f00550af05f05f05f06f05f02f11f005506f02f02f02f06f02f02f02f05f05f05f05f0000555506f46eb31a06f06f02f02fb3eabc2414914205f464ab8e02f462ab86,0x55005502f32f23f01e801540bc8fc8fc8fc9fccbccbccbc01540bc8fc8fc8fccbccbc8fc8fc0bd27a50a801540bc0bc8fc8fccbccbc8fc8fc8fd2327ef88fd2aa7c5b4d6,0x55005506f02f02f06f00550af05f05f05f06f05f02f024801540bd2324c281bc0bc0bc0bc17c17c0bc0bc001541bd27a82b81bc1bc0bc0bc17c17c0bc0bc0bd2c27cbb4ee,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bc0aa005502f48c926206f02f02f02f05f05f05f05f0005506f4c8ab3a06f06f02f02f05f05f02f02f00,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bc0da005506f02f02f50a924a498930a06f02f02f02f05f05f05f05f0000555506f50ab37a06f06f02f02fb44ab9643291a605f05f02f02fb42ab8e43391a202f4c2aaaa,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bc0f2005502f492927a06f02f02f02f05f05f05f05f00550006f06f02f02f05f05f02f02f02f4c8aaf2,0x555005519f27f27f19f48a950200550af05f05f05f54e94ba0af05f4ef3bf00550af05f05f05f54c94c219f27f27f27f05f05f05f05f000055550af552b3da19f19f27f27fb4aab62444921205f05f05f05fb42aab243393ea05f05f05f05fb40aaaa43593e2,0x55005506f02f02f06f00550af05f05f05f06f05f02f11f005506f02f02f02f06f02f02f02f05f05f05f05f0016520035de555506f06f02f02fca2b1be40e95c206f5a0add205f5a1adca02f57ca9d2,0x55005506f02f02f06f00550af05f05f05f06f05f02f11f005506f02f02f02f06f02f02f02f05f05f05f05f0017420035c6555506f5c4af7e06f5dcae6205f5ddae5a02f02f02f02fb52aa1a56a95c2,0x55005506f02f02f06f005511f18f18f11f06f18f02f11f005506f02f02f02f06f02f02f02f0c0821a08482ba0000555506f06f02f02fca8ae9241497d206f612af2211f608a8ee02f606a8e6,0x15401541bc0bc0bc1bc015447c63c63c47c1bc63c0bc47c01541bc0bc0bc0bc1bc0bc0bc0bc67c9fd3bc34a0000555506f63cae0606f64eaffa11f11f02f02fb6ca91e57097d202f636a856,0x1540154ffcffe33cffc01540bc8fc8fc8fc9fcffcffcffc01540bc8fc8fc8fcffcffcffcffc0bd9fa726801540bc0bc8fc8fc48211f88fc8fc8fd9ca6b388fda5a6a1b51a,0x15401541bc0bc0bc1bc015447c63c63c47c1bc63c0bc47c01541bc0bc0bc0bc0bd9ca67d860210881fe138801541bc1bc0bc0bc1bdad29c4b55e11f11f02f02f00,0x55005506f02f02f06f005511f18f18f11f06f18f02f11f005506f02f02f02f06f02f02f72699e267d9aba19f27f0ea85420000555506f06f02f02fcaeae06432990a06f726b18611f11f02f02fb72a8ee59a983202f6aea65e,0x154007209541bc0bc0bc1bc015447c63c63c47c1bc63c0bc47c01541bc0bc0bc0bc0bd9e267e867c9fcffcffc01541bc1bc0bc0bc0047c47c0bc0bc0bdad29c1b55e,0x55005506f02f02f06f00551bc869201486c206f10680bc6aa0055506f02f02f02f74a9d7206f02f02f02f6899d5a19f25f25f25f0000555506f06f02f02fcdeae064f8990a06f06f02f02fc61ab9670291a625f25f02f02fb78a8be5ad989202f750a526,0x154015541bc0bc0bc1bde4a7a48015447c63c63c47c1bc63c0bc47deca68e801541bc0bc0bc0bc1bc0bc0bc0bdec268f867c9fd3bc7220000555506f06f02f02fcb4ad424449e0206f7b6b27211f11f02f02fb72a66659a9c1202f02f02f02fb70a65e59c9c0a,0x15401540bd242496801541bc63c0bc47c47c63c63c47c01541bc0bc0bc0bc1bc0bc0bc0bc67c9fd3bc76a005506f7f2ab020011f11f02f02f02f02f02f02f,0x154001541bc0bc1bd25a7eca0a249c8015447c63c63c47c1bc63c0bc47c01541bc0bc0bc0bc1bc0bc0bc0bc67c9fd3bc7820000555506f7ecaaba06f828b38a11f11f02f02fb96a85e5d6991202f02f02f02fb94a8565d8990a,0x15401540bd2724a2801541bc63c0bc47c47c63c63c47c01541bc0bc0bc0bc1bc0bc0bc0bc67c9fd3bc79a00550006f7f2ab4a11f11f02f02f02f02f02f02f,0x5500055506f02f02f06f84c92a2005511f18f18f11f06f18f02f11f66ea0ea005506f02f02f02f06f02f02f02f8469a5619f27f0fd88420000555506f06f02f02fcaeaaba432a04206f852b3de11f11f02f02fb9ca8165e8998a02f02f02f02fb94a65e5d89c0a,0x550055265873a01c891e0055264873e01a891a258844a11088d20055570f36f36f36f25384c60f688a66a7a2b625284be0f788a26a5a2b20000555570fc2f36f36fcbaa93644aa26a25389060f6822ec61a8f6702983625289020f7822ac60a8ee703983236f8a6a492,0x55005511f18f18f11f4baa3ee005511f18f18f11f4b8a3ea11f18f18f11f005570f36f36f36f11f137863c9de3bf13593bc9da0000555511f8eea52e11f11f18f18fce2a866810991a11f11f18f18fce0a85e811991236f36f18f18fba6a4f25f1a26a,0x5500553df45f45f3df005598f83f83fabf2af850a1408a2e005570f36f36f36f2ad850e13e8a262ac850613f8a2200005592a955d8c93df36f36f36fcc0a44a450a46245f8aaa2f283f8a8a2ea36f8a6a2e2,0x5500553df45f45f3df00550af05f05f05f0af05f95f5af00550af05f05f05f15f46f59f59f05f05f05f05f0000555505f8f2a41215f45f45f45fbb6a30a5f4a46205f7539d9605f7519d8e,0x1540154de21e080ea306801542bc17c17c17c2bc17c54a2d2801542bc17c17c17cebd1bc5422d0817c17c17e7026b1a70a6afb55a000055550af05f05f05fcc6a412468a52236688e20ae8a22bc8a2f260ca49205f6b19c1605f6af9c0e,0x15401559fc53c53d9fc009ba9542bc17c17c17c2bc17c53d9fc000155542bc17c17c17e7c27d792f29728ebc53c53d9fe77a6d79aa2967817dac66b7801542bc17c17c17cdfa23e82ea29a817e36a8ecb52205f6b59c9e,0x55005539c87b204c8e4200550af05f05f05f0af05f1708bae00550af05f05f05f7dda83a3af46f1688b8e05f05f05f05fa1a9aee000055550af05f05f05fcdea4124f8a5223af46f0c68ae6bcea29661ea4de05f05f05f05fb429c16433a65a05f637990e,0x5500553ae87e20588e8a00550af05f05f05f0af05f17c8bf6000550af05f05f05f3a886461748bbe6dda5b605f05f05f05fa3e9b06000055550af05f05f05fccca33e47aa89a3a889121748a82c61a2f2702a49205f05f05f05fb729c1659aa65a05f6079836]
def h2b4 : Array Nat := #[0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bcc0e0055506f02f02f02f7e3a9a206f02f02f02fa7b9b1a05f05f05f05fa7a9b1e0000555506f02f02f02fcd2a25e480a95a06f02f02f02fbc89c1e60ca65e05f05f05f05fbc69c1660da65a02f57c966a,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bcc260005506f02f02fabc9fbeace930a06f02f02f02f05f05f05f05f0000555502f7efa04e06f02f02f02fbfe9d9e642a52605f05f05f05fbfc9d96643a52202f4c293e2,0x55005506f02f02f06f00550af05f05f05f06f05f02f30f80015540bdfbe7f581bc0bc0bc0bc17c17c17c17c01540be1e688bb4d606f02f02f02f05f05f05f05f02f4c8942a,0x5500055506f4c29322005514f06f06f14f14f06f06f14f005514f0af0af0af17f0af0af0af5ef0af06f315801541be1fe891b4ee06f7f5a0ae14f06f06f06f0af0af0af0af,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bcc6e0005506f02f02f02fae6933a06f02f02f02f6e9a5e605f05f05f05f0000555506f02f02f02fcaea04e432aaaa06f02f02f02fc619d9e702a52605f05f05f05fc029d1e65ba56a02f46391a6,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bccb600055506f02f02f02fb04935206f02f02f02f6efa5fe05f05f05f05fafe9b360000555506f02f02f02fcc6a04e468aaaa06f02f02f02fc109d0e660a58605f05f05f05fbfc9c16643a65a02f42190ce,0x55005519f27f27f19f00550af05f05f05f0af05f1888ce6000055550af05f05f05fcf6a04e546aaaa0af05f27f27fc67997e738a83205f05f05f05fc609916703a85a000550af05f05f05fd0b944219f27f27f27f05f05f05f05f70ba69205f4359106,0x55005506f02f02f06f00553af46f46f46f06f19680bccfe0000555506f02f02f02fce49de6516ad7a06f02f02f02fc9c9c1e7aaa65e19f25f25f25fc60983e703a8ea0005506f02f02f02f06f02f02f02fd119cb219f25f25f25f711a6aa02f59c968e,0x15401541bc0bc0bc1bd392a96801542bc17c17c17c1bc17c0bcd160000555502f641991e06f02f02f02fce29d9e810a52605f05f05f05fc7498b6775a8a2005506f02f02f02fb829fee06f02f02f02f05f05f05f05f02f02f02f02fb9497624f8aaaa,0x15401541bc0bc0bc1bc01542bc17c17c17c1bc17c0bcd2e0000555506f02f02f02fcde991e4f8adf206f02f02f02fcf79c1e840a65e05f05f05f05fc78988677ba8d2005506f02f02f02f81fab0a06f02f02f02fd179cca05f05f05f05f02f5d8977e,0x55005514f19f19f14f002efa00358a555514f19f19f14fcea97c651caeb214f15f15f14fc61967a702a9e200553af46f46f46f3d8867219a8da614f25f19f25fc609c0e59ca9da0055514f19f19f19f14f15f15f15f719a6ca15f60f985614f19f25f25f717a6c2,0x555005514f06f06f14f4f0aa8a0000555505f5c8976a14f06f06f14fc8e96da780a96a00550af05f05f05fbe49ffe0af05f06f21f05f05f05f05fbfc990e4faaab200550af05f05f05fbe2a00614f06f06f06f05f05f05f05fbfa99164f8aaaa05f05f05f05f,0x154015453c1bc1bc53c000155542bc17c17c17f37a5da93e2bdc853c1bc1bc53f2465b19e1aa60801542bc17c17c17c2bc17c1bcdbe05f05f05f05fc609c0e435abea005550af05f05f05f825ab2214f06f06f06f05f645994605f05f05f05f71da6da,0x1555573d7fd7fd73d555573cfbcfbcfbf0da5ce94eabd6973cfbd7fe9ff0925929e7aa72954faa076819a3de8f92070870a3be8015687cfbcfbcfbe87cfbef7e9fcfbdbc672183ef0555cf3ef3ef3ef5cf5ff5ff5ff3ef6f39c8e17fc0fbcfbcfbdc869ba9c8e9bcb542,0x154015453c67c67c53c00c12800d68955542bc17c17c17f3da5da951abdc82bc17c67c53f27259e9eaaa78801542bc17c17c17c2bc17cefd3fc17dc0e727801542bc17c17c17c53c67c67c67c17dc16729817c17c17dc9e9c09ca69c2b55a,0x5500325a003602553f6955d1a914f06f06f14f55eb1facfc95aa564b212d26b5ea005514f06f06f14f06f7aa9eda005521f0af0af0af0af7ab9ede21f0af06f21f005514f06f06f06f06f7ad9ee614f06f06f06f0af0af0af0af,0x5555005506f43290e2005514f06f06f14fcf7a1024fcaaba14f06f06f14fd02a05a005514f0af0af0afce6a0be47dab7217f0af0af0af21f0af06f21f005514f06f06f06fcdea04e469ab8214f06f06f06f4feaac214f06f06f06f0af0af0af0af,0x5555005506f46891ba005517f06f06f21fceea0d244eabda17f06f06f21f005517f0af0af0afce0a046435abea17f0af0af0af506aae221f0af06f21f005517f06f06f06fcdea04e433abe217f06f06f06f504aada21f06f06f06f0af0af0af0af,0x1555401541bd3e250a8015453c1bc1bc53f3de84090deafc853c1bc1bc53c015453c2bc2bc2bf3da84190d6afa85fc2bc2bc2bd7bc2bc1bcdee005506f813a0ae06f06f06f50aaaf282bab3a14f06f06f06f0af0af0af0af,0x33c200361a55408955d20900550af546954a005514f19f0af14fcfca17a412ac6a86aacb2d2cb58214f19f19f14f00550af841a14e17f0af0af0af4ff0af3bf4ff00550af843a15614f0af0af0af14f19f19f19f0af0af0af0af,0x15401567f27ce937a9d2800d509567da5bc94d29cca7925869e629c6801567aa8f89172942a7628b6980291ea382d42b53a,0x5555c3c9f9a4f6aaa255c30979a522af42c1e96aa78ca99a55c2ca0164e8aa6ac1a9bea6e0a64e199e055c2aa01e4e6aa62c189bee6dea64619a601bce6f1a612]
def h2 : Array (Array Nat) := #[h2b0,h2b1,h2b2,h2b3,h2b4]
def h3b0 : Array Nat := #[0x333304f005533333333333300553333333333336cf33,0x53333005533333333333333005533333333333344f,0x53333335333333333353333333333333310f,0x5533333333005533333333333333005533333333333310f53f333333333310f35f00f00f,0x5333333330055333333333333330055333333333333333333331cf35f00f00f,0xcccc03c0154cccccccccccccccccccccc42e,0xcccc13c0154cccccccccccccc0cccccccc446,0xcccc13c0154cccccccccccccc0cccccc0,0x55333333333333333300553333333333336cf33,0x333304f0055333333333333333300553333333333333333336cf0ef00f00f33,0xcccccccc13c0154cccccccccccccc0333333,0xcccc0154cccccccccccccccccc0154ccccccccccccd2e24f333333336cf0ef00f00f33,0x333333005533333333333333333300553333333333330ef24f333333330ef1cf00f00f33,0x553333333333333333333300553333333333330ef33,0x3300553333333333333333333300553333333333333333330ef1cf00f00f33,0x5330333353333333300f33333353333333333,0x14cccc04a005533333326f61f333333333300553333333333333333336cf0ef00f10f3333,0x5509f0ff03fc2fc3fcc7c27d43fcc7c3fc3fc00ff0ff0ff0ff0ff0ff0ff0ff0189543fc2fc0fc6fc0fc83c3fc3fcdfa0ff0ff03f0ff03f0ff0ff03f0ff03f,0x15477c0fc2fd23c003f03f003f03f003f03f03f03f03080fc0fc03f03f03f02a857c0fc0fc0fc0fd546fe6fc0fc0fc0fc003f012bc003f03f03f000fc003f03f,0x1542fd23c27c0bf48f61f04282fd23d23c2fc003f03f03f03f03f03f03f03f03c80fc0fc0fc0fd5523c6fc27c01bf005fc048f1bf03f000fc003f03f03f03f,0x333307f005533333333333300553333332de8ccb72331ff,0x14cccccccc1e2000154cccccccc43ccccc52a,0x5333333005533333333333300553333333310f33331ff,0x53333330055333333333333304f3300553333331928cccc58e3300f,0x333305a80154cccccccccc13d4cc03ccd0fccd43ccc8ca,0x55333333333333333306080154cccccccccccccc0154cccccccccccc8b2,0x333300553333333333333300553333333333331ff,0xcccc19a0035542124cccccd47ccccc0154cccccca0a33333300f,0x333307880154ccccccccc13d47ccc30cc005533333356f332d08033,0xcccc1e2005533333333304f51f33330055333333332d88ccb5a331ff,0xfccccc1fa005533333351f3333500ce37ccd5bccca0a,0x3f00553333333333533333304e8cc0154ccccccccbd23358f33]
def h3b1 : Array Nat := #[0xfc0015f55333333335333353333333307880154ccccccccdc23333,0xcccc0154ccccccccc13d47ccccccc0154ccccccccccccd3a331ff,0x53303300553333333333333300553333333333331cf,0xcccccc1fc0154cccccccccccc0154cccccccccc03cb7a333333333300f1ff00f04f,0x335333303333333309080154cccccccccccc03ccccccccc296,0x5333333033333307f000154cccccccccccc03c43ccccccc03ccccccc52a,0x5333333330333304f333300553333333300f3333333304f04f,0x5333333330055333333333304f53f3333005533333333333300f10f33333333331ff00f04f00f,0x14cccccccc0154cccccd4fccccc0c0c333300f3333333300f00f,0x14cccccc0154ccccccccc13d4fccccccc0154cccccccccccc52e3300f,0x533335333333005533333333333333005533333333333300f10f33333333331ff00f04f00f,0x53303333330055333333333333330055333333333333333333331cf00f04f00f,0x533033333300553333333333333317c8cc03333,0x5330333333330055333333333333333304f00553333333333331a08596333333333335f00f00f04f,0xcc0154cccccccccc13ccc0cccccd4cccccccd5fccccccd5fccc772,0xcc0154cccccccccc0cccccc6bccccccccccccc78a,0x154cccc0cccccccccccccccd4cccccccccc7d2,0xcccc25a00553333333333333304f5333300f3333333350f51f33,0x553333333303333309c8cc0154cccccccccccccccc13c0154cccccccccccccc936,0x3303333330055333333333333330055333333333333333333331ff00f04f00f,0x3333330ae800d550c6933333309c8cccccc97e00ccb5e,0x3333330035543324cccccc28a333300553333333333333300f,0xcccccc2ea0055333333333304f09c8cccccccc13d4cccd5bcccccafe00ccccccb5e,0xcccccccc1fc0cccc13c30c3300553333333300f3333333304f04f,0x3333333307f0055333333333304f0a28cccc0154cccccccccccc03cb62333333333300f1ff00f04f,0x3f0333333330c080154cccccc28a333353030ccce37ccccccccca0a04f,0x3333333307f0333304f33330055333333332d88ccafe33333300f04f,0xfc02d2330055333333333353333330908cc0154cccccccccccccccc03c3bc03c1e233333300f,0x5333333330055333333333304f9ff33333300553333333333333333333300f1ff00f04f,0xcc0cccccc0154cccccccccccccc0154cccccccccccc03cd5a333333333300f74f00f04f,0x333333005533333333304f0a28cccccc0154ccccccccccccb5e331ff,0x14cc0cccc0cccccccc1fc0154cccccccccc28a3333333304f00553333333333331cf35c8cccccccccc73cad200f04f]
def h3b2 : Array Nat := #[0x3f00057d54cccccccd4cccd4cccccccc2ba333438cccccc0,0x5533333333033335333333333300553333333333333300f65f00f04f333333,0x154cccc0154cccccccccccccd4ccccd4fccccccc13ccc0154ccccccccdba333333,0x55333333333353f0333353f335333333333304f333300553333333333333300f51f00f04f33333300f65f33,0x3f00057d54cccccccd4cccd4cccccccccc13ccccc2ea00553333333333333300f07f00f04f33333300f65f33,0x55333333333333533333335f04f3300553333333307f07f00f04f33333333333333,0x3333533330055333333333333005533333333333333333333331ff00f04f00f,0x5333304f0055333333335333333330055333333333333333333331cf0ef04f00f33,0x50333300553333333353333333300553333333333333333333300f0ef00f04f33,0x55333303333533333353333333335f04f33005533333333333307f07f00f04f33333333330ef24f33,0x55333333333333533333335f04f333300553333333307f07f00f04f33333333333333,0x3f20f5509f31f1df20f03f03f00fc0fc0fc0fc0fc003f03f03f03f03f03f03f03f0d29546fc2fc0fc0fc0fc0fc0fc0fcdaa03f03f03f03f03f03f03f03f03f03f,0x5330333303333333307f0055333333333304f99f3333005533333333333300f3333331cf333333331cf1ff04f04f,0x14cccd4cccc0154cccccccccccccc0154cccccccccccccc7fc576333333331ff00f00f04f,0x3333005533333333333300553333333333333300f,0xcccccc1fc0154cccccccccccccc03333,0x3333333307f005533333333333300553333333333333333333300f1ff00f04f,0xcccccccccc1fc0154cccccccccccc0333333,0x3333333300553333333333333300553333333333333333333300f1ff00f04f,0xcccc0cccc0154cccccccccccccc0154cccccccccccccc03cd3e3333333300f1ff00f04f,0xcccccc0cccc0154cccccccccccccc0154cccccccccccccc03cd563333333300f1ff00f04f,0x3333005533333333333333330055333333333333331ff,0x53333333304f0533333304f333310f3353333333333,0x14cccccc3f20055333333333304fb1f33330055333333333333333333333300f1ff00f04f,0x5333333333307f0055333333333304fb1f33330055333333333333333333333300f1ff00f04f,0x55333333336ff53f0533333317f26f333333333333330ef333304f33,0x154ccccccccc4fa51f330035545424cccccc4b6331268cccccc97a0cc300,0xcccc4e2005533333333354692331308cc4ba3373f3328580,0x154ccccccccccccc43c27e00553333333333192947ccccc0154cccccccccccccc03cb62333333331ff00f04f,0x14cccccc512005533333333533331308cccccccdcfc7fccccc3bccc73c30c,0xcccc5ea005533333333533333333373f1ff00553333333333333307f33,0xfc0154cccccc0cc46a3353333333309985123333005533333333333333330ef0ef10f04f3333]
def h3b3 : Array Nat := #[0xcc0154cccccccccd4cccccc43cccccc2961ff0055333333333333310f04f3300f33,0x5333300553333333353333333300553333333333333333333300f0ef00f04f33,0x3f000602553333333333331988cccd4cccdcfccc0154cccccccccc3bccccccca16,0xfc00186954cccccccc0cccd4cccc296333310f0055333333333324f3333300f33,0x3f000632553333033033333317a94cccccc7fc5ba33333333005533333333333307f51f00f44f3333330ef33333324f33,0x5533333333333333533333384f1ff333300553333333307f0ef00f10f33333307f0ef3333333333,0x55333333333333533333384f1ff333300553333333307f24f00f1ff33333333333333,0xcccc6aa005533333333053333333333331cf1ff00553333333333333333333307f0ef1ff00f33,0x3333005533333333053333333333331cf65f00553333333333333333333300f0ef00f04f33,0x33533333310f00553333333333330055333333333333333333333300f1ff00f04f,0xcc31f0033bd54cccccd87c43ccccccccccd4cccccc0154cccccccccccccc1fdb3c03c43ccccccccccc1fca9a,0xcccccccccc94a005533333397f50f333333330055333333333333333333333317f1ff00f04f,0xcccc97a0055333333333282943ccccc00d552e893333333314c8cc52a3304f,0x3333264801407d333333333288943ccccc0153333331a88cc54a331508cc212,0x3f333326a80154cccccd43ccc2c6330af8d52ee8cc8ca331588cc55a3304f,0x3f00553333333333033332958cc6ea33003554bea4cccccccc9023310f33,0x333333005533333333350f333333003554d824cccccccd43ccc58a3304f,0xfc00270954cccccccccccca3a3333005533333333333333003554dca4cccccccc8a23333,0xfc00276954cccccccc0cccc0cccccccc97a003554e424cccccccc9323333,0xcccca6a00553333333333330055333333333307f3310f3304f,0x33330055333333333333358f07f33005533333333333310f3300f,0x33332a080154cccccccccccccccca9a1ff0055333333333333333333336cf1cf00f1ff33,0xccccae20055333333333333333300553333333333333304f,0x533333356f333358f05333333333300f333300f053333333304f33333304f333300f,0x533333356f333358f005533333333333300f14c8cc0154cccccccccc13c53a33333333333300f00f04f1ff,0xfd4cccccd5bcccccb1653333331588cc0154cccccc53a33330bb8cccccc13ca0a,0xfd4cccc0154cccccccccc0154cccccccccccccccc03c1fc03c97a033333168cc77a3333333300f,0x53333333358f00553333333333333300f07f3300553333333333333333333300f00f04f1ff,0xcd4cccccd63c0154cccccccccccccc0154cccccccccc13c58233333333333304f10f04f1ff,0x154ccccccccccccd63c1fc0154cccccccccccccc03c532330055333333333304f50f333333333300f04f1ff,0x154cccccccccccccc03cb8a331cf33330ef0533333317f00f33333333330ef,0x5333333005533333333333314c8cccccd63ccccc0154ccccccccce0bc59a333333333300f00f04f1ff33]
def h3b4 : Array Nat := #[0x14cc0154cccccd4ccccce37ccccccc03d4cccccd0fccccccc73ccccc3bc0154cccccccccd97c5ca333333331cf1cf04f1ff3333,0x3333005533333333333333330ef0055333333333333333324f00f04f1cf3333,0x14cccc42233333333330ef00553333333333333333,0x14cccc43a33333333330ef00553333333333333333,0x33005533333333333333333333330ef0055333333333333333324f00f04f1cf3333,0x533005533333333333333333333330ef0055333333333304f1ff3333333324f2bf04f1cf3333,0x53300553333333333333333330ef0055333333333324f2bf3333333324f00f04f1ff3333,0x53300553333333333333333333333330ef0055333333333368f2bf3333333368f00f04f1ff3333,0x154cccc14cccccccccccccccccccccc2005533333333333324f2bf04f1ff33333304f1ff3333,0x55333303333333333333333330ef005533333333333307f57f04f1ff33333333,0x154cccc0cccccccc0ccccccb5a33332be8cccc3bc0154cccccccccccc1fd5fc13c7fccccccc93c68a3333,0x5533333333033333333333333330ef005533333333333324f00f04f1cf33333333,0x154cccccccc0cccccc03ccccccccccc73cb2a33330ef005533333333333324f1cf04f1ff33333324f2bf3333,0x553333333333333333333333330ef005533333304f2bf3333333317f00f04f1cf33333333,0x553333333333333300f2cc8cccccc73cb2a33330ef005533333333333317f1cf04f1ff33333324f2bf3333,0x55333305333333333333333333330ef005533333333333324f2bf00f00f33333304f2bf3333,0x1542fc0fc3fc3fc0503f03f03f03f03f03f03f03f03f03f03f03f03f03f03f03f03f03f33c954c7c2fc0fc0fc0fc0fc61200fc00fc0fc0fc0fc0fc57c9f203f03f03f03f,0xfc0041f553333533333333333333333334280154ccccccafcccccc13ca0a3333,0x553333533333333033333300f333356f33330ef005533333333333324f2bf00f00f33333333,0x553333333333333300f57f3333331cf00f33330ef00553333333317f1cf00f00f33333317f26f33333333,0x553333333333333300f57f3333331cf00f33330ef00553333333317f1cf00f00f333333333333,0x3f00107d54cccd4cc03f33333300553333333333330ef07f00f00f3333330c08b163353333332958cc86a33,0x553333333333333333331cf00f3300553333333307f1cf00f00f33333333333333,0x33333300553333333333333333333324f53f0055333333333324f43f33333333333324f04f04f1ff33,0x333300553333333333333333330055333333333333333307f00f04f1cf333333,0x154cccccccc0cccccccccccccc73cd3a33005533333333333307f1cf04f1ff33333307f2bf333333,0x553333333333333333331cf00f333300553333333307f1cf00f00f33333333333333,0x3333005533333333330333333330055333333333333333307f00f04f1cf333333,0xfc0041f55333353333333303357f333356f3300553333332bf3333304f333333,0x5533333333333303333331cf00f333300553333333307f1cf00f00f33333333333333,0x333300553333333305333333333300f1cf330055333333333333333307f00f04f1cf333333,0x5509f03f0bf66f000fc0fc00fc0fc00fc0fc0fc0fcc0e48f03f03f03f03f00fc0fc0fc0fd56d7d23c0fc0fc0fc0fc3ce03f03f03f03f03f03f03f03f03f03f03f03f]
def h3b5 : Array Nat := #[0x5330333353333333300f3303333333353333333300f3333333307f33,0x3303333005533333333330333333333307f00f00553333333333333307f35f3333333307f04f00f00f33,0x14cc0154cccccccccccccccc14ccccccb8e33333343f04f330055333333333324f35f3333333324f35f04f04f333333,0x55333303333333333005533333333333307f00f04fb2f33333304f34c8cccc0cccccccc03cd263333,0x3f000abd54cccd4cc03f00133d54cccccccccccc1fcd7c03c73ccccccc3bd4ccccccd1633333324f533333307f1cf33333138ccccccc4a,0x550bf0ff09f02fc27c83c6fc3fc83c2fc3fc05520f0ff03f20f03f0ff0ff0ff01e83fc3fc3fc3fc0fc0fc3fc3fc3fc3fc3fc3fc0fc0fc3fc3fc3fc3fcc62,0x1542fc0fc3fc6fc0fc0fd546fc83c27c6fc03f000fc00df003f03f00fc0fc0fc3aa2af03f03f03f03f03f03f0003f003f0f3c03f03f00fc00fc1ef00fc0fc0fc0fc0fc0fcc92,0x1d7d556ef43fc3fc2fc0fc3fc6fc83c2feffc7bd540ff002fc00df00ff0ff02fc27c2fce7cde21bf09f20f1bf50ff0bf0ff0ff0bf0bf000ff00bf0f3c0bf0bf03fc02fc1ef02fc2fc2fc2fc2fc2fccaa,0x6fc6fc6fc6fc006ef000ed20bf0ff0ff0ff26f1ef1ef2ff43fc6fc6fd1ef1ef2ff000bf0ff0ff0ff0bf1bf1bf1bf0ff1ef1ef000bf0ff0ff0ff1bf0ff1bf1bf0ff38f2ff0ff0ff0ff1ef38f2ff2ff3ae8002fc2fc3fc3fd4c7d50ff5557d50ff543fd,0x1ffc003c086fc2fc2fc6fc7bcbfc9bc7bc7bcbfcea23ba8006fc6fc6fc6fc6fc7bc7bc006fc2fc2fc2fc2fc7bc7bc6fc2fc6fc6fc006fc2fc2fc2fc2fce3cbfc6fc6fc6fc6fc2fc2fc2fc2fc0083c83c2fc2fd554c7d50bf542fd,0x6fc6fc6fc6fc006ef000f9243fc3fc3fd1ef1ef2ff0bf0ff1bf1bf2ff1ef1ef2ff000bf0ff0ff0ff0bf1bf1bf1bf0ff1ef1ef000bf0ff0ff0ff1bf0ff1bf1bf0ff38f2ff0ff0ff0ff1ef38f2ff2ff3de80143fd20f20f31f31f50ff5557d50ff543fd,0x2fce3ce3c0027c6fc6fc27c9bd57c7bcbfc27c6fc6fc27c010bf0bf0bf47bce3ce3c27c2fc2fc2fc6fc2fc6fc6fc002fce3c9bc2fc2fc2fce3ce3c9bc9bc6fc6fc6fc6fc2fc2fc2fc2fc0142fd555f542fd09f09f1df1df50bf542fd,0x9bc003f08002fc7bc7bc0027c6fc2fc27c9bc7bc7bcbfc7bc9bcf623ea827c6fc6fc27c002fc7bc7bc27c2fc2fc2fc6fc2fc6fc6fc002fce3c9bc27c2fc2fc2fc6fc6fc6fc6fc2fc2fc2fc2fc015542fd09f09f1df1df50bf542fd,0x1540154cccc0154cccccccc0154cccccccccccc0000f0019be5500f5559e24c03c3bcc03c3bcc03c03cc03c03d78a,0x5500553333005533333333005533333333333300005555300f17f300f24f300f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc001554c13c1fcc13c1fccccc93c13cc13c13d226,0x1540154cccc0154cccccccc0154cccccccccccc001554c03c1fcc03c1fd716333300f00f00,0x1540154cccc0154cccccccc0154cccccccccccc00154c03c1fcc03c1fd6c63333300f00f,0x1540154cccc0154cccccccc0154cccccccccccc0154c13c1fd7b6304f07f3333304f04f,0x5500553333005533333333005533333333333300005555300f07f300f07f333300f00f00f00f300f00f,0x55005533330055333333330055333333333333005500300f07f3333300f00f,0x1540154cccc0154cccccccc0154cccccccccccc00154c03c1fc00ccccc03c03d716,0x55005533330cf04f0cf04f005533333333005533333333333300005555304f07f304f07f333300f0ef00f04f333304f00f04f00f,0x5500553333005533333333005533333333333300005555300f07f333307f07f00f00f333300f00f00f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc00015403d5567e9300f07f300f07f300f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc0154cccccb3cb3ccb3cb3ccb3cb3d392,0x1540154cccc003cf55333333330055533300f2cf00f00f3333300f00f00005555300f43f333333083bc03c03cc03c03d442300f00f,0x5500553333005533333333005533333333333300055300f17f3333300f00f00,0x5500553333005533333333005533333333333300005555300f17f333324f07f00f00f300f00f300f00f,0x550055333300553333333300553333333333330055003333300f00f300f00f,0x1540154cccc0154cccccccc0154cccc03c03ccccccccc00154c03c5fcccccc03c03d6be300f00f,0x5500553333005533333333005533333333333300005555300f07f333307f07f00f00f333300f00f00f00f300f00f]
def h3b6 : Array Nat := #[0x55005533330055333333330055333300f00f3333333300005555300f17f333324f07f00f00f333300f00f00f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc33c33c33c33c01554cccc13c33ccccc43c33cc33c33ccccc33c33c33c33d06a,0x55005533330055333333330055333333330000154cccccccc030cf0cf,0x1540154cccc0154cccccccc0154ccccccccc03c03c0154ccccccccc33c33cc33c33d23e,0x1540154cccc0154cccccccc0154c33c03ccccccccc00154c03c1fcccccccccc03c03d256,0x5500553333005533333333005500cccccccc0154033333333300f00f,0x55005533330055333333330055333300f00f33333333000555300f07f333307f00f333300f00f300f00f,0x550055333300553333333300553333333333300f0cf00f0cf00005555333304f04f0cf0cf33332cf2cf0cf0cf30cf0cf30cf0cf,0x5500553333005533333333005533300f0cf00f00f3333333300005555300f07f333307f07f00f00f333300f00f00f00f300f00f,0x5500553333005533333333005533333333333300f0cf0055333304f0cf333330cf0cf30cf0cf,0x1540154cccc003cf55333333330055333300f2cf3333300f00f00005555300f0ef33330ef0ef00f00f300f00f333300f00f00f00f,0x5500553333005533333333005530cf00f3333333300055300f07f3333333300,0x5500553333005533333333005530cf00f3333333300055500cccccccc0,0x55005533330055333333330055333300f0cf00f00f3333333300055300f07f333300f00f07f00f33330ccc00f003c,0x1540154cccc0154cccccccc0154cccc03c33c03c03ccccccccc001554c03c5fccccc3bc03ccccc03c03c03c03d7120ccc00f003c,0x154004af55333300f04f0055333330069a3c0154ccc13c03c13c13ccccccccc00015554c13da3ccccc3bda3c13c13cccccaee0ef04f04f304f04f,0x550055333300553333333300553333333300f0cf33330055333332cf2cf33330ef10f32cf2cf,0x1555427c0fc2fc27d5427c3fc3fc27c0fc0fc0fc0fd5427c2fc2fc2fc0fc0fc0fc0fc03f05509f0bf03f0df2cf0df0df03f03f03f03f00fc003f03f03f555509f0df33f03f03f03f03f2af1ef0df0df00fc064f003f03f03f03f0df0df0df0df03f0df0df,0x55005533330055333333330055333300f0cf3333333300555300f07f333307f00f333300f00f300f00f,0x1555427c0fc2fc27d5427c0fc3fc27c03f05509f0bf0bf0bf00fc003f03f03f5509f0bf03f0df0cf0df0df03f03f03f03f03f03f03f03f03f03f03f03f555509f0df17f03f03f03f03f17f17f0df0df03f03f03f03f2af62f0df0df03f03f03f03f0df0df0df0df03f0df0df,0x5500553333005533333333005533300f0cf00f00f3333333300005555300f07f333307f07f00f00f333300f00f00f00f300f00f,0x55005533330055333333330055333300f0cf00f00f33333333005530cc03c003c333300f00f07f00f3333300f00f,0x55005533330055333333330055333300f0cf00f00f33333333005530cc03c003c3333333300f00f00f00f300f00f,0x5500553333005533333333005530cf00f3333333300550033333333300f00f,0x55005533330055333333330055333300f00f3333333300055300f07f3333333300f00f300f00f,0x55005533330cf04f0055333333330055333304f0cf3333333300005555304f07f333307f07f04f00f333300f0ef00f04f333304f00f04f00f,0x555005533330055333333330055333326f2cf3333333300005555326f07f333307f07f00f10f333300f24f00f26f33331cf00f10f00f,0x1555427c77c77c27d55427c3fc27ce7ed3d87ce7c27c77c77c27d5427c3fc3fc3fc2fe27e27d9bc0ff05509f0ff0ff0ff20f0ff31f31f03fc00ff0ff0ff555509f39f33f09f09f1df1df2af1ef15f2df09f39f64f0ff0ff0ff0ff0df6df0df39f0ff0ff0ff0ff15f0df15f0df,0x5500553333005533333333000b3d554cccc43c6bcc6bc43cc6bcb3c0154ccccccccccccc6bc6bd10a,0x550055333300553333333300555333310f1af300f00f33332cf1af00553333333310f1af333331af1af,0x15540154cccc6bc1fc003cf5533300f1af00f00f33330055333300f2cf3333300f00f00005555300f0ef33330ef0ef07f07f300f00f333300f00f00f00f,0x5555509f0bf0bf09f81f2df5509f0ff027ce7ed3c27c77c77c27d5427c2fc2fc2fc37cb3c2fc2fc2fc2fc0bf05509f0bf0bf0bf0df2cf20f0bf0bf0bf03fc00bf0bf0bf555509f0df1ef09f09f0bf0bf1ef1ef2df2df027c064f00bf0bf0bf0bf0df0df0df0df0bf0bf0bf0bf0df0df0df0df]
def h3b7 : Array Nat := #[0x550055531af1af00553333333300f1af00553333333300f2cf3333005533331af1af07f04f310f07f33333333,0x555005533331af10f0055333300f1af33330055333300f2cf3333333300005555300f07f333307f07f04f10f333300f00f00f00f333300f00f00f00f,0x555005533331af10f0055333300f1af00f00f3333005532cf00f33333333005530cc03c003c33333333333300f00f00f00f,0x37d547bd540154cccc6bc43c6bc03d00a005531af00f3333005532cf00f33333333005500333333333333,0x5500003c0040e95554cccc03c6bc33c43c0154ccccc6bc1fc0154cccccb3c43cccc1fc1fc43c43d02200553333333304f04f1af1af33333333,0xdf001052551ef554ea240154c33c33c0154c6bc03ccccc0154c33c03ccccccccc0154c03c1fd8f2333333333333,0x55550055333304f0cf0cf04f0055333300f1af1af10f33330055333300f0cf0cf0cf3333333300005555300f07f333307f07f04f04f333300f00f00f00f333300f00f00f00f,0x1540154cccc0154cccccccc0154cccccccccccc000df0019525500f555a124c03c1fd8f2300f07f300f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc000df0018ce5555300f07f300f07f300f00f300f00f,0x5500553333005533333333005533333333333300037d554cccc1fc03cc03c1fcc03c03cc03c03d26e,0x1540154cccc0154cccccccc0154cccccccccccc000df55533330ef00f300f0ef5a68c03c03d69e00,0x154004af555333300f04f0055333331af1af0055333333304f00f04f04f3333000f3c0053795554cccc3bc3bc13c13cc13c3bcc13c3bd62e304f04f,0x1540154cccc0154cccccccc0154cccccccc13c03ccccc0015f057f954ccccc13c3bcc13c3bd676304f04f,0x1555477c0fc2fc77d542fc0fc3fc3fc03f0550bf0bf0bf0bf00fc003f03f03f550bf0bf03f03f03f03f00fc0fc0fc0fc0fc0fc0fc0fc0fd55542fc2fc0fc0fc5fd2bc37c37c0fc37cabd93a03f0df2af69680fc37c37da5e03f0df0df,0x1555477c0fc2fc77d542fc0fc3fc3fc03f0550bf0bf0bf0bf00fc00fc0fc0fc0fd542fc2fc0fc0fc003f03f03f03f03f03f03f03f03f55550bf0ff03f03f17f3cf0df0df0003f0df2af69c80fc37c37da7603f0df0df,0x1540154cccc0154cccccccc0154cccccccccccc000df0018b6555533330ef07f00f00f300f0ef300f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc000df069c954cccc00c03c03cc03c03d69a,0x55551df03f0bf1df551df03f77f78f00fc015477c2fc2fc2fc03f0000fc0fc0fd5477c2fc0fc0fc0fc0fc0fc57c97c57c57c0fc0fc0fc0fc0fc0fc0fc0fd555477c77c0fc0fc5fce1e0df15f03f15f2af03f00abc003f0037c003f15f15f,0x5500553333005533333333005533333333333300005555333307f07f00f00f300f07f333300f00f00f00f300f00f,0x550055333300553333333300555333300f00f3333333300005555333307f07f00f00f333307f07f00f00f333300f00f00f00f300f00f,0x550012bc10b255533300f04f04f00f0055333331af1af00553333333300f00f3333000f3c0053195554c13c3bcc13c3bcc13c3bd646333304f04f04f04f,0x5500055333304f00f0055333333330055333333333333000f7d54c13c1fcc13c1fcc13c3bd65e3333,0x1540154cccc0154cccccccc0154cccccccccccc0000f55500300f07f300f00f333300f00f,0x555548f02fd23d542fc0fc3fc3fc03f0550bf0bf0bf0bf00fc003f03f03f55f3cf0df60f42c9542fc2fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fd55543fc03cf3d23c03ec3d9a603f0df62f03f0df0df03f03f03f03f0df0df0df0df,0x15554020f550bf03f0ff0ff00fc1542fc2fc2fc2fc03f003f03f03f03f550bf0bf03f03f03f03f03f03f03f03f03f03f03f03f03f03f55550ff00f3cf0003f0df62f03f0df0df03f03f03f03f0df0df0df0df,0x1540154cccc0154cccccccc0154cccccccccccc000df0018865555300f07f300f07f300f00f333300f00f00f00f,0x1540154cccc0154cccccccc0154cccccccccccc000df55300f07f00300f00f3333,0x1555427c2fc27d87c9bc9bd87d5427c0fc77c27c03f05509f0bf0bf0bf00fc003f03f03f5509f0bf03f03f03f03f03f03f03f03f03f03f03f03f03f03f555509f26f17f09f26f17f03f005fc003f0037c003f03f03f03f0df15f0df15f,0x55005533330055333333330cf10f00f04f43880154cccccccccccc000df001856555533330ef07f00f00f300f0ef300f00f333300f00f00f00f,0x1540154cccc0154cccccccc0154cccccccccccc000df0017fa5555300f07f300f07f333300f00f00f00f333300f00f00f00f,0x5500553333005533333333005533333333333300005555304f07f304f07f304f0ef304f04f,0x1540154cccc0154cccccccc0154cccccccccccc01554ccccd47eabcd47d43cd47f2bd3aa]
def h3b8 : Array Nat := #[0x1540154cccc00072954cccccccc01554ccccccc1fa05a81820668c122054800015554cccd0fc3bc03c1fcc1fa3428c1b230c94123066897a,0x1540154cccc0154cccccccc0154cccccccccccc00154ccccc13c93d60e304f24f00,0x5500553333005533333333005533333333333300005555333317f07f00f04f304f24f304f24f304f04f,0x1540015f553333005533333333005533333333333300555333300304f24f5858c13c13d60e,0x1540154cccc0154cccccccc0154cccccccc13c13ccccc00154ccccc13c93cc13c93d676304f04f,0x5500553333005533333333005533333333333300005555333307f07f00f04f304f07f333300f24f00f04f304f04f,0x5500553333005533333333005533333333333300005555333317f07f00f04f333324f07f04f00f304f1cf304f04f,0x55005533330055333333330055333304f04f3333333300005555333307f07f00f04f333307f07f04f00f333300f1cf00f04f304f04f,0x1540154cccc0154cccccccc0154cccccccccccc01554c33c13cccccc33c33cc33c33d32e,0x1540154cccc0154cccccccc0154cccccccccccc0154c13c1fcc13c1fd5c6333300,0x55005533330055333333330055333333333333005500304f07f3333304f04f,0x5500553333005533333333005533333333333300005555304f07f304f07f333300f0ef00f04f304f04f,0x1540154cccc0154cccccccc0154cccccccccccc0154c13c1fd7b6304f07f3333304f04f,0x1540154cccc0154cccccccc0154cccccccccccc01554c13c1fc00ccccc13c13d5c6,0x1540154cccc0154cccccccc0154cccccccccccc0154c13c1fcc13c1fcccccc13c13d656,0x550055333300553333333300553333333333330000555533330ef07f00f04f304f0ef333300f0ef00f04f304f04f,0x550055333300553333333300553333333304f04f333300005555333317f07f00f04f304f24f333300f24f00f04f304f04f,0x1555427c0fc77c27d5427c0fc77c27c9bc9bc0005509f77f1df66f03f03f03f03f03f03f03f03f5509f31f03f03f00fc003f00fc0fc0fc0fc0fd555427c27c0fc0fc5fc5fc57c57c0000fc0fc0fc0fd07d33c57c57c0fc57c57d5ae,0x1540154cccc0154cccccccc0154cccccccccccc33c33c33c33c001554cccc13c33ccccc43c33cc33c33ccccc33c33c33c33d202,0x1540154cccc0154cccccccc0154cccccccc000553333333300c33c33d2b2,0x1540154cccc0154cccccccc0154ccccccccc13c13c0154ccccccccc33c33cc33c33d2e2,0x5500057d54cccc0154cccccccc0154cccc033330055333300ccccc13c13d312,0x5500553333005533333333005533333333333304f0cf00555333304f0cf333330cf0cf30cf0cf,0x550055333300553333333300553333333304f04f333300555333307f04f304f07f333300f00f304f04f,0x550055333300553333333300553333333304f04f3333000555333307f04f304f07f333324f04f304f04f,0x1540154cccc0154cccccccc0154ccccccccccc13c33c13c33c00015554cccc13c13c33c33ccccc7d21e3833c33cc33c33d2b230cf0cf,0x1540154cccc0154cccccccc0154ccccccc13c33c13c13ccccc00015554cccc1fc1fc13c13cc13c1fd312333324f24f04f04f304f04f,0x5500553333005533333333005533333333333304f0cf0055533333333aaf51f309c853a30a884da,0x55005533330018fd54cccccccc0154cccccccc3020968c22a07f0000555533330ef0ef00f07f307f0ef307f0ef333300f25e803c1e2,0x1540154cccc0154cccccccc0154ccccc33c13ccccc0154ccccc13c1fd57e333300,0x1540015f5533330055333333330055333330cf04f333300005555333307f07f04f04f00cccc93c93c13c13c0,0x550055333300553333333300553333333304f0cf04f04f33330055333304f04f07f04f304f07f33330ccc04f013c]
def h3b9 : Array Nat := #[0x550055333300553333333300553333333304f0cf04f04f3333000553333304f24f333304f04f24f04f0ccc04f013c,0x1540154cccc0154cccccccc0154cccccccc13c33c13c13ccccc01554cccc3bc13cc13c93ccccc13c13c03c03d69e0ccc04f003c,0x550055333300553333333300553333333304f0cf04f04f3333000555333304f04f07f00f304f07f333324f04f0ccc04f003c,0x1540060f553333005533333a9f68f00553333333304f04f333300005555333324f0ef04f04f33330ef24f04f04f304f24f304f04f,0x1540154cccc0154cccccccc0154cccccccc13c33ccccc00154ccccd4fc93ccccc03c03cd4fcb6a,0x555520f03f0bf20f5520f31f31f20f03f03f03f03f5531f0bf0bf0bf03f03f03f03f00fc155483c2fc0fc0fc0fc0fc0fc57ce3c57c57c03f000fc0fc0fcb7c2d2555520f20f03f03f33f1ef0df15f03f15f2af00fc02af003f03f03f03f0df4cf0df15f03f15f15f,0x550055333300553333333300553333333304f0cf333300055333307f00f304f07f3333304f04f,0x550055333300553333333300553333333335f8ef3333000555333307f00f335f07f333300f00f335f35f,0x555520f03f31f20f5550bf03f0ff0ff55fa2f000550bf0ff0ff0ff03f03f03f03f03f03f03f03f60f83f550bf0ff03f03f00fc003f03f0e3c57c57c0fc0fc0fc0fd55542fc3fc0fc0fc5fd8bc57c57c0000003f03f03f03f41f4cf15f15f03f15f15f,0x15554a7c0fddfca7d542fc0fc3fc3fc03f0550bf0ff0ff0ff00fc003f03f03f550bf0ff03f03f03f03f03f03f03f03f03f15f59f15f15f03f03f03f03f55550bf0ff03f03f17f62f0df15f03f03f03f03f2af17f15f15f03f15f2af03f03f03f03f15f15f0df4cf0df15f69795e603f15f15f,0x15554a7c0fddfca7d542fc0fc3fc3fc03f0550bf0ff0ff0ff00fc00fc0fc0fc0fd542fc3fc0fc0fc003f03f03f03f15f59f15f15f03f03f03f03f55550bf0ff03f03f17f62f0df15f000fc015f03f15f2af03f03f00fc57c57c37d33c15f69d95fe03f15f15f,0x55005533330055333333330055333333304f0cf04f04f333300005555333307f07f00f04f304f07f333300f24f00f04f304f04f,0x550055333300553333333300553333333304f0cf04f04f333300055333304f04f07f00f30cc13c003c3333304f04f,0x550055333300553333333300553333333304f0cf04f04f333300055333330cc13c003c333304f04f00f00f304f04f,0x5500057d54cccc0154cccccccc0154cccccccc13c33c13c13ccccc01554ccccc3304f004f0cccc13c13c93c13d616304f04f,0x550055333300553333333300553333333304f0cf04f04f333300555333304f04f07f04f30cc13c013c3333304f04f,0x15555483c0fc2fc2fd57ce3d5483c0fcc7c83c05531f0bf0bf0bf03f03f03f03f2df38f03f03f03f03f5520f0bf03f03f03f38f15f00fc00fc0fc0fc0fd5483c2fc0fc0fc00000fc0fc0fc0fc0fc57c57d48e,0x5500057d54cccc0154cccccccc0154ccccc33c13ccccc0154cccc00ccccc13c13d57e,0x550055333300553333333300553333333304f04f3333000553333304f07f333324f04f304f04f,0x550055333300553333333300553333333304f04f33330055333307f04f304f07f3333304f04f,0x55005533330cf04f00553333333300553333333304f0cf333300005555333307f07f04f04f304f07f333300f0ef00f04f333304f04f04f04f,0x5500553333005533333333005553333333304f04f333300005555333307f07f00f04f333307f07f04f00f333300f24f00f04f304f04f,0x550055333300553333333300553333333304f04f333300005555333307f07f00f04f333307f07f04f00f333300f1cf00f04f304f04f,0x55005533330055333333330055530cf04f333304f04f333300055333307f00f33333333304f04f,0x55005533330055333333330055530cf04f30cf04f3333005533333333333300,0x1540154cccc0154cccccccc01554cccc13c33c13c13cc33c13ccccc0154cccccccc13c13c1fc13d57e33330ccc04f013c,0x55005533330055333333330055530cf04f333304f0cf04f04f333300055333304f04f07f00f333333330ccc04f003c,0x550055333300553333333300555333304f04f333304f04f333300005555333307f07f00f04f333307f07f04f00f333300f1cf00f04f304f04f,0x5500553333005533333333005533333333333300005555333307f07f00f04f333307f07f04f10f333300f0ef00f10f333300f04f00f04f,0x550055333304f0cf00553333333300553333333304f04f333300005555333307f07f04f04f333307f07f04f04f333300f1cf00f1cf333304f04f04f04f,0x55000553333005533333333005533333333333300005555304f07f304f07f333300f0ef00f04f333300f04f00f04f,0x550005533330055333333330cf44f00553333333304f0cf333300005555333307f07f00f04f304f07f333300f24f00f04f333300f04f00f04f]
def h3b10 : Array Nat := #[0x55005533330cf04f005533333333005533333333333300005555304f07f304f07f333300f0ef00f04f333300f04f00f04f,0x5500555333300553333333300553333333304f0cf333300005555333307f07f00f04f304f07f333300f24f00f04f333300f04f00f04f,0x1555427c0fc77c27c9bce7d5427c77c77c27c0fc0fc0fc57c9bd67c57d5427e27c77d9bc0fc0fc0fc0fc03f05509f31f03f03f03f03f03f03f00fc003f03f03f555509f09f03f03f33f1ef15f15f03f15f2af03f15f2af03f03f03f03f0df4cf0df15f03f03f03f03f15f15f15f15f,0x1540154cccc0154cccccccc01554c33c13ccccc43c33ccccc33c33c00154cccc33c33c13c33ccccccccccccc33c33c33c33d202,0x15401554cccc6bc1fc0063f0444954ccccccc1fc6bc6bc1fc0154cccccccc3920de8c36207f0000555533330ef0ef07f07f307f0ef307f0ef33331cf25e873c1e2,0x15555483c0fc2fc83e07cb7d5483cc7cc7c83c0fc0fc03f0ea80ba5531f0bf0bf0bf03f03f03f03f8ff81f00fc15483c2fc0fc0fc0fc0fc0fc0fcb7ce3c03f000fc0fc0fd17defcb7e3fd112555520f20f03f03f1ef1ef2df2df03f2df1ef00fc02af003f03f03f03f0df4cf0df5af03f03f03f03f25f15f25f15f,0x550055530cf0cf00553333333310f1af00553333333304f0cf33330005533330cf0cf07f04f304f07f33333333,0x550055533330cf04f00553333333304f1af00553333333304f0cf333300005555333307f07f04f04f304f07f333300f0ef00f04f333304f04f04f04f,0x55000b7d554cccc33c13c0154cccccccc13c6bc1fc13c0154ccccc33c13ccccc0154ccccc3304f004f0cccccccc13c13c13c13d57e,0x55000b7d547bd54cccc33c13c33c13d12a0055333331af07f0055333330cf04f3333005533330033333333,0x5500553333005533333333005533333333333300005555333307f07f00f04f333307f07f04f10f333300f0ef00f10f333300f04f00f04f,0x550055333300553333333300553330cf0cf04f0cf333333330000555530cf04f333310f10f0cf0cf33330cf0cf0cf0cf30cf0cf,0x5500553333005533333333000553330cf0cf04f0cf333333330000555530cf04f333310f10f0cf0cf33330cf0cf0cf0cf30cf0cf,0x15400154ccc6bc1fc1fc6bc0063f55333333331af07f00553333333330f681fc00015554c1fc3bcc1fc3bccccc03c3bc03c1fccccc03ca6a00f07f,0x154002df5533330cf04f0055333333330055333330cf04f333300005555304f07f333307f07f04f04f333324f24f04f04f304f04f,0x550055333300553333333300055333304f0cf33333333005530cf04f333333330cf0cf30cf0cf,0x5500055333310f1af005533333333005533333333333300555310f07f310f07f333300f00f333300f00f,0x555509f0bf09f81f2df17f26f5509f1df1df09f03f03f03f03f26f17f5509f0bf0bf0bf03f03f03f03f00fc15427c2fc0fc0fc0fc0fc0fc0fc03f000fc0fc0fd555427cb7c7bc27c5fc7bc0fc0fc0fc0fce2a2af2df15f03f03f03f03f0df4cf0df2df03f03f03f03f0df15f0df15f,0x55005530cf0cf00553333333300553333333333330055304f07f0033333333,0x55005530cf0cf005533333333005533333333333300055500033333333,0x550005533330cf04f04f0cf005533333333005533333333333300550ccc04f013c304f07f333304f04f0ef04f3333,0x550005533330cf04f04f0cf0055333333330055333333333333005550ccc04f003c304f07f33330ef04f333304f04f00f00f,0x555509f03f1df09f5509f0ff09f0cf04f17f26f00fc09bc5509f0ff0ff0ff03f03f03f03f03f03f03f03f5509f0ff03f03f00fc003f03f03f55fbaf03f03f03f03f555509f04f62f09f03f03f03fb0f17f60f15f09f17f17f03f03f03f03f6df4cf60f5af03f03f03f03f6df15f60f15f,0x55550027d5427c3fc27c33c13c5fc9bc03f026f15427c3fc3fc3fc0fc0fc0fc0fc0fc0fc0fc0fd5427c3fc0fc0fc03f003f03f03f03f03f03f03f03f555509f04f62f000fc015f09f17f17f03f03f03f03f0df4cf0df3df03f03f00fc37c57c15f,0x55000553330cf04f04f0cf005533333333005533333333333300005555304f07f304f07f333300f0ef00f04f333300f04f00f04f,0x55005533330cf04f00553333333300553333333333330055304f07f304f07f3333333304f04f,0x550005533330cf04f04f0cf00553333333300553333333333330055304f07f30cc13c003c333304f04f00f00f3333,0x15400154cccc33c13c13c33c0154cccccccc0154cccccccccccc01554c13c1fcc3304f004f0cccccccc13c13c13c13d5c6,0x55005530cf0cf0055333333330055333333333333005500304f07f33333333,0x5500055333304f0cf0055333333330cf10f00553333333333330000555533330ef07f00f04f304f0ef333300f0ef00f04f333300f04f00f04f,0x55000555333304f0cf005533333333005533333333333300005555333317f07f00f04f304f17f333300f24f00f04f333300f04f00f04f,0x1540154cccc001554cccc5fc9bcc33c33c0154ccccccccccccd7db3c0154cccccccc33c33c3bc43d0e2344f24f3333]
def h3b11 : Array Nat := #[0x55000555333304f0cf0055333333330cf44f00553333333304f0cf333300005555333307f07f00f04f304f07f333300f24f00f04f333300f04f00f04f,0x154002df045c9554cccc33c13c13c33c0154cccccccc33d13c0154ccccc33c13ccccc0154ccccc3304f004f0cccccccc13c13c13c13d57e,0x555005530cf0cf005533330cf44f33330055333304f0cf04f04f33333333005530cc13c013c333304f04f07f04f33333333,0x17f04629549bd540154c33c33c0154cccc33d13c1fc13d15a3333005530cf04f33333333005500333333333333,0x55000b7c0047495554cccc43c33c6bc13c0154ccccc6bc1fc0154ccccd2fc43cccc1fc1fc43c43d1ba00553333333310f10f0cf0cf33333333,0x5500005555333304f0cf0cf04f00553333333304f1af0cf10f00553333333304f0cf0cf0cf333300005555333307f07f04f04f304f07f333300f0ef00f04f333304f04f04f04f,0x5555005530cf0cf0055333310f1af26f4bf3333005530cf04f3330cf0cf04f04f33330055333304f04f0cf0cf333333333333,0x17f0011ea551ef554f6240154c6bc6bc0154c6bc1fccccc0154d2fc43ccccccccc0154c43c1fd79a333333333333,0x5500055333304f0cf0055333333330055333304f04f3333333300005555333307f07f00f04f333307f07f04f00f333300f1cf00f04f333300f04f00f04f,0x5550000555530cf0cf00553333333310f1af1af10f00553333333304f0cf0cf0cf333300553330cf0cf07f04f304f07f33333333,0x5550000555530cf0cf00553333333310f1af1af10f00553333333304f0cf0cf0cf3333000553330cf0cf07f04f304f07f33333333,0x555500005555333304f0cf0cf04f04f0cf0cf04f0055333310f1af1af10f333304f1af0cf10f0055333304f0cf0cf0cf333304f0cf0cf0cf333300005555333304f04f0cf0cf07f07f04f04f333304f04f0cf0cf07f07f04f04f333300f0ef00f10f333304f04f04f04f,0x555500055530cf0cf0055333304f1af0cf10f33330055333304f0cf0cf0cf333333330055304f07f3330cf0cf07f04f33333333,0x555500055530cf0cf0055333304f1af0cf10f33330055333304f0cf0cf0cf333333330055304f07f3330cf0cf07f04f33333333,0x55005533330cf04f005533333333005533333333333300005555304f07f333307f07f04f00f333300f0ef00f04f333300f04f00f04f,0x5500553333005533333333005533333333333300005555310f0ef333307f0ef04f00f333300f0ef00f04f310f1ff,0x550055333300553333333300553333333353f53f333300005555333307f0ef00f10f333307f0ef04f00f333300f24f00f04f31ff1ff,0x550055333300553333333300551ff5527a3333351fadf351f73f005533333333333300,0x1540154cccc0154cccccccc01554cccccccc55a12dab7c7fcc27e0a580154cccccccccccc43c43c03c03d57a0ccc1ff003c,0x550005d25533330005533333114848200555333333330e185a2333198818e05d84e200005555333368f0ef04f10f33330ef65f04f44f31988d1631388986,0x550055333300553333333300555333333330a7852e33330a5852a00005555333307f0ef00f10f333307f0ef04f00f333300f24f00f04f31ff1ff,0x550055333300553333333300055533331ff1ff333382f82f33331cf1cf00005555333307f0ef00f10f333307f0ef04f00f333300f1cf00f04f31cf1cf,0x5500553333000553333333310f1af005533333333333310f10f00005555333307f0ef04f10f333307f0ef04f00f333300f0ef00f04f333304f1ff04f1ff,0x550005533331af10f005533333333005533333333333300005555310f0ef333307f0ef04f00f333300f0ef00f04f333300f1ff00f10f,0x5500055333300553333333300553333333333330000555533330ef0ef00f10f33330ef0ef04f00f333300f0ef00f04f333300f1ff00f10f,0x15400015554cccc43c6bc6bc43c00015554cccc43c6bc6bc43cc6bc6bc0154cccccccc43c2361af1d48cccc85a051846a1b680154ccccccc43c6bc6bc3bc43d586310f0ef3333,0x154005af0012925555333310f1af1af10f00005555333310f1af1af10f00553333333310f0db86bc79a333321c815e12086f20000555533330ef0ef10f10f33333398ab244f44f,0x15400015554cccc43c6bc6bc43c00015554cccc43c6bc6bc43ccccc43c6bc6bc43c43c6bc6bc43d30a4aa80154cccccccd4fc256a9f1db8cccc43c24e1af1da800015554cccc3bc3bc43c43ccccc43c43c6bc6bc3bc3bc13c03ccccc43c43c6bc6bc3bc3bc03c13cccccd7caca35f44f,0x550016bc004b095554cccc43c6bc6bc43c00015554cccc43c6bc6bc43cc6bc6bc0154cccccccc43d2fc6bd2fccccc43d2fc6bd2fc0154ccccc43c3bcccc43c6bc6bc3bc13d5863333,0x5500553333005531af1af31af1af0055333333333333005533333333003333,0x550023fd54cccc6bc43c00154ccc6bc43c43c6bcc6bc6bc0154cccccccccccc00015554c43c3bccccc3bc3bc13c43cc43c3bccccc13ca8204f10f,0x550005533330055333310f1af1af10f31af1af005533333333333300553333333310f10f00f10f0ccc10f043c3333]
def h3b12 : Array Nat := #[0x55005533331af10f005533331af10f3333005533333333333300005555310f0ef333307f0ef04f00f33330ef0ef00f04f333300f1ff00f10f,0x5500553333005533331af10f333310f1af00553333333333330000555533330ef0ef04f10f33330ef0ef04f00f33330ef0ef00f04f333304f1ff04f1ff,0x5500553333005533333333005533333333333300005555333307f0ef00f10f333307f0ef04f00f333307f24f00f04f333300f1ff00f1ff,0x550055333399f2bf00553333c5fc4f33330055333397f97f3333333300005555350f1cf333307f2bf04f00f33330ef74f00f04f333307f1ff00f10f,0x5500553333005533333333005533333333333300097c004f295473d5568a9350f1ff350f2bf31cf1cf31cf1cf,0x1540154cccc00258954cccccccc00154ccccccc9aa13c8a4a06693f231b48702000055264955564933330ef252803c73cc4f217e8c8ea24693b2306681e2,0x1540154cccc0154cccccccc0154cccccccccccc0001547fd556909333307f1ff00f1cf350f2bf350f74f31ff1ff,0x29f54f54f29f00534cccc01553d3333333300501f4cccccccccccc000154ccce5bc7fc7fc7fcd43cafd28a350f74f4a08c7fc7fd27a,0x1540027c954cccc0154cccccccc0154cccccccccccca560b18a5e0af93f20055288956a28ccccc89a23893aa31408652313e864a,0x5500553333005533333333005533333333333300005555333317f1ff00f1cf333324f2bf00f1ff307f35f310f10f,0x5500553333005533333333005533331ff1ff3333333300005555333307f1ff00f1cf333307f2bf00f1ff333300f35f00f1ff310f10f,0x1540154cccc003cf55333333330005533300f2cf43f00f3333300f00f0000555532cf00f33330ef1ae81fc73cc03c03d34a300f00f,0x550055333300553333333300553333333333330000555532cf00f333307f2bf04f1cf300f00f300f00f,0x1540154cccc0154cccccccc0154cccccccccccc0154cb3c03d3923333300f00f300f00f,0x1540154cccc0154cccccccc00154cccd0fc03ccccccccc01554cb3c03cccccc03c03d336300f00f,0x5500553333005533333333005533333333333300005555333317f00f00f00f333324f2bf04f1cf300f00f300f00f,0x5500553333005533333333005533333333333300005555333307f00f00f00f333307f2bf04f1ff300f00f300f00f,0x550022bd54cccc0154cccccccc0154ccccc75a9ff33332c4851a00005555333324f56f04f56f343f56f307f35f333304f079813c97e,0x5500553333005533333333005533333333333358f07f00f00f55e800154cccccccd5bd0fc93c13d60e307f35f0ccc00f013c,0x1540154cccc003cf553333333300005555307f00f33330ef07f07f1cf300f00f0055333300f2cf3333300f00f333300f00f00f00f,0x1540154cccc0154cccccccc0154cccccccccccc03c03c03c03d57a00055333300f2cf17f00f3333300f00f0ccc00f003c,0x5500553333005533333333005533333333333300f00f00f00f51e8001554cccc5fc03ccccc93c13cc03c03ccccc03c03c03c03d78a,0x555531f03f0bf31f550bf0ff0ff0ff03f03f03f03f5550bf0bf0bf0bf0df0df03f03f03f03f4af0b6803f005550bf0bf03f03f0df0df03f03f03f03f9ef0b4803f0000fc0fc0df037c55550bf0bf03f03f33f0df0df0df03f03f03f03f2af190857c9da00fc025f003f0df0df03f0df0df,0x555578f03f77f78f550bf03f0ff0ff00fc1542fc3fc3fc3fc0fc0fc0fc0fc0fc0fc0fc0fd542fc3fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fd07d07d07d07d50255550bf0ff03f03f17fb2f26f15f00fc026f000fc0fc0fc184857c9d203f41f41f03f41f41f,0x555578f03f54f78f550bf03f0ff0ff00fc1542fc3fc3fc3fc0fc0fc0fc0fc0fc0fc0fc0fd542fc3fc0fc0fc03f000fc0fc0fc0fc0fc0fd07d07d07d07d51a55550bf0ff03f03f17f6df26f15f00fc026f003f03f03f03f2af18a857c9de03f41f41f03f41f41f,0x1540154cccc0154cccccccc0154ccccccccccc03c03c03c03d57a00005555333317f00f00f00f333324f2bf04f1ff300f00f300f00f,0x29f54f54f29f00534cccc01553d3333333300501f4cccccccccccbea0c98bf20c795920000501f5613d333396f2bf1ff2bf3334bba1a88dda2bf08496a2928a30c9833e30c78336,0x1540154cccc0154cccccccc0154cccc03c03ccccccccc03c03c03c03d57a00055333317f00f3333300f00f300f00f,0x5500553333005533333333000553333333357f2bf8cccc03c03c03c03d57a000553333333324f04f300f00f300f00f,0x550055333300097d54cccccccc01554cccc03c03cccccc520ba8cccc03c03c03c03d57a00555333333331968a0e300f00f300f00f,0x1540154cccc0154cccccccc001554cccd0fc03ccccc1fd63ccccc03c03c03c03d57a00555333300f00f3333300f00f300f00f,0x1555483c0fcc7c83d5542fc3fc3fc3fc37c37c0fc0fc0fc0fd2bdefd542fc3fc3fc3fc0fc0fc0fc0fc055550bf0ff03f03f2ff3cf3cf3cf03f03f03f03f2ff7df63fb8f03f0df25f00fc025f0550bf0ff03f03f03f03f03f03f03f0df25f4b4803f003f25f25f]
def h3b13 : Array Nat := #[0x550055333300097d54cccccccc00015554cccc3bc03c03c03ccccc3bc1fc1fd63cc03c03c0154ccccccccc03c03d2ea300f00f,0x15401554cccc1fc3bc001ef555333307f0ef3330ef07f0ef07f4fe800015554cccc3bc1fc1fc3bcc1fc03cc1fc1fc0154ccccccccc1a16c8c7aa0ef33331cf1cf078897a,0x5550055333307f0ef0007bc142a55533300f07f0ef00f333300f0ef00005555307f00f33330ef07f07f0ef300f00f0055333300f2cf3333300f00f333300f00f00f00f,0x55000553330ef07f0ef07f00005555307f07f307f07f000bfd54cccc1fc3bccccc1fc3bccccc3bc03c1fc3bc0154cccccccccccd0fc03c73c73cc7c20ef,0x55000cf20015025555333392f00f01683bc01554ccccc1e207e80031e954cccccccc3bc03c73c73ccccc392306801554ccccc5fa19c8ccc1fa26a867229293f2320e8882,0x550012bc0054695554cccc3bc03c03c3bc0154ccccc1fc1fc002ff55333333330ef00f00f00f333307f0ef00553333300f0ef3333343f0ef,0x550012bc00552954bfd553ae9333300f0ef0ef00f00f0ef408953200553333307f07f000bfc14a2553333300f07f33307f0ef07f0ef4fe80154ccccc03c3bd3623333343f0ef,0x55550055300f00f0055333392f0fc81fc3bccccc008af5533330ef00f00f00f333300f00f333300555300f43f33300f00f43f43f3333343f43f,0x155540154c03c03c0154cccc3bc1fc1fc3bccccc002ff5533330ef00f00f00f333300f00f33330055300f0ef33333333343f0ef,0xf3c00558954bfd553de90055300f00f005533330ef07f00f0ef07f0ef46e94ea3333000bfd54c03c1fcccc03c03c1fc3bccccc0154c03c3bd37a33333333343f0ef,0x55550055307f07f0055307f07f33307f0ef07f0ef000bfd54cccc3bc03c1fc3bc1fc3bd0f25168cccccccc0154ccce4bc73c03c03cccccccccc8520ef,0x5500553333005533333333005533333333333300f00f00005555333307f00f00f00f333307f2bf04f1ff333300f00f00f00f300f00f,0x55005533330055333333330055333300f00f3333333300f00f00005555333317f00f00f00f333324f2bf04f1ff333300f00f00f00f300f00f,0x1540154cccc0154cccccccc0154cb3c03ccccccccc03c03c03c03d5c200055333300f2cf07f00f333333330ccc00f003c,0x55005533330055333333330055333300f00f3333333300f00f00005555333307f00f00f00f333307f2bf04f1ff333300f00f00f00f300f00f,0x55005533330007bd54cccc03c03ccccc00154cccc3bc03cccccc03c03c0154ccccccccc03c03ccccc03c03c03c03d57a,0x5500553333005533333333005533333333333300005555333317f00f04f00f333324f00f04f2bf333300f04f00f1cf333304f00f04f00f,0x5500553333005533333333000553333333333330000555532cf00f333307f2bf04f1cf333300f00f00f00f300f00f,0x5500553333005533333333000553333333357f82f333300005555333307f00f00f00f333307f2bf04f1cf333300f00f00f00f300f00f,0x1540154cccc0154cccccccc00154cccccccd5fcb2e333300f00f00005555333317f00f00f00f333324f2bf04f1ff333300f00f00f00f300f00f,0x1540154cccc0154cccccccc00154cccccccd5fcb5e333300f00f00005555333307f00f00f00f333307f2bf04f1ff333300f00f00f00f300f00f,0x1540154cccc001ef0576954cccccccc03c3bc00154cccccccc3bc1fcc03c03c0154ccccccccc03c03ccccc03c03c03c03d57a,0x1540154cccc0154cccccccc001554cccc03c03ccccd5fcb76333300f00f00005555333307f00f00f00f333307f2bf04f1ff333300f00f00f00f300f00f,0x550055333399f2bf00553333333300553333333333330000555532cf00f333307f2bf04f1cf333300f00f00f00f333300f00f00f00f,0x5500553333005533333333005533333333333300005555333317f00f00f00f333317f2bf04f1ff333300f00f00f00f333300f00f00f00f,0x550055333300553333333300553333333333330000555530cf00f333307f04f04f04f333300f00f00f00f300f00f,0x55005533330055333333330055533333333333300f00f00005555333317f00f00f00f333324f04f04f04f333300f00f00f00f300f00f,0x1555427c0fc2fc27d5427c0fc77c27c03f005509f0bf0bf0bf00fc0003f03f03f5509f0bf03f03fccf26f03f03f03f15f25f2af15f03f03f03f03f03f03f03f03f555509f0bf03f03f17f26f0df26f03f25f15f03f03f03f03f2af15f15f0df03f03f03f03f0df41f0df26f03f15f15f,0x1540154cccc0154cccccccc01554c33c03ccccc3bc13ccccc03c03c00154cccc03c33c5fc03ccccccccccccc03c03c03c03d78a,0x55551df03f0bf1df550bf03f0ff0ff00fc1542fc2fc2fc2fc03f000fc0fc0fd5542fc2fc0fc0fc37c37c0fc0fc0fc2af15f03f03f03f03f2af15f03f03f03f03f0df0df55550bf0bf03f03f17f0df0df0df00fc015f003f03f03f03f2af15f15f15f03f03f03f03f0df0df0df0df03f0df0df,0x550055333300553333333300555333300f00f333324f04f333300f00f00005555333317f00f00f00f333324f04f04f04f333300f00f00f00f300f00f,0x55005533330007bd554cccc03c03ccccc3bc13c01554cccccccc03c3bcc03c03c0154ccccccccc03c03ccccc03c03c03c03d57a]
def h3b14 : Array Nat := #[0x550012bd54bfd54cccc03c3bc03c3bd68200553333304f04f00553333300f10f333304f0ef10f0ef50180154ccccc03c3bd26e33333333,0x550055333300553333333300555333300f00f333307f04f333300f00f00005555333307f00f00f00f333307f04f04f04f333300f00f00f00f300f00f,0x5500553333005533333333005533330cf0cf333333330000555533330ef00f00f00f33330ef00f04f04f333300f00f00f00f333300f00f00f00f,0x5500553333005533333333000553333333300f0cf00f2cf3333005533330ccc0cf043c33332cf2cf0ef10f32cf2cf,0x555520f03f0bf20f550bf0ff0ff0ff03f03f03f03f550bf0bf0bf0bf03f03f03f03f00fc1542fc2fc0fc37cb3ccfc37c0fc0fc0fc0fc03f02df003f03f03f0df0df55550bf2cf0df03f03f03f03f1ef2df15f25f00fc039f003f03f03f03f0df0df0df0df03f0df0df,0x1540154cccc0154cccccccc00154cccc03c33c1fc03ccccccccc01554cccc03c33c1fc03d8f2333307f04f333300f00f300f00f,0x1555477c0fc2fc77d542fc0fc3fc3fc03f0550bf0bf0bf0bf00fc003f03f03f550bf0bf03f0df0cf17f0df03f03f03f03f26f26f03f03f03f03f03f03f03f03f55550bf0cf0df03f03f03f03f2af26f15f26f03f03f03f03f2af5af15f41f03f03f03f03f0df0df0df0df03f0df0df,0x55005533330055333333330005533300f0cf07f00f333333330000555530cf00f333307f04f04f04f333300f00f00f00f300f00f,0x55005533330055333333330055333300f0cf33333333005530cf00f333307f04f3333300f00f,0x550055333300553333333300555333300f0cf33333333005530cf00f3333333300f00f300f00f,0x1540154cccc0154cccccccc001554c33c03ccccccccc0154c33c03d23e33333333300f00f,0x550055333300553333333300055333307f00f33333333005530cf00f333307f04f3333300f00f,0x5550055333300055333307f00f3333005533333333333300555304f00f3333300f00f333300f00f,0x154001554c03c03c0154cccccccc0154cccccccccccc0154c03c1fd256300f07f33333333,0x550055333300553333333300055333317f00f333333330000555533330ef00f00f00f33330ef04f04f04f333300f00f00f00f300f00f,0x550055333300553333333300055333317f00f333304f04f333300005555333317f00f00f00f333324f04f04f04f333300f00f00f00f300f00f,0x550055333300553333333300055333307f00f333304f04f333300005555333307f00f00f00f333307f04f04f04f333300f00f00f00f300f00f,0x550055300f00f0055333304f07f333300553333333333330055300f07f333307f07f33333333,0x5500553333005533333333000555333307f00f333304f04f333300f00f00005555333307f00f00f00f333307f04f04f04f333300f00f00f00f300f00f,0x5500553333005533333333000555333307f00f3333333300005555333307f00f00f00f333307f04f04f04f333300f00f00f00f300f00f,0x5500553333005533333333000555333317f00f333304f04f333300f00f00005555333317f00f00f00f333324f04f04f04f333300f00f00f00f300f00f,0x1540154cccc001ef05b29554cccc3bc03ccccc03c3bc01554cccc03c03cccccc03c03c0154ccccccccc03c03ccccc03c03c03c03d57a,0x5550055300f00f0055333304f0ef3333005533330ef00f333333330055300f17f333307f07f33333333,0x5fc16fa5526f550055300f00f0055333300f0ef10f0ef5b88cccc0154c03c43ccccc43c3bccccc0154c03c3bd22e333333333333,0x5500553333005533333333000555333307f00f333304f04f333300f00f00005555333307f00f00f00f333307f04f04f04f333300f00f00f00f300f00f,0x550055333300553333333300005555333317f00f00f00f333324f04f04f04f333300f00f00f00f00005555333317f00f00f00f333324f04f04f04f333300f00f00f00f300f00f,0x550012bc005d695554cccc03c3bc3bc03c03c3bd0165d080154ccccc13c13c0154ccccc03c43cccc13c3bc43c3bd4f60055333333330ef00f00f00f33333333,0x55550055300f00f005533330ef04f00f0ef10f0ef45896f633330055300f10f33300f00f10f0ef3333005533330ef00f00f00f333333333333,0x5fc005dc9549bd553ed90055300f00f40580154c13c13d16233330055300f10f45a8cccccccc0154c03c3bd20e333333333333,0x550055333300553333333300005555333307f00f04f00f333307f04f04f04f333300f1cf00f1cf000555333307f04f333307f04f33331cf1cf304f04f,0x55005533330055333300f00f33330000555533330ef00f00f00f33330ef00f04f35f333300f00f00f00f00055333317f00f33333333333300f00f00f00f,0x550055333300553333333300005555333307f00f26f00f333307f00f04f35f333300f04f00f1cf000555333307f26f333335f35f33331cf1cf310f10f]
def h3b15 : Array Nat := #[0x550055333300553333333300005555333307f00f00f00f333307f00f04f35f333300f00f00f00f00055333307f00f3333333300f00f300f00f,0x1540154cccc0154cccccccc00015554cccc33c33c1fc03c03c03d06a333307f00f04f04f333300f00f00f00f0005533330cf0cf07f00f33333333300f00f,0x55005533330055333333330000555530cf00f333307f04f04f04f333300f00f00f00f0055333300f0cf33333333333300f00f00f00f,0x550055333300553333333300005555333307f00f00f00f333307f04f04f04f333300f00f00f00f00555333300f00f333307f04f333300f00f300f00f,0x550055333300553333333300f04f0000555533330ef00f04f00f33330ef04f04f04f333300f1cf00f1cf00553333333324f04f3333333304f04f00f00f,0x55005533330cf04f0055333333330000555530cf00f333307f04f04f04f333300f00f00f00f00055333300f0cf33333333333300f00f00f00f,0x55005533330055333333330000555533330ef00f04f00f33330ef04f04f04f333300f35f00f44f00055333333333333333304f04f00f00f,0x550055333300553333333300005555333307f00f00f00f333307f04f04f04f333300f00f00f00f000555333300f00f333307f04f333300f00f300f00f,0x550055333300553333333300005555333307f00f04f00f333307f04f04f04f333300f1cf00f1cf000553333333307f04f33331cf1cf304f04f,0x550055333300553333333300005555333307f00f00f00f333307f00f04f35f333300f00f00f00f0005533333333333300f00f300f00f,0x55005533330cf04f0055333333330000555530cf00f333307f04f04f04f333300f00f00f00f0055333300f0cf33333333333300f00f00f00f,0x55005533330cf04f005533333333005530cf00f33333333005530cf00f33333333333300f00f,0x55005533330055333333330000555533330ef00f04f00f33330ef04f04f04f333300f1cf00f1cf0055333333330cf0cf3333333304f04f00f00f,0x55005533330cf04f00553333333300005555333307f00f00f00f333307f04f04f04f333300f00f00f00f00553333333307f04f3333333300f00f00f00f,0x550055333300553333333300005555333307f00f00f00f333307f04f04f04f333300f00f00f00f0055333300f00f333307f04f3333300f00f,0x1540154cccc0154cccccccc00015554cccc1fc03c13c03ccccc33c33c1fc13c13c13d202333300f1cf00f1cf0055333333330cf0cf07f04f3333304f04f,0x55005533330cf04f005533332cf2cf33330000555530cf00f333307f04f04f04f33330ef00f00f00f0055333300f0cf33333333333300f00f00f00f,0x550055333300553333333300005555333307f00f00f00f333307f04f04f04f333307f00f00f00f0055333300f00f33333333300f00f,0x5550055333300005555304f00f333307f04f04f07f005533333333333300f00f00f00f0055333300f04f3333333300f00f00f00f3333,0x550055333300005555333307f00f00f00f333307f04f04f07f005533333333333300f00f00f00f000555333300f00f333307f07f300f00f333300f00f,0x550055333300005555333307f00f10f00f333307f00f04f07f005533333333333300f00f04f0ef005533333333333307f1cf00f00f3333,0x1555483c0fc83c83d555483c3fc3fc3fccfcb7cb7db7c0fc0fc0fc0fcabc57c57cabd55dbc3fc3fc3fc0fc0fc0fc0fc015483c3fc3fc3fc0fc0fc0fc0fc0fc0fc0fc0fc97c97c97c97c0fc0fc0fc0fd55483c3fc0fc0fc0fc0fc0fc0fcabcabc0fc57c97c03f003f03f03f03f25f25f,0x1540154cccc0025f0017ba5555333307f00f26f00f333307f00f04f07f005533333333333300f00f04f1cf005553333333307f07f31cf07f333307f1cf,0x1540154cccc001ef0017d25555333307f00f00f00f333307f00f04f07f005533333333333300f00f00f00f005533333333300f00f333300f00f,0x55551bf09f09f1bf550bf09f09f64fb3f33f39f1bf09f09f1bf555509fb3f39f1bf09f09f0ff1ef03a857c37c27ce7ce7d542fc3fc27c3fc2fd9bd9bc6fc09f00ff09f0ff0ff0df0df00e857d542fc3fc27c3fddbc3fc83c83c09f00ff09f0ff09f0df0df00c8e7c0ff0ff0ff,0x1555546fc2fc2fc6fe8bdefd542fc3fc3fc378811a1bf20f20f1bf55550bf2cf0df1bf0bf0bf0bf1ef2df2df25f03fc039f0550bf0bf0bf0bf0df2cf0bf0bf0bf0bf02fc02fc2fc2fc2fc37c37c37c37d542fc2fc2fc2fc37cb3cc7c2fc2fc2fc0ff00bf0bf0bf0bf0df0df0df0df02fc2fc2fc37c37c37c37d42a,0x5550055333304f07f00005555304f00f333307f04f04f07f0055333300f10f3333333300f00f00f00f0055333300f04f3333333300f00f00f00f3333,0x5550055333304f07f0055304f00f33330055333300f10f333333330055304f00f3333333300f00f3333,0xdf552ff550055333310f07f10f00f5d480154c43c03d10a33330055310f00f33333333005532cf00f333333333333,0x550055333304f07f00005555333307f00f04f00f333307f04f04f07f005533333333333300f00f10f0ef005533333333333307f04f00f00f3333,0x55005533330000555533330ef00f00f00f33330ef04f04f07f0055333300f10f3333333300f00f00f00f005533333333333300f00f00f00f333300f00f,0x550055333300005555333307f00f00f00f333307f04f04f07f005533333333333300f00f00f00f00555333300f00f3333300f00f333300f00f]
def h3b16 : Array Nat := #[0x550055333300005555333307f00f04f00f333307f04f04f07f005533333333333300f00f10f0ef005533333333304f07f333307f0ef,0x1540154cccc43c1fc43c1fc00015554cccc1fc03c43c03ccccc1fc03c13c1fc0154cccccccccccc03c03c13c3bc0154cccccccccccc1fc73c03c03ccccc43d63c1fc3bd45a,0x1540154cccc0025f0018025555333307f00f26f00f333307f00f04f07f005533333333333300f00f04f1cf1cf07f5e4801554ccccccccc73c1fccccc73c73c1fc73d472,0x155546fc0fc83c6fd55542fc3fc3fc3fc7bc37c37c37c0fc0fc0fc0fc7bc37cb7cabd542fc3fc3fc3fc0fc0fc0fc0fc01542fc3fc3fc3fc0fc0fc0fc0fc0fc37c97c03f0550bf0ff03f03f03f03f03f03f03f0df1ef00fc00fc0fc0fc97c97c7bc7bd48a,0x55555520f03f20f20f33f0df2df1ef5520f03f20f20f03f15f15f5576f20f20f76f03f03f03f03f1ef15f15f25f15f2af42497ba03f03f03f03f5520f31f31f31f03f03f03f03f1ef0df25f25f03f03f03f03f00fc155483c83c0fc0fc0fc57cabc0fc0fc0fc57c57cabcabd51e00fc003f03f03f3df9ef,0x15555546fc0fc27c6fccfcb7c37c7bd546fc0fc27c6fc0fc57c57d546fc27c27c6fc0fc57c57c0fc0fc0fc57cabc57cabd546fd9bc27c6fc03f0037c00fc0fc0fc0fc03f05530f20f03f03f00fc00df003f03f03f03f00fc003f03f03f,0x15556bfd553b491bf03f0bf1bf0df1ef1ef0df0df1ef40e981a551bf03f20f1bf03f2df2df551bf0bf0bf0bf03f7df2ff42a803f03f03f551bf0bf0bf0bf03f0df4af03f03f03f03f00fc15483c2fc0fc0fc0fc37c7bc0fc0fc0fc0fc03f000fc0fc0fcf7d2bc7bc7bd4a2,0x155555427c37c37d5483c27c27c83ccfcb7c57c7bc83c27c27c83d5483c27c27c2fc7bce7c57c97cc3c27c27c2fcc3c27c27cc3d5483c2fc27c2fc7bc37c37c37ccfccfd1765b4883c2fc27c2fc83c2fcc7cc7c09f0550bf0df33f0bf09f0bf0df0df33f33f20f20f20f20f027c00bf0bf0bf,0x154e7d553d295509f39f39f551bf09f09f1bf33f102857c7bc5fccfd1a25ce86fc27c27c6fd55427ce7c9bc27c27c2fce7d93c9bccfc6fc27c27c6fd540bf0037c0cfc45181bf0bf09f0bf1bf0bf66f1bf027c1540bf00b7c0cfc453830f0bf09f0bf76f20f20f20f027c00bf0bf0bf,0x5539f554f9255427c37c37d546fc27c27c6fc7bc57c37c7bc5fc7bd1d25da86fc27c27c6fd5427c57c9bd0da027c27c2fc6fc27c27c6fd542fc37ccfd1761bf0bf09f0bf1bf0bf31f1bf027c1542fc37c7bd17e20f0bf09f0bf20f20f20f20f027c00bf0bf0bf,0x155555427cb7cb7d5427cb7c5fc27c27c6fcb7c7bc5fc7bd546fc27c27c6fccfc97c57cabc6fc27c27c6fc6fc27c27c6fd546fcc7c27c6fc7bc37ce7d33c6fcc7c27c6fc6fcc7cc7c6fc09f05520f20f09f20f33f25f0df0df20f20f09f20f20f20f20f20f027c020f31f31f,0x55551bf03f0bf1bf55003fc0fc0fc0fc0fd55542fc0bf0bf1ef037c37c0fc0fc0fc0fc7bc37cb7cabc03f00037c01542fc2fc2fc2fc0fc0fc0fc0fc03f003f0df0df550bf0bf03f03f03f03f03f03f00fc00fc37c37c0fc0fc0fc37c37c37c37d4ba,0x55551bf03f0bf1bf550bf0ff0ff0ff000fd55542fc2fc2fc2fc7bc37c37c37c0fc03f03f1ef0b7cabc03f00037c01542fc2fc2fc2fc0fc0fc0fc0fc03f003f0df0df550bf0bf03f03f03f03f03f03f00fc00fc37c37c0fc0fc0fc37c37c37c37d4d2,0x55005533330007bc0060695554cccc1fc03c03c03ccccc43c1fc1fc03c13c1fd12a5a480154ccccccccc03c03c0154ccccccccc03c03cccc03c03c03c03d532,0x55551bf03f0bf1bf550bf03f0ff0ff00fc155542fc2fc2fc2fc5fc37c37c37c03f00037c0003f03f03f037cf7cabd542fc2fc2fc2fc03f003f03f03f03f03f0df0df550bf0bf03f03f00fc00fc0fc0fc0fc0fc37c37c0fc0fc0fc37c37c37c37d54a,0x555502fc1546fc83ccc3fcccd5554300003c00333003c03c03ccccc1fc03c43c1fd543033333333300f00f550c0ccccccccc03c03cccc03c03c03c03d562,0x55005533330007bc0060c95554cccc1fc03c03c03ccccc1fc03c13c1fc0154ccccccccc03c03c0154ccccccccc03c03cccc03c03c03c03d57a,0x55005533330007bc0061895554cccc13c1fc1fc03c03c03d06a333307f00f04f07f005533333333300f00f005533333333300f00f3333,0x5550055333304f07f00005555304f00f333307f04f04f07f0055333300f10f3333333300f00f00f00f0055333300f04f3333333300f00f00f00f3333,0x550055333300005555333307f00f00f00f333307f04f04f07f005533333333333300f00f00f00f0055333300f00f3333300f00f3333,0x55005533330007bc0062495554cccc1fc03c03c03ccccc43c1fc1fc03c13c1fd202005533333333300f00f005533333333300f00f3333,0xf3c00636954bfd553ba90055300f00f41a80154c13c13d12a33330055300f10f44b8cccccccc0154c03c1fd136333333333333,0x555500005555300f00f0055333307f04f04f07f333307f04f04f07f005533330ef00f00f00f33330ef00f00f00f33330055333307f00f00f00f333307f00f00f00f33333333,0x15400015554cccc03c1fc1fc03c03c1fd8f200553333333307f04f04f07f00553333333307f00f00f00f333300555333300f00f07f07f300f07f33333333,0x550012bc00642954bfd553a29333300f07f07f00f00f07f63c80154cccccccc1fc13c03c1fc43c1fd79a00553333300f10f333300553333300f07f33333333,0x55557ff554f0246fc0fc2fc2fc37cf3c5fc37c37cf3d0526369546fc0fc83c6fc01546fc0fc2fc2fc0fcf7cb7c03f0551bf0bf0bf0bf03f0df4af00fc00fc0fc0fc0fd54c7c2fc0fc0fc0fc37d2bc03f003f03f03f03f03f03f03f03f,0x550012bc00648954bfd553c69333300f07f07f00f00f07f41a98f200553333304f04f00553333300f10f333300553333300f07f33333333,0x555500555300f00f005533330ef04f04f07f33330ef04f0055333307f00f00f00f33330ef00f33330055333307f00f00f00f333300f00f33333333,0x55550055300f00f0055333317f04f04f07f333317f04f005533330ef00f00f00f333300f00f33330055333307f00f00f00f333300f00f33333333,0x55550055300f00f0055333307f04f04f07f333307f04f0055333307f00f00f00f333333330055333307f00f00f00f333300f00f33333333,0x155540154c13c13c0154cccc1fc13c13c1fc13c1fd202333307f04f04f07f0055333307f00f10f0ef333333330055333307f04f00f00f333333333333,0x55550055300f00f0055333307f04f04f07f33330055333307f00f00f00f333333330055333307f00f00f00f333300f00f33333333]
def h3b17 : Array Nat := #[0x555500055300f00f0055333307f04f04f07f333304f07f005533330ef00f00f00f333300f00f33330055333307f00f00f00f333300f00f33333333,0x55550055300f00f0055333317f04f04f07f3333005533330ef00f00f00f333300f00f33330055333307f00f00f00f333300f00f33333333,0x55550055300f00f0055333307f04f04f07f33330055333307f00f00f00f333333330055333307f00f00f00f333300f00f33333333,0x155540154c03c03c0154cccc5fc13c13c1fccccc0154cccc3bc03c03c03ccccccccc0154cccc1fc03c03c03c5fc5fd78a333300f00f17f17f33333333,0x15555543009bc15409f0300f00f5530f09f3309f33317f35f10f07f09f333550c0333003c03c03c5fc1fd18e5c08cccccccd5430300f07f33300f00f07f07f33333333,0x55550055300f00f0055333307f04f04f07f33330055333307f00f00f00f333333330055300f07f33300f00f07f07f33333333,0x155540154c13c13c0154cccc1fc13c13c1fc13c1fd20233330055333307f00f10f0ef333333330055304f07f333333333333,0x5fc0065a9549bd553cc90055326f26f0055333307f04f00f07f17f07f5e68cccc0154cccc1fc03c13c73c5fc1fd792333333330055335f07f333333333333,0x5526f554fc2554015427c03c37c09f05509f09f09f0ff17f10f00f07f17f17f47a97821bf09f09f1bf09f09f09f0ff550ff00f17f463809f009f0ff09f0ff0ff0ff0ff0ff550ff00f17f465809f009f0ff09f0ff0ff0ff0ff0ff0ff0ff0ff0ff,0x5fc006609549bd553f690055300f00f0055333307f04f00f07f10f07f480979a33330055300f10f333333330055300f07f333333333333,0x5fc006729549bd553fc90055300f00f41a80154c13c13d20233330055300f10f4818cccccccc0154c03c1fd20e333333333333,0x550055333003c04f00055304f04f333304f07f04f07f00553333333333330055333300f00f07f07f333333333333,0x1540154c13c13c0154ccc00f013c0cccc13c1fc13c1fc0154cccccccccccc0154cccc03c03c1fc1fd716333333333333,0x550012bc1a5a55333300553333333003c04f000553333300f10f333304f0ef10f0ef56180154cccccccc03c03c3bc3bd69a33333333,0x550012bd54cccc03c3bc03c1fc0154ccccccc00f013c00154ccccc03c43ccccc13c3bc43c3bd58600553333333333333333,0x9bc7bc7bcbfc009bc7bc7bcbfcbfc7bc7bcbfc009bce3ce3ce3d83ce3d57e8fcbfce3c7bce3c009bc9bd87d87d557d563f55efd,0x9bc7bc7bcbfc009bc7bc7bcbfcbfc7bc7bcbfc009bce3ce3ce3d83ce3d57e8fcbfce3c7bce3c01587d60f60f55f55f563f55efd,0x55005500f1af0cf10f005504f0cf0cf0cf10f2cf1af2cf005504f04f0cf0cf10f10f1af1af0cf0cf0cf0cf,0x55005510f1af1af10f005504f0cf0cf0cf10f4bf1af4bf005504f04f0cf0cf10f10f0cf0cf0cf0cf0cf0cf,0x154015413c6bc33c43c015413c33c33c33c43e3bc6bc422005504f04f0cf0cf10f10f1af1af0cf0cf0cf0cf,0x154015443c6bc6bc43c015413c33c33c33c43e3bc6bc43a005504f04f0cf0cf10f10f1af1af0cf0cf0cf0cf,0x55005510f1af1af10f005521083e600687b220a812e11486c2005510f10f1af1af10f4c295861f8870a6ff6ff,0x55005510f1af1af10f00554bf4bfb6f4bf10f4bf1af4bf005510f10f1af1af10f10f1af1af4c292aa1fe87226ff6ff,0x550012f25510f1af1af10f00554bf4bf68f4bf10f4bf1af4bf005510f10f1af1af10f4aa9586204873a6ff6ff,0x55552ff63f63f2ff5552ff3cf3cf1ef430942a2ff3cf63f1ef52891125532a81020188c6232480d20d28c0201562bcf3cf3cf3cc7a17881ca258897d2a24c0825f0,0x5500550ef07f07f0ef00148a550ef00f00f00f0ef00f07f0ef005543f00f00f00f34285fa078897a00f4ae931a,0x5500550ef04f04f0ef00550ef00f00f00f0ef00f04f0ef005517f00f00f00f24f04f04f04f00f00f00f00f,0x15554cfcb7cb7ee7d54cfce7ce7d93cabc57c57cabd54cfdb7ce7db7d33d6bd6bd33c97c97c97c97d54cfcb7cb7cb7cabc57c57c57c15f025f25f25f25f,0x155547bcb7cb7c7bd54cfce7ce7d93cabc57c57cabd547bc37c37c37c7bc37d6bd33c0df05533f0df0df0df2af15f15f15f057c00df0df0df,0x155547bcb7cb7c7bd54064f2af15f15f2af551ef0df0df0df1ef0df5af4cf037c154cfc37c37c37cabc57c57c57c15f00df0df0df0df,0x155547bcb7cb7c7bd54cfce7ce7d93c02af551ef0df0df0df1ef0df5af4cf037c154cfc37c37c37cabc57c57c57c15f00df0df0df0df,0x55005507f04f04f07f00550ef00f00f00f0ef00f04f0ef005507f00f00f00f07f04f04f04f00f00f00f00f]
def h3b18 : Array Nat := #[0x155545fc9bc9bc5fd545fcf7c9bd8bc15f05517f0df0df0df037c0f3c37d6bd33d545fc37c37c37c15f02af15f15f15f0df0df0df0df,0x1555426f05585f3df3df33f17f10f10f07f55003c03bc03c03c03c3bc03c43c3bd5435f007f00f00f00f07f35f35f35f00f00f00f00f,0xe72024800239680172fdacf2bf2bfacf005c8f70fdd3dd3dcfce4e0d0833a2eb801613d96f1ff1ff1ff39183460cc8ba6390833e0cd8ba2]
def h3 : Array (Array Nat) := #[h3b0,h3b1,h3b2,h3b3,h3b4,h3b5,h3b6,h3b7,h3b8,h3b9,h3b10,h3b11,h3b12,h3b13,h3b14,h3b15,h3b16,h3b17,h3b18]
def h4b0 : Array Nat := #[0x29f54f54f29f0029f30f29f30f16fb16fbb16fb16fb29fb29f,0xbbbbbb0055bbbbbbbbbbbb,0x144fc07c07c07c07c01f01f5522f0007c07c07c07c01f001f01f01f01f01f01f,0x1422fbb5bbbbbb0055bbbbbbbbbbbbbb,0x513f13f22f42f513fb13f13f013f13f5513f08f01f08f01f2ef13f08f4df13f08f13f01f13f01f,0x4fec27c13f13f13f13f00095423c001f08f01f09f0023c001f08f01f13f08f01f13f01f,0x153ca7ca7d53c00a7cc3ca7cc3d30f545bd5b5,0x1f01f01f01f00c8007c59bf01f01f01f01f007c01f01f,0x1407dfbc007c07c007c07c07c07c03201f01f01f01f5508f42f01f01f01f007c072f007c07c07c001f01f,0x51df01f01f01f5509f09f01f01f01f01f01f01f01f01f01f01f01f01f01f01f01f01f,0x522f2ef0bbc04a22f2ef2ef22f01df42f2ef22f552ef08f008f000bbc23c07c022f01f22f01f,0x4fc4fc42f2ef22f2ef012948bc23c0008f2c22f22f,0x2eeeeec0156eeeeeeeeec242,0xbbbb0055bbbbbbbbbb,0x1fbb5bbbb0055bbbbbbbbbb,0x7eeeed6ed27eeeec1da,0x7eed6eeec2eeeeec1c2,0x7ed5018aeeec2ec312bbbb28f,0x5bbbbbbbb0055bbbbbb28fbb28fbb,0x1407c8bc07c07c1407c07c07c07c07c07d548bc23c07c07c07c07c07c07e53c01f001f01f,0x1f5bbbbbb0055bbbbbbbb28fbb,0x7c01f5bbbb502eca3eec312,0x2eeec062005df56eeeeec43abbbb,0x2eeeeec0156eeeeeeeeeeed27eeeeeec242,0xbbbbbb0055bbbbbbbbbbbb28fbbbbbb,0x1fbbbb5bbbbbb,0xbb2c2ec246,0xbb5bbbbbb,0x2ec2eeec246bb,0x7ed501eaeeeeec30abb28f,0x501f22f01f01f0501f01f01f01f01f01f508f01f01f01f001f01f01f01f1cf01f01f01f01f1cf,0x1f5bbbbbb5bbbbbbbb28fbbbb28f]
def h4b1 : Array Nat := #[0x7c01f5bbbb5b0b2eeeeec312,0x2eeeeec07abb0e580,0x2eeeeec0177d5bbbbbbbbbbbb,0x1f2ef501f2ef01f007c07c07c07c007c07d5423c23c07c07c07c07c07c07c34a01f01f01f01f01f01f,0x16eeeeec2eeeeec0156eeeeeeeeeeee47eeeeeec242,0x7c00920bb5bbbbbbbb5bbbbbbbb,0x1f5bb007c00aabbbb5bbbb5b0b2eeeeec312,0x501f2ef01f01f007c07c007c07c01f01f01f01f030800007c07c,0x7cbbc07c07c07c0001f01f01f01f03695423c23c27c4fc07c00007c001f01f01f01f01f01f01f01f,0xbbbbbb0055bbbbbbbbbbbb,0x16ec01fbb5bbbb0055bbbbbbbbbbbbbb,0x5509f01f09f09f01f01f01f01f01f01f01f01f01f01f01f01f5508f08f01f01f09f08f01f01f01f01f01f01f01f01f01f01f01f01f,0xbbbb37f0055bbbbbbbbbbbb,0xbbbb37f0055bbbbbbbbbbbb,0x5bbbbbbbb0055bbbbbbbbbbbb,0x5bbbbbbbb0055bbbbbbbbbb37fbbbbbb,0x1f5bbbb0bbbbbb0055bbbbbbbbbb6bfbbbbbbbb37f,0x2eeecb2cb2eeeec242,0x2eeeeecb,0x5bbbb0bbbbbb,0x7c2eed5048aec0f2bbbb0c080,0x7ed504eaeeeeeeec3120,0x7c2ed6eeeeeeecb2c,0x16eeeeeeeeeca3cb2c,0x516f6eeeeeeeed04eaeeeeec3921bb2c,0x7d6eeeeecb,0x16eeeeeeecb2c,0x16eeeeec2eeeeecb2c,0x7d6ec2ed6eeeeed6eeeeeca3eecb2c,0x16eeeeeeed6eeeeeeeeecb2c,0x501f13f001f01f01f1407c07c07c07c09e01f01f01f01f5534f08f01f01f01f01f01f01f01f01f72f65f01f01f01f01f01f01f01f01f,0x1f0bb5bbbbbb0055bbbbbbbbbbbb]
def h4b2 : Array Nat := #[0x1f01f01f01f0429407c07c07c07d54d3c8bc07c07c07c07c07c07c01f001f01f01f01f01f01f,0x1f01f501f01f01f01f5522f08f01f01f01f01f01f01f007c001f01f01f01f01f,0x501f01f01f01f01f01f01f01f5509f08f01f01f01f01f01f01f01f01f01f01f01f01f4df01f01f01f01f01f01f65f01f01f,0x1f5bbbbbb5bbbbbb28fbb,0x7c01f0042aed6eeed6eeeca3eec302,0x5bbbb0bbbbbb,0x2eeec12200516f6eeeeeeeeec446,0x1f0bb05bbbbbb0055bbbbbbbbbbbbbb,0x2eeec02d550549bbbbbbbbbbbb49f,0x2ec02d5505a9bbbbbbbbbbbb,0x7eec02d550609bbbbbbbb0bbbbbb,0xbb0055bbbbbbbbbb5bbbbbbbbbb,0x55bbbbbbbbbbbbbbbbbb,0x1f0bb0055bbbbbbbbbb0bbbbbb6bfbb,0xbbbb0055bbbbbbbbbb6bfbbbbbbbbbb49f,0xbb0055bbbbbbbbbb37fbbbbbbbbbbbb,0xbb0055bbbbbbbbbbbbbbbbbb,0x5bbbbbb0055bbbbbbbbbb6bfbb5bbbbbbbb49fbbbbbb49f,0xbbbb0055bbbbbbbbbbbbbb,0x55bbbbbbbb0bbbbbbbbbbbb,0x55bbbbbbbb0bbbb0bbbbbbbb6bf,0x55bbbbbbbb0bbbbbbbbbb,0x1f0055bbbbbbbb0bbbb5bbbbbbbb,0x7c0044f55bbbbbb5bbbbbbbbbbbbbb,0x55bbbbbbbbbbbbbbbbbb28f6bfbb,0x7c0044f55bbbbbbbbbb6bf5bbbbbbbbbbbbbb,0x7c01f00113d56eeeeeeeeedafd6eeeeed6eeeeeeeca3eeeec332,0x2eeec19a00b55617dbbbbbbbbbb,0x2eeec1b20055bbbbbbbbbbbb0055bbbbbbbbbbbbbbbbbbbb,0x2eeec1ca0055bbbbbbbbbbbb,0x1f002bbd56eeeeeeeeeeec1e2bbbb5bbbbbb,0x2eeec21200b55425a6eeeeec102bbbbbbbb28f]
def h4b3 : Array Nat := #[0x156eeeeeeec2eeec28abbbbbbbb28fbbbb49f,0x7c0008a956eeeeeeec2eeec2a2bb0055bbbbbbbbbbbbbbb28f,0x2ec2eeeeec2420055bbbbbbbbbbbbbbbbbbbb,0x2ec42fbb0bbbb0055bbbbbbbbbbbbbb,0x1407c8bc07c07c007c07c07c07c2fa01f01f01f007d550de908f42f01f01f01f01f01f01f08a801f001f01f,0x7c2eeec312bb00b5543926eeeeeeec242bb,0x7c2eeec32abb0056eeeeec132bb096aec062,0x7c01f0055bbbbbbbbb543aabb076aec272bb,0x7c07c07c07c2ba522f01f01f01f001f01f01f5543c250bc8bc07c07c07c07c01f001f01f01f01f,0x1f01f01f01f01f5543da423c8bc07c07c07c07c01f001f01f01f01f,0x1407c4fc007c07c07c07c07c07c07c07c2e201f5442201f01fc9f01f01f01f01f,0x7eeeec312b5443abb71fbbbb,0x7eeeec32a005bbbbbb71fbb050aec13a,0x7c01f00aeaec0156eeeeeeeeeed5114aeeec1b2bb,0x1f007c0156eeeeeeeeeed511aaec28ebbbb,0x7c16eeeeec0156eeeeeeeeec1fabb,0x1fbb0bbbbbb0055bbbbbbbbbbbbbb,0x1fbb5bbbbbb,0x1f5bb0bb0bbbbbbbb0cc80156eeeeeeeeec24ebbbbbb28fbb,0xbbbb0055bbbbbbbbbbbbbbbbbb,0x42fbb0055bbbbbbbbbbbb05bbbbbbbb,0xbbbbbb28f0bbbb79fbbbbbb28f,0x1f007d6eeed6eeeeeeec30a,0xbbbb28f0bbbb79fbbbbbb17f,0xbbbb28fbbbb2cb2cb,0x2eeeca3c2eeede7eecb2c,0x2eeeca3c16eeeeecb2c,0xbbbbbbbb28f05bbbbbbbb17fbbbb17f,0xbbbb0e480145bdbbbbbbbbb443a71fbbbb,0x1fbbbb0ea80145bdbbbbbb71fbb021aec07e,0x55bbbbbbbbbbbbbb28f5bbbbbbbb49fbb,0x7c014a7dbbbbbbbbbb0bbbb11baec17abb]
def h4b4 : Array Nat := #[0x7c23d407c23c07c07c07c07c07c07c15423c4fcbbc23c07c07c07c07c0da01f01f01f01f001f01f01f01f,0x1f5bb007d6eeeeeca3d6eeed6eeeeeeec312,0x7c0094f55bbbbbbbb0055bbbbbbbbbb5bbbbbbbbbbb28f,0x1f5bb5bb007eeeed6eeeeec302bb,0x513f023cbbc23ec23c4fc156c4fc07cbbc07c23c4fc4fc00213f13f13f08f13f13f01f01f,0x552ef01f42f08f501f01f501f42f01f01f01f01f01f01f40f1cf01f01f01f01f02a807c07c07c07c07c07d03c73c1407c07c07c07c07c07c2fa01f01f,0x5508f01f13f08f01f01f501f08f007c00007c07c01f030807c07c07c07c07c07c001f001f103c01f01f,0x273d55a5f44fc4fc23c07c4fc23cbbc23dcbd03d401f022f137c13f08f22f08f0d8823cbbd44fc8bc4fc23c8bc23c013f008f103c22f08f,0x156eeec16eeec01fbbbbbb5bbbbbbbb,0x156eeec2ec01f094fbbbbbb28fbbbb28f5bbbbbb28fbbbbbb,0x1548bc07c4fc4fc0501f01f01f01f01f01f01f01f01f01f501f01f046807c07c07c07c2e201f01f,0x7c0090f55bbbb5bb007eeeeeed6eeeeec312bb,0xbbbb0bbbbbb,0x2eeec2eeede7eecb2c,0x2eeec2eeecb2c,0x2eeeeeeec2eeeeeeecb2c,0xbbbbbb00516f6eeeeeeeed71fbbbbbb,0x7c07c07c07c35622f01f01f007c07d5427c4fc27c4fc001f0007c07c07c07c07c07c07c07c01f0,0x55bbbb49f0055bbbbbbbbbbbbbbbbbbbbbbbb,0x7c000f094a7dbbbbbbbbbbbb114aeeec01677dbbbbbbbbbbbbbb,0x75f55b08f2ef08f7cf5b13fb13f009f0b13f1ebcb08f1f3c4fc4fc23c23c362,0x508fb13f15401f001f09f01f08f0027c001f01f09f08f13f13f01f01f13f13f08f08f4df,0x9f08f5509f09f08f09f01f08f08f09f09f08f01f01f09f08f01f01f22f08f13f13f01f01f,0x5508f09f09f08f01f01f08f01f01f01f17f509f08f01f01f01f01f01f01f007c0001f00,0x1f0003da529f6eeeeeeec2eeec2eeeeeeec392,0xc3ca7cc3ca7c3f20a7c000068a7ca7ca7ca7d6d516f54a7d,0xc3c001028a7ca7ca7ca7ca7cc3ca7cc3c3f213fb29f30f88f30f71fc6f13fb16f16f30f30f71f85f30f16fbb30f30f85fc1f,0x8f08f08f08f0008f08f08f08f08f08f08f08f0008f08f08f08f08f08f08f08f08f08f08f08f0009f09f13f13f09f09f1df1df513f544fd,0x8fb08f08f0008f08f08f08fbbbb0008f08f08f08fbbbbbbbb00586f56d5b56d,0x23c23c23c23c007df08f08f08f08f423c23c23c0023c23c23c23c23c23c23c23c23dbbd03c008bc8bc4fc4fd50bd513f544fd,0x27c77c77c27c27c77c77c27c27c77c77c27c27c4bc4bc4bcd3cd3cd3cd3c1df009f12f12f12f34f12f34f34f04bc012f12f12f09f09f12f12f51df5477d512f544bd,0x8f08f08f08f0008f08f08f08f08f08f08f08f0008f08f08f08f08f08f08f08f08f08f08f08f00513f550bd513f544fd]
def h4b5 : Array Nat := #[0x9f1df1df09f09f1df1df09f077c027c4bc4bc4bc1df034f34f34f34f09f12f12f12f04bc0d3c4bcd3cd3c4bc4bc4bc4bc27c27c4bc4bc41477d512f544bd,0x23c23c23c23c0023c23c23c23c23c23c23c23c0023c23c23c23c23c23c23c23c23c23c23c23c0027c27c4fc4fd477d513f544fd,0x8f08f08f08f0008f08f08f08f08f08f08f08f0008f08f08f08f08f08f08f08f08f08f08f08f00513f427c27c77c77c23c4fc4fc4fd44fd,0x9f1df1df09f477c77c27c27c77c77c27c27c4bc4bc4bcd3cd3cd3cd3c1df009f12f12f12f34f12f34f34f04bc012f12f12f512f427c27c77c77d477d12f12f12f12f12f12f12f12f,0x8f08f08f08f0008f08f08f08f08f08f08f08f0008f08f08f08f08f08f08f08f08f08f08f08f0051df5477d586f561bd,0x23c23c23c23c007df423c23c23c23c23c23c23c0023c23c23c23c23c23c23c23c23dbbd03c0144fd2ef2ef42f42f513f544fd,0x27c77c77c27c27c77c77c27c27c77c77c27c27c4bc4bc4bcd3cd3cd3cd3c1df009f12f12f12f34f12f34f34f04bc012f12f12f512f427c27c77c77d477d512f544bd,0x8f08f08f08f0008f08f08f08f08f08f08f08f0008f08f08f08f08f08f08f08f08f08f08f08f00513f5477d513f544fd,0x77c027c77c77c27c27c23c23c23c08f008f08f08f08f08f08f08f08f077c023c23c23c23c23c23c23c23c23c23c23c23c4144fd09f09f1df1df513f544fd,0x23c23c23c23c0023c23c23c23c23c23c23c23c0023c23c23c23c23c23c23c23c23c23c23c23c0144fd09f09f1df1df513f544fd,0x8f08f08f08f0008f08f08f08f08f08f08f08f0008f08f08f08f08f08f08f08f08f08f08f08f00513f5477d513f544fd,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x1540049f55bbbb0055bbbbb7af37f0055bbbbbbbbbbbb,0x1555427c77c77c27d544fec4fc4fcb05522f12f13f13f2c0bbb5509f09f13f13fbbbbbbbbbbbb,0x5555077c154b0bbbb5504bc2eeeeeeed5409f0bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x1555423c07cbbc23d5423c07c4fc23c07c07c07c07d5423c23c07c07c07c07c07c07c07c07c07c07d5477c77c4fc4fc07c001f0001f0,0x1555423c07cbbc23d5423c07c4fc23c07c07c07c07d5423c23c07c07c07c07c07c07c07c07c07c07d5477c77c4fc4fc07c001f0001f0,0x55552ef08bcbbd548bc07c4fc4fc01f05522f13f01f01f01f01f01f01f01f01f01f01f55513f37f7cf2ef37fc7f01f4df7cf01f01f01f01f1ff1ff,0x1555423c07c77c23d5423c07c4fc23c07c07c07c07d5423c23c07c07c07c07c07c07c07c07c07c07d5409f001f0007c001f01f01f01f,0x1540156eeec0156eeeeeeec0044f55bbbbb37f28fbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x155554bbc07c8bcbbe03cafd54bbd0bd0bcbbc07c07c01f03080425542f22f01f01f01f01f01f01f02a8092007c1554bbcbbc07c07d03cafc07cafd03c01f0001f01f01f01f1cf1cf,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x555509f09f09f09f5509f01f09f13f01f01f01f01f5509f13f01f01f007c007c07c07c07d5427c27c07c07c27c01f01f01f01f01f01f01f01f01f01f,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x555509f09f09f09f5509f01f09f13f01f01f01f01f5509f13f01f01f007c007c07c07c07d5427c27c07c07c27c01f01f01f01f01f01f01f01f01f01f,0x5555027c1544fec27dfbeeeed541df0bbbbbbbb5500bbbbbbbbbbbb,0x1555427c77c27c27d5427c07c27c4fc01f05509f13f01f01f007c001f01f01f5509f09f01f01f01f01f01f01f01f01f01f01f01f01f01f01f,0x1540072f55bbbb0055bbbbb79f37f0055bbbbbbbbbbbb,0x1555427c77c27c27d5427c07c27c4fc01f05509f13f01f01f007c001f01f01f5509f09f01f01f01f01f01f01f01f01f01f01f01f01f01f01f,0x5555027c154b0bbbb55077c2eeeeeeed5409f0bbbbbbbbbbbb]
def h4b6 : Array Nat := #[0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x30f29f29f30f00529f6eeec0145bdbbbbbbbb0055bbbbbbbbbbbb,0x1555427c77c77c27d5427c07c4fc4fe03e9bc0015427c4fc07c07c07c07c07c07c07c07c07c07d55427c27c07c07df3d13c000001f01f01f01fc0f44f,0x550055bbbb0055bbbbbbbb0055bbbbb37f28fbbbb,0x555509f1df1df09f5509f01f13f13f80f6ef007c015427c4fc07c07c07c07c07c07c07c07c07c07d5427c4fc07c07c01f0007c07c07c44f01f01f01f01f,0x550055bbbb0055bbbbbbbb0055bbbbbbbb37f37fbbbb,0x55552ef01f22f22f80f6ef552ef42f42f2ef01550bc8bc07c07c07c07c07c07c07c07c07c07d54bbc8bc07c07c07d13d97c01f001f01f01f01f,0x1540044f55bbbb0055bbbbbbbb0055bbbbb37f28fbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb37fa8f0055bbbbbbbb0055bbbbbbbb28f37fbbbb,0x1540072f55bbbb0055bbbbbbbb37f37f0055bbbbbbbb28f37fbbbb,0x1540072f55bbbba8f37f0055bbbbbbbb0055bbbbbbbb28f37fbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb09c81020055bbbbbbbbbbbb28f49f,0x555508f01f1df08f5508f01f13f08f01f01f01f01f5508f13f01f01f01f01f01f01f01f01f01f01f55004fc001f0007c001f,0x154000ba956eeec000b4956eeeeeeec015431a544b2bbbbb08782aeb06681e2,0x55001cbd5503d56eeecdfca3cdfca3c4820055bbbbb37f37f0055bbbbb49f28fbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbb28f49fbbbb28f49f,0x15555423c8bc8bc23e9bef3d5423c4fc4fc0d8805a08f2ef2ef08f55513f7af4df08f22f22f08f40f2bf04fc01548bc4fc4fc4fd37debd0bc8bc8bc8bc13f013f13f13f13f1cf1cf,0x550055bbbb0055bbbbbbbb0055bbbb28f7afbbbbbbbb28f49f,0x550055bbbb37f28f37f28f0055bbbbbbbb0055bbbbbbbbbbbb91f91f,0x1540156eeec001cf55bbbbbbbb0055bbbbbbbbb49f28f,0x555508f01f2ef08f55508f01f13f08f4df4df01f01f01f01f40f2bf5508f13f13f08f01f01f01f01f01548bc4fc07c07c07c07c07c07c07c73c73c01f0,0x1555697d5423c07c8bc23cafd03cafd03c49a5508f01f2ef08f01f2bf2bf5508f22f22f08f01faef40f007c07c07d54bbc8bc07c07c07d37d03c07c07c07c07c01f0,0x555508f01f22f08f550023c07c07c07c07d55423c13f08f01f01f01f01f007c01548bc4fc07c07c07c07c07c07c01f001f1cf1cf,0x555508f01f22f08f5508f13f13f08f0007d55423c07c4fc23d37d37c07c01f01f40f2bf007c01548bc4fc07c07c07c07c07c07c01f001f1cf1cf,0x1540156eeec0040f55bbbb37f28f37f28fbbbb0055bbbbbbbbb49f28f]
def h4b7 : Array Nat := #[0x15555fbe1fe1fdfbd548bc07c4fc4fc01f05522f01f13f13f01f01f01f01f1cf1cf01f01f01f01f55522f13f01f01f007c001f01f01f04682ca01f90f90f,0x555508f22f22f08f5508f01f13f08f007c15423c07c4fc23c07c07c07c07c73c73c07c07c07c07d548bc4fc07c07c01f001f01f01f01f01f4df4df,0x1540156eeec0040f0126956eeeeeeecdfca3c9bca3c4820055bbbbbbbbb49f28f,0x555508f22f22f08f5508f01f13f08f007c15423c07c4fc23c01f00007c07c07d548bc4fc07c07c01f001f01f01f01f01f4df4df,0x555508bc15423cbbcbbc23c23eeed54b002eecdfca3eeeed5422f0bbbbbbbbb49f28f,0x1540156eeec001cf55bbbbbbbb0055bbbbbbbbb49f28f,0x177ca7ca7d77c014a7dbbbb00037a529f6eeeeeeec00145bdbbbbbbb43aa04c846201884c2b0588192,0x1555423c07c27c23d5423c27c27c23c07c07c07c07d5423c07c27c23ccfccfc07c07c07c07c01f005522f13f01f01f01f01f01f01f007c001f0,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x555508f01f22f08f5508f13f13f08f01f01f01f01f5508f01f13f08f01f01f01f01f40f2bf007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x1555423c07c8bc23d5423c4fc4fc23c001f5508f01f13f08f01f01f01f01f40f2bf007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x1540156eeec001cf55bbbbbbbb0055bbbbbbbbbbbb,0x1540156eeec0040f55bbbbbbbb37f28f0055bbbbbbbbbbbb28f28f,0x1540156eeec0040f55bbbb37f28fbbbb0055bbbbbbbbbbbb28f28f,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x1540156eeec0156eeeeeeec9bca3c9bca3c48e0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x555508f01f09f08f5508f09f09f08f01f01f01f01f5508f01f09f08f33f33f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x550055bbbb0055bbbb17f17fbbbb0055bbbbbbbbbbbb,0x1555409f05508f09f09f08f08fbbb552c2eeec5fc5feeeed5409f0bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x1555423c27c27c23d5423c07c27c23c01f05508f01f09f08f007c001f01f01f5509f13f01f01f01f01f01f01f01f01f01f01f01f01f01f01f,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x1555423c27c27c23d5423c07c27c23c01f05508f01f09f08f007c001f01f01f5509f13f01f01f01f01f01f01f01f01f01f01f01f01f01f01f,0x5555027c15409f0bbbb552c2eeeeeeed5409f0bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x15554d3c07c27cd3d54d3c27c27cd3c07c07c07c07d54d3c07c27c8bc07c07c07c07c07c07c07c07d550bc8bc07c07c07c07c07c07c01f001f01f01f01f,0x1555423c07c27c23d5423c27c27c23c07c07c07c07d5423c07c27c23c07c07c07c07c07c07c07c07d548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x555508f01f09f08f550023c07c07c07c07d5423c07c27c23c07c07c07c07c07c07c07c07d548bc4fc07c07c07c07c07c07c01f001f01f01f01f]
def h4b8 : Array Nat := #[0x15554c3c07c27cc3d54c3c27c27cc3c07c07c07c07d54c3c07c27c8bc07c07c07c07c07c07c07c07d54c3c8bc07c07c07c07c07c07c01f001f01f01f01f,0x555508f01f22f08f5508f13f13f08f08f01f01f01f5508f01f13f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f0007c07c07cafd37cafd37c49a,0x1555423c07c27c23d5423c27c27c23c07c07c07c07d5423c07c27c23c07c07c07c07c01f05522f13f01f01f01f01f01f01f007c001f01f01f,0x555508f01f09f08f5508f09f09f08f01f01f01f01f5508f01f09f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x555508f01f09f08f5508f09f09f08f01f01f01f01f5508f01f09f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x1555423c07c27c23d54008f01f01f01f01f5508f01f09f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x555508f01f09f08f5508f09f09f08f08f01f01f01f5508f01f09f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x1555423c07c27c23d5423c27c27c23c001f5508f01f09f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x555508f01f09f08f550023c001f5508f01f09f08f01f01f01f01f007c1548bc4fc07c07c07c07c07c07c01f001f01f01f01f,0x555508bc1542ef0bbbb552c2eeeeeeed5422f0bbbbbbbbbbbb,0x550055bbbb0055bbbbbbbb0055bbbbbbbbbbbb,0x555508f09f09f08f5508f01f09f08f01f01f01f01f5508f01f09f08f007c007c07c07c07d5427c4fc07c07c01f001f01f01f01f01f01f01f01f,0x1555423c27c27c23d5423c07c27c23c01f05508f01f09f08f007c007c07c07c07d5427c4fc07c07c01f001f01f01f01f01f01f01f01f,0x1555423c77c77c23d5423c07c4fc23c01f05508f01f13f08f007c007c07c07c07d5427c4fc07c07c01f001f01f01f01f01f01f01f01f,0x55550023d5423c07c27c23c01f05508f01f09f08f007c007c07c07c07d5427c4fc07c07c01f001f01f01f01f01f01f01f01f,0x5555027c154c3c27c27cc3c27eeed544fee1fc77eeeeeeeed5409f0bbbbbbbbbbbb,0x1555409f05508f09f09f08f08fbbb552c2eeeeeeed5409f0bbbbbbbbbbbb,0x1555409f05508f09f09f08f08fbbb552c2eeeeeeed541df0bbbbbbbbbbbb,0x5555027c154008f08fbbb552c2eeeeeeed5409f0bbbbbbbbbbbb,0x5555027c15409f0bbbb552c2eeeeeeed5409f0bbbbbbbbbbbb,0x8f540023d5bbbb0008f56eeeeeeec01477dbbbbbbbbbbbb,0x8f5401427dbbbb00516f6eeeeeeec01477dbbbbbbbbbbbb,0x509f40023d5bbbb0008f56eeeeeeec0027d5bbbbbbbbbbbb,0x529f4014a7dbbbb00516f6eeeeeeec014a7dbbbbbbbbbbbb,0xc3ca7ca7cc3c014a7dbbbb00516f6eeeeeeec014a7dbbbbbbbbbbbb,0x555508f1df1df08f5508f01f13f08f01f01f01f15423c07c4fc23c01f001f01f01f01f5509f13f01f01f01f01f01f01f01f01f01f01f01f01f01f01f,0x555508f1df1df08f5508f01f13f08f005508f01f13f08f007c007c07c07c07d5427c4fc07c07c001f01f01f01f01f01f01f01f01f,0x5df29f29f5df000422529f6eeec0145bdbbbbbbbb00529f6eeeeeeeeeeec46e021847601f84c2]
def h4 : Array (Array Nat) := #[h4b0,h4b1,h4b2,h4b3,h4b4,h4b5,h4b6,h4b7,h4b8]
def h5b0 : Array Nat := #[0x48f12f5016f16f029f29f,0x0,0x154bd6fc5bc5bc5bc16f16f,0x153d56fd4bc14bc5bf5bf,0x5bc04bc4bc07212f12f,0x5bc4bc4bc06a,0x516f75f16f16f16f16f16f16f,0x145bd6fc5bc5bc5bc5bd45bc5bc5bc16f16f,0x145bdd7c5bc5bc16f16f0016f,0x5bd6fc5bc5bd54bd23c5bc016f16f,0x12f12f,0x16f16f516f16f516f16f16f16f,0x5bc04bc4bc4bc4bc062,0x5bc4bc4bc4bc4bc072,0x12f12f12f12f,0x12f12f,0x16f012f12f12f12f,0x5bc4bd12f12f12f12f,0x16f12f12f12f09f12f12f,0x16f12f12f12f12f,0x5bc16f12f12f512f09f12f12f,0x12f09f,0x5bc4bd12f12f12f12f,0x5bc5bd45bd23c5bc5bc016f,0x12f12f12f09f,0x12f12f12f12f,0x16f12f12f12f12f,0x16f12f12f12f12f,0x5bc16f12f12f512f09f12f12f,0x16f16f516f5bf16f16f016f5401a16f16f16f16f,0x516f5bf16f16f16f16f016f5403216f16f16f16f,0x516f9af016f16f16f16f16f5404a16f16f16f16f]
def h5b1 : Array Nat := #[0x5bc16f12f5406212f12f12f12f,0x5bc16f00512f12f12f12f12f12f12f12f,0x5bc16f0bef09f12f512f12f09f09f,0x16f52f16f16f516f29f0016f16f,0x54f5512f52f75f52f7ff512f48f12f48f004bd4bc7ff,0x516f52f16f16f016f16f16f16f01685bc5bc5bc,0x5bc04bc4bc4bc4bc07212f12f,0x16f05bc0151fd12f12f12f12f12f12f12f12f,0x5bc5bc5bc5bc01a516f5bf16f16f016f16f,0x16f16f16f16f,0x30f0000829f29f29f9df30f30f30f30f30f,0xa7cc3ca7cc3c002,0x145be6bc05bc5bc5bc5bc5bc5bc5bc5bc042,0x5bc4bc4bc4bc4bc072,0x5bc16f000684bc4bc0151fd12f12f12f12f12f12f12f12f12f12f,0x16f05bc0151fd12f12f12f12f12f12f12f12f12f12f,0x55005512f12f12f12f005512f12f12f12f12f12f12f12f,0x155554bc5bd6fd4bd554bd23d23d4bd4bc5bc5bc5bd556fd23c5bc5bc5bc5bc5bc5bc16f0,0x30f5df5df30f00004a55df44bc4bc4bc4bc0000c9577d12f12f12f12f12f12f12f12f]
def h5 : Array (Array Nat) := #[h5b0,h5b1]
def h6b0 : Array Nat := #[0x29f,0x47f47f547f88f47f47f0,0x547f88f47f47f47f47f0,0x547f9cf047f47f47f47f,0x11fc47f]
def h6 : Array (Array Nat) := #[h6b0]
def h7 : Array (Array Nat) := #[]
def hLevels : Array (Array (Array Nat)) := #[h0,h1,h2,h3,h4,h5,h6,h7]
def lengths : Array Nat := #[1,7,150,579,284,51,5,0]
def levelSize (level : Nat) : Nat := lengths[level]?.getD 0

def blockGet (all : Array (Array (Array Nat))) (level id : Nat) : Option Nat := do
  let base←all[level]?
  let slab←base[id/32]?
  slab[id % 32]?

def stateAt (level id : Nat) : Option (List W × Nat) :=
  if id < levelSize level then (blockGet mLevels level id).map decodeState else none

def hintAt (level id : Nat) : Nat := (blockGet hLevels level id).getD 0
end Dag12122Data

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good0_0 : block cfg decodeStep stateAt hintAt 16 0 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good1_0 : block cfg decodeStep stateAt hintAt 16 1 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_0 : block cfg decodeStep stateAt hintAt 16 2 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_1 : block cfg decodeStep stateAt hintAt 16 2 1=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_2 : block cfg decodeStep stateAt hintAt 16 2 2=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_3 : block cfg decodeStep stateAt hintAt 16 2 3=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_4 : block cfg decodeStep stateAt hintAt 16 2 4=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_5 : block cfg decodeStep stateAt hintAt 16 2 5=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_6 : block cfg decodeStep stateAt hintAt 16 2 6=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_7 : block cfg decodeStep stateAt hintAt 16 2 7=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_8 : block cfg decodeStep stateAt hintAt 16 2 8=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good2_9 : block cfg decodeStep stateAt hintAt 16 2 9=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_0 : block cfg decodeStep stateAt hintAt 16 3 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_1 : block cfg decodeStep stateAt hintAt 16 3 1=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_2 : block cfg decodeStep stateAt hintAt 16 3 2=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_3 : block cfg decodeStep stateAt hintAt 16 3 3=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_4 : block cfg decodeStep stateAt hintAt 16 3 4=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_5 : block cfg decodeStep stateAt hintAt 16 3 5=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_6 : block cfg decodeStep stateAt hintAt 16 3 6=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_7 : block cfg decodeStep stateAt hintAt 16 3 7=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_8 : block cfg decodeStep stateAt hintAt 16 3 8=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_9 : block cfg decodeStep stateAt hintAt 16 3 9=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_10 : block cfg decodeStep stateAt hintAt 16 3 10=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_11 : block cfg decodeStep stateAt hintAt 16 3 11=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_12 : block cfg decodeStep stateAt hintAt 16 3 12=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_13 : block cfg decodeStep stateAt hintAt 16 3 13=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_14 : block cfg decodeStep stateAt hintAt 16 3 14=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_15 : block cfg decodeStep stateAt hintAt 16 3 15=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_16 : block cfg decodeStep stateAt hintAt 16 3 16=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_17 : block cfg decodeStep stateAt hintAt 16 3 17=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_18 : block cfg decodeStep stateAt hintAt 16 3 18=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_19 : block cfg decodeStep stateAt hintAt 16 3 19=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_20 : block cfg decodeStep stateAt hintAt 16 3 20=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_21 : block cfg decodeStep stateAt hintAt 16 3 21=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_22 : block cfg decodeStep stateAt hintAt 16 3 22=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_23 : block cfg decodeStep stateAt hintAt 16 3 23=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_24 : block cfg decodeStep stateAt hintAt 16 3 24=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_25 : block cfg decodeStep stateAt hintAt 16 3 25=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_26 : block cfg decodeStep stateAt hintAt 16 3 26=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_27 : block cfg decodeStep stateAt hintAt 16 3 27=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_28 : block cfg decodeStep stateAt hintAt 16 3 28=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_29 : block cfg decodeStep stateAt hintAt 16 3 29=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_30 : block cfg decodeStep stateAt hintAt 16 3 30=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_31 : block cfg decodeStep stateAt hintAt 16 3 31=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_32 : block cfg decodeStep stateAt hintAt 16 3 32=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_33 : block cfg decodeStep stateAt hintAt 16 3 33=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_34 : block cfg decodeStep stateAt hintAt 16 3 34=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_35 : block cfg decodeStep stateAt hintAt 16 3 35=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good3_36 : block cfg decodeStep stateAt hintAt 16 3 36=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_0 : block cfg decodeStep stateAt hintAt 16 4 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_1 : block cfg decodeStep stateAt hintAt 16 4 1=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_2 : block cfg decodeStep stateAt hintAt 16 4 2=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_3 : block cfg decodeStep stateAt hintAt 16 4 3=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_4 : block cfg decodeStep stateAt hintAt 16 4 4=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_5 : block cfg decodeStep stateAt hintAt 16 4 5=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_6 : block cfg decodeStep stateAt hintAt 16 4 6=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_7 : block cfg decodeStep stateAt hintAt 16 4 7=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_8 : block cfg decodeStep stateAt hintAt 16 4 8=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_9 : block cfg decodeStep stateAt hintAt 16 4 9=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_10 : block cfg decodeStep stateAt hintAt 16 4 10=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_11 : block cfg decodeStep stateAt hintAt 16 4 11=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_12 : block cfg decodeStep stateAt hintAt 16 4 12=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_13 : block cfg decodeStep stateAt hintAt 16 4 13=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_14 : block cfg decodeStep stateAt hintAt 16 4 14=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_15 : block cfg decodeStep stateAt hintAt 16 4 15=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_16 : block cfg decodeStep stateAt hintAt 16 4 16=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good4_17 : block cfg decodeStep stateAt hintAt 16 4 17=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good5_0 : block cfg decodeStep stateAt hintAt 16 5 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good5_1 : block cfg decodeStep stateAt hintAt 16 5 1=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good5_2 : block cfg decodeStep stateAt hintAt 16 5 2=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good5_3 : block cfg decodeStep stateAt hintAt 16 5 3=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good6_0 : block cfg decodeStep stateAt hintAt 16 6 0=true := by decide +kernel
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level6 : ∀i p,stateAt 6 i=some p → Dead cfg 5 p := by
  apply groupSound (width:=16) (size:=5) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 6 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · intro j p h
    have emp : levelSize 7=0 := by decide
    simp [stateAt,emp] at h
  · intro group small
    change group<1 at small
    interval_cases group
    · exact good6_0
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level5 : ∀i p,stateAt 5 i=some p → Dead cfg 6 p := by
  apply groupSound (width:=16) (size:=51) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 5 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact level6
  · intro group small
    change group<4 at small
    interval_cases group
    · exact good5_0
    · exact good5_1
    · exact good5_2
    · exact good5_3
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level4 : ∀i p,stateAt 4 i=some p → Dead cfg 7 p := by
  apply groupSound (width:=16) (size:=284) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 4 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact level5
  · intro group small
    change group<18 at small
    interval_cases group
    · exact good4_0
    · exact good4_1
    · exact good4_2
    · exact good4_3
    · exact good4_4
    · exact good4_5
    · exact good4_6
    · exact good4_7
    · exact good4_8
    · exact good4_9
    · exact good4_10
    · exact good4_11
    · exact good4_12
    · exact good4_13
    · exact good4_14
    · exact good4_15
    · exact good4_16
    · exact good4_17
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level3 : ∀i p,stateAt 3 i=some p → Dead cfg 8 p := by
  apply groupSound (width:=16) (size:=579) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 3 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact level4
  · intro group small
    change group<37 at small
    interval_cases group
    · exact good3_0
    · exact good3_1
    · exact good3_2
    · exact good3_3
    · exact good3_4
    · exact good3_5
    · exact good3_6
    · exact good3_7
    · exact good3_8
    · exact good3_9
    · exact good3_10
    · exact good3_11
    · exact good3_12
    · exact good3_13
    · exact good3_14
    · exact good3_15
    · exact good3_16
    · exact good3_17
    · exact good3_18
    · exact good3_19
    · exact good3_20
    · exact good3_21
    · exact good3_22
    · exact good3_23
    · exact good3_24
    · exact good3_25
    · exact good3_26
    · exact good3_27
    · exact good3_28
    · exact good3_29
    · exact good3_30
    · exact good3_31
    · exact good3_32
    · exact good3_33
    · exact good3_34
    · exact good3_35
    · exact good3_36
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level2 : ∀i p,stateAt 2 i=some p → Dead cfg 9 p := by
  apply groupSound (width:=16) (size:=150) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 2 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact level3
  · intro group small
    change group<10 at small
    interval_cases group
    · exact good2_0
    · exact good2_1
    · exact good2_2
    · exact good2_3
    · exact good2_4
    · exact good2_5
    · exact good2_6
    · exact good2_7
    · exact good2_8
    · exact good2_9
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level1 : ∀i p,stateAt 1 i=some p → Dead cfg 10 p := by
  apply groupSound (width:=16) (size:=7) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 1 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact level2
  · intro group small
    change group<1 at small
    interval_cases group
    · exact good1_0
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem level0 : ∀i p,stateAt 0 i=some p → Dead cfg 11 p := by
  apply groupSound (width:=16) (size:=1) (read:=decodeStep) (hints:=hintAt) (by decide)
  · intro i p eq
    have h:i<levelSize 0 := by by_contra! bad; simp [stateAt,Nat.not_lt.mpr bad] at eq
    exact h
  · exact level1
  · intro group small
    change group<1 at small
    interval_cases group
    · exact good0_0
end LiveAIG.SixLayers.Dag

namespace LiveAIG.SixStart
open FreeAIG LiveAIG
def cut (x : X) (i : Fin 6) : Bool := x ⟨i.val, by omega⟩
def f : X → Bool := Upper12122.target ∘ cut
abbrev t := SixLenses.target
def A : List W := inputs.take 6
def S : Set (Fn X) := {g | ∃ i : Fin 6,g=fun x=>cut x i}
set_option maxRecDepth 65536 in
theorem wordF : word f=t := by decide +kernel
theorem compile {k : Nat} (h : Has Inputs k Upper12122.target) :
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

open CofactorLoan

private theorem initOK (l : Lens t) (eval : A.all (fun w=>offers raw (l.image w)) = true)
    (hf : 1 ≤ flats l A) : Tight l A 11 :=
  initial l hf (List.all_eq_true.mp eval)

theorem tightF : Tight SixLenses.F A 11 := initOK _ (by decide +kernel) (by decide +kernel)
theorem tightE : Tight SixLenses.E A 11 := initOK _ (by decide +kernel) (by decide +kernel)
end LiveAIG.SixStart

namespace LiveAIG.SixLayers.Dag
open Dag12122Data
theorem core {k} (h : FreeAIG.Has FreeAIG.Inputs k Upper12122.target) : 12≤k := by
  by_contra! small
  obtain ⟨n,nk,c,run⟩:=SixStart.compile h
  have b:=balance run
  have len : SixStart.A.length=6 := by decide +kernel
  rw [len] at b
  have root : stateAt 0 0=some (SixStart.A,6) := by decide +kernel
  exact level0 0 _ root SixStart.tightF SixStart.tightE (by omega) (by omega) run
end LiveAIG.SixLayers.Dag

end PEqualNP.Outside.L_meta_12122

theorem PEqualNP.Outside.L_meta_12122 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12122.Upper12122.completeFromSigned PEqualNP.Outside.L_meta_12122.LiveAIG.SixLayers.Dag.core
