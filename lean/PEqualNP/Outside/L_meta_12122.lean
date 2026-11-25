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

namespace LiveAIG.Small12122.Data
open LiveAIG
def words : Array Nat := #[0x2000200020002,0x8000800080008,0xa000a000a000a,0xe000e000e000e,0x2a002a002a002a,0x80008000800080,0x88008800880088,0x8a008a008a008a,0xa800a800a800a8,0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xee00ee00000000,0xee00ee00ee00ee,0xfc00fc00fc00fc,0x100010001000100,0x200020002000200,0x202020202020202,0x2020202aaaaaaaa,0x20a020a020a020a,0x300030003000300,0x3000300ff00ff00,0x302030203020302,0x700070007000700,0x800080008000800,0x808080808080808,0x80a080a080a080a,0x888088808880888,0xa000a000a000a00,0xa020a020a020a02,0xa080a080a080a08,0xa0a0a0a00000000,0xa0a0a0a0a0a0a0a,0xaaa0aaa0aaa0aaa,0xace0ace0ace0ace,0xb000b000b000b00,0xc0c0c0c0c0c0c0c,0xe000e000e000e00,0xe0e0e0e00000000,0xe0e0e0e0e0e0e0e,0xeee0eee0eee0eee,0xf000f000f000f00,0xf0a0f0a0f0a0f0a,0xf0c0f0c0f0c0f0c,0x2222222222222222,0x2a002a002a002a00,0x2a2a2a2a2a2a2a2a,0x2f222f222f222f22,0x3030303030303030,0x3300330033003300,0x3c3c3c3c3c3c3c3c,0x3f003f003f003f00,0x3f2a3f2a3f2a3f2a,0x4444444444444444,0x5050505050505050,0x5500550055005500,0x6666666666666666,0x8000800080008000,0x8080808080808080,0x8088808880888088,0x8800880088008800,0x8808880888088808,0x8880888088808880,0x8888888888888888,0x88aa88aa88aa88aa,0x88f888f888f888f8,0x8a008a008a008a00,0x8a8a8a8a8a8a8a8a,0x8f888f888f888f88,0xa0a0a0a0a0a0a0a0,0xa0aaa0aaa0aaa0aa,0xa800a800a800a800,0xa8a8a8a800000000,0xa8a8a8a8a8a8a8a8,0xa8fca8fca8fca8fc,0xaa00aa00aa00aa00,0xaa0aaa0aaa0aaa0a,0xaa88aa88aa88aa88,0xaaa0aaa0aaa0aaa0,0xaaaaaaaaaaaaaaaa,0xaaeeaaeeaaeeaaee,0xae0cae0cae0cae0c,0xaeaeaeaeaeaeaeae,0xaf00af00af00af00,0xaf8caf8caf8caf8c,0xafaaafaaafaaafaa,0xc040c040c040c040,0xc0c0c0c0c0c0c0c0,0xc0eac0eac0eac0ea,0xc4c4c4c4c4c4c4c4,0xcc00cc00cc00cc00,0xcc44cc44cc44cc44,0xcccccccccccccccc,0xcceecceecceeccee,0xcececececececece,0xe0e0e0e0e0e0e0e0,0xeac0eac0eac0eac0,0xeaeaeaeaeaeaeaea,0xee00ee0000000000,0xee00ee00ee00ee00,0xee0eee0eee0eee0e,0xeeaaeeaaeeaaeeaa,0xeecceecceecceecc,0xeee0eee0eee0eee0,0xeeeeeeee00000000,0xeeeeeeeeeeeeeeee,0xeefeeefeeefeeefe,0xefeeefee0f000f00,0xefeeefeeefeeefee,0xf000f000f000f000,0xf0c0f0c0f0c0f0c0,0xf0f0f0f0f0f0f0f0,0xf500f500f500f500,0xf8f8f8f8f8f8f8f8,0xfafafafa00000000,0xfafafafafafafafa,0xfc00fc00fc00fc00,0xfcfcfcfc00000000,0xfcfcfcfcfcfcfcfc,0xfeeefeeefeeefeee,0xfefefefef0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xff0aff0aff0aff0a,0xff88ff88ff88ff88,0xffaaffaaffaaffaa,0xffaeffaeffaeffae,0xffccffccffccffcc,0xffeaffeaffeaffea,0xffeeffeeff00ff00,0xffeeffeeffeeffee,0xfff0fff0fff0fff0,0xfffefffefffefffe,0xffff0000ffff0000,0xffffffff00000000]
def rowCodes : Array Nat := #[0x44092044c19448d52b64cdd3b,0x44092044c19489562d68d5e3d,0x840a2048c1a489962e68d9e3e,0x1040c2050c1c42954ad62d5cbd,0x1040c2050c1c449952e64d9d3e,0x20c287122c68f428d2a752ad6af,0x40c307142c70f448d32754ad72f,0x814307183470f489532758b572f,0x102450b183470f50a552b58b572f,0x4085123489532760c593368d5b37,0x408512350a552b60c593370e5d3b,0x408522550a562d60c5a3570e5e3d,0x408922650a962e60c9a3670e9e3e,0x7ef5db96ed59b15eb55a94e951a1,0x7ef9dba6ed99b25eb95aa4e991a2]
def symbols : Array Nat := #[0x0,0x1,0x2,0x3,0x4,0x6,0x8,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x11,0x12,0x13,0x14,0x15,0x17,0x18,0x1a,0x1c,0x1e,0x20,0x21,0x23,0x24,0x26,0x27,0x28,0x2a,0x2c,0x2d,0x2e,0x30,0x32,0x33,0x34,0x38,0x39,0x3a,0x3c,0x3e,0x42,0x44,0x45,0x46,0x4a,0x50,0x51,0x54,0x56,0x57,0x58,0x5a,0x5c,0x5d,0x62,0x63,0x66,0x67,0x68,0x69,0x6a,0x6e,0x71,0x72,0x74,0x76,0x7a,0x7b,0x7c,0x7e,0x80,0x81,0x83,0x86,0x8c,0x90,0x92,0x93,0x94,0x95,0x98,0x9c,0x9e,0xa4,0xaa,0xb0,0xb2,0xb6,0xb7,0xbc,0xbd,0xc2,0xc4,0xc8,0xce,0xd1,0xd2,0xd4,0xd5,0xd6,0xd7,0xda,0xe0,0xe4,0xe5,0xe6,0xe8,0xec,0xed,0xef,0xf2,0xf3,0xf5,0xf8,0xfc,0xfd,0xfe,0x104,0x106,0x108,0x10a,0x10e,0x110,0x112,0x116,0x119,0x11a,0x11b,0x11c,0x120,0x122,0x123,0x125,0x126,0x128,0x12c,0x12d,0x12e,0x134,0x135,0x13a,0x13c,0x13e,0x140,0x143,0x145,0x148,0x149,0x14b,0x14c,0x152,0x153,0x154,0x155,0x158,0x15e,0x15f,0x160,0x161,0x164,0x166,0x16a,0x16b,0x16c,0x16d,0x170,0x172,0x174,0x175,0x176,0x178,0x17c,0x17f,0x180,0x182,0x183,0x184,0x185,0x188,0x189,0x18a,0x18e,0x191,0x194,0x195,0x19d,0x19e,0x1a3,0x1a4,0x1a6,0x1ac,0x1b2,0x1b3,0x1b8,0x1b9,0x1ba,0x1bb,0x1be,0x1bf,0x1c0,0x1c2,0x1c3,0x1c4,0x1c8,0x1ca,0x1cd,0x1ce,0x1d0,0x1d1,0x1d6,0x1d7,0x1d8,0x1d9,0x1da,0x1dc,0x1e0,0x1e2,0x1e3,0x1e4,0x1e6,0x1e8,0x1eb,0x1ee,0x1f2,0x1f4,0x1f5,0x1fa,0x1fb,0x200,0x201,0x202,0x203,0x206,0x20a,0x20c,0x20e,0x212,0x213,0x214,0x216,0x219,0x21a,0x21b,0x21c,0x21e,0x224,0x226,0x22a,0x22d,0x230,0x231,0x232,0x236,0x23c,0x23f,0x242,0x243,0x248,0x249,0x24e,0x24f,0x251,0x253,0x254,0x255,0x257,0x25a,0x25e,0x260,0x264,0x266,0x26a,0x26c,0x272,0x276,0x278,0x27a,0x27e,0x282,0x284,0x286,0x288,0x28a,0x28c,0x290,0x291,0x292,0x295,0x296,0x29a,0x29b,0x29c,0x29d,0x29f,0x2a3,0x2a5,0x2a8,0x2a9,0x2ab,0x2ae,0x2b0,0x2b1,0x2b3,0x2b4,0x2ba,0x2bc,0x2bd,0x2c0,0x2c3,0x2c6,0x2c9,0x2cc,0x2cd,0x2cf,0x2d2,0x2d6,0x2db,0x2dc,0x2de,0x2e0,0x2e4,0x2e5,0x2e8,0x2ea,0x2eb,0x2f0,0x2f2,0x2f4,0x2f7,0x2f9,0x2fa,0x2fc,0x2ff,0x306,0x308,0x30c,0x30e,0x314,0x31d,0x31f,0x322,0x324,0x328,0x32a,0x32e,0x337,0x338,0x33a,0x342,0x344,0x34c,0x34e,0x350,0x357,0x35c,0x362,0x368,0x36e,0x372,0x374,0x375,0x37a,0x380,0x63376,0x63665,0x63674,0x73372,0x73373,0x7b370,0x7b687,0xc8f21,0xc8f32,0x13bc76,0x9b5652,0x9b5760,0x9b5763,0x9b5764,0x9b6632,0x9b6643,0x9b6653,0x9b6761,0x9b6762,0x9b6763,0x9b6764,0xab3632,0xab3650,0xab3651,0xab3652,0xab3721,0xab3732,0xab3760,0xab3761,0xab3762,0xab3763,0xab6651,0xab6652,0xab6653,0xab6742,0xab6762,0xab6763,0xab6764,0xb33540,0xb33541,0xb33610,0xb33620,0xb33621,0xb33642,0xb33650,0xb33651,0xb33652,0xb33760,0xb33761,0xb33762,0xb35650,0xb35760,0xb35761,0xb35762,0xb35763,0x100f210,0x100f310,0x100f421,0x159c654,0x15bc432,0x15bc532,0x15bc543,0x15bc643,0x169a651,0x169a652,0x169a653,0x1719541,0x1719650,0x18b6532,0x18b6643,0x1a33521,0x1a33621,0x1a33632,0x200f321]
def read (_b stream : Nat) : Nat × Nat := (symbols[stream % 512]?.getD 0,stream/512)
def pool : Nat→Nat→List W
  | 0,_=>[]
  | k+1,stream=>BitVec.ofNat 128 ((words[stream % 256]?.getD 0)*18446744073709551617)::pool k (stream/256)
def s0g0 : Array Nat := #[0x42c23cb72da736]
def s0 : Array (Array Nat) := #[s0g0]
def h0g0 : Array Nat := #[0x80402010000000000080402010f8300a170000000000080402010f03408160d02810130000000000080402010e03804150c82c0c120c0240e11]
def h0 : Array (Array Nat) := #[h0g0]
def c0g0 : Array Nat := #[0]
def c0 : Array (Array Nat) := #[c0g0]
def s1g0 : Array Nat := #[0x42c23cb72da704bc,0x42c23cb72da70fbc,0x42c23cb72da7143c,0x42c23cb72da71f3c,0x42c23cb72da7253c,0x42c23cb7342da73c,0x42c23e3cb72da73c]
def s1 : Array (Array Nat) := #[s1g0]
def h1g0 : Array Nat := #[0x1008040200000000001008040247120646a00000000001008040246128606841108806200000000001008040244158c22b0e884487e280e0b87c270e8b40000000000000000000201008040201008048915b48ec72020956eaf07860e8700308d6aad08858c22552,0x10080402000000000010080402932f8a9000000000000100804029032888f28a31174ea0000000000100804028e35070e486349be59249349cfc63309b40000000000000000000201008040201008051a8403162cf5d83c810d2cb29f0f04d2b572a1198f1be4f48,0x402010080000000000000010080402b9162be1f349cc44000000000020100805709a1329d686b302840000000000201008056c9c12295646c2fa7d5a68332780000000000000000000201008040201008055f34a9ae6736a55290a05aafd36372254a8ca459af5323920,0x20100804000000000020100805c09e19b40000000000020100805bca017b2dae763731c000000000020100805b8a216b25aa7736b159c7138526534a945b4000000000000000000020100804020100805b4c00ab0ad14185d11a6be2bb06c13f8f508e329959c2512a,0x4020100800000000004020100bc54a3772800000000004020100bc14c36723b0f67a6880000000000000010080402ee580c2a936aac49d28339329d08139b2400000000000000000002010080402010080561369c39d305b6258e6520a2b992e5c61d8a6321a20c22514,0x2010080400000000002010080602ad21bb40000000000164000000000005b80201008040201008060055253e2d71d8bd85f64f4cb8ecd1a99d44000000000020100805feb3203a9f48b3fb610f2a96800000000004020100bf56a3e743e5187e6b222572e4421d9d2da4cba956d,0x10080402010080402000000000010080402448a4540000000000201008060cbb083ded93b8556608b624bcc0000000000201008060abc073d6d73c84d6206b7243ca049248b8400000000002010080575389d2e888ee8ad5275557f2551cdd7ea511edc]
def h1 : Array (Array Nat) := #[h1g0]
def c1g0 : Array Nat := #[0,0,0,0,0,0,0]
def c1 : Array (Array Nat) := #[c1g0]
def s2g0 : Array Nat := #[0x42c23cb72da7048142,0x42c23cb72da70f8142,0x42c2413cb72da70142,0x42c23cb72da7048342,0x42c23cb72da71f0342,0x42c23cb72da70504c2,0x42c23cb72da70f84c2,0x42c23cb72da71184c2,0x42c23cb72da71404c2,0x42c23cb72da71a04c2,0x42c23cb72da71b04c2,0x42c23cb72da71f04c2,0x42c23cb72da72504c2,0x42c23cb72dab2704c2,0x42c23cb72daca704c2,0x42c23cb72dad2704c2,0x42c23cb72e2da704c2,0x42c23cb7342da704c2,0x42c23cbab72da704c2,0x42c23e3cb72da704c2,0x42c23f3cb72da704c2,0x42c23cb7342da70642,0x42c23cb72da70f8842,0x42c23cbab72da70842]
def s2g1 : Array Nat := #[0x42c23cb72da71409c2,0x42c23cbab72da709c2,0x42c23cb72da70f8c42,0x42c23cb72da71f0c42,0x42c23cb72da70f8dc2,0x42c23cb72da7140dc2,0x42c23cb72da7250dc2,0x42c23cb72da7118fc2,0x42c23cb72da7140fc2,0x42c23cb72da7158fc2,0x42c23cb72da7178fc2,0x42c23cb72da7180fc2,0x42c23cb72da71a8fc2,0x42c23cb72da71b0fc2,0x42c23cb72da71f0fc2,0x42c23cb72da7220fc2,0x42c23cb72da7250fc2,0x42c23cb72dab270fc2,0x42c23cb72dac270fc2,0x42c23cb72daca70fc2,0x42c23cb72eada70fc2,0x42c23cb7342da70fc2,0x42c23cb7362da70fc2,0x42c23cb7b72da70fc2]
def s2g2 : Array Nat := #[0x42c23cb9372da70fc2,0x42c23cbab72da70fc2,0x42c23d3cb72da70fc2,0x42c23e3cb72da70fc2,0x42c23f3cb72da70fc2,0x42c2413cb72da70fc2,0x42c23cb7362da71042,0x42c23cb7342da71342,0x42c23cb72da7181442,0x42c23cb72da71f1442,0x42c23cb72da7221442,0x42c23cb72da7229442,0x42c23cb72da7251442,0x42c23cb72daa271442,0x42c23cb7342da71442,0x42c23cb7362da71442,0x42c23cb9372da71442,0x42c23e3cb72da71442,0x42c2413cb72da71442,0x42c23e3cb72da714c2,0x42c23cb72dab2716c2,0x42c23cb72dab271942,0x42c23cb72da71f1cc2,0x42c23cb72da71f1dc2]
def s2g3 : Array Nat := #[0x42c23cb72da7251dc2,0x42c23cb72da7221f42,0x42c23cb72da7251f42,0x42c23cb7342da71f42,0x42c23cb7362da71f42,0x42c23cb8372da71f42,0x42c23cb9372da71f42,0x42c23dbcb72da71f42,0x42c23e3cb72da71f42,0x42c2413cb72da71f42,0x42c23cbab72da72442,0x42c23cb72daca72542,0x42c23cb732ada72542,0x42c23cb7342da72542,0x42c23cbab72da72542,0x42c23e3cb72da72542,0x42c23f3cb72da72542,0x42c23f3cb72da72642,0x42c23cb734312da742,0x42c23cb937342da742,0x42c23cbc37342da742,0x42c23e3cb7342da742,0x42c240bcb7342da742,0x42c2413cb7342da742]
def s2g4 : Array Nat := #[0x42c23f3e3cb72da742,0x42c240be3cb72da742,0x42c23cb72da7013b,0x42c23cb72da7033b,0x42c2372da71b04bb,0x42c23cb72d9b04bb,0x42c23cb72da504bb,0x42c23cb72da704bb,0x42c23e372da704bb,0x42c23cb72da7063b,0x42c23cb72da7083b,0x42c23cb72da709bb,0x42c23cb72da70c3b,0x42c23cb72da70dbb,0x42c23cada71a8fbb,0x42c23cb72da20fbb,0x42c23cb72da70fbb,0x42c23cb92da70fbb,0x42c23cb72da7103b,0x42c23cb72da7133b,0x42c237362da7143b,0x42c23cb72da7143b,0x42c2413cada7143b,0x42c23cb72da714bb]
def s2g5 : Array Nat := #[0x42c23cb72da716bb,0x42c23cb72da7193b,0x42c23cb72da71cbb,0x42c23cb72da71dbb,0x42c23cb72da71f3b,0x42c23cb734271f3b,0x42c23cb72da71fbb,0x42c23cb72da7213b,0x42c23cb72da7243b,0x42c23cb72da7253b,0x42c23e372da7253b,0x42c23e3cb72da53b,0x42c23cb72da725bb,0x42c23cb72da7263b,0x42c23cb72da7a73b,0x42c23cb72da8a73b,0x42c23cb72da9273b,0x42c23cb72daa273b,0x42c23cb7302da73b,0x42c23cb7312da73b,0x42c23cb7322da73b,0x423cb73433ada73b,0x42c23cb7342da73b,0x42c23cbc372da73b]
def s2g6 : Array Nat := #[0x42c23d3cb72da73b,0x42c23dbcb72da73b,0x42c23e3cb72da73b,0x42c240bcb72da73b,0x42c23cb7341f34,0x423cb733ada734]
def s2 : Array (Array Nat) := #[s2g0,s2g1,s2g2,s2g3,s2g4,s2g5,s2g6]
def h2g0 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20100804000000000020100806eb75badd4000000000020100806eb75badd6eb75bae4f0192c9800000000004020100dd6eb75c9e532793badd6eb75badd6eb75000000000000000000008040201008040201badd6eb75c964b2793bae4f2575c9862eb75badd72793c9e4c000000000000000000020100804020100806eb93c95d6eb75bae4b2593c9dd6eb75bae7f4793c9dd72793badd6eb75c9e4f2793c9e4f279357258bc56,0x0,0x0,0x0,0x0,0x0,0x4020100800000000004020100dd6eb75ba800000000004020100dd6eb75badd6eb75c0e0b259331000000000000000000004020100804020100dd6eb75bae33698dda5d70583bae4f2600000000001008040375badd4380606046eb75badd6eb75badd6eb75badd7198dda6d0000000000000000000020100804020100806ea1c29dd6eb75bae8b3da3cfdd6eb75bae7b459fd1dd6eb75ba8802b93c990b4402d1c25d6582cdd4224c,0x0,0x0,0x0,0x0,0x4020100800000000003220000000000035004020100804020100dd6eb75bae4f2592c9e4f246134800000000004020100dd6eb75badd72793000000000008040201badd6eb75bae0f0575badd72781c1648c400000000001008040375badd72593c964aeb75badd72593c9e4eeb75badd6eb75badd4000000000000000000020100804020100806eb92c0dd6eb75bae4b2593c9e8b0392c94f656542fdd6eb75bae8b3d92c95d6eb75bae0b0592c95d72592,0x0,0x0,0x0,0x0,0x0]
def h2g1 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8040201000000000008040201badd6eb7500000000000000020100806eb75bae9749a4d2dd6eb75ba800000000004020100dd6eb75badd6eb75d25eb49a4badd6eb75000000000000000000008040201008040201bae934775badd6eb92d1e4f4975d268eeb75badd7262bc9e90000000000000000000020100804020100806eb75badd705a3c1e92eba4d1dd6eb75bae0f4783d25d74832badd6eb75d26932793d260f49836a2c52078,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8040201000000000008040201badd6eb7500000000000000020100806eb75bae8f49a3d25d6eb75ba800000000000000000004020100804020100dd749a4badd6eb75c969327a3bae934800000000001008040375badd6eb75badd7477ad1e8eeb75badd6eb75badd72593d86c0000000000000000000020100804020100806eb75badd705a2c1e8eeba3d15d6eb75bae0f4583d1dd6eb75bae8f4793c9e0f4583d1c7e1a7e46dd7464b,0x0,0x0,0x0,0x0]
def h2g2 : Array Nat := #[0x0,0x0,0x0,0x0,0x20100804020100804000000000020100806eba4d2000000000004020100dd6eb75bae4b27a4d1e93469e51dd6eb75ba800000000004020100dd749a4badd6eba4d1e934775badd6ea00000000001008040375badd6eb8cc6e4f2775badd6eb75badd7477ad1e8eeb75badd4000000000000000000020100804020100806eb75badd747a3c9e4f4da2c168e87232a266eb75badd74da2c168eeba3d15d6eb75bae0b4582d1dd74651,0x0,0x0,0x0,0x0,0x100804020000000000000004020100dd6eb75050c0680f000000000008040201badd6eb75badd6eb75000000000008040201badd6eb75badd6eb75badd6eb8bc667f40c1000000000000000000008040201008040201badd6eb75c96df27b7badd6eb75c96df27b7bae331b75d0680000000000000000000020100804020100806ea30255d46850badd6eb75c19170629badd6eb75c19130627badd6eb751c0b72793c18fb062487391148d,0x0,0x0,0x0,0x0,0x100804020000000000000004020100dd6eb75c6e33198d0000000000062400000000000c3008040201008040201badd6eb75c664f1b92badd6eb75c6e33258dc9e3172c2000000000008040201badd6eb75badd6eb75bae831600000000001008040375badd6eb75badd6eb75c6e32eb75bae2f178ccfb04000000000000000000020100804020100806eb8cc5dd7198bbadd6eb75c66332793c1e2f078c9f458eab2badd6eb75c1e7b078cbadd6eb75c1e33078c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h2g3 : Array Nat := #[0x0,0x0,0x0,0x0,0x100804020000000000000004020100dd6eb75268c09c14000000000000000000008040201008040201ba8c063750a06c000000000020100806eb75badd6eb75badd6eb75badd70583d4ea4000000000020100806eb75badd6eb75badd6eb75badd70583d4ea6eb75bae2b179ecfbec000000000000000000020100804020100806eb75badd745b6c96daeb75badd745b6c96daeb75badd70583d4ea745b6c96da4acf49b82eb8bc65d73f9f,0x0,0x0,0x0,0x0,0x4020100804020100800000000004020100dd4361f000000000008040201ba8c46975badd43e4d1a138000000000020100806eb75badd70583be5f07848663beeb75badd6eb75badd4000000000020100806eb75badd6f7a9c1e0c7a4666bbaeb75badd6eb75badd6eb75bae2b179ecfc14000000000000000000020100804020100806eb75badd75ba9c1e0f4db6c96da8cdf2b3b2eb75badd74db6c96daeb75badd745b6c96daeb8bc65d73f9f,0x0,0x0,0x0,0x0,0x1008040200000000000c88000000000023601008040201008040375badd6eb93c964b2793c91d23200000000001008040375badd6eb75c9e4c000000000020100806eb75badd6eb83c15d6eb75c9e0705927e0000000000000001008040375badd72593c0e4aeb75badd72593c9e4f25925ec52eb75badd6eb75badd4000000000000000000020100804020100806eb93c95d6eb75bae4b2793c9e8b2592c95017e78885d6eb75bae8b2592c95d6eb75bae0b0582c15d72592,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4020100804020100800000000004020100dd7198c000000000008040201bae331975badd7198bc662c0000000000188000000000004e4020100804020100806eb75badd70583c662f178cc962e8e892bcb2eb75badd71792c662eeb75badd7178cc962c000000000020100806eb75badd70583cfdf2eb75badd6eb75badd6eb9fcf800000000004020100dd6eb75bae2f1983c1dd6eb75badd6eb75badd7198bbadd6eb9fc562f3d05]
def h2g4 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h2g5 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h2g6 : Array Nat := #[0x0,0x0,0x0,0x0,0x100804020000000000100804030560991f600000000000a7804020100c0d046f7cc00f6bb7c000000000004020100c05b65b733f5a48e71366974e,0x80402010080402019cb0cd71d0080402019ba14db27999f56d130080402019ab18cf18982ad42f60026c00000080402019a320cb1797ab13ef4002740000002a14cf0]
def h2 : Array (Array Nat) := #[h2g0,h2g1,h2g2,h2g3,h2g4,h2g5,h2g6]
def c2g0 : Array Nat := #[0x101,0x101,0x381,0x101,0x81,0x401,0x101,0,0x401,0x281,0x281,0x101,0x101,0,0x401,0x401,0x401,0x281,0,0x281,0x401,0x281,0x101,0x301]
def c2g1 : Array Nat := #[0x381,0x301,0x101,0x81,0x101,0x381,0x101,0x381,0x381,0x101,0x381,0,0x281,0x281,0x101,0x101,0x101,0x381,0x381,0,0x381,0x281,0x381,0x381]
def c2g2 : Array Nat := #[0x281,0x381,0x381,0x281,0,0x381,0x481,0x281,0x481,0,0x381,0x381,0x481,0x381,0,0x381,0x381,0x401,0x381,0x281,0x501,0x501,0x81,0x81]
def c2g3 : Array Nat := #[0x101,0x101,0x101,0x281,0,0x581,0x281,0x581,0x281,0,0x301,0x481,0x481,0x281,0,0x281,0x401,0x301,0x281,0x281,0x281,0x281,0x281,0]
def c2g4 : Array Nat := #[0x401,0x281,0x381,0x401,0x281,0x401,0x401,0x401,0x281,0x401,0x301,0x301,0x381,0x381,0x281,0x381,0x381,0x281,0x601,0x381,0x381,0x381,0x381,0x381]
def c2g5 : Array Nat := #[0x601,0x481,0x501,0x481,0x581,0x281,0x601,0x601,0x601,0x481,0x281,0x401,0x601,0x601,0x281,0x281,0x481,0x281,0x281,0x481,0x281,0x281,0x281,0x281]
def c2g6 : Array Nat := #[0x401,0x401,0x281,0x281,0,0]
def c2 : Array (Array Nat) := #[c2g0,c2g1,c2g2,c2g3,c2g4,c2g5,c2g6]
def s3g0 : Array Nat := #[0x42c23cb72dab270241,0x42c2372dab271b04c1,0x42c23cb72dab1b04c1,0x42c23cb72dab2504c1,0x42c23cb72daaa704c1,0x42c23cb72dab2704c1,0x42c23e372dab2704c1,0x42c23cb72daba704c1,0x42c23cb72da71f0bc1,0x42c23cb72da71f0dc1,0x42c23cb72da71f8fc1,0x42c23cb72da71d1441,0x42c237362da71f1441,0x42c23cb72da71f1441,0x42c2413cada71f1441,0x42c23cb72da7219441,0x42c23e3cadab2714c1,0x42c23cb72da71f1d41,0x42c23cb72da7201f41,0x42c23cb72da7229f41,0x42c2413cb72da69f41,0x42c23cb7362da71f41,0x42c24137362da71f41,0x42c2413cb62da71f41]
def s3g1 : Array Nat := #[0x42c2413cb72da71f41,0x42c23cb72da7003a,0x42c23cb72da700ba,0x42c23cb72da701ba,0x42c23cb72da7023a,0x42c23cb72da702ba,0x42c23cb7341f033a,0x42c23cb72da703ba,0x42c23cb72da7043a,0x42c2372da70684ba,0x42c23cbaab2704ba,0x423cb733ada704ba,0x42c239b72da704ba,0x423cba372da704ba,0x423cb733ada705ba,0x42c23cb7341f063a,0x42c237362da7063a,0x42c23cb72da7073a,0x42c23cb72da707ba,0x42c23cbaab27083a,0x423cba372da708ba,0x42c23cb72da7093a,0x42c23cbaab2709ba,0x423cba372da70a3a]
def s3g2 : Array Nat := #[0x42c23cb72da70aba,0x42c23cb72da70b3a,0x42c23cb72da70bba,0x42c23cb7341f0c3a,0x42c23cb72da70cba,0x42c23cb72da70d3a,0x42c23cb72da70e3a,0x42c23cb72da70eba,0x423cb8b72da70f3a,0x42c23cada7150fba,0x423cb733ada70fba,0x42c23cb6ada70fba,0x423cb8b72da70fba,0x423cba372da70fba,0x42c23cb72da710ba,0x42c23cb72da7113a,0x42c23cb72da7123a,0x423cb733ada712ba,0x42c23cada714133a,0x42c23cb7341f133a,0x42c23cb62da7133a,0x42c23cb72da713ba,0x42c23cb7341f143a,0x42c23caf2da7143a]
def s3g3 : Array Nat := #[0x423cb733ada7143a,0x423cb8b72da7143a,0x42c23cadab2714ba,0x42c23cb72da7163a,0x42c23cbaab2716ba,0x42c23cb72da7173a,0x42c23cbaab2718ba,0x42c23cbaab27193a,0x42c23cb72da719ba,0x42c23cb72da71c3a,0x42c23cb7341f1cba,0x42c23cb72da71d3a,0x42c23cb7341f1dba,0x42c23cb72da71e3a,0x42c23cb72da71eba,0x42c23cb72da69f3a,0x423cb733ada71f3a,0x423cb8b72da71f3a,0x42c23cb7342f1f3a,0x42c23cb734311f3a,0x42c23cb736341f3a,0x42c23cb837341f3a,0x42c23cbc37341f3a,0x42c23dbcb7341f3a]
def s3g4 : Array Nat := #[0x42c240bcb7341f3a,0x42c2413cb7341f3a,0x42c23cb72da7203a,0x42c23cb72da720ba,0x42c23cb72da721ba,0x42c23cb72da7233a,0x423cba372da723ba,0x42c23cb72da5243a,0x42c23cb72da724ba,0x423cb733ada7253a,0x42c239b72da7253a,0x423cba372da7253a,0x42c23cb72da8273a,0x42c23cb72da9a73a,0x42c23cb72fada73a,0x423cb733b0ada73a,0x42c23cb731ada73a,0x42c23cb7332da73a,0x423cb93733ada73a,0x423cbbb733ada73a,0x423e3cb733ada73a,0x42403cb733ada73a,0x42413cb733ada73a,0x42c23cb734ada73a]
def s3g5 : Array Nat := #[0x42c23cb735ada73a,0x42c23cbb372da73a,0x42c23ebcb72da73a,0x42c23fbcb72da73a,0x42c241bcb72da73a,0x42c23cab2718b3,0x42c23cbaa718b3,0x423cb734339f33]
def s3 : Array (Array Nat) := #[s3g0,s3g1,s3g2,s3g3,s3g4,s3g5]
def h3g0 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h3g1 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8040201000000000005f4020100806df6fb7dbeff8f000000000008040201b7dbedf6fb780b1c0000000000100804036fb7dbf1f7fc7e3edf6fb7dbedf6fb7dbc000000000000000000020100804020100806df8fc75bedf6fb7e6f1d8fc7dbedf6fb786b378fc7dbf1f8f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h3g2 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8040201000000000008040201b7dbedf6f000000000008040201b7dbedf6fb7dbedf6f000000000008040201b7dbedf6fb7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fc361aff8fb7dbedf6fc361b1f9cb7dbedf6fbfe6eff9cb7dbedf6fbfe3eff8f,0x0,0x0,0x0,0x0,0x0,0x0,0x8040201000000000008040201b7dbedf6f000000000008040201b7dbedf6fb7dbedf6f000000000008040201b7dbedf6fb7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fc361aff8fb7dbedf6fc361b1f9cb7dbedf6fbfe6eff9cb7dbedf6fbfe3eff8f,0x201008040000000000000008040201b7dbedf9dc361b3a00000000000cc804020100dbedf6fb7dbedf6fb7e770c0000000000100804036fb7dbedf6fb7dbedf6f03618000000000000000000020100804020100806df86cddbf0d9bb7dbedf6fbfe6eff86b7dbedf6fbf856ff86,0x0]
def h3g3 : Array Nat := #[0x4020100804020100ddae376cd6134db8008040201bb5deef76bc5e2f178dc698020100806ed71b8dc6f178bc5e0017800000020100806ed71bc5e2f178bc5e00178000000178bc5e0020100804020100806ed84cc5db4d98bc5e2f1780e6bb09afbc5e2f178bf6cafd84bc5e2f178bf6befdaf,0x0,0x0,0x0,0x0,0x201008040000000000000008040201b7dbedf6f000000000008040201b7dbedf6fb7dbedf6f000000000008040201b7dbedf6fb7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fcde6eff9cb7dbedf6fcde6f1f7fb7dbedf6fbfe6eff8fb7dbedf6fbfeceff9c,0x0,0x0,0x8040201000000000008040201b7dbedf6f000000000008040201b7dbedf6fb7dbedf6f000000000008040201b7dbedf6fb7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fc366eff9cb7dbedf6fc366f1f7fb7dbedf6fc3686ff8fb7dbedf6fbfeceffb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x804020100000000000000020100806df6fb7e6f0d9bc3000000000000000000004020100804020100dbf0d86b7e1b0c00000000000cb804020100dbedf6fb7e1b376fb7dbedf86cddbedf6fb7e6eff86cd800000000004020100dbedf6fb7dbedf6fb7dbedf6fb7de6ffacd65bc1f9b,0x0,0x0,0x0]
def h3g4 : Array Nat := #[0x0,0x20100804020100804000000000020100806df86c3000000000004020100dbf0d86b7dbedf86cde1b3600000000000cb804020100dbedf6fb7e6eff86cde1b3623125bedf6fb7dbedf6fb7800000000004020100dbedf6fb7eaf597fbfdbedf6fb7dbedf6fb7dbc299b,0x8040201000000000008040201b7dbedf6f000000000008040201b7dbedf6fb7dbedf6f000000000008040201b7dbedf6fb7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fd35ff1f7fb7dbedf6fd0dff1fb5b7dbedf6fbfe3effacb7dbedf6fc7dff1f7f,0x0,0x8040201000000000008040201b7dbedf6f000000000008040201b7dbedf6fb7dbedf6f000000000008040201b7dbedf6fb7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fd35feff7fb7dbedf6fd36d71fb3b7dbedf6fbfdfeff7fb7dbedf6fbfdfeff7f,0x0,0x0,0x0,0x20100804000000000020100806df6fb7dbc000000000020100806df6fb7dbedf6fb7dbc000000000020100806df6fb7dbf2190b7dbedf6fb7dbedf6f000000000000000000008040201008040201b7dbedf6fcddfeff7fb7dbedf6fcddff1f8fb7dbedf6fbfdfeff7fb7dbedf6fbfdfeff7f,0x0,0x0,0x0,0x20100804000000000020100806df6fb7dbc000000000020100806df6fb7dbedf6fb7dbc000000000000000000020100804020100806df6fb7dbf377fc7dfedf6fb7dbf378fc7e3edf6fb7dbeff87bfec40000000000000008040201b7dbedf6fb7dbedf6fb7dbedf6fb7dbedf6fc7e3eff7f,0x20100804000000000020100806df6fb7dbc000000000020100806df6fb7dbedf6fb7dbc000000000000000000020100804020100806df6fb7dbf377fc7dfedf6fb7dbf378fc7e3edf6fb7dbeffacbfeb0000000000020100806df6fb7dbedf6fb7dbf2190b7dbedf6fb7dbedf6fc7e3eff7f,0x8040201000000000008040201b7dbedf6f000000000000000000008040201008040201b7dbedf6fc35ff397fb7dbedf6fc35ff1f86000000000008040201b7dbedf6fb7dbedf6fb7dbedf6fbfdff1f9b000000000008040201b7dbedf6fb7dbedf6fb7dbedf6fc36b2ff7fb7dbedf6f,0x0,0x20100804000000000020100806df6fb7dbf1f86000000000000000000008040201008040201b7dbedf6fc35ff1f7fb7dbedf6fc363f1f86000000000008040201b7dbedf6fb7dbedf6fb7dbedf6fbfdff399b000000000008040201b7dbedf6fb7dbedf6fb7dbedf6fc363eff7fb7dbedf6f,0x100804020000000000100804036fb7dbedf9cc36730c0000000000000000000100804020100804036fb7dbedf86bfe72ff6fb7dbedf86bfe3f0c0000000000100804036fb7dbedf6fb7dbedf6fb7dbedf7fbfe3f360000000000100804036fb7dbedf6fb7dbedf6fb7dbedf86d65feff6fb7dbedf9cc2e1b3624,0x0,0x0,0x0,0x0,0x1008040201008040201008040376c2610020100806ed84d35daed74c26634d98008040201ba5daed74d3ea75faeba5daed74ba5daed74008040201ba5ceed74cc5fb51b2ba5ceed74ba5cee774005d80000008040201b95caed72d3ea6fd7eb95caed72b95cae572005d80000005cae773,0x0]
def h3g5 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h3 : Array (Array Nat) := #[h3g0,h3g1,h3g2,h3g3,h3g4,h3g5]
def c3g0 : Array Nat := #[0x438,0x2b3,0x438,0x438,0x438,0x438,0x2b3,0x438,0x81,0x101,0x101,0x3b3,0x3b3,0x3b3,0x3b3,0x3b3,0x2b3,0x81,0x59b,0x101,0x3b3,0x4b3,0x3b3,0x433]
def c3g1 : Array Nat := #[0x3b3,0x101,0x81,0x381,0x101,0x1,0x81,0x101,0x101,0x401,0,0x201,0x481,0x101,0x681,0x281,0x401,0x281,0x101,0x301,0x101,0x101,0x301,0x701]
def c3g2 : Array Nat := #[0x301,0x381,0x81,0x81,0x101,0x81,0x101,0x101,0x81,0x381,0x201,0x501,0x101,0x101,0,0x381,0x381,0x681,0x381,0x281,0x381,0,0,0x501]
def c3g3 : Array Nat := #[0,0x381,0x381,0x101,0x501,0,0x301,0x501,0,0x1,0x81,0x81,0x81,0x81,0x81,0x101,0x181,0x81,0x281,0x281,0,0x581,0x281,0x581]
def c3g4 : Array Nat := #[0x281,0,0,0x101,0,0x101,0x101,0x101,0,0x201,0x481,0x101,0,0,0,0x681,0,0,0x281,0x681,0x281,0x681,0,0x281]
def c3g5 : Array Nat := #[0x281,0x281,0x281,0x281,0x281,0x501,0x301,0x281]
def c3 : Array (Array Nat) := #[c3g0,c3g1,c3g2,c3g3,c3g4,c3g5]
def s4g0 : Array Nat := #[0x42c23cab271884b9,0x42c23cb71f1b9439,0x42c23cab272518b9,0x42c23e3cab2718b9,0x42c23cb7341f1d39,0x42c23cb734201f39,0x423cb73533ada739,0x42c23cab270ab2,0x42c23cb7331f32]
def s4 : Array (Array Nat) := #[s4g0]
def h4g0 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20100804000000000020100806e170b85c32d95cb654000000000020100806e170b85c2e170b85c0000000000020100806e170b85c2e170b85c2e170b85c355aa]
def h4 : Array (Array Nat) := #[h4g0]
def c4g0 : Array Nat := #[0x51a,0x598,0x534,0x504,0x81,0x59b,0x681,0x301,0]
def c4 : Array (Array Nat) := #[c4g0]
def s5 : Array (Array Nat) := #[]
def h5 : Array (Array Nat) := #[]
def c5 : Array (Array Nat) := #[]
def sLevels : Array (Array (Array Nat)) := #[s0,s1,s2,s3,s4,s5]
def hLevels : Array (Array (Array Nat)) := #[h0,h1,h2,h3,h4,h5]
def cLevels : Array (Array (Array Nat)) := #[c0,c1,c2,c3,c4,c5]
def sizes : Array Nat := #[1,7,150,128,9,0]
def size (d:Nat) := sizes[d]?.getD 0
def get (a:Array (Array (Array Nat))) (d i:Nat) : Nat := (((a[d]?.getD #[])[i/24]?.getD #[])[i % 24]?).getD 0
def next (d i:Nat) : Option (List W × Nat) := if i<size d then
  let z:=get sLevels d i
  some (pool ((z/8) % 16) (z/128),z % 8)
  else none
def hint (d i:Nat) := get hLevels d i
def cert (d i:Nat) := get cLevels d i
end LiveAIG.Small12122.Data

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

namespace LiveAIG.FourPin
open FreeAIG FlatProjection
abbrev B := Fin 16
abbrev T := BitVec 16
def obs (w:T) : Fn B := fun r=>w[r.val]
def raw : List T := [0xaaaa,0xcccc,0xf0f0,0xff00]
def base (xs : List T) : Set (Fn B) := {f | ∃w∈xs,f=obs w}
def goal : T := 0xfee8
theorem negOut {α : Type} {S : Set (Fn α)} {k f} (h : Has S k f) : Has S k (neg f) := by
  induction h with
  | done a=>exact .done a.neg
  | step a b _ ih=>exact .step a b ih
theorem obsc (w:T) : obs (~~~w)=neg (obs w) := by funext r; simp [obs,FreeAIG.neg]
private theorem transferCore : CommonArchive.Lower true (CommonArchive.varsX 45)
    (CommonArchive.graphGoal 45) 7 := by
  exact CommonArchive.low45

private def coords (r : Fin 512) : B :=
  ⟨(r.val % 2+2*(r.val/4 % 2)+4*(r.val/8 % 2)+8*(r.val/32 % 2)) % 16,by omega⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Has (base raw) k (obs goal)) : 7≤k := by
  apply MinorTransfer.imported transferCore
  let roots:=CommonArchive.varsX 45
  have m : Has {g | g∈roots.map CommonArchive.observe} k (obs goal ∘ coords) :=
    h.map coords (by
      rintro _ ⟨w,wm,rfl⟩
      apply Avail.src
      apply List.mem_map.mpr
      have cover : ∀ v∈raw, ∃u∈roots,∀ r,CommonArchive.observe u r=obs v (coords r) := by
        intro v hv
        simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl
        · exact ⟨roots[0]!,by decide +kernel,by decide +kernel⟩
        · exact ⟨roots[1]!,by decide +kernel,by decide +kernel⟩
        · exact ⟨roots[2]!,by decide +kernel,by decide +kernel⟩
        · exact ⟨roots[3]!,by decide +kernel,by decide +kernel⟩
      obtain ⟨u,hu,eq⟩:=cover w wm
      exact ⟨u,hu,funext eq⟩)
  have eq : obs goal ∘ coords = CommonArchive.observe (CommonArchive.graphGoal 45) := by
    funext r;exact (show ∀ j,obs goal (coords j)=_ from by decide +kernel) r
  rwa [eq] at m

def row (rows : Nat) (j : B) : R := ⟨(rows >>> (7*j.val)) % 128,by omega⟩
def sample (rows : Nat) (w : W) : T := K4Core.pack (read (row rows) w)
theorem sampleEq (rows : Nat) (w : W) : obs (sample rows w)=read (row rows) w :=
  funext (fun i=>K4Core.pack_get _ i)
def literal (w:T) (b:Bool) := if b then ~~~w else w
def codeWord (g:Nat) : T :=
  let z:=g-1
  literal (raw[z % 4]?.getD 0) (z.testBit 4) &&& literal (raw[z/4 % 4]?.getD 0) (z.testBit 5)
def bank (g:Nat) := if g=0 then raw else codeWord g::raw
def plain (v:T) := v==0 || v==65535
def supplied (xs:List T) (v:T) := plain v || xs.contains v || xs.contains (~~~v)
def test (t:W) (s:List W) (max rows gate:Nat) :=
  let z:=sample rows t
  let ws:=s.map (sample rows)
  (z==goal || z==~~~goal) && ws.all (supplied (bank gate)) &&
    decide (max+(gate != 0).toNat < 7+ws.countP plain)
theorem constantWord {v:T} (good : plain v=true) : constant (obs v) := by
  simp only [plain,Bool.or_eq_true,beq_iff_eq] at good
  rcases good with rfl|rfl
  · exact ⟨false,by funext i;simp [obs]⟩
  · exact ⟨true,by funext i;exact (show ∀j:B,(65535:T)[j.val]=true from by decide +kernel) i⟩
theorem canSupply {xs v} (h:supplied xs v=true) : Avail (base xs) (obs v) := by
  simp only [supplied,Bool.or_eq_true,List.contains_iff_mem] at h
  rcases h with (h|h)|h
  · obtain ⟨b,e⟩:=constantWord h;rw [e];exact .const b
  · exact .src ⟨_,h,rfl⟩
  · have one:=Avail.neg (Avail.src (S:=base xs) (f:=obs (~~~v)) ⟨_,h,rfl⟩)
    rw [←obsc,BitVec.not_not] at one
    exact one
private theorem both (w:T) (b:Bool) (h:Avail (base raw) (obs w)) : Avail (base raw) (obs (literal w b)) := by
  cases b
  · exact h
  · exact obsc w ▸ h.neg
private theorem cost {g k f} (h:Has (base (bank g)) k f) : Has (base raw) (k+(g != 0).toNat) f := by
  by_cases gz:g=0
  · simpa [bank,gz] using h
  · let z:=g-1
    let a:=literal (raw[z % 4]?.getD 0) (z.testBit 4)
    let b:=literal (raw[z/4 % 4]?.getD 0) (z.testBit 5)
    have arg (i:Nat) : (raw[i % 4]?.getD 0)∈raw := by
      have lt:i % 4<4:=Nat.mod_lt _ (by decide)
      set n:=i % 4;interval_cases n <;> decide
    have srcA:=both _ (z.testBit 4) (.src ⟨_,arg z,rfl⟩)
    have srcB:=both _ (z.testBit 5) (.src ⟨_,arg (z/4),rfl⟩)
    have atGate : obs (codeWord g)=meet (obs a) (obs b) := by funext i;simp [a,b,z,codeWord,obs,meet]
    have hh:=h.map (T:=insert (meet (obs a) (obs b)) (base raw)) id (by
      rintro _ ⟨u,um,rfl⟩
      simp only [bank,if_neg gz,List.mem_cons] at um
      rcases um with rfl|old
      · exact .src (Set.mem_insert_iff.mpr (Or.inl atGate))
      · exact .src (Set.mem_insert_of_mem _ ⟨u,old,rfl⟩))
    have ge : (g != 0)=true := bne_iff_ne.mpr gz
    simpa [ge] using Has.step srcA srcB hh

theorem sound {t : W} {s : List W} {max rows gate n c : Nat} (good:test t s max rows gate=true) (hn : n ≤ max) : ¬Run t s n c := by
  intro run
  simp only [test,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,List.all_eq_true,List.mem_map,
    decide_eq_true_eq] at good
  obtain ⟨⟨eq,all⟩,less⟩:=good
  have proper : ¬constant (read (row rows) t) := by
    rw [←sampleEq]
    rcases eq with e|e <;> rw [e] <;> rintro ⟨b,h⟩ <;>
      have bad:=(congrFun h 0).trans (congrFun h 15).symm <;> exact (by decide : ¬(false = true)) (by first | exact bad | exact bad.symm)
  obtain ⟨k,save,net⟩:=saves (row rows) run proper (S:=base (bank gate)) (by
    intro w wm;rw [←sampleEq];exact canSupply (all _ ⟨w,wm,rfl⟩))
  have cnt : (s.map (sample rows)).countP plain ≤ s.countP (flat (row rows)) := by
    rw [List.countP_map];apply List.countP_mono_left
    intro w _ hw
    exact (flat_spec _ _).mpr (sampleEq rows w ▸ constantWord hw)
  have lo : 7≤k+(gate != 0).toNat := by
    rw [←sampleEq] at net
    rcases eq with e|e
    · rw [e] at net
      exact lower (cost net)
    · rw [e] at net
      have negated:=negOut (cost net)
      rw [←obsc,BitVec.not_not] at negated
      exact lower negated
  omega
end LiveAIG.FourPin

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

namespace LiveAIG.Small12122
open SixLayers SixLenses
def site (d i : Nat) := match Data.next d i with
  | none=>true
  | some p=>
    let z:=Data.cert d i
    if z=0 then checked cfg Data.read (Data.next (d+1)) p.1 p.2 (Data.hint d i)
    else FourPin.test target p.1 (11-d) (Data.rowCodes[(z-1)/128]?.getD 0) ((z-1) % 128)
def block (d g : Nat) := (List.range 8).all fun j=>site d (8*g+j)
theorem layer {d} (sm : d<11)
    (good : ∀g, g<(Data.size d+7)/8 → block d g=true)
    (later : ∀i p,Data.next (d+1) i=some p → Dead cfg (11-(d+1)) p) :
    ∀i p, Data.next d i=some p → Dead cfg (11-d) p := by
  intro i p hp
  have hi : i<Data.size d := by
    unfold Data.next at hp
    split at hp
    · assumption
    · contradiction
  have gd := good (i/8) (by omega)
  have ok := List.all_eq_true.mp gd (i % 8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  rw [Nat.div_add_mod] at ok
  simp only [site,hp] at ok
  split at ok
  · have h := checkedSound ok later
    exact (show 11-(d+1)+1=11-d by omega) ▸ h
  · intro _ _ n c hn _ hr
    exact FourPin.sound ok hn hr
end LiveAIG.Small12122

namespace LiveAIG.Small12122
open SixLayers
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem l5 : ∀i p,Data.next 5 i=some p → Dead cfg 6 p := by
  intro i p h
  have z : Data.size 5=0 := by decide +kernel
  simp [Data.next,z] at h
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good4_0 : block 4 0=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good4_1 : block 4 1=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem l4 : ∀i p,Data.next 4 i=some p → Dead cfg 7 p := by
  apply layer (by decide) _ l5
  intro g small
  change g<2 at small
  interval_cases g
  · exact good4_0
  · exact good4_1
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_0 : block 3 0=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_1 : block 3 1=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_2 : block 3 2=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_3 : block 3 3=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_4 : block 3 4=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_5 : block 3 5=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_6 : block 3 6=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_7 : block 3 7=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_8 : block 3 8=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_9 : block 3 9=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_10 : block 3 10=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_11 : block 3 11=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_12 : block 3 12=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_13 : block 3 13=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_14 : block 3 14=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good3_15 : block 3 15=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem l3 : ∀i p,Data.next 3 i=some p → Dead cfg 8 p := by
  apply layer (by decide) _ l4
  intro g small
  change g<16 at small
  interval_cases g
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_0 : block 2 0=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_1 : block 2 1=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_2 : block 2 2=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_3 : block 2 3=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_4 : block 2 4=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_5 : block 2 5=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_6 : block 2 6=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_7 : block 2 7=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_8 : block 2 8=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_9 : block 2 9=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_10 : block 2 10=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_11 : block 2 11=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_12 : block 2 12=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_13 : block 2 13=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_14 : block 2 14=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_15 : block 2 15=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_16 : block 2 16=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_17 : block 2 17=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good2_18 : block 2 18=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem l2 : ∀i p,Data.next 2 i=some p → Dead cfg 9 p := by
  apply layer (by decide) _ l3
  intro g small
  change g<19 at small
  interval_cases g
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
  · exact good2_10
  · exact good2_11
  · exact good2_12
  · exact good2_13
  · exact good2_14
  · exact good2_15
  · exact good2_16
  · exact good2_17
  · exact good2_18
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good1_0 : block 1 0=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem l1 : ∀i p,Data.next 1 i=some p → Dead cfg 10 p := by
  apply layer (by decide) _ l2
  intro g small
  change g<1 at small
  interval_cases g
  · exact good1_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem good0_0 : block 0 0=true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem l0 : ∀i p,Data.next 0 i=some p → Dead cfg 11 p := by
  apply layer (by decide) _ l1
  intro g small
  change g<1 at small
  interval_cases g
  · exact good0_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem core {k} (h : FreeAIG.Has FreeAIG.Inputs k Upper12122.target) : 12≤k := by
  by_contra! small
  obtain ⟨n,nk,c,run⟩:=SixStart.compile h
  have b:=balance run
  have len : SixStart.A.length=6 := by decide +kernel
  rw [len] at b
  have root : Data.next 0 0=some (SixStart.A,6) := by decide +kernel
  exact l0 0 _ root SixStart.tightF SixStart.tightE (by omega) (by omega) run
end LiveAIG.Small12122

end PEqualNP.Outside.L_meta_12122

theorem PEqualNP.Outside.L_meta_12122 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12122.Upper12122.completeFromSigned PEqualNP.Outside.L_meta_12122.LiveAIG.Small12122.core
