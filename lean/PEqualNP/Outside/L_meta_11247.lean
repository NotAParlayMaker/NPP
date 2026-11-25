import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11247_aux

-- The signed live-wire checker is adapted from the checked L-meta-3143 proof.
-- The six-input certificate restricts the input for vertex 2 to false.

namespace Theta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

inductive Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | done {a} (hg : Good m a) (nonzero : a≠0) : Live m 0 {a}
  | step {k U a b d} (hd : d<4) (ha : a≠0) (hb : b≠0) (diff : a≠b)
      (fresh : combine d a b ∉ insert a (insert b U))
      (next : Live m k (insert (combine d a b) U)) :
      Live m (k+1) (insert a (insert b U))

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction h with
  | done hg hn => simpa using hn
  | @step k U a b d hd ha hb ne fresh tail ih =>
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction h with
  | done hg hn => simp
  | @step k U a b d hd ha hb ne fresh tail ih =>
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at ih
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction h with
  | done hg hn => exact ⟨_,Finset.mem_singleton_self _,hg i hi⟩
  | @step k U a b d hd ha hb ne fresh tail ih =>
    obtain ⟨x,hx,dist⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases h with
    | done hg hn => exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _))
    | step hd _ _ _ _ _ => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases h with
    | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _)))
    | step hd _ _ ab fresh tail =>
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

structure Projection (m h : ℕ) where
  toFun : ℕ → ℕ
  atZero : toFun 0=0
  combineEq : ∀ d a b, d<4 → toFun (combine d a b)=combine d (toFun a) (toFun b)
  good : ∀ a, Good m a → Good h (toFun a)
  someRow : 0<h

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction live with
  | @done a hg hn =>
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | @step k U a b d hd ha hb ab fz tail ih =>
    obtain ⟨j,T,cost,ok,raw⟩ := ih
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i<m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i<m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i<m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j<m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r<m) : Projection m m where
  toFun := slice m q r
  atZero := by simp [slice,half]
  combineEq := slice_hom m q r
  good := by
    intro a ga i hi
    rw [slice_lo _ _ _ hi,slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi
  someRow := by omega

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def cutSearch (m q fuel : ℕ) (v : List ℕ) : Bool :=
  let r := min (Nat.log2 q) (m-1)
  let xs := v.map (slice m q r)
  let gone := xs.count 0
  gone≤fuel && start m (fuel-gone) xs

theorem cut_complete {m k S} (hm : 0<m) (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup)
    (q fuel : ℕ) (lim : k≤fuel) : cutSearch m q fuel v=true := by
  let r := min (Nat.log2 q) (m-1)
  let p := projection m q r (show r<m by dsimp [r];omega)
  obtain ⟨l,T,cost,live,sub⟩ := projectLive p h
  let xs := v.map (slice m q r)
  have fixed : dead p.toFun S=xs.count 0 := by
    rw [←rep];dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [xs,List.count_eq_countP,List.countP_map,p,projection,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at cost
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs,p,projection,←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]

def oneOutput (m fuel : ℕ) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : List (List ℕ) :=
  if optionStep m fuel (fun _ => true) rest n cv a b z ka kb then [z::save ka a (save kb b rest)] else []
def oneGate (m fuel : ℕ) (v rest : List ℕ) (n cv a b z : ℕ) :=
  if z != 0 && !(v.contains z) then
    oneOutput m fuel rest n cv a b z false false ++ oneOutput m fuel rest n cv a b z true false ++
    oneOutput m fuel rest n cv a b z false true ++ oneOutput m fuel rest n cv a b z true true
  else []
def onePair (m fuel : ℕ) (v : List ℕ) (a b : ℕ) :=
  if a<b then
    let rest := without v a b
    let gate := oneGate m fuel v rest rest.length (cover m rest) a b
    gate (a &&& b) ++ gate (a ||| b) ++ gate (a ^^^ (a &&& b)) ++ gate (b ^^^ (a &&& b))
  else []
def successors (m fuel : ℕ) (v : List ℕ) :=
  v.flatMap (fun a => v.flatMap (fun b => onePair m fuel v a b))
lemma output_any (m fuel : ℕ) (go : List ℕ→Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) :
    (oneOutput m fuel rest n cv a b z ka kb).any go=optionStep m fuel go rest n cv a b z ka kb := by
  have E (t : Bool) (x : List ℕ) : ((if t then [x] else []) : List (List ℕ)).any go = (t && go x) := by cases t <;> simp
  unfold oneOutput
  rw [E]
  simp only [optionStep,Bool.and_true]
lemma gate_any (m fuel : ℕ) (go : List ℕ→Bool) (v rest : List ℕ) (n cv a b z : ℕ) :
    (oneGate m fuel v rest n cv a b z).any go=gateStep m fuel go v rest n cv a b z := by
  have E (t : Bool) (xs : List (List ℕ)) : (if t then xs else []).any go = (t && xs.any go) := by cases t <;> simp
  unfold oneGate gateStep
  rw [E]
  simp only [List.any_append,output_any,Bool.or_assoc,Bool.and_assoc]
lemma pair_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) (a b : ℕ) :
    (onePair m fuel v a b).any go=pairStep m fuel go v a b := by
  by_cases h : a<b <;> simp [onePair,pairStep,h,gate_any,Bool.or_assoc]
lemma successors_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) :
    (successors m fuel v).any go=anyGate m fuel go v := by simp [successors,anyGate,pair_any]
def feasible (m fuel : ℕ) (v : List ℕ) := ∃ k≤fuel,Live m k v.toFinset ∧ v.Nodup
theorem move {m fuel : ℕ} {v : List ℕ} (h : feasible m (fuel+1) v) :
    terminal m v=true ∨ ∃ w∈successors m fuel v,feasible m fuel w := by
  classical
  obtain ⟨k,lim,live,nd⟩ := h
  generalize e : v.toFinset=S at live
  cases live with
  | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (e ▸ Finset.mem_singleton_self _)))
  | step hd ha hb ab fz tail =>
    let step := fun w => decide (feasible m fuel w)
    have hit := transition (go:=step) hd ab fz e nd (by omega : _≤fuel) tail (fun w rep nu => by
      apply decide_eq_true;exact ⟨_,by omega,rep ▸ tail,nu⟩)
    rw [←successors_any] at hit
    obtain ⟨w,hw,works⟩ := List.any_eq_true.mp hit
    exact Or.inr ⟨w,hw,of_decide_eq_true works⟩

def zeroPairs (m : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | x::xs, code, acc => zeroPairs m xs (code >>> 1)
      (if code % 2=1 then acc ^^^ (acc &&& (x ||| (x >>> m))) else acc)

def flipSwap (i j a : ℕ) := if a.testBit i = a.testBit j then a else a ^^^ ((1 <<< i) ||| (1 <<< j))
lemma swapBit (i j k a : ℕ) : (flipSwap i j a).testBit k =
    a.testBit (if k=i then j else if k=j then i else k) := by
  by_cases h : a.testBit i=a.testBit j
  · by_cases x : k=i <;> by_cases y : k=j <;> simp [flipSwap,h,x,y] <;> grind
  · have n : i≠j := fun e => h (e ▸ rfl)
    by_cases x : k=i
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    by_cases y : k=j
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    · simp [flipSwap,h,x,y,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow,Ne.symm x,Ne.symm y]
lemma flipSwap_twice (i j a : ℕ) : flipSwap i j (flipSwap i j a)=a := by
  apply Nat.eq_of_testBit_eq;intro k
  by_cases x : k=i <;> by_cases y : k=j <;> by_cases n : i=j <;> simp_all [swapBit]
lemma flipSwap_hom (i j d a b : ℕ) (hd : d<4) : flipSwap i j (combine d a b)=combine d (flipSwap i j a) (flipSwap i j b) := by
  apply Nat.eq_of_testBit_eq;intro k
  interval_cases d <;> simp [swapBit,combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]

def turn (m i j a : ℕ) := flipSwap i j (flipSwap (m+i) (m+j) a)
lemma turnGood {m i j a : ℕ} (hi : i<m) (hj : j<m) (g : Good m a) : Good m (turn m i j a) := by
  intro k hk
  have hm : m≠0 := by omega
  have ki : k≠m+i := by omega
  have kj : k≠m+j := by omega
  have ii : i≠m+i := by omega
  have ij : i≠m+j := by omega
  have ji : j≠m+i := by omega
  have jj : j≠m+j := by omega
  have ui : m+k≠i := by omega
  have uj : m+k≠j := by omega
  by_cases x : k=i
  · subst k;simp [turn,swapBit,ii,ij,ji,jj,ui,uj,hm];exact g _ hj
  by_cases y : k=j
  · subst k;simp [turn,swapBit,x,ii,ij,ji,jj,ui,uj,hm];exact g _ hi
  · simpa [turn,swapBit,x,y,ki,kj,ui,uj] using g k hk

theorem relabelLive {m k S} (f : ℕ→ℕ) (fz : f 0=0) (inj : Function.Injective f)
    (op : ∀ d a b,d<4 → f (combine d a b)=combine d (f a) (f b))
    (labels : ∀ a,Good m a → Good m (f a)) (live : Live m k S) : Live m k (S.image f) := by
  induction live with
  | done hg hn =>
    simp only [Finset.image_singleton]
    exact Live.done (labels _ hg) (fun h => hn (inj (h.trans fz.symm)))
  | @step k U a b d hd ha hb ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,op d a b hd] at ih
    apply Live.step hd (fun h => ha (inj (h.trans fz.symm))) (fun h => hb (inj (h.trans fz.symm))) (fun h => ne (inj h)) _ ih
    rw [←op d a b hd,←Finset.image_insert,←Finset.image_insert]
    exact fun h => fresh ((Finset.mem_image.mp h).elim (fun x hh => inj hh.2 ▸ hh.1))
def permute (m : ℕ) : List (ℕ×ℕ) → ℕ → ℕ
  | [],a => a
  | (i,j)::ss,a => permute m ss (turn m i j a)
theorem perm_live {m k S} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m) (h : Live m k S) :
    Live m k (S.image (permute m ss)) := by
  induction ss generalizing S with
  | nil => simpa [permute] using h
  | cons p ss ih =>
    obtain ⟨i,j⟩ := p
    obtain ⟨hi,hj⟩ := safe _ (List.mem_cons_self)
    have fi (a b : ℕ) : Function.Injective (flipSwap a b) := fun x y e =>
      (flipSwap_twice a b x).symm.trans ((congrArg (flipSwap a b) e).trans (flipSwap_twice a b y))
    have inj : Function.Injective (turn m i j) := (fi i j).comp (fi (m+i) (m+j))
    have names := relabelLive (turn m i j) (by simp [turn,flipSwap]) inj
      (fun d a b hd => by simp [turn,flipSwap_hom _ _ _ _ _ hd]) (fun _ => turnGood hi hj) h
    simpa [permute,Finset.image_image,Function.comp_def] using ih (fun p hp => safe _ (List.mem_cons_of_mem _ hp)) names
theorem perm_feasible {m fuel : ℕ} {v w : List ℕ} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m)
    (eq : (v.map (permute m ss)).toFinset=w.toFinset) (nw : w.Nodup) (h : feasible m fuel v) : feasible m fuel w := by
  obtain ⟨k,lim,ok,_⟩ := h
  refine ⟨k,lim,?_,nw⟩
  have tr := perm_live ss safe ok
  have imageEq : (v.map (permute m ss)).toFinset = v.toFinset.image (permute m ss) := by ext x;simp
  rw [←eq,imageEq]
  exact tr

def Excluded (m k : ℕ) (v : List ℕ) := ¬feasible m k v
def Block (m k : ℕ) (vs : List (List ℕ)) (i n : ℕ) := ∀ v∈(vs.drop i).take n,Excluded m k v
lemma blocks_cover {m k width q : ℕ} {vs : List (List ℕ)} (pw : 0<width) (size : vs.length≤q*width)
    (all : ∀ j : Fin q,Block m k vs (j.val*width) width) : ∀ v∈vs,Excluded m k v := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  have split := Nat.div_add_mod' i width
  have within := Nat.mod_lt i pw
  have bound : i/width<q := (Nat.div_lt_iff_lt_mul pw).2 (by omega)
  apply all ⟨i/width,bound⟩ _
  apply List.mem_iff_getElem.mpr
  have ix : i % width<((vs.drop (i/width*width)).take width).length := by simp only [List.length_take,List.length_drop];omega
  refine ⟨i % width,ix,?_⟩
  simp only [List.getElem_take,List.getElem_drop]
  simp [split]
lemma join_exclusions {m k : ℕ} {v : List ℕ} (term : terminal m v=false)
    (no : ∀ w∈successors m k v,Excluded m k w) : Excluded m (k+1) v := by
  intro h
  rcases move h with e|⟨w,hw,hf⟩
  · exact Bool.noConfusion (term.symm.trans e)
  · exact no w hw hf

structure FloorData where
  pairMask : ℕ
  lower : ℕ
  basis : List ℕ
deriving Inhabited
def Floor (m : ℕ) (s : FloorData) := ∀ k,Possible m k (0::s.basis) → s.lower≤k
theorem floorChecked {m : ℕ} {s : FloorData} (checked : start m (s.lower-1) (0::s.basis)=false) : Floor m s := by
  intro k poss
  by_contra small
  obtain ⟨j,S,le,live,sub⟩ := poss
  exact Bool.noConfusion (checked.symm.trans (start_complete live _ sub _ (by omega)))
lemma getMember {av : List ℕ} (zeroMem : 0∈av) (i : ℕ) : av.getD i 0∈av := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : av[i]? with
  | none => exact zeroMem
  | some t => exact List.mem_of_getElem? e

def instruction (av : List ℕ) (part : ℕ) :=
  let n := (part &&& 4095)-1
  combine (n % 4) (av.getD ((n >>> 2) &&& 15) 0) (av.getD ((n >>> 6) &&& 15) 0)
def replay : ℕ → ℕ → List ℕ → List ℕ
  | 0,_,av => av
  | k+1,code,av => if code=0 then av else replay k (code >>> 12) (av++[instruction av code])
def paidCount : ℕ → ℕ → ℕ
  | 0,_ => 0
  | k+1,code => if code=0 then 0 else paidCount k (code >>> 12)+1

theorem replay_back {m k : ℕ} (count code : ℕ) (av : List ℕ) (hasZero : 0∈av)
    (later : Possible m k (replay count code av)) : Possible m (k+paidCount count code) av := by
  induction count generalizing code av with
  | zero => simpa [replay,paidCount] using later
  | succ n ih =>
    by_cases stop : code=0
    · simpa [replay,paidCount,stop] using later
    rw [replay,ite_eq_right stop] at later
    have post := ih _ (av++[instruction av code]) (by simp [hasZero]) later
    let p := (code &&& 4095)-1
    have full := pullPaid (d:=p % 4) (Nat.mod_lt _ (by decide)) (getMember hasZero ((p >>> 2) &&& 15)) (getMember hasZero ((p >>> 6) &&& 15)) post
    obtain ⟨j,S,lim,live,sub⟩ := full
    refine ⟨j,S,?_,live,sub⟩
    rw [paidCount,ite_eq_right stop]
    have one (b : Bool) : b.toNat≤1 := by cases b <;> decide
    have bound := one (charge av (combine (p % 4) (av.getD ((p >>> 2) &&& 15) 0) (av.getD ((p >>> 6) &&& 15) 0)))
    omega

def contradictsFloor (m fuel : ℕ) (v : List ℕ) (s : FloorData) (code : ℕ) : Bool :=
  let r := min s.pairMask.log2 (m-1)
  let pv := v.map (slice m s.pairMask r)
  let av := replay 5 code (0::s.basis)
  fuel+paidCount 5 code<s.lower+pv.count 0 && pv.all (fun x => av.contains x)
lemma deadCount (f : ℕ→ℕ) {v : List ℕ} (nd : v.Nodup) :
    dead f v.toFinset=(v.map f).count 0 := by
  unfold dead
  have E : v.toFinset.filter (fun x => f x=0) = (v.filter (fun x => decide (f x=0))).toFinset := by ext x;simp
  rw [E,List.toFinset_card_of_nodup (nd.filter _)]
  simp only [List.count_eq_countP,List.countP_map]
  rw [List.countP_eq_length_filter]
  congr 2

theorem floor_consistent {m fuel : ℕ} (pos : 0<m) {v : List ℕ} (ok : feasible m fuel v) (s : FloorData)
    (known : Floor m s) (code : ℕ) : contradictsFloor m fuel v s code=false := by
  let r := min s.pairMask.log2 (m-1)
  let p := projection m s.pairMask r (show r<m by dsimp [r];omega)
  let pv := v.map p.toFun
  let av := replay 5 code (0::s.basis)
  obtain ⟨k,hk,live,nd⟩ := ok
  obtain ⟨l,T,lim,pr,inside⟩ := projectLive p live
  rw [deadCount _ nd] at lim
  apply Bool.eq_false_iff.mpr
  intro bad
  change (decide (fuel+paidCount 5 code < s.lower+pv.count 0) && pv.all (fun x => av.contains x))=true at bad
  simp only [Bool.and_eq_true] at bad
  obtain ⟨lo,mem⟩ := bad
  have low := of_decide_eq_true lo
  have final : Possible m l av := by
    refine ⟨l,T,le_rfl,pr,?_⟩
    intro x hx
    have active : x∈pv := by simpa [pv] using inside x hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp mem x active)
  have size := known _ (replay_back 5 code (0::s.basis) (by simp) final)
  change l+pv.count 0≤k at lim
  omega

def Memo := ℕ → FloorData × ℕ
def Certified (m : ℕ) (db : Memo) := ∀ i,Floor m (db i).1
inductive Advice where
  | plain
  | restrict (which : ℕ)
  | saved (index : ℕ)
  | fork (codes : ℕ) (nested : List Advice)
deriving Inhabited
def chooseAdvice (tag : ℕ) (gs : List Advice) : Advice :=
  if tag=1 then gs.headD .plain else if tag=0 then .plain else if tag<1024 then .restrict (tag-2) else .saved (tag-1024)
def memoRows (go : Advice → List ℕ → Bool) : List (List ℕ) → ℕ → List Advice → Bool
  | [],_,_ => false
  | v::vs,code,gs =>
    let tag := code &&& 4095
    go (chooseAdvice tag gs) v || memoRows go vs (code >>> 12) (if tag=1 then gs.tail else gs)
lemma memoRows_ok {go : Advice→List ℕ→Bool} {v : List ℕ} {vs : List (List ℕ)} (mem : v∈vs)
    (all : ∀ g,go g v=true) (code : ℕ) (gs : List Advice) : memoRows go vs code gs=true := by
  induction vs generalizing code gs with
  | nil => simp at mem
  | cons x xs ih =>
    rw [memoRows,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|next
    · exact Or.inl (all _)
    · exact Or.inr (ih next _ _)
def audited (m : ℕ) (db : Memo) : ℕ → Advice → List ℕ → Bool
  | 0,_,v => terminal m v
  | k+1,.plain,v => search m (k+1) v
  | k+1,.restrict which,v => cutSearch m (zeroPairs m v which (full m)) (k+1) v
  | k+1,.saved i,v => !(contradictsFloor m (k+1) v (db i).1 (db i).2)
  | k+1,.fork code gs,v => terminal m v || memoRows (audited m db k) (successors m k v) code gs
theorem audited_complete {m : ℕ} (hm : 0<m) (db : Memo) (safe : Certified m db)
    (fuel : ℕ) (v : List ℕ) (h : feasible m fuel v) (g : Advice) : audited m db fuel g v=true := by
  induction fuel generalizing v g with
  | zero =>
    obtain ⟨j,lim,live,nd⟩ := h
    exact complete m 0 live lim v rfl nd
  | succ k ih =>
    cases g with
    | plain =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact complete m (k+1) live lim v rfl nd
    | restrict which =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact cut_complete hm live v rfl nd _ _ lim
    | saved i => simp [audited,floor_consistent hm h _ (safe i) _]
    | fork code gs =>
      rw [audited,Bool.or_eq_true]
      rcases move h with endNow|⟨w,hw,next⟩
      · exact Or.inl endNow
      · exact Or.inr (memoRows_ok hw (fun g => ih w next g) _ _)
lemma offAudit {m k v g} {db : Memo} (safe : Certified m db) (pos : 0<m) (e : audited m db k g v=false) : Excluded m k v := by
  intro h;exact Bool.noConfusion (e.symm.trans (audited_complete pos db safe k v h g))
lemma offMemoRows {m k : ℕ} {vs : List (List ℕ)} {i n code : ℕ} {gs : List Advice} {db : Memo}
    (safe : Certified m db) (pos : 0<m)
    (e : memoRows (audited m db k) ((vs.drop i).take n) code gs=false) : Block m k vs i n := by
  intro w hw h
  exact Bool.noConfusion (e.symm.trans (memoRows_ok hw (fun g => audited_complete pos db safe k w h g) code gs))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
end Theta

namespace Graph11247
open PEqualNP.CircuitLowerBounds
def witness : List Gate := [⟨.or, [0,1]⟩, ⟨.or, [4,6]⟩, ⟨.and, [7,8]⟩, ⟨.or, [1,2]⟩, ⟨.or, [5,6]⟩, ⟨.and, [10,11]⟩, ⟨.or, [0,5]⟩, ⟨.and, [3,13]⟩, ⟨.and, [4,6]⟩, ⟨.or, [9,12]⟩, ⟨.or, [14,15]⟩, ⟨.or, [16,17]⟩]
theorem witness_basis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem witness_table : ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witness, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
theorem size_suffices (s : ℕ) (h : 12 ≤ s) : ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ s ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact ⟨witness,18,witness_basis,h,witness_table⟩
end Graph11247

namespace Six11247
open Theta
def inputs : List ℕ := [0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def noDB : Memo := fun _ => (⟨0,0,[]⟩,0)
theorem noDBsafe : Certified 190 noDB := by intro i k _; exact Nat.zero_le k
def turns1 : List (ℕ × ℕ) := [(5,7),(13,99),(14,100),(15,101),(16,103),(17,104),(18,102),(19,105),(20,106),(21,107),(22,108),(23,109),(24,110),(25,111),(26,112),(27,113),(28,114),(29,115),(30,116),(31,117),(32,118),(33,119),(34,120),(35,121),(36,122),(37,123),(38,124),(39,125),(40,126),(41,127),(42,128),(49,50),(59,63),(62,64),(76,153),(77,156),(78,154),(79,155),(80,157),(81,158),(82,160),(83,159),(84,161),(85,162),(86,163),(87,164),(88,165),(89,167),(90,168),(91,166),(92,169),(93,171),(94,170),(95,172),(96,173),(97,174),(98,175),(130,133),(131,134),(132,135),(137,138),(140,141),(144,146),(145,147),(148,149),(151,152),(176,179),(178,180),(182,183),(184,185),(186,188),(187,189)]
theorem safe1 : ∀ p ∈ turns1, p.1<190 ∧ p.2<190 := by
  have ht : turns1.all (fun p => decide (p.1<190 ∧ p.2<190)) = true := by decide +kernel
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp ht p hp)
def turns2 : List (ℕ × ℕ) := [(0,43),(1,44),(2,45),(3,47),(4,48),(5,49),(6,46),(7,50),(8,52),(9,51),(10,53),(11,54),(12,55),(13,20),(14,21),(15,22),(16,24),(17,26),(18,23),(19,25),(27,28),(31,81),(32,83),(33,82),(34,84),(35,76),(36,78),(37,79),(38,77),(39,80),(40,85),(41,86),(42,87),(57,60),(58,61),(59,62),(63,64),(65,69),(66,72),(67,70),(68,71),(74,75),(88,91),(90,92),(93,98),(94,96),(95,97),(99,106),(100,107),(101,108),(102,109),(103,110),(104,112),(105,111),(113,114),(117,158),(118,159),(119,160),(120,161),(121,153),(122,154),(123,155),(124,156),(125,157),(126,162),(127,163),(128,164),(131,132),(134,135),(136,139),(137,140),(138,141),(143,177),(144,176),(145,178),(146,179),(147,180),(148,184),(149,185),(150,181),(151,182),(152,183),(165,166),(168,169),(170,173),(171,175),(172,174),(186,187),(188,189)]
theorem safe2 : ∀ p ∈ turns2, p.1<190 ∧ p.2<190 := by
  have ht : turns2.all (fun p => decide (p.1<190 ∧ p.2<190)) = true := by decide +kernel
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp ht p hp)
def turns3 : List (ℕ × ℕ) := [(0,43),(1,44),(2,45),(3,47),(4,48),(5,50),(6,46),(7,49),(8,52),(9,51),(10,53),(11,54),(12,55),(13,106),(14,107),(15,108),(16,110),(17,112),(18,109),(19,111),(20,99),(21,100),(22,101),(23,102),(24,103),(25,105),(26,104),(27,114),(28,113),(29,115),(30,116),(31,158),(32,159),(33,160),(34,161),(35,153),(36,154),(37,155),(38,156),(39,157),(40,162),(41,163),(42,164),(57,60),(58,61),(59,64),(62,63),(65,69),(66,72),(67,70),(68,71),(74,75),(76,121),(77,124),(78,122),(79,123),(80,125),(81,117),(82,119),(83,118),(84,120),(85,126),(86,127),(87,128),(88,166),(89,167),(90,169),(91,165),(92,168),(93,175),(94,173),(95,174),(96,170),(97,172),(98,171),(130,133),(131,135),(132,134),(136,139),(137,141),(138,140),(143,177),(144,179),(145,180),(146,176),(147,178),(148,185),(149,184),(150,181),(151,183),(152,182),(186,189),(187,188)]
theorem safe3 : ∀ p ∈ turns3, p.1<190 ∧ p.2<190 := by
  have ht : turns3.all (fun p => decide (p.1<190 ∧ p.2<190)) = true := by decide +kernel
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp ht p hp)
def s0 : List ℕ := [0x7000010007007800000380380003e01c01e0007c0000000040000400040081020002002000020210020408404,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s1 : List ℕ := [0xf83f07fffc1fc07ffffffff83fffff803fffffffffffffc020240c4a404900ca2e387140629eb224b97328b8e4d756,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s2 : List ℕ := [0x3807000f8c01c0007800fe38007c0780000001e003f83fc02004080a00010000220050404098122089000088044142,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s3 : List ℕ := [0xc03800f0700e000f807f01c00780780001fe3e01fc000000002000404008008a042801000204a00410522810a01210,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s4 : List ℕ := [0x700000c00007078000038000387800001c1e00007ffc00000000000000000000000000000000000000000000000,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s5 : List ℕ := [0xf383fff0ffff1c07fff80fffff87ffffffe01fffe03ffffd4206d2c0bfac149ed6ab17365609ed6aea967b5aac6ddfe,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s6 : List ℕ := [0x3800070f8011c0000780fe00387c00003e00001e03f8000020040c0a004100402a107040609a1220a92100a844c546,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s7 : List ℕ := [0xf0038f80073e0000f800001c7c000787fc0003e000000001400692001fa8049ad40a103250004c48e0046b5028218b8,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s8 : List ℕ := [0x380000000c11c00000000038387c00000001c1fe03f800000000000000000000000000000000000000000000000000,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s9 : List ℕ := [0xfffc7070ffffffff07f80ffffffff87803e01ffffffffffcd65040c0a93531c402a1076f6f5ba1268ab25c6ef4fc566,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s10 : List ℕ := [0x7070f800000707f80fe00000387803e0000000007ffc020040c0a004100402a107040609a1220a92100a844c546,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s11 : List ℕ := [0xfc7c0000073ee3f80000001c7c780000000003e01fc00000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s12 : List ℕ := [0x3807070f8000000000000038387f87803e000000000000002004080800000000000040404088102081000000040040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s13 : List ℕ := [0xfffffffff8c11c0707f80ffffffffffffffffc1fe03ffffebf6965eae004190402b1274d8f9db1b70efa100ac4cc546,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s14 : List ℕ := [0xc11c0707f80fe00000000000001c1fe03ffffc000000402004100402a10300020120200282100a840c506,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s15 : List ℕ := [0xfc7f8f8f000000000000001c7c780787fc1fe00000000002bd69252a400009000010204989941095046800004080000,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s16 : List ℕ := [0x3807070f8c11c0707f80fe000000000000000000000000000000000000000000000000000000000000000000000000,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s17 : List ℕ := [0xffffffffffffffffffffffe38387f87803e01c1fe03fffff2b8df9f3b2c65e171bbd3f040609a13a0ad2100a844c5c6,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s18 : List ℕ := [0x38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s19 : List ℕ := [0xfc7f8f8f073ee3f8f807f000000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s20 : List ℕ := [0x3800007000007f800001c00003f8000001fe000007c0000020000040000088002001000004800400422000801010,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s21 : List ℕ := [0xfc03ffff07ffe007fffff01ffff83fffffffffffffc07ffd400692441fac849ef4cb923252206e48e3077bd32e29ebc,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s22 : List ℕ := [0xc00007f0001e000007ff00003f8000003ffe001ffc00000000000440004800420c1820002202200030310830608604,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s23 : List ℕ := [0xf0007f8000fe000007800003fc00007ffc00001e000003fd400492001ba804925408102250000448a000495020208a8,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s24 : List ℕ := [0xc0000000701e0000000001c03f8000000001fe1ffc0000000000000000000000000000000000000000000000000000,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s25 : List ℕ := [0xffff807f07fffffff87ff01fffffff8003fffffffffffc00d45200440d35a1cca0c3827b6b726a04c3277ee77eb9634,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s26 : List ℕ := [0x3807f00000007f87ff00000003f8003ffe00000007c00000200440404800ca0c3821002206a00430732830e09614,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s27 : List ℕ := [0xf3fc000000fe1ff800000003fc07c0000000001e003f8000d4500000093121c00000006b6952000480204c6470b0020,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s28 : List ℕ := [0xc03807f000000000000001c03f83f8003ffe0000000000000000000000000000000000000000000000000000000000,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s29 : List ℕ := [0xffffffffff01e007f87ff01fffffffffffffffe1ffc07c02bf6b65eec404890ca0d3a65d8fbcfb974f7f32834ec9654,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s30 : List ℕ := [0x701e007f87ff0000000000000001fe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s31 : List ℕ := [0xf3fc7f80f800000000000003fc07c07ffc00000000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s32 : List ℕ := [0xc03807f0701e007f87ff00000000000000000000000000000000000000000000000000000000000000000000000000,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s33 : List ℕ := [0xfffffffffffffffffffffffc03f83f8003ffffe1ffc07c03298fb97716c6ce1fb9dfba1002206a18434732830e09694,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s34 : List ℕ := [0x1c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s35 : List ℕ := [0xf3fc7f80f8fe1ff807800fe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s36 : List ℕ := [0xf000000007fe00000000001ffc00000000001ffe0000000040000000092000800000002240000000800048402020020,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s37 : List ℕ := [0xffffff8007ffffffff80001ffffffffffc001ffffffffffdd45692001fb925dad40a107b79524c4ce0246f7478b18b8,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s38 : List ℕ := [0x3ff8000000007ff80000000003ffffc00000000007ffd000692001688041ad40a101010004c48600423100801898,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s39 : List ℕ := [0xffc00000001fff80000000003ffc00000000001ffff800094500000001121400000004929520004002004245090000,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s40 : List ℕ := [0xf003ff80000000000000001ffc003ffffc0000000000000000000000000000000000000000000000000000000000000,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s41 : List ℕ := [0xfffffffffffe0007ff80001ffffffffffffffffe00007fffff6ff7aadfa80d9ad41a347fdd9cdddfec7c6b5068e18f8,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s42 : List ℕ := [0x7fe0007ff8000000000000000001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s43 : List ℕ := [0xffc007ff80000000000000003ffc00003ffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s44 : List ℕ := [0xf003ff8007fe0007ff80000000000000000000000000000100049000128004121008100000000008000000000000080,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s45 : List ℕ := [0xfffffffffffffffffffffffffc003ffffc001ffe00007fff698fbb331fea4e9bdd1e383250004c58e0446b5028218b8,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s46 : List ℕ := [0x1ffc003ffffc001ffe00007ffc400202000d280088c402003250004c40e0046b502821838,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s47 : List ℕ := [0xffc007ff801fff8007fffe00000000000000000000000022989293300424a010914280000000010004000000000000,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s48 : List ℕ := [0xfffc0000000000000000001fffffc000000000000000000094400000000001000000004909100004002000004080000,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s49 : List ℕ := [0xfffffffffffffff80000001fffffffffffffffffffff8002ff7965aac93129c00010246fedde91978c784c6470f0060,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s50 : List ℕ := [0x7fffff8000000000000000000001fffffff800040100000093120c0000000226042000080004c643030020,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s51 : List ℕ := [0x3fffff80000000000000000003fffffffe000000000022b2965aac000080000102404848c91930c5800000040040,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def s52 : List ℕ := [0xfffc000007fffff80000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s53 : List ℕ := [0xffffffffffffffffffffffffffffc00000001fffffff8003fdddb9331bf36fd3191c386b6952001c80604c6470b00a0,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s54 : List ℕ := [0x1fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s55 : List ℕ := [0x3fffff8000007ffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040]
def s56 : List ℕ := [0xfffffffff80000000000000000000000000000000000000229092122000008000010200000000010004000000000000,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020]
def s57 : List ℕ := [0xffffffffffffffffffffffffffffffffffffe00000000003bfedfdbbd2c24f13191c3c4d8d9c919f0c78000040c00c0,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020]
def s58 : List ℕ := [0x1fffffffffffffe0000000000096604488c00001000000044d8d9c91870c38000040c0040,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020]
def s59 : List ℕ := [0x7ffffffffffffe00000000000000000000000010084981112c24613190c180000000008000000000000080,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080,0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020]
def states : List (List ℕ) := [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,s47,s48,s49,s50,s51,s52,s53,s54,s55,s56,s57,s58,s59]
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem next_states : successors 190 8 inputs = states := by decide +kernel
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem essential : ∀ a ∈ inputs, ∃ i : Fin 190, ∀ b ∈ inputs, b.testBit i.val ≠ b.testBit (190+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 190 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_0 : Block 190 7 (successors 190 7 s0) 0 4 := offMemoRows (code:=0x2e00602c02e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_1 : Block 190 7 (successors 190 7 s0) 4 4 := offMemoRows (code:=0x402800602c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_2 : Block 190 7 (successors 190 7 s0) 8 4 := offMemoRows (code:=0x4028003027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_3 : Block 190 7 (successors 190 7 s0) 12 4 := offMemoRows (code:=0x4003005027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_4 : Block 190 7 (successors 190 7 s0) 16 4 := offMemoRows (code:=0x4036003003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_5 : Block 190 7 (successors 190 7 s0) 20 4 := offMemoRows (code:=0x4018005004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_6 : Block 190 7 (successors 190 7 s0) 24 4 := offMemoRows (code:=0x4018003017) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_7 : Block 190 7 (successors 190 7 s0) 28 4 := offMemoRows (code:=0x4003005017) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_8 : Block 190 7 (successors 190 7 s0) 32 4 := offMemoRows (code:=0x4056003003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_9 : Block 190 7 (successors 190 7 s0) 36 4 := offMemoRows (code:=0x2c02c005004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_10 : Block 190 7 (successors 190 7 s0) 40 4 := offMemoRows (code:=0x2c00402c054) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_11 : Block 190 7 (successors 190 7 s0) 44 4 := offMemoRows (code:=0x4000004006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_12 : Block 190 7 (successors 190 7 s0) 48 4 := offMemoRows (code:=0x4003004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_13 : Block 190 7 (successors 190 7 s0) 52 4 := offMemoRows (code:=0x4023004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_14 : Block 190 7 (successors 190 7 s0) 56 4 := offMemoRows (code:=0x400300400e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_15 : Block 190 7 (successors 190 7 s0) 60 4 := offMemoRows (code:=0x4043004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_16 : Block 190 7 (successors 190 7 s0) 64 4 := offMemoRows (code:=0x400300400e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_17 : Block 190 7 (successors 190 7 s0) 68 4 := offMemoRows (code:=0x4000004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_18 : Block 190 7 (successors 190 7 s0) 72 4 := offMemoRows (code:=0x4003004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_19 : Block 190 7 (successors 190 7 s0) 76 4 := offMemoRows (code:=0xb00b00b000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_20 : Block 190 7 (successors 190 7 s0) 80 4 := offMemoRows (code:=0xc01300b00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_21 : Block 190 7 (successors 190 7 s0) 84 4 := offMemoRows (code:=0xb00b00b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_22 : Block 190 7 (successors 190 7 s0) 88 4 := offMemoRows (code:=0xb00b00b00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_23 : Block 190 7 (successors 190 7 s0) 92 4 := offMemoRows (code:=0xc00c00c00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_24 : Block 190 7 (successors 190 7 s0) 96 4 := offMemoRows (code:=0xb00b00b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b0_25 : Block 190 7 (successors 190 7 s0) 100 4 := offMemoRows (code:=0xb) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e0 : Excluded 190 8 s0 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=26) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b0_0
  · exact b0_1
  · exact b0_2
  · exact b0_3
  · exact b0_4
  · exact b0_5
  · exact b0_6
  · exact b0_7
  · exact b0_8
  · exact b0_9
  · exact b0_10
  · exact b0_11
  · exact b0_12
  · exact b0_13
  · exact b0_14
  · exact b0_15
  · exact b0_16
  · exact b0_17
  · exact b0_18
  · exact b0_19
  · exact b0_20
  · exact b0_21
  · exact b0_22
  · exact b0_23
  · exact b0_24
  · exact b0_25
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_0 : Block 190 7 (successors 190 7 s1) 0 4 := offMemoRows (code:=0x100104e028) (gs:=[(.fork 0x3000000000000000000000000000000000000000000000000000000000009000000000000 []),(.fork 0xe00b00000000000000000f [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_1 : Block 190 7 (successors 190 7 s1) 4 4 := offMemoRows (code:=0x4e028001007) (gs:=[(.fork 0xc00000000002e000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_2 : Block 190 7 (successors 190 7 s1) 8 4 := offMemoRows (code:=0x1001006004) (gs:=[(.fork 0xa00000000000a000000000004000000000000000000000004000003000000000000 []),(.fork 0x3000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_3 : Block 190 7 (successors 190 7 s1) 12 4 := offMemoRows (code:=0x6004001001) (gs:=[(.fork 0x4004000000000003000000000000000000000000003000000000003000000000000000 []),(.fork 0x3 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_4 : Block 190 7 (successors 190 7 s1) 16 4 := offMemoRows (code:=0x100102e018) (gs:=[(.fork 0x9000000000000000003000000000000000000000000000000000000 []),(.fork 0xf00b00000e000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_5 : Block 190 7 (successors 190 7 s1) 20 4 := offMemoRows (code:=0x2e01800100b) (gs:=[(.fork 0xc00000001e000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_6 : Block 190 7 (successors 190 7 s1) 24 4 := offMemoRows (code:=0x1001006004) (gs:=[(.fork 0x400000000000000000000400300000000000000000a00000000000a000000000000 []),(.fork 0x3000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_7 : Block 190 7 (successors 190 7 s1) 28 4 := offMemoRows (code:=0x6004001001) (gs:=[(.fork 0x4004000000000000000000000000000000000000000000000003000000000000003000000000003000000000000000 []),(.fork 0x3 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_8 : Block 190 7 (successors 190 7 s1) 32 4 := offMemoRows (code:=0x2c05a02e02e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_9 : Block 190 7 (successors 190 7 s1) 36 4 := offMemoRows (code:=0x5402c05402c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_10 : Block 190 7 (successors 190 7 s1) 40 4 := offMemoRows (code:=0x4802c05602c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_11 : Block 190 7 (successors 190 7 s1) 44 4 := offMemoRows (code:=0x4502c047043) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_12 : Block 190 7 (successors 190 7 s1) 48 4 := offMemoRows (code:=0x1000001064) (gs:=[(.fork 0x34000000000003000000000000000000000000000000000004000000004000000000000000000000004000000000000000000 []),(.fork 0x28000023000000000000000000000003000000000023000034000003000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_13 : Block 190 7 (successors 190 7 s1) 52 4 := offMemoRows (code:=0x1028006064) (gs:=[(.fork 0x2600100000000800700401800401800d02600002600000800b01600001600401601600c01400001400000000000000b000016000000000000000026001014000000000 [(.fork 0x13000003 []),(.fork 0x13000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_14 : Block 190 7 (successors 190 7 s1) 56 4 := offMemoRows (code:=0x2502700b023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_15 : Block 190 7 (successors 190 7 s1) 60 4 := offMemoRows (code:=0x10000010a4) (gs:=[(.fork 0x4000000000000000054000003000000000000000000000000000000000000000004000000004000000000000000000000000 []),(.fork 0x28000000000043000000000000000000000003000023000000000054000003000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_16 : Block 190 7 (successors 190 7 s1) 64 4 := offMemoRows (code:=0x2e02e0060a4) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_17 : Block 190 7 (successors 190 7 s1) 68 4 := offMemoRows (code:=0x4300104805a) (gs:=[(.fork 0x4600000800b02600002600002600402602601402400002400000000000000b00002600000000000000004600100800702600102400000000001800401800400d000000 [(.fork 0x3013 []),(.fork 0x3013 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_18 : Block 190 7 (successors 190 7 s1) 72 4 := offMemoRows (code:=0x6404504700b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_19 : Block 190 7 (successors 190 7 s1) 76 4 := offMemoRows (code:=0x64001000001) (gs:=[(.fork 0x3000000000000000000000000000004000000004000000000000000000000004000000000000000000000034 []),(.fork 0x23000028000000000000000000000003000000000034000023000003000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_20 : Block 190 7 (successors 190 7 s1) 80 4 := offMemoRows (code:=0x2302801c006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_21 : Block 190 7 (successors 190 7 s1) 84 4 := offMemoRows (code:=0xa402501c027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_22 : Block 190 7 (successors 190 7 s1) 88 4 := offMemoRows (code:=0xa4001000001) (gs:=[(.fork 0x34000004000000000000000000000000000003000000000000000000000000000004000000004000000000000000000000000 []),(.fork 0x23000000000048000000000000000000000003000034000000000043000003000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_23 : Block 190 7 (successors 190 7 s1) 92 4 := offMemoRows (code:=0x54001054006) (gs:=[(.fork 0x1000000000000000025000000000000000007 [(.fork 0x3013 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_24 : Block 190 7 (successors 190 7 s1) 96 4 := offMemoRows (code:=0x17013018006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_25 : Block 190 7 (successors 190 7 s1) 100 4 := offMemoRows (code:=0x94001094015) (gs:=[(.fork 0x1000000000000000045000000000000000007 [(.fork 0x3013 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_26 : Block 190 7 (successors 190 7 s1) 104 4 := offMemoRows (code:=0x4001056006) (gs:=[(.fork 0x27001000000000000000000000005 [(.fork 0x13000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_27 : Block 190 7 (successors 190 7 s1) 108 4 := offMemoRows (code:=0x4001004056) (gs:=[(.fork 0x6006000000006006000000004006004006000000000008003 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_28 : Block 190 7 (successors 190 7 s1) 112 4 := offMemoRows (code:=0x54001054006) (gs:=[(.fork 0x25001000000000000000000000007 [(.fork 0x13000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b1_29 : Block 190 7 (successors 190 7 s1) 116 4 := offMemoRows (code:=0x6) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e1 : Excluded 190 8 s1 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=30) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b1_0
  · exact b1_1
  · exact b1_2
  · exact b1_3
  · exact b1_4
  · exact b1_5
  · exact b1_6
  · exact b1_7
  · exact b1_8
  · exact b1_9
  · exact b1_10
  · exact b1_11
  · exact b1_12
  · exact b1_13
  · exact b1_14
  · exact b1_15
  · exact b1_16
  · exact b1_17
  · exact b1_18
  · exact b1_19
  · exact b1_20
  · exact b1_21
  · exact b1_22
  · exact b1_23
  · exact b1_24
  · exact b1_25
  · exact b1_26
  · exact b1_27
  · exact b1_28
  · exact b1_29
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e2 : Excluded 190 8 s2 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e4 : Excluded 190 8 s4 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_0 : Block 190 7 (successors 190 7 s5) 0 4 := offMemoRows (code:=0x44000004004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_1 : Block 190 7 (successors 190 7 s5) 4 4 := offMemoRows (code:=0x4400400402e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_2 : Block 190 7 (successors 190 7 s5) 8 4 := offMemoRows (code:=0x3003004010) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_3 : Block 190 7 (successors 190 7 s5) 12 4 := offMemoRows (code:=0x500f004005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_4 : Block 190 7 (successors 190 7 s5) 16 4 := offMemoRows (code:=0x84000004004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_5 : Block 190 7 (successors 190 7 s5) 20 4 := offMemoRows (code:=0x8400400404e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_6 : Block 190 7 (successors 190 7 s5) 24 4 := offMemoRows (code:=0x26006024025) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_7 : Block 190 7 (successors 190 7 s5) 28 4 := offMemoRows (code:=0xa02600a026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_8 : Block 190 7 (successors 190 7 s5) 32 4 := offMemoRows (code:=0x4a00000a026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_9 : Block 190 7 (successors 190 7 s5) 36 4 := offMemoRows (code:=0x4a00a04a00a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_10 : Block 190 7 (successors 190 7 s5) 40 4 := offMemoRows (code:=0x700a04a00a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_11 : Block 190 7 (successors 190 7 s5) 44 4 := offMemoRows (code:=0xb00a00800b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_12 : Block 190 7 (successors 190 7 s5) 48 4 := offMemoRows (code:=0x8a00a08a00a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_13 : Block 190 7 (successors 190 7 s5) 52 4 := offMemoRows (code:=0xa006024025) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_14 : Block 190 7 (successors 190 7 s5) 56 4 := offMemoRows (code:=0xa02604a001) (gs:=[(.fork 0x1300000000002a00000000000400000000000400000000000000000000000000000000c000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_15 : Block 190 7 (successors 190 7 s5) 60 4 := offMemoRows (code:=0xa00b00a04a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_16 : Block 190 7 (successors 190 7 s5) 64 4 := offMemoRows (code:=0x8a00100a00b) (gs:=[(.fork 0xc00000000000000001300000000004a000000000004000004000000000000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_17 : Block 190 7 (successors 190 7 s5) 68 4 := offMemoRows (code:=0x2c08a00a046) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_18 : Block 190 7 (successors 190 7 s5) 72 4 := offMemoRows (code:=0x3046001006) (gs:=[(.fork 0x300000000000000000000000000000000000000000000000d000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_19 : Block 190 7 (successors 190 7 s5) 76 4 := offMemoRows (code:=0x602e046) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_20 : Block 190 7 (successors 190 7 s5) 80 4 := offMemoRows (code:=0xb00a04a043) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_21 : Block 190 7 (successors 190 7 s5) 84 4 := offMemoRows (code:=0xe006064000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_22 : Block 190 7 (successors 190 7 s5) 88 4 := offMemoRows (code:=0xb00e00e023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_23 : Block 190 7 (successors 190 7 s5) 92 4 := offMemoRows (code:=0xe0060a4000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_24 : Block 190 7 (successors 190 7 s5) 96 4 := offMemoRows (code:=0x400e00b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_25 : Block 190 7 (successors 190 7 s5) 100 4 := offMemoRows (code:=0xc006004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b5_26 : Block 190 7 (successors 190 7 s5) 104 4 := offMemoRows (code:=0xb00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e5 : Excluded 190 8 s5 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=27) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b5_0
  · exact b5_1
  · exact b5_2
  · exact b5_3
  · exact b5_4
  · exact b5_5
  · exact b5_6
  · exact b5_7
  · exact b5_8
  · exact b5_9
  · exact b5_10
  · exact b5_11
  · exact b5_12
  · exact b5_13
  · exact b5_14
  · exact b5_15
  · exact b5_16
  · exact b5_17
  · exact b5_18
  · exact b5_19
  · exact b5_20
  · exact b5_21
  · exact b5_22
  · exact b5_23
  · exact b5_24
  · exact b5_25
  · exact b5_26
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e6 : Excluded 190 8 s6 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_0 : Block 190 7 (successors 190 7 s7) 0 4 := offMemoRows (code:=0x4006028028) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_1 : Block 190 7 (successors 190 7 s7) 4 4 := offMemoRows (code:=0x2e013001012) (gs:=[(.fork 0x3000000000000000003000000000000000000000000000003000000000000003000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_2 : Block 190 7 (successors 190 7 s7) 8 4 := offMemoRows (code:=0x10013004012) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_3 : Block 190 7 (successors 190 7 s7) 12 4 := offMemoRows (code:=0x900b007012) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_4 : Block 190 7 (successors 190 7 s7) 16 4 := offMemoRows (code:=0x400d00f012) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_5 : Block 190 7 (successors 190 7 s7) 20 4 := offMemoRows (code:=0x4e013001012) (gs:=[(.fork 0x3000000000000000003000000000000000003000000000000000000000000000003000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_6 : Block 190 7 (successors 190 7 s7) 24 4 := offMemoRows (code:=0x23013004012) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_7 : Block 190 7 (successors 190 7 s7) 28 4 := offMemoRows (code:=0x6028003023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_8 : Block 190 7 (successors 190 7 s7) 32 4 := offMemoRows (code:=0x25028003023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_9 : Block 190 7 (successors 190 7 s7) 36 4 := offMemoRows (code:=0x4c02c000007) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_10 : Block 190 7 (successors 190 7 s7) 40 4 := offMemoRows (code:=0x1304c00c02b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_11 : Block 190 7 (successors 190 7 s7) 44 4 := offMemoRows (code:=0x1600c04c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_12 : Block 190 7 (successors 190 7 s7) 48 4 := offMemoRows (code:=0x1301301300b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_13 : Block 190 7 (successors 190 7 s7) 52 4 := offMemoRows (code:=0x401600c08c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_14 : Block 190 7 (successors 190 7 s7) 56 4 := offMemoRows (code:=0x402e003001) (gs:=[(.fork 0x300000000000400000000000000000000001c000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_15 : Block 190 7 (successors 190 7 s7) 60 4 := offMemoRows (code:=0x4013004005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_16 : Block 190 7 (successors 190 7 s7) 64 4 := offMemoRows (code:=0x3001004015) (gs:=[(.fork 0x1c000000000000000000000000000000000003000004000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_17 : Block 190 7 (successors 190 7 s7) 68 4 := offMemoRows (code:=0x2c00500404e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_18 : Block 190 7 (successors 190 7 s7) 72 4 := offMemoRows (code:=0x2b05302b012) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_19 : Block 190 7 (successors 190 7 s7) 76 4 := offMemoRows (code:=0x601202c053) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_20 : Block 190 7 (successors 190 7 s7) 80 4 := offMemoRows (code:=0x23006047043) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_21 : Block 190 7 (successors 190 7 s7) 84 4 := offMemoRows (code:=0x28026064064) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_22 : Block 190 7 (successors 190 7 s7) 88 4 := offMemoRows (code:=0x23025027023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_23 : Block 190 7 (successors 190 7 s7) 92 4 := offMemoRows (code:=0x230260a40a4) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_24 : Block 190 7 (successors 190 7 s7) 96 4 := offMemoRows (code:=0x2401e02301e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_25 : Block 190 7 (successors 190 7 s7) 100 4 := offMemoRows (code:=0x23026024001) (gs:=[(.fork 0x3000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b7_26 : Block 190 7 (successors 190 7 s7) 104 4 := offMemoRows (code:=0x2301c01c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e7 : Excluded 190 8 s7 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=27) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b7_0
  · exact b7_1
  · exact b7_2
  · exact b7_3
  · exact b7_4
  · exact b7_5
  · exact b7_6
  · exact b7_7
  · exact b7_8
  · exact b7_9
  · exact b7_10
  · exact b7_11
  · exact b7_12
  · exact b7_13
  · exact b7_14
  · exact b7_15
  · exact b7_16
  · exact b7_17
  · exact b7_18
  · exact b7_19
  · exact b7_20
  · exact b7_21
  · exact b7_22
  · exact b7_23
  · exact b7_24
  · exact b7_25
  · exact b7_26
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e8 : Excluded 190 8 s8 := offAudit (g:=(.restrict 4)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_0 : Block 190 7 (successors 190 7 s9) 0 4 := offMemoRows (code:=0x1004028) (gs:=[(.fork 0x9000000000000000000000000000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_1 : Block 190 7 (successors 190 7 s9) 4 4 := offMemoRows (code:=0x4e043004003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_2 : Block 190 7 (successors 190 7 s9) 8 4 := offMemoRows (code:=0x1004004) (gs:=[(.fork 0x3000000000000000000000000000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_3 : Block 190 7 (successors 190 7 s9) 12 4 := offMemoRows (code:=0x6004004001) (gs:=[(.fork 0x300000c000000000000000000000000000000000000003000000000004000000000003000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_4 : Block 190 7 (successors 190 7 s9) 16 4 := offMemoRows (code:=0x34006006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_5 : Block 190 7 (successors 190 7 s9) 20 4 := offMemoRows (code:=0xa034006004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_6 : Block 190 7 (successors 190 7 s9) 24 4 := offMemoRows (code:=0x100a006004) (gs:=[(.fork 0x2c000004000000000000000000000000000003000000000000000000000000000000000004000000004000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_7 : Block 190 7 (successors 190 7 s9) 28 4 := offMemoRows (code:=0x600a003000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_8 : Block 190 7 (successors 190 7 s9) 32 4 := offMemoRows (code:=0x4500a04300a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_9 : Block 190 7 (successors 190 7 s9) 36 4 := offMemoRows (code:=0x4500a043000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_10 : Block 190 7 (successors 190 7 s9) 40 4 := offMemoRows (code:=0x100000100a) (gs:=[(.fork 0x12000006000000003003004004000000004000004004000004000004004000000004000000 []),(.fork 0x4000004000000000004003003000000004000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_11 : Block 190 7 (successors 190 7 s9) 44 4 := offMemoRows (code:=0x3603600600a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_12 : Block 190 7 (successors 190 7 s9) 48 4 := offMemoRows (code:=0x4000000006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_13 : Block 190 7 (successors 190 7 s9) 52 4 := offMemoRows (code:=0x1001004056) (gs:=[(.fork 0x700a00300400000a000006003004004000000000000000004004004004000003004000004000004006000 []),(.fork 0x600000000000000e004000000000000006000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_14 : Block 190 7 (successors 190 7 s9) 56 4 := offMemoRows (code:=0x34006004001) (gs:=[(.fork 0x4000004000000000004003003000005004006 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_15 : Block 190 7 (successors 190 7 s9) 60 4 := offMemoRows (code:=0x34000001006) (gs:=[(.fork 0x4000000000012000000000012000000000000000000000004000003000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_16 : Block 190 7 (successors 190 7 s9) 64 4 := offMemoRows (code:=0x6006001003) (gs:=[(.fork 0x7000000000000000000000000000000000000000000000004003000000000003000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_17 : Block 190 7 (successors 190 7 s9) 68 4 := offMemoRows (code:=0xb006004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_18 : Block 190 7 (successors 190 7 s9) 72 4 := offMemoRows (code:=0x56056004001) (gs:=[(.fork 0x24000017000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_19 : Block 190 7 (successors 190 7 s9) 76 4 := offMemoRows (code:=0x6056004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_20 : Block 190 7 (successors 190 7 s9) 80 4 := offMemoRows (code:=0x28006004001) (gs:=[(.fork 0x6000000006000000000008000012 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_21 : Block 190 7 (successors 190 7 s9) 84 4 := offMemoRows (code:=0x28000000006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_22 : Block 190 7 (successors 190 7 s9) 88 4 := offMemoRows (code:=0x600600704c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_23 : Block 190 7 (successors 190 7 s9) 92 4 := offMemoRows (code:=0x3054000001) (gs:=[(.fork 0x23000000000004000000000000000000018000000000003000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_24 : Block 190 7 (successors 190 7 s9) 96 4 := offMemoRows (code:=0x17013018006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_25 : Block 190 7 (successors 190 7 s9) 100 4 := offMemoRows (code:=0xb000094015) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_26 : Block 190 7 (successors 190 7 s9) 104 4 := offMemoRows (code:=0x9400100b00b) (gs:=[(.fork 0x3000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b9_27 : Block 190 7 (successors 190 7 s9) 108 4 := offMemoRows (code:=0x6) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e9 : Excluded 190 8 s9 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=28) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b9_0
  · exact b9_1
  · exact b9_2
  · exact b9_3
  · exact b9_4
  · exact b9_5
  · exact b9_6
  · exact b9_7
  · exact b9_8
  · exact b9_9
  · exact b9_10
  · exact b9_11
  · exact b9_12
  · exact b9_13
  · exact b9_14
  · exact b9_15
  · exact b9_16
  · exact b9_17
  · exact b9_18
  · exact b9_19
  · exact b9_20
  · exact b9_21
  · exact b9_22
  · exact b9_23
  · exact b9_24
  · exact b9_25
  · exact b9_26
  · exact b9_27
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e10 : Excluded 190 8 s10 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e11 : Excluded 190 8 s11 := offAudit (g:=(.restrict 4)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_0 : Block 190 7 (successors 190 7 s12) 0 4 := offMemoRows (code:=0x17006017017) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_1 : Block 190 7 (successors 190 7 s12) 4 4 := offMemoRows (code:=0x401c006017) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_2 : Block 190 7 (successors 190 7 s12) 8 4 := offMemoRows (code:=0x401c00301b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_3 : Block 190 7 (successors 190 7 s12) 12 4 := offMemoRows (code:=0x400300501b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_4 : Block 190 7 (successors 190 7 s12) 16 4 := offMemoRows (code:=0x401000b00f) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_5 : Block 190 7 (successors 190 7 s12) 20 4 := offMemoRows (code:=0x400300b00f) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_6 : Block 190 7 (successors 190 7 s12) 24 4 := offMemoRows (code:=0x402e003003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_7 : Block 190 7 (successors 190 7 s12) 28 4 := offMemoRows (code:=0x4003005004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_8 : Block 190 7 (successors 190 7 s12) 32 4 := offMemoRows (code:=0x402e003003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_9 : Block 190 7 (successors 190 7 s12) 36 4 := offMemoRows (code:=0x13013005004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_10 : Block 190 7 (successors 190 7 s12) 40 4 := offMemoRows (code:=0x15004015023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_11 : Block 190 7 (successors 190 7 s12) 44 4 := offMemoRows (code:=0x4034004006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_12 : Block 190 7 (successors 190 7 s12) 48 4 := offMemoRows (code:=0x400300400e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_13 : Block 190 7 (successors 190 7 s12) 52 4 := offMemoRows (code:=0x4000004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_14 : Block 190 7 (successors 190 7 s12) 56 4 := offMemoRows (code:=0x4000004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_15 : Block 190 7 (successors 190 7 s12) 60 4 := offMemoRows (code:=0x4000004000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_16 : Block 190 7 (successors 190 7 s12) 64 4 := offMemoRows (code:=0x6005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_17 : Block 190 7 (successors 190 7 s12) 68 4 := offMemoRows (code:=0xb023013006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_18 : Block 190 7 (successors 190 7 s12) 72 4 := offMemoRows (code:=0xc00b00b00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_19 : Block 190 7 (successors 190 7 s12) 76 4 := offMemoRows (code:=0xc00b00b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_20 : Block 190 7 (successors 190 7 s12) 80 4 := offMemoRows (code:=0x1300600e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_21 : Block 190 7 (successors 190 7 s12) 84 4 := offMemoRows (code:=0x1303400b006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_22 : Block 190 7 (successors 190 7 s12) 88 4 := offMemoRows (code:=0x1303400b00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_23 : Block 190 7 (successors 190 7 s12) 92 4 := offMemoRows (code:=0x700000600b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_24 : Block 190 7 (successors 190 7 s12) 96 4 := offMemoRows (code:=0xc00b00c006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b12_25 : Block 190 7 (successors 190 7 s12) 100 4 := offMemoRows (code:=0xe) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e12 : Excluded 190 8 s12 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=26) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b12_0
  · exact b12_1
  · exact b12_2
  · exact b12_3
  · exact b12_4
  · exact b12_5
  · exact b12_6
  · exact b12_7
  · exact b12_8
  · exact b12_9
  · exact b12_10
  · exact b12_11
  · exact b12_12
  · exact b12_13
  · exact b12_14
  · exact b12_15
  · exact b12_16
  · exact b12_17
  · exact b12_18
  · exact b12_19
  · exact b12_20
  · exact b12_21
  · exact b12_22
  · exact b12_23
  · exact b12_24
  · exact b12_25
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_0 : Block 190 7 (successors 190 7 s13) 0 4 := offMemoRows (code:=0x44001044004) (gs:=[(.fork 0xf000000000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_1 : Block 190 7 (successors 190 7 s13) 4 4 := offMemoRows (code:=0x4400404402e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_2 : Block 190 7 (successors 190 7 s13) 8 4 := offMemoRows (code:=0x16026014015) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_3 : Block 190 7 (successors 190 7 s13) 12 4 := offMemoRows (code:=0x2a01602a016) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_4 : Block 190 7 (successors 190 7 s13) 16 4 := offMemoRows (code:=0x102a02a016) (gs:=[(.fork 0x3200100000001400b00401c00401c00f03200101400000000002a00002a00000c01301a00401a01a00e01400001400001600000000000000700001a000000000000000 [(.fork 0x13000003 []),(.fork 0x13000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_5 : Block 190 7 (successors 190 7 s13) 20 4 := offMemoRows (code:=0x2a02a01602a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_6 : Block 190 7 (successors 190 7 s13) 24 4 := offMemoRows (code:=0x800b00700e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_7 : Block 190 7 (successors 190 7 s13) 28 4 := offMemoRows (code:=0x4a04a00b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_8 : Block 190 7 (successors 190 7 s13) 32 4 := offMemoRows (code:=0x4a04a04a04a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_9 : Block 190 7 (successors 190 7 s13) 36 4 := offMemoRows (code:=0x1401504a04a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_10 : Block 190 7 (successors 190 7 s13) 40 4 := offMemoRows (code:=0x4a00104a026) (gs:=[(.fork 0x400300000c000000000000000000000004000013000001000000000000000000000000000000000000000000000000000 [(.fork 0x7000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_11 : Block 190 7 (successors 190 7 s13) 44 4 := offMemoRows (code:=0x1c04a04a026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_12 : Block 190 7 (successors 190 7 s13) 48 4 := offMemoRows (code:=0x1c026001026) (gs:=[(.fork 0xd000000000000000000000000000000000003000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_13 : Block 190 7 (successors 190 7 s13) 52 4 := offMemoRows (code:=0x1602601e026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_14 : Block 190 7 (successors 190 7 s13) 56 4 := offMemoRows (code:=0x2a00402302a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_15 : Block 190 7 (successors 190 7 s13) 60 4 := offMemoRows (code:=0xe02300e02a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_16 : Block 190 7 (successors 190 7 s13) 64 4 := offMemoRows (code:=0x6400106400e) (gs:=[(.fork 0x2700000000002a000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_17 : Block 190 7 (successors 190 7 s13) 68 4 := offMemoRows (code:=0x6400106404a) (gs:=[(.fork 0x2700000002a000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_18 : Block 190 7 (successors 190 7 s13) 72 4 := offMemoRows (code:=0x401000104a) (gs:=[(.fork 0x400000f00300000600000602c02c00300602c02c00301601600800001600800601a00e01300b00300300000f00000600000000000000300000000000301400c00f01401000000000700000000600000900300700600600e00400300e00300600e00400300e00300e009004000007004 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_19 : Block 190 7 (successors 190 7 s13) 76 4 := offMemoRows (code:=0xf003003008) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_20 : Block 190 7 (successors 190 7 s13) 80 4 := offMemoRows (code:=0x4005001007) (gs:=[(.fork 0x3004000000000000000000000003000000000003000000000003000000000000000000000000000000000003000000000003000000000000000000000000000003000000000000000000000000000000003003000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_21 : Block 190 7 (successors 190 7 s13) 84 4 := offMemoRows (code:=0xb00700c005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_22 : Block 190 7 (successors 190 7 s13) 88 4 := offMemoRows (code:=0xc00c00800b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_23 : Block 190 7 (successors 190 7 s13) 92 4 := offMemoRows (code:=0xc00c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_24 : Block 190 7 (successors 190 7 s13) 96 4 := offMemoRows (code:=0x400c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_25 : Block 190 7 (successors 190 7 s13) 100 4 := offMemoRows (code:=0x4046001046) (gs:=[(.fork 0xf000000000000000000000000000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_26 : Block 190 7 (successors 190 7 s13) 104 4 := offMemoRows (code:=0x4a04602e046) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_27 : Block 190 7 (successors 190 7 s13) 108 4 := offMemoRows (code:=0x2604a04a001) (gs:=[(.fork 0x400300000c000000000000000000000004000013000001000000000000000000000000000000000000000000000000000000000000000 [(.fork 0x7000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_28 : Block 190 7 (successors 190 7 s13) 112 4 := offMemoRows (code:=0x8a00100404a) (gs:=[(.fork 0x400000000000004a000000000000003 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b13_29 : Block 190 7 (successors 190 7 s13) 116 4 := offMemoRows (code:=0x8a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e13 : Excluded 190 8 s13 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=30) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b13_0
  · exact b13_1
  · exact b13_2
  · exact b13_3
  · exact b13_4
  · exact b13_5
  · exact b13_6
  · exact b13_7
  · exact b13_8
  · exact b13_9
  · exact b13_10
  · exact b13_11
  · exact b13_12
  · exact b13_13
  · exact b13_14
  · exact b13_15
  · exact b13_16
  · exact b13_17
  · exact b13_18
  · exact b13_19
  · exact b13_20
  · exact b13_21
  · exact b13_22
  · exact b13_23
  · exact b13_24
  · exact b13_25
  · exact b13_26
  · exact b13_27
  · exact b13_28
  · exact b13_29
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e14 : Excluded 190 8 s14 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_0 : Block 190 7 (successors 190 7 s15) 0 4 := offMemoRows (code:=0x4006018018) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_1 : Block 190 7 (successors 190 7 s15) 4 4 := offMemoRows (code:=0x43003001004) (gs:=[(.fork 0x3000000000000000000000003000004000000000000004000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_2 : Block 190 7 (successors 190 7 s15) 8 4 := offMemoRows (code:=0x4005004004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_3 : Block 190 7 (successors 190 7 s15) 12 4 := offMemoRows (code:=0x43003001004) (gs:=[(.fork 0x4000004000000000000000000000000000000000000000003000000000000000000000000000000000003000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_4 : Block 190 7 (successors 190 7 s15) 16 4 := offMemoRows (code:=0x13005004004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_5 : Block 190 7 (successors 190 7 s15) 20 4 := offMemoRows (code:=0x6018023013) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_6 : Block 190 7 (successors 190 7 s15) 24 4 := offMemoRows (code:=0x15017023013) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_7 : Block 190 7 (successors 190 7 s15) 28 4 := offMemoRows (code:=0x2c02c013027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_8 : Block 190 7 (successors 190 7 s15) 32 4 := offMemoRows (code:=0xf00b00e016) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_9 : Block 190 7 (successors 190 7 s15) 36 4 := offMemoRows (code:=0x4c04c01300e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_10 : Block 190 7 (successors 190 7 s15) 40 4 := offMemoRows (code:=0x4c04c01300e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_11 : Block 190 7 (successors 190 7 s15) 44 4 := offMemoRows (code:=0x302600400e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_12 : Block 190 7 (successors 190 7 s15) 48 4 := offMemoRows (code:=0x300500402e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_13 : Block 190 7 (successors 190 7 s15) 52 4 := offMemoRows (code:=0x1b01301b006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_14 : Block 190 7 (successors 190 7 s15) 56 4 := offMemoRows (code:=0x1800601c013) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_15 : Block 190 7 (successors 190 7 s15) 60 4 := offMemoRows (code:=0x7018003006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_16 : Block 190 7 (successors 190 7 s15) 64 4 := offMemoRows (code:=0x2302300b006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_17 : Block 190 7 (successors 190 7 s15) 68 4 := offMemoRows (code:=0x2406400b023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_18 : Block 190 7 (successors 190 7 s15) 72 4 := offMemoRows (code:=0x2406400b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_19 : Block 190 7 (successors 190 7 s15) 76 4 := offMemoRows (code:=0x700601000e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_20 : Block 190 7 (successors 190 7 s15) 80 4 := offMemoRows (code:=0x900700f003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_21 : Block 190 7 (successors 190 7 s15) 84 4 := offMemoRows (code:=0x1300b006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_22 : Block 190 7 (successors 190 7 s15) 88 4 := offMemoRows (code:=0xb00600d000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_23 : Block 190 7 (successors 190 7 s15) 92 4 := offMemoRows (code:=0xb02300c00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_24 : Block 190 7 (successors 190 7 s15) 96 4 := offMemoRows (code:=0x602300c00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_25 : Block 190 7 (successors 190 7 s15) 100 4 := offMemoRows (code:=0x2e007003026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_26 : Block 190 7 (successors 190 7 s15) 104 4 := offMemoRows (code:=0xc00100c006) (gs:=[(.fork 0x8003000000007 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b15_27 : Block 190 7 (successors 190 7 s15) 108 4 := offMemoRows (code:=0xe) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e15 : Excluded 190 8 s15 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=28) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b15_0
  · exact b15_1
  · exact b15_2
  · exact b15_3
  · exact b15_4
  · exact b15_5
  · exact b15_6
  · exact b15_7
  · exact b15_8
  · exact b15_9
  · exact b15_10
  · exact b15_11
  · exact b15_12
  · exact b15_13
  · exact b15_14
  · exact b15_15
  · exact b15_16
  · exact b15_17
  · exact b15_18
  · exact b15_19
  · exact b15_20
  · exact b15_21
  · exact b15_22
  · exact b15_23
  · exact b15_24
  · exact b15_25
  · exact b15_26
  · exact b15_27
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e36 : Excluded 190 8 s36 := offAudit (g:=(.restrict 4)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_0 : Block 190 7 (successors 190 7 s37) 0 4 := offMemoRows (code:=0x4018) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_1 : Block 190 7 (successors 190 7 s37) 4 4 := offMemoRows (code:=0x2e018004007) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_2 : Block 190 7 (successors 190 7 s37) 8 4 := offMemoRows (code:=0x1004004) (gs:=[(.fork 0x4027000000000003000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_3 : Block 190 7 (successors 190 7 s37) 12 4 := offMemoRows (code:=0x6004004001) (gs:=[(.fork 0x8000000000000000000000000004000000000000000000003004000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_4 : Block 190 7 (successors 190 7 s37) 16 4 := offMemoRows (code:=0x2c006006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_5 : Block 190 7 (successors 190 7 s37) 20 4 := offMemoRows (code:=0xa02c006004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_6 : Block 190 7 (successors 190 7 s37) 24 4 := offMemoRows (code:=0xa004006004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_7 : Block 190 7 (successors 190 7 s37) 28 4 := offMemoRows (code:=0x2500400a023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_8 : Block 190 7 (successors 190 7 s37) 32 4 := offMemoRows (code:=0x1000001000) (gs:=[(.fork 0x4000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000 []),(.fork 0x28000000000000000000000004000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_9 : Block 190 7 (successors 190 7 s37) 36 4 := offMemoRows (code:=0x2e02e00600a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_10 : Block 190 7 (successors 190 7 s37) 40 4 := offMemoRows (code:=0x1001004006) (gs:=[(.fork 0x700b00000001501300d00b00b01300000002b000000000004004004004003004000004000000004000004000000000000022033000000000 []),(.fork 0x4000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_11 : Block 190 7 (successors 190 7 s37) 44 4 := offMemoRows (code:=0x4036004003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_12 : Block 190 7 (successors 190 7 s37) 48 4 := offMemoRows (code:=0x28006004001) (gs:=[(.fork 0x7004000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_13 : Block 190 7 (successors 190 7 s37) 52 4 := offMemoRows (code:=0x28000000006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_14 : Block 190 7 (successors 190 7 s37) 56 4 := offMemoRows (code:=0xa00600104c) (gs:=[(.fork 0x3000000000003000000000000000000000000003000000000000000000000003000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_15 : Block 190 7 (successors 190 7 s37) 60 4 := offMemoRows (code:=0x1047043001) (gs:=[(.fork 0x8000000000000000007000026000000000004000000000000000004000000000000000000000000000 []),(.fork 0x10000000000000000000000000000003000000000000000004000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_16 : Block 190 7 (successors 190 7 s37) 64 4 := offMemoRows (code:=0x100600a) (gs:=[(.fork 0x3000000000000000000000000000000000000000023000000000004000000000000000000000000018 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_17 : Block 190 7 (successors 190 7 s37) 68 4 := offMemoRows (code:=0xb006001054) (gs:=[(.fork 0x4000000003000000000000000000000000003000000000018000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_18 : Block 190 7 (successors 190 7 s37) 72 4 := offMemoRows (code:=0x18056054001) (gs:=[(.fork 0x100000000000000002b000000000000000005 [(.fork 0x3007 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_19 : Block 190 7 (successors 190 7 s37) 76 4 := offMemoRows (code:=0x9400b00b013) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_20 : Block 190 7 (successors 190 7 s37) 80 4 := offMemoRows (code:=0x28006094000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_21 : Block 190 7 (successors 190 7 s37) 84 4 := offMemoRows (code:=0x28000001006) (gs:=[(.fork 0x9 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_22 : Block 190 7 (successors 190 7 s37) 88 4 := offMemoRows (code:=0x600104c) (gs:=[(.fork 0x3000000000000000000000000000000000000000000004000000000000000000000003000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_23 : Block 190 7 (successors 190 7 s37) 92 4 := offMemoRows (code:=0x23047043001) (gs:=[(.fork 0x4000001000000000008000000000000000000000007000000000000000000000000000000004000003000000000000000000000000000 [(.fork 0x7000003 [])])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_24 : Block 190 7 (successors 190 7 s37) 96 4 := offMemoRows (code:=0x5400000600a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_25 : Block 190 7 (successors 190 7 s37) 100 4 := offMemoRows (code:=0x17013018006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_26 : Block 190 7 (successors 190 7 s37) 104 4 := offMemoRows (code:=0x94001094015) (gs:=[(.fork 0x3000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_27 : Block 190 7 (successors 190 7 s37) 108 4 := offMemoRows (code:=0x5400100b006) (gs:=[(.fork 0xa000004000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b37_28 : Block 190 7 (successors 190 7 s37) 112 4 := offMemoRows (code:=0x6) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e37 : Excluded 190 8 s37 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=29) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b37_0
  · exact b37_1
  · exact b37_2
  · exact b37_3
  · exact b37_4
  · exact b37_5
  · exact b37_6
  · exact b37_7
  · exact b37_8
  · exact b37_9
  · exact b37_10
  · exact b37_11
  · exact b37_12
  · exact b37_13
  · exact b37_14
  · exact b37_15
  · exact b37_16
  · exact b37_17
  · exact b37_18
  · exact b37_19
  · exact b37_20
  · exact b37_21
  · exact b37_22
  · exact b37_23
  · exact b37_24
  · exact b37_25
  · exact b37_26
  · exact b37_27
  · exact b37_28
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_0 : Block 190 7 (successors 190 7 s38) 0 4 := offMemoRows (code:=0x2e006006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_1 : Block 190 7 (successors 190 7 s38) 4 4 := offMemoRows (code:=0x4028003001) (gs:=[(.fork 0x300000000000400000000000000000000001c000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_2 : Block 190 7 (successors 190 7 s38) 8 4 := offMemoRows (code:=0x4028003027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_3 : Block 190 7 (successors 190 7 s38) 12 4 := offMemoRows (code:=0x4028005027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_4 : Block 190 7 (successors 190 7 s38) 16 4 := offMemoRows (code:=0x404304b027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_5 : Block 190 7 (successors 190 7 s38) 20 4 := offMemoRows (code:=0x404304b027) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_6 : Block 190 7 (successors 190 7 s38) 24 4 := offMemoRows (code:=0x401802b017) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_7 : Block 190 7 (successors 190 7 s38) 28 4 := offMemoRows (code:=0x400402b017) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_8 : Block 190 7 (successors 190 7 s38) 32 4 := offMemoRows (code:=0x4056003001) (gs:=[(.fork 0x2c000000000000000000000003000004000000000000000000000000000003000000000000000004000004000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_9 : Block 190 7 (successors 190 7 s38) 36 4 := offMemoRows (code:=0x4004005004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_10 : Block 190 7 (successors 190 7 s38) 40 4 := offMemoRows (code:=0x402c00302c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_11 : Block 190 7 (successors 190 7 s38) 44 4 := offMemoRows (code:=0x23004018006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_12 : Block 190 7 (successors 190 7 s38) 48 4 := offMemoRows (code:=0x4025018004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_13 : Block 190 7 (successors 190 7 s38) 52 4 := offMemoRows (code:=0x4047003001) (gs:=[(.fork 0x2c000000000000000000000000000000000004000000000000000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_14 : Block 190 7 (successors 190 7 s38) 56 4 := offMemoRows (code:=0x4036004005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_15 : Block 190 7 (successors 190 7 s38) 60 4 := offMemoRows (code:=0x4001004036) (gs:=[(.fork 0x4000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_16 : Block 190 7 (successors 190 7 s38) 64 4 := offMemoRows (code:=0x302300600e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_17 : Block 190 7 (successors 190 7 s38) 68 4 := offMemoRows (code:=0x6006025000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_18 : Block 190 7 (successors 190 7 s38) 72 4 := offMemoRows (code:=0xb00600c054) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_19 : Block 190 7 (successors 190 7 s38) 76 4 := offMemoRows (code:=0xc05400c054) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_20 : Block 190 7 (successors 190 7 s38) 80 4 := offMemoRows (code:=0xb013013013) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_21 : Block 190 7 (successors 190 7 s38) 84 4 := offMemoRows (code:=0x600e00c00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_22 : Block 190 7 (successors 190 7 s38) 88 4 := offMemoRows (code:=0x25047043023) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_23 : Block 190 7 (successors 190 7 s38) 92 4 := offMemoRows (code:=0x54054006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_24 : Block 190 7 (successors 190 7 s38) 96 4 := offMemoRows (code:=0x17013018006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_25 : Block 190 7 (successors 190 7 s38) 100 4 := offMemoRows (code:=0x9409400b015) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_26 : Block 190 7 (successors 190 7 s38) 104 4 := offMemoRows (code:=0x5405400b00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b38_27 : Block 190 7 (successors 190 7 s38) 108 4 := offMemoRows (code:=0x13) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e38 : Excluded 190 8 s38 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=28) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b38_0
  · exact b38_1
  · exact b38_2
  · exact b38_3
  · exact b38_4
  · exact b38_5
  · exact b38_6
  · exact b38_7
  · exact b38_8
  · exact b38_9
  · exact b38_10
  · exact b38_11
  · exact b38_12
  · exact b38_13
  · exact b38_14
  · exact b38_15
  · exact b38_16
  · exact b38_17
  · exact b38_18
  · exact b38_19
  · exact b38_20
  · exact b38_21
  · exact b38_22
  · exact b38_23
  · exact b38_24
  · exact b38_25
  · exact b38_26
  · exact b38_27
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e39 : Excluded 190 8 s39 := offAudit (g:=(.restrict 4)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e40 : Excluded 190 8 s40 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_0 : Block 190 7 (successors 190 7 s41) 0 4 := offMemoRows (code:=0x24000024004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_1 : Block 190 7 (successors 190 7 s41) 4 4 := offMemoRows (code:=0x2400302401e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_2 : Block 190 7 (successors 190 7 s41) 8 4 := offMemoRows (code:=0xe01600c00d) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_3 : Block 190 7 (successors 190 7 s41) 12 4 := offMemoRows (code:=0x1a00e01a00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_4 : Block 190 7 (successors 190 7 s41) 16 4 := offMemoRows (code:=0x2a00001a00e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_5 : Block 190 7 (successors 190 7 s41) 20 4 := offMemoRows (code:=0x2a00002a02a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_6 : Block 190 7 (successors 190 7 s41) 24 4 := offMemoRows (code:=0xc00d02a02a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_7 : Block 190 7 (successors 190 7 s41) 28 4 := offMemoRows (code:=0x2a02a000016) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_8 : Block 190 7 (successors 190 7 s41) 32 4 := offMemoRows (code:=0x300801002a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_9 : Block 190 7 (successors 190 7 s41) 36 4 := offMemoRows (code:=0x500700f003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_10 : Block 190 7 (successors 190 7 s41) 40 4 := offMemoRows (code:=0xb00b00c005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_11 : Block 190 7 (successors 190 7 s41) 44 4 := offMemoRows (code:=0xb00700c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_12 : Block 190 7 (successors 190 7 s41) 48 4 := offMemoRows (code:=0xc00c00800b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_13 : Block 190 7 (successors 190 7 s41) 52 4 := offMemoRows (code:=0xc00c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_14 : Block 190 7 (successors 190 7 s41) 56 4 := offMemoRows (code:=0xc00c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_15 : Block 190 7 (successors 190 7 s41) 60 4 := offMemoRows (code:=0x1000c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_16 : Block 190 7 (successors 190 7 s41) 64 4 := offMemoRows (code:=0xf003003008) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_17 : Block 190 7 (successors 190 7 s41) 68 4 := offMemoRows (code:=0xc005005007) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_18 : Block 190 7 (successors 190 7 s41) 72 4 := offMemoRows (code:=0x800b00b007) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_19 : Block 190 7 (successors 190 7 s41) 76 4 := offMemoRows (code:=0xb00b00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_20 : Block 190 7 (successors 190 7 s41) 80 4 := offMemoRows (code:=0xc00c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_21 : Block 190 7 (successors 190 7 s41) 84 4 := offMemoRows (code:=0xc00c00c00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_22 : Block 190 7 (successors 190 7 s41) 88 4 := offMemoRows (code:=0x2600400c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_23 : Block 190 7 (successors 190 7 s41) 92 4 := offMemoRows (code:=0x1e026003026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_24 : Block 190 7 (successors 190 7 s41) 96 4 := offMemoRows (code:=0x2a02a000026) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_25 : Block 190 7 (successors 190 7 s41) 100 4 := offMemoRows (code:=0x400000402a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b41_26 : Block 190 7 (successors 190 7 s41) 104 4 := offMemoRows (code:=0x6) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e41 : Excluded 190 8 s41 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=27) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b41_0
  · exact b41_1
  · exact b41_2
  · exact b41_3
  · exact b41_4
  · exact b41_5
  · exact b41_6
  · exact b41_7
  · exact b41_8
  · exact b41_9
  · exact b41_10
  · exact b41_11
  · exact b41_12
  · exact b41_13
  · exact b41_14
  · exact b41_15
  · exact b41_16
  · exact b41_17
  · exact b41_18
  · exact b41_19
  · exact b41_20
  · exact b41_21
  · exact b41_22
  · exact b41_23
  · exact b41_24
  · exact b41_25
  · exact b41_26
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_0 : Block 190 7 (successors 190 7 s42) 0 4 := offMemoRows (code:=0xb006010010) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_1 : Block 190 7 (successors 190 7 s42) 4 4 := offMemoRows (code:=0xa01001300b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_2 : Block 190 7 (successors 190 7 s42) 8 4 := offMemoRows (code:=0xa00d00b00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_3 : Block 190 7 (successors 190 7 s42) 12 4 := offMemoRows (code:=0xa01000b00f) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_4 : Block 190 7 (successors 190 7 s42) 16 4 := offMemoRows (code:=0xa00d01300b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_5 : Block 190 7 (successors 190 7 s42) 20 4 := offMemoRows (code:=0xa00401500f) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_6 : Block 190 7 (successors 190 7 s42) 24 4 := offMemoRows (code:=0xa01e00b001) (gs:=[(.fork 0x300000000000000000000000300000000000400000000000300000000001c000000000000000004000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_7 : Block 190 7 (successors 190 7 s42) 28 4 := offMemoRows (code:=0xa00400b004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_8 : Block 190 7 (successors 190 7 s42) 32 4 := offMemoRows (code:=0xa01e00b001) (gs:=[(.fork 0x400000000000300000000000000000000000300001c000000000000000004000000000003000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_9 : Block 190 7 (successors 190 7 s42) 36 4 := offMemoRows (code:=0x401000b004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_10 : Block 190 7 (successors 190 7 s42) 40 4 := offMemoRows (code:=0x1000d01300b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_11 : Block 190 7 (successors 190 7 s42) 44 4 := offMemoRows (code:=0x4003004015) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_12 : Block 190 7 (successors 190 7 s42) 48 4 := offMemoRows (code:=0x4003004005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_13 : Block 190 7 (successors 190 7 s42) 52 4 := offMemoRows (code:=0x2c00a000005) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_14 : Block 190 7 (successors 190 7 s42) 56 4 := offMemoRows (code:=0x601302c01b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_15 : Block 190 7 (successors 190 7 s42) 60 4 := offMemoRows (code:=0x6007003) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_16 : Block 190 7 (successors 190 7 s42) 64 4 := offMemoRows (code:=0x1300001300b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_17 : Block 190 7 (successors 190 7 s42) 68 4 := offMemoRows (code:=0x1302c01402c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_18 : Block 190 7 (successors 190 7 s42) 72 4 := offMemoRows (code:=0x1301601402c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_19 : Block 190 7 (successors 190 7 s42) 76 4 := offMemoRows (code:=0x601601402c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_20 : Block 190 7 (successors 190 7 s42) 80 4 := offMemoRows (code:=0xd01701300b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_21 : Block 190 7 (successors 190 7 s42) 84 4 := offMemoRows (code:=0xb01000c006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_22 : Block 190 7 (successors 190 7 s42) 88 4 := offMemoRows (code:=0x1300d00f00c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_23 : Block 190 7 (successors 190 7 s42) 92 4 := offMemoRows (code:=0x1301602c02c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_24 : Block 190 7 (successors 190 7 s42) 96 4 := offMemoRows (code:=0x1602c02c) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_25 : Block 190 7 (successors 190 7 s42) 100 4 := offMemoRows (code:=0x1b01302e00a) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_26 : Block 190 7 (successors 190 7 s42) 104 4 := offMemoRows (code:=0x1400001402e) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b42_27 : Block 190 7 (successors 190 7 s42) 108 4 := offMemoRows (code:=0x16) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e42 : Excluded 190 8 s42 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=28) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b42_0
  · exact b42_1
  · exact b42_2
  · exact b42_3
  · exact b42_4
  · exact b42_5
  · exact b42_6
  · exact b42_7
  · exact b42_8
  · exact b42_9
  · exact b42_10
  · exact b42_11
  · exact b42_12
  · exact b42_13
  · exact b42_14
  · exact b42_15
  · exact b42_16
  · exact b42_17
  · exact b42_18
  · exact b42_19
  · exact b42_20
  · exact b42_21
  · exact b42_22
  · exact b42_23
  · exact b42_24
  · exact b42_25
  · exact b42_26
  · exact b42_27
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e52 : Excluded 190 8 s52 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_0 : Block 190 7 (successors 190 7 s53) 0 4 := offMemoRows (code:=0x3006006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_1 : Block 190 7 (successors 190 7 s53) 4 4 := offMemoRows (code:=0x4004004004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_2 : Block 190 7 (successors 190 7 s53) 8 4 := offMemoRows (code:=0x4006004004) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_3 : Block 190 7 (successors 190 7 s53) 12 4 := offMemoRows (code:=0x6001004001) (gs:=[(.fork 0x500a000000000000 []),(.fork 0xa000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_4 : Block 190 7 (successors 190 7 s53) 16 4 := offMemoRows (code:=0x6064006006) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_5 : Block 190 7 (successors 190 7 s53) 20 4 := offMemoRows (code:=0x4064001001) (gs:=[(.fork 0x3000000000000000000000000000000000000000000000000000000 []),(.fork 0xc00300c000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_6 : Block 190 7 (successors 190 7 s53) 24 4 := offMemoRows (code:=0x1006006001) (gs:=[(.fork 0x3000000000000000003000000000003000000000000000000000000000000003000000000003000000000 []),(.fork 0x300400b012006000000012003004004000000000000000004000006004004004000003004000004000006 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_7 : Block 190 7 (successors 190 7 s53) 28 4 := offMemoRows (code:=0x6001004001) (gs:=[(.fork 0x400000600000000000000800a000000000000 []),(.fork 0x1200600a01200400000a00600000300000a004004004004003004000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_8 : Block 190 7 (successors 190 7 s53) 32 4 := offMemoRows (code:=0x4001001006) (gs:=[(.fork 0x300400b012006000004004000004003000012003004004000000000000000004000006004000004000006 []),(.fork 0x400000800a006000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_9 : Block 190 7 (successors 190 7 s53) 36 4 := offMemoRows (code:=0x1013006001) (gs:=[(.fork 0x1200600a01200400000a00600000300000a004004004004003004000 []),(.fork 0x301201200000001201200000000a01200a01200000000001a [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_10 : Block 190 7 (successors 190 7 s53) 40 4 := offMemoRows (code:=0x400b00b) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_11 : Block 190 7 (successors 190 7 s53) 44 4 := offMemoRows (code:=0x100b001004) (gs:=[(.fork 0x3000000000 []),(.fork 0xa000003000000000044000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_12 : Block 190 7 (successors 190 7 s53) 48 4 := offMemoRows (code:=0x6064001004) (gs:=[(.fork 0x500000001a003000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_13 : Block 190 7 (successors 190 7 s53) 52 4 := offMemoRows (code:=0x4064001001) (gs:=[(.fork 0x3000000000000000000000000000000000000000000 []),(.fork 0xc00300c000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_14 : Block 190 7 (successors 190 7 s53) 56 4 := offMemoRows (code:=0x1006006001) (gs:=[(.fork 0x3000003000000000000000000000000003000000000003000000000003000000000 []),(.fork 0x300400001200b012006000003004004000000000000000004000006004004004000003004000004000006 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_15 : Block 190 7 (successors 190 7 s53) 60 4 := offMemoRows (code:=0x6001004001) (gs:=[(.fork 0x400000600000000000000800a000000000000 []),(.fork 0x1200600a01200400000a00600000300000a004004004004003004000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_16 : Block 190 7 (successors 190 7 s53) 64 4 := offMemoRows (code:=0x4001001006) (gs:=[(.fork 0x300400001200b012006000004004000004003003004004000000000000000004000006004000004000006 []),(.fork 0x400000800a006000000000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_17 : Block 190 7 (successors 190 7 s53) 68 4 := offMemoRows (code:=0x100b006001) (gs:=[(.fork 0x1200600a01200400000a00600000300000a004004004004003004000 []),(.fork 0x300000000004400a000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_18 : Block 190 7 (successors 190 7 s53) 72 4 := offMemoRows (code:=0x4001004) (gs:=[(.fork 0x500000001a003000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_19 : Block 190 7 (successors 190 7 s53) 76 4 := offMemoRows (code:=0x6054001004) (gs:=[(.fork 0x3000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_20 : Block 190 7 (successors 190 7 s53) 80 4 := offMemoRows (code:=0x23054001001) (gs:=[(.fork 0x4025000000000000000003000000 []),(.fork 0x600000b00300b000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_21 : Block 190 7 (successors 190 7 s53) 84 4 := offMemoRows (code:=0x1006006003) (gs:=[(.fork 0x700a000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_22 : Block 190 7 (successors 190 7 s53) 88 4 := offMemoRows (code:=0x1006006001) (gs:=[(.fork 0xa000000000000000 []),(.fork 0x700a000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_23 : Block 190 7 (successors 190 7 s53) 92 4 := offMemoRows (code:=0x4006001) (gs:=[(.fork 0xa000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_24 : Block 190 7 (successors 190 7 s53) 96 4 := offMemoRows (code:=0x6054000000) (gs:=[]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_25 : Block 190 7 (successors 190 7 s53) 100 4 := offMemoRows (code:=0x43054001001) (gs:=[(.fork 0x3000000000000000000000000000000000000000000000000004025000000000000000000000000000000000000 []),(.fork 0x600000b00300b000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_26 : Block 190 7 (successors 190 7 s53) 104 4 := offMemoRows (code:=0x1006006003) (gs:=[(.fork 0x700a000000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem b53_27 : Block 190 7 (successors 190 7 s53) 108 4 := offMemoRows (code:=0x6001) (gs:=[(.fork 0xa000000000000000 [])]) noDBsafe (by decide) (by decide +kernel)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e53 : Excluded 190 8 s53 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=4) (q:=28) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact b53_0
  · exact b53_1
  · exact b53_2
  · exact b53_3
  · exact b53_4
  · exact b53_5
  · exact b53_6
  · exact b53_7
  · exact b53_8
  · exact b53_9
  · exact b53_10
  · exact b53_11
  · exact b53_12
  · exact b53_13
  · exact b53_14
  · exact b53_15
  · exact b53_16
  · exact b53_17
  · exact b53_18
  · exact b53_19
  · exact b53_20
  · exact b53_21
  · exact b53_22
  · exact b53_23
  · exact b53_24
  · exact b53_25
  · exact b53_26
  · exact b53_27
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem e54 : Excluded 190 8 s54 := offAudit (g:=(.restrict 2)) noDBsafe (by decide) (by decide +kernel)
end Six11247

namespace Six11247
open Theta
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem conclusionOf
    (e8 : Excluded 190 8 s8)
    (e11 : Excluded 190 8 s11)
    (e36 : Excluded 190 8 s36)
    (e39 : Excluded 190 8 s39)
    (e52 : Excluded 190 8 s52)
    (e54 : Excluded 190 8 s54)
    (e12 : Excluded 190 8 s12)
    (e0 : Excluded 190 8 s0)
    (e2 : Excluded 190 8 s2)
    (e4 : Excluded 190 8 s4)
    (e6 : Excluded 190 8 s6)
    (e10 : Excluded 190 8 s10)
    (e14 : Excluded 190 8 s14)
    (e41 : Excluded 190 8 s41)
    (e42 : Excluded 190 8 s42)
    (e38 : Excluded 190 8 s38)
    (e7 : Excluded 190 8 s7)
    (e15 : Excluded 190 8 s15)
    (e5 : Excluded 190 8 s5)
    (e40 : Excluded 190 8 s40)
    (e13 : Excluded 190 8 s13)
    (e9 : Excluded 190 8 s9)
    (e37 : Excluded 190 8 s37)
    (e53 : Excluded 190 8 s53)
    (e1 : Excluded 190 8 s1) : ¬Possible 190 9 inputs := by
  have e3 : Excluded 190 8 s3 := fun h => e2 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e16 : Excluded 190 8 s16 := fun h => e8 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e17 : Excluded 190 8 s17 := fun h => e9 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e18 : Excluded 190 8 s18 := fun h => e10 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e19 : Excluded 190 8 s19 := fun h => e11 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e20 : Excluded 190 8 s20 := fun h => e12 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e21 : Excluded 190 8 s21 := fun h => e13 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e22 : Excluded 190 8 s22 := fun h => e14 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e23 : Excluded 190 8 s23 := fun h => e15 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e24 : Excluded 190 8 s24 := fun h => e8 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e25 : Excluded 190 8 s25 := fun h => e9 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e26 : Excluded 190 8 s26 := fun h => e10 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e27 : Excluded 190 8 s27 := fun h => e11 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e28 : Excluded 190 8 s28 := fun h => e4 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e29 : Excluded 190 8 s29 := fun h => e5 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e30 : Excluded 190 8 s30 := fun h => e6 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e31 : Excluded 190 8 s31 := fun h => e7 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e32 : Excluded 190 8 s32 := fun h => e8 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e33 : Excluded 190 8 s33 := fun h => e9 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e34 : Excluded 190 8 s34 := fun h => e10 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e35 : Excluded 190 8 s35 := fun h => e11 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e43 : Excluded 190 8 s43 := fun h => e42 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e44 : Excluded 190 8 s44 := fun h => e36 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e45 : Excluded 190 8 s45 := fun h => e37 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e46 : Excluded 190 8 s46 := fun h => e38 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e47 : Excluded 190 8 s47 := fun h => e39 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e48 : Excluded 190 8 s48 := fun h => e36 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e49 : Excluded 190 8 s49 := fun h => e37 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e50 : Excluded 190 8 s50 := fun h => e39 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e51 : Excluded 190 8 s51 := fun h => e38 (perm_feasible turns2 safe2 (by decide +kernel) (by decide +kernel) h)
  have e55 : Excluded 190 8 s55 := fun h => e54 (perm_feasible turns1 safe1 (by decide +kernel) (by decide +kernel) h)
  have e56 : Excluded 190 8 s56 := fun h => e36 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e57 : Excluded 190 8 s57 := fun h => e37 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e58 : Excluded 190 8 s58 := fun h => e38 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have e59 : Excluded 190 8 s59 := fun h => e39 (perm_feasible turns3 safe3 (by decide +kernel) (by decide +kernel) h)
  have root : Excluded 190 9 inputs := by
    apply join_exclusions (by decide +kernel)
    rw [next_states]
    intro v hv
    simp only [states, List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
    · exact e11
    · exact e12
    · exact e13
    · exact e14
    · exact e15
    · exact e16
    · exact e17
    · exact e18
    · exact e19
    · exact e20
    · exact e21
    · exact e22
    · exact e23
    · exact e24
    · exact e25
    · exact e26
    · exact e27
    · exact e28
    · exact e29
    · exact e30
    · exact e31
    · exact e32
    · exact e33
    · exact e34
    · exact e35
    · exact e36
    · exact e37
    · exact e38
    · exact e39
    · exact e40
    · exact e41
    · exact e42
    · exact e43
    · exact e44
    · exact e45
    · exact e46
    · exact e47
    · exact e48
    · exact e49
    · exact e50
    · exact e51
    · exact e52
    · exact e53
    · exact e54
    · exact e55
    · exact e56
    · exact e57
    · exact e58
    · exact e59
  rintro ⟨j,S,hj,live,sub⟩
  have eq := initial live sub
  apply root
  exact ⟨j,hj,eq ▸ live,by decide +kernel⟩
end Six11247

namespace Six11247
open Theta
theorem excluded : ¬Possible 190 9 inputs := conclusionOf e8 e11 e36 e39 e52 e54 e12 e0 e2 e4 e6 e10 e14 e41 e42 e38 e7 e15 e5 e40 e13 e9 e37 e53 e1
end Six11247

namespace SixBridge11247
open PEqualNP.CircuitLowerBounds Theta

def seedWires (inputs : List ℕ) : List Wire := inputs.map fun a => (false, a)

theorem sampled_binary_lower {m : ℕ} {inputs : List ℕ} {f : (Fin 7 → Bool) → Bool}
    (hm : 0 < m) (pos neg : Fin m → Fin 7 → Bool)
    (listed : ∀ i : Fin m, (seedWires inputs).map (read i.val) = List.ofFn (pos i) ∧
      (seedWires inputs).map (read (m+i.val)) = List.ofFn (neg i))
    (labels : ∀ i, f (pos i) = true ∧ f (neg i) = false)
    (noLive : ∀ k ≤ 10, ∀ S, Live m k S → (∀ a ∈ S, a ∈ inputs) → False)
    (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) :
    11 ≤ gs.countP counted := by
  let wires := execute gs (seedWires inputs)
  let result := wires.getD o zero
  have hlegal : ∀ g ∈ gs, g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := legal
  have readEval (j : ℕ) (x : Fin 7 → Bool) (row : (seedWires inputs).map (read j) = List.ofFn x) :
      read j result = f x := by
    change read j (wires.getD o zero) = f x
    rw [← read_get]
    dsimp only [wires]
    rw [execute_read j gs _ hlegal, row]
    exact computes x
  have good : Good m result.2 := by
    intro i hi e
    let t : Fin m := ⟨i, hi⟩
    have same : read i result = read (m+i) result := congrArg (fun b : Bool => result.1 != b) e
    have hp := (readEval i (pos t) (listed t).1).trans (labels t).1
    have hn := (readEval (m+i) (neg t) (listed t).2).trans (labels t).2
    exact Bool.noConfusion (hp.symm.trans (same.trans hn))
  have nonzero : result.2 ≠ 0 := by
    intro h
    have atZero := good 0 hm
    simp [h] at atZero
  have found : result.2 ∈ reps wires := (get_simple wires o).resolve_left nonzero
  obtain ⟨k,S,hk,live,subset⟩ := extract good nonzero gs (seedWires inputs) found
  have subset' : ∀ a ∈ S, a ∈ inputs := by simpa [reps,seedWires] using subset
  by_contra! small
  exact noLive k (by omega) S live subset'

def edges : List ℕ := [0,3,0,4,1,4,1,5,2,5,3,5,0,6,1,6,2,6,4,6]
def edgeSpec (x : Fin 7 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

theorem replacement {m : ℕ} {inputs : List ℕ}
    (hm : 0 < m) (pos neg : Fin m → Fin 7 → Bool)
    (listed : ∀ i : Fin m, (seedWires inputs).map (read i.val) = List.ofFn (pos i) ∧
      (seedWires inputs).map (read (m+i.val)) = List.ofFn (neg i))
    (labels : ∀ i, edgeSpec (pos i) = true ∧ edgeSpec (neg i) = false)
    (noLive : ∀ k ≤ 10, ∀ S, Live m k S → (∀ a ∈ S, a ∈ inputs) → False) :
    ∀ (gates : List Gate) (o : ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
      (∀ x : Fin 7 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeSpec x) →
      ∃ (gates' : List Gate) (o' : ℕ),
        (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates',o'⟩ (List.ofFn x) = edgeSpec x := by
  intro gates o legal _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g,hg,op⟩ := hasNot
    have binary := sampled_binary_lower hm pos neg listed labels noLive gates o legal computes
    have ne : gates.countP counted ≠ gates.length := by
      intro eq
      have h := List.countP_eq_length.mp eq g hg
      simp [counted, op] at h
    have le := List.countP_le_length (p := counted) (l := gates)
    exact Graph11247.size_suffices gates.length (by omega)
  · refine ⟨gates,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨basis,fanin⟩ := legal g hg
    rcases basis with h | h | h
    · exact ⟨Or.inl h,fanin⟩
    · exact ⟨Or.inr h,fanin⟩
    · exact (hasNot ⟨g,hg,h⟩).elim

end SixBridge11247

namespace ProjectPair11247
open Theta

/-- Keep the first `m` entries of both banks and exchange the banks. -/
def trim (m a : ℕ) : ℕ :=
  let mask := 2 ^ m - 1
  ((a >>> (m+1)) &&& mask) ||| ((a &&& mask) <<< m)

theorem trim_bit (m a j : ℕ) : (trim m a).testBit j =
    if j < m then a.testBit (m+1+j) else if j < m+m then a.testBit (j-m) else false := by
  simp only [trim, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h : j < m
  · simp [h, show ¬ m ≤ j by omega]
  · by_cases k : j < m+m
    · simp [h,k,show m ≤ j by omega,show j-m < m by omega]
    · simp [h,k,show m ≤ j by omega,show ¬ j-m < m by omega]

def dropPair (m : ℕ) (hm : 0 < m) : Projection (m+1) m where
  toFun := trim m
  atZero := by simp [trim]
  combineEq := by
    intro d a b hd
    apply Nat.eq_of_testBit_eq
    intro j
    interval_cases d <;> simp only [combine, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_xor, trim_bit] <;> split_ifs <;> simp
  good := by
    intro a h i hi
    simp only [trim_bit, hi, ite_true, show ¬m+i<m by omega, ite_false,
      show m+i<m+m by omega, Nat.add_sub_cancel_left]
    exact (h i (by omega)).symm
  someRow := hm

theorem noLive_of_minor {m : ℕ} (hm : 0 < m) (xs ys : List ℕ) (special : ℕ)
    (distinguished : ∀ a ∈ xs, a.testBit m ≠ a.testBit (m+1+m) → a = special)
    (vanishes : trim m special = 0)
    (rawImages : ∀ a ∈ xs, trim m a = 0 ∨ trim m a ∈ ys)
    (excluded : ¬ Possible m 9 ys) :
    ∀ k ≤ 10, ∀ S, Live (m+1) k S → (∀ a ∈ S, a ∈ xs) → False := by
  intro k hk S h sub
  obtain ⟨a, ha, different⟩ := liveSeparates h m (by omega)
  have mem := distinguished a (sub a ha) different ▸ ha
  have filt : special ∈ S.filter (fun v => (dropPair m hm).toFun v = 0) :=
    Finset.mem_filter.mpr ⟨mem,vanishes⟩
  have loss : 0 < dead (dropPair m hm).toFun S := Finset.card_pos.mpr ⟨special,filt⟩
  obtain ⟨s,T,hs,liveT,images⟩ := projectLive (dropPair m hm) h
  apply excluded
  refine ⟨s,T,by omega,liveT,?_⟩
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (images z hz)
  exact (rawImages x (sub x hx)).resolve_left (liveNonzero liveT _ hz)

end ProjectPair11247

namespace SixLift11247
open Theta ProjectPair11247

def six : List ℕ := [0x3807070f8c11c0707f80fe38387f87803e01c1fe03ffffc020040c0a004100402a107040609a1220a92100a844c546,0xc03807f0701e007f87ff01c03f83f8003ffffe1ffc07c00000200440404800ca0c3821002206a00430732830e09614,0xf003ff8007fe0007ff80001ffc003ffffc001ffe00007ffd400692001fa8049ad40a103250004c48e0046b5028218b8,0xfffc000007fffff80000001fffffc00000001fffffff8000d4500000093121c00000006b6952000480204c6470b0020,0xfffffffff80000000000001fffffffffffffe00000000002bf6965aac00009000010244d8d9c91970c78000040c0040,0xffffffffffffffffffffffe0000000000000000000000003298db93312c24e13191c380000000018004000000000080]
def seven : List ℕ := [0x100206050020802015083820304d0910549080542262a300e01c1c3e304701c1fe03f8e0e1fe1e00f80707f80fffff,0x10022020240065061c10801103500218399418704b0a0300e01fc1c07801fe1ffc0700fe0fe000fffff87ff01f00,0x400000000000000000000000000000000000000000000000,0xa00349000fd4024d6a05081928002624700235a81410c5c3c00ffe001ff8001ffe00007ff000fffff0007ff80001fff,0x6a280000049890e000000035b4a900024010263238580103fff000001fffffe00000007fffff000000007ffffffe000,0x35fb4b2d56000048000081226c6ce48cb863c000020600207ffffffffe00000000000007fffffffffffff80000000000,0x194c6dc99896127098c8e1c000000000c0020000000000403ffffffffffffffffffffff8000000000000000000000000]
def posBank : ℕ := 0x93c78f1e3972e3c78f0e1c3870d5ab569d3a7468d1a3463c78f162c58b0e1c3870dab56acd9b162c58b14e952a5468d1a142850a14284b972e54a952a54993264c3870e1c2850a142850a0c183060c182e9d3a72e5cb870e1c3866cd9b264c993162c58b156ad5aa54a952952a54a850a142850a1428468d1a346891224489122446cd9b3468d1a3464c99324c993264891224489122244891224488b162c58b12244891224489
def negBank : ℕ := 0x830486063030c0c10e080c1010c12056090870488080460420f040400b04042800c8302a4189100c10100e0100500801c1220303040048140e440142014880200c006080e091005030403048808418100c0c0a6084c30406080860841b04040130428080142281a0142012140200e090c10a03028400428018203818214028182006050330405080460808024018202c0c10140c1006084c10060400a100c1019084c0a100c080
def special : ℕ := 0x400000000000000000000000000000000000000000000000
def sample (bank : ℕ) (i : Fin 191) (j : Fin 7) := bank.testBit (7*i.val+j.val)

def graph (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) ||
  (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6)

theorem listed : ∀ i : Fin 191, (SixBridge11247.seedWires seven).map (read i.val) = List.ofFn (sample posBank i) ∧
    (SixBridge11247.seedWires seven).map (read (191+i.val)) = List.ofFn (sample negBank i) := by decide +kernel

theorem labels : ∀ i : Fin 191, SixBridge11247.edgeSpec (sample posBank i) = true ∧
    SixBridge11247.edgeSpec (sample negBank i) = false := by
  have spec : ∀ x, SixBridge11247.edgeSpec x = graph x := by decide +kernel
  simp only [spec]
  decide +kernel

theorem distinguished : ∀ a ∈ seven, a.testBit 190 ≠ a.testBit 381 → a = special := by
  intro a ha
  simp only [seven, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem projected : ∀ a ∈ seven, trim 190 a = 0 ∨ trim 190 a ∈ six := by
  intro a ha
  simp only [seven, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem noLiveFromSix (excluded : ¬ Possible 190 9 six) :
    ∀ k ≤ 10, ∀ S, Live 191 k S → (∀ a ∈ S, a ∈ seven) → False :=
  noLive_of_minor (by decide) seven six special distinguished (by decide +kernel) projected excluded

theorem from_six (excluded : ¬ Possible 190 9 six) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  SixBridge11247.replacement (m := 191) (inputs := seven) (by decide)
    (sample posBank) (sample negBank) listed labels (noLiveFromSix excluded)

end SixLift11247

end PEqualNP.Outside.L_meta_11247_aux

theorem PEqualNP.Outside.L_meta_11247 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact PEqualNP.Outside.L_meta_11247_aux.SixLift11247.from_six PEqualNP.Outside.L_meta_11247_aux.Six11247.excluded
