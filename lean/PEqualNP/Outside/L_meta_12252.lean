import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12252

-- Compression des fils et restriction adaptées de L-meta-4425 et L-meta-2960.
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
def Good (m a : ℕ) := ∀ i< m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i< m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
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
  have bit : (full m).testBit i=decide (i< m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i< m
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
  if a< b then
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
  have e : (full m).testBit i=decide (i< m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i< m
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
lemma pair_ok {m fuel go v a b d} (ordered : a< b) (hd : d<4)
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
    (lt : a< b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
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
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))






abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

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
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
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






lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i< m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i< m
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


def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i< m) (pos : 0< h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i< r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i< r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)



-- Five-input exhaustive certificate adapted from L-meta-8632 and L-meta-1417.
namespace Five
abbrev Q := BitVec 32

def norm (w : Q) := if w.getLsbD 0 then ~~~w else w

def ops (a b : Q) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]

def Trail (t : Q) (s : Finset Q) (n : ℕ) : Prop :=
  ∀ P : Finset Q → ℕ → Prop,
    (∀ k, P {t} k) →
    (∀ {r : Finset Q} {a b c : Q} {k : ℕ}, a ≠ b → c ∉ insert a (insert b r) →
      c ≠ 0 → c ∈ ops a b → P (insert c r) k → P (insert a (insert b r)) (k+1)) →
    P s n

theorem Trail.done {t : Q} (k : ℕ) : Trail t {t} k :=
  fun _ done _ => done k

theorem Trail.step {t a b c : Q} {r : Finset Q} {k : ℕ} (hab : a ≠ b)
    (hf : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (h : Trail t (insert c r) k) : Trail t (insert a (insert b r)) (k+1) :=
  fun P done step => step hab hf nz hc (h P done step)

theorem trail_ind {t : Q} {P : Finset Q → ℕ → Prop} {s n} (h : Trail t s n)
    (done : ∀ k, P {t} k)
    (step : ∀ {r a b c k}, a ≠ b → c ∉ insert a (insert b r) → c ≠ 0 → c ∈ ops a b →
      Trail t (insert c r) k → P (insert c r) k → P (insert a (insert b r)) (k+1)) : P s n :=
  (h (fun r k => Trail t r k ∧ P r k) (fun k => ⟨Trail.done k, done k⟩)
    (fun hab hf nz hc h' => ⟨Trail.step hab hf nz hc h'.1, step hab hf nz hc h'.1 h'.2⟩)).2

theorem trail_lift {t s n} (h : Trail t s n) : Trail t s (n+1) := by
  apply trail_ind (P := fun s n => Trail t s (n+1)) h
  · intro k; exact Trail.done _
  · intro r a b c k hab hf nz hc _ ih; exact .step hab hf nz hc ih

theorem trail_mono {t s n m} (h : Trail t s n) (le : n ≤ m) : Trail t s m := by
  induction le with
  | refl => exact h
  | step _ ih => exact trail_lift ih

theorem trail_card {t s n} (h : Trail t s n) : s.card ≤ n+1 := by
  apply trail_ind (P := fun s n => s.card ≤ n+1) h
  · simp
  · intro r a b c k hab fresh nz hc h ih
    have hn : c ∉ r := fun hh => fresh (by simp [hh])
    rw [Finset.card_insert_of_notMem hn] at ih
    have := Finset.card_insert_le a (insert b r)
    have := Finset.card_insert_le b r
    omega

theorem trail_sep {t s n} (h : Trail t s n) (i j : ℕ) (hi : i < 32) (hj : j < 32)
    (same : ∀ x ∈ s, x.getLsbD i = x.getLsbD j) : t.getLsbD i = t.getLsbD j := by
  revert same
  apply trail_ind (P := fun s _ => (∀ x ∈ s, x.getLsbD i = x.getLsbD j) → t.getLsbD i = t.getLsbD j) h
  · intro k same; exact same _ (by simp)
  · intro r a b c k hab fresh nz hc h ih same
    apply ih
    have ha := same a (by simp)
    have hb := same b (by simp)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxr
    · simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hi, decide_eq_true hj, ha, hb]
    · exact same _ (by simp [hxr])

def jumps : List ℕ := [1, 2, 4, 8, 16]
def dif (w : Q) (d : ℕ) := (w ^^^ (w >>> d)) &&& (BitVec.allOnes 32 >>> d)
def unionDif (ws : List Q) (d : ℕ) : Q :=
  ws.foldr (fun w s => dif w d ||| s) 0
def cover (t : Q) (ws : List Q) : Bool :=
  jumps.all fun d => (dif t d &&& unionDif ws d) == dif t d

theorem bit_dif {w : Q} {d i : ℕ} (hi : i < 32) :
    (dif w d).getLsbD i = true ↔ i+d < 32 ∧ w.getLsbD i ≠ w.getLsbD (i+d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

theorem bit_union (ws : List Q) (d i : ℕ) :
    (unionDif ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif w d ||| unionDif ws d).getLsbD i = true ↔ _
    simp [ih]

theorem trail_cover {t : Q} {ws : List Q} {n} (h : Trail t ws.toFinset n) :
    cover t ws = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif t d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    have ex : ∃ w ∈ ws, w.getLsbD i ≠ w.getLsbD (i+d) := by
      by_contra! hn
      exact hne (trail_sep h i _ hi hj (by simpa using hn))
    obtain ⟨w, hw, hh⟩ := ex
    rw [(bit_union ws d i).mpr ⟨w, hw, (bit_dif hi).mpr ⟨hj,hh⟩⟩]
    rfl

def pools (ws : List Q) (a b : Q) : List (List Q) :=
  [ws.filter (fun x => x != a && x != b), ws.filter (· != a), ws.filter (· != b), ws]

def walk (t : Q) : ℕ → List Q → Bool
  | 0, ws => ws.contains t
  | n+1, ws =>
    ws.length ≤ n+2 && cover t ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk t n (c :: r))

theorem pools_find {ws : List Q} {r : Finset Q} {a b : Q}
    (hw : ws.toFinset = insert a (insert b r)) (hn : ws.Nodup) :
    ∃ l ∈ pools ws a b, l.Nodup ∧ l.toFinset = r := by
  have mem (x : Q) : x ∈ ws ↔ x = a ∨ x = b ∨ x ∈ r := by
    rw [← List.mem_toFinset, hw]; simp
  by_cases ha : a ∈ r <;> by_cases hb : b ∈ r
  · exact ⟨ws, by simp [pools], hn, by simpa [ha,hb] using hw⟩
  · refine ⟨ws.filter (· != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (· != a), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (fun x => x != a && x != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind

theorem ops_swap {a b c : Q} (h : c ∈ ops a b) : c ∈ ops b a := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at *
  rw [BitVec.and_comm a b, BitVec.or_comm a b] at h
  tauto


theorem walk_pair {a b c : Q} {r : Finset Q} {t : Q} {k : ℕ}
    {ws : List Q} (hab : a < b) (hw : ws.toFinset = insert a (insert b r))
    (hn : ws.Nodup) (fresh : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (hdr : Trail t (insert c r) k)
    (ih : ∀ vs : List Q, vs.toFinset = insert c r → vs.Nodup → walk t k vs = true) :
    (ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ k &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk t k (c :: r)) = true := by
  obtain ⟨l, hl, hnl, hfl⟩ := pools_find hw hn
  have ha : a ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hb : b ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hnws : c ∉ ws := by simpa [← hw] using fresh
  have hnr : c ∉ r := fun h => fresh (by simp [h])
  have hnlc : c ∉ l := by simpa [← hfl] using hnr
  have hsize := trail_card hdr
  rw [Finset.card_insert_of_notMem hnr, ← hfl, List.toFinset_card_of_nodup hnl] at hsize
  apply List.any_eq_true.mpr
  refine ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hab, List.any_eq_true.mpr ⟨l, hl, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, List.any_eq_true.mpr ⟨c, hc, ?_⟩⟩
  simp [hnws, nz, ih (c :: l) (by simp [hfl]) (List.nodup_cons.mpr ⟨hnlc, hnl⟩)] <;> exact nz

theorem trail_walk {t s n} (h : Trail t s n) :
    ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk t n ws = true := by
  apply trail_ind (P := fun s n => ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk t n ws = true) h
  · intro k
    intro ws hw hn
    have ht : t ∈ ws := by rw [← List.mem_toFinset, hw]; simp
    cases k with
    | zero => simpa [walk] using ht
    | succ k =>
      have hcv := trail_cover (t := t) (n := k+1) (ws := ws) (hw ▸ Trail.done (t := t) (k+1))
      have hc := List.toFinset_card_of_nodup hn
      rw [hw, Finset.card_singleton] at hc
      simp [walk, ht, hcv, show ws.length ≤ k+2 by omega]
  · intro r a b c k hab fresh nz hc h ih
    intro ws hw hn
    have hall := Trail.step hab fresh nz hc h
    have hcv := trail_cover (ws := ws) (hw ▸ hall)
    have hsize := trail_card hall
    rw [← hw, List.toFinset_card_of_nodup hn] at hsize
    simp only [walk, show ws.length ≤ k+2 by omega, decide_true, hcv, Bool.true_and]
    rw [Bool.or_eq_true]
    right
    have hne : a.toNat ≠ b.toNat := fun he => hab (BitVec.eq_of_toNat_eq he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact walk_pair hlt hw hn fresh nz hc h ih
    · rw [Finset.insert_comm] at hw fresh
      exact walk_pair hgt hw hn fresh nz (ops_swap hc) h ih


def inputs : List Q := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def initial : List Q := 0 :: inputs
def run (t : Q) (k : ℕ) := initial.sublists.any (walk t k)

def splitRun (t : Q) (n m j : ℕ) :=
  initial.sublists.any fun ws =>
    ws.length ≤ n+2 && cover t ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => (c.toNat % m == j) &&
          !(ws.contains c) && c != 0 && walk t n (c :: r))

theorem partition_run {t : Q} {n m : ℕ} (hm : 0 < m)
    (hh : ∀ j : Fin m, splitRun t n m j.val = false) : run t (n+1) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨ws,hw,hg⟩ := List.any_eq_true.mp h
  simp only [walk, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hl, hv⟩, ht | ⟨a,ha,b,hb,hab,r,hr,hlen,c,hc,⟨hhc,hz⟩,hwalk⟩⟩ := hg
  · have hsplit : splitRun t n m 0 = true := by
      apply List.any_eq_true.mpr
      exact ⟨ws,hw, by simp [hl, hv, List.contains_iff_mem.mp ht]⟩
    have he := hh ⟨0,hm⟩
    change splitRun t n m 0 = false at he
    rw [he] at hsplit
    contradiction
  · let j : Fin m := ⟨c.toNat % m, Nat.mod_lt _ hm⟩
    have hsplit : splitRun t n m j.val = true := by
      apply List.any_eq_true.mpr
      refine ⟨ws,hw,?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact ⟨⟨hl,hv⟩, Or.inr ⟨a,ha,b,hb,hab,r,hr,hlen,c,hc,⟨⟨by simp [j],hhc⟩,hz⟩,hwalk⟩⟩
    rw [hh j] at hsplit
    contradiction


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x0 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 0 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x1 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 1 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x2 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 2 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x3 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 3 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x4 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 4 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x5 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 5 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x6 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 6 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x7 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 7 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x8 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 8 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x9 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 9 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x10 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 10 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x11 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 11 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x12 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 12 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x13 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 13 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x14 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 14 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x15 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 15 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x16 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 16 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x17 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 17 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x18 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 18 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x19 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 19 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x20 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 20 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x21 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 21 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x22 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 22 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x23 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 23 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x24 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 24 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x25 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 25 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x26 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 26 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x27 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 27 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x28 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 28 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x29 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 29 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x30 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 30 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x31 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 31 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x32 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 32 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x33 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 33 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x34 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 34 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x35 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 35 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x36 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 36 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x37 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 37 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x38 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 38 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x39 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 39 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x40 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 40 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x41 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 41 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x42 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 42 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x43 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 43 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x44 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 44 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x45 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 45 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x46 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 46 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x47 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 47 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x48 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 48 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x49 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 49 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x50 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 50 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x51 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 51 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem case9x52 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 52 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem excluded : run (norm (BitVec.ofNat 32 0xe8888880)) (9-2) = false := by
  apply partition_run (n := 6) (m := 53) (by decide)
  intro j
  fin_cases j
  · exact case9x0
  · exact case9x1
  · exact case9x2
  · exact case9x3
  · exact case9x4
  · exact case9x5
  · exact case9x6
  · exact case9x7
  · exact case9x8
  · exact case9x9
  · exact case9x10
  · exact case9x11
  · exact case9x12
  · exact case9x13
  · exact case9x14
  · exact case9x15
  · exact case9x16
  · exact case9x17
  · exact case9x18
  · exact case9x19
  · exact case9x20
  · exact case9x21
  · exact case9x22
  · exact case9x23
  · exact case9x24
  · exact case9x25
  · exact case9x26
  · exact case9x27
  · exact case9x28
  · exact case9x29
  · exact case9x30
  · exact case9x31
  · exact case9x32
  · exact case9x33
  · exact case9x34
  · exact case9x35
  · exact case9x36
  · exact case9x37
  · exact case9x38
  · exact case9x39
  · exact case9x40
  · exact case9x41
  · exact case9x42
  · exact case9x43
  · exact case9x44
  · exact case9x45
  · exact case9x46
  · exact case9x47
  · exact case9x48
  · exact case9x49
  · exact case9x50
  · exact case9x51
  · exact case9x52

end Five
def goalBits : BitVec 32 := 0xe8888880
def low (w : BitVec 32) : BitVec 32 :=
  (w &&& goalBits) ||| (if w.getLsbD 7 then ~~~goalBits else 0)
def high (w : BitVec 32) := w &&& ~~~goalBits
def packed (w : BitVec 32) := (high w) ++ (low w)
def enc (w : BitVec 32) : ℕ := (packed w).toNat
def dec (x : ℕ) : BitVec 32 :=
  (BitVec.ofNat 32 x &&& goalBits) ||| (BitVec.ofNat 32 (x >>> 32) &&& ~~~goalBits)
theorem lowAt (q : BitVec 32) {i : ℕ} (hi : i<32) :
    (low q).getLsbD i = if goalBits.getLsbD i then q.getLsbD i else q.getLsbD 7 := by
  cases h : q.getLsbD 7 <;> cases g : goalBits.getLsbD i <;> simp only [low,h,g,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,BitVec.getLsbD_xor,decide_eq_true hi] <;> simp [hi,g]
  exact (BitVec.getLsbD_eq_getElem hi) ▸ g
theorem highAt (q : BitVec 32) {i : ℕ} (hi : i<32) :
    (high q).getLsbD i = if goalBits.getLsbD i then false else q.getLsbD i := by
  cases g : goalBits.getLsbD i <;> simp only [high,g,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,BitVec.getLsbD_xor,decide_eq_true hi] <;> simp [hi,g]
theorem inverse (w : BitVec 32) : dec (enc w) = w := by
  unfold dec enc
  rw [← BitVec.toNat_ushiftRight]
  change ((packed w).setWidth 32 &&& goalBits) ||| (((packed w) >>> 32).setWidth 32 &&& ~~~goalBits) = w
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : ¬ i+32<32 := by omega
  cases g : goalBits.getLsbD i <;> simp only [packed,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_append,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,BitVec.getLsbD_xor, Nat.add_comm 32 i, Nat.add_sub_cancel,decide_eq_true hi, Bool.true_and,if_pos hi,if_neg hn,lowAt _ hi,highAt _ hi,g] <;> simp
theorem enc0 : enc 0 = 0 := by decide +kernel
def bin (d : ℕ) (a b : BitVec 32) : BitVec 32 :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
theorem encBin (d : ℕ) (a b : BitVec 32) (hd : d < 4) :
    enc (bin d a b) = combine d (enc a) (enc b) := by
  interval_cases d <;> simp only [enc,bin,combine,← BitVec.toNat_and,← BitVec.toNat_or,← BitVec.toNat_xor] <;> apply congrArg BitVec.toNat <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> by_cases h : i < 32
  all_goals have hh : i-32 < 32 := by omega
  all_goals cases g : goalBits.getLsbD i <;> cases gg : goalBits.getLsbD (i-32) <;>
    simp only [packed,BitVec.getLsbD_append,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,BitVec.getLsbD_xor,h,ite_true,ite_false,lowAt,highAt _ hh,g,gg,Bool.false_eq_true,reduceCtorEq] <;> try rfl
theorem inOps (d : ℕ) (a b : BitVec 32) (hd : d < 4) : bin d a b ∈ Five.ops a b := by
  have ha : a ^^^ (a &&& b) = a &&& ~~~b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    cases u : a.getLsbD i <;> cases v : b.getLsbD i <;> simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,BitVec.getLsbD_xor,decide_eq_true hi,u,v] <;> decide
  have hb : b ^^^ (a &&& b) = b &&& ~~~a := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    cases u : a.getLsbD i <;> cases v : b.getLsbD i <;> simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,BitVec.getLsbD_xor,decide_eq_true hi,u,v] <;> decide
  interval_cases d <;> simp [bin,Five.ops,ha,hb]
theorem packedGood (q : BitVec 32) (h : Good 32 (enc q)) : q=goalBits := by
  have hx : low q ^^^ high q = (0xffffffff : BitVec 32) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have e := h i hi
    change (packed q).getLsbD i ≠ (packed q).getLsbD (32+i) at e
    have hn : ¬32+i<32 := by omega
    simp only [packed,BitVec.getLsbD_append,if_pos hi,if_neg hn,Nat.add_sub_cancel_left] at e
    change ((low q ^^^ high q).getLsbD i) = (BitVec.allOnes 32).getLsbD i
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, decide_eq_true hi]
    revert e
    cases (low q).getLsbD i <;> cases (high q).getLsbD i <;> decide
  have sep (i : ℕ) (hi : i<32) : ((low q).getLsbD i ^^ (high q).getLsbD i) = true := by
    have e := congrArg (fun v : BitVec 32 => v.getLsbD i) hx
    change (low q ^^^ high q).getLsbD i = (BitVec.allOnes 32).getLsbD i at e
    simpa only [BitVec.getLsbD_xor,BitVec.getLsbD_allOnes,decide_eq_true hi] using e
  have anchor : q.getLsbD 7 = true := by
    have e := sep 7 (by decide)
    rw [lowAt _ (by decide),highAt _ (by decide),show goalBits.getLsbD 7 = true by decide] at e
    simpa only [ite_true,Bool.xor_false] using e
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := sep i hi
  rw [lowAt _ hi,highAt _ hi,anchor] at e
  cases g : goalBits.getLsbD i <;> cases v : q.getLsbD i <;> simp [g,v] at e ⊢

theorem sim {k S} (h : Live 32 k S) (back : ∀ x∈S, enc (dec x)=x) :
    Five.Trail goalBits (S.image dec) k := by
  induction k generalizing S with
  | zero =>
    obtain ⟨a,rfl,hg,_⟩ := h
    have ea := back a (Finset.mem_singleton_self a)
    rw [← ea] at hg
    simpa [packedGood _ hg] using (Five.Trail.done (t:=goalBits) 0)
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,hd,_,_,hab,hf,ht⟩ := h
    have ea := back a (by simp)
    have eb := back b (by simp)
    let z := combine d a b
    have ez : enc (bin d (dec a) (dec b)) = z := by rw [encBin _ _ _ hd,ea,eb]
    have dz : dec z = bin d (dec a) (dec b) := by rw [← ez,inverse]
    have backz : enc (dec z)=z := by rw [dz,ez]
    have eu (x) (hx : x ∈ U) : enc (dec x)=x := back x (by simp [hx])
    have tailProof := ih ht (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hu
      · exact backz
      · exact eu x hu)
    change Five.Trail goalBits ((insert z U).image dec) k at tailProof
    simp only [Finset.image_insert] at tailProof ⊢
    apply Five.Trail.step (c:=dec z) _ _ _ _ tailProof
    · intro e
      exact hab (ea.symm.trans ((congrArg enc e).trans eb))
    · intro hm
      apply hf
      rw [← Finset.image_insert,← Finset.image_insert] at hm
      obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp hm
      have eqx : x=z := (back x hx).symm.trans ((congrArg enc ex).trans (backz))
      rw [eqx] at hx; exact hx
    · intro e
      apply liveNonzero ht z (Finset.mem_insert_self _ _)
      calc
        z = enc (dec z) := (backz).symm
        _ = 0 := by rw [e,enc0]
    · rw [dz]
      exact inOps _ _ _ hd

theorem runOfTrail {t : Five.Q} {k : ℕ} {T : Finset Five.Q}
    (hs : T ⊆ Five.initial.toFinset) (trail : Five.Trail t T k) : Five.run t k = true := by
  let ws := Five.initial.filter (· ∈ T)
  have hw : ws.toFinset = T := by ext x; simp [ws]; exact fun a => List.mem_toFinset.mp (hs a)
  have nd : Five.initial.Nodup := by decide +kernel
  unfold Five.run
  apply List.any_eq_true.mpr
  exact ⟨ws, List.mem_sublists.mpr List.filter_sublist, Five.trail_walk trail ws hw (nd.filter _)⟩

theorem fixedBound : Wide 32 7 (Five.inputs.map enc) := by
  rintro ⟨k,S,le,live,sub⟩
  have inv (x) (hx : x ∈ S) : ∃ q∈Five.inputs, enc q=x := List.mem_map.mp (sub x hx)
  have back (x) (hx : x ∈ S) : enc (dec x) = x := by
    obtain ⟨q,_,rfl⟩ := inv x hx
    rw [inverse]
  have hs : S.image dec ⊆ Five.initial.toFinset := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨v,hv,rfl⟩ := inv x hx
    rw [inverse]
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ hv)
  have ok := runOfTrail hs (Five.trail_mono (sim live back) le)
  have bad : Five.run goalBits 7 = false := Five.excluded
  exact Bool.noConfusion (ok.symm.trans bad)


-- Setting f to true gives the certified five-input table in input order d,e,a,b,c.
def caseInputs : List ℕ := [73272492985767817639935, 53232700084793651529728, 50873652182900909015040, 27163445542305176485887, 37798608392304757571583, 74377272105330056101888]
def projectRows : Projection 38 32 := pick [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] rfl (by decide +kernel) (by decide)
theorem caseBound : Ban 38 8 caseInputs := viaCut projectRows fixedBound (by decide) (by decide +kernel) (by decide +kernel)
def graph (x : Fin 6 → Bool) := Nat.testBit (4269834240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0xdd93cf3cfff7bf9fb9e79f79e79f39e79ef9e79eb9e79e79e79e79e79
def negBits : ℕ := 0x5c91cb34e820827836ba6835b65834b24833ae3832aa2831a61e30a20
def sample (bank : ℕ) (i : Fin 38) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := caseInputs
def seeds : List Wire := [(false,73272492985767817639935),(false,53232700084793651529728),(false,50873652182900909015040),(false,27163445542305176485887),(false,37798608392304757571583),(true,74377272105330056101888)]
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 38, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (38+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 38, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 38, ∀ b∈inputs, b.testBit i.val≠b.testBit (38+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 38 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=graph) :
    ∃ k≤C.gates.countP counted, Live 38 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 38 out.2 := by
    intro i hi same
    let j : Fin 38 := ⟨i,hi⟩
    have diff : read i out=read (38+i) out := by simp [read,same]
    have p := ev i;have n := ev (38+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa only [show reps seeds = inputs from rfl] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def temoin : List Gate := [⟨.or, [0,1]⟩, ⟨.or, [6,2]⟩, ⟨.and, [0,1]⟩, ⟨.and, [8,2]⟩, ⟨.and, [3,4]⟩, ⟨.and, [4,5]⟩, ⟨.or, [3,11]⟩, ⟨.and, [7,10]⟩, ⟨.and, [9,12]⟩, ⟨.or, [13,14]⟩]
theorem upperMono : Monotone2 ⟨temoin,15⟩ := by simp [Monotone2, temoin]
theorem upperEq : ∀ x : Fin 6 → Bool, Circuit.eval ⟨temoin,15⟩ (List.ofFn x) = graph x := by decide +kernel
end PEqualNP.Outside.L_meta_12252
open PEqualNP.Outside.L_meta_12252 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_12252 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, fan, size, eq⟩

  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨k, small, live⟩ := trace C fan (funext eq)
    have lower : 9 ≤ k := by
      by_contra! h
      exact caseBound k (by omega) live
    have strict : C.gates.countP counted < C.gates.length := by
      apply List.countP_lt_length_iff.mpr
      obtain ⟨g,mem,op⟩ := hn
      exact ⟨g,mem,by simp [counted,op]⟩
    change C.gates.length ≤ s at size
    exact ⟨⟨temoin,15⟩,upperMono,by change 10 ≤ s; omega,upperEq⟩
  · refine ⟨C, ?_, size, eq⟩
    intro g mem
    obtain ⟨op, cap⟩ := fan g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun e => (hn ⟨g,mem,e⟩).elim)), cap⟩
