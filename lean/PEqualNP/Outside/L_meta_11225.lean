import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11225

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
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

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
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
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
def projection (m q r : ℕ) (hr : r < m) : Projection m m := by
  refine ⟨slice m q r, ?_, slice_hom m q r, ?_, by omega⟩
  · simp [slice, half]
  · intro a ga i hi
    rw [slice_lo _ _ _ hi, slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi

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
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs, p, projection, Projection.toFun, ←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]

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

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
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


theorem viaDirect {m f v} (nd : v.Nodup) (test : search m f v = false) : Ban m f v := by
  intro k le run
  have yes := complete m f run le v rfl nd
  simp_all

def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def posBits : ℕ := 0x44e1c3462c386c51a142850a1428509526448912244891221c3850a142850a14270e193154a142850a1428508d122448912244890a142850a14284d1a324c912244891224488912244891224458b12244891224489
def negBits : ℕ := 0x40c0c3060c104c41c1060303040503150704180c0c0a100e083c1060303028182606183015820b04060508060f0416080c0a060b0416080c0a0604c0a300f041606080a060b041606080a0604503c1058181420181
def sample (bank : ℕ) (i : Fin 97) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0xa82a0e84041a1218a121a860d0040300100403fcc03ffff,0x702a0e1058383283836141000803ff2807fc037fc0300,0x1000000000000000000000000,0x4150701890e060670a0a4382200ffc00cff8000380003ff,0x84380c031e28141451c1c060c3ff00000f0000003ffffc00,0x1f120481216b0585805050140fc0000000fffffffc0000000,0x37bc0f05c00c0606006060181fffffffff000000000000000]
def seeds : List Wire := inputs.map (fun a => (false,a))
theorem listed : ∀ i : Fin 97, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (97+i.val))=List.ofFn (sample negBits i) := by decide +kernel
theorem labels : ∀ i : Fin 97, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 97, ∀ b∈inputs, b.testBit i.val≠b.testBit (97+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 97 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 97 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 97 out.2 := by
    intro i hi same
    let j : Fin 97 := ⟨i,hi⟩
    have diff : read i out=read (97+i) out := by simp [read,same]
    have p := ev i;have n := ev (97+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj0 : Projection 96 96 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj1 : Projection 96 96 := pick [30,36,34,37,35,33,31,32,90,91,10,16,17,13,15,14,11,12,85,86,87,82,84,83,80,81,88,56,95,94,0,6,7,5,2,4,1,3,75,76,77,74,71,73,70,72,78,53,51,54,52,48,50,47,49,93,27,89,59,58,65,66,67,64,63,60,61,62,69,68,44,42,45,43,41,38,39,40,46,92,24,25,21,23,22,18,19,20,26,57,8,9,79,55,29,28] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj2 : Projection 96 96 := pick [60,61,65,66,67,64,62,63,68,69,38,39,44,42,45,43,40,41,30,31,36,34,37,35,32,33,46,92,90,91,18,19,24,25,21,23,20,22,10,11,16,17,13,15,12,14,26,80,85,86,87,82,84,81,83,88,57,56,95,94,0,1,6,7,5,2,3,4,8,9,70,75,76,77,74,71,72,73,79,78,47,53,51,54,52,48,49,50,55,93,28,29,27,89,59,58] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj3 : Projection 96 96 := pick [18,20,21,22,23,25,19,24,28,29,38,40,41,42,43,45,39,44,48,49,50,51,52,54,47,53,55,57,58,59,60,62,63,64,65,67,61,66,71,72,73,74,75,77,70,76,79,81,82,83,84,85,87,80,86,89,92,93,94,95,2,3,4,5,7,0,1,6,9,8,12,13,14,15,17,10,11,16,26,27,32,33,34,35,37,30,31,36,46,56,68,69,78,88,91,90] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj4 : Projection 96 96 := pick [2,3,0,1,6,7,4,5,9,8,71,72,70,75,76,77,73,74,60,62,61,65,66,67,63,64,79,78,68,69,48,49,47,53,51,54,50,52,38,40,39,44,42,45,41,43,55,32,30,31,36,34,37,33,35,46,93,92,90,91,18,20,19,24,25,21,22,23,28,29,12,10,11,16,17,13,14,15,27,26,81,80,85,86,87,82,83,84,89,88,58,59,57,56,95,94] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj5 : Projection 96 96 := pick [48,50,51,52,54,53,49,47,58,59,71,73,74,75,77,76,72,70,82,83,84,85,87,86,81,80,89,93,94,95,2,4,5,7,0,6,3,1,13,14,15,17,10,16,12,11,27,33,34,35,37,30,36,32,31,56,78,88,91,90,21,22,23,25,24,18,20,19,29,28,41,42,43,45,44,38,40,39,55,57,63,64,65,67,66,60,62,61,79,92,9,8,26,46,69,68] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj6 : Projection 96 96 := pick [21,22,18,20,19,24,23,25,29,28,13,14,12,10,11,16,15,17,2,4,3,0,1,6,5,7,27,26,9,8,82,83,81,80,85,86,84,87,71,73,72,70,75,76,74,77,89,63,60,62,61,65,66,64,67,79,88,78,68,69,48,50,49,47,53,51,52,54,58,59,41,38,40,39,44,42,43,45,57,55,33,32,30,31,36,34,35,37,56,46,94,95,93,92,90,91] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj7 : Projection 96 96 := pick [82,84,85,87,86,80,83,81,94,95,13,15,17,10,16,11,14,12,34,35,37,30,36,31,33,32,56,88,91,90,21,23,25,24,18,19,22,20,42,43,45,44,38,39,41,40,57,64,65,67,66,60,61,63,62,92,26,46,69,68,51,52,54,53,47,48,50,49,59,58,74,75,77,76,70,71,73,72,89,93,5,7,0,6,1,2,4,3,27,78,29,28,55,79,8,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj8 : Projection 96 96 := pick [51,52,48,50,49,47,54,53,59,58,42,43,41,38,40,39,45,44,21,23,22,18,20,19,25,24,57,55,29,28,34,35,33,32,30,31,37,36,13,15,14,12,10,11,17,16,56,5,2,4,3,0,1,7,6,27,46,26,9,8,82,84,83,81,80,85,87,86,94,95,74,71,73,72,70,75,77,76,93,89,64,63,60,62,61,65,67,66,92,79,91,90,88,78,68,69] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj9 : Projection 96 96 := pick [34,37,30,36,31,32,35,33,91,90,42,45,44,38,39,40,43,41,65,67,66,60,61,62,64,63,92,46,69,68,51,54,53,47,48,49,52,50,75,77,76,70,71,72,74,73,93,7,0,6,1,2,3,5,4,78,55,79,8,9,85,87,86,80,81,82,84,83,95,94,17,10,16,11,12,13,15,14,56,88,25,24,18,19,20,21,23,22,57,26,59,58,89,27,28,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj10 : Projection 96 96 := pick [65,66,60,61,62,63,67,64,69,68,75,76,70,71,72,73,77,74,0,6,1,2,3,4,7,5,78,79,8,9,85,86,80,81,82,83,87,84,10,16,11,12,13,14,17,15,88,24,18,19,20,21,22,25,23,26,89,27,28,29,30,36,31,32,33,34,37,35,90,91,44,38,39,40,41,42,45,43,92,46,53,47,48,49,50,51,54,52,93,55,95,94,56,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj11 : Projection 96 96 := pick [85,87,82,84,83,81,86,80,95,94,75,77,74,71,73,72,76,70,51,54,52,48,50,49,53,47,93,89,59,58,65,67,64,63,60,62,66,61,42,45,43,41,38,40,44,39,92,25,21,23,22,18,20,24,19,57,79,55,29,28,34,37,35,33,32,30,36,31,91,90,17,13,15,14,12,10,16,11,88,56,7,5,2,4,3,0,6,1,78,27,69,68,46,26,9,8] rfl (by decide +kernel) (by decide)
def valeur0 : ℕ := 0x100503000c0c0840c09021000003ff2007fc007fc0000
def valeur1 : ℕ := 0x281004082010110101208000080000080000030000300
def valeur2 : ℕ := 0x20a8380c48703033850521c2200ffc00cff8000380003ff
def valeur3 : ℕ := 0x54150742020d090c5090d430d0040300100403fcc03ffff
def valeur4 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000f0000003ffffc00
def valeur5 : ℕ := 0xbde0782e00603030030300c0fffffffff000000000000000
def valeur6 : ℕ := 0xf89024090b582c2c028280a0fc0000000fffffffc0000000
def etat0 : List ℕ := [valeur0,valeur1,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne12 : Ban 96 6 etat0 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur7 : ℕ := 0x381507082c1c1941c1b0a1000803ff2807fc037fc0300
def etat1 : List ℕ := [valeur0,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne13 : Ban 96 6 etat1 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur8 : ℕ := 0x2080280840502022840401422007fc00c7f8000080000ff
def etat2 : List ℕ := [valeur1,valeur7,valeur8,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne14 : Ban 96 6 etat2 := viaDirect (by decide +kernel) (by decide +kernel)
def etat3 : List ℕ := [valeur7,valeur8,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne15 : Ban 96 6 etat3 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur9 : ℕ := 0x300
def etat4 : List ℕ := [valeur9,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne16 : Ban 96 6 etat4 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur10 : ℕ := 0x543d17460a2d191d5191f4b0d00c0300180403ffc03ffff
def etat5 : List ℕ := [valeur7,valeur2,valeur3,valeur10,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne17 : Ban 96 6 etat5 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur11 : ℕ := 0x281004082010110101208000080000080000030000000
def etat6 : List ℕ := [valeur11,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne18 : Ban 96 6 etat6 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur12 : ℕ := 0x54150742020d090c5090d430d0040300100403fcc03fcff
def etat7 : List ℕ := [valeur7,valeur2,valeur12,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne19 : Ban 96 6 etat7 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur13 : ℕ := 0x30000000
def etat8 : List ℕ := [valeur13,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne20 : Ban 96 6 etat8 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur14 : ℕ := 0x421e8701cf960b0b38f0f238c3ff80000f8000003fffff00
def etat9 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur14,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne21 : Ban 96 6 etat9 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur15 : ℕ := 0x281004082010110101208000080000080000000000300
def etat10 : List ℕ := [valeur15,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne22 : Ban 96 6 etat10 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur16 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000f0000000ffffc00
def etat11 : List ℕ := [valeur7,valeur2,valeur3,valeur16,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne23 : Ban 96 6 etat11 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur17 : ℕ := 0x381507082c1c1941c1b0a1000803ff2807fc03ffc0300
def etat12 : List ℕ := [valeur17,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne24 : Ban 96 5 etat12 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur18 : ℕ := 0x20a8380c48703033850521c2200ffc00cff8000300003ff
def etat13 : List ℕ := [valeur7,valeur18,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne25 : Ban 96 5 etat13 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur19 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000f00000037fffc00
def etat14 : List ℕ := [valeur7,valeur2,valeur3,valeur19,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne26 : Ban 96 5 etat14 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur20 : ℕ := 0xbde0782e00603030030300c0fffffffff000000008000000
def etat15 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur20,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne27 : Ban 96 5 etat15 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur21 : ℕ := 0xf89024090b582c2c028280a0fc0000000fffffffc8000000
def etat16 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur21]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne28 : Ban 96 5 etat16 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur22 : ℕ := 0x8000000
def etat17 : List ℕ := [valeur22,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne29 : Ban 96 6 etat17 := viaBranch (ws := [etat12,etat13,etat14,etat15,etat16]) (consBan borne24 (consBan borne25 (consBan borne26 (consBan borne27 (consBan borne28 (nilBan 96 5)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur23 : ℕ := 0x80000000000000000000
def etat18 : List ℕ := [valeur23,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne30 : Ban 96 6 etat18 := viaPerm proj10 proj3 borne29 (by decide +kernel) (by decide +kernel)
def valeur24 : ℕ := 0xbde2f92e40e23131131312c8fffffffff080000030000300
def etat19 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur24,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne31 : Ban 96 6 etat19 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur25 : ℕ := 0x281004082010110101208000000000080000030000300
def etat20 : List ℕ := [valeur25,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne32 : Ban 96 6 etat20 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur26 : ℕ := 0xbde0782e00603030030300c0ffff7ffff000000000000000
def etat21 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur26,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne33 : Ban 96 6 etat21 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur27 : ℕ := 0x80000000000000
def etat22 : List ℕ := [valeur27,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne34 : Ban 96 6 etat22 := viaPerm proj8 proj8 borne29 (by decide +kernel) (by decide +kernel)
def valeur28 : ℕ := 0xf892a5094bda2d2d129292a8fc0080000ffffffff0000300
def etat23 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur28]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne35 : Ban 96 6 etat23 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur29 : ℕ := 0x281004082010110101208000080000000000030000300
def etat24 : List ℕ := [valeur29,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne36 : Ban 96 6 etat24 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur30 : ℕ := 0xf89024090b582c2c028280a0fc0000000f7fffffc0000000
def etat25 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur30,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne37 : Ban 96 6 etat25 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur31 : ℕ := 0x20b83d0f487c3c3bc5c5b1e3200fffffeffffc03ffc03ff
def etat26 : List ℕ := [valeur1,valeur7,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne38 : Ban 96 6 etat26 := viaDirect (by decide +kernel) (by decide +kernel)
def etat27 : List ℕ := [valeur1,valeur2,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne39 : Ban 96 6 etat27 := viaDirect (by decide +kernel) (by decide +kernel)
def etat28 : List ℕ := [valeur1,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne40 : Ban 96 7 etat28 := viaBranch (ws := [etat0,etat1,etat2,etat3,etat4,etat5,etat6,etat7,etat8,etat9,etat10,etat11,etat18,etat19,etat20,etat21,etat22,etat23,etat24,etat25,etat26,etat27]) (consBan borne12 (consBan borne13 (consBan borne14 (consBan borne15 (consBan borne16 (consBan borne17 (consBan borne18 (consBan borne19 (consBan borne20 (consBan borne21 (consBan borne22 (consBan borne23 (consBan borne30 (consBan borne31 (consBan borne32 (consBan borne33 (consBan borne34 (consBan borne35 (consBan borne36 (consBan borne37 (consBan borne38 (consBan borne39 (nilBan 96 6))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur32 : ℕ := 0x543d17470a2d1d1d51d1f4b1d00c03ff3807fffffffffff
def etat29 : List ℕ := [valeur2,valeur31,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne41 : Ban 96 6 etat29 := viaDirect (by decide +kernel) (by decide +kernel)
def etat30 : List ℕ := [valeur0,valeur2,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne42 : Ban 96 6 etat30 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur33 : ℕ := 0x100502000c08084080902000000300000400004000300
def etat31 : List ℕ := [valeur33,valeur7,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne43 : Ban 96 6 etat31 := viaDirect (by decide +kernel) (by decide +kernel)
def etat32 : List ℕ := [valeur33,valeur2,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne44 : Ban 96 6 etat32 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur34 : ℕ := 0x2810050820141101412081000800ff2803fc033fc0000
def etat33 : List ℕ := [valeur34,valeur7,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne45 : Ban 96 6 etat33 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur35 : ℕ := 0x540502400201010410104410d0040000100003fc803fcff
def etat34 : List ℕ := [valeur2,valeur35,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne46 : Ban 96 6 etat34 := viaDirect (by decide +kernel) (by decide +kernel)
def etat35 : List ℕ := [valeur7,valeur2,valeur35,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne47 : Ban 96 6 etat35 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur36 : ℕ := 0x421f8751ff96cbcbbcfcfb3ad3ff803fff807fc03fffff00
def etat36 : List ℕ := [valeur2,valeur3,valeur32,valeur4,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne48 : Ban 96 6 etat36 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur37 : ℕ := 0x381507082c1c1941c1b0a1000803ff0807fc000000300
def etat37 : List ℕ := [valeur37,valeur2,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne49 : Ban 96 6 etat37 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur38 : ℕ := 0x20a8380c48703033850521c2200ffc00cff8000080003ff
def valeur39 : ℕ := 0x421e8781cf970b0b38f0f23ce3ffffc00fff80003fffffff
def etat38 : List ℕ := [valeur7,valeur38,valeur3,valeur39,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne50 : Ban 96 5 etat38 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur40 : ℕ := 0x54150742020d090c5090d430d0040300300403fffffffff
def etat39 : List ℕ := [valeur7,valeur2,valeur40,valeur39,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne51 : Ban 96 5 etat39 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur41 : ℕ := 0xbde0782e00603030030300c0fffffffff200000037fc0000
def etat40 : List ℕ := [valeur7,valeur2,valeur3,valeur39,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne52 : Ban 96 5 etat40 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur42 : ℕ := 0xf89024090b582c2c028280a0fc0000000ffffffff7fc0000
def etat41 : List ℕ := [valeur7,valeur2,valeur3,valeur39,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne53 : Ban 96 5 etat41 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur43 : ℕ := 0x200000037fc0000
def etat42 : List ℕ := [valeur43,valeur31,valeur3,valeur39,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne54 : Ban 96 5 etat42 := viaDirect (by decide +kernel) (by decide +kernel)
def etat43 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur39,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne55 : Ban 96 6 etat43 := viaBranch (ws := [etat38,etat39,etat40,etat41,etat42]) (consBan borne50 (consBan borne51 (consBan borne52 (consBan borne53 (consBan borne54 (nilBan 96 5)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur44 : ℕ := 0x1000803ff000000000000000
def etat44 : List ℕ := [valeur44,valeur2,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne56 : Ban 96 6 etat44 := viaPerm proj9 proj5 borne55 (by decide +kernel) (by decide +kernel)
def valeur45 : ℕ := 0xbde0782e00603030030300c0efff7fc00000000000000000
def etat45 : List ℕ := [valeur2,valeur3,valeur32,valeur4,valeur45,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne57 : Ban 96 6 etat45 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur46 : ℕ := 0xf893a5597bdaeded969e9baafc00803ffffffffff7fc0300
def etat46 : List ℕ := [valeur2,valeur3,valeur32,valeur4,valeur5,valeur6,valeur46]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne58 : Ban 96 6 etat46 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur47 : ℕ := 0x381507082c1c1941c1b0a0000803ff000000037fc0300
def etat47 : List ℕ := [valeur47,valeur2,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne59 : Ban 96 6 etat47 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur48 : ℕ := 0x400000000000080003ff
def etat48 : List ℕ := [valeur48,valeur7,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne60 : Ban 96 6 etat48 := viaPerm proj6 proj6 borne55 (by decide +kernel) (by decide +kernel)
def valeur49 : ℕ := 0x20a8380c48703033850521c2200bfc00cff800030000000
def etat49 : List ℕ := [valeur7,valeur49,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne61 : Ban 96 6 etat49 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur50 : ℕ := 0x2810040820101101012080000c00000800000380003ff
def etat50 : List ℕ := [valeur50,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne62 : Ban 96 6 etat50 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur51 : ℕ := 0x74bd3f4f4a7d3d3fd5d5f5f3f00ffffffffffffffffffff
def etat51 : List ℕ := [valeur7,valeur2,valeur3,valeur51,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne63 : Ban 96 6 etat51 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur52 : ℕ := 0x2080280840502022840401422003fc00c7f800000000000
def etat52 : List ℕ := [valeur7,valeur52,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne64 : Ban 96 6 etat52 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur53 : ℕ := 0x54150743020d0d0c50d0d431d00003ff3007fffc7fffc00
def etat53 : List ℕ := [valeur7,valeur2,valeur3,valeur53,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne65 : Ban 96 6 etat53 := viaDirect (by decide +kernel) (by decide +kernel)
def etat54 : List ℕ := [valeur34,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne66 : Ban 96 6 etat54 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur54 : ℕ := 0x475d5675af34da9aede9ed73cfff40300f00403fffffffff
def etat55 : List ℕ := [valeur7,valeur2,valeur32,valeur4,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne67 : Ban 96 6 etat55 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur55 : ℕ := 0x54150742020d090c5090d430c0040300000403fc00003ff
def etat56 : List ℕ := [valeur7,valeur2,valeur55,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne68 : Ban 96 6 etat56 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur56 : ℕ := 0xbde1787e2060f0b0c70b0dc3fffffffff100403fcc03ffff
def etat57 : List ℕ := [valeur7,valeur2,valeur32,valeur4,valeur5,valeur56,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne69 : Ban 96 6 etat57 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur57 : ℕ := 0x100502000c080c4080d03000000000100403fcc03ffff
def etat58 : List ℕ := [valeur57,valeur7,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne70 : Ban 96 6 etat58 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur58 : ℕ := 0xfdd1747d2b78fcbcc78b8de3fd0040300fffffffcc03ffff
def etat59 : List ℕ := [valeur7,valeur2,valeur32,valeur4,valeur5,valeur6,valeur58]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne71 : Ban 96 6 etat59 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur59 : ℕ := 0x54150742020d090c5090d4301004030000000000c03ffff
def etat60 : List ℕ := [valeur7,valeur2,valeur59,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne72 : Ban 96 6 etat60 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur60 : ℕ := 0x381507082c1c1941c1b0a3200fffff2807fc03ffc03ff
def etat61 : List ℕ := [valeur60,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne73 : Ban 96 5 etat61 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur61 : ℕ := 0x381507082c1c1941c1b0a1000003ff2807fc037fc0000
def etat62 : List ℕ := [valeur61,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne74 : Ban 96 5 etat62 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur62 : ℕ := 0x54150742020d090c5090d432f00fff00100403fcc03ffff
def etat63 : List ℕ := [valeur7,valeur2,valeur62,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne75 : Ban 96 5 etat63 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur63 : ℕ := 0x421c06018f140a0a28e0e030e3ffffc00f0000003fffffff
def etat64 : List ℕ := [valeur7,valeur2,valeur3,valeur63,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne76 : Ban 96 5 etat64 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur64 : ℕ := 0x421c06018f140a0a28e0e030c1ff00000f00000037fffc00
def etat65 : List ℕ := [valeur7,valeur2,valeur3,valeur64,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne77 : Ban 96 5 etat65 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur65 : ℕ := 0xbde0782e00603030030300c0fffffffff0000000080003ff
def etat66 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur65,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne78 : Ban 96 5 etat66 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur66 : ℕ := 0xf89024090b582c2c028280a0fe00ffc00fffffffc80003ff
def etat67 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur66]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne79 : Ban 96 5 etat67 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur67 : ℕ := 0xf89024090b582c2c028280a0dc0000000fffffffc0000000
def etat68 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur67]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne80 : Ban 96 5 etat68 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur68 : ℕ := 0x2200ffc000000000080003ff
def etat69 : List ℕ := [valeur68,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne81 : Ban 96 6 etat69 := viaBranch (ws := [etat61,etat62,etat63,etat64,etat65,etat66,etat67,etat68]) (consBan borne73 (consBan borne74 (consBan borne75 (consBan borne76 (consBan borne77 (consBan borne78 (consBan borne79 (consBan borne80 (nilBan 96 5))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur69 : ℕ := 0x1000000030000003ffffc00
def etat70 : List ℕ := [valeur69,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne82 : Ban 96 6 etat70 := viaPerm proj3 proj10 borne81 (by decide +kernel) (by decide +kernel)
def valeur70 : ℕ := 0x475fd775ffb6dbdbfdfdff7bdfffc03fff807fffffffffff
def etat71 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur70,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne83 : Ban 96 6 etat71 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur71 : ℕ := 0x543d17470a2d1d1d51d1f4b1c00c03ff0807fffc00003ff
def etat72 : List ℕ := [valeur7,valeur2,valeur3,valeur71,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne84 : Ban 96 6 etat72 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur72 : ℕ := 0x421c06018f140a0a28e0e030c2ff00000c00000000000000
def etat73 : List ℕ := [valeur7,valeur2,valeur3,valeur72,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne85 : Ban 96 6 etat73 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur73 : ℕ := 0x540502400201010010100401d00c03ff000000000000000
def etat74 : List ℕ := [valeur7,valeur2,valeur73,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne86 : Ban 96 6 etat74 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur74 : ℕ := 0xbde3f97e70e2f1f1d71f1fcbfffffffff3807fffffffffff
def etat75 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur74,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne87 : Ban 96 6 etat75 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur75 : ℕ := 0x381507082c1c1d41c1f0b0000000003807fffffffffff
def etat76 : List ℕ := [valeur7,valeur75,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne88 : Ban 96 6 etat76 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur76 : ℕ := 0xb8a0280a0040202002020080e2ff3fc00000000000000000
def etat77 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur76,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne89 : Ban 96 6 etat77 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur77 : ℕ := 0x1c00000003807fffc0000000
def etat78 : List ℕ := [valeur77,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne90 : Ban 96 6 etat78 := viaPerm proj1 proj1 borne81 (by decide +kernel) (by decide +kernel)
def valeur78 : ℕ := 0xfdd3f57d7bfafdfdd79f9febfd00c03fffffffffffffffff
def etat79 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur78]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne91 : Ban 96 6 etat79 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur79 : ℕ := 0x543d17470a2d1d1d51d1f4b0100c03ff00000003fffffff
def etat80 : List ℕ := [valeur7,valeur2,valeur3,valeur79,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne92 : Ban 96 6 etat80 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur80 : ℕ := 0xf89024090b582c2c028280a0e00000000c7f800000000000
def etat81 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur80,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne93 : Ban 96 6 etat81 := viaDirect (by decide +kernel) (by decide +kernel)
def etat82 : List ℕ := [valeur7,valeur2,valeur3,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne94 : Ban 96 7 etat82 := viaBranch (ws := [etat29,etat30,etat31,etat32,etat33,etat34,etat35,etat36,etat37,etat44,etat45,etat46,etat47,etat48,etat49,etat50,etat51,etat52,etat53,etat54,etat55,etat56,etat57,etat58,etat59,etat60,etat70,etat71,etat72,etat73,etat74,etat75,etat76,etat77,etat78,etat79,etat80,etat81]) (consBan borne41 (consBan borne42 (consBan borne43 (consBan borne44 (consBan borne45 (consBan borne46 (consBan borne47 (consBan borne48 (consBan borne49 (consBan borne56 (consBan borne57 (consBan borne58 (consBan borne59 (consBan borne60 (consBan borne61 (consBan borne62 (consBan borne63 (consBan borne64 (consBan borne65 (consBan borne66 (consBan borne67 (consBan borne68 (consBan borne69 (consBan borne70 (consBan borne71 (consBan borne72 (consBan borne82 (consBan borne83 (consBan borne84 (consBan borne85 (consBan borne86 (consBan borne87 (consBan borne88 (consBan borne89 (consBan borne90 (consBan borne91 (consBan borne92 (consBan borne93 (nilBan 96 6))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat83 : List ℕ := [valeur7,valeur2,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne95 : Ban 96 7 etat83 := viaPerm proj3 proj10 borne94 (by decide +kernel) (by decide +kernel)
def etat84 : List ℕ := [valeur33,valeur34,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne96 : Ban 96 6 etat84 := viaDirect (by decide +kernel) (by decide +kernel)
def etat85 : List ℕ := [valeur33,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne97 : Ban 96 6 etat85 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur81 : ℕ := 0x20a8380d48703433854521c3200ffcffeffbfc03bfc03ff
def etat86 : List ℕ := [valeur7,valeur81,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne98 : Ban 96 6 etat86 := viaDirect (by decide +kernel) (by decide +kernel)
def etat87 : List ℕ := [valeur34,valeur7,valeur81,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne99 : Ban 96 6 etat87 := viaDirect (by decide +kernel) (by decide +kernel)
def etat88 : List ℕ := [valeur7,valeur2,valeur81,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne100 : Ban 96 6 etat88 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur82 : ℕ := 0x10000040000400001000000ff2003fc003fc0000
def etat89 : List ℕ := [valeur82,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne101 : Ban 96 6 etat89 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur83 : ℕ := 0x2810050820141101412081000803ff2803fc033fc0000
def valeur84 : ℕ := 0x20a8380d48703433854521c3200fffffeffbfc03bfc03ff
def etat90 : List ℕ := [valeur83,valeur84,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne102 : Ban 96 5 etat90 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur85 : ℕ := 0x2080280840502022840401422007fc00c7f8000080003ff
def etat91 : List ℕ := [valeur83,valeur85,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne103 : Ban 96 5 etat91 := viaDirect (by decide +kernel) (by decide +kernel)
def etat92 : List ℕ := [valeur83,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne104 : Ban 96 5 etat92 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur86 : ℕ := 0x54150742020d090c5090d430d0040000100403fcc03ffff
def etat93 : List ℕ := [valeur83,valeur2,valeur86,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne105 : Ban 96 5 etat93 := viaDirect (by decide +kernel) (by decide +kernel)
def etat94 : List ℕ := [valeur83,valeur2,valeur3,valeur4,valeur56,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne106 : Ban 96 5 etat94 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur87 : ℕ := 0xb8a0280a0040202002020080f2ffbfcff000000000000000
def etat95 : List ℕ := [valeur83,valeur2,valeur3,valeur4,valeur87,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne107 : Ban 96 5 etat95 := viaDirect (by decide +kernel) (by decide +kernel)
def etat96 : List ℕ := [valeur83,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne108 : Ban 96 6 etat96 := viaBranch (ws := [etat90,etat91,etat92,etat93,etat94,etat95]) (consBan borne102 (consBan borne103 (consBan borne104 (consBan borne105 (consBan borne106 (consBan borne107 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat97 : List ℕ := [valeur7,valeur85,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne109 : Ban 96 6 etat97 := viaPerm proj3 proj10 borne108 (by decide +kernel) (by decide +kernel)
def etat98 : List ℕ := [valeur34,valeur7,valeur85,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne110 : Ban 96 6 etat98 := viaDirect (by decide +kernel) (by decide +kernel)
def etat99 : List ℕ := [valeur7,valeur84,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne111 : Ban 96 5 etat99 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne112 : Ban 96 5 etat97 := viaDirect (by decide +kernel) (by decide +kernel)
def etat100 : List ℕ := [valeur7,valeur2,valeur86,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne113 : Ban 96 5 etat100 := viaDirect (by decide +kernel) (by decide +kernel)
def etat101 : List ℕ := [valeur83,valeur2,valeur35,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne114 : Ban 96 5 etat101 := viaDirect (by decide +kernel) (by decide +kernel)
def etat102 : List ℕ := [valeur83,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne115 : Ban 96 6 etat102 := viaBranch (ws := [etat99,etat97,etat100,etat92,etat101]) (consBan borne111 (consBan borne112 (consBan borne113 (consBan borne104 (consBan borne114 (nilBan 96 5)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat103 : List ℕ := [valeur7,valeur85,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne116 : Ban 96 6 etat103 := viaPerm proj3 proj10 borne115 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne117 : Ban 96 6 etat82 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur88 : ℕ := 0x381507082c1c1941c1b0a1000803ff2807fc03ffc03ff
def etat104 : List ℕ := [valeur88,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne118 : Ban 96 5 etat104 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur89 : ℕ := 0x381507082c1c1941c1b0a1000803ff2807fc037fc0000
def etat105 : List ℕ := [valeur89,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne119 : Ban 96 5 etat105 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur90 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000f0000003fffffff
def etat106 : List ℕ := [valeur7,valeur2,valeur3,valeur90,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne120 : Ban 96 5 etat106 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur91 : ℕ := 0xf89024090b582c2c028280a0fc0000000fffffffc80003ff
def etat107 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur91]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne121 : Ban 96 5 etat107 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur92 : ℕ := 0x80003ff
def etat108 : List ℕ := [valeur92,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne122 : Ban 96 6 etat108 := viaBranch (ws := [etat104,etat105,etat106,etat14,etat66,etat107]) (consBan borne118 (consBan borne119 (consBan borne120 (consBan borne26 (consBan borne78 (consBan borne121 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur93 : ℕ := 0x200000033fc0000
def etat109 : List ℕ := [valeur93,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne123 : Ban 96 6 etat109 := viaPerm proj3 proj10 borne122 (by decide +kernel) (by decide +kernel)
def valeur94 : ℕ := 0x421e8701df960b4b38f4f238d3ff800fff803fc03ffffc00
def etat110 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur94,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne124 : Ban 96 6 etat110 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur95 : ℕ := 0x2810050820141101412081000800ff0803fc000000000
def etat111 : List ℕ := [valeur95,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne125 : Ban 96 6 etat111 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur96 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000d0000000c03fc00
def etat112 : List ℕ := [valeur7,valeur2,valeur3,valeur96,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne126 : Ban 96 6 etat112 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur97 : ℕ := 0x381507082c1c1941c1b0a13ff803ff2807fc037fc0300
def etat113 : List ℕ := [valeur97,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne127 : Ban 96 5 etat113 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur98 : ℕ := 0x20a8380c48703033850521c23ffffc00cff8000380003ff
def etat114 : List ℕ := [valeur7,valeur98,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne128 : Ban 96 5 etat114 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur99 : ℕ := 0x20a8380c48703033850521c2000ffc00cff8000380003ff
def etat115 : List ℕ := [valeur7,valeur99,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne129 : Ban 96 5 etat115 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur100 : ℕ := 0x54150742020d090c5090d430fff40300100403fcc03ffff
def etat116 : List ℕ := [valeur7,valeur2,valeur100,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne130 : Ban 96 5 etat116 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur101 : ℕ := 0x54150742020d090c5090d430c0040300100403fcc03ffff
def etat117 : List ℕ := [valeur7,valeur2,valeur101,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne131 : Ban 96 5 etat117 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur102 : ℕ := 0xf89024090b582c2c028280a0ffff00000fffffffc0000000
def etat118 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur102]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne132 : Ban 96 5 etat118 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur103 : ℕ := 0x3ff00000000000000000000
def etat119 : List ℕ := [valeur103,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne133 : Ban 96 6 etat119 := viaBranch (ws := [etat113,etat114,etat115,etat116,etat117,etat118]) (consBan borne127 (consBan borne128 (consBan borne129 (consBan borne130 (consBan borne131 (consBan borne132 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur104 : ℕ := 0x1000800ff000000000000000
def etat120 : List ℕ := [valeur104,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne134 : Ban 96 6 etat120 := viaPerm proj5 proj9 borne133 (by decide +kernel) (by decide +kernel)
def valeur105 : ℕ := 0xbde2f92e50e23171131712c8fffffffff2803fc033fc0000
def etat121 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur105,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne135 : Ban 96 6 etat121 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur106 : ℕ := 0x2810050820141101412080000000002803fc033fc0000
def etat122 : List ℕ := [valeur106,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne136 : Ban 96 6 etat122 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur107 : ℕ := 0xbde0782e00603030030300c0efff7ff00000000000000000
def etat123 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur107,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne137 : Ban 96 6 etat123 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur108 : ℕ := 0x381507082c1c1941c1b0a3200fffff2807fc037fc0300
def etat124 : List ℕ := [valeur108,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne138 : Ban 96 5 etat124 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur109 : ℕ := 0x54150742020d090c5090d432f007ff00100403fcc03ffff
def etat125 : List ℕ := [valeur7,valeur2,valeur109,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne139 : Ban 96 5 etat125 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur110 : ℕ := 0x54150742020d090c5090d430d0000300100403fcc03ffff
def etat126 : List ℕ := [valeur7,valeur2,valeur110,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne140 : Ban 96 5 etat126 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur111 : ℕ := 0x421c06018f140a0a28e0e030e3ff7fc00f0000003ffffc00
def etat127 : List ℕ := [valeur7,valeur2,valeur3,valeur111,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne141 : Ban 96 5 etat127 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur112 : ℕ := 0x421c06018f140a0a28e0e030c1ff00000f0000003ffffc00
def etat128 : List ℕ := [valeur7,valeur2,valeur3,valeur112,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne142 : Ban 96 5 etat128 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur113 : ℕ := 0xf89024090b582c2c028280a0fe007fc00fffffffc0000000
def etat129 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur113]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne143 : Ban 96 5 etat129 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur114 : ℕ := 0x22007fc00000000000000000
def etat130 : List ℕ := [valeur114,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne144 : Ban 96 6 etat130 := viaBranch (ws := [etat124,etat125,etat126,etat127,etat128,etat129,etat68]) (consBan borne138 (consBan borne139 (consBan borne140 (consBan borne141 (consBan borne142 (consBan borne143 (consBan borne80 (nilBan 96 5)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur115 : ℕ := 0x1000000002803fc000000000
def etat131 : List ℕ := [valeur115,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne145 : Ban 96 6 etat131 := viaPerm proj10 proj3 borne144 (by decide +kernel) (by decide +kernel)
def valeur116 : ℕ := 0xf892a5095bda2d6d129692a8fc00800ffffffffff3fc0000
def etat132 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur116]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne146 : Ban 96 6 etat132 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur117 : ℕ := 0x2810050820141101412080000800ff000000033fc0000
def etat133 : List ℕ := [valeur117,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne147 : Ban 96 6 etat133 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur118 : ℕ := 0xf89024090b582c2c028280a0ec0000000d7fc03fc0000000
def etat134 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur118,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne148 : Ban 96 6 etat134 := viaDirect (by decide +kernel) (by decide +kernel)
def etat135 : List ℕ := [valeur34,valeur2,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne149 : Ban 96 6 etat135 := viaDirect (by decide +kernel) (by decide +kernel)
def etat136 : List ℕ := [valeur0,valeur34,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne150 : Ban 96 6 etat136 := viaDirect (by decide +kernel) (by decide +kernel)
def etat137 : List ℕ := [valeur34,valeur81,valeur35,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne151 : Ban 96 5 etat137 := viaDirect (by decide +kernel) (by decide +kernel)
def etat138 : List ℕ := [valeur34,valeur85,valeur35,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne152 : Ban 96 5 etat138 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur119 : ℕ := 0x542d12450a21151511516491d00c00ff3803ffffbfffcff
def etat139 : List ℕ := [valeur34,valeur2,valeur119,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne153 : Ban 96 5 etat139 := viaDirect (by decide +kernel) (by decide +kernel)
def etat140 : List ℕ := [valeur2,valeur35,valeur119,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne154 : Ban 96 5 etat140 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur120 : ℕ := 0xbde0782e00603030430304c1fffffffff100003fc803fcff
def etat141 : List ℕ := [valeur34,valeur2,valeur35,valeur4,valeur120,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne155 : Ban 96 5 etat141 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur121 : ℕ := 0xb8a0280a0040202002020080f2ffbffff000000000000000
def etat142 : List ℕ := [valeur34,valeur2,valeur35,valeur4,valeur121,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne156 : Ban 96 5 etat142 := viaDirect (by decide +kernel) (by decide +kernel)
def etat143 : List ℕ := [valeur34,valeur2,valeur35,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne157 : Ban 96 6 etat143 := viaBranch (ws := [etat137,etat138,etat139,etat140,etat141,etat142]) (consBan borne151 (consBan borne152 (consBan borne153 (consBan borne154 (consBan borne155 (consBan borne156 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat144 : List ℕ := [valeur34,valeur7,valeur2,valeur35,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne158 : Ban 96 6 etat144 := viaDirect (by decide +kernel) (by decide +kernel)
def etat145 : List ℕ := [valeur34,valeur2,valeur35,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne159 : Ban 96 6 etat145 := viaDirect (by decide +kernel) (by decide +kernel)
def etat146 : List ℕ := [valeur34,valeur2,valeur3,valeur4,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne160 : Ban 96 6 etat146 := viaDirect (by decide +kernel) (by decide +kernel)
def etat147 : List ℕ := [valeur34,valeur37,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne161 : Ban 96 6 etat147 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur122 : ℕ := 0x401404010b10080800a0a020c1ff00000300000007fffc00
def etat148 : List ℕ := [valeur7,valeur38,valeur3,valeur122,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne162 : Ban 96 5 etat148 := viaDirect (by decide +kernel) (by decide +kernel)
def etat149 : List ℕ := [valeur7,valeur2,valeur40,valeur122,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne163 : Ban 96 5 etat149 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur123 : ℕ := 0x401404010b10080800a0a020c1ff00000300000037fffc00
def etat150 : List ℕ := [valeur7,valeur2,valeur3,valeur123,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne164 : Ban 96 5 etat150 := viaDirect (by decide +kernel) (by decide +kernel)
def etat151 : List ℕ := [valeur7,valeur2,valeur3,valeur122,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne165 : Ban 96 5 etat151 := viaDirect (by decide +kernel) (by decide +kernel)
def etat152 : List ℕ := [valeur7,valeur2,valeur3,valeur122,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne166 : Ban 96 5 etat152 := viaDirect (by decide +kernel) (by decide +kernel)
def etat153 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur122,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne167 : Ban 96 6 etat153 := viaBranch (ws := [etat148,etat149,etat150,etat151,etat152]) (consBan borne162 (consBan borne163 (consBan borne164 (consBan borne165 (consBan borne166 (nilBan 96 5)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat154 : List ℕ := [valeur44,valeur34,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne168 : Ban 96 6 etat154 := viaPerm proj9 proj5 borne167 (by decide +kernel) (by decide +kernel)
def etat155 : List ℕ := [valeur34,valeur2,valeur3,valeur4,valeur45,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne169 : Ban 96 6 etat155 := viaDirect (by decide +kernel) (by decide +kernel)
def etat156 : List ℕ := [valeur34,valeur2,valeur3,valeur4,valeur5,valeur6,valeur46]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne170 : Ban 96 6 etat156 := viaDirect (by decide +kernel) (by decide +kernel)
def etat157 : List ℕ := [valeur34,valeur47,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne171 : Ban 96 6 etat157 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne172 : Ban 96 7 etat54 := viaBranch (ws := [etat84,etat85,etat6,etat86,etat87,etat88,etat89,etat97,etat98,etat103,etat33,etat82,etat109,etat110,etat111,etat112,etat120,etat121,etat122,etat123,etat131,etat132,etat133,etat134,etat135,etat136,etat143,etat144,etat145,etat146,etat147,etat154,etat155,etat156,etat157]) (consBan borne96 (consBan borne97 (consBan borne18 (consBan borne98 (consBan borne99 (consBan borne100 (consBan borne101 (consBan borne109 (consBan borne110 (consBan borne116 (consBan borne45 (consBan borne117 (consBan borne123 (consBan borne124 (consBan borne125 (consBan borne126 (consBan borne134 (consBan borne135 (consBan borne136 (consBan borne137 (consBan borne145 (consBan borne146 (consBan borne147 (consBan borne148 (consBan borne149 (consBan borne150 (consBan borne157 (consBan borne158 (consBan borne159 (consBan borne160 (consBan borne161 (consBan borne168 (consBan borne169 (consBan borne170 (consBan borne171 (nilBan 96 6)))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne173 : Ban 96 7 etat1 := viaPerm proj4 proj4 borne172 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne174 : Ban 96 7 etat3 := viaPerm proj3 proj10 borne172 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne175 : Ban 96 7 etat85 := viaPerm proj4 proj4 borne40 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne176 : Ban 96 7 etat35 := viaPerm proj2 proj2 borne172 (by decide +kernel) (by decide +kernel)
def etat158 : List ℕ := [valeur43,valeur37,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne177 : Ban 96 6 etat158 := viaDirect (by decide +kernel) (by decide +kernel)
def etat159 : List ℕ := [valeur37,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne178 : Ban 96 6 etat159 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur124 : ℕ := 0x20a8380c48703033850521c2200ffc00eff80003ffc03ff
def etat160 : List ℕ := [valeur7,valeur124,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne179 : Ban 96 6 etat160 := viaDirect (by decide +kernel) (by decide +kernel)
def etat161 : List ℕ := [valeur7,valeur38,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne180 : Ban 96 5 etat161 := viaDirect (by decide +kernel) (by decide +kernel)
def etat162 : List ℕ := [valeur7,valeur124,valeur40,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne181 : Ban 96 5 etat162 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur125 : ℕ := 0x54150742020d090c5090d430d0040300100403fc803ffff
def etat163 : List ℕ := [valeur7,valeur124,valeur125,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne182 : Ban 96 5 etat163 := viaDirect (by decide +kernel) (by decide +kernel)
def etat164 : List ℕ := [valeur7,valeur124,valeur3,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne183 : Ban 96 5 etat164 := viaDirect (by decide +kernel) (by decide +kernel)
def etat165 : List ℕ := [valeur7,valeur124,valeur3,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne184 : Ban 96 5 etat165 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur126 : ℕ := 0xf89024090b582c2c028280a0fc0000000dffffffc0000000
def etat166 : List ℕ := [valeur7,valeur124,valeur3,valeur4,valeur5,valeur126]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne185 : Ban 96 5 etat166 := viaDirect (by decide +kernel) (by decide +kernel)
def etat167 : List ℕ := [valeur43,valeur7,valeur124,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne186 : Ban 96 6 etat167 := viaBranch (ws := [etat161,etat162,etat163,etat164,etat165,etat166]) (consBan borne180 (consBan borne181 (consBan borne182 (consBan borne183 (consBan borne184 (consBan borne185 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat168 : List ℕ := [valeur7,valeur2,valeur124,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne187 : Ban 96 6 etat168 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur127 : ℕ := 0x200000007fc0000
def etat169 : List ℕ := [valeur127,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne188 : Ban 96 6 etat169 := viaPerm proj1 proj1 borne133 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne189 : Ban 96 6 etat161 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne190 : Ban 96 5 etat160 := viaDirect (by decide +kernel) (by decide +kernel)
def etat170 : List ℕ := [valeur7,valeur38,valeur40,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne191 : Ban 96 5 etat170 := viaDirect (by decide +kernel) (by decide +kernel)
def etat171 : List ℕ := [valeur7,valeur38,valeur125,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne192 : Ban 96 5 etat171 := viaDirect (by decide +kernel) (by decide +kernel)
def etat172 : List ℕ := [valeur7,valeur38,valeur3,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne193 : Ban 96 5 etat172 := viaDirect (by decide +kernel) (by decide +kernel)
def etat173 : List ℕ := [valeur7,valeur38,valeur3,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne194 : Ban 96 5 etat173 := viaDirect (by decide +kernel) (by decide +kernel)
def etat174 : List ℕ := [valeur7,valeur38,valeur3,valeur4,valeur5,valeur126]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne195 : Ban 96 5 etat174 := viaDirect (by decide +kernel) (by decide +kernel)
def etat175 : List ℕ := [valeur43,valeur7,valeur38,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne196 : Ban 96 6 etat175 := viaBranch (ws := [etat160,etat170,etat171,etat172,etat173,etat174]) (consBan borne190 (consBan borne191 (consBan borne192 (consBan borne193 (consBan borne194 (consBan borne195 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur128 : ℕ := 0x540502400201010410104410d0040000100003fc803ffff
def etat176 : List ℕ := [valeur7,valeur2,valeur128,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne197 : Ban 96 5 etat176 := viaDirect (by decide +kernel) (by decide +kernel)
def etat177 : List ℕ := [valeur89,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne198 : Ban 96 5 etat177 := viaDirect (by decide +kernel) (by decide +kernel)
def etat178 : List ℕ := [valeur89,valeur8,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne199 : Ban 96 5 etat178 := viaDirect (by decide +kernel) (by decide +kernel)
def etat179 : List ℕ := [valeur89,valeur2,valeur32,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne200 : Ban 96 5 etat179 := viaDirect (by decide +kernel) (by decide +kernel)
def etat180 : List ℕ := [valeur89,valeur2,valeur35,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne201 : Ban 96 5 etat180 := viaDirect (by decide +kernel) (by decide +kernel)
def etat181 : List ℕ := [valeur89,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne202 : Ban 96 6 etat181 := viaBranch (ws := [etat97,etat176,etat177,etat178,etat179,etat180]) (consBan borne112 (consBan borne197 (consBan borne198 (consBan borne199 (consBan borne200 (consBan borne201 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat182 : List ℕ := [valeur7,valeur38,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne203 : Ban 96 6 etat182 := viaPerm proj3 proj10 borne202 (by decide +kernel) (by decide +kernel)
def valeur129 : ℕ := 0x4000000
def etat183 : List ℕ := [valeur129,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne204 : Ban 96 6 etat183 := viaPerm proj6 proj6 borne29 (by decide +kernel) (by decide +kernel)
def etat184 : List ℕ := [valeur2,valeur31,valeur3,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne205 : Ban 96 5 etat184 := viaDirect (by decide +kernel) (by decide +kernel)
def etat185 : List ℕ := [valeur0,valeur2,valeur3,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne206 : Ban 96 5 etat185 := viaDirect (by decide +kernel) (by decide +kernel)
def etat186 : List ℕ := [valeur7,valeur2,valeur3,valeur36,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne207 : Ban 96 5 etat186 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur130 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000d0000000803fc00
def etat187 : List ℕ := [valeur7,valeur2,valeur3,valeur130,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne208 : Ban 96 5 etat187 := viaDirect (by decide +kernel) (by decide +kernel)
def etat188 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne209 : Ban 96 6 etat188 := viaBranch (ws := [etat184,etat185,etat186,etat187,etat41,etat152]) (consBan borne205 (consBan borne206 (consBan borne207 (consBan borne208 (consBan borne53 (consBan borne166 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat189 : List ℕ := [valeur7,valeur2,valeur40,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne210 : Ban 96 6 etat189 := viaPerm proj8 proj8 borne209 (by decide +kernel) (by decide +kernel)
def etat190 : List ℕ := [valeur7,valeur2,valeur40,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne211 : Ban 96 5 etat190 := viaDirect (by decide +kernel) (by decide +kernel)
def etat191 : List ℕ := [valeur7,valeur2,valeur125,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne212 : Ban 96 5 etat191 := viaDirect (by decide +kernel) (by decide +kernel)
def etat192 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur41,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne213 : Ban 96 5 etat192 := viaDirect (by decide +kernel) (by decide +kernel)
def etat193 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur126]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne214 : Ban 96 5 etat193 := viaDirect (by decide +kernel) (by decide +kernel)
def etat194 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur4,valeur5,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne215 : Ban 96 6 etat194 := viaBranch (ws := [etat165,etat173,etat190,etat191,etat187,etat192,etat193]) (consBan borne184 (consBan borne194 (consBan borne211 (consBan borne212 (consBan borne208 (consBan borne213 (consBan borne214 (nilBan 96 5)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat195 : List ℕ := [valeur43,valeur7,valeur2,valeur40,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne216 : Ban 96 6 etat195 := viaPerm proj8 proj8 borne215 (by decide +kernel) (by decide +kernel)
def etat196 : List ℕ := [valeur7,valeur2,valeur3,valeur40,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne217 : Ban 96 6 etat196 := viaDirect (by decide +kernel) (by decide +kernel)
def etat197 : List ℕ := [valeur7,valeur2,valeur125,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne218 : Ban 96 6 etat197 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne219 : Ban 96 5 etat189 := viaDirect (by decide +kernel) (by decide +kernel)
def etat198 : List ℕ := [valeur7,valeur2,valeur125,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne220 : Ban 96 5 etat198 := viaDirect (by decide +kernel) (by decide +kernel)
def etat199 : List ℕ := [valeur7,valeur2,valeur125,valeur4,valeur5,valeur126]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne221 : Ban 96 5 etat199 := viaDirect (by decide +kernel) (by decide +kernel)
def etat200 : List ℕ := [valeur43,valeur7,valeur2,valeur125,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne222 : Ban 96 6 etat200 := viaBranch (ws := [etat163,etat171,etat189,etat198,etat191,etat199]) (consBan borne182 (consBan borne192 (consBan borne219 (consBan borne220 (consBan borne212 (consBan borne221 (nilBan 96 5))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat201 : List ℕ := [valeur7,valeur2,valeur125,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne223 : Ban 96 6 etat201 := viaDirect (by decide +kernel) (by decide +kernel)
def etat202 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur130,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne224 : Ban 96 6 etat202 := viaDirect (by decide +kernel) (by decide +kernel)
def etat203 : List ℕ := [valeur7,valeur2,valeur3,valeur130,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne225 : Ban 96 6 etat203 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur131 : ℕ := 0xf89024090b582c2c028280a0fc0040000fffffffc80003ff
def etat204 : List ℕ := [valeur7,valeur31,valeur3,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne226 : Ban 96 5 etat204 := viaDirect (by decide +kernel) (by decide +kernel)
def etat205 : List ℕ := [valeur7,valeur8,valeur3,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne227 : Ban 96 5 etat205 := viaDirect (by decide +kernel) (by decide +kernel)
def etat206 : List ℕ := [valeur7,valeur2,valeur32,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne228 : Ban 96 5 etat206 := viaDirect (by decide +kernel) (by decide +kernel)
def etat207 : List ℕ := [valeur7,valeur2,valeur35,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne229 : Ban 96 5 etat207 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur132 : ℕ := 0x74bd3f4e4a7d393fd595f5f2f00fff00dffc03ffc03ffff
def etat208 : List ℕ := [valeur7,valeur2,valeur132,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne230 : Ban 96 5 etat208 := viaDirect (by decide +kernel) (by decide +kernel)
def etat209 : List ℕ := [valeur7,valeur3,valeur132,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne231 : Ban 96 5 etat209 := viaDirect (by decide +kernel) (by decide +kernel)
def etat210 : List ℕ := [valeur7,valeur49,valeur3,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne232 : Ban 96 5 etat210 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur133 : ℕ := 0x54150742020d090c5090d430d0000300100403fc403fc00
def etat211 : List ℕ := [valeur7,valeur2,valeur133,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne233 : Ban 96 5 etat211 := viaDirect (by decide +kernel) (by decide +kernel)
def etat212 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne234 : Ban 96 6 etat212 := viaBranch (ws := [etat204,etat205,etat206,etat207,etat208,etat209,etat210,etat211]) (consBan borne226 (consBan borne227 (consBan borne228 (consBan borne229 (consBan borne230 (consBan borne231 (consBan borne232 (consBan borne233 (nilBan 96 5))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat213 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne235 : Ban 96 6 etat213 := viaPerm proj3 proj10 borne234 (by decide +kernel) (by decide +kernel)
def etat214 : List ℕ := [valeur37,valeur2,valeur3,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne236 : Ban 96 5 etat214 := viaDirect (by decide +kernel) (by decide +kernel)
def etat215 : List ℕ := [valeur7,valeur2,valeur40,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne237 : Ban 96 5 etat215 := viaDirect (by decide +kernel) (by decide +kernel)
def etat216 : List ℕ := [valeur7,valeur2,valeur3,valeur130,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne238 : Ban 96 5 etat216 := viaDirect (by decide +kernel) (by decide +kernel)
def etat217 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne239 : Ban 96 5 etat217 := viaDirect (by decide +kernel) (by decide +kernel)
def etat218 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur41,valeur126]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne240 : Ban 96 5 etat218 := viaDirect (by decide +kernel) (by decide +kernel)
def etat219 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur4,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne241 : Ban 96 6 etat219 := viaBranch (ws := [etat214,etat164,etat172,etat215,etat198,etat216,etat217,etat192,etat218]) (consBan borne236 (consBan borne183 (consBan borne193 (consBan borne237 (consBan borne220 (consBan borne238 (consBan borne239 (consBan borne213 (consBan borne240 (nilBan 96 5)))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat220 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur41,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne242 : Ban 96 6 etat220 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur134 : ℕ := 0x200000000000000
def etat221 : List ℕ := [valeur134,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne243 : Ban 96 6 etat221 := viaPerm proj3 proj10 borne29 (by decide +kernel) (by decide +kernel)
def etat222 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur42]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne244 : Ban 96 6 etat222 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur135 : ℕ := 0x37fc0000
def etat223 : List ℕ := [valeur135,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne245 : Ban 96 6 etat223 := viaPerm proj6 proj6 borne122 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne246 : Ban 96 6 etat193 := viaDirect (by decide +kernel) (by decide +kernel)
def etat224 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur4,valeur5,valeur126]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne247 : Ban 96 6 etat224 := viaPerm proj8 proj8 borne222 (by decide +kernel) (by decide +kernel)
def etat225 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur126,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne248 : Ban 96 6 etat225 := viaDirect (by decide +kernel) (by decide +kernel)
def etat226 : List ℕ := [valeur43,valeur2,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne249 : Ban 96 6 etat226 := viaPerm proj8 proj8 borne55 (by decide +kernel) (by decide +kernel)
def etat227 : List ℕ := [valeur43,valeur0,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne250 : Ban 96 6 etat227 := viaPerm proj8 proj8 borne167 (by decide +kernel) (by decide +kernel)
def etat228 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne251 : Ban 96 6 etat228 := viaDirect (by decide +kernel) (by decide +kernel)
def etat229 : List ℕ := [valeur43,valeur2,valeur3,valeur4,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne252 : Ban 96 6 etat229 := viaDirect (by decide +kernel) (by decide +kernel)
def etat230 : List ℕ := [valeur43,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne253 : Ban 96 7 etat230 := viaBranch (ws := [etat158,etat159,etat8,etat160,etat167,etat168,etat169,etat161,etat175,etat182,etat183,etat189,etat195,etat196,etat109,etat197,etat200,etat201,etat202,etat203,etat213,etat219,etat220,etat221,etat188,etat194,etat222,etat223,etat193,etat224,etat225,etat226,etat227,etat228,etat229,etat43,etat153]) (consBan borne177 (consBan borne178 (consBan borne20 (consBan borne179 (consBan borne186 (consBan borne187 (consBan borne188 (consBan borne189 (consBan borne196 (consBan borne203 (consBan borne204 (consBan borne210 (consBan borne216 (consBan borne217 (consBan borne123 (consBan borne218 (consBan borne222 (consBan borne223 (consBan borne224 (consBan borne225 (consBan borne235 (consBan borne241 (consBan borne242 (consBan borne243 (consBan borne209 (consBan borne215 (consBan borne244 (consBan borne245 (consBan borne246 (consBan borne247 (consBan borne248 (consBan borne249 (consBan borne250 (consBan borne251 (consBan borne252 (consBan borne55 (consBan borne167 (nilBan 96 6)))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat231 : List ℕ := [valeur37,valeur7,valeur2,valeur3,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne254 : Ban 96 6 etat231 := viaDirect (by decide +kernel) (by decide +kernel)
def etat232 : List ℕ := [valeur2,valeur3,valeur130,valeur4,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne255 : Ban 96 6 etat232 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur136 : ℕ := 0xbde3f97e70e2f1f1971f1bcafffffffff2807fc037fc0300
def etat233 : List ℕ := [valeur2,valeur3,valeur4,valeur36,valeur5,valeur136,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne256 : Ban 96 6 etat233 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur137 : ℕ := 0x381507082c1c1941c1b0a0000000002807fc037fc0300
def etat234 : List ℕ := [valeur137,valeur2,valeur3,valeur4,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne257 : Ban 96 6 etat234 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur138 : ℕ := 0x20a8300c486030338505218020080000c80000038000300
def etat235 : List ℕ := [valeur7,valeur138,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne258 : Ban 96 6 etat235 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur139 : ℕ := 0x421f87d1ff97cbcbbcfcfb3ef3ffffffffffffc03fffffff
def etat236 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur139,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne259 : Ban 96 6 etat236 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur140 : ℕ := 0x80000100000000000420007fc0007f8000000000ff
def etat237 : List ℕ := [valeur140,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne260 : Ban 96 6 etat237 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur141 : ℕ := 0x401504513b10c8c884aca922d1ff003ff3007fc007fffc00
def etat238 : List ℕ := [valeur7,valeur2,valeur3,valeur141,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne261 : Ban 96 6 etat238 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur142 : ℕ := 0x100502000c0808408090201000030010040000c03ff00
def etat239 : List ℕ := [valeur142,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne262 : Ban 96 6 etat239 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur143 : ℕ := 0x540502400201010410104410c0040000000003fc00000ff
def etat240 : List ℕ := [valeur7,valeur2,valeur143,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne263 : Ban 96 6 etat240 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur144 : ℕ := 0x421e8701df960b4b38f4f238d2ff800ffe803fc033fc0000
def etat241 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur144,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne264 : Ban 96 6 etat241 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur145 : ℕ := 0xfffc7e2f8f743a3a2be3e0f0ffffffffff0000003ffffc00
def etat242 : List ℕ := [valeur7,valeur2,valeur3,valeur36,valeur5,valeur6,valeur145]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne265 : Ban 96 6 etat242 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur146 : ℕ := 0x421c06018f140a0a28e0e030000000000f0000003ffffc00
def etat243 : List ℕ := [valeur7,valeur2,valeur3,valeur146,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne266 : Ban 96 6 etat243 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur147 : ℕ := 0xfa9c26098f5c2e2e2ae2e0b0ffff00000ffffffffffffc00
def etat244 : List ℕ := [valeur7,valeur2,valeur3,valeur36,valeur5,valeur6,valeur147]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne267 : Ban 96 6 etat244 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur148 : ℕ := 0x20c0200840402022860601003ff0000000000003ffffc00
def etat245 : List ℕ := [valeur7,valeur2,valeur148,valeur3,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne268 : Ban 96 6 etat245 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur149 : ℕ := 0x381507082c1c1941c1b0a3c00803ffffffffff7fc0300
def etat246 : List ℕ := [valeur149,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne269 : Ban 96 5 etat246 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur150 : ℕ := 0x381507082c1c1941c1b0a1000803ff2003fc037fc0300
def etat247 : List ℕ := [valeur150,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne270 : Ban 96 5 etat247 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur151 : ℕ := 0x20a8380c48703033850521c2e00ffc00dffc03ff80003ff
def etat248 : List ℕ := [valeur7,valeur151,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne271 : Ban 96 5 etat248 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur152 : ℕ := 0x54150742020d090c5090d432d0040300dffc03fcc03ffff
def etat249 : List ℕ := [valeur7,valeur2,valeur152,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne272 : Ban 96 5 etat249 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur153 : ℕ := 0x421c06018f140a0a28e0e030efff00000fffc03ffffffc00
def etat250 : List ℕ := [valeur7,valeur2,valeur3,valeur153,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne273 : Ban 96 5 etat250 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur154 : ℕ := 0x421c06018f140a0a28e0e030c3ff0000020000003ffffc00
def etat251 : List ℕ := [valeur7,valeur2,valeur3,valeur154,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne274 : Ban 96 5 etat251 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur155 : ℕ := 0xbde0782e00603030030300c0fffffffffdffc03fc0000000
def etat252 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur155,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne275 : Ban 96 5 etat252 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur156 : ℕ := 0xbde0782e00603030030300c0d3fffffff000000000000000
def etat253 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur156,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne276 : Ban 96 5 etat253 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur157 : ℕ := 0x2c0000000dffc03fc0000000
def etat254 : List ℕ := [valeur157,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne277 : Ban 96 6 etat254 := viaBranch (ws := [etat246,etat247,etat248,etat249,etat250,etat251,etat252,etat253]) (consBan borne269 (consBan borne270 (consBan borne271 (consBan borne272 (consBan borne273 (consBan borne274 (consBan borne275 (consBan borne276 (nilBan 96 5))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur158 : ℕ := 0xd3ff803ff000000000000000
def etat255 : List ℕ := [valeur158,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne278 : Ban 96 6 etat255 := viaPerm proj3 proj10 borne277 (by decide +kernel) (by decide +kernel)
def valeur159 : ℕ := 0xffffff7ffff6fbfbbffffbfaffffffffff807fc03fffff00
def etat256 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur159]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne279 : Ban 96 6 etat256 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur160 : ℕ := 0x421f8751ff96cbcbbcfcfb3a000000000f807fc03fffff00
def etat257 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur160,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne280 : Ban 96 6 etat257 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur161 : ℕ := 0xbde0782e00603030030300c02c007fc00000000000000000
def etat258 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur161,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne281 : Ban 96 6 etat258 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur162 : ℕ := 0x401004010b10080800808020d00000000f807fc000000000
def etat259 : List ℕ := [valeur7,valeur2,valeur3,valeur162,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne282 : Ban 96 6 etat259 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur163 : ℕ := 0xfa9fa759ffdeefefbefefbbaffff803fffffffffffffff00
def etat260 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur163]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne283 : Ban 96 6 etat260 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur164 : ℕ := 0x20f8350f486c3c3bc7c7b1a03ff803ff00000003fffff00
def etat261 : List ℕ := [valeur7,valeur2,valeur164,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne284 : Ban 96 6 etat261 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur165 : ℕ := 0xb880200800482424020200802c000000007f803fc0000000
def etat262 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur165,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne285 : Ban 96 6 etat262 := viaDirect (by decide +kernel) (by decide +kernel)
def etat263 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur36,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne286 : Ban 96 7 etat263 := viaBranch (ws := [etat36,etat146,etat228,etat229,etat231,etat232,etat203,etat233,etat234,etat235,etat236,etat237,etat238,etat239,etat71,etat240,etat241,etat159,etat242,etat243,etat244,etat245,etat255,etat256,etat257,etat258,etat259,etat260,etat261,etat262]) (consBan borne48 (consBan borne160 (consBan borne251 (consBan borne252 (consBan borne254 (consBan borne255 (consBan borne225 (consBan borne256 (consBan borne257 (consBan borne258 (consBan borne259 (consBan borne260 (consBan borne261 (consBan borne262 (consBan borne83 (consBan borne263 (consBan borne264 (consBan borne178 (consBan borne265 (consBan borne266 (consBan borne267 (consBan borne268 (consBan borne278 (consBan borne279 (consBan borne280 (consBan borne281 (consBan borne282 (consBan borne283 (consBan borne284 (consBan borne285 (nilBan 96 6))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat264 : List ℕ := [valeur44,valeur137,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne287 : Ban 96 6 etat264 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne288 : Ban 96 5 etat197 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne289 : Ban 96 5 etat213 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne290 : Ban 96 5 etat188 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne291 : Ban 96 6 etat230 := viaBranch (ws := [etat160,etat161,etat189,etat197,etat213,etat188,etat193]) (consBan borne190 (consBan borne180 (consBan borne219 (consBan borne288 (consBan borne289 (consBan borne290 (consBan borne214 (nilBan 96 5)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat265 : List ℕ := [valeur44,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne292 : Ban 96 6 etat265 := viaPerm proj4 proj4 borne291 (by decide +kernel) (by decide +kernel)
def valeur166 : ℕ := 0x20b83d0f487c3c3bc5c5b1e2200ffc00effffc03ffc03ff
def etat266 : List ℕ := [valeur7,valeur2,valeur166,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne293 : Ban 96 6 etat266 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur167 : ℕ := 0x100503000c0c0840c09020000000002007fc007fc0000
def etat267 : List ℕ := [valeur167,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne294 : Ban 96 6 etat267 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur168 : ℕ := 0x208028084050202284040142200ffc00c7f8000080000ff
def etat268 : List ℕ := [valeur7,valeur168,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne295 : Ban 96 6 etat268 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur169 : ℕ := 0x100502000c08084080902000000000000400004000300
def etat269 : List ℕ := [valeur169,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne296 : Ban 96 6 etat269 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur170 : ℕ := 0x543d17470a2d1d1d51d1f4b0d00403003807fffffffffff
def etat270 : List ℕ := [valeur7,valeur2,valeur3,valeur170,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne297 : Ban 96 6 etat270 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur171 : ℕ := 0x540502400201010410104410d0040300100003fc803fcff
def etat271 : List ℕ := [valeur7,valeur2,valeur171,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne298 : Ban 96 6 etat271 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur172 : ℕ := 0x421f8751ff96cbcbbcfcfb3ac3ff00000f807fc03fffff00
def etat272 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur172,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne299 : Ban 96 6 etat272 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur173 : ℕ := 0x381507082c1c1941c1b0a0000000000807fc000000300
def etat273 : List ℕ := [valeur173,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne300 : Ban 96 6 etat273 := viaDirect (by decide +kernel) (by decide +kernel)
def etat274 : List ℕ := [valeur137,valeur7,valeur2,valeur3,valeur4,valeur136,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne301 : Ban 96 6 etat274 := viaDirect (by decide +kernel) (by decide +kernel)
def etat275 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur136,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne302 : Ban 96 6 etat275 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur174 : ℕ := 0x2807fc000000000
def etat276 : List ℕ := [valeur174,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne303 : Ban 96 6 etat276 := viaPerm proj1 proj1 borne144 (by decide +kernel) (by decide +kernel)
def valeur175 : ℕ := 0xf893a5597bdaeded969e9baafc0000000ffffffff7fc0300
def etat277 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur175]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne304 : Ban 96 6 etat277 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur176 : ℕ := 0x381507082c1c1941c1b0a000000000000000037fc0300
def etat278 : List ℕ := [valeur176,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne305 : Ban 96 6 etat278 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur177 : ℕ := 0xf89024090b582c2c028280a0fc0000000d7f803fc0000000
def etat279 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur177,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne306 : Ban 96 6 etat279 := viaDirect (by decide +kernel) (by decide +kernel)
def etat280 : List ℕ := [valeur137,valeur2,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne307 : Ban 96 6 etat280 := viaDirect (by decide +kernel) (by decide +kernel)
def etat281 : List ℕ := [valeur0,valeur137,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne308 : Ban 96 6 etat281 := viaDirect (by decide +kernel) (by decide +kernel)
def etat282 : List ℕ := [valeur137,valeur37,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne309 : Ban 96 6 etat282 := viaDirect (by decide +kernel) (by decide +kernel)
def etat283 : List ℕ := [valeur137,valeur2,valeur3,valeur4,valeur45,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne310 : Ban 96 6 etat283 := viaDirect (by decide +kernel) (by decide +kernel)
def etat284 : List ℕ := [valeur137,valeur7,valeur2,valeur3,valeur4,valeur45,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne311 : Ban 96 6 etat284 := viaDirect (by decide +kernel) (by decide +kernel)
def etat285 : List ℕ := [valeur137,valeur2,valeur3,valeur4,valeur45,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne312 : Ban 96 6 etat285 := viaDirect (by decide +kernel) (by decide +kernel)
def etat286 : List ℕ := [valeur137,valeur7,valeur2,valeur3,valeur4,valeur56,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne313 : Ban 96 6 etat286 := viaDirect (by decide +kernel) (by decide +kernel)
def etat287 : List ℕ := [valeur137,valeur7,valeur2,valeur3,valeur4,valeur87,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne314 : Ban 96 6 etat287 := viaDirect (by decide +kernel) (by decide +kernel)
def etat288 : List ℕ := [valeur137,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne315 : Ban 96 7 etat288 := viaBranch (ws := [etat264,etat265,etat20,etat266,etat267,etat268,etat269,etat270,etat122,etat271,etat230,etat272,etat273,etat203,etat274,etat275,etat276,etat277,etat278,etat279,etat280,etat281,etat234,etat282,etat283,etat284,etat285,etat286,etat287]) (consBan borne287 (consBan borne292 (consBan borne32 (consBan borne293 (consBan borne294 (consBan borne295 (consBan borne296 (consBan borne297 (consBan borne136 (consBan borne298 (consBan borne291 (consBan borne299 (consBan borne300 (consBan borne225 (consBan borne301 (consBan borne302 (consBan borne303 (consBan borne304 (consBan borne305 (consBan borne306 (consBan borne307 (consBan borne308 (consBan borne257 (consBan borne309 (consBan borne310 (consBan borne311 (consBan borne312 (consBan borne313 (consBan borne314 (nilBan 96 6)))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne316 : Ban 96 7 etat159 := viaPerm proj4 proj4 borne315 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne317 : Ban 96 7 etat203 := viaPerm proj5 proj9 borne315 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne318 : Ban 96 7 etat265 := viaPerm proj4 proj4 borne253 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne319 : Ban 96 7 etat275 := viaPerm proj4 proj4 borne286 (by decide +kernel) (by decide +kernel)
def etat289 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur45,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne320 : Ban 96 7 etat289 := viaPerm proj1 proj1 borne315 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne321 : Ban 96 6 etat124 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur178 : ℕ := 0xf89024090b582c2c028280a0fe00ffc00fffffffc0000000
def etat290 : List ℕ := [valeur108,valeur2,valeur3,valeur4,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne322 : Ban 96 5 etat290 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur179 : ℕ := 0x381507082c1c1941c1b0a1000003ff2807fc037fc0300
def etat291 : List ℕ := [valeur179,valeur2,valeur3,valeur4,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne323 : Ban 96 5 etat291 := viaDirect (by decide +kernel) (by decide +kernel)
def etat292 : List ℕ := [valeur7,valeur2,valeur62,valeur4,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne324 : Ban 96 5 etat292 := viaDirect (by decide +kernel) (by decide +kernel)
def etat293 : List ℕ := [valeur7,valeur2,valeur110,valeur4,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne325 : Ban 96 5 etat293 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur180 : ℕ := 0x421c06018f140a0a28e0e030e3ffffc00f0000003ffffc00
def etat294 : List ℕ := [valeur7,valeur2,valeur3,valeur180,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne326 : Ban 96 5 etat294 := viaDirect (by decide +kernel) (by decide +kernel)
def etat295 : List ℕ := [valeur7,valeur2,valeur3,valeur112,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne327 : Ban 96 5 etat295 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur181 : ℕ := 0xbde0782e00603030030300c0ddff003ff000000000000000
def etat296 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur181,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne328 : Ban 96 5 etat296 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur182 : ℕ := 0x2200ffc00000000000000000
def etat297 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur4,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne329 : Ban 96 6 etat297 := viaBranch (ws := [etat290,etat291,etat292,etat293,etat294,etat295,etat296,etat68]) (consBan borne322 (consBan borne323 (consBan borne324 (consBan borne325 (consBan borne326 (consBan borne327 (consBan borne328 (consBan borne80 (nilBan 96 5))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat298 : List ℕ := [valeur182,valeur108,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne330 : Ban 96 6 etat298 := viaPerm proj7 proj7 borne329 (by decide +kernel) (by decide +kernel)
def etat299 : List ℕ := [valeur7,valeur108,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne331 : Ban 96 6 etat299 := viaDirect (by decide +kernel) (by decide +kernel)
def etat300 : List ℕ := [valeur179,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne332 : Ban 96 6 etat300 := viaDirect (by decide +kernel) (by decide +kernel)
def etat301 : List ℕ := [valeur179,valeur2,valeur62,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne333 : Ban 96 5 etat301 := viaDirect (by decide +kernel) (by decide +kernel)
def etat302 : List ℕ := [valeur179,valeur2,valeur110,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne334 : Ban 96 5 etat302 := viaDirect (by decide +kernel) (by decide +kernel)
def etat303 : List ℕ := [valeur179,valeur2,valeur3,valeur180,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne335 : Ban 96 5 etat303 := viaDirect (by decide +kernel) (by decide +kernel)
def etat304 : List ℕ := [valeur179,valeur2,valeur3,valeur112,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne336 : Ban 96 5 etat304 := viaDirect (by decide +kernel) (by decide +kernel)
def etat305 : List ℕ := [valeur179,valeur2,valeur3,valeur4,valeur5,valeur67]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne337 : Ban 96 5 etat305 := viaDirect (by decide +kernel) (by decide +kernel)
def etat306 : List ℕ := [valeur182,valeur179,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne338 : Ban 96 6 etat306 := viaBranch (ws := [etat124,etat301,etat302,etat303,etat304,etat291,etat305]) (consBan borne138 (consBan borne333 (consBan borne334 (consBan borne335 (consBan borne336 (consBan borne323 (consBan borne337 (nilBan 96 5)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat307 : List ℕ := [valeur179,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne339 : Ban 96 6 etat307 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur183 : ℕ := 0x20a8380c48703033850521c000000000cff8000380003ff
def etat308 : List ℕ := [valeur182,valeur7,valeur183,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne340 : Ban 96 6 etat308 := viaDirect (by decide +kernel) (by decide +kernel)
def etat309 : List ℕ := [valeur7,valeur183,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne341 : Ban 96 6 etat309 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur184 : ℕ := 0x40000000000000000000
def etat310 : List ℕ := [valeur184,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne342 : Ban 96 6 etat310 := viaPerm proj4 proj4 borne29 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne343 : Ban 96 6 etat63 := viaDirect (by decide +kernel) (by decide +kernel)
def etat311 : List ℕ := [valeur182,valeur7,valeur2,valeur62,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne344 : Ban 96 6 etat311 := viaPerm proj8 proj8 borne329 (by decide +kernel) (by decide +kernel)
def etat312 : List ℕ := [valeur7,valeur2,valeur3,valeur62,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne345 : Ban 96 6 etat312 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur185 : ℕ := 0x2200bfc00000000000000000
def etat313 : List ℕ := [valeur185,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne346 : Ban 96 6 etat313 := viaPerm proj2 proj2 borne144 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne347 : Ban 96 6 etat126 := viaDirect (by decide +kernel) (by decide +kernel)
def etat314 : List ℕ := [valeur182,valeur7,valeur2,valeur110,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne348 : Ban 96 6 etat314 := viaPerm proj2 proj2 borne338 (by decide +kernel) (by decide +kernel)
def etat315 : List ℕ := [valeur7,valeur2,valeur110,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne349 : Ban 96 6 etat315 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur186 : ℕ := 0x20000000000000000000000
def etat316 : List ℕ := [valeur186,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne350 : Ban 96 6 etat316 := viaPerm proj11 proj11 borne29 (by decide +kernel) (by decide +kernel)
def etat317 : List ℕ := [valeur7,valeur2,valeur3,valeur180,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne351 : Ban 96 6 etat317 := viaDirect (by decide +kernel) (by decide +kernel)
def etat318 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur180,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne352 : Ban 96 6 etat318 := viaPerm proj2 proj2 borne329 (by decide +kernel) (by decide +kernel)
def etat319 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur180,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne353 : Ban 96 6 etat319 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur187 : ℕ := 0x2000ffc00000000000000000
def etat320 : List ℕ := [valeur187,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne354 : Ban 96 6 etat320 := viaPerm proj8 proj8 borne144 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne355 : Ban 96 6 etat128 := viaDirect (by decide +kernel) (by decide +kernel)
def etat321 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur112,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne356 : Ban 96 6 etat321 := viaPerm proj8 proj8 borne338 (by decide +kernel) (by decide +kernel)
def etat322 : List ℕ := [valeur7,valeur2,valeur3,valeur112,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne357 : Ban 96 6 etat322 := viaDirect (by decide +kernel) (by decide +kernel)
def etat323 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur4,valeur181,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne358 : Ban 96 6 etat323 := viaDirect (by decide +kernel) (by decide +kernel)
def etat324 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur181,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne359 : Ban 96 6 etat324 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur188 : ℕ := 0x200000000000000000000000
def etat325 : List ℕ := [valeur188,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne360 : Ban 96 6 etat325 := viaPerm proj5 proj9 borne29 (by decide +kernel) (by decide +kernel)
def etat326 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne361 : Ban 96 6 etat326 := viaDirect (by decide +kernel) (by decide +kernel)
def etat327 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur178]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne362 : Ban 96 6 etat327 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur189 : ℕ := 0x200ffc00000000000000000
def etat328 : List ℕ := [valeur189,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne363 : Ban 96 6 etat328 := viaPerm proj7 proj7 borne144 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne364 : Ban 96 6 etat68 := viaDirect (by decide +kernel) (by decide +kernel)
def etat329 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur4,valeur5,valeur67]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne365 : Ban 96 6 etat329 := viaPerm proj7 proj7 borne338 (by decide +kernel) (by decide +kernel)
def etat330 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur67,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne366 : Ban 96 6 etat330 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur190 : ℕ := 0xbfeafbaec4e733333b5352dcfffffffffcff8000380003ff
def etat331 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur4,valeur190,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne367 : Ban 96 6 etat331 := viaDirect (by decide +kernel) (by decide +kernel)
def etat332 : List ℕ := [valeur182,valeur7,valeur3,valeur4,valeur5,valeur190,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne368 : Ban 96 6 etat332 := viaDirect (by decide +kernel) (by decide +kernel)
def etat333 : List ℕ := [valeur182,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne369 : Ban 96 7 etat333 := viaBranch (ws := [etat18,etat124,etat298,etat299,etat130,etat300,etat306,etat307,etat308,etat309,etat310,etat63,etat311,etat312,etat313,etat126,etat314,etat315,etat316,etat317,etat318,etat319,etat320,etat128,etat321,etat322,etat323,etat324,etat325,etat326,etat297,etat327,etat328,etat68,etat329,etat330,etat331,etat332]) (consBan borne30 (consBan borne321 (consBan borne330 (consBan borne331 (consBan borne144 (consBan borne332 (consBan borne338 (consBan borne339 (consBan borne340 (consBan borne341 (consBan borne342 (consBan borne343 (consBan borne344 (consBan borne345 (consBan borne346 (consBan borne347 (consBan borne348 (consBan borne349 (consBan borne350 (consBan borne351 (consBan borne352 (consBan borne353 (consBan borne354 (consBan borne355 (consBan borne356 (consBan borne357 (consBan borne358 (consBan borne359 (consBan borne360 (consBan borne361 (consBan borne329 (consBan borne362 (consBan borne363 (consBan borne364 (consBan borne365 (consBan borne366 (consBan borne367 (consBan borne368 (nilBan 96 6))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur191 : ℕ := 0x1000000002807fc000000000
def etat334 : List ℕ := [valeur191,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne370 : Ban 96 7 etat334 := viaPerm proj1 proj1 borne369 (by decide +kernel) (by decide +kernel)
def etat335 : List ℕ := [valeur7,valeur2,valeur35,valeur4,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne371 : Ban 96 6 etat335 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur192 : ℕ := 0x100502000c08084080902000000300200400037fc0300
def etat336 : List ℕ := [valeur192,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne372 : Ban 96 6 etat336 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur193 : ℕ := 0x475c56258f341a1a69e1e471cfff40000d00003fc803fcff
def etat337 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur193,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne373 : Ban 96 6 etat337 := viaDirect (by decide +kernel) (by decide +kernel)
def etat338 : List ℕ := [valeur7,valeur2,valeur3,valeur39,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne374 : Ban 96 6 etat338 := viaDirect (by decide +kernel) (by decide +kernel)
def etat339 : List ℕ := [valeur7,valeur2,valeur3,valeur122,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne375 : Ban 96 6 etat339 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur194 : ℕ := 0x20802008404020228404010020040000c000000380003ff
def etat340 : List ℕ := [valeur7,valeur194,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne376 : Ban 96 6 etat340 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur195 : ℕ := 0x475fd7f5efb7db9bfdf9ff7feffffff00fffc03fffffffff
def etat341 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur195,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne377 : Ban 96 6 etat341 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur196 : ℕ := 0x28180408301011010120c2000bfc000ff800000000000
def etat342 : List ℕ := [valeur196,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne378 : Ban 96 6 etat342 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur197 : ℕ := 0x455554752b30d898c5a9ad63cdff00300300403fc7fffc00
def etat343 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur197,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne379 : Ban 96 6 etat343 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur198 : ℕ := 0x1000000010000000c03fc00
def etat344 : List ℕ := [valeur198,valeur7,valeur2,valeur3,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne380 : Ban 96 6 etat344 := viaDirect (by decide +kernel) (by decide +kernel)
def etat345 : List ℕ := [valeur198,valeur7,valeur2,valeur4,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne381 : Ban 96 6 etat345 := viaDirect (by decide +kernel) (by decide +kernel)
def etat346 : List ℕ := [valeur7,valeur2,valeur55,valeur3,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne382 : Ban 96 6 etat346 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur199 : ℕ := 0x421c06018f140a0a28e0e030c2ff00000e00000033fc0000
def etat347 : List ℕ := [valeur7,valeur2,valeur199,valeur4,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne383 : Ban 96 6 etat347 := viaDirect (by decide +kernel) (by decide +kernel)
def etat348 : List ℕ := [valeur7,valeur2,valeur3,valeur199,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne384 : Ban 96 6 etat348 := viaDirect (by decide +kernel) (by decide +kernel)
def etat349 : List ℕ := [valeur7,valeur2,valeur4,valeur54,valeur5,valeur56,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne385 : Ban 96 6 etat349 := viaDirect (by decide +kernel) (by decide +kernel)
def etat350 : List ℕ := [valeur57,valeur7,valeur2,valeur4,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne386 : Ban 96 6 etat350 := viaDirect (by decide +kernel) (by decide +kernel)
def etat351 : List ℕ := [valeur7,valeur2,valeur55,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne387 : Ban 96 6 etat351 := viaDirect (by decide +kernel) (by decide +kernel)
def etat352 : List ℕ := [valeur7,valeur2,valeur3,valeur54,valeur5,valeur6,valeur147]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne388 : Ban 96 6 etat352 := viaDirect (by decide +kernel) (by decide +kernel)
def etat353 : List ℕ := [valeur7,valeur2,valeur148,valeur3,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne389 : Ban 96 6 etat353 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur200 : ℕ := 0x54050240020101001010040cfff40300000000000000000
def etat354 : List ℕ := [valeur7,valeur2,valeur200,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne390 : Ban 96 6 etat354 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur201 : ℕ := 0xfffd7e7faf74fabaefebedf3ffffffffff00403fffffffff
def etat355 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur201]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne391 : Ban 96 6 etat355 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur202 : ℕ := 0x421d0651af14ca8aece8ed33000000000f00403fffffffff
def etat356 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur202,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne392 : Ban 96 6 etat356 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur203 : ℕ := 0xb8a0280a00402020020200803000bfcff000000000000000
def etat357 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur203,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne393 : Ban 96 6 etat357 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur204 : ℕ := 0x401004010b10080800808020cc0000000f00403fc0000000
def etat358 : List ℕ := [valeur7,valeur2,valeur3,valeur204,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne394 : Ban 96 6 etat358 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur205 : ℕ := 0xffdd767daf7cfebeefebedf3ffff40300fffffffffffffff
def etat359 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur205]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne395 : Ban 96 6 etat359 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur206 : ℕ := 0x74d5274a424d292ed696d5303ff4030000000003fffffff
def etat360 : List ℕ := [valeur7,valeur2,valeur3,valeur206,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne396 : Ban 96 6 etat360 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur207 : ℕ := 0xb880200800482424020200803000000000ffbfc000000000
def etat361 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur207,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne397 : Ban 96 6 etat361 := viaDirect (by decide +kernel) (by decide +kernel)
def etat362 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur54,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne398 : Ban 96 7 etat362 := viaBranch (ws := [etat55,etat335,etat336,etat71,etat111,etat337,etat338,etat339,etat340,etat341,etat342,etat343,etat344,etat345,etat346,etat347,etat348,etat349,etat350,etat351,etat352,etat353,etat354,etat355,etat356,etat357,etat358,etat359,etat360,etat361]) (consBan borne67 (consBan borne371 (consBan borne372 (consBan borne83 (consBan borne125 (consBan borne373 (consBan borne374 (consBan borne375 (consBan borne376 (consBan borne377 (consBan borne378 (consBan borne379 (consBan borne380 (consBan borne381 (consBan borne382 (consBan borne383 (consBan borne384 (consBan borne385 (consBan borne386 (consBan borne387 (consBan borne388 (consBan borne389 (consBan borne390 (consBan borne391 (consBan borne392 (consBan borne393 (consBan borne394 (consBan borne395 (consBan borne396 (consBan borne397 (nilBan 96 6))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat363 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur46]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne399 : Ban 96 7 etat363 := viaPerm proj2 proj2 borne398 (by decide +kernel) (by decide +kernel)
def etat364 : List ℕ := [valeur191,valeur47,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne400 : Ban 96 6 etat364 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne401 : Ban 96 5 etat300 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne402 : Ban 96 5 etat317 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne403 : Ban 96 5 etat326 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne404 : Ban 96 6 etat333 := viaBranch (ws := [etat124,etat300,etat63,etat126,etat317,etat128,etat326,etat68]) (consBan borne138 (consBan borne401 (consBan borne75 (consBan borne140 (consBan borne402 (consBan borne142 (consBan borne403 (consBan borne80 (nilBan 96 5))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne405 : Ban 96 6 etat334 := viaPerm proj1 proj1 borne404 (by decide +kernel) (by decide +kernel)
def valeur208 : ℕ := 0x20b83d0f487c3c3bc5c5b1e2200fffffcff80003ffc03ff
def etat365 : List ℕ := [valeur7,valeur2,valeur208,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne406 : Ban 96 6 etat365 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur209 : ℕ := 0x100503000c0c0840c09020000003ff000000007fc0000
def etat366 : List ℕ := [valeur209,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne407 : Ban 96 6 etat366 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur210 : ℕ := 0x2080280840502022840401422007fc00cff8000080000ff
def etat367 : List ℕ := [valeur7,valeur210,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne408 : Ban 96 6 etat367 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur211 : ℕ := 0x100502000c08084080902000000300000000004000300
def etat368 : List ℕ := [valeur211,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne409 : Ban 96 6 etat368 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur212 : ℕ := 0x543d17470a2d1d1d51d1f4b0d00c03ff100403fffffffff
def etat369 : List ℕ := [valeur7,valeur2,valeur3,valeur212,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne410 : Ban 96 6 etat369 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur213 : ℕ := 0x540502400201010410104410d0040000100403fc803fcff
def etat370 : List ℕ := [valeur7,valeur2,valeur213,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne411 : Ban 96 6 etat370 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur214 : ℕ := 0x421f8751ff96cbcbbcfcfb3ac3ff803fff0000003fffff00
def etat371 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur214,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne412 : Ban 96 6 etat371 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur215 : ℕ := 0x381507082c1c1941c1b0a0000803ff000000000000300
def etat372 : List ℕ := [valeur215,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne413 : Ban 96 6 etat372 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur216 : ℕ := 0x421c06018f140a0a28e0e030c3ff00000f0000000803fc00
def etat373 : List ℕ := [valeur7,valeur2,valeur3,valeur216,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne414 : Ban 96 6 etat373 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur217 : ℕ := 0x803ff000000000000000
def etat374 : List ℕ := [valeur217,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne415 : Ban 96 6 etat374 := viaPerm proj10 proj3 borne122 (by decide +kernel) (by decide +kernel)
def valeur218 : ℕ := 0xbde3f97e70e2f1f1971f1bcafffffffff000000037fc0300
def etat375 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur218,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne416 : Ban 96 6 etat375 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur219 : ℕ := 0xbde0782e00603030030300c0ffff7fc00000000000000000
def etat376 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur219,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne417 : Ban 96 6 etat376 := viaDirect (by decide +kernel) (by decide +kernel)
def etat377 : List ℕ := [valeur47,valeur7,valeur2,valeur3,valeur4,valeur5,valeur46]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne418 : Ban 96 6 etat377 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne419 : Ban 96 6 etat363 := viaDirect (by decide +kernel) (by decide +kernel)
def etat378 : List ℕ := [valeur47,valeur2,valeur31,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne420 : Ban 96 6 etat378 := viaDirect (by decide +kernel) (by decide +kernel)
def etat379 : List ℕ := [valeur0,valeur47,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne421 : Ban 96 6 etat379 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur220 : ℕ := 0xf89024090b582c2c028280a0ec0000000d7f803fc0000000
def etat380 : List ℕ := [valeur47,valeur2,valeur3,valeur4,valeur5,valeur220]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne422 : Ban 96 6 etat380 := viaDirect (by decide +kernel) (by decide +kernel)
def etat381 : List ℕ := [valeur47,valeur7,valeur2,valeur3,valeur4,valeur5,valeur220]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne423 : Ban 96 6 etat381 := viaDirect (by decide +kernel) (by decide +kernel)
def etat382 : List ℕ := [valeur47,valeur2,valeur3,valeur4,valeur5,valeur220,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne424 : Ban 96 6 etat382 := viaDirect (by decide +kernel) (by decide +kernel)
def etat383 : List ℕ := [valeur47,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne425 : Ban 96 7 etat383 := viaBranch (ws := [etat364,etat334,etat24,etat365,etat366,etat367,etat368,etat369,etat133,etat370,etat223,etat371,etat372,etat373,etat374,etat375,etat278,etat376,etat377,etat363,etat378,etat379,etat47,etat157,etat380,etat381,etat382]) (consBan borne400 (consBan borne405 (consBan borne36 (consBan borne406 (consBan borne407 (consBan borne408 (consBan borne409 (consBan borne410 (consBan borne147 (consBan borne411 (consBan borne245 (consBan borne412 (consBan borne413 (consBan borne414 (consBan borne415 (consBan borne416 (consBan borne305 (consBan borne417 (consBan borne418 (consBan borne419 (consBan borne420 (consBan borne421 (consBan borne59 (consBan borne171 (consBan borne422 (consBan borne423 (consBan borne424 (nilBan 96 6)))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat384 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur220,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne426 : Ban 96 7 etat384 := viaPerm proj7 proj7 borne425 (by decide +kernel) (by decide +kernel)
def etat385 : List ℕ := [valeur48,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne427 : Ban 96 7 etat385 := viaPerm proj6 proj6 borne253 (by decide +kernel) (by decide +kernel)
def etat386 : List ℕ := [valeur7,valeur2,valeur3,valeur132,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne428 : Ban 96 7 etat386 := viaPerm proj6 proj6 borne286 (by decide +kernel) (by decide +kernel)
def etat387 : List ℕ := [valeur7,valeur49,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne429 : Ban 96 7 etat387 := viaPerm proj3 proj10 borne315 (by decide +kernel) (by decide +kernel)
def etat388 : List ℕ := [valeur7,valeur2,valeur133,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne430 : Ban 96 7 etat388 := viaPerm proj2 proj2 borne315 (by decide +kernel) (by decide +kernel)
def valeur221 : ℕ := 0x20802008404020228404010020000000c00000038000000
def etat389 : List ℕ := [valeur7,valeur221,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne431 : Ban 96 7 etat389 := viaPerm proj3 proj10 borne40 (by decide +kernel) (by decide +kernel)
def etat390 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur39,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne432 : Ban 96 7 etat390 := viaPerm proj5 proj9 borne94 (by decide +kernel) (by decide +kernel)
def valeur222 : ℕ := 0x28180408301011010120c2000ffc000ff8000000003ff
def etat391 : List ℕ := [valeur222,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne433 : Ban 96 7 etat391 := viaPerm proj6 proj6 borne172 (by decide +kernel) (by decide +kernel)
def etat392 : List ℕ := [valeur7,valeur2,valeur3,valeur122,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne434 : Ban 96 7 etat392 := viaPerm proj5 proj9 borne172 (by decide +kernel) (by decide +kernel)
def etat393 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur190,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne435 : Ban 96 7 etat393 := viaPerm proj4 proj4 borne398 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne436 : Ban 96 7 etat309 := viaPerm proj3 proj10 borne425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne437 : Ban 96 7 etat324 := viaPerm proj1 proj1 borne425 (by decide +kernel) (by decide +kernel)
def valeur223 : ℕ := 0x200000000cff800000000000
def etat394 : List ℕ := [valeur223,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne438 : Ban 96 7 etat394 := viaPerm proj3 proj10 borne253 (by decide +kernel) (by decide +kernel)
def valeur224 : ℕ := 0xfa9aa789cfdf2f2f3ad2d2bcfe00ffc00ffffffff80003ff
def etat395 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur224]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne439 : Ban 96 7 etat395 := viaPerm proj3 proj10 borne286 (by decide +kernel) (by decide +kernel)
def valeur225 : ℕ := 0x20a8380c48703033850521c0200ffc000000000380003ff
def etat396 : List ℕ := [valeur7,valeur225,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne440 : Ban 96 7 etat396 := viaPerm proj6 proj6 borne315 (by decide +kernel) (by decide +kernel)
def valeur226 : ℕ := 0xf89024090b582c2c028280a0dc00000003007fffc0000000
def etat397 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur226,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne441 : Ban 96 7 etat397 := viaPerm proj7 proj7 borne315 (by decide +kernel) (by decide +kernel)
def etat398 : List ℕ := [valeur198,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne442 : Ban 96 7 etat398 := viaPerm proj3 proj10 borne369 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne443 : Ban 96 7 etat351 := viaPerm proj2 proj2 borne425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne444 : Ban 96 7 etat348 := viaPerm proj5 proj9 borne425 (by decide +kernel) (by decide +kernel)
def valeur227 : ℕ := 0x540502400201010010100400d0040300000000000000000
def etat399 : List ℕ := [valeur7,valeur2,valeur227,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne445 : Ban 96 7 etat399 := viaPerm proj2 proj2 borne40 (by decide +kernel) (by decide +kernel)
def etat400 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur56,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne446 : Ban 96 7 etat400 := viaPerm proj1 proj1 borne94 (by decide +kernel) (by decide +kernel)
def etat401 : List ℕ := [valeur57,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne447 : Ban 96 7 etat401 := viaPerm proj10 proj3 borne172 (by decide +kernel) (by decide +kernel)
def etat402 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur87,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne448 : Ban 96 7 etat402 := viaPerm proj1 proj1 borne172 (by decide +kernel) (by decide +kernel)
def valeur228 : ℕ := 0xc0000000100403fc0000000
def etat403 : List ℕ := [valeur228,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne449 : Ban 96 7 etat403 := viaPerm proj2 proj2 borne253 (by decide +kernel) (by decide +kernel)
def etat404 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur58]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne450 : Ban 96 7 etat404 := viaPerm proj2 proj2 borne286 (by decide +kernel) (by decide +kernel)
def etat405 : List ℕ := [valeur7,valeur2,valeur59,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne451 : Ban 96 7 etat405 := viaPerm proj10 proj3 borne315 (by decide +kernel) (by decide +kernel)
def valeur229 : ℕ := 0xf89024090b582c2c028280a0f00000000effbfc000000000
def etat406 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur229,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne452 : Ban 96 7 etat406 := viaPerm proj11 proj11 borne315 (by decide +kernel) (by decide +kernel)
def valeur230 : ℕ := 0xc3ff00000000000000000000
def etat407 : List ℕ := [valeur230,valeur7,valeur2,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne453 : Ban 96 7 etat407 := viaPerm proj1 proj1 borne253 (by decide +kernel) (by decide +kernel)
def etat408 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur145]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne454 : Ban 96 7 etat408 := viaPerm proj1 proj1 borne286 (by decide +kernel) (by decide +kernel)
def etat409 : List ℕ := [valeur7,valeur2,valeur3,valeur146,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne455 : Ban 96 7 etat409 := viaPerm proj8 proj8 borne315 (by decide +kernel) (by decide +kernel)
def valeur231 : ℕ := 0xbde0782e00603030030300c03c00fffff000000000000000
def etat410 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur231,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne456 : Ban 96 7 etat410 := viaPerm proj9 proj5 borne315 (by decide +kernel) (by decide +kernel)
def valeur232 : ℕ := 0x401004010b10080800808020c00000000f00000000000000
def etat411 : List ℕ := [valeur7,valeur2,valeur3,valeur232,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne457 : Ban 96 7 etat411 := viaPerm proj5 proj9 borne40 (by decide +kernel) (by decide +kernel)
def etat412 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur147]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne458 : Ban 96 7 etat412 := viaPerm proj7 proj7 borne94 (by decide +kernel) (by decide +kernel)
def etat413 : List ℕ := [valeur7,valeur2,valeur148,valeur3,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne459 : Ban 96 7 etat413 := viaPerm proj8 proj8 borne172 (by decide +kernel) (by decide +kernel)
def valeur233 : ℕ := 0xb880200800482424020200803c00000000ffffffc0000000
def etat414 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur233,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne460 : Ban 96 7 etat414 := viaPerm proj7 proj7 borne172 (by decide +kernel) (by decide +kernel)
def valeur234 : ℕ := 0xb88020080040202002020080fc0000000000000000000000
def etat415 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur234,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne461 : Ban 96 7 etat415 := viaPerm proj1 proj1 borne40 (by decide +kernel) (by decide +kernel)
def valeur235 : ℕ := 0xfdf07c2f0b783c3c038380e0ffffffffffffffffc0000000
def etat416 : List ℕ := [valeur7,valeur2,valeur3,valeur4,valeur5,valeur6,valeur235]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne462 : Ban 96 7 etat416 := viaPerm proj9 proj5 borne94 (by decide +kernel) (by decide +kernel)
def valeur236 : ℕ := 0x5605826002010100101004003fffffff000000000000000
def etat417 : List ℕ := [valeur7,valeur2,valeur3,valeur236,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne463 : Ban 96 7 etat417 := viaPerm proj9 proj5 borne172 (by decide +kernel) (by decide +kernel)
def valeur237 : ℕ := 0x401004010b180c0c00808020000000000fffffffc0000000
def etat418 : List ℕ := [valeur7,valeur2,valeur3,valeur237,valeur4,valeur5,valeur6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne464 : Ban 96 7 etat418 := viaPerm proj11 proj11 borne172 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne465 : Ban 96 8 etat217 := viaBranch (ws := [etat28,etat83,etat1,etat3,etat85,etat82,etat54,etat35,etat230,etat263,etat159,etat203,etat265,etat275,etat288,etat289,etat334,etat363,etat383,etat384,etat385,etat386,etat387,etat388,etat389,etat390,etat391,etat392,etat333,etat393,etat309,etat324,etat394,etat395,etat396,etat397,etat398,etat362,etat351,etat348,etat399,etat400,etat401,etat402,etat403,etat404,etat405,etat406,etat407,etat408,etat409,etat410,etat411,etat412,etat413,etat414,etat415,etat416,etat417,etat418]) (consBan borne40 (consBan borne95 (consBan borne173 (consBan borne174 (consBan borne175 (consBan borne94 (consBan borne172 (consBan borne176 (consBan borne253 (consBan borne286 (consBan borne316 (consBan borne317 (consBan borne318 (consBan borne319 (consBan borne315 (consBan borne320 (consBan borne370 (consBan borne399 (consBan borne425 (consBan borne426 (consBan borne427 (consBan borne428 (consBan borne429 (consBan borne430 (consBan borne431 (consBan borne432 (consBan borne433 (consBan borne434 (consBan borne369 (consBan borne435 (consBan borne436 (consBan borne437 (consBan borne438 (consBan borne439 (consBan borne440 (consBan borne441 (consBan borne442 (consBan borne398 (consBan borne443 (consBan borne444 (consBan borne445 (consBan borne446 (consBan borne447 (consBan borne448 (consBan borne449 (consBan borne450 (consBan borne451 (consBan borne452 (consBan borne453 (consBan borne454 (consBan borne455 (consBan borne456 (consBan borne457 (consBan borne458 (consBan borne459 (consBan borne460 (consBan borne461 (consBan borne462 (consBan borne463 (consBan borne464 (nilBan 96 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne466 : Wide 96 8 etat217 := widen (by decide +kernel) borne465
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj467 : Projection 97 96 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] rfl (by decide +kernel) (by decide)
def valeur238 : ℕ := 0xa82a0e84041a1218a121a860d0040300100403fcc03ffff
def valeur239 : ℕ := 0x702a0e1058383283836141000803ff2807fc037fc0300
def valeur240 : ℕ := 0x1000000000000000000000000
def valeur241 : ℕ := 0x4150701890e060670a0a4382200ffc00cff8000380003ff
def valeur242 : ℕ := 0x84380c031e28141451c1c060c3ff00000f0000003ffffc00
def valeur243 : ℕ := 0x1f120481216b0585805050140fc0000000fffffffc0000000
def valeur244 : ℕ := 0x37bc0f05c00c0606006060181fffffffff000000000000000
def etat419 : List ℕ := [valeur238,valeur239,valeur240,valeur241,valeur242,valeur243,valeur244]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne468 : Ban 97 9 etat419 := viaCut proj467 borne466 (by decide +kernel) (by decide +kernel) (by decide +kernel)

def neuf : List Gate := [⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.and,[7,8]⟩,⟨.or,[0,5]⟩,⟨.and,[3,10]⟩,⟨.or,[1,2]⟩,⟨.or,[3,4]⟩,⟨.or,[12,13]⟩,⟨.and,[14,6]⟩,⟨.or,[9,11]⟩,⟨.or,[16,15]⟩]
theorem neuf_ok : ∀ g ∈ neuf, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [neuf,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
theorem neuf_calc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨neuf,17⟩ (List.ofFn x) = graph x := by decide +kernel

theorem lt_count {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

end PEqualNP.Outside.L_meta_11225

open PEqualNP.Outside.L_meta_11225 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_11225 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hfan _ he
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have fan : FanInTwo ⟨gs,o⟩ := fun g hg => ⟨(hfan g hg).1,(hfan g hg).2⟩
    obtain ⟨k,kle,live⟩ := trace ⟨gs,o⟩ fan (funext he)
    have huit : 10 ≤ k := by
      by_contra! small
      exact borne468 k (by omega) live
    have less := lt_count hn
    change k ≤ gs.countP counted at kle
    exact ⟨neuf,17,neuf_ok,by change 11 ≤ gs.length; omega,neuf_calc⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hg
    exact ⟨(hfan g hg).1.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),(hfan g hg).2⟩
