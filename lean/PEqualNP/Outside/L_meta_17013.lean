import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17013.Support

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

theorem smallByCut {m h f t : Nat} {v w : List Nat} (p : Projection m h) (bound : Wide h t w)
    (nd : v.Nodup := by decide) (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w := by decide +kernel)
    (cost : f≤t+(v.map p.toFun).count 0 := by decide +kernel) : Ban m f v :=
  viaCut p bound nd mem cost

theorem solid {m f : Nat} {v : List Nat} (bound : Ban m f v)
    (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a := by decide +kernel) :
    Wide m f v := widen ess bound

theorem bySubset {m f t : Nat} {v w : List Nat} (bound : Wide m t w)
    (sub : ∀ a∈v, a∈w := by decide +kernel) (le : f≤t := by decide) : Ban m f v := by
  intro j h hb
  exact bound ⟨j,v.toFinset,h.trans le,hb,fun x hx => sub x (List.mem_toFinset.mp hx)⟩

theorem checkedSmall {m f : Nat} {v : List Nat} (ex : search m f v = false := by decide +kernel)
    (nd : v.Nodup := by decide) : Ban m f v := viaSmall ex nd

def t0 := 0x10a08599114433e19f993
def t1 := 0x1845822c0b42b8cd866c1fc
def t2 := 0x4c10a085020acc30e1870e1f
def t3 := 0xb02b01580d40f03f01f80fe0
def t4 := 0xfec001f7a000ffc001fff000
def t5 := 0xff7ef4000000fffffe000000
def v0 := [t0,t1,t2,t3,t4,t5]
def t6 := 0x800409000001800c190
def v1 := [t6,t0,t1,t2,t3,t4,t5]
def t7 := 0x14f
def t8 := 0x4b3
def t9 := 0xa3c
def v2 := [t7,t8,t9]
def p63_14 : Projection 48 6 := pick [2,3,5,6,9,10] rfl (by decide +kernel) (by decide)
def t10 := 0x1855a2ad9b53fcffe7ff9ff
def v3 := [t0,t1,t10,t2,t3,t4,t5]
def v4 := [t6,t10,t2,t3,t4,t5]
def v5 := [t6,t0,t10,t2,t3,t4,t5]
def v6 := [t6,t1,t10,t2,t3,t4,t5]
def t11 := 0x102081901144326193803
def v7 := [t11,t0,t10,t2,t3,t4,t5]
def t12 := 0x184502280242b8cc066006c
def v8 := [t12,t1,t10,t2,t3,t4,t5]
def v9 := [t0,t12,t1,t2,t3,t4,t5]
def t13 := 0x4c11aa8d5b9bdc73ff9fff9f
def v10 := [t1,t10,t2,t13,t3,t4,t5]
def t14 := 0x10a08599110431e18f180
def v11 := [t14,t1,t10,t2,t3,t4,t5]
def t15 := 0xb02b0b585dd1f47f3ff9fff3
def v12 := [t1,t10,t2,t3,t15,t4,t5]
def t16 := 0xa00509104403e01f013
def v13 := [t16,t1,t10,t2,t3,t4,t5]
def v14 := [t11,t0,t1,t2,t3,t4,t5]
def t17 := 0x4d94f8a7c2beefbcf9e7cfff
def v15 := [t0,t10,t2,t17,t3,t4,t5]
def t18 := 0x1845822c0b4238c1860c1e0
def v16 := [t0,t18,t10,t2,t3,t4,t5]
def t19 := 0x200c006001e0
def v17 := [t19,t0,t10,t2,t3,t4,t5]
def t20 := 0xb02b01580d40d03301980e00
def v18 := [t0,t10,t2,t20,t3,t4,t5]
def t21 := 0xffc459f7e0b4ffccd9fff1fc
def v19 := [t0,t10,t2,t3,t4,t5,t21]
def t22 := 0x104580040b4000cd80001fc
def v20 := [t0,t22,t10,t2,t3,t4,t5]
def t23 := 0xfffefc22c0b4fffffe66c1fc
def v21 := [t0,t10,t2,t3,t4,t5,t23]
def t24 := 0x800822c0b400000066c1fc
def v22 := [t0,t24,t10,t2,t3,t4,t5]
def t25 := 0xc00e007081f
def v23 := [t25,t0,t1,t2,t3,t4,t5]
def t26 := 0x4d95faafdbbfffffffffffff
def v24 := [t0,t1,t2,t26,t3,t4,t5]
def t27 := 0x1855a2ad9b533cf1e78f1e0
def v25 := [t0,t1,t27,t2,t3,t4,t5]
def t28 := 0x4c10a085020ac03001800600
def v26 := [t0,t1,t28,t2,t3,t4,t5]
def t29 := 0x100080900300f007809e0
def v27 := [t29,t0,t1,t2,t3,t4,t5]
def t30 := 0xb1af5b7addf5ffffffffffff
def v28 := [t0,t1,t2,t3,t30,t4,t5]
def t31 := 0x1845a22d0b50fc0fe07f01f
def v29 := [t0,t1,t31,t2,t3,t4,t5]
def t32 := 0xb02a01500440c03001800600
def v30 := [t0,t1,t2,t32,t3,t4,t5]
def t33 := 0x80002280003fc0007ff000
def v31 := [t0,t33,t1,t2,t3,t5]
def v32 := [t0,t33,t1,t10,t2,t3,t5]
def v33 := [t0,t33,t1,t2,t3,t4,t5]
def t34 := 0xffc55bfff9b5ffcffffff9ff
def v34 := [t0,t1,t2,t3,t4,t5,t34]
def t35 := 0x1055a0859b5000ffe0009ff
def v35 := [t0,t35,t1,t2,t3,t5]
def v36 := [t0,t35,t1,t10,t2,t3,t5]
def v37 := [t0,t35,t1,t2,t3,t4,t5]
def t36 := 0xfe4001d52000c00001800000
def v38 := [t0,t1,t2,t3,t36,t4,t5]
def t37 := 0x104500000003fcffe000000
def v39 := [t0,t37,t1,t2,t3,t4]
def v40 := [t0,t37,t1,t10,t2,t3,t4]
def v41 := [t0,t37,t1,t2,t3,t4,t5]
def t38 := 0xfffffe2ad9b5fffffe7ff9ff
def v42 := [t0,t1,t2,t3,t4,t5,t38]
def t39 := 0x810a2ad9b50000007ff9ff
def v43 := [t0,t39,t1,t2,t3,t4]
def v44 := [t0,t39,t1,t10,t2,t3,t4]
def v45 := [t0,t39,t1,t2,t3,t4,t5]
def t40 := 0xfe7aa4000000c03000000000
def v46 := [t0,t1,t2,t3,t40,t4,t5]
def t41 := 0xfed0a1f7a20afff0e1fffe1f
def v47 := [t0,t1,t10,t2,t3,t41,t5]
def t42 := 0xb2c00172a00033c00078f000
def v48 := [t0,t1,t10,t2,t3,t42,t5]
def t43 := 0xff7ef485020affffff870e1f
def v49 := [t0,t1,t10,t2,t3,t4,t43]
def t44 := 0xb36e5400000033cf1e000000
def v50 := [t0,t1,t10,t2,t3,t44,t4]
def t45 := 0x10b32219f993
def t46 := 0x45816866c1fc
def t47 := 0x10a0415870e1f
def t48 := 0x2b01a81f80fe0
def t49 := 0x3ef4001fff000
def v51 := [t45,t46,t47,t48,t49]
def t50 := 0x812000c190
def v52 := [t50,t45,t46,t47,t48,t49]
def t51 := 0x55b36a7ff9ff
def v53 := [t45,t46,t51,t47,t48,t49]
def t52 := 0x103202193803
def v54 := [t52,t45,t46,t47,t48,t49]
def t53 := 0x45004866006c
def v55 := [t45,t53,t46,t47,t48,t49]
def t54 := 0x10813
def v56 := [t54,t45,t46,t47,t48,t49]
def t55 := 0x11ab7379fff9f
def v57 := [t45,t46,t47,t55,t48,t49]
def t56 := 0x10b32218f180
def v58 := [t56,t45,t46,t47,t48,t49]
def t57 := 0x10a041586060c
def v59 := [t45,t46,t57,t47,t48,t49]
def t58 := 0x101200180980
def v60 := [t58,t45,t46,t47,t48,t49]
def t59 := 0x2b0bba3f9fff3
def v61 := [t45,t46,t47,t48,t59,t49]
def t60 := 0xa12201f013
def v62 := [t60,t45,t46,t47,t48,t49]
def t61 := 0x2a00881e00660
def v63 := [t45,t46,t47,t61,t48,t49]
def t62 := 0x19f000
def v64 := [t62,t45,t46,t47,t48]
def v65 := [t62,t45,t46,t47,t48,t49]
def t63 := 0x3fff323fff993
def v66 := [t45,t46,t47,t48,t49,t63]
def t64 := 0x10b322000993
def v67 := [t64,t45,t46,t47,t48]
def v68 := [t64,t45,t46,t47,t48,t49]
def t65 := 0x3ef4001e60000
def v69 := [t45,t46,t47,t48,t65,t49]
def t66 := 0x6001c
def v70 := [t66,t45,t46,t47,t48,t49]
def t67 := 0x14f857de7cfff
def v71 := [t45,t46,t47,t67,t48,t49]
def t68 := 0x45816860c1e0
def v72 := [t45,t68,t46,t47,t48,t49]
def t69 := 0x10a0415810e03
def v73 := [t45,t46,t69,t47,t48,t49]
def t70 := 0x6001e0
def v74 := [t70,t45,t46,t47,t48,t49]
def t71 := 0x2f59be9fecffc
def v75 := [t45,t46,t47,t48,t71,t49]
def t72 := 0x45816806c01c
def v76 := [t45,t72,t46,t47,t48,t49]
def t73 := 0x2b01a81980e00
def v77 := [t45,t46,t47,t73,t48,t49]
def t74 := 0x45000066c000
def v78 := [t45,t74,t46,t47,t48,t49]
def t75 := 0x3efc169fff1fc
def v79 := [t45,t46,t47,t48,t49,t75]
def t76 := 0x81680001fc
def v80 := [t76,t45,t46,t47,t48,t49]
def t77 := 0x3aa4001993000
def v81 := [t45,t46,t47,t48,t77,t49]
def t78 := 0x1800e00
def v82 := [t78,t45,t46,t47,t48,t49]
def t79 := 0x3ba1e95ff0fff
def v83 := [t45,t46,t47,t48,t79,t49]
def t80 := 0x10a041407001f
def v84 := [t45,t46,t80,t47,t48,t49]
def t81 := 0x2b01a807801e0
def v85 := [t45,t46,t47,t81,t48,t49]
def t82 := 0x10a0001870000
def v86 := [t45,t46,t82,t47,t48,t49]
def t83 := 0x3ef4415fffe1f
def v87 := [t45,t46,t47,t48,t83]
def v88 := [t45,t46,t47,t48,t49,t83]
def t84 := 0x414000e1f
def v89 := [t84,t45,t46,t47,t48,t49]
def t85 := 0x2e5400078f000
def v90 := [t45,t46,t47,t48,t85]
def v91 := [t45,t46,t47,t48,t85,t49]
def t86 := 0x2a00001f80000
def v92 := [t45,t46,t47,t86,t48,t49]
def t87 := 0x3ff5a81ffffe0
def v93 := [t45,t46,t47,t48,t49,t87]
def t88 := 0x101a80000fe0
def v94 := [t88,t45,t46,t47,t48,t49]
def t89 := 0x14f400007f000
def v95 := [t45,t46,t47,t89,t48,t49]
def v96 := [t53,t46,t51,t47,t48,t49]
def v97 := [t50,t45,t53,t47,t48,t49]
def v98 := [t52,t53,t47,t48,t49]
def v99 := [t52,t45,t53,t47,t48,t49]
def v100 := [t52,t53,t46,t47,t48,t49]
def v101 := [t62,t45,t53,t46,t47,t48]
def v102 := [t64,t45,t53,t46,t47,t48]
def t90 := 0x6000c
def v103 := [t90,t45,t46,t47,t48,t49]
def t91 := 0x14f045de70e7f
def v104 := [t45,t46,t47,t91,t48,t49]
def t92 := 0x450048600060
def v105 := [t45,t92,t46,t47,t48,t49]
def t93 := 0x10a0415810e13
def v106 := [t45,t46,t93,t47,t48,t49]
def t94 := 0x600060
def v107 := [t94,t45,t46,t47,t48,t49]
def t95 := 0x2f51ac9fe0fec
def v108 := [t45,t46,t47,t48,t95,t49]
def t96 := 0x45004806000c
def v109 := [t45,t96,t46,t47,t48,t49]
def t97 := 0x2b01a81980f80
def v110 := [t45,t46,t47,t97,t48,t49]
def t98 := 0x450000660000
def v111 := [t45,t98,t46,t47,t48,t49]
def t99 := 0x3ef4049fff06c
def v112 := [t45,t46,t47,t48,t99]
def v113 := [t45,t53,t46,t47,t48,t99]
def v114 := [t45,t46,t47,t48,t49,t99]
def t100 := 0x4800006c
def v115 := [t100,t45,t46,t47,t48,t49]
def t101 := 0x3aa400199f000
def v116 := [t45,t46,t47,t48,t101]
def v117 := [t45,t53,t46,t47,t48,t101]
def v118 := [t45,t46,t47,t48,t101,t49]
def v119 := [t45,t53,t47,t67,t48,t49]
def v120 := [t45,t53,t68,t47,t48,t49]
def v121 := [t70,t45,t53,t47,t48,t49]
def v122 := [t45,t53,t47,t73,t48,t49]
def v123 := [t45,t53,t47,t48,t49,t75]
def v124 := [t76,t45,t53,t47,t48,t49]
def v125 := [t45,t53,t46,t47,t48,t83]
def v126 := [t45,t53,t46,t47,t48,t85]
def p63_31 : Projection 48 25 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24] rfl (by decide +kernel) (by decide)
def t102 := 0x40020010813
def v127 := [t102,t0,t1,t2,t3,t4,t5]
def v128 := [t0,t1,t2,t13,t3,t4,t5]
def v129 := [t46,t51,t47,t55,t48,t49]
def v130 := [t52,t46,t47,t55,t48,t49]
def v131 := [t54,t46,t55,t48,t49]
def v132 := [t54,t45,t46,t55,t48,t49]
def v133 := [t54,t46,t47,t55,t48,t49]
def v134 := [t56,t45,t46,t55,t48,t49]
def v135 := [t46,t57,t47,t55,t48,t49]
def v136 := [t46,t47,t55,t48,t59,t49]
def v137 := [t60,t46,t47,t55,t48,t49]
def v138 := [t62,t45,t46,t47,t55,t48]
def v139 := [t64,t45,t46,t47,t55,t48]
def t103 := 0x812006c19c
def v140 := [t103,t45,t46,t47,t48,t49]
def t104 := 0x15fb77fffffff
def v141 := [t45,t46,t47,t104,t48,t49]
def t105 := 0x11a3617993e03
def v142 := [t45,t46,t47,t105,t48,t49]
def v143 := [t45,t46,t55,t48,t83]
def v144 := [t45,t46,t47,t55,t48,t83]
def v145 := [t45,t46,t55,t48,t49,t83]
def v146 := [t84,t45,t46,t55,t48,t49]
def v147 := [t45,t46,t47,t55,t48,t85]
def t106 := 0x101201980f80
def v148 := [t106,t45,t46,t47,t48,t49]
def t107 := 0x3babfb7ffffff
def v149 := [t45,t46,t47,t48,t107,t49]
def t108 := 0x10aa53607f01f
def v150 := [t45,t46,t47,t108,t48,t49]
def t109 := 0x2a00880600060
def v151 := [t45,t46,t47,t109,t48,t49]
def t110 := 0x10a00019ff000
def v152 := [t45,t46,t110,t47,t48]
def v153 := [t45,t46,t110,t47,t55,t48]
def v154 := [t45,t46,t110,t47,t48,t49]
def t111 := 0x3fff737ffff9f
def v155 := [t45,t46,t47,t48,t49,t111]
def t112 := 0x10b736000f9f
def v156 := [t45,t112,t46,t47,t48]
def v157 := [t45,t112,t46,t47,t55,t48]
def v158 := [t45,t112,t46,t47,t48,t49]
def t113 := 0x2e54000600000
def v159 := [t45,t46,t47,t48,t113,t49]
def v160 := [t14,t0,t1,t2,t3,t4,t5]
def t114 := 0x4c10a085020ac830c186060c
def v161 := [t0,t1,t114,t2,t3,t4,t5]
def t120 := 0x100080900100300180980
def v163 := [t120,t0,t1,t2,t3,t4,t5]
def v164 := [t0,t1,t2,t3,t15,t4,t5]
def t121 := 0xa16289f3f3
def t122 := 0x658b2976cd9c
def t123 := 0x30a1415870e1f
def t124 := 0x3b01e81f80fe0
def t125 := 0x3df4001fff000
def v165 := [t121,t122,t123,t124,t125]
def v166 := [t50,t121,t122,t123,t124,t125]
def t126 := 0x65ab6bffffff
def v167 := [t121,t126,t123,t124,t125]
def v168 := [t121,t122,t126,t123,t124,t125]
def t127 := 0x2042893263
def v169 := [t127,t121,t122,t123,t124,t125]
def t128 := 0x650a09760c0c
def v170 := [t121,t128,t123,t124,t125]
def v171 := [t121,t128,t122,t123,t124,t125]
def t129 := 0x810213
def v172 := [t129,t121,t122,t123,t124,t125]
def t130 := 0x30ab5778fffff
def v173 := [t121,t122,t123,t130,t124,t125]
def t131 := 0xa16208f1e0
def v174 := [t131,t121,t122,t123,t124,t125]
def t132 := 0x30a1415060c0c
def v175 := [t121,t122,t132,t123,t124,t125]
def t133 := 0x8803e0
def v176 := [t133,t121,t122,t123,t124,t125]
def t134 := 0x3b0bfe3f9fff3
def v177 := [t121,t122,t123,t124,t134,t125]
def t135 := 0xa16201f013
def v178 := [t135,t121,t122,t123,t124,t125]
def t136 := 0x3b01e81700c00
def v179 := [t121,t122,t123,t136,t124,t125]
def t137 := 0x89f000
def v180 := [t137,t121,t122,t123,t124,t125]
def t138 := 0x3dfe163fff3f3
def v181 := [t121,t122,t123,t124,t125,t138]
def t139 := 0xa1620003f3
def v182 := [t139,t121,t122,t123,t124,t125]
def t140 := 0x3df4001760000
def v183 := [t121,t122,t123,t124,t140,t125]
def t141 := 0x1060c1c
def v184 := [t141,t121,t122,t123,t124,t125]
def t142 := 0x36f9f3df7cf9f
def v185 := [t121,t122,t123,t142,t124,t125]
def t143 := 0x658b2870c180
def v186 := [t121,t143,t122,t123,t124,t125]
def t144 := 0x30a1414810203
def v187 := [t121,t122,t144,t123,t124,t125]
def t145 := 0x200a01700d80
def v188 := [t121,t145,t122,t123,t124,t125]
def t146 := 0x3f59fa9fecffc
def v189 := [t121,t122,t123,t124,t125,t146]
def t147 := 0x45812806c01c
def v190 := [t121,t147,t122,t123,t124,t125]
def t148 := 0x3901480880260
def v191 := [t121,t122,t123,t148,t124,t125]
def t149 := 0x45000176c000
def v192 := [t121,t149,t122,t123,t124,t125]
def t150 := 0x3ffcb29fffd9c
def v193 := [t121,t122,t123,t124,t125,t150]
def t151 := 0x208b28000d9c
def v194 := [t121,t151,t122,t123,t124,t125]
def t152 := 0x39a4000893000
def v195 := [t121,t122,t123,t152,t124,t125]
def t153 := 0x3001401800e00
def v196 := [t121,t122,t153,t123,t124,t125]
def v197 := [t121,t122,t123,t79,t125]
def v198 := [t121,t122,t123,t124,t79,t125]
def t154 := 0xa001407001f
def v199 := [t121,t154,t122,t123,t124,t125]
def t155 := 0xb00a807801e0
def v200 := [t121,t122,t155,t123,t125]
def v201 := [t121,t122,t155,t123,t124,t125]
def t156 := 0x30a0001870000
def v202 := [t121,t122,t156,t123,t124,t125]
def t157 := 0x3df5415fffe1f
def v203 := [t121,t122,t123,t124,t157]
def v204 := [t121,t122,t123,t124,t125,t157]
def t158 := 0x1414000e1f
def v205 := [t158,t121,t122,t123,t124,t125]
def t159 := 0xd5400078f000
def v206 := [t121,t122,t159,t123,t124]
def v207 := [t121,t122,t159,t123,t124,t125]
def t160 := 0x3900001f80000
def v208 := [t121,t122,t123,t160,t124,t125]
def t161 := 0x3ff5e81ffffe0
def v209 := [t121,t122,t123,t124,t125,t161]
def t162 := 0x201e80000fe0
def v210 := [t121,t162,t122,t123,t124,t125]
def t163 := 0x4f400007f000
def v211 := [t121,t163,t122,t123,t124,t125]
def p63_55 : Projection 48 25 := pick [0,1,2,3,4,12,13,14,15,16,17,18,25,26,27,28,29,30,31,38,39,40,41,42,43] rfl (by decide +kernel) (by decide)
def v212 := [t16,t0,t1,t2,t3,t4,t5]
def t164 := 0xb02a01500440e03c01e00660
def v213 := [t0,t1,t2,t164,t3,t4,t5]
def t165 := 0x551ff
def t166 := 0x6ccecc
def t167 := 0xb0af0f
def t168 := 0xda0ff0
def v214 := [t165,t166,t167,t168]
def p63_51 : Projection 48 12 := pick [12,13,14,15,25,26,27,28,38,39,40,41] rfl (by decide +kernel) (by decide)
def t169 := 0x14400019f000
def v215 := [t169,t0,t1,t2,t3,t4,t5]
def t170 := 0xfec10bfff991ffc33ffff993
def v216 := [t0,t1,t2,t3,t4,t170,t5]
def t171 := 0x10a08599100033e000993
def v217 := [t171,t0,t1,t2,t3,t4,t5]
def t172 := 0x10a08599100000019f993
def v218 := [t172,t0,t1,t2,t3,t4,t5]
def map63_1 : Projection 48 48 := pick [0,1,2,3,4,5,6,7,8,9,10,11,25,26,27,28,29,30,31,32,33,34,35,36,37,12,13,14,15,16,17,18,19,20,21,22,23,24,38,40,39,41,42,43,44,45,46,47] rfl (by decide +kernel) (by decide)
def t173 := 0xfec001f7a000eb8001e60000
def v219 := [t0,t1,t2,t3,t173,t4,t5]
def t174 := 0x14433e000000
def v220 := [t174,t0,t1,t2,t3,t4,t5]
def t175 := 0xff7ffe085991fffffe19f993
def v221 := [t0,t1,t2,t3,t4,t5,t175]
def t176 := 0xff7ef4000000ebbcc0000000
def v222 := [t0,t1,t2,t3,t4,t176,t5]
def t177 := 0x800c006001c
def v223 := [t177,t0,t1,t2,t3,t4,t5]
def v224 := [t0,t1,t2,t17,t3,t4,t5]
def v225 := [t121,t126,t123,t142,t124,t125]
def v226 := [t121,t128,t123,t142,t124,t125]
def t178 := 0x812081c393
def v227 := [t178,t121,t122,t123,t124,t125]
def t179 := 0x36fbf7fffffff
def v228 := [t121,t122,t123,t179,t124,t125]
def t180 := 0x2042083060
def v229 := [t180,t121,t122,t123,t124,t125]
def t181 := 0x36f1e1d760c0c
def v230 := [t121,t122,t123,t181,t124,t125]
def v231 := [t141,t121,t142,t124,t125]
def v232 := [t141,t121,t122,t142,t124,t125]
def v233 := [t141,t121,t123,t142,t124,t125]
def v234 := [t121,t143,t122,t142,t124,t125]
def v235 := [t121,t144,t123,t142,t124,t125]
def v236 := [t121,t122,t123,t142,t79,t125]
def v237 := [t121,t122,t155,t123,t142,t125]
def v238 := [t121,t122,t123,t142,t124,t157]
def v239 := [t121,t122,t159,t123,t142,t124]
def t182 := 0x3201e01f00f80
def v240 := [t121,t122,t123,t182,t124,t125]
def t183 := 0x3ff9fbdffcfff
def v241 := [t121,t122,t123,t124,t125,t183]
def t184 := 0x4f813c07c01f
def v242 := [t121,t184,t122,t123,t124,t125]
def t185 := 0x900080080060
def v243 := [t121,t122,t185,t123,t124,t125]
def t186 := 0x34f0001f7c000
def v244 := [t121,t122,t123,t186,t124,t125]
def t187 := 0x3ffdf3dffff9f
def v245 := [t121,t122,t123,t124,t125,t187]
def t188 := 0x209f3c000f9f
def v246 := [t121,t188,t122,t123,t124,t125]
def t189 := 0x904000083000
def v247 := [t121,t122,t189,t123,t124,t125]
def v248 := [t0,t18,t1,t2,t3,t4,t5]
def t190 := 0x812000c180
def v249 := [t190,t45,t46,t47,t48,t49]
def t191 := 0x55b36a79f9f3
def v250 := [t45,t46,t191,t47,t48,t49]
def t192 := 0x103202193813
def v251 := [t192,t45,t46,t47,t48,t49]
def v252 := [t45,t68,t51,t47,t48,t49]
def v253 := [t62,t45,t68,t46,t47,t48]
def v254 := [t64,t45,t68,t46,t47,t48]
def v255 := [t66,t45,t68,t47,t48,t49]
def v256 := [t45,t68,t46,t67,t48,t49]
def t193 := 0x2f59be9f8cfe0
def v257 := [t45,t46,t47,t48,t193,t49]
def t194 := 0x45816800c000
def v258 := [t45,t194,t46,t47,t48,t49]
def t195 := 0x45000060c000
def v259 := [t45,t195,t46,t47,t48,t49]
def t196 := 0x3efc169fff1e0
def v260 := [t45,t46,t47,t48,t49,t196]
def t197 := 0x81680001e0
def v261 := [t197,t45,t46,t47,t48,t49]
def t198 := 0x3aa40019f3000
def v262 := [t45,t46,t47,t48,t198,t49]
def v263 := [t45,t68,t69,t48,t49]
def v264 := [t45,t68,t46,t69,t48,t49]
def v265 := [t45,t68,t69,t47,t48,t49]
def v266 := [t45,t68,t47,t48,t71,t49]
def v267 := [t45,t72,t68,t47,t48,t49]
def v268 := [t45,t68,t46,t47,t48,t83]
def v269 := [t45,t68,t46,t47,t48,t85]
def t199 := 0x4c10a085020ac43021810e03
def v270 := [t0,t1,t199,t2,t3,t4,t5]
def v271 := [t19,t0,t1,t2,t3,t4,t5]
def t200 := 0xb1af597acdf4fbbfd9fecffc
def v272 := [t0,t1,t2,t3,t200,t4,t5]
def t201 := 0x1845822c0b40b80d806c01c
def v273 := [t0,t201,t1,t2,t3,t4,t5]
def v274 := [t0,t1,t2,t20,t3,t4,t5]
def t202 := 0x80002280002b800066c000
def v275 := [t0,t202,t1,t2,t3,t4,t5]
def t203 := 0x104500000002b8cd8000000
def v276 := [t0,t203,t1,t2,t3,t4,t5]
def v277 := [t0,t1,t2,t3,t4,t5,t21]
def p63_47 : Projection 48 25 := pick [0,1,2,3,4,5,6,7,8,9,10,11,25,26,27,28,29,30,31,32,33,34,35,36,37] rfl (by decide +kernel) (by decide)
def v278 := [t0,t22,t1,t2,t3,t4,t5]
def t204 := 0xfe4001d52000d44001993000
def v279 := [t0,t1,t2,t3,t204,t4,t5]
def v280 := [t0,t1,t2,t3,t4,t5,t23]
def v281 := [t0,t24,t1,t2,t3,t4,t5]
def t205 := 0xfe7aa4000000d47326000000
def v282 := [t0,t1,t2,t3,t205,t4,t5]
def t206 := 0xc03001800e00
def v283 := [t206,t0,t1,t2,t3,t4,t5]
def t207 := 0xfc3ba1dd0f4afc3fe1ff0fff
def v284 := [t0,t1,t2,t3,t207,t4,t5]
def t208 := 0x4c10a085020a0c00e007001f
def v285 := [t0,t1,t208,t2,t3,t4,t5]
def t209 := 0xb02b01580d40300f007801e0
def v286 := [t0,t1,t2,t209,t3,t4,t5]
def t210 := 0x4c0000850000cc0001870000
def v287 := [t0,t1,t210,t2,t3,t4,t5]
def v288 := [t0,t1,t2,t3,t41,t5]
def v289 := [t0,t1,t2,t3,t4,t43]
def v290 := [t6,t0,t1,t2,t3,t4,t43]
def v291 := [t11,t0,t1,t2,t3,t4,t43]
def v292 := [t0,t12,t1,t2,t3,t4,t43]
def v293 := [t102,t0,t1,t2,t3,t4,t43]
def v294 := [t0,t1,t13,t3,t4,t43]
def v295 := [t0,t1,t2,t13,t3,t4,t43]
def v296 := [t14,t0,t1,t2,t3,t4,t43]
def v297 := [t0,t1,t114,t3,t4,t43]
def v298 := [t0,t1,t114,t2,t3,t4,t43]
def v299 := [t120,t0,t1,t2,t3,t4,t43]
def v300 := [t0,t1,t2,t3,t15,t4,t43]
def v301 := [t16,t0,t1,t2,t3,t4,t43]
def v302 := [t0,t1,t2,t164,t3,t4,t43]
def v303 := [t169,t0,t1,t2,t3,t4,t43]
def v304 := [t0,t1,t2,t3,t4,t170,t43]
def v305 := [t171,t0,t1,t2,t3,t4,t43]
def v306 := [t0,t1,t2,t3,t173,t4,t43]
def t211 := 0x14433e010813
def v307 := [t211,t0,t1,t2,t3,t4,t43]
def t212 := 0xff7ffe8d5b9bffffff9fff9f
def v308 := [t0,t1,t2,t3,t4,t43,t212]
def t213 := 0x10a08599100000018f180
def v309 := [t213,t0,t1,t2,t3,t4,t43]
def t214 := 0xff7ef485020aebbcc186060c
def v310 := [t0,t1,t2,t3,t4,t214,t43]
def v311 := [t177,t0,t1,t2,t3,t4,t43]
def v312 := [t0,t1,t2,t17,t3,t4,t43]
def v313 := [t0,t18,t1,t2,t3,t4,t43]
def v314 := [t0,t1,t199,t2,t3,t4,t43]
def v315 := [t19,t0,t1,t2,t3,t4,t43]
def v316 := [t0,t1,t2,t3,t200,t4,t43]
def v317 := [t0,t201,t1,t2,t3,t4,t43]
def v318 := [t0,t1,t2,t20,t3,t4,t43]
def v319 := [t0,t202,t1,t2,t3,t4,t43]
def v320 := [t0,t1,t2,t3,t4,t43,t21]
def v321 := [t0,t22,t1,t2,t3,t4,t43]
def v322 := [t0,t1,t2,t3,t204,t4,t43]
def t215 := 0x104500000002b8cd806001c
def v323 := [t0,t215,t1,t2,t3,t4,t43]
def t216 := 0xfffefca7c2beffffffe7cfff
def v324 := [t0,t1,t2,t3,t4,t43,t216]
def t217 := 0x800822c0b400000060c1e0
def v325 := [t0,t217,t1,t2,t3,t4,t43]
def t218 := 0xfe7aa485020ad47327810e03
def v326 := [t0,t1,t2,t3,t218,t4,t43]
def v327 := [t206,t0,t1,t2,t3,t4,t43]
def v328 := [t0,t1,t2,t3,t207,t4,t43]
def v329 := [t0,t1,t208,t2,t3,t4,t43]
def v330 := [t0,t1,t2,t209,t3,t4,t43]
def v331 := [t0,t1,t210,t2,t3,t4,t43]
def v332 := [t0,t1,t2,t3,t41,t43]
def v333 := [t0,t1,t2,t3,t4,t41,t43]
def t219 := 0x10a000020a0030e0000e1f
def v334 := [t0,t219,t1,t2,t3,t4,t43]
def v335 := [t0,t1,t2,t3,t42,t43]
def v336 := [t0,t1,t2,t3,t42,t4,t43]
def v337 := [t0,t1,t2,t3,t44,t4]
def v338 := [t0,t1,t3,t44,t4,t43]
def v339 := [t0,t1,t2,t3,t44,t4,t43]
def t220 := 0xb00001500000f00001f80000
def v340 := [t0,t1,t2,t220,t3,t4,t43]
def t221 := 0xfeeb01ffad40ffff01ffffe0
def v341 := [t0,t1,t2,t3,t4,t221,t43]
def t222 := 0x2b00080d40003f00000fe0
def v342 := [t0,t222,t1,t2,t3,t4,t43]
def t223 := 0x4ec000a7a0000fc00007f000
def v343 := [t0,t1,t2,t223,t3,t4,t43]
def t224 := 0xb02a00000000f03f01800e00
def v344 := [t0,t1,t2,t224,t3,t4,t43]
def t225 := 0xff7ff5dd0f4affffffff0fff
def v345 := [t0,t1,t2,t3,t4,t43,t225]
def t226 := 0x101580d400000007801e0
def v346 := [t226,t0,t1,t2,t3,t4,t43]
def t227 := 0x4f54f485020a0fc0fe07001f
def v347 := [t0,t1,t2,t227,t3,t4,t43]
def t228 := 0xfe4000850000ffc001870000
def v348 := [t0,t1,t2,t3,t228,t4,t43]
def t229 := 0xfffef5f7a20afffffffffe1f
def v349 := [t0,t1,t2,t3,t4,t43,t229]
def t230 := 0x800172a00000000078f000
def v350 := [t0,t230,t1,t2,t3,t4,t43]
def t231 := 0x13ef400020a003ffe000e1f
def v351 := [t0,t231,t1,t2,t3,t4,t43]
def v352 := [t0,t1,t2,t3,t4,t41,t5]
def v353 := [t0,t219,t1,t2,t3,t4,t5]
def v354 := [t0,t1,t2,t3,t42,t5]
def v355 := [t0,t1,t2,t3,t42,t4,t5]
def t232 := 0x4c10a0000000cc30e0000000
def v356 := [t0,t1,t232,t2,t3,t4,t5]
def v357 := [t0,t1,t2,t3,t4,t5,t43]
def t233 := 0x85020a000001870e1f
def v358 := [t233,t0,t1,t2,t3,t4,t5]
def v359 := [t0,t1,t2,t3,t44,t4,t5]
def v360 := [t0,t1,t2,t220,t3,t4,t5]
def v361 := [t0,t1,t2,t3,t4,t221,t5]
def v362 := [t0,t222,t1,t2,t3,t4,t5]
def t234 := 0x101580d40000001f80fe0
def v363 := [t234,t0,t1,t2,t3,t4,t5]
def v364 := [t0,t1,t2,t223,t3,t4,t5]
def t235 := 0xb02a00000000f03f00000000
def v365 := [t0,t1,t2,t235,t3,t4,t5]
def t236 := 0xff7ff5580d40fffffff80fe0
def v366 := [t0,t1,t2,t3,t4,t5,t236]
def t237 := 0x4f54f40000000fc0fe000000
def v367 := [t0,t1,t2,t237,t3,t4,t5]
def t238 := 0xfe4000000000ffc000000000
def v368 := [t0,t1,t2,t3,t238,t4,t5]
def t239 := 0xfffef5f7a000fffffffff000
def v369 := [t0,t1,t2,t3,t4,t5,t239]
def t240 := 0x8001f7a000000001fff000
def v370 := [t0,t240,t1,t2,t3,t4,t5]
def t241 := 0x13ef4000000003ffe000000
def v371 := [t0,t241,t1,t2,t3,t4,t5]
theorem b0 : Ban 6 3 v2 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 6 3 v2 := viaSub (ws := [v2]) (consBan b0 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1 : Ban 48 7 v1 := smallByCut p63_14 w0
theorem b2 : Ban 48 6 v4 := smallByCut p63_14 w0
theorem b3 : Ban 48 6 v5 := smallByCut p63_14 w0
theorem b4 : Ban 48 6 v6 := smallByCut p63_14 w0
theorem b5 : Ban 48 6 v7 := smallByCut p63_14 w0
theorem b96 : Ban 25 5 v96 := checkedSmall
theorem solidb96 : Wide 25 5 v96 := solid b96
theorem b6 : Ban 48 6 v8 := smallByCut p63_31 solidb96
theorem b7 : Ban 48 6 v9 := smallByCut p63_14 w0
theorem b130 : Ban 25 5 v129 := checkedSmall
theorem solidb130 : Wide 25 5 v129 := solid b130
theorem b8 : Ban 48 6 v10 := smallByCut p63_31 solidb130
theorem b9 : Ban 48 6 v11 := smallByCut p63_14 w0
theorem b10 : Ban 48 6 v12 := checkedSmall
theorem b11 : Ban 48 6 v13 := smallByCut p63_14 w0
theorem b12 : Ban 48 6 v14 := smallByCut p63_14 w0
theorem b13 : Ban 48 6 v15 := checkedSmall
theorem b255 : Ban 25 5 v252 := checkedSmall
theorem solidb255 : Wide 25 5 v252 := solid b255
theorem b14 : Ban 48 6 v16 := smallByCut p63_31 solidb255
theorem b168 : Ban 25 5 v167 := checkedSmall
theorem solidb168 : Wide 25 5 v167 := solid b168
theorem b15 : Ban 48 6 v17 := smallByCut p63_55 solidb168
theorem b16 : Ban 48 6 v18 := smallByCut p63_55 solidb168
theorem b17 : Ban 48 6 v19 := smallByCut p63_14 w0
theorem b18 : Ban 48 6 v20 := smallByCut p63_14 w0
theorem b19 : Ban 48 6 v21 := smallByCut p63_14 w0
theorem b20 : Ban 48 6 v22 := smallByCut p63_14 w0
theorem b216 : Ban 12 4 v214 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 4 v214 := viaSub (ws := [v214]) (consBan b216 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b21 : Ban 48 6 v23 := smallByCut p63_51 w5
theorem b22 : Ban 48 6 v24 := checkedSmall
theorem b23 : Ban 48 6 v25 := checkedSmall
theorem b24 : Ban 48 6 v26 := smallByCut p63_51 w5
theorem b25 : Ban 48 6 v27 := smallByCut p63_51 w5
theorem b26 : Ban 48 6 v28 := checkedSmall
theorem b27 : Ban 48 6 v29 := checkedSmall
theorem b28 : Ban 48 6 v30 := smallByCut p63_51 w5
theorem b29 : Ban 48 6 v31 := smallByCut p63_14 w0
theorem b30 : Ban 48 6 v32 := smallByCut p63_14 w0
theorem b31 : Ban 48 6 v33 := smallByCut p63_14 w0
theorem b32 : Ban 48 6 v34 := smallByCut p63_14 w0
theorem b33 : Ban 48 6 v35 := checkedSmall
theorem b34 : Ban 48 6 v36 := checkedSmall
theorem b35 : Ban 48 6 v37 := smallByCut p63_14 w0
theorem b36 : Ban 48 6 v38 := smallByCut p63_14 w0
theorem b37 : Ban 48 6 v39 := smallByCut p63_14 w0
theorem b38 : Ban 48 6 v40 := smallByCut p63_14 w0
theorem b39 : Ban 48 6 v41 := smallByCut p63_14 w0
theorem b40 : Ban 48 6 v42 := smallByCut p63_14 w0
theorem b41 : Ban 48 6 v43 := checkedSmall
theorem b42 : Ban 48 6 v44 := checkedSmall
theorem b43 : Ban 48 6 v45 := smallByCut p63_14 w0
theorem b44 : Ban 48 6 v46 := smallByCut p63_14 w0
theorem b45 : Ban 48 6 v47 := checkedSmall
theorem b46 : Ban 48 6 v48 := smallByCut p63_14 w0
theorem b47 : Ban 48 6 v49 := checkedSmall
theorem b48 : Ban 48 6 v50 := smallByCut p63_14 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b49 : Ban 48 7 v3 := viaBranch (ws := [v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50]) (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (nilBan 48 6)))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b50 : Ban 48 7 v14 := smallByCut p63_14 w0
theorem b51 : Ban 25 5 v52 := checkedSmall
theorem b52 : Ban 25 5 v53 := checkedSmall
theorem b53 : Ban 25 5 v54 := checkedSmall
theorem b54 : Ban 25 5 v55 := checkedSmall
theorem b55 : Ban 25 5 v56 := checkedSmall
theorem b56 : Ban 25 5 v57 := checkedSmall
theorem b57 : Ban 25 5 v58 := checkedSmall
theorem b58 : Ban 25 5 v59 := checkedSmall
theorem b59 : Ban 25 5 v60 := checkedSmall
theorem b60 : Ban 25 5 v61 := checkedSmall
theorem b61 : Ban 25 5 v62 := checkedSmall
theorem b62 : Ban 25 5 v63 := checkedSmall
theorem b63 : Ban 25 5 v64 := checkedSmall
theorem b64 : Ban 25 5 v65 := checkedSmall
theorem b65 : Ban 25 5 v66 := checkedSmall
theorem b66 : Ban 25 5 v67 := checkedSmall
theorem b67 : Ban 25 5 v68 := checkedSmall
theorem b68 : Ban 25 5 v69 := checkedSmall
theorem b69 : Ban 25 5 v70 := checkedSmall
theorem b70 : Ban 25 5 v71 := checkedSmall
theorem b71 : Ban 25 5 v72 := checkedSmall
theorem b72 : Ban 25 5 v73 := checkedSmall
theorem b73 : Ban 25 5 v74 := checkedSmall
theorem b74 : Ban 25 5 v75 := checkedSmall
theorem b75 : Ban 25 5 v76 := checkedSmall
theorem b76 : Ban 25 5 v77 := checkedSmall
theorem b77 : Ban 25 5 v78 := checkedSmall
theorem b78 : Ban 25 5 v79 := checkedSmall
theorem b79 : Ban 25 5 v80 := checkedSmall
theorem b80 : Ban 25 5 v81 := checkedSmall
theorem b81 : Ban 25 5 v82 := checkedSmall
theorem b82 : Ban 25 5 v83 := checkedSmall
theorem b83 : Ban 25 5 v84 := checkedSmall
theorem b84 : Ban 25 5 v85 := checkedSmall
theorem b85 : Ban 25 5 v86 := checkedSmall
theorem b86 : Ban 25 5 v87 := checkedSmall
theorem b87 : Ban 25 5 v88 := checkedSmall
theorem b88 : Ban 25 5 v89 := checkedSmall
theorem b89 : Ban 25 5 v90 := checkedSmall
theorem b90 : Ban 25 5 v91 := checkedSmall
theorem b91 : Ban 25 5 v92 := checkedSmall
theorem b92 : Ban 25 5 v93 := checkedSmall
theorem b93 : Ban 25 5 v94 := checkedSmall
theorem b94 : Ban 25 5 v95 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b95 : Ban 25 6 v51 := viaBranch (ws := [v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95]) (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (nilBan 25 5))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b97 : Ban 25 5 v97 := checkedSmall
theorem b98 : Ban 25 5 v98 := checkedSmall
theorem b99 : Ban 25 5 v99 := checkedSmall
theorem b100 : Ban 25 5 v100 := checkedSmall
theorem b101 : Ban 25 5 v101 := checkedSmall
theorem b102 : Ban 25 5 v102 := checkedSmall
theorem b103 : Ban 25 5 v103 := checkedSmall
theorem b104 : Ban 25 5 v104 := checkedSmall
theorem b105 : Ban 25 5 v105 := checkedSmall
theorem b106 : Ban 25 5 v106 := checkedSmall
theorem b107 : Ban 25 5 v107 := checkedSmall
theorem b108 : Ban 25 5 v108 := checkedSmall
theorem b109 : Ban 25 5 v109 := checkedSmall
theorem b110 : Ban 25 5 v110 := checkedSmall
theorem b111 : Ban 25 5 v111 := checkedSmall
theorem b112 : Ban 25 5 v112 := checkedSmall
theorem b113 : Ban 25 5 v113 := checkedSmall
theorem b114 : Ban 25 5 v114 := checkedSmall
theorem b115 : Ban 25 5 v115 := checkedSmall
theorem b116 : Ban 25 5 v116 := checkedSmall
theorem b117 : Ban 25 5 v117 := checkedSmall
theorem b118 : Ban 25 5 v118 := checkedSmall
theorem b119 : Ban 25 5 v119 := checkedSmall
theorem b120 : Ban 25 5 v120 := checkedSmall
theorem b121 : Ban 25 5 v121 := checkedSmall
theorem b122 : Ban 25 5 v122 := checkedSmall
theorem b123 : Ban 25 5 v123 := checkedSmall
theorem b124 : Ban 25 5 v124 := checkedSmall
theorem b125 : Ban 25 5 v125 := checkedSmall
theorem b126 : Ban 25 5 v126 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b127 : Ban 25 6 v55 := viaBranch (ws := [v53,v96,v97,v98,v99,v100,v101,v102,v52,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126]) (consBan b52 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b51 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (nilBan 25 5)))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 25 6 v55 := viaSub (ws := [v51,v55]) (consBan b95 (consBan b127 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b128 : Ban 48 7 v9 := smallByCut p63_31 w1
theorem b129 : Ban 48 7 v127 := smallByCut p63_14 w0
theorem b131 : Ban 25 5 v130 := checkedSmall
theorem b132 : Ban 25 5 v131 := checkedSmall
theorem b133 : Ban 25 5 v132 := checkedSmall
theorem b134 : Ban 25 5 v133 := checkedSmall
theorem b135 : Ban 25 5 v134 := checkedSmall
theorem b136 : Ban 25 5 v135 := checkedSmall
theorem b137 : Ban 25 5 v136 := checkedSmall
theorem b138 : Ban 25 5 v137 := checkedSmall
theorem b139 : Ban 25 5 v138 := checkedSmall
theorem b140 : Ban 25 5 v139 := checkedSmall
theorem b141 : Ban 25 5 v140 := checkedSmall
theorem b142 : Ban 25 5 v141 := checkedSmall
theorem b143 : Ban 25 5 v142 := checkedSmall
theorem b144 : Ban 25 5 v143 := checkedSmall
theorem b145 : Ban 25 5 v144 := checkedSmall
theorem b146 : Ban 25 5 v145 := checkedSmall
theorem b147 : Ban 25 5 v146 := checkedSmall
theorem b148 : Ban 25 5 v147 := checkedSmall
theorem b149 : Ban 25 5 v148 := checkedSmall
theorem b150 : Ban 25 5 v149 := checkedSmall
theorem b151 : Ban 25 5 v150 := checkedSmall
theorem b152 : Ban 25 5 v151 := checkedSmall
theorem b153 : Ban 25 5 v152 := checkedSmall
theorem b154 : Ban 25 5 v153 := checkedSmall
theorem b155 : Ban 25 5 v154 := checkedSmall
theorem b156 : Ban 25 5 v155 := checkedSmall
theorem b157 : Ban 25 5 v156 := checkedSmall
theorem b158 : Ban 25 5 v157 := checkedSmall
theorem b159 : Ban 25 5 v158 := checkedSmall
theorem b160 : Ban 25 5 v159 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b161 : Ban 25 6 v57 := viaBranch (ws := [v129,v130,v131,v132,v133,v134,v135,v59,v136,v137,v138,v139,v140,v141,v105,v142,v58,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159]) (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b58 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b105 (consBan b143 (consBan b57 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (nilBan 25 5))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 25 6 v57 := viaSub (ws := [v51,v57]) (consBan b95 (consBan b161 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b162 : Ban 48 7 v128 := smallByCut p63_31 w2
theorem b163 : Ban 48 7 v160 := smallByCut p63_14 w0
theorem b165 : Ban 48 7 v161 := smallByCut p63_51 w5
theorem b166 : Ban 48 7 v163 := smallByCut p63_14 w0
theorem b167 : Ban 25 5 v166 := checkedSmall
theorem b169 : Ban 25 5 v168 := checkedSmall
theorem b170 : Ban 25 5 v169 := checkedSmall
theorem b171 : Ban 25 5 v170 := checkedSmall
theorem b172 : Ban 25 5 v171 := checkedSmall
theorem b173 : Ban 25 5 v172 := checkedSmall
theorem b174 : Ban 25 5 v173 := checkedSmall
theorem b175 : Ban 25 5 v174 := checkedSmall
theorem b176 : Ban 25 5 v175 := checkedSmall
theorem b177 : Ban 25 5 v176 := checkedSmall
theorem b178 : Ban 25 5 v177 := checkedSmall
theorem b179 : Ban 25 5 v178 := checkedSmall
theorem b180 : Ban 25 5 v179 := checkedSmall
theorem b181 : Ban 25 5 v180 := checkedSmall
theorem b182 : Ban 25 5 v181 := checkedSmall
theorem b183 : Ban 25 5 v182 := checkedSmall
theorem b184 : Ban 25 5 v183 := checkedSmall
theorem b185 : Ban 25 5 v184 := checkedSmall
theorem b186 : Ban 25 5 v185 := checkedSmall
theorem b187 : Ban 25 5 v186 := checkedSmall
theorem b188 : Ban 25 5 v187 := checkedSmall
theorem b189 : Ban 25 5 v188 := checkedSmall
theorem b190 : Ban 25 5 v189 := checkedSmall
theorem b191 : Ban 25 5 v190 := checkedSmall
theorem b192 : Ban 25 5 v191 := checkedSmall
theorem b193 : Ban 25 5 v192 := checkedSmall
theorem b194 : Ban 25 5 v193 := checkedSmall
theorem b195 : Ban 25 5 v194 := checkedSmall
theorem b196 : Ban 25 5 v195 := checkedSmall
theorem b197 : Ban 25 5 v196 := checkedSmall
theorem b198 : Ban 25 5 v197 := checkedSmall
theorem b199 : Ban 25 5 v198 := checkedSmall
theorem b200 : Ban 25 5 v199 := checkedSmall
theorem b201 : Ban 25 5 v200 := checkedSmall
theorem b202 : Ban 25 5 v201 := checkedSmall
theorem b203 : Ban 25 5 v202 := checkedSmall
theorem b204 : Ban 25 5 v203 := checkedSmall
theorem b205 : Ban 25 5 v204 := checkedSmall
theorem b206 : Ban 25 5 v205 := checkedSmall
theorem b207 : Ban 25 5 v206 := checkedSmall
theorem b208 : Ban 25 5 v207 := checkedSmall
theorem b209 : Ban 25 5 v208 := checkedSmall
theorem b210 : Ban 25 5 v209 := checkedSmall
theorem b211 : Ban 25 5 v210 := checkedSmall
theorem b212 : Ban 25 5 v211 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b213 : Ban 25 6 v165 := viaBranch (ws := [v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211]) (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (nilBan 25 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b227 : Ban 25 5 v225 := checkedSmall
theorem b228 : Ban 25 5 v226 := checkedSmall
theorem b229 : Ban 25 5 v227 := checkedSmall
theorem b230 : Ban 25 5 v228 := checkedSmall
theorem b231 : Ban 25 5 v229 := checkedSmall
theorem b232 : Ban 25 5 v230 := checkedSmall
theorem b233 : Ban 25 5 v231 := checkedSmall
theorem b234 : Ban 25 5 v232 := checkedSmall
theorem b235 : Ban 25 5 v233 := checkedSmall
theorem b236 : Ban 25 5 v234 := checkedSmall
theorem b237 : Ban 25 5 v235 := checkedSmall
theorem b238 : Ban 25 5 v236 := checkedSmall
theorem b239 : Ban 25 5 v237 := checkedSmall
theorem b240 : Ban 25 5 v238 := checkedSmall
theorem b241 : Ban 25 5 v239 := checkedSmall
theorem b242 : Ban 25 5 v240 := checkedSmall
theorem b243 : Ban 25 5 v241 := checkedSmall
theorem b244 : Ban 25 5 v242 := checkedSmall
theorem b245 : Ban 25 5 v243 := checkedSmall
theorem b246 : Ban 25 5 v244 := checkedSmall
theorem b247 : Ban 25 5 v245 := checkedSmall
theorem b248 : Ban 25 5 v246 := checkedSmall
theorem b249 : Ban 25 5 v247 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b250 : Ban 25 6 v185 := viaBranch (ws := [v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v187,v186,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247]) (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b188 (consBan b187 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (nilBan 25 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 25 6 v185 := viaSub (ws := [v165,v185]) (consBan b213 (consBan b250 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b214 : Ban 48 7 v164 := smallByCut p63_55 w6
theorem b215 : Ban 48 7 v212 := smallByCut p63_14 w0
theorem b217 : Ban 48 7 v213 := smallByCut p63_51 w5
theorem b218 : Ban 48 7 v215 := smallByCut p63_14 w0
theorem b219 : Ban 48 7 v216 := smallByCut p63_14 w0
theorem b221 : Ban 48 7 v217 := smallByCut p63_14 w0
theorem b222 : Ban 48 7 v219 := smallByCut p63_14 w0
theorem b223 : Ban 48 7 v220 := smallByCut p63_14 w0
theorem b224 : Ban 48 7 v221 := smallByCut p63_14 w0
theorem b220 : Ban 48 7 v218 := smallByCut p63_14 w0
theorem b225 : Ban 48 7 v222 := smallByCut p63_14 w0
theorem b226 : Ban 48 7 v223 := smallByCut p63_51 w5
theorem b251 : Ban 48 7 v224 := smallByCut p63_55 w6
theorem b252 : Ban 25 5 v249 := checkedSmall
theorem b253 : Ban 25 5 v250 := checkedSmall
theorem b254 : Ban 25 5 v251 := checkedSmall
theorem b256 : Ban 25 5 v253 := checkedSmall
theorem b257 : Ban 25 5 v254 := checkedSmall
theorem b258 : Ban 25 5 v255 := checkedSmall
theorem b259 : Ban 25 5 v256 := checkedSmall
theorem b260 : Ban 25 5 v257 := checkedSmall
theorem b261 : Ban 25 5 v258 := checkedSmall
theorem b262 : Ban 25 5 v259 := checkedSmall
theorem b263 : Ban 25 5 v260 := checkedSmall
theorem b264 : Ban 25 5 v261 := checkedSmall
theorem b265 : Ban 25 5 v262 := checkedSmall
theorem b266 : Ban 25 5 v263 := checkedSmall
theorem b267 : Ban 25 5 v264 := checkedSmall
theorem b268 : Ban 25 5 v265 := checkedSmall
theorem b269 : Ban 25 5 v266 := checkedSmall
theorem b270 : Ban 25 5 v267 := checkedSmall
theorem b271 : Ban 25 5 v268 := checkedSmall
theorem b272 : Ban 25 5 v269 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b273 : Ban 25 6 v72 := viaBranch (ws := [v249,v250,v251,v105,v252,v120,v253,v254,v255,v70,v256,v71,v74,v257,v258,v77,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269]) (consBan b252 (consBan b253 (consBan b254 (consBan b105 (consBan b255 (consBan b120 (consBan b256 (consBan b257 (consBan b258 (consBan b69 (consBan b259 (consBan b70 (consBan b73 (consBan b260 (consBan b261 (consBan b76 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (nilBan 25 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 25 6 v72 := viaSub (ws := [v51,v72]) (consBan b95 (consBan b273 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b274 : Ban 48 7 v248 := smallByCut p63_31 w7
theorem b275 : Ban 48 7 v270 := smallByCut p63_51 w5
theorem b276 : Ban 48 7 v271 := smallByCut p63_51 w5
theorem b277 : Ban 48 7 v272 := smallByCut p63_55 w6
theorem b278 : Ban 48 7 v273 := smallByCut p63_55 w6
theorem b279 : Ban 48 7 v274 := smallByCut p63_51 w5
theorem b281 : Ban 48 7 v275 := smallByCut p63_14 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 25 6 v51 := viaSub (ws := [v51]) (consBan b95 (nilBan 25 6)) (by decide) (by decide +kernel)
theorem b282 : Ban 48 7 v277 := smallByCut p63_47 w8
theorem b283 : Ban 48 7 v278 := smallByCut p63_47 w8
theorem b284 : Ban 48 7 v279 := smallByCut p63_14 w0
theorem b280 : Ban 48 7 v276 := smallByCut p63_14 w0
theorem b285 : Ban 48 7 v280 := smallByCut p63_31 w8
theorem b286 : Ban 48 7 v281 := smallByCut p63_31 w8
theorem b287 : Ban 48 7 v282 := smallByCut p63_14 w0
theorem b288 : Ban 48 7 v283 := smallByCut p63_51 w5
theorem b289 : Ban 48 7 v284 := smallByCut p63_51 w5
theorem b290 : Ban 48 7 v285 := smallByCut p63_51 w5
theorem b291 : Ban 48 7 v286 := smallByCut p63_51 w5
theorem b292 : Ban 48 7 v287 := smallByCut p63_14 w0
theorem b293 : Ban 48 6 v290 := smallByCut p63_14 w0
theorem b294 : Ban 48 6 v291 := smallByCut p63_14 w0
theorem b295 : Ban 48 6 v292 := smallByCut p63_31 w1
theorem b296 : Ban 48 6 v293 := smallByCut p63_14 w0
theorem b297 : Ban 48 6 v294 := smallByCut p63_31 w2
theorem b298 : Ban 48 6 v295 := smallByCut p63_51 w5
theorem b299 : Ban 48 6 v296 := smallByCut p63_14 w0
theorem b300 : Ban 48 6 v297 := smallByCut p63_51 w5
theorem b301 : Ban 48 6 v298 := smallByCut p63_51 w5
theorem b302 : Ban 48 6 v299 := smallByCut p63_14 w0
theorem b303 : Ban 48 6 v300 := smallByCut p63_51 w5
theorem b304 : Ban 48 6 v301 := smallByCut p63_14 w0
theorem b305 : Ban 48 6 v302 := smallByCut p63_51 w5
theorem b306 : Ban 48 6 v303 := smallByCut p63_14 w0
theorem b307 : Ban 48 6 v304 := smallByCut p63_14 w0
theorem b308 : Ban 48 6 v305 := smallByCut p63_14 w0
theorem b309 : Ban 48 6 v306 := smallByCut p63_14 w0
theorem b310 : Ban 48 6 v307 := smallByCut p63_14 w0
theorem b311 : Ban 48 6 v308 := smallByCut p63_31 w2
theorem b312 : Ban 48 6 v309 := smallByCut p63_14 w0
theorem b313 : Ban 48 6 v310 := checkedSmall
theorem b314 : Ban 48 6 v311 := smallByCut p63_51 w5
theorem b315 : Ban 48 6 v312 := smallByCut p63_51 w5
theorem b316 : Ban 48 6 v313 := smallByCut p63_51 w5
theorem b317 : Ban 48 6 v314 := smallByCut p63_51 w5
theorem b318 : Ban 48 6 v315 := smallByCut p63_51 w5
theorem b319 : Ban 48 6 v316 := smallByCut p63_51 w5
theorem b320 : Ban 48 6 v317 := smallByCut p63_51 w5
theorem b321 : Ban 48 6 v318 := smallByCut p63_51 w5
theorem b322 : Ban 48 6 v319 := smallByCut p63_14 w0
theorem solidb86 : Wide 25 5 v87 := solid b86
theorem b323 : Ban 48 6 v320 := smallByCut p63_47 solidb86
theorem b324 : Ban 48 6 v321 := smallByCut p63_47 solidb86
theorem b325 : Ban 48 6 v322 := smallByCut p63_14 w0
theorem b326 : Ban 48 6 v323 := checkedSmall
theorem b327 : Ban 48 6 v324 := checkedSmall
theorem b328 : Ban 48 6 v325 := smallByCut p63_31 w7
theorem b329 : Ban 48 6 v326 := checkedSmall
theorem b330 : Ban 48 6 v327 := smallByCut p63_51 w5
theorem b331 : Ban 48 6 v328 := smallByCut p63_51 w5
theorem b332 : Ban 48 6 v329 := smallByCut p63_51 w5
theorem b333 : Ban 48 6 v330 := smallByCut p63_51 w5
theorem b334 : Ban 48 6 v331 := smallByCut p63_14 w0
theorem b335 : Ban 48 6 v332 := smallByCut p63_51 w5
theorem b336 : Ban 48 6 v333 := smallByCut p63_51 w5
theorem b337 : Ban 48 6 v334 := smallByCut p63_51 w5
theorem b338 : Ban 48 6 v335 := smallByCut p63_51 w5
theorem b339 : Ban 48 6 v336 := smallByCut p63_14 w0
theorem b340 : Ban 48 6 v337 := smallByCut p63_14 w0
theorem b341 : Ban 48 6 v338 := smallByCut p63_14 w0
theorem b342 : Ban 48 6 v339 := smallByCut p63_14 w0
theorem b343 : Ban 48 6 v340 := smallByCut p63_14 w0
theorem b344 : Ban 48 6 v341 := smallByCut p63_51 w5
theorem b345 : Ban 48 6 v342 := smallByCut p63_51 w5
theorem b346 : Ban 48 6 v343 := smallByCut p63_14 w0
theorem b347 : Ban 48 6 v344 := smallByCut p63_51 w5
theorem b348 : Ban 48 6 v345 := smallByCut p63_51 w5
theorem b349 : Ban 48 6 v346 := smallByCut p63_51 w5
theorem b350 : Ban 48 6 v347 := smallByCut p63_51 w5
theorem b351 : Ban 48 6 v348 := smallByCut p63_14 w0
theorem b352 : Ban 48 6 v349 := smallByCut p63_47 solidb86
theorem b353 : Ban 48 6 v350 := smallByCut p63_14 w0
theorem b354 : Ban 48 6 v351 := smallByCut p63_47 solidb86
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b355 : Ban 48 7 v289 := viaBranch (ws := [v290,v49,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351]) (consBan b293 (consBan b47 (consBan b294 (consBan b295 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b336 (consBan b337 (consBan b338 (consBan b339 (consBan b340 (consBan b341 (consBan b342 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (consBan b347 (consBan b348 (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (nilBan 48 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b356 : Ban 48 7 v288 := viaPerm map63_1 map63_1 b355 (by decide +kernel) (by decide +kernel)
theorem b357 : Ban 48 7 v352 := smallByCut p63_47 w8
theorem b358 : Ban 48 7 v353 := smallByCut p63_51 w5
theorem b359 : Ban 48 7 v354 := smallByCut p63_47 w8
theorem b360 : Ban 48 7 v355 := smallByCut p63_14 w0
theorem b361 : Ban 48 7 v356 := smallByCut p63_14 w0
theorem b362 : Ban 48 7 v357 := smallByCut p63_31 w8
theorem b363 : Ban 48 7 v358 := smallByCut p63_51 w5
theorem b364 : Ban 48 7 v337 := smallByCut p63_31 w8
theorem b365 : Ban 48 7 v359 := smallByCut p63_14 w0
theorem b366 : Ban 48 7 v360 := smallByCut p63_14 w0
theorem b367 : Ban 48 7 v361 := smallByCut p63_47 w8
theorem b369 : Ban 48 7 v362 := smallByCut p63_51 w5
theorem b370 : Ban 48 7 v364 := smallByCut p63_14 w0
theorem b371 : Ban 48 7 v365 := smallByCut p63_14 w0
theorem b372 : Ban 48 7 v366 := smallByCut p63_31 w8
theorem b368 : Ban 48 7 v363 := smallByCut p63_51 w5
theorem b373 : Ban 48 7 v367 := smallByCut p63_14 w0
theorem b374 : Ban 48 7 v368 := smallByCut p63_14 w0
theorem b375 : Ban 48 7 v369 := smallByCut p63_14 w0
theorem b376 : Ban 48 7 v370 := smallByCut p63_14 w0
theorem b377 : Ban 48 7 v371 := smallByCut p63_14 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b378 : Ban 48 8 v0 := viaBranch (ws := [v1,v3,v14,v9,v127,v128,v160,v161,v163,v164,v212,v213,v215,v216,v217,v219,v220,v221,v218,v222,v223,v224,v248,v270,v271,v272,v273,v274,v275,v277,v278,v279,v276,v280,v281,v282,v283,v284,v285,v286,v287,v288,v352,v353,v354,v355,v356,v289,v357,v358,v337,v359,v360,v361,v362,v364,v365,v366,v363,v367,v368,v369,v370,v371]) (consBan b1 (consBan b49 (consBan b50 (consBan b128 (consBan b129 (consBan b162 (consBan b163 (consBan b165 (consBan b166 (consBan b214 (consBan b215 (consBan b217 (consBan b218 (consBan b219 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b220 (consBan b225 (consBan b226 (consBan b251 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b280 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b355 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b368 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b377 (nilBan 48 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 48 8 v0 := widen (by decide +kernel) b378
end PEqualNP.Outside.L_meta_17013.Support

namespace PEqualNP.Outside.L_meta_17013.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17013.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4277075690 * 2 ^ 32 + 4276813024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0xf3ceb9db5cb2cb1b2caaaa699a69638e185c71a6996565954d345134c30b2ca287186145
def negBits : ℕ := 0xe34e38d34c224b0a24a22a099229220e00585184982544944834012481090c8083102101
def sample (bank : ℕ) (i : Fin 48) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x10a08599114433e19f993,0x1845822c0b42b8cd866c1fc,0x4c10a085020acc30e1870e1f,0xb02b01580d40f03f01f80fe0,0xfec001f7a000ffc001fff000,0xff7ef4000000fffffe000000]
def seeds : List Wire := [(false,0x10a08599114433e19f993),(false,0x1845822c0b42b8cd866c1fc),(false,0x4c10a085020acc30e1870e1f),(false,0xb02b01580d40f03f01f80fe0),(false,0xfec001f7a000ffc001fff000),(false,0xff7ef4000000fffffe000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 48, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (48+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 48, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 48, ∀ b∈inputs, b.testBit i.val≠b.testBit (48+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 48 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 48 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 48 out.2 := by
    intro i hi same
    let j : Fin 48 := ⟨i,hi⟩
    have diff : read i out=read (48+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (48+i))
      rw [same]
    have p := ev i;have n := ev (48+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have keep : ∀ a∈reps seeds, a≠0 → a∈inputs := by decide +kernel
  have stays : ∀ a∈S, a∈inputs := fun a ha => keep a (sub a ha) (liveNonzero live a ha)
  exact ⟨k,limit,initial live stays ▸ live⟩

def restricted : List ℕ := v0
def restrictRows : Projection 48 48 := pick (List.range 48) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 48 8 restricted := verifiedPin
theorem six_floor : Ban 48 8 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[1,2]⟩, ⟨.and,[7,3]⟩, ⟨.and,[0,4]⟩, ⟨.or,[8,9]⟩, ⟨.or,[0,4]⟩, ⟨.and,[11,5]⟩, ⟨.or,[2,12]⟩, ⟨.and,[6,13]⟩, ⟨.or,[10,14]⟩],15⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
theorem wcomputes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by decide +kernel
theorem binary_floor {C : Circuit} (fan : FanInTwo C) (d : ∀ x, C.eval (List.ofFn x) = target x) :
    9 ≤ C.gates.countP counted := by
  obtain ⟨k,le,live⟩ := trace C fan (funext d)
  by_contra! low
  exact six_floor k (by omega) live
theorem mono_enough : ∀ s, HasCircuitSize 6 target s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x)=target x := by
  rintro s ⟨C,fan,sz,correct⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g,hg,hop⟩ := hn
    have low := binary_floor fan correct
    have lt : C.gates.countP counted < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro equal
      have is := List.countP_eq_length.mp equal g hg
      simp [counted,hop] at is
    refine ⟨witness,wmono,?_,wcomputes⟩
    change C.gates.length ≤ s at sz
    change 10 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_17013.Data

theorem PEqualNP.Outside.L_meta_17013 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276813024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276813024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_17013.Data.mono_enough
