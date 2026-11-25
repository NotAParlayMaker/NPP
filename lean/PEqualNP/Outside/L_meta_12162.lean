import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12162.Support

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

def t0 := 0x22d8b40d1fc7e07
def t1 := 0x324ffd24007fe00
def t2 := 0x346d1861e3f8e38
def t3 := 0x3b0ec301fc7f1c0
def t4 := 0x3ffc9249ff80000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x2048100103c0e00
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x9d21c0
def t7 := 0xb46fc7
def t8 := 0xdb0ff8
def t9 := 0xf24e00
def v2 := [t6,t7,t8,t9]
def t10 := 0x9421c0
def v3 := [t10,t6,t7,t8,t9]
def t11 := 0xbd6fc7
def v4 := [t6,t7,t11,t8,t9]
def t12 := 0x90000
def v5 := [t12,t6,t7,t8,t9]
def t13 := 0x204e07
def v6 := [t13,t6,t7,t8,t9]
def t14 := 0x421c7
def v7 := [t14,t6,t7,t8,t9]
def t15 := 0x421c0
def v8 := [t15,t6,t7,t8,t9]
def t16 := 0x9d21c7
def v9 := [t6,t16,t7,t8,t9]
def t17 := 0x7
def v10 := [t17,t6,t7,t8,t9]
def t18 := 0x990000
def v11 := [t18,t6,t7,t8,t9]
def t19 := 0xb04e00
def v12 := [t14,t6,t19,t8,t9]
def v13 := [t6,t19,t7,t8,t9]
def t20 := 0x1c0
def v14 := [t20,t6,t7,t8,t9]
def t21 := 0xdf2fff
def v15 := [t6,t7,t8,t21,t9]
def t22 := 0x42007
def v16 := [t22,t6,t7,t8,t9]
def t23 := 0xdb0e38
def v17 := [t6,t7,t23,t8,t9]
def t24 := 0xf66fc7
def v18 := [t14,t6,t7,t8,t24]
def v19 := [t6,t7,t8,t9,t24]
def v20 := [t14,t6,t11,t8,t9]
def v21 := [t14,t13,t6,t8,t9]
def t25 := 0xff6fc0
def v22 := [t14,t6,t7,t8,t25]
def t26 := 0x624e00
def v23 := [t14,t26,t6,t7,t8]
def t27 := 0x900fc0
def v24 := [t14,t27,t6,t8,t9]
def t28 := 0x4b0038
def v25 := [t14,t28,t6,t8,t9]
def t29 := 0x420000
def v26 := [t14,t29,t6,t8]
def v27 := [t14,t29,t6,t7,t8]
def v28 := [t14,t29,t6,t8,t9]
def t30 := 0xd20e00
def v29 := [t14,t6,t7,t30,t8]
def t31 := 0x901f8
def v30 := [t14,t31,t6,t7,t8]
def map29_1 : Projection 12 12 := pick [0,2,1,3,5,4,9,10,11,6,7,8] rfl (by decide +kernel) (by decide)
def t32 := 0x9901c0
def v31 := [t32,t6,t7,t8,t9]
def t33 := 0xdf2ff8
def v32 := [t6,t7,t8,t33,t9]
def t34 := 0x42000
def v33 := [t34,t6,t7,t8,t9]
def t35 := 0x420e38
def v34 := [t35,t6,t7,t8,t9]
def map29_3 : Projection 12 12 := pick [3,5,4,0,2,1,10,9,11,7,6,8] rfl (by decide +kernel) (by decide)
def t36 := 0x900000
def v35 := [t36,t6,t7,t8,t9]
def v36 := [t6,t7,t8,t9,t25]
def v37 := [t10,t7,t8,t9,t25]
def v38 := [t13,t7,t8,t9,t25]
def v39 := [t32,t7,t8,t9,t25]
def v40 := [t35,t7,t8,t9,t25]
def v41 := [t36,t7,t8,t25]
def v42 := [t36,t6,t7,t8,t25]
def v43 := [t36,t7,t8,t9,t25]
def t37 := 0xd21c0
def v44 := [t37,t6,t7,t8,t25]
def v45 := [t26,t7,t8,t9,t25]
def v46 := [t26,t6,t7,t8,t9]
def v47 := [t6,t19,t7,t8,t25]
def t38 := 0xb46fc0
def v48 := [t6,t38,t7,t8,t9]
def t39 := 0xff6fc7
def v49 := [t6,t7,t8,t9,t39]
def t40 := 0x4b0000
def v50 := [t40,t6,t7,t8,t9]
def v51 := [t6,t7,t30,t8,t25]
def v52 := [t31,t6,t7,t8,t25]
def t41 := 0xdb0fc0
def v53 := [t6,t7,t41,t8,t9]
def t42 := 0xff6ff8
def v54 := [t6,t7,t8,t9,t42]
def t43 := 0x38
def v55 := [t43,t6,t7,t8,t9]
def t44 := 0x246000
def v56 := [t44,t6,t7,t8,t9]
def v57 := [t37,t6,t7,t8,t9]
def v58 := [t27,t6,t7,t8,t9]
def t45 := 0x9001c0
def v59 := [t45,t6,t7,t8,t9]
def t46 := 0x9d2fc0
def v60 := [t6,t46,t7,t8,t9]
def t47 := 0xe00
def v61 := [t47,t6,t7,t8,t9]
def t48 := 0xd2000
def v62 := [t48,t6,t7,t8,t9]
def t49 := 0x246007
def v63 := [t49,t27,t6,t8,t9]
def v64 := [t49,t6,t7,t8,t9]
def v65 := [t28,t27,t6,t7,t9]
def v66 := [t28,t6,t7,t8,t9]
def t50 := 0x900e00
def v67 := [t50,t6,t7,t8,t9]
def t51 := 0xf24fc0
def v68 := [t6,t7,t8,t9,t51]
def t52 := 0x624000
def v69 := [t52,t6,t7,t8,t9]
def v70 := [t27,t6,t11,t8,t9]
def v71 := [t13,t27,t6,t8,t9]
def v72 := [t27,t6,t7,t33,t9]
def v73 := [t35,t27,t6,t7,t9]
def t53 := 0xff6fff
def v74 := [t27,t6,t9,t53]
def v75 := [t27,t6,t7,t9,t53]
def v76 := [t27,t6,t8,t9,t53]
def v77 := [t27,t6,t8,t9,t24]
def t54 := 0xfb4ff8
def v78 := [t27,t6,t7,t9,t54]
def v79 := [t31,t27,t6,t7,t9]
def v80 := [t6,t7,t8,t9,t53]
def v81 := [t29,t6,t7,t8,t9]
def v82 := [t6,t7,t30,t8,t9]
def v83 := [t6,t7,t8,t9,t54]
def v84 := [t31,t6,t7,t8,t9]
def map29_2 : Projection 12 12 := pick [3,4,5,0,1,2,7,6,8,10,9,11] rfl (by decide +kernel) (by decide)
def t55 := 0x204000
def v85 := [t55,t6,t7,t8,t9]
def p31_29 : Projection 29 12 := pick [0,1,2,6,7,8,12,13,14,22,23,24] rfl (by decide +kernel) (by decide)
def t56 := 0x36fdbc6dffffe3f
def v86 := [t0,t1,t2,t56,t3,t4]
def v87 := [t5,t1,t56,t3,t4]
def v88 := [t5,t0,t1,t56,t3,t4]
def v89 := [t5,t1,t2,t56,t3,t4]
def map31_4 : Projection 29 29 := pick [3,4,5,0,1,2,6,7,8,10,9,11,15,16,17,12,13,14,18,20,19,21,25,26,27,22,23,24,28] rfl (by decide +kernel) (by decide)
def v90 := [t5,t0,t1,t2,t56,t3,t4]
def t57 := 0x290a40c1c07007
def v91 := [t57,t0,t1,t56,t3,t4]
def t58 := 0xd0340c0380e07
def t59 := 0x3bdef70dfffffc7
def v92 := [t58,t0,t1,t2,t59,t4]
def p31_30 : Projection 29 12 := pick [3,4,5,6,7,8,15,16,17,25,26,27] rfl (by decide +kernel) (by decide)
def map31_2 : Projection 29 29 := pick [0,1,2,6,7,8,3,4,5,12,13,14,9,10,11,16,15,17,18,22,23,24,19,20,21,26,25,27,28] rfl (by decide +kernel) (by decide)
def v93 := [t57,t0,t1,t2,t56,t3,t4]
def v94 := [t58,t0,t1,t2,t3,t59,t4]
def map27_1 : Projection 12 12 := pick [0,2,1,3,5,4,9,10,11,6,7,8] rfl (by decide +kernel) (by decide)
def map27_3 : Projection 12 12 := pick [3,5,4,0,2,1,10,9,11,7,6,8] rfl (by decide +kernel) (by decide)
def map27_2 : Projection 12 12 := pick [3,4,5,0,1,2,7,6,8,10,9,11] rfl (by decide +kernel) (by decide)
def p31_27 : Projection 29 12 := pick [0,1,2,3,4,5,9,10,11,19,20,21] rfl (by decide +kernel) (by decide)
def t60 := 0x14250860e038038
def v95 := [t60,t1,t2,t56,t3,t4]
def map31_6 : Projection 29 29 := pick [3,4,5,6,7,8,0,1,2,15,16,17,10,9,11,13,12,14,18,25,26,27,20,19,21,23,22,24,28] rfl (by decide +kernel) (by decide)
def map31_8 : Projection 29 29 := pick [6,7,8,0,1,2,3,4,5,13,12,14,16,15,17,9,10,11,18,23,22,24,26,25,27,19,20,21,28] rfl (by decide +kernel) (by decide)
def v96 := [t60,t0,t1,t2,t56,t3,t4]
def t61 := 0x220880011c47000
def v97 := [t61,t0,t1,t2,t56,t3,t4]
def v98 := [t5,t0,t1,t2,t3,t59,t4]
def v99 := [t1,t2,t56,t3,t59,t4]
def t62 := 0x3f6fdb61ffffff8
def v100 := [t0,t1,t2,t59,t62,t4]
def v101 := [t5,t0,t1,t2,t59,t62,t4]
def v102 := [t1,t56,t59,t62,t4]
def t63 := 0x324dbc24007fe00
def v103 := [t63,t1,t56,t59,t62,t4]
def t64 := 0x36fffd6dffffe3f
def v104 := [t1,t56,t64,t59,t62,t4]
def t65 := 0x241000000000
def v105 := [t65,t1,t56,t59,t62,t4]
def t66 := 0x4b00049ff8003f
def v106 := [t66,t1,t56,t59,t62,t4]
def t67 := 0x324ef504007fe00
def v107 := [t67,t1,t56,t59,t62,t4]
def t68 := 0x3bdfff2dfffffc7
def v108 := [t1,t56,t59,t68,t62,t4]
def t69 := 0x108200000000
def v109 := [t69,t1,t56,t59,t62,t4]
def t70 := 0x9900209ff801c7
def v110 := [t70,t1,t56,t59,t62,t4]
def t71 := 0x324fd920007fe00
def v111 := [t71,t1,t56,t59,t62,t4]
def t72 := 0x3f6fff65ffffff8
def v112 := [t1,t56,t59,t62,t72,t4]
def t73 := 0x24040000000
def v113 := [t73,t1,t56,t59,t62,t4]
def t74 := 0xd200241ff801f8
def v114 := [t74,t1,t56,t59,t62,t4]
def t75 := 0x324c90000000000
def v115 := [t75,t1,t56,t59,t62,t4]
def t76 := 0x3fffff6dffffe00
def v116 := [t1,t56,t59,t62,t4,t76]
def t77 := 0x36d24007fe00
def v117 := [t77,t1,t56,t59,t62,t4]
def t78 := 0xdb00249ff80000
def v118 := [t78,t1,t56,t59,t62,t4]
def t79 := 0x32dcb40dffffe07
def v119 := [t1,t79,t62,t4]
def v120 := [t1,t79,t56,t62,t4]
def v121 := [t1,t79,t59,t62,t4]
def v122 := [t1,t79,t56,t59,t62,t4]
def t80 := 0x3fffff6dfffffff
def v123 := [t1,t56,t59,t62,t4,t80]
def t81 := 0x42108600000038
def v124 := [t81,t1,t56,t62,t4]
def v125 := [t81,t1,t56,t59,t62,t4]
def t82 := 0x902430000001c0
def v126 := [t82,t1,t59,t62,t4]
def v127 := [t82,t1,t56,t59,t62,t4]
def t83 := 0x366d9861ffffe38
def v128 := [t1,t83,t59,t4]
def v129 := [t1,t83,t56,t59,t4]
def v130 := [t1,t83,t59,t62,t4]
def v131 := [t1,t83,t56,t59,t62,t4]
def t84 := 0x90240c0000007
def v132 := [t84,t1,t56,t59,t4]
def v133 := [t84,t1,t56,t59,t62,t4]
def t85 := 0x36fc9049ff80000
def v134 := [t1,t85,t56,t59,t62,t4]
def t86 := 0x3ffdbe6dffffe3f
def v135 := [t1,t56,t59,t62,t4,t86]
def t87 := 0x12c24007fe3f
def v136 := [t87,t1,t56,t59,t62,t4]
def t88 := 0x90002000000000
def v137 := [t88,t1,t56,t59,t62,t4]
def t89 := 0x3b4ed301fffffc0
def v138 := [t1,t56,t89,t4]
def v139 := [t1,t56,t89,t59,t4]
def v140 := [t1,t56,t89,t62,t4]
def v141 := [t1,t56,t89,t59,t62,t4]
def t90 := 0x3bdc9209ff80000
def v142 := [t1,t56,t90,t59,t62,t4]
def t91 := 0x3ffef74dfffffc7
def v143 := [t1,t56,t59,t62,t4,t91]
def t92 := 0x26504007ffc7
def v144 := [t92,t1,t56,t59,t62,t4]
def t93 := 0x42000400000000
def v145 := [t93,t1,t56,t59,t62,t4]
def t94 := 0x3f6c9241ff80000
def v146 := [t1,t56,t59,t94,t62,t4]
def t95 := 0x3fffdb69ffffff8
def v147 := [t1,t56,t59,t62,t4,t95]
def t96 := 0x34920007fff8
def v148 := [t96,t1,t56,t59,t62,t4]
def t97 := 0x9000080000000
def v149 := [t97,t1,t56,t59,t62,t4]
def v150 := [t0,t1,t56,t59,t62,t4]
def v151 := [t1,t2,t56,t59,t62,t4]
def v152 := [t0,t1,t2,t56,t59,t62,t4]
def v153 := [t57,t1,t2,t59,t62,t4]
def v154 := [t58,t1,t56,t3,t62,t4]
def v155 := [t57,t0,t1,t2,t59,t62,t4]
def v156 := [t60,t0,t1,t59,t62,t4]
def v157 := [t60,t0,t1,t2,t59,t62,t4]
def t98 := 0x2248b4040047e00
def v158 := [t98,t0,t1,t2,t59,t62,t4]
def t99 := 0x32dffd2d1fffe07
def v159 := [t0,t1,t99,t2,t59,t62,t4]
def t100 := 0x9000091f80007
def v160 := [t100,t0,t1,t2,t59,t62,t4]
def t101 := 0x100749200038000
def v161 := [t101,t0,t1,t2,t59,t62,t4]
def t102 := 0x19064300e0381c0
def v162 := [t102,t0,t1,t2,t62,t4]
def v163 := [t102,t1,t2,t59,t62,t4]
def v164 := [t102,t0,t1,t2,t59,t62,t4]
def t103 := 0x224890011fc7e00
def v165 := [t103,t1,t2,t59,t4]
def v166 := [t103,t0,t1,t2,t59,t4]
def t104 := 0x4b3
def t105 := 0xa3c
def t106 := 0xeb0
def v167 := [t104,t105,t106]
def p31_14 : Projection 29 6 := pick [3,4,6,7,15,16] rfl (by decide +kernel) (by decide)
def v168 := [t103,t1,t2,t59,t62,t4]
def v169 := [t103,t0,t1,t2,t59,t62,t4]
def v170 := [t0,t1,t2,t59,t62,t4,t80]
def v171 := [t84,t0,t1,t2,t59,t4]
def v172 := [t84,t0,t1,t2,t59,t62,t4]
def t107 := 0x1d274b60e0381f8
def v173 := [t107,t1,t2,t59,t62,t4]
def v174 := [t107,t0,t1,t2,t59,t62,t4]
def t108 := 0x22d890091f80000
def v175 := [t108,t0,t1,t2,t59,t62,t4]
def t109 := 0x3ffcb64dffc7e07
def v176 := [t0,t1,t2,t59,t62,t4,t109]
def t110 := 0x24040047e07
def v177 := [t110,t0,t1,t2,t59,t62,t4]
def t111 := 0x1d240240e000000
def v178 := [t111,t0,t1,t2,t59,t62,t4]
def t112 := 0x304d18200078e00
def v179 := [t0,t112,t1,t2,t59,t62,t4]
def t113 := 0x366ffd65e3ffe38
def v180 := [t0,t1,t2,t113,t59,t62,t4]
def t114 := 0x4200041e380038
def v181 := [t114,t0,t1,t2,t59,t62,t4]
def t115 := 0x202e5040007000
def v182 := [t115,t0,t1,t2,t59,t62,t4]
def t116 := 0x304c1001e3f8e00
def v183 := [t0,t116,t1,t62,t4]
def v184 := [t0,t116,t1,t2,t62,t4]
def v185 := [t0,t116,t1,t59,t62,t4]
def v186 := [t0,t116,t1,t2,t59,t62,t4]
def v187 := [t81,t0,t1,t2,t62,t4]
def v188 := [t81,t0,t1,t2,t59,t62,t4]
def t117 := 0xb92e70c1c071c7
def v189 := [t117,t0,t1,t59,t62,t4]
def v190 := [t117,t0,t1,t2,t59,t62,t4]
def t118 := 0xb02c3001c071c0
def v191 := [t118,t0,t1,t2,t59,t4]
def v192 := [t118,t0,t1,t59,t62,t4]
def v193 := [t118,t0,t1,t2,t59,t62,t4]
def t119 := 0x346c1041e380000
def v194 := [t0,t1,t119,t2,t59,t62,t4]
def t120 := 0x3ffd9a69fff8e38
def v195 := [t0,t1,t2,t59,t62,t4,t120]
def t121 := 0x108200078e38
def v196 := [t121,t0,t1,t2,t59,t62,t4]
def t122 := 0xb9082081c00000
def v197 := [t122,t0,t1,t2,t59,t62,t4]
def v198 := [t0,t67,t1,t2,t59,t62,t4]
def v199 := [t0,t1,t2,t59,t68,t62,t4]
def v200 := [t69,t0,t1,t2,t59,t62,t4]
def v201 := [t93,t0,t1,t2,t59,t62,t4]
def t123 := 0x1423c3
def t124 := 0x488ccc
def t125 := 0xb62ff3
def t126 := 0xea8ffc
def t127 := 0xfeafc0
def v202 := [t123,t124,t125,t126,t127]
def p31_15 : Projection 29 12 := pick [0,1,3,4,6,7,9,10,12,13,15,16] rfl (by decide +kernel) (by decide)
def map31_1 : Projection 29 29 := pick [0,2,1,3,5,4,6,8,7,19,20,21,22,23,24,25,26,27,28,9,10,11,12,13,14,15,16,17,18] rfl (by decide +kernel) (by decide)
def v203 := [t70,t0,t1,t2,t59,t62,t4]
def v204 := [t0,t71,t1,t2,t59,t62,t4]
def v205 := [t0,t1,t2,t59,t62,t72,t4]
def v206 := [t73,t0,t1,t2,t59,t62,t4]
def map31_5 : Projection 29 29 := pick [3,5,4,0,2,1,6,8,7,20,19,21,25,26,27,22,23,24,28,10,9,11,15,16,17,12,13,14,18] rfl (by decide +kernel) (by decide)
def v207 := [t74,t0,t1,t2,t59,t62,t4]
def v208 := [t0,t75,t1,t2,t59,t62,t4]
def v209 := [t0,t1,t2,t59,t62,t4,t76]
def v210 := [t103,t1,t2,t59,t4,t76]
def t128 := 0x22d8b40d1fc7e00
def v211 := [t128,t1,t2,t59,t62,t4]
def t129 := 0x1d274b60e038000
def v212 := [t129,t1,t2,t59,t62,t4]
def v213 := [t0,t116,t1,t62,t4,t76]
def t130 := 0x346d1861e3f8e00
def v214 := [t0,t1,t130,t59,t62,t4]
def t131 := 0xb92e70c1c07000
def v215 := [t131,t0,t1,t59,t62,t4]
def v216 := [t0,t75,t2,t59,t62,t76]
def v217 := [t0,t1,t2,t89,t4,t76]
def t132 := 0x3bdef70dffffe00
def v218 := [t0,t1,t2,t132,t62,t4]
def t133 := 0x42108600000000
def v219 := [t133,t0,t1,t2,t62,t4]
def t134 := 0x3f6fdb61ffffe00
def v220 := [t0,t1,t2,t59,t134,t4]
def t135 := 0x90240c0000000
def v221 := [t135,t0,t1,t2,t59,t4]
def v222 := [t77,t0,t1,t2,t59,t62,t4]
def v223 := [t78,t0,t1,t2,t59,t62,t4]
def v224 := [t0,t1,t2,t89,t4]
def v225 := [t0,t1,t2,t89,t59,t4]
def v226 := [t0,t1,t2,t89,t62,t4]
def v227 := [t0,t1,t2,t89,t59,t62,t4]
def v228 := [t0,t1,t2,t90,t59,t62,t4]
def v229 := [t0,t1,t2,t59,t62,t4,t91]
def v230 := [t92,t0,t1,t2,t59,t62,t4]
def v231 := [t0,t1,t2,t59,t94,t62,t4]
def v232 := [t0,t1,t2,t59,t62,t4,t95]
def v233 := [t96,t0,t1,t2,t59,t62,t4]
def v234 := [t97,t0,t1,t2,t59,t62,t4]
def v235 := [t0,t1,t2,t56,t3,t59,t4]
def map30_1 : Projection 12 12 := pick [0,2,1,3,5,4,9,10,11,6,7,8] rfl (by decide +kernel) (by decide)
def map30_3 : Projection 12 12 := pick [3,5,4,0,2,1,10,9,11,7,6,8] rfl (by decide +kernel) (by decide)
def map30_2 : Projection 12 12 := pick [3,4,5,0,1,2,7,6,8,10,9,11] rfl (by decide +kernel) (by decide)
def v236 := [t58,t1,t2,t56,t3,t4]
def v237 := [t34,t49,t6,t7,t8,t9]
def t136 := 0xbd61c7
def v238 := [t6,t7,t136,t8,t9]
def v239 := [t49,t6,t7,t136,t8,t9]
def t137 := 0x204007
def v240 := [t137,t6,t7,t8,t9]
def v241 := [t137,t49,t6,t7,t8,t9]
def v242 := [t49,t32,t6,t7,t8,t9]
def v243 := [t49,t27,t6,t7,t8,t9]
def v244 := [t49,t6,t7,t9,t53]
def v245 := [t49,t6,t7,t8,t9,t53]
def v246 := [t55,t49,t6,t7,t8,t9]
def t138 := 0xf66e07
def v247 := [t6,t7,t8,t9,t138]
def v248 := [t49,t6,t7,t8,t9,t138]
def v249 := [t22,t49,t6,t7,t8,t9]
def v250 := [t49,t6,t7,t30,t8,t9]
def v251 := [t49,t10,t6,t7,t8,t9]
def v252 := [t49,t6,t7,t11,t8,t9]
def v253 := [t12,t49,t6,t7,t8,t9]
def v254 := [t13,t49,t6,t7,t8,t9]
def v255 := [t49,t6,t7,t33,t9]
def v256 := [t49,t6,t7,t8,t33,t9]
def v257 := [t49,t35,t6,t7,t9]
def t139 := 0x4f21ff
def v258 := [t14,t139,t6,t8,t9]
def v259 := [t28,t139,t6,t8,t9]
def v260 := [t28,t6,t16,t8,t9]
def v261 := [t17,t28,t6,t8,t9]
def v262 := [t28,t6,t8,t21,t9]
def v263 := [t22,t28,t6,t8,t9]
def v264 := [t14,t28,t6,t8,t24]
def v265 := [t28,t6,t8,t9,t24]
def t140 := 0xdf21f8
def v266 := [t14,t6,t8,t140,t9]
def t141 := 0x420038
def v267 := [t14,t141,t6,t8,t9]
def v268 := [t14,t28,t27,t6,t9]
def v269 := [t14,t29,t28,t6,t8]
def t142 := 0x90038
def v270 := [t14,t142,t28,t6,t8]
def v271 := [t14,t28,t6,t8,t25]
def v272 := [t14,t28,t26,t6,t8]
def v273 := [t14,t28,t6,t30,t8]
def v274 := [t14,t31,t28,t6,t8]
def v275 := [t49,t35,t6,t7,t8,t9]
def v276 := [t49,t36,t6,t7,t8,t9]
def v277 := [t49,t6,t7,t8,t9,t25]
def v278 := [t37,t49,t6,t7,t8,t9]
def v279 := [t49,t26,t6,t7,t8,t9]
def v280 := [t49,t28,t6,t9]
def t143 := 0x6f603f
def v281 := [t143,t6,t9]
def v282 := [t49,t143,t6,t9]
def v283 := [t28,t143,t6,t9]
def v284 := [t49,t28,t143,t6,t9]
def v285 := [t34,t49,t28,t6,t9]
def v286 := [t49,t28,t6,t136,t9]
def v287 := [t137,t49,t28,t6,t9]
def v288 := [t49,t28,t32,t6,t9]
def v289 := [t55,t49,t28,t6,t9]
def v290 := [t49,t28,t6,t9,t138]
def v291 := [t22,t49,t28,t6,t9]
def v292 := [t49,t28,t6,t30,t9]
def v293 := [t12,t49,t28,t6,t9]
def v294 := [t49,t28,t6,t140,t9]
def v295 := [t49,t141,t28,t6,t9]
def v296 := [t49,t28,t10,t6,t9]
def v297 := [t49,t29,t28,t6,t9]
def t144 := 0xfb4e38
def v298 := [t49,t28,t6,t9,t144]
def v299 := [t142,t49,t28,t6,t9]
def v300 := [t49,t28,t6,t19,t9]
def v301 := [t49,t28,t36,t6,t9]
def v302 := [t49,t28,t6,t9,t25]
def v303 := [t37,t49,t28,t6,t9]
def v304 := [t49,t28,t26,t6,t9]
def v305 := [t49,t28,t6,t7,t9]
def v306 := [t49,t28,t6,t8,t9]
def v307 := [t49,t28,t6,t7,t8,t9]
def v308 := [t49,t6,t19,t7,t8,t9]
def v309 := [t49,t6,t7,t8,t9,t24]
def v310 := [t14,t49,t6,t7,t8,t9]
def v311 := [t49,t29,t6,t7,t8,t9]
def v312 := [t49,t6,t7,t9,t54]
def v313 := [t49,t6,t7,t8,t9,t54]
def v314 := [t31,t49,t6,t7,t9]
def v315 := [t31,t49,t6,t7,t8,t9]
def v316 := [t58,t0,t1,t2,t56,t3,t4]
def v317 := [t102,t0,t1,t2,t56,t3,t4]
def v318 := [t58,t0,t1,t2,t3,t62,t4]
def map31_10 : Projection 29 29 := pick [6,7,8,3,4,5,0,1,2,16,15,17,13,12,14,10,9,11,18,26,25,27,23,22,24,20,19,21,28] rfl (by decide +kernel) (by decide)
def v319 := [t98,t0,t1,t2,t56,t3,t4]
def t145 := 0xa20f30
def v320 := [t123,t124,t145,t127]
def t146 := 0x5cafcf
def v321 := [t123,t124,t146,t145,t127]
def t147 := 0xc0
def v322 := [t147,t146,t145,t127]
def v323 := [t147,t123,t146,t145,t127]
def v324 := [t147,t124,t146,t145,t127]
def t148 := 0x142303
def v325 := [t148,t123,t146,t145,t127]
def t149 := 0x488c0c
def v326 := [t149,t124,t146,t145,t127]
def v327 := [t123,t149,t124,t145,t127]
def v328 := [t124,t146,t145,t125,t127]
def t150 := 0x1420c3
def v329 := [t150,t124,t146,t145,t127]
def t151 := 0x1423c0
def v330 := [t151,t124,t146,t145,t127]
def t152 := 0xea8c00
def v331 := [t124,t146,t145,t152,t127]
def v332 := [t148,t123,t124,t145,t127]
def v333 := [t123,t146,t145,t126,t127]
def t153 := 0x4880cc
def v334 := [t123,t153,t146,t145,t127]
def t154 := 0x488cc0
def v335 := [t123,t154,t146,t145,t127]
def t155 := 0xb62300
def v336 := [t123,t146,t145,t155,t127]
def t156 := 0xf00
def v337 := [t156,t123,t124,t145,t127]
def t157 := 0xfeafff
def v338 := [t123,t124,t145,t127,t157]
def t158 := 0x5ca0cf
def v339 := [t123,t124,t158,t145,t127]
def t159 := 0xa20030
def v340 := [t123,t124,t159,t145,t127]
def t160 := 0x5cafc0
def v341 := [t123,t124,t160,t145,t127]
def t161 := 0xfeafcf
def v342 := [t123,t124,t145,t127,t161]
def t162 := 0xf
def v343 := [t162,t123,t124,t145,t127]
def t163 := 0xa20000
def v344 := [t123,t124,t163,t145,t127]
def p31_23 : Projection 29 12 := pick [0,2,3,5,6,8,19,20,22,23,25,26] rfl (by decide +kernel) (by decide)
def v345 := [t0,t1,t99,t2,t56,t3,t4]
def v346 := [t10,t11,t8,t9]
def t164 := 0x294e07
def v347 := [t164,t8,t9]
def v348 := [t164,t10,t8,t9]
def v349 := [t164,t11,t8,t9]
def v350 := [t164,t10,t11,t8,t9]
def v351 := [t45,t10,t11,t8,t9]
def v352 := [t10,t11,t8,t33,t9]
def v353 := [t34,t10,t11,t8,t9]
def t165 := 0x4b0e38
def v354 := [t165,t10,t11,t8,t9]
def v355 := [t36,t10,t11,t8,t9]
def t166 := 0xf66fc0
def v356 := [t10,t11,t8,t9,t166]
def v357 := [t15,t10,t11,t8,t9]
def v358 := [t26,t10,t11,t8,t9]
def t167 := 0x990fc0
def v359 := [t10,t167,t11,t8,t9]
def v360 := [t10,t11,t8,t9,t53]
def v361 := [t49,t10,t11,t8,t9]
def v362 := [t141,t10,t11,t8,t9]
def v363 := [t10,t19,t11,t8,t9]
def v364 := [t10,t11,t8,t9,t39]
def t168 := 0xd21c7
def v365 := [t168,t10,t11,t8,t9]
def v366 := [t29,t10,t11,t8,t9]
def v367 := [t10,t11,t30,t8,t9]
def v368 := [t10,t11,t8,t9,t54]
def v369 := [t31,t10,t11,t8,t9]
def v370 := [t55,t10,t11,t8,t9]
def v371 := [t10,t6,t11,t8,t9]
def v372 := [t10,t7,t11,t8,t9]
def v373 := [t10,t6,t7,t11,t8,t9]
def v374 := [t12,t6,t11,t8,t9]
def v375 := [t12,t6,t7,t11,t8,t9]
def v376 := [t13,t7,t11,t8,t9]
def v377 := [t13,t6,t7,t11,t8,t9]
def v378 := [t32,t6,t7,t11,t8,t9]
def v379 := [t6,t7,t11,t8,t33,t9]
def v380 := [t34,t6,t7,t11,t8,t9]
def v381 := [t35,t6,t7,t11,t8,t9]
def v382 := [t36,t6,t7,t11,t8,t9]
def v383 := [t6,t7,t11,t8,t9,t25]
def v384 := [t37,t6,t7,t11,t8,t9]
def v385 := [t26,t6,t7,t11,t8,t9]
def v386 := [t45,t6,t7,t33,t9]
def v387 := [t48,t6,t7,t33,t9]
def v388 := [t49,t27,t6,t33,t9]
def t169 := 0x4f2038
def v389 := [t169,t27,t6,t7,t9]
def v390 := [t169,t6,t7,t33,t9]
def v391 := [t6,t7,t33,t9,t51]
def v392 := [t20,t6,t7,t33,t9]
def v393 := [t27,t6,t11,t33,t9]
def v394 := [t13,t27,t6,t33,t9]
def v395 := [t35,t27,t7,t33,t9]
def v396 := [t27,t6,t33,t9,t53]
def v397 := [t137,t27,t6,t33,t9]
def v398 := [t27,t6,t33,t9,t24]
def v399 := [t14,t27,t6,t33,t9]
def v400 := [t27,t6,t7,t9,t42]
def t170 := 0xd21f8
def v401 := [t170,t27,t6,t7,t9]
def v402 := [t27,t6,t7,t11,t8,t9]
def v403 := [t6,t7,t11,t8,t9,t53]
def v404 := [t28,t6,t11,t8,t9]
def v405 := [t28,t6,t7,t11,t8,t9]
def v406 := [t6,t19,t7,t11,t8,t9]
def v407 := [t6,t11,t8,t9,t24]
def v408 := [t6,t7,t11,t8,t9,t24]
def v409 := [t15,t6,t11,t8,t9]
def v410 := [t18,t6,t11,t8,t9]
def t171 := 0xb94e00
def v411 := [t14,t6,t171,t8,t9]
def v412 := [t6,t171,t11,t8,t9]
def v413 := [t20,t6,t11,t8,t9]
def v414 := [t6,t11,t23,t8,t9]
def v415 := [t14,t6,t11,t8,t24]
def v416 := [t14,t13,t11,t8,t9]
def v417 := [t14,t6,t11,t8,t25]
def v418 := [t14,t26,t6,t11,t8]
def v419 := [t14,t167,t6,t8,t9]
def v420 := [t14,t6,t11,t8,t39]
def v421 := [t14,t29,t6,t11,t8]
def v422 := [t14,t6,t11,t30,t8]
def v423 := [t14,t31,t6,t11,t8]
def v424 := [t14,t6,t7,t11,t8,t9]
def v425 := [t29,t6,t7,t11,t8,t9]
def v426 := [t167,t6,t7,t8,t9]
def v427 := [t167,t6,t7,t11,t8,t9]
def v428 := [t141,t6,t7,t8,t9]
def v429 := [t141,t6,t7,t11,t8,t9]
def v430 := [t6,t7,t11,t8,t9,t39]
def v431 := [t168,t6,t7,t8,t9]
def v432 := [t168,t6,t7,t11,t8,t9]
def v433 := [t6,t7,t11,t30,t8,t9]
def v434 := [t6,t7,t11,t8,t9,t54]
def v435 := [t31,t6,t7,t11,t8,t9]
def v436 := [t55,t6,t7,t11,t8,t9]
def v437 := [t100,t0,t1,t2,t56,t3,t4]
def v438 := [t114,t0,t1,t2,t56,t3,t4]
def v439 := [t101,t0,t1,t2,t56,t3,t4]
def t172 := 0x413c240000e00
def v440 := [t172,t0,t1,t2,t3,t59,t4]
def v441 := [t123,t124,t145,t125,t127]
def map23_1 : Projection 12 12 := pick [0,1,4,5,2,3,8,9,6,7,11,10] rfl (by decide +kernel) (by decide)
def v442 := [t60,t0,t1,t2,t3,t4]
def v443 := [t58,t0,t1,t2,t3,t4]
def v444 := [t147,t123,t124,t145,t127]
def t173 := 0x300
def v445 := [t173,t123,t124,t145,t127]
def map15_1 : Projection 12 12 := pick [0,1,4,5,2,3,8,9,6,7,11,10] rfl (by decide +kernel) (by decide)
def v446 := [t150,t123,t124,t145,t127]
def t174 := 0xa20c30
def v447 := [t123,t124,t174,t145,t127]
def v448 := [t151,t123,t124,t145,t127]
def t175 := 0xfeafc3
def v449 := [t123,t124,t145,t127,t175]
def t176 := 0x3
def v450 := [t176,t123,t124,t145,t127]
def v451 := [t123,t124,t145,t152,t127]
def t177 := 0x5ca0c0
def v452 := [t123,t124,t177,t145,t127]
def t178 := 0x1420c0
def v453 := [t178,t123,t124,t145,t127]
def t179 := 0x5ca3c3
def v454 := [t123,t124,t179,t145,t127]
def t180 := 0x303
def v455 := [t180,t123,t124,t145,t127]
def t181 := 0x488000
def v456 := [t123,t181,t124,t145,t127]
def v457 := [t123,t124,t177,t125,t127]
def v458 := [t123,t124,t177,t174,t127]
def v459 := [t123,t124,t177,t145,t175]
def v460 := [t123,t124,t177,t145,t152]
def t182 := 0x4880c0
def v461 := [t123,t182,t124,t145,t127]
def t183 := 0x5caccc
def v462 := [t123,t124,t183,t145,t127]
def t184 := 0xc0c
def v463 := [t184,t123,t124,t145,t127]
def t185 := 0x142000
def v464 := [t185,t123,t124,t145,t127]
def v465 := [t123,t124,t177,t126,t127]
def t186 := 0xa20330
def v466 := [t123,t124,t177,t186,t127]
def t187 := 0xfeafcc
def v467 := [t123,t124,t177,t145,t187]
def v468 := [t123,t124,t177,t145,t155]
def t188 := 0xfeaff0
def v469 := [t123,t124,t177,t127,t188]
def v470 := [t123,t124,t145,t127,t188]
def t189 := 0xa20f00
def v471 := [t123,t124,t177,t189,t145]
def v472 := [t123,t124,t189,t145,t127]
def t190 := 0x30
def v473 := [t190,t123,t124,t177]
def v474 := [t190,t123,t124,t177,t145]
def v475 := [t190,t123,t124,t177,t127]
def map15_3 : Projection 12 12 := pick [2,3,4,5,0,1,10,11,7,6,9,8] rfl (by decide +kernel) (by decide)
def map15_4 : Projection 12 12 := pick [4,5,0,1,2,3,9,8,11,10,6,7] rfl (by decide +kernel) (by decide)
def t191 := 0xc00
def v476 := [t191,t123,t124,t145,t127]
def v477 := [t123,t124,t145,t126,t127]
def v478 := [t123,t153,t124,t145,t127]
def v479 := [t123,t124,t186,t145,t127]
def v480 := [t123,t154,t124,t145,t127]
def v481 := [t123,t124,t145,t127,t187]
def t192 := 0xc
def v482 := [t192,t123,t124,t145,t127]
def v483 := [t123,t124,t145,t155,t127]
def v484 := [t190,t123,t124,t145,t127]
def v485 := [t173,t150,t124,t145,t127]
def v486 := [t173,t150,t123,t124,t145,t127]
def v487 := [t147,t150,t123,t124,t145,t127]
def t193 := 0x5caccf
def v488 := [t123,t124,t193,t145,t127]
def v489 := [t150,t123,t124,t193,t145,t127]
def t194 := 0x142003
def v490 := [t194,t123,t124,t145,t127]
def v491 := [t194,t150,t123,t124,t145,t127]
def v492 := [t150,t123,t149,t124,t145,t127]
def v493 := [t150,t123,t124,t125,t127]
def v494 := [t150,t123,t124,t145,t125,t127]
def v495 := [t178,t150,t123,t124,t145,t127]
def v496 := [t150,t123,t124,t145,t127,t175]
def v497 := [t176,t150,t123,t124,t145,t127]
def t195 := 0xea8f00
def v498 := [t123,t124,t145,t195,t127]
def v499 := [t150,t123,t124,t145,t195,t127]
def v500 := [t147,t150,t146,t145,t127]
def v501 := [t194,t150,t146,t145,t127]
def t196 := 0x488f0c
def v502 := [t150,t124,t196,t145,t127]
def v503 := [t124,t196,t146,t145,t127]
def v504 := [t150,t124,t146,t125,t127]
def v505 := [t178,t124,t146,t145,t127]
def v506 := [t124,t146,t145,t195,t127]
def v507 := [t150,t148,t124,t145,t127]
def v508 := [t150,t148,t146,t145,t127]
def v509 := [t150,t146,t145,t126,t127]
def v510 := [t150,t153,t146,t145,t127]
def v511 := [t150,t154,t146,t145,t127]
def v512 := [t150,t146,t145,t155,t127]
def v513 := [t156,t150,t124,t145,t127]
def v514 := [t150,t124,t159,t145,t127]
def v515 := [t150,t124,t160,t145,t127]
def v516 := [t150,t124,t163,t145,t127]
def v517 := [t150,t123,t124,t146,t145,t127]
def v518 := [t150,t148,t123,t124,t145,t127]
def v519 := [t150,t124,t174,t127]
def v520 := [t147,t150,t124,t174,t127]
def v521 := [t150,t124,t193,t174,t127]
def v522 := [t194,t150,t124,t174,t127]
def v523 := [t150,t149,t124,t174,t127]
def t197 := 0xb62cf3
def v524 := [t124,t197,t127]
def v525 := [t150,t124,t197,t127]
def v526 := [t124,t174,t197,t127]
def v527 := [t150,t124,t174,t197,t127]
def v528 := [t178,t150,t124,t174,t127]
def v529 := [t150,t124,t174,t127,t175]
def v530 := [t176,t150,t124,t174,t127]
def v531 := [t150,t124,t174,t195,t127]
def v532 := [t191,t150,t124,t174,t127]
def t198 := 0xea8cfc
def v533 := [t150,t124,t174,t198,t127]
def v534 := [t150,t153,t124,t174,t127]
def v535 := [t150,t124,t159,t174,t127]
def v536 := [t150,t154,t124,t174,t127]
def v537 := [t150,t124,t174,t127,t187]
def v538 := [t192,t150,t124,t174,t127]
def v539 := [t150,t124,t174,t155,t127]
def t199 := 0xa20c00
def v540 := [t150,t124,t199,t174,t127]
def v541 := [t150,t124,t174,t127,t188]
def v542 := [t190,t150,t124,t174,t127]
def t200 := 0x5ca3c0
def v543 := [t150,t124,t200,t174,t127]
def v544 := [t150,t123,t124,t174,t127]
def v545 := [t150,t124,t174,t145,t127]
def v546 := [t150,t123,t124,t174,t145,t127]
def v547 := [t150,t151,t124,t145,t127]
def v548 := [t150,t151,t123,t124,t145,t127]
def v549 := [t150,t124,t145,t152,t127]
def v550 := [t124,t193,t145,t152,t127]
def v551 := [t194,t124,t145,t152,t127]
def v552 := [t150,t124,t125,t152,t127]
def v553 := [t124,t145,t125,t152,t127]
def t201 := 0xfeacc3
def v554 := [t150,t124,t145,t201,t127]
def v555 := [t124,t145,t152,t201,t127]
def v556 := [t178,t150,t124,t145,t152]
def v557 := [t124,t145,t152,t127,t175]
def v558 := [t176,t124,t145,t152]
def v559 := [t176,t150,t124,t145,t152]
def v560 := [t176,t124,t145,t152,t127]
def t202 := 0xea8ccc
def v561 := [t150,t124,t145,t202,t127]
def v562 := [t150,t124,t145,t152,t187]
def v563 := [t150,t124,t145,t155,t152]
def v564 := [t150,t124,t199,t145,t127]
def t203 := 0x330
def v565 := [t203,t150,t124,t145,t127]
def v566 := [t150,t124,t145,t152,t188]
def v567 := [t150,t124,t177,t145,t152]
def v568 := [t150,t151,t124,t145,t152]
def v569 := [t150,t123,t124,t145,t152,t127]
def v570 := [t191,t150,t123,t124,t145,t127]
def v571 := [t150,t123,t124,t145,t126,t127]
def v572 := [t150,t123,t153,t124,t145,t127]
def v573 := [t150,t123,t124,t186,t145,t127]
def v574 := [t150,t123,t154,t124,t145,t127]
def v575 := [t150,t123,t124,t145,t127,t187]
def v576 := [t192,t150,t123,t124,t145,t127]
def v577 := [t150,t123,t124,t145,t155,t127]
def v578 := [t150,t123,t124,t189,t145,t127]
def v579 := [t150,t123,t124,t145,t127,t188]
def v580 := [t190,t150,t123,t124,t145,t127]
def v581 := [t150,t123,t124,t177,t145,t127]
def v582 := [t108,t0,t1,t2,t56,t3,t4]
def v583 := [t0,t1,t2,t56,t3,t4,t109]
def v584 := [t110,t0,t1,t2,t56,t3,t4]
def v585 := [t111,t0,t1,t2,t56,t3,t4]
def map31_7 : Projection 29 29 := pick [3,5,4,6,8,7,0,2,1,25,26,27,20,19,21,23,22,24,28,15,16,17,10,9,11,13,12,14,18] rfl (by decide +kernel) (by decide)
def map31_9 : Projection 29 29 := pick [6,8,7,0,2,1,3,5,4,23,22,24,26,25,27,19,20,21,28,13,12,14,16,15,17,9,10,11,18] rfl (by decide +kernel) (by decide)
def t204 := 0x300c0001e078000
def v586 := [t0,t204,t1,t2,t56,t3,t4]
def v587 := [t0,t1,t56,t3,t62,t4]
def v588 := [t0,t1,t2,t56,t3,t62,t4]
def t205 := 0x46118600380e38
def v589 := [t205,t0,t1,t56,t3,t4]
def v590 := [t205,t0,t1,t2,t56,t3,t4]
def v591 := [t118,t0,t1,t2,t56,t3,t4]
def v592 := [t0,t112,t1,t2,t56,t3,t4]
def v593 := [t0,t1,t2,t113,t56,t3,t4]
def v594 := [t115,t0,t1,t2,t56,t3,t4]
def v595 := [t57,t0,t1,t2,t3,t4]
def v596 := [t0,t1,t119,t2,t56,t3,t4]
def v597 := [t0,t1,t2,t56,t3,t4,t120]
def v598 := [t121,t0,t1,t2,t56,t3,t4]
def v599 := [t122,t0,t1,t2,t56,t3,t4]
def map31_3 : Projection 29 29 := pick [0,2,1,6,8,7,3,5,4,22,23,24,19,20,21,26,25,27,28,12,13,14,9,10,11,16,15,17,18] rfl (by decide +kernel) (by decide)
def t206 := 0x320ec100007f000
def v600 := [t0,t206,t1,t2,t56,t3,t4]
def v601 := [t98,t0,t1,t2,t3,t62,t4]
def map23_3 : Projection 12 12 := pick [2,3,4,5,0,1,10,11,7,6,9,8] rfl (by decide +kernel) (by decide)
def map23_4 : Projection 12 12 := pick [4,5,0,1,2,3,9,8,11,10,6,7] rfl (by decide +kernel) (by decide)
def t207 := 0x3b4fff25fc7ffc0
def v602 := [t0,t1,t2,t56,t3,t207,t4]
def v603 := [t0,t1,t99,t2,t3,t62,t4]
def t208 := 0x9000201fc001c0
def v604 := [t208,t0,t1,t2,t56,t3,t4]
def v605 := [t114,t0,t1,t2,t3,t59,t4]
def v606 := [t172,t0,t1,t2,t56,t3,t4]
def t209 := 0x320c8001fc7f000
def v607 := [t0,t209,t1,t2,t3,t4]
def v608 := [t103,t0,t1,t2,t3,t4]
def v609 := [t0,t209,t1,t2,t56,t3,t4]
def v610 := [t103,t0,t1,t2,t3,t62,t4]
def v611 := [t0,t1,t2,t3,t4,t80]
def v612 := [t5,t0,t1,t2,t3,t4,t80]
def v613 := [t0,t1,t2,t56,t3,t4,t80]
def v614 := [t57,t0,t1,t2,t3,t4,t80]
def v615 := [t60,t0,t1,t2,t3,t4,t80]
def v616 := [t61,t0,t1,t2,t3,t4,t80]
def v617 := [t0,t1,t2,t3,t59,t4,t80]
def v618 := [t58,t0,t1,t2,t3,t4,t80]
def v619 := [t102,t0,t1,t2,t3,t4,t80]
def v620 := [t98,t0,t1,t2,t3,t4,t80]
def v621 := [t0,t1,t99,t2,t3,t4,t80]
def v622 := [t100,t0,t1,t2,t3,t4,t80]
def v623 := [t101,t0,t1,t2,t3,t4,t80]
def v624 := [t108,t0,t1,t2,t3,t4,t80]
def v625 := [t0,t1,t2,t3,t4,t109,t80]
def v626 := [t110,t0,t1,t2,t3,t4,t80]
def v627 := [t111,t0,t1,t2,t3,t4,t80]
def v628 := [t107,t0,t1,t2,t3,t4]
def v629 := [t107,t1,t2,t3,t4,t80]
def v630 := [t107,t0,t1,t2,t3,t4,t80]
def v631 := [t0,t204,t1,t2,t3,t4,t80]
def v632 := [t0,t1,t2,t3,t62,t4,t80]
def v633 := [t205,t0,t1,t2,t3,t4,t80]
def v634 := [t118,t0,t1,t2,t3,t4,t80]
def v635 := [t0,t112,t1,t2,t3,t4,t80]
def v636 := [t0,t1,t2,t113,t3,t4,t80]
def v637 := [t114,t0,t1,t2,t3,t4,t80]
def v638 := [t115,t0,t1,t2,t3,t4,t80]
def v639 := [t0,t1,t119,t2,t3,t4,t80]
def v640 := [t0,t1,t2,t3,t4,t120,t80]
def v641 := [t121,t0,t1,t2,t3,t4,t80]
def v642 := [t122,t0,t1,t2,t3,t4,t80]
def v643 := [t117,t0,t1,t2,t3,t4]
def v644 := [t117,t0,t1,t3,t4,t80]
def v645 := [t117,t0,t1,t2,t3,t4,t80]
def v646 := [t0,t206,t1,t2,t3,t4,t80]
def v647 := [t0,t1,t2,t3,t207,t4,t80]
def v648 := [t208,t0,t1,t2,t3,t4,t80]
def v649 := [t172,t0,t1,t2,t3,t4,t80]
def t210 := 0x3b0c8201fc00000
def v650 := [t0,t1,t2,t210,t3,t4,t80]
def t211 := 0x3ffed349ffff1c0
def v651 := [t0,t1,t2,t3,t4,t211,t80]
def t212 := 0x24100007f1c0
def v652 := [t212,t0,t1,t2,t3,t4,t80]
def t213 := 0x4f010480380000
def v653 := [t213,t0,t1,t2,t3,t4,t80]
def t214 := 0x4f13c6c0380e3f
def v654 := [t214,t0,t1,t2,t3,t4]
def v655 := [t214,t0,t1,t2,t4,t80]
def v656 := [t214,t0,t1,t2,t3,t4,t80]
def v657 := [t0,t75,t1,t2,t3,t4,t80]
def v658 := [t0,t1,t2,t3,t4,t76,t80]
def v659 := [t77,t0,t1,t2,t3,t4,t80]
def v660 := [t78,t0,t1,t2,t3,t4,t80]
def t215 := 0xdb00249ff801ff
def v661 := [t215,t0,t2,t3,t4]
def v662 := [t100,t215,t0,t2,t3,t4]
def t216 := 0x2ff8b64dffc7fff
def v663 := [t215,t0,t216,t2,t3,t4]
def t217 := 0xd200240e0001f8
def v664 := [t217,t215,t0,t2,t3,t4]
def v665 := [t215,t98,t0,t2,t3,t4]
def v666 := [t114,t215,t0,t2,t3,t4]
def t218 := 0x3dfd1a69fff8fff
def v667 := [t215,t0,t2,t3,t218,t4]
def t219 := 0x99002081c001c7
def v668 := [t219,t215,t0,t2,t3,t4]
def v669 := [t215,t0,t112,t2,t3,t4]
def v670 := [t208,t215,t0,t2,t3,t4]
def t220 := 0x3fbec349ffff1ff
def v671 := [t215,t0,t2,t3,t220,t4]
def t221 := 0x4b00048038003f
def v672 := [t221,t215,t0,t2,t3,t4]
def v673 := [t215,t0,t206,t2,t3,t4]
def v674 := [t78,t215,t0,t2,t3,t4]
def t222 := 0x3ffc9249ff801ff
def v675 := [t215,t0,t2,t3,t4,t222]
def t223 := 0x1ff
def v676 := [t223,t215,t0,t2,t3,t4]
def v677 := [t215,t0,t75,t2,t3,t4]
def v678 := [t215,t5,t0,t2,t3,t4]
def v679 := [t215,t0,t2,t56,t3,t4]
def v680 := [t57,t215,t0,t2,t3,t4]
def v681 := [t215,t60,t0,t2,t3,t4]
def v682 := [t215,t61,t0,t2,t3,t4]
def v683 := [t215,t0,t2,t3,t59,t4]
def v684 := [t58,t215,t0,t2,t3,t4]
def v685 := [t215,t102,t0,t2,t3,t4]
def v686 := [t215,t108,t0,t2,t3,t4]
def v687 := [t215,t0,t2,t3,t4,t109]
def v688 := [t110,t215,t0,t2,t3,t4]
def v689 := [t215,t111,t0,t2,t3,t4]
def v690 := [t215,t0,t204,t2,t3,t4]
def v691 := [t215,t0,t2,t3,t62,t4]
def v692 := [t205,t215,t0,t2,t3,t4]
def v693 := [t118,t215,t0,t2,t3,t4]
def v694 := [t215,t0,t119,t2,t3,t4]
def v695 := [t215,t0,t2,t3,t4,t120]
def v696 := [t121,t215,t0,t2,t3,t4]
def v697 := [t122,t215,t0,t2,t3,t4]
def v698 := [t215,t0,t2,t210,t3,t4]
def v699 := [t215,t0,t2,t3,t4,t211]
def v700 := [t212,t215,t0,t2,t3,t4]
def v701 := [t213,t215,t0,t2,t3,t4]
def v702 := [t215,t0,t1,t2,t3,t4]
def v703 := [t215,t0,t2,t3,t4,t80]
def v704 := [t215,t0,t1,t2,t3,t4,t80]
def t224 := 0x36d24007ffff
def v705 := [t224,t0,t1,t2,t3]
def v706 := [t224,t0,t1,t2,t3,t4]
def v707 := [t224,t0,t1,t2,t3,t80]
def v708 := [t224,t0,t1,t2,t3,t4,t80]
def v709 := [t5,t1,t56,t3,t4,t80]
def v710 := [t5,t0,t1,t56,t3,t4,t80]
def v711 := [t5,t1,t2,t56,t3,t4,t80]
def v712 := [t57,t0,t1,t56,t3,t4,t80]
def v713 := [t60,t1,t2,t56,t3,t4,t80]
def v714 := [t1,t2,t56,t3,t59,t4,t80]
def v715 := [t58,t1,t2,t56,t3,t4,t80]
def v716 := [t107,t1,t2,t56,t3,t4]
def v717 := [t107,t0,t1,t2,t56,t3,t4]
def v718 := [t107,t1,t2,t56,t3,t4,t80]
def v719 := [t0,t1,t56,t3,t62,t4,t80]
def v720 := [t205,t0,t1,t56,t3,t4,t80]
def v721 := [t117,t0,t1,t56,t3,t4]
def v722 := [t117,t0,t1,t2,t56,t3,t4]
def v723 := [t117,t0,t1,t56,t3,t4,t80]
def v724 := [t0,t209,t1,t2,t4,t80]
def v725 := [t103,t1,t2,t3,t4,t80]
def v726 := [t0,t209,t1,t2,t3,t4,t80]
def v727 := [t103,t0,t1,t2,t3,t4,t80]
def v728 := [t0,t209,t1,t2,t56,t4,t80]
def v729 := [t82,t0,t1,t2,t3,t4,t80]
def v730 := [t214,t0,t1,t2,t56,t4,t80]
def v731 := [t214,t0,t1,t2,t56,t3,t4]
def v732 := [t0,t63,t1,t2,t3,t4,t80]
def v733 := [t0,t1,t2,t64,t3,t4,t80]
def v734 := [t65,t0,t1,t2,t3,t4,t80]
def v735 := [t66,t0,t1,t2,t3,t4,t80]
def v736 := [t66,t215,t0,t2,t3,t4]
def t225 := 0x3ffdbe6dfffffff
def v737 := [t215,t0,t2,t3,t4,t225]
def t226 := 0x900020000001c0
def v738 := [t226,t215,t0,t2,t3,t4]
def v739 := [t215,t0,t63,t2,t3,t4]
def v740 := [t215,t5,t56,t3,t4]
def v741 := [t215,t5,t0,t56,t3,t4]
def v742 := [t215,t5,t2,t56,t3,t4]
def v743 := [t57,t215,t0,t56,t3,t4]
def v744 := [t215,t60,t2,t56,t3,t4]
def v745 := [t215,t2,t56,t3,t59,t4]
def v746 := [t58,t215,t2,t56,t3,t4]
def v747 := [t215,t0,t56,t3,t62,t4]
def v748 := [t205,t215,t0,t56,t3,t4]
def v749 := [t215,t0,t209,t2,t4]
def v750 := [t215,t0,t209,t2,t3,t4]
def v751 := [t215,t0,t209,t2,t56,t4]
def v752 := [t82,t215,t0,t2,t3,t4]
def v753 := [t214,t215,t0,t2,t4]
def v754 := [t214,t215,t0,t2,t3,t4]
def v755 := [t214,t215,t0,t2,t56,t4]
def v756 := [t215,t0,t2,t85,t3,t4]
def v757 := [t215,t0,t2,t3,t4,t86]
def v758 := [t87,t215,t0,t2,t3,t4]
def v759 := [t88,t215,t0,t2,t3,t4]
def v760 := [t215,t0,t1,t2,t56,t3,t4]
def v761 := [t215,t0,t2,t56,t3,t4,t80]
def v762 := [t0,t1,t2,t85,t3,t4,t80]
def v763 := [t0,t1,t2,t3,t4,t86,t80]
def v764 := [t87,t0,t1,t2,t3,t4,t80]
def v765 := [t88,t0,t1,t2,t3,t4,t80]
def v766 := [t82,t0,t1,t2,t3,t4]
def v767 := [t82,t0,t1,t2,t56,t3,t4]
def v768 := [t224,t0,t1,t2,t56,t3]
def v769 := [t224,t0,t1,t2,t56,t3,t4]
def v770 := [t224,t0,t1,t2,t56,t3,t80]
def v771 := [t81,t0,t1,t2,t3,t4]
def t227 := 0x48800c
def v772 := [t123,t227,t124,t145,t127]
def t228 := 0x3c0
def v773 := [t228,t194,t124,t145,t127]
def t229 := 0xcc0
def v774 := [t229,t123,t227,t145,t127]
def p15_13 : Projection 12 6 := pick [0,1,4,5,8,9] rfl (by decide +kernel) (by decide)
def map15_2 : Projection 12 12 := pick [2,3,0,1,4,5,7,6,10,11,8,9] rfl (by decide +kernel) (by decide)
def v775 := [t228,t123,t124,t145,t127]
def v776 := [t229,t123,t124,t145,t127]
def v777 := [t228,t194,t123,t124,t145,t127]
def v778 := [t194,t123,t193,t145,t127]
def v779 := [t194,t123,t124,t193,t145,t127]
def t230 := 0xb62f33
def v780 := [t194,t123,t124,t230,t127]
def v781 := [t123,t124,t145,t230,t127]
def v782 := [t194,t123,t124,t145,t230,t127]
def v783 := [t185,t194,t123,t124,t145,t127]
def v784 := [t194,t123,t124,t145,t127,t175]
def v785 := [t176,t194,t123,t124,t145,t127]
def t231 := 0xea8fc0
def v786 := [t123,t124,t145,t231,t127]
def v787 := [t194,t123,t124,t145,t231,t127]
def v788 := [t147,t194,t123,t124,t145,t127]
def v789 := [t194,t123,t146,t145,t127]
def v790 := [t194,t123,t124,t125,t127]
def p15_14 : Projection 12 6 := pick [2,3,4,5,10,11] rfl (by decide +kernel) (by decide)
def v791 := [t194,t123,t124,t146,t145,t127]
def v792 := [t194,t148,t123,t124,t145,t127]
def v793 := [t194,t123,t149,t145,t127]
def v794 := [t194,t123,t149,t124,t145,t127]
def v795 := [t173,t194,t123,t124,t145,t127]
def v796 := [t194,t123,t124,t145,t125,t127]
def v797 := [t194,t123,t124,t174,t127]
def v798 := [t194,t123,t124,t174,t145,t127]
def v799 := [t194,t151,t124,t145,t127]
def v800 := [t194,t151,t123,t124,t145,t127]
def v801 := [t194,t193,t145,t152,t127]
def v802 := [t194,t124,t230,t152,t127]
def v803 := [t124,t145,t230,t152,t127]
def t232 := 0xfeac03
def v804 := [t124,t145,t232,t127]
def v805 := [t194,t124,t145,t232,t127]
def v806 := [t124,t145,t152,t232,t127]
def v807 := [t185,t194,t124,t145,t152]
def v808 := [t176,t194,t124,t145,t152]
def v809 := [t194,t124,t145,t152,t187]
def v810 := [t194,t124,t145,t155,t152]
def v811 := [t194,t124,t145,t152,t188]
def v812 := [t194,t124,t177,t145,t152]
def v813 := [t194,t151,t124,t145,t152]
def v814 := [t194,t123,t124,t145,t152,t127]
def v815 := [t191,t194,t123,t124,t145,t127]
def v816 := [t194,t123,t124,t145,t126,t127]
def v817 := [t194,t123,t153,t124,t145,t127]
def v818 := [t194,t123,t124,t186,t145,t127]
def v819 := [t194,t123,t154,t124,t145,t127]
def v820 := [t194,t123,t124,t145,t127,t187]
def v821 := [t192,t194,t123,t124,t145,t127]
def v822 := [t194,t123,t124,t145,t155,t127]
def v823 := [t194,t123,t124,t189,t145,t127]
def v824 := [t194,t123,t124,t145,t127,t188]
def v825 := [t190,t194,t123,t124,t145,t127]
def v826 := [t194,t123,t124,t177,t145,t127]
def v827 := [t81,t0,t1,t2,t3,t59,t4]
def v828 := [t147,t123,t124,t158,t145,t127]
def v829 := [t123,t124,t158,t146,t145,t127]
def v830 := [t148,t123,t124,t158,t145,t127]
def v831 := [t123,t149,t124,t158,t145,t127]
def v832 := [t150,t123,t124,t158,t145,t127]
def t233 := 0x5ca3cf
def v833 := [t123,t124,t233,t145,t127]
def v834 := [t123,t124,t158,t233,t145,t127]
def v835 := [t173,t123,t124,t158,t145,t127]
def v836 := [t123,t227,t124,t158,t145,t127]
def v837 := [t123,t124,t158,t125,t127]
def v838 := [t124,t158,t146,t125,t127]
def v839 := [t148,t124,t158,t125,t127]
def v840 := [t124,t158,t233,t125,t127]
def v841 := [t173,t124,t125,t127]
def v842 := [t173,t123,t124,t125,t127]
def v843 := [t173,t124,t158,t125,t127]
def v844 := [t123,t124,t158,t174,t127]
def v845 := [t124,t158,t174,t125,t127]
def v846 := [t151,t124,t158,t125,t127]
def v847 := [t124,t158,t125,t152,t127]
def v848 := [t123,t124,t193,t125,t127]
def v849 := [t229,t123,t158,t125,t127]
def v850 := [t123,t124,t158,t127,t157]
def t234 := 0xb62333
def v851 := [t123,t158,t234,t127]
def v852 := [t123,t124,t158,t234,t127]
def v853 := [t123,t158,t234,t125,t127]
def v854 := [t123,t154,t158,t125,t127]
def v855 := [t123,t158,t155,t125,t127]
def v856 := [t123,t124,t189,t125,t127]
def t235 := 0xfeaff3
def v857 := [t123,t124,t158,t127,t235]
def t236 := 0x33
def v858 := [t236,t123,t124,t158,t127]
def v859 := [t123,t124,t158,t145,t125,t127]
def t237 := 0xea8c3c
def v860 := [t150,t124,t145,t237,t127]
def v861 := [t124,t193,t145,t237,t127]
def v862 := [t194,t124,t145,t237,t127]
def v863 := [t150,t124,t125,t237,t127]
def v864 := [t124,t145,t125,t237,t127]
def t238 := 0xfeacff
def v865 := [t150,t124,t145,t238,t127]
def v866 := [t124,t145,t237,t238,t127]
def v867 := [t124,t145,t237,t127,t175]
def v868 := [t176,t124,t145,t237,t127]
def v869 := [t191,t150,t124,t237,t127]
def v870 := [t150,t153,t124,t237,t127]
def v871 := [t150,t124,t145,t198,t127]
def v872 := [t150,t154,t145,t237,t127]
def v873 := [t150,t145,t155,t237,t127]
def v874 := [t150,t124,t174,t237,t127]
def v875 := [t150,t227,t124,t237,t127]
def v876 := [t150,t124,t189,t237,t127]
def v877 := [t150,t124,t177,t237,t127]
def map15_5 : Projection 12 12 := pick [4,5,2,3,0,1,11,10,9,8,7,6] rfl (by decide +kernel) (by decide)
def v878 := [t123,t124,t158,t174,t145,t127]
def v879 := [t151,t124,t158,t145,t127]
def v880 := [t151,t123,t124,t158,t145,t127]
def v881 := [t123,t124,t158,t145,t127,t175]
def v882 := [t176,t123,t124,t158,t145,t127]
def v883 := [t124,t158,t145,t152,t127]
def v884 := [t123,t124,t177,t234,t127]
def v885 := [t123,t177,t146,t234,t127]
def v886 := [t123,t149,t177,t234,t127]
def t239 := 0xb623f3
def v887 := [t123,t124,t177,t239,t127]
def v888 := [t123,t124,t177,t159,t127]
def v889 := [t151,t124,t177,t234,t127]
def v890 := [t123,t124,t177,t234,t175]
def v891 := [t124,t177,t234,t152]
def v892 := [t123,t124,t177,t234,t152]
def v893 := [t124,t177,t234,t152,t127]
def v894 := [t123,t177,t183,t234,t127]
def v895 := [t184,t123,t177,t234,t127]
def v896 := [t123,t124,t177,t127,t157]
def v897 := [t123,t177,t234,t127,t157]
def v898 := [t123,t177,t234,t187]
def v899 := [t123,t124,t177,t234,t187]
def v900 := [t123,t177,t234,t127,t187]
def v901 := [t192,t123,t177,t234,t127]
def v902 := [t123,t124,t177,t155,t234]
def t240 := 0xfea3f3
def v903 := [t123,t124,t177,t240,t127]
def t241 := 0xa20333
def v904 := [t123,t124,t177,t241,t127]
def v905 := [t123,t124,t177,t189,t234]
def v906 := [t123,t124,t189,t234,t127]
def v907 := [t123,t124,t177,t127,t235]
def v908 := [t236,t123,t124,t177]
def v909 := [t236,t123,t124,t177,t234]
def v910 := [t236,t123,t124,t177,t127]
def v911 := [t123,t124,t158,t145,t152,t127]
def v912 := [t123,t153,t124,t158,t145,t127]
def v913 := [t123,t124,t158,t193,t145,t127]
def v914 := [t191,t123,t124,t158,t145,t127]
def v915 := [t194,t123,t124,t158,t145,t127]
def v916 := [t123,t124,t158,t126,t127]
def v917 := [t123,t124,t158,t145,t126,t127]
def v918 := [t123,t124,t158,t186,t127]
def v919 := [t123,t124,t158,t186,t145,t127]
def v920 := [t123,t154,t158,t145,t127]
def v921 := [t123,t154,t124,t158,t145,t127]
def v922 := [t123,t124,t158,t145,t127,t187]
def v923 := [t192,t123,t124,t158,t145,t127]
def v924 := [t123,t158,t145,t155,t127]
def v925 := [t123,t124,t158,t145,t155,t127]
def v926 := [t123,t124,t158,t145,t127,t157]
def v927 := [t123,t124,t177,t158,t145,t127]
def v928 := [t123,t124,t158,t145,t127,t161]
def t242 := 0x1423cf
def v929 := [t242,t124,t145,t127]
def v930 := [t162,t242,t124,t145,t127]
def v931 := [t123,t242,t124,t145,t127]
def v932 := [t162,t151,t124,t145,t127]
def t243 := 0x488ccf
def v933 := [t123,t243,t145,t127]
def v934 := [t162,t123,t243,t145,t127]
def v935 := [t123,t124,t243,t145,t127]
def v936 := [t162,t123,t154,t145,t127]
def t244 := 0xa20f3f
def v937 := [t123,t124,t244,t127]
def v938 := [t162,t123,t124,t244,t127]
def v939 := [t123,t124,t145,t244,t127]
def v940 := [t162,t123,t124,t145,t161]
def v941 := [t162,t123,t124,t145,t175]
def v942 := [t162,t124,t145,t152]
def v943 := [t162,t123,t124,t145,t152]
def v944 := [t162,t124,t145,t152,t127]
def v945 := [t162,t123,t124,t145,t187]
def v946 := [t162,t123,t145,t155]
def v947 := [t162,t123,t124,t145,t155]
def v948 := [t162,t123,t145,t155,t127]
def v949 := [t162,t123,t124,t189,t145]
def v950 := [t162,t190,t123,t124,t145]
def v951 := [t162,t123,t124,t158,t145,t127]
def v952 := [t123,t124,t158,t189,t145,t127]
def v953 := [t123,t124,t158,t127,t188]
def v954 := [t151,t124,t158,t127,t188]
def v955 := [t123,t124,t158,t175,t188]
def v956 := [t124,t158,t152,t188]
def v957 := [t123,t124,t158,t152,t188]
def v958 := [t124,t158,t152,t127,t188]
def t245 := 0xea8c30
def v959 := [t124,t158,t245,t127]
def v960 := [t123,t124,t158,t245,t127]
def v961 := [t124,t158,t245,t127,t188]
def v962 := [t123,t154,t158,t127,t188]
def v963 := [t123,t124,t158,t187,t188]
def v964 := [t123,t158,t155,t188]
def v965 := [t123,t124,t158,t155,t188]
def v966 := [t123,t158,t155,t127,t188]
def t246 := 0xfeaffc
def v967 := [t123,t124,t158,t127,t246]
def t247 := 0xb62330
def v968 := [t123,t158,t247,t127]
def v969 := [t123,t124,t158,t247,t127]
def v970 := [t123,t158,t247,t127,t188]
def v971 := [t123,t124,t158,t161,t188]
def v972 := [t123,t124,t189,t188]
def v973 := [t123,t124,t158,t189,t188]
def v974 := [t123,t124,t189,t127,t188]
def v975 := [t190,t123,t124,t158,t127]
def v976 := [t190,t123,t124,t158,t188]
def v977 := [t123,t124,t158,t145,t127,t188]
def v978 := [t243,t145,t237,t127]
def v979 := [t176,t243,t145,t237,t127]
def v980 := [t124,t243,t145,t237,t127]
def t248 := 0xa20f33
def v981 := [t124,t248,t237,t127]
def v982 := [t176,t124,t248,t237,t127]
def v983 := [t124,t145,t248,t237,t127]
def t249 := 0xea8c3f
def v984 := [t124,t145,t249,t127]
def v985 := [t176,t124,t145,t249,t127]
def v986 := [t124,t145,t237,t249,t127]
def v987 := [t176,t124,t145,t237,t175]
def v988 := [t176,t154,t145,t237,t127]
def v989 := [t176,t145,t155,t237,t127]
def v990 := [t176,t124,t189,t237,t127]
def v991 := [t176,t124,t177,t237,t127]
def v992 := [t176,t124,t145,t152,t237]
def t250 := 0x3c
def v993 := [t176,t250,t124,t145,t237]
def v994 := [t176,t151,t124,t145,t127]
def v995 := [t190,t123,t124,t158,t145,t127]
def v996 := [t0,t1,t2,t56,t210,t3,t4]
def v997 := [t0,t1,t2,t56,t3,t4,t211]
def v998 := [t212,t0,t1,t2,t56,t3,t4]
def v999 := [t213,t0,t1,t2,t56,t3,t4]
def v1000 := [t0,t63,t1,t2,t3,t4]
def v1001 := [t147,t123,t124,t160,t145,t127]
def v1002 := [t123,t124,t160,t146,t145,t127]
def v1003 := [t148,t123,t124,t160,t145,t127]
def v1004 := [t123,t149,t124,t160,t145,t127]
def v1005 := [t151,t123,t124,t160,t145,t127]
def t251 := 0x5cafc3
def v1006 := [t123,t124,t251,t145,t127]
def v1007 := [t123,t124,t160,t251,t145,t127]
def v1008 := [t176,t123,t124,t160,t145,t127]
def t252 := 0x488c00
def v1009 := [t123,t252,t124,t145,t127]
def v1010 := [t123,t252,t124,t160,t145,t127]
def v1011 := [t173,t123,t124,t160,t145,t127]
def v1012 := [t124,t160,t145,t125,t127]
def t253 := 0xb62fc0
def v1013 := [t123,t124,t253,t126,t127]
def v1014 := [t146,t253,t126,t127]
def v1015 := [t123,t146,t253,t126,t127]
def v1016 := [t124,t146,t253,t126,t127]
def v1017 := [t148,t124,t253,t126,t127]
def v1018 := [t123,t149,t253,t126,t127]
def t254 := 0xb62fc3
def v1019 := [t123,t124,t254,t126,t127]
def v1020 := [t123,t124,t199,t126,t127]
def v1021 := [t123,t124,t253,t126,t175]
def v1022 := [t123,t124,t253,t152,t126]
def v1023 := [t229,t123,t126,t127]
def v1024 := [t229,t123,t124,t126,t127]
def v1025 := [t229,t123,t253,t126,t127]
def v1026 := [t123,t227,t124,t126,t127]
def v1027 := [t123,t155,t253,t126,t127]
def v1028 := [t123,t124,t186,t253,t127]
def v1029 := [t123,t186,t253,t126,t127]
def v1030 := [t123,t154,t253,t126]
def v1031 := [t123,t154,t124,t253,t126]
def v1032 := [t123,t154,t253,t126,t127]
def v1033 := [t192,t123,t124,t253,t126]
def t255 := 0xa20fc0
def v1034 := [t123,t124,t255,t126,t127]
def t256 := 0x48803c
def v1035 := [t123,t256,t124,t126,t127]
def v1036 := [t123,t181,t124,t253,t126]
def v1037 := [t123,t181,t124,t126,t127]
def v1038 := [t123,t124,t253,t231,t126]
def v1039 := [t250,t123,t124,t253,t126]
def v1040 := [t123,t124,t160,t145,t125,t127]
def v1041 := [t150,t123,t124,t160,t145,t127]
def v1042 := [t123,t124,t160,t174,t145,t127]
def v1043 := [t123,t124,t160,t145,t175]
def v1044 := [t147,t124,t160,t145,t175]
def v1045 := [t149,t124,t160,t145,t175]
def v1046 := [t151,t124,t145,t175]
def v1047 := [t151,t123,t124,t145,t175]
def v1048 := [t151,t124,t160,t145,t175]
def v1049 := [t176,t123,t124,t145,t175]
def v1050 := [t252,t124,t160,t145,t175]
def v1051 := [t124,t160,t145,t125,t175]
def v1052 := [t150,t124,t160,t145,t175]
def v1053 := [t123,t124,t160,t145,t152]
def v1054 := [t124,t160,t145,t152,t175]
def t257 := 0x5cafcc
def v1055 := [t123,t124,t257,t145,t175]
def t258 := 0x142300
def v1056 := [t258,t123,t124,t145,t175]
def v1057 := [t123,t160,t145,t126,t175]
def v1058 := [t123,t153,t160,t145,t175]
def v1059 := [t123,t124,t160,t145,t161]
def t259 := 0xb62303
def v1060 := [t123,t124,t160,t145,t259]
def v1061 := [t123,t124,t145,t175,t188]
def t260 := 0xa20003
def v1062 := [t123,t124,t160,t260,t145]
def v1063 := [t123,t124,t260,t145,t175]
def v1064 := [t123,t124,t160,t189,t145]
def v1065 := [t190,t123,t124,t160,t145]
def v1066 := [t123,t124,t160,t145,t127,t175]
def v1067 := [t123,t124,t177,t145,t253]
def v1068 := [t124,t177,t146,t145,t253]
def v1069 := [t148,t124,t177,t145,t253]
def v1070 := [t124,t179,t145,t253]
def v1071 := [t123,t124,t179,t145,t253]
def v1072 := [t124,t177,t179,t145,t253]
def v1073 := [t180,t124,t177,t145,t253]
def v1074 := [t123,t181,t124,t145,t253]
def v1075 := [t123,t124,t177,t253,t125]
def v1076 := [t123,t124,t177,t174,t253]
def v1077 := [t123,t124,t177,t145,t254]
def v1078 := [t123,t124,t177,t199,t145]
def v1079 := [t123,t182,t124,t145,t253]
def v1080 := [t184,t123,t124,t145,t253]
def v1081 := [t123,t124,t177,t253,t126]
def v1082 := [t123,t124,t177,t186,t253]
def v1083 := [t123,t124,t177,t253,t188]
def v1084 := [t123,t124,t145,t253,t188]
def v1085 := [t123,t124,t145,t253,t127]
def t261 := 0xb62ff0
def v1086 := [t123,t124,t177,t253,t261]
def v1087 := [t190,t123,t124,t177,t253]
def v1088 := [t123,t124,t160,t145,t152,t127]
def v1089 := [t123,t154,t124,t160,t145,t127]
def v1090 := [t123,t124,t257,t145,t127]
def v1091 := [t123,t124,t160,t257,t145,t127]
def v1092 := [t192,t123,t124,t160,t145,t127]
def v1093 := [t258,t123,t124,t145,t127]
def v1094 := [t258,t123,t124,t160,t145,t127]
def v1095 := [t191,t123,t124,t160,t145,t127]
def v1096 := [t123,t160,t145,t126,t127]
def v1097 := [t123,t124,t160,t145,t126,t127]
def v1098 := [t123,t153,t160,t145,t127]
def v1099 := [t123,t153,t124,t160,t145,t127]
def v1100 := [t123,t124,t160,t186,t145,t127]
def v1101 := [t123,t124,t160,t145,t187]
def v1102 := [t123,t124,t160,t145,t127,t187]
def v1103 := [t123,t124,t160,t145,t155]
def v1104 := [t123,t124,t160,t145,t155,t127]
def v1105 := [t156,t123,t124,t160,t145,t127]
def v1106 := [t123,t124,t160,t145,t127,t188]
def v1107 := [t123,t124,t177,t160,t145,t127]
def v1108 := [t123,t124,t160,t159,t145,t127]
def v1109 := [t123,t124,t160,t163,t145]
def v1110 := [t123,t124,t160,t163,t145,t127]
def v1111 := [t151,t123,t124,t145,t231]
def v1112 := [t123,t124,t160,t189,t145,t127]
def v1113 := [t176,t123,t124,t145,t231]
def v1114 := [t190,t123,t124,t160,t145,t127]
def v1115 := [t0,t63,t1,t2,t56,t3,t4]
def v1116 := [t0,t1,t2,t64,t3,t4]
def v1117 := [t147,t123,t124,t145,t127,t161]
def v1118 := [t123,t124,t146,t145,t127,t161]
def v1119 := [t148,t123,t124,t145,t127,t161]
def v1120 := [t123,t149,t124,t145,t127,t161]
def v1121 := [t173,t123,t124,t145,t127,t161]
def v1122 := [t123,t124,t145,t125,t127,t161]
def v1123 := [t150,t123,t124,t145,t127,t161]
def v1124 := [t123,t124,t174,t145,t127,t161]
def v1125 := [t151,t124,t145,t127,t161]
def v1126 := [t151,t123,t124,t145,t127,t161]
def v1127 := [t123,t124,t145,t127,t175,t161]
def v1128 := [t176,t123,t124,t145,t127,t161]
def v1129 := [t124,t145,t152,t127,t161]
def v1130 := [t151,t124,t177,t127,t235]
def v1131 := [t123,t124,t177,t175,t235]
def v1132 := [t124,t177,t152,t235]
def v1133 := [t123,t124,t177,t152,t235]
def v1134 := [t124,t177,t152,t127,t235]
def v1135 := [t123,t124,t177,t245,t127]
def v1136 := [t124,t177,t245,t127,t235]
def v1137 := [t123,t124,t177,t187,t235]
def v1138 := [t123,t124,t177,t155,t235]
def v1139 := [t123,t124,t177,t189,t235]
def v1140 := [t123,t124,t189,t127,t235]
def v1141 := [t123,t124,t248,t127]
def v1142 := [t123,t124,t177,t248,t127]
def v1143 := [t123,t124,t248,t127,t235]
def v1144 := [t236,t123,t124,t177,t235]
def v1145 := [t123,t124,t145,t152,t127,t161]
def t262 := 0xea8c0c
def v1146 := [t123,t124,t145,t262,t127]
def v1147 := [t124,t145,t262,t127,t161]
def v1148 := [t123,t124,t145,t262,t127,t161]
def v1149 := [t191,t123,t124,t145,t127,t161]
def v1150 := [t123,t124,t145,t126,t127,t161]
def v1151 := [t123,t153,t124,t145,t127,t161]
def v1152 := [t123,t124,t186,t145,t127,t161]
def v1153 := [t123,t154,t145,t127,t161]
def v1154 := [t123,t154,t124,t145,t127,t161]
def v1155 := [t123,t124,t145,t127,t187,t161]
def v1156 := [t192,t123,t124,t145,t127,t161]
def v1157 := [t123,t145,t155,t127,t161]
def v1158 := [t123,t124,t145,t155,t127,t161]
def v1159 := [t123,t124,t145,t259,t127]
def v1160 := [t123,t145,t259,t127,t161]
def v1161 := [t123,t124,t145,t259,t127,t161]
def v1162 := [t123,t124,t189,t145,t127,t161]
def v1163 := [t123,t124,t145,t161,t188]
def v1164 := [t123,t124,t145,t127,t161,t188]
def v1165 := [t190,t123,t124,t145,t127,t161]
def v1166 := [t123,t124,t177,t145,t161]
def v1167 := [t123,t124,t177,t125,t161]
def v1168 := [t123,t124,t177,t174,t161]
def v1169 := [t123,t124,t177,t145,t262]
def v1170 := [t124,t177,t145,t262,t161]
def v1171 := [t123,t124,t177,t126,t161]
def v1172 := [t123,t124,t177,t186,t161]
def v1173 := [t123,t124,t177,t145,t259]
def v1174 := [t123,t177,t145,t259,t161]
def v1175 := [t123,t124,t177,t161,t188]
def t263 := 0xa20f0f
def v1176 := [t123,t124,t263,t145]
def v1177 := [t123,t124,t177,t263,t145]
def v1178 := [t123,t124,t263,t145,t161]
def v1179 := [t123,t124,t177,t161,t157]
def v1180 := [t190,t123,t124,t177,t161]
def v1181 := [t123,t124,t177,t145,t127,t161]
def v1182 := [t123,t124,t145,t127,t161,t157]
def v1183 := [t162,t242,t124,t145,t161]
def v1184 := [t162,t151,t124,t145,t161]
def v1185 := [t162,t123,t243,t145,t161]
def v1186 := [t162,t123,t154,t145,t161]
def v1187 := [t123,t124,t244,t161]
def v1188 := [t162,t123,t124,t244,t161]
def v1189 := [t123,t124,t145,t244,t161]
def v1190 := [t162,t124,t145,t262]
def v1191 := [t162,t123,t124,t145,t262]
def v1192 := [t162,t124,t145,t262,t161]
def v1193 := [t162,t123,t145,t259]
def v1194 := [t162,t123,t124,t145,t259]
def v1195 := [t162,t123,t145,t259,t161]
def v1196 := [t162,t123,t124,t145,t127,t161]
def v1197 := [t0,t1,t2,t56,t64,t3,t4]
def v1198 := [t65,t0,t1,t2,t3,t4]
def v1199 := [t93,t0,t1,t2,t3,t4]
def v1200 := [t65,t0,t1,t2,t56,t3,t4]
def v1201 := [t93,t0,t1,t2,t3,t59,t4]
def v1202 := [t66,t0,t1,t2,t3,t4]
def v1203 := [t100,t0,t1,t2,t3,t4]
def v1204 := [t100,t66,t0,t1,t2,t3,t4]
def t264 := 0x26f8b44dffc7e3f
def v1205 := [t0,t264,t1,t2,t3,t4]
def v1206 := [t66,t0,t264,t1,t2,t3,t4]
def t265 := 0x4200040e000038
def v1207 := [t265,t0,t1,t2,t3,t4]
def v1208 := [t265,t66,t0,t1,t2,t3,t4]
def v1209 := [t98,t0,t1,t2,t3,t4]
def v1210 := [t66,t98,t0,t1,t2,t3,t4]
def v1211 := [t114,t0,t1,t2,t3,t4]
def v1212 := [t114,t66,t0,t1,t2,t3,t4]
def t266 := 0x34fd1869fff8e3f
def v1213 := [t0,t1,t2,t266,t3,t4]
def v1214 := [t66,t0,t1,t2,t266,t3,t4]
def t267 := 0x9000081c00007
def v1215 := [t267,t0,t1,t2,t3,t4]
def v1216 := [t267,t66,t0,t1,t2,t3,t4]
def v1217 := [t0,t112,t1,t2,t3,t4]
def v1218 := [t66,t0,t112,t1,t2,t3,t4]
def t268 := 0x1fc00000
def v1219 := [t268,t0,t1,t2,t3,t4]
def v1220 := [t268,t66,t0,t1,t2,t3,t4]
def v1221 := [t0,t1,t2,t3,t220,t4]
def v1222 := [t66,t0,t1,t2,t3,t220,t4]
def v1223 := [t221,t0,t1,t2,t3,t4]
def v1224 := [t221,t66,t0,t1,t2,t3,t4]
def t269 := 0x3b0ec300007f1c0
def v1225 := [t0,t1,t2,t269,t3,t4]
def v1226 := [t66,t0,t1,t2,t269,t3,t4]
def v1227 := [t66,t0,t2,t64,t3,t4]
def v1228 := [t66,t0,t1,t2,t64,t3,t4]
def t270 := 0x4b00049ff80000
def v1229 := [t270,t0,t1,t2,t3,t4]
def v1230 := [t270,t66,t0,t1,t2,t3,t4]
def t271 := 0x3ffc9249ff8003f
def v1231 := [t0,t1,t2,t3,t4,t271]
def v1232 := [t66,t0,t1,t2,t3,t4,t271]
def t272 := 0x3f
def v1233 := [t272,t0,t1,t2,t3,t4]
def v1234 := [t272,t66,t0,t1,t2,t3,t4]
def t273 := 0x3b4c92000000000
def v1235 := [t0,t1,t2,t3,t273,t4]
def t274 := 0x324cb4040000000
def v1236 := [t0,t274,t1,t2,t3,t4]
def v1237 := [t66,t0,t1,t2,t3,t273,t4]
def v1238 := [t66,t5,t0,t1,t2,t3,t4]
def v1239 := [t66,t0,t1,t2,t56,t3,t4]
def v1240 := [t57,t66,t0,t1,t2,t3,t4]
def v1241 := [t66,t60,t0,t1,t2,t3,t4]
def v1242 := [t66,t61,t0,t1,t2,t3,t4]
def v1243 := [t66,t0,t1,t2,t3,t59,t4]
def v1244 := [t58,t66,t0,t1,t2,t3,t4]
def v1245 := [t66,t102,t0,t1,t2,t3,t4]
def v1246 := [t66,t0,t99,t2,t3,t4]
def v1247 := [t66,t0,t1,t99,t2,t3,t4]
def v1248 := [t66,t101,t0,t2,t3,t4]
def v1249 := [t66,t101,t0,t1,t2,t3,t4]
def v1250 := [t66,t108,t0,t1,t2,t3,t4]
def v1251 := [t66,t0,t1,t2,t3,t4,t109]
def v1252 := [t110,t66,t0,t1,t2,t3,t4]
def v1253 := [t66,t111,t0,t1,t2,t3,t4]
def v1254 := [t66,t0,t204,t1,t2,t3,t4]
def v1255 := [t66,t0,t1,t2,t3,t62,t4]
def v1256 := [t205,t66,t0,t1,t2,t3,t4]
def v1257 := [t66,t118,t0,t1,t2,t3,t4]
def v1258 := [t66,t0,t2,t113,t3,t4]
def v1259 := [t66,t0,t1,t2,t113,t3,t4]
def v1260 := [t115,t66,t0,t2,t3,t4]
def v1261 := [t115,t66,t0,t1,t2,t3,t4]
def v1262 := [t66,t0,t1,t119,t2,t3,t4]
def v1263 := [t66,t0,t1,t2,t3,t4,t120]
def v1264 := [t121,t66,t0,t1,t2,t3,t4]
def v1265 := [t66,t122,t0,t1,t2,t3,t4]
def v1266 := [t66,t0,t206,t2,t3,t4]
def v1267 := [t66,t0,t206,t1,t2,t3,t4]
def v1268 := [t66,t0,t1,t2,t3,t207,t4]
def v1269 := [t66,t208,t0,t2,t3,t4]
def v1270 := [t66,t208,t0,t1,t2,t3,t4]
def v1271 := [t172,t66,t0,t1,t2,t3,t4]
def v1272 := [t66,t0,t1,t2,t210,t3,t4]
def v1273 := [t66,t0,t1,t2,t3,t4,t211]
def v1274 := [t212,t66,t0,t1,t2,t3,t4]
def v1275 := [t66,t213,t0,t1,t2,t3,t4]
def v1276 := [t66,t0,t75,t1,t2,t3,t4]
def v1277 := [t66,t0,t2,t3,t4,t76]
def v1278 := [t66,t0,t1,t2,t3,t4,t76]
def v1279 := [t77,t66,t0,t2,t3,t4]
def v1280 := [t77,t66,t0,t1,t2,t3,t4]
def v1281 := [t66,t78,t0,t1,t2,t3,t4]
def v1282 := [t0,t264,t1,t2,t56,t3,t4]
def v1283 := [t265,t0,t1,t2,t56,t3,t4]
def v1284 := [t0,t1,t2,t266,t56,t3,t4]
def v1285 := [t267,t0,t1,t2,t56,t3,t4]
def v1286 := [t268,t0,t1,t2,t56,t3,t4]
def v1287 := [t0,t1,t2,t56,t3,t220,t4]
def v1288 := [t221,t0,t1,t2,t56,t3,t4]
def v1289 := [t0,t1,t2,t56,t269,t3,t4]
def v1290 := [t66,t0,t2,t56,t64,t3,t4]
def v1291 := [t66,t0,t63,t1,t2,t3,t4]
def v1292 := [t270,t0,t1,t2,t56,t3,t4]
def v1293 := [t0,t1,t2,t56,t3,t4,t271]
def v1294 := [t272,t0,t1,t2,t56,t3,t4]
def v1295 := [t0,t1,t2,t56,t3,t273,t4]
def v1296 := [t0,t274,t1,t2,t3,t62,t4]
def p31_19 : Projection 29 6 := pick [0,2,3,5,19,20] rfl (by decide +kernel) (by decide)
def v1297 := [t66,t5,t1,t56,t3,t4]
def v1298 := [t66,t5,t0,t1,t56,t3,t4]
def v1299 := [t66,t5,t1,t2,t56,t3,t4]
def v1300 := [t57,t66,t0,t1,t56,t3,t4]
def v1301 := [t66,t60,t1,t2,t56,t3,t4]
def v1302 := [t66,t1,t2,t56,t3,t59,t4]
def v1303 := [t58,t66,t1,t2,t56,t3,t4]
def v1304 := [t66,t0,t99,t2,t56,t3,t4]
def v1305 := [t66,t101,t0,t2,t56,t3,t4]
def v1306 := [t66,t0,t1,t56,t3,t62,t4]
def v1307 := [t205,t66,t0,t1,t56,t3,t4]
def v1308 := [t66,t0,t2,t113,t56,t3,t4]
def v1309 := [t115,t66,t0,t2,t56,t3,t4]
def v1310 := [t66,t0,t206,t2,t56,t3,t4]
def v1311 := [t66,t208,t0,t2,t56,t3,t4]
def v1312 := [t66,t0,t209,t1,t2,t3,t4]
def v1313 := [t66,t82,t0,t1,t2,t3,t4]
def v1314 := [t66,t214,t0,t1,t2,t3,t4]
def v1315 := [t65,t66,t0,t2,t3,t4]
def v1316 := [t73,t74,t0,t2,t3,t4]
def v1317 := [t65,t66,t0,t1,t2,t3,t4]
def v1318 := [t65,t66,t0,t2,t56,t3,t4]
def v1319 := [t66,t0,t2,t56,t3,t4,t76]
def v1320 := [t0,t63,t2,t3,t4,t76]
def v1321 := [t0,t2,t56,t3,t273,t76]
def t275 := 0x3b4fff24007fe00
def v1322 := [t0,t2,t56,t3,t275,t4]
def v1323 := [t66,t5,t56,t3,t4,t76]
def v1324 := [t66,t129,t2,t56,t3,t4]
def v1325 := [t66,t131,t0,t56,t3,t4]
def v1326 := [t66,t0,t2,t85,t3,t76]
def v1327 := [t87,t66,t0,t2,t3,t76]
def t276 := 0x3fffff6dffffe3f
def v1328 := [t66,t0,t2,t3,t4,t276]
def t277 := 0x90243000000000
def v1329 := [t66,t277,t0,t2,t3,t4]
def v1330 := [t77,t66,t0,t2,t56,t3,t4]
def v1331 := [t66,t0,t1,t2,t85,t3,t4]
def v1332 := [t66,t0,t1,t2,t3,t4,t86]
def v1333 := [t87,t66,t0,t1,t2,t3,t4]
def v1334 := [t66,t88,t0,t1,t2,t3,t4]
def v1335 := [t0,t75,t1,t2,t56,t3,t4]
def v1336 := [t0,t1,t2,t56,t3,t4,t76]
def v1337 := [t5,t1,t56,t3,t4,t76]
def v1338 := [t5,t0,t1,t56,t3,t4,t76]
def v1339 := [t5,t1,t2,t56,t3,t4,t76]
def v1340 := [t57,t0,t1,t56,t3,t4,t76]
def v1341 := [t60,t1,t2,t56,t3,t4,t76]
def v1342 := [t1,t2,t56,t3,t59,t4,t76]
def v1343 := [t58,t1,t2,t56,t3,t4,t76]
def v1344 := [t60,t0,t1,t2,t3,t4,t76]
def v1345 := [t128,t1,t2,t56,t3,t4]
def v1346 := [t128,t0,t1,t2,t56,t3,t4]
def v1347 := [t128,t1,t2,t56,t3,t4,t76]
def t278 := 0x3fffff6dffffe07
def v1348 := [t0,t1,t2,t56,t3,t4,t278]
def v1349 := [t17,t0,t1,t2,t56,t3,t4]
def v1350 := [t129,t1,t2,t56,t3,t4]
def v1351 := [t129,t0,t1,t2,t56,t3,t4]
def v1352 := [t129,t1,t2,t56,t3,t4,t76]
def v1353 := [t0,t1,t56,t3,t62,t4,t76]
def v1354 := [t205,t0,t1,t56,t3,t4,t76]
def v1355 := [t57,t0,t1,t2,t3,t4,t76]
def v1356 := [t0,t1,t130,t56,t3,t4]
def v1357 := [t0,t1,t130,t2,t56,t3,t4]
def v1358 := [t0,t1,t130,t56,t3,t4,t76]
def t279 := 0x3fffff6dffffe38
def v1359 := [t0,t1,t2,t56,t3,t4,t279]
def v1360 := [t43,t0,t1,t2,t56,t3,t4]
def v1361 := [t131,t0,t1,t56,t3,t4]
def v1362 := [t131,t0,t1,t2,t56,t3,t4]
def v1363 := [t131,t0,t1,t56,t3,t4,t76]
def v1364 := [t0,t209,t1,t2,t3,t4,t76]
def v1365 := [t82,t0,t1,t2,t3,t4,t76]
def v1366 := [t214,t0,t1,t2,t3,t4,t76]
def t280 := 0x3b0ec301fc7f000
def v1367 := [t0,t1,t2,t56,t280,t3,t4]
def t281 := 0x3fffff6dfffffc0
def v1368 := [t0,t1,t2,t56,t3,t4,t281]
def v1369 := [t20,t0,t1,t2,t56,t3,t4]
def t282 := 0x4f13c6c0380e00
def v1370 := [t282,t0,t1,t2,t56,t3,t4]
def v1371 := [t0,t63,t1,t2,t3,t4,t76]
def v1372 := [t0,t63,t2,t56,t3,t4,t76]
def v1373 := [t0,t1,t2,t64,t3,t4,t76]
def v1374 := [t65,t0,t1,t2,t3,t4,t76]
def v1375 := [t0,t75,t2,t56,t3,t76]
def v1376 := [t0,t75,t1,t2,t56,t3,t76]
def v1377 := [t0,t75,t2,t56,t3,t4,t76]
def v1378 := [t77,t0,t1,t2,t56,t3,t76]
def v1379 := [t78,t0,t2,t56,t3,t4,t76]
def v1380 := [t78,t0,t1,t2,t56,t3,t4]
def v1381 := [t0,t1,t2,t85,t3,t76]
def v1382 := [t0,t1,t2,t85,t56,t3,t76]
def v1383 := [t0,t1,t2,t85,t3,t4,t76]
def v1384 := [t0,t1,t2,t3,t4,t86,t76]
def v1385 := [t87,t0,t1,t2,t3,t76]
def v1386 := [t87,t0,t1,t2,t56,t3,t76]
def v1387 := [t87,t0,t1,t2,t3,t4,t76]
def v1388 := [t88,t0,t1,t2,t3,t4,t76]
def t283 := 0x36fdbc6dffffe00
def v1389 := [t0,t1,t2,t283,t3,t4]
def v1390 := [t0,t1,t2,t283,t56,t3,t4]
def v1391 := [t0,t1,t2,t283,t3,t4,t76]
def v1392 := [t0,t1,t2,t3,t4,t276]
def v1393 := [t0,t1,t2,t56,t3,t4,t276]
def v1394 := [t0,t1,t2,t3,t4,t76,t276]
def v1395 := [t272,t0,t1,t2,t3,t4,t76]
def v1396 := [t277,t0,t1,t2,t3,t4]
def v1397 := [t277,t0,t1,t2,t56,t3,t4]
def v1398 := [t133,t0,t1,t2,t3,t59,t4]
def t284 := 0xbd61c0
def v1399 := [t7,t284,t8,t9]
def v1400 := [t44,t7,t284,t8,t9]
def v1401 := [t6,t7,t284,t8,t9]
def v1402 := [t44,t32,t7,t8,t9]
def t285 := 0x900fc7
def v1403 := [t285,t6,t8,t9]
def v1404 := [t44,t285,t6,t8,t9]
def v1405 := [t285,t6,t7,t8,t9]
def v1406 := [t44,t6,t7,t9,t42]
def t286 := 0xf66e00
def v1407 := [t6,t7,t8,t286]
def v1408 := [t44,t6,t7,t8,t286]
def v1409 := [t6,t7,t8,t9,t286]
def v1410 := [t44,t6,t7,t30,t8]
def v1411 := [t44,t6,t7,t33,t9]
def v1412 := [t44,t35,t7,t9]
def v1413 := [t44,t35,t6,t7,t9]
def v1414 := [t44,t35,t7,t8,t9]
def v1415 := [t44,t6,t7,t9,t53]
def v1416 := [t44,t28,t6,t7,t9]
def v1417 := [t44,t6,t7,t9,t54]
def v1418 := [t31,t44,t6,t7]
def v1419 := [t31,t44,t6,t7,t8]
def v1420 := [t31,t44,t6,t7,t9]
def v1421 := [t277,t0,t1,t2,t3,t4,t76]
def v1422 := [t77,t0,t1,t2,t56,t3,t4]
def v1423 := [t0,t1,t2,t85,t3,t4]
def v1424 := [t0,t1,t2,t85,t56,t3,t4]
def v1425 := [t0,t1,t2,t3,t4,t86]
def v1426 := [t0,t1,t2,t56,t3,t4,t86]
def v1427 := [t87,t0,t1,t2,t3,t4]
def v1428 := [t87,t0,t1,t2,t56,t3,t4]
def v1429 := [t88,t0,t1,t2,t3,t4]
def v1430 := [t88,t0,t1,t2,t56,t3,t4]
def v1431 := [t61,t0,t1,t2,t3,t4]
def v1432 := [t0,t1,t2,t3,t59,t4]
def v1433 := [t102,t0,t1,t2,t3,t4]
def v1434 := [t0,t1,t99,t2,t3,t4]
def v1435 := [t5,t0,t1,t99,t2,t3,t4]
def p31_22 : Projection 29 6 := pick [3,5,6,8,25,26] rfl (by decide +kernel) (by decide)
def v1436 := [t57,t0,t1,t99,t2,t3,t4]
def v1437 := [t58,t0,t1,t99,t2,t3,t4]
def v1438 := [t60,t0,t1,t99,t2,t3,t4]
def v1439 := [t58,t0,t1,t2,t3,t207,t4]
def v1440 := [t147,t123,t124,t145,t127,t175]
def v1441 := [t123,t124,t146,t145,t127,t175]
def v1442 := [t148,t123,t124,t145,t127,t175]
def v1443 := [t123,t149,t124,t145,t127,t175]
def v1444 := [t173,t123,t124,t145,t127,t175]
def v1445 := [t123,t124,t145,t125,t127,t175]
def v1446 := [t123,t124,t174,t145,t127,t175]
def v1447 := [t147,t151,t124,t145,t175]
def v1448 := [t151,t124,t257,t145,t175]
def v1449 := [t258,t151,t124,t145,t175]
def v1450 := [t151,t149,t124,t145,t175]
def v1451 := [t173,t151,t124,t145,t175]
def v1452 := [t151,t124,t145,t261,t175]
def v1453 := [t178,t151,t124,t145,t175]
def v1454 := [t151,t124,t174,t145,t175]
def t287 := 0xea8c03
def v1455 := [t124,t145,t287]
def v1456 := [t151,t124,t145,t287]
def v1457 := [t124,t145,t287,t175]
def v1458 := [t151,t124,t145,t287,t175]
def v1459 := [t191,t151,t124,t145,t175]
def v1460 := [t151,t124,t145,t126,t175]
def v1461 := [t151,t153,t124,t145,t175]
def v1462 := [t151,t124,t186,t145,t175]
def v1463 := [t151,t154,t124,t145,t175]
def v1464 := [t151,t124,t145,t175,t161]
def v1465 := [t192,t151,t124,t145,t175]
def v1466 := [t151,t124,t145,t259,t175]
def v1467 := [t151,t124,t189,t145,t175]
def v1468 := [t151,t124,t145,t175,t235]
def v1469 := [t190,t151,t124,t145,t175]
def t288 := 0x5ca0c3
def v1470 := [t151,t124,t288,t145,t175]
def v1471 := [t151,t124,t145,t127,t175]
def v1472 := [t151,t123,t124,t145,t127,t175]
def v1473 := [t176,t123,t124,t145,t127,t175]
def v1474 := [t123,t124,t145,t152,t127,t175]
def v1475 := [t191,t123,t124,t145,t127,t175]
def v1476 := [t123,t124,t145,t126,t127,t175]
def v1477 := [t123,t153,t124,t145,t127,t175]
def v1478 := [t123,t124,t186,t145,t127,t175]
def v1479 := [t123,t154,t124,t145,t127,t175]
def v1480 := [t123,t124,t145,t175,t187]
def v1481 := [t123,t124,t145,t127,t175,t187]
def v1482 := [t192,t123,t124,t145,t127,t175]
def v1483 := [t123,t124,t145,t155,t175]
def v1484 := [t178,t123,t124,t145,t175]
def v1485 := [t180,t123,t124,t145,t175]
def v1486 := [t123,t124,t177,t125,t175]
def v1487 := [t123,t124,t177,t174,t175]
def v1488 := [t124,t177,t145,t152,t175]
def v1489 := [t123,t124,t183,t145,t175]
def v1490 := [t185,t123,t124,t145,t175]
def v1491 := [t123,t124,t177,t126,t175]
def v1492 := [t123,t124,t177,t186,t175]
def v1493 := [t123,t124,t177,t175,t188]
def t289 := 0xa20f03
def v1494 := [t123,t124,t177,t289,t145]
def v1495 := [t123,t124,t289,t145,t175]
def v1496 := [t190,t123,t124,t177,t175]
def v1497 := [t123,t124,t145,t155,t127,t175]
def v1498 := [t123,t124,t145,t259,t127,t175]
def v1499 := [t123,t124,t189,t145,t127,t175]
def v1500 := [t123,t124,t145,t127,t175,t188]
def v1501 := [t190,t123,t124,t145,t127,t175]
def v1502 := [t123,t124,t177,t145,t127,t175]
def v1503 := [t123,t124,t145,t127,t235]
def v1504 := [t123,t124,t145,t127,t175,t235]
def v1505 := [t123,t124,t288,t145,t127]
def v1506 := [t123,t124,t288,t145,t127,t175]
def v1507 := [t173,t150,t124,t145,t127,t188]
def v1508 := [t173,t123,t124,t145,t127,t188]
def v1509 := [t147,t123,t124,t145,t127,t188]
def v1510 := [t123,t124,t193,t145,t127,t188]
def v1511 := [t123,t149,t124,t145,t127,t188]
def v1512 := [t150,t123,t124,t125,t127,t188]
def v1513 := [t123,t124,t145,t125,t127,t188]
def v1514 := [t178,t123,t124,t145,t127,t188]
def v1515 := [t150,t123,t124,t145,t175,t188]
def v1516 := [t176,t123,t124,t145,t127,t188]
def v1517 := [t123,t124,t145,t195,t188]
def v1518 := [t123,t124,t200,t145,t175]
def v1519 := [t147,t124,t200,t145,t175]
def v1520 := [t149,t124,t200,t145,t175]
def v1521 := [t151,t124,t200,t145,t175]
def v1522 := [t181,t124,t200,t145,t175]
def v1523 := [t124,t200,t145,t125,t175]
def v1524 := [t150,t124,t200,t145,t175]
def v1525 := [t123,t124,t200,t145,t152]
def v1526 := [t124,t200,t145,t152,t175]
def v1527 := [t123,t124,t200,t126,t175]
def v1528 := [t123,t124,t200,t186,t175]
def v1529 := [t123,t124,t200,t145,t161]
def v1530 := [t123,t124,t200,t145,t259]
def t290 := 0xa20c03
def v1531 := [t123,t124,t200,t290,t145]
def v1532 := [t123,t124,t290,t145,t175]
def v1533 := [t123,t124,t200,t189,t145]
def v1534 := [t190,t123,t124,t200,t145]
def v1535 := [t150,t123,t124,t145,t195,t188]
def v1536 := [t123,t124,t145,t195,t127,t188]
def v1537 := [t150,t123,t124,t145,t127,t235]
def v1538 := [t123,t124,t145,t127,t188,t235]
def t291 := 0xea8f30
def v1539 := [t123,t124,t145,t291,t127]
def v1540 := [t150,t123,t124,t145,t291,t127]
def v1541 := [t123,t124,t145,t291,t127,t188]
def v1542 := [t150,t124,t146,t145,t127,t188]
def v1543 := [t150,t148,t124,t145,t127,t188]
def v1544 := [t124,t197,t127,t175]
def v1545 := [t150,t124,t197,t127,t175]
def v1546 := [t124,t174,t197,t127,t175]
def v1547 := [t178,t124,t174,t175]
def v1548 := [t178,t150,t124,t174,t175]
def v1549 := [t178,t124,t174,t127,t175]
def v1550 := [t176,t150,t124,t174,t175]
def v1551 := [t124,t174,t195,t127,t175]
def v1552 := [t150,t124,t174,t175,t187]
def v1553 := [t150,t124,t174,t155,t175]
def v1554 := [t150,t124,t174,t127,t161]
def v1555 := [t150,t124,t174,t259,t127]
def v1556 := [t150,t124,t174,t175,t188]
def v1557 := [t150,t124,t200,t174,t175]
def v1558 := [t150,t124,t174,t127,t235]
def v1559 := [t150,t124,t179,t174,t127]
def v1560 := [t150,t123,t124,t174,t127,t188]
def v1561 := [t150,t124,t174,t145,t127,t188]
def v1562 := [t150,t151,t124,t145,t127,t188]
def v1563 := [t124,t193,t145,t152,t188]
def v1564 := [t150,t124,t125,t152,t188]
def v1565 := [t124,t145,t125,t152,t188]
def v1566 := [t150,t124,t145,t201,t188]
def v1567 := [t124,t145,t152,t201,t188]
def v1568 := [t124,t145,t152,t188,t235]
def v1569 := [t176,t124,t145,t152,t188]
def v1570 := [t191,t150,t124,t152,t188]
def v1571 := [t150,t153,t124,t152,t188]
def v1572 := [t150,t124,t145,t202,t188]
def v1573 := [t150,t124,t163,t145,t188]
def v1574 := [t150,t124,t145,t152,t246]
def v1575 := [t150,t124,t145,t247,t152]
def v1576 := [t150,t124,t199,t188]
def v1577 := [t150,t124,t199,t145,t188]
def v1578 := [t150,t124,t199,t152,t188]
def v1579 := [t203,t150,t124,t145,t188]
def v1580 := [t150,t181,t124,t152,t188]
def v1581 := [t150,t124,t177,t152,t188]
def t292 := 0x1423f0
def v1582 := [t150,t292,t124,t145,t152]
def v1583 := [t150,t292,t124,t145,t188]
def v1584 := [t150,t123,t124,t145,t152,t188]
def v1585 := [t150,t124,t145,t152,t127,t188]
def v1586 := [t150,t124,t145,t245,t127]
def v1587 := [t124,t193,t145,t245,t127]
def v1588 := [t194,t124,t145,t245,t127]
def v1589 := [t150,t124,t125,t245,t127]
def v1590 := [t124,t145,t125,t245,t127]
def t293 := 0xfeacf3
def v1591 := [t150,t124,t145,t293,t127]
def v1592 := [t124,t145,t245,t293,t127]
def v1593 := [t124,t145,t245,t127,t175]
def v1594 := [t176,t124,t145,t245,t127]
def v1595 := [t191,t150,t124,t245,t127]
def v1596 := [t150,t153,t124,t245,t127]
def v1597 := [t150,t124,t145,t245,t187]
def v1598 := [t150,t124,t145,t155,t245]
def v1599 := [t150,t124,t174,t245,t127]
def v1600 := [t150,t181,t124,t245,t127]
def v1601 := [t150,t124,t189,t245,t127]
def v1602 := [t150,t124,t177,t245,t127]
def v1603 := [t150,t123,t124,t145,t245,t127]
def v1604 := [t150,t124,t145,t245,t127,t188]
def v1605 := [t191,t150,t123,t124,t127,t188]
def v1606 := [t150,t123,t153,t124,t127,t188]
def t294 := 0x483
def t295 := 0xebc
def v1607 := [t294,t104,t106,t295]
def v1608 := [t150,t123,t124,t145,t187,t188]
def v1609 := [t150,t123,t124,t145,t155,t188]
def v1610 := [t150,t123,t124,t145,t127,t246]
def v1611 := [t150,t123,t124,t145,t247,t127]
def v1612 := [t150,t123,t124,t189,t188]
def t296 := 0xa30
def v1613 := [t104,t296,t295]
def v1614 := [t150,t123,t124,t189,t145,t188]
def v1615 := [t150,t123,t124,t189,t127,t188]
def v1616 := [t190,t150,t123,t124,t145,t188]
def v1617 := [t150,t123,t124,t177,t127,t188]
def v1618 := [t61,t0,t1,t99,t2,t3,t4]
def v1619 := [t0,t1,t99,t2,t3,t59,t4]
def v1620 := [t102,t0,t1,t99,t2,t3,t4]
def v1621 := [t98,t99,t2,t3,t4]
def t297 := 0x4b0
def t298 := 0xeb3
def v1622 := [t297,t105,t298]
def v1623 := [t147,t257,t145,t175]
def v1624 := [t147,t151,t257,t145,t175]
def v1625 := [t147,t124,t257,t145,t175]
def v1626 := [t258,t151,t257,t145,t175]
def v1627 := [t149,t124,t257,t145,t175]
def v1628 := [t124,t257,t145,t261,t175]
def v1629 := [t178,t124,t257,t145,t175]
def v1630 := [t124,t257,t145,t287]
def v1631 := [t151,t124,t257,t145,t287]
def v1632 := [t124,t257,t145,t287,t175]
def v1633 := [t151,t257,t145,t126,t175]
def v1634 := [t151,t153,t257,t145,t175]
def v1635 := [t151,t154,t257,t145,t175]
def v1636 := [t151,t257,t145,t259,t175]
def v1637 := [t156,t151,t124,t145,t175]
def v1638 := [t151,t124,t145,t175,t246]
def t299 := 0x5ca0cc
def v1639 := [t151,t124,t299,t145,t175]
def v1640 := [t151,t124,t159,t145,t175]
def v1641 := [t151,t124,t260,t145,t175]
def t300 := 0x5ca0f0
def v1642 := [t123,t124,t300]
def v1643 := [t147,t123,t124,t300]
def v1644 := [t123,t124,t300,t146]
def v1645 := [t148,t123,t124,t300]
def v1646 := [t123,t149,t124,t300]
def v1647 := [t178,t123,t124,t300]
def t301 := 0x5ca3f3
def v1648 := [t123,t124,t300,t301]
def v1649 := [t180,t123,t124,t300]
def t302 := 0x488030
def v1650 := [t123,t302,t124,t300]
def v1651 := [t123,t182,t124,t300]
def t303 := 0x5cacfc
def v1652 := [t123,t124,t300,t303]
def v1653 := [t184,t123,t124,t300]
def t304 := 0x142030
def v1654 := [t304,t123,t124,t300]
def v1655 := [t147,t124,t145,t287]
def v1656 := [t147,t151,t124,t145,t287]
def v1657 := [t258,t124,t145,t287]
def v1658 := [t258,t151,t124,t145,t287]
def v1659 := [t149,t124,t145,t287]
def v1660 := [t151,t149,t124,t145,t287]
def v1661 := [t173,t124,t145,t287]
def v1662 := [t173,t151,t124,t145,t287]
def v1663 := [t124,t145,t261,t287]
def v1664 := [t151,t124,t145,t261,t287]
def v1665 := [t178,t124,t145,t287]
def v1666 := [t178,t151,t124,t145,t287]
def v1667 := [t124,t174,t145,t287]
def v1668 := [t151,t124,t174,t145,t287]
def v1669 := [t191,t151,t124,t145,t287]
def v1670 := [t151,t124,t145,t287,t126]
def v1671 := [t151,t153,t124,t145,t287]
def v1672 := [t151,t124,t186,t145,t287]
def v1673 := [t151,t252,t124,t145,t287]
def t305 := 0xea8ccf
def v1674 := [t151,t124,t145,t287,t305]
def t306 := 0xcc
def v1675 := [t306,t151,t124,t145,t287]
def v1676 := [t151,t124,t260,t145,t287]
def v1677 := [t151,t124,t199,t145,t287]
def t307 := 0xea8f33
def v1678 := [t151,t124,t145,t287,t307]
def v1679 := [t203,t151,t124,t145,t287]
def t308 := 0x488003
def v1680 := [t151,t308,t124,t145,t287]
def v1681 := [t123,t124,t300,t188]
def v1682 := [t147,t123,t124,t300,t188]
def v1683 := [t123,t124,t300,t146,t188]
def v1684 := [t148,t123,t124,t300,t188]
def v1685 := [t123,t149,t124,t300,t188]
def v1686 := [t178,t123,t124,t300,t188]
def v1687 := [t123,t124,t300,t301,t188]
def v1688 := [t180,t123,t124,t300,t188]
def v1689 := [t123,t302,t124,t300,t188]
def v1690 := [t151,t123,t124,t300]
def v1691 := [t151,t123,t124,t300,t188]
def v1692 := [t123,t124,t300,t235]
def v1693 := [t123,t124,t300,t188,t235]
def v1694 := [t176,t123,t124,t300]
def v1695 := [t176,t123,t124,t300,t188]
def v1696 := [t123,t124,t300,t245]
def v1697 := [t123,t124,t300,t245,t188]
def v1698 := [t123,t182,t124,t300,t188]
def v1699 := [t123,t124,t300,t303,t188]
def v1700 := [t184,t123,t124,t300,t188]
def v1701 := [t304,t123,t124,t300,t188]
def v1702 := [t123,t154,t124,t300]
def v1703 := [t123,t154,t124,t300,t188]
def v1704 := [t123,t124,t300,t246]
def v1705 := [t123,t124,t300,t188,t246]
def v1706 := [t192,t123,t124,t300]
def v1707 := [t192,t123,t124,t300,t188]
def v1708 := [t123,t124,t300,t247]
def v1709 := [t123,t124,t300,t247,t188]
def v1710 := [t123,t124,t300,t189]
def v1711 := [t123,t124,t300,t189,t188]
def v1712 := [t147,t124,t145,t287,t175]
def v1713 := [t258,t124,t145,t287,t175]
def v1714 := [t149,t124,t145,t287,t175]
def v1715 := [t173,t124,t145,t287,t175]
def v1716 := [t124,t145,t261,t287,t175]
def v1717 := [t178,t124,t145,t287,t175]
def v1718 := [t124,t174,t145,t287,t175]
def v1719 := [t151,t252,t124,t145,t175]
def v1720 := [t151,t124,t145,t305,t175]
def v1721 := [t306,t151,t124,t145,t175]
def v1722 := [t151,t154,t124,t145,t287]
def v1723 := [t151,t124,t145,t287,t161]
def v1724 := [t192,t151,t124,t145,t287]
def v1725 := [t151,t124,t145,t259,t287]
def v1726 := [t151,t124,t199,t145,t175]
def v1727 := [t151,t124,t145,t307,t175]
def v1728 := [t203,t151,t124,t145,t175]
def v1729 := [t151,t308,t124,t145,t175]
def v1730 := [t151,t124,t189,t145,t287]
def v1731 := [t151,t124,t145,t287,t235]
def v1732 := [t190,t151,t124,t145,t287]
def v1733 := [t151,t124,t288,t145,t287]
def v1734 := [t147,t123,t124,t189,t188]
def v1735 := [t151,t149,t145,t126,t175]
def v1736 := [t151,t124,t261,t126,t175]
def v1737 := [t151,t124,t174,t126,t175]
def v1738 := [t228,t151,t124,t145,t175]
def v1739 := [t185,t151,t124,t145,t175]
def v1740 := [t151,t124,t145,t237,t175]
def v1741 := [t124,t145,t287,t126]
def v1742 := [t124,t145,t287,t126,t175]
def v1743 := [t191,t151,t126,t175]
def v1744 := [t191,t151,t124,t126,t175]
def v1745 := [t191,t151,t145,t126,t175]
def v1746 := [t151,t153,t124,t126,t175]
def v1747 := [t151,t186,t145,t126,t175]
def v1748 := [t151,t154,t145,t126,t175]
def v1749 := [t151,t145,t259,t126,t175]
def v1750 := [t151,t124,t189,t126,t175]
def v1751 := [t151,t124,t288,t126,t175]
def v1752 := [t151,t124,t145,t231,t175]
def v1753 := [t151,t124,t145,t175,t157]
def v1754 := [t250,t151,t124,t145,t175]
def v1755 := [t194,t151,t124,t145,t175]
def v1756 := [t150,t123,t154,t145,t187]
def v1757 := [t151,t123,t154,t145,t187]
def v1758 := [t124,t145,t287,t161]
def v1759 := [t124,t145,t287,t175,t161]
def t309 := 0xea8c0f
def v1760 := [t124,t145,t309,t175]
def v1761 := [t151,t124,t145,t309,t175]
def v1762 := [t124,t145,t309,t175,t161]
def v1763 := [t151,t154,t145,t161]
def v1764 := [t151,t154,t124,t145,t161]
def v1765 := [t151,t154,t145,t175,t161]
def v1766 := [t192,t151,t124,t145,t161]
def v1767 := [t151,t145,t259,t175,t161]
def v1768 := [t151,t124,t145,t161,t235]
def v1769 := [t151,t124,t288,t145,t161]
def v1770 := [t151,t124,t158,t145,t175]
def v1771 := [t176,t123,t154,t145,t187]
def v1772 := [t151,t124,t179,t145,t175]
def v1773 := [t151,t124,t288,t261,t175]
def v1774 := [t151,t124,t288,t174,t175]
def v1775 := [t124,t288,t145,t287]
def v1776 := [t124,t288,t145,t287,t175]
def v1777 := [t151,t182,t124,t145,t175]
def v1778 := [t151,t124,t193,t145,t175]
def v1779 := [t184,t151,t124,t145,t175]
def v1780 := [t151,t124,t288,t186,t175]
def v1781 := [t151,t124,t288,t145,t259]
def v1782 := [t151,t124,t288,t175,t235]
def v1783 := [t151,t124,t288,t189,t145]
def v1784 := [t190,t151,t124,t288]
def v1785 := [t190,t151,t124,t288,t145]
def v1786 := [t190,t151,t124,t288,t175]
def v1787 := [t98,t0,t99,t2,t3,t4]
def v1788 := [t176,t151,t124,t145,t175]
def v1789 := [t176,t151,t123,t124,t145,t175]
def v1790 := [t147,t151,t123,t124,t145,t175]
def v1791 := [t123,t124,t251,t145,t187]
def v1792 := [t147,t251,t145,t187]
def v1793 := [t147,t123,t251,t145,t187]
def v1794 := [t147,t124,t251,t145,t187]
def v1795 := [t148,t123,t251,t145,t187]
def v1796 := [t149,t124,t251,t145,t187]
def v1797 := [t123,t252,t124,t145,t187]
def v1798 := [t252,t124,t251,t145,t187]
def v1799 := [t124,t251,t145,t125,t187]
def v1800 := [t150,t124,t251,t145,t187]
def v1801 := [t151,t124,t251,t145,t187]
def v1802 := [t124,t251,t145,t262,t187]
def v1803 := [t123,t154,t145,t187]
def v1804 := [t123,t154,t124,t145,t187]
def v1805 := [t123,t154,t251,t145,t187]
def v1806 := [t192,t123,t124,t145,t187]
def v1807 := [t123,t251,t145,t126,t187]
def v1808 := [t123,t153,t251,t145,t187]
def v1809 := [t123,t124,t251,t145,t155]
def v1810 := [t123,t251,t145,t155,t187]
def v1811 := [t123,t124,t145,t187,t235]
def v1812 := [t123,t124,t288,t145,t187]
def t310 := 0xa2000c
def v1813 := [t123,t124,t310,t145,t187]
def v1814 := [t151,t123,t124,t257,t145,t175]
def v1815 := [t258,t151,t123,t124,t145,t175]
def v1816 := [t151,t123,t149,t124,t145,t175]
def v1817 := [t173,t151,t123,t124,t145,t175]
def v1818 := [t123,t124,t145,t261,t175]
def v1819 := [t151,t123,t124,t145,t261,t175]
def v1820 := [t178,t151,t123,t124,t145,t175]
def v1821 := [t151,t123,t124,t174,t145,t175]
def v1822 := [t123,t124,t145,t287]
def v1823 := [t123,t124,t300,t145]
def v1824 := [t147,t123,t124,t300,t145]
def v1825 := [t123,t124,t300,t146,t145]
def v1826 := [t148,t123,t124,t300,t145]
def v1827 := [t123,t149,t124,t300,t145]
def v1828 := [t178,t123,t124,t300,t145]
def v1829 := [t123,t124,t300,t301,t145]
def v1830 := [t180,t123,t124,t300,t145]
def v1831 := [t123,t302,t124,t300,t145]
def v1832 := [t173,t123,t124,t300]
def v1833 := [t173,t123,t124,t300,t145]
def v1834 := [t123,t124,t300,t125]
def v1835 := [t123,t124,t300,t145,t125]
def v1836 := [t150,t123,t124,t300]
def v1837 := [t150,t123,t124,t300,t145]
def v1838 := [t123,t124,t300,t174]
def v1839 := [t123,t124,t300,t174,t145]
def v1840 := [t123,t182,t124,t300,t145]
def v1841 := [t123,t124,t300,t303,t145]
def v1842 := [t184,t123,t124,t300,t145]
def v1843 := [t304,t123,t124,t300,t145]
def v1844 := [t191,t123,t124,t300]
def v1845 := [t191,t123,t124,t300,t145]
def v1846 := [t123,t124,t300,t126]
def v1847 := [t123,t124,t300,t145,t126]
def v1848 := [t123,t153,t124,t300]
def v1849 := [t123,t153,t124,t300,t145]
def v1850 := [t123,t124,t300,t186]
def v1851 := [t123,t124,t300,t186,t145]
def v1852 := [t190,t123,t124,t300]
def v1853 := [t190,t123,t124,t300,t145]
def v1854 := [t123,t124,t300,t145,t188]
def v1855 := [t123,t124,t177,t300]
def v1856 := [t123,t124,t177,t300,t145]
def v1857 := [t123,t124,t300,t189,t145]
def v1858 := [t151,t123,t124,t145,t287]
def v1859 := [t123,t124,t145,t287,t175]
def v1860 := [t123,t124,t301,t145,t188]
def v1861 := [t123,t302,t124,t145,t188]
def v1862 := [t173,t123,t124,t300,t188]
def v1863 := [t123,t124,t300,t125,t188]
def v1864 := [t150,t123,t124,t300,t188]
def v1865 := [t123,t124,t300,t174,t188]
def v1866 := [t151,t123,t124,t300,t145]
def v1867 := [t123,t124,t300,t145,t235]
def v1868 := [t176,t123,t124,t300,t145]
def v1869 := [t123,t124,t300,t145,t245]
def v1870 := [t123,t124,t303,t145,t188]
def v1871 := [t304,t123,t124,t145,t188]
def v1872 := [t191,t123,t124,t300,t188]
def v1873 := [t123,t124,t300,t126,t188]
def v1874 := [t123,t153,t124,t300,t188]
def v1875 := [t123,t124,t300,t186,t188]
def v1876 := [t123,t154,t124,t300,t145]
def v1877 := [t123,t124,t300,t145,t246]
def v1878 := [t192,t123,t124,t300,t145]
def v1879 := [t123,t124,t300,t145,t247]
def v1880 := [t190,t123,t124,t300,t188]
def v1881 := [t190,t123,t124,t145,t188]
def v1882 := [t123,t124,t177,t300,t188]
def v1883 := [t123,t124,t189,t145,t188]
def v1884 := [t151,t123,t124,t145,t287,t175]
def v1885 := [t151,t124,t146,t145,t175]
def v1886 := [t147,t151,t146,t145,t175]
def v1887 := [t258,t151,t146,t145,t175]
def t311 := 0x488c0f
def v1888 := [t151,t311,t124,t145,t175]
def v1889 := [t311,t124,t146,t145,t175]
def v1890 := [t124,t146,t145,t261,t175]
def v1891 := [t178,t124,t146,t145,t175]
def v1892 := [t124,t146,t145,t287]
def v1893 := [t151,t124,t146,t145,t287]
def v1894 := [t124,t146,t145,t287,t175]
def v1895 := [t148,t151,t124,t145,t175]
def v1896 := [t148,t151,t146,t145,t175]
def v1897 := [t151,t146,t145,t126,t175]
def v1898 := [t151,t153,t146,t145,t175]
def v1899 := [t151,t154,t146,t145,t175]
def v1900 := [t151,t146,t145,t259,t175]
def v1901 := [t151,t124,t251,t145,t175]
def v1902 := [t151,t124,t163,t145,t175]
def v1903 := [t151,t123,t124,t146,t145,t175]
def v1904 := [t148,t151,t123,t124,t145,t175]
def v1905 := [t151,t124,t145,t125,t175]
def v1906 := [t151,t123,t124,t145,t125,t175]
def v1907 := [t150,t151,t124,t145,t175]
def v1908 := [t150,t151,t123,t124,t145,t175]
def v1909 := [t151,t123,t124,t145,t152]
def v1910 := [t151,t124,t145,t152,t175]
def v1911 := [t124,t257,t145,t152,t175]
def v1912 := [t258,t124,t145,t152,t175]
def v1913 := [t124,t145,t261,t152,t175]
def v1914 := [t178,t124,t145,t152,t175]
def v1915 := [t124,t145,t152,t287]
def v1916 := [t151,t124,t145,t152,t287]
def v1917 := [t124,t145,t152,t287,t175]
def v1918 := [t151,t124,t145,t202,t175]
def v1919 := [t151,t124,t145,t152,t161]
def v1920 := [t151,t124,t145,t259,t152]
def v1921 := [t151,t124,t145,t291,t175]
def v1922 := [t151,t181,t124,t145,t175]
def v1923 := [t151,t124,t145,t152,t235]
def v1924 := [t151,t124,t288,t145,t152]
def v1925 := [t151,t123,t124,t145,t152,t175]
def v1926 := [t191,t151,t123,t124,t145,t175]
def v1927 := [t151,t123,t124,t145,t126,t175]
def v1928 := [t123,t257,t145,t126,t175]
def v1929 := [t123,t124,t261,t126,t175]
def v1930 := [t123,t124,t145,t175,t246]
def v1931 := [t123,t124,t145,t287,t126]
def v1932 := [t151,t124,t125,t126,t175]
def v1933 := [t191,t151,t123,t126,t175]
def v1934 := [t250,t151,t123,t124,t145]
def v1935 := [t151,t123,t153,t124,t145,t175]
def v1936 := [t151,t123,t124,t186,t145,t175]
def v1937 := [t151,t123,t154,t124,t145,t175]
def v1938 := [t151,t123,t124,t145,t175,t161]
def v1939 := [t192,t151,t123,t124,t145,t175]
def v1940 := [t151,t123,t124,t145,t259,t175]
def v1941 := [t151,t123,t124,t189,t145,t175]
def v1942 := [t151,t123,t124,t145,t175,t235]
def v1943 := [t190,t151,t123,t124,t145,t175]
def v1944 := [t151,t123,t124,t288,t145,t175]
def v1945 := [t98,t1,t99,t2,t3,t4]
def v1946 := [t147,t151,t124,t145,t127,t175]
def v1947 := [t151,t124,t257,t145,t127,t175]
def v1948 := [t258,t151,t124,t145,t127,t175]
def v1949 := [t151,t149,t124,t145,t127,t175]
def v1950 := [t173,t151,t124,t145,t127,t175]
def v1951 := [t151,t124,t145,t261,t127,t175]
def v1952 := [t178,t151,t124,t145,t127,t175]
def v1953 := [t151,t124,t174,t145,t127,t175]
def v1954 := [t151,t124,t145,t152,t127,t175]
def v1955 := [t124,t145,t287,t127]
def v1956 := [t123,t124,t300,t127]
def v1957 := [t147,t123,t124,t300,t127]
def v1958 := [t123,t124,t300,t146,t127]
def v1959 := [t148,t123,t124,t300,t127]
def v1960 := [t123,t149,t124,t300,t127]
def v1961 := [t178,t123,t124,t300,t127]
def v1962 := [t123,t124,t300,t301,t127]
def v1963 := [t180,t123,t124,t300,t127]
def v1964 := [t123,t302,t124,t300,t127]
def v1965 := [t151,t123,t124,t300,t127]
def v1966 := [t123,t124,t300,t175]
def v1967 := [t123,t124,t300,t127,t175]
def v1968 := [t176,t123,t124,t300,t127]
def v1969 := [t123,t124,t300,t152]
def v1970 := [t123,t124,t300,t152,t127]
def v1971 := [t123,t182,t124,t300,t127]
def v1972 := [t123,t124,t300,t303,t127]
def v1973 := [t184,t123,t124,t300,t127]
def v1974 := [t304,t123,t124,t300,t127]
def v1975 := [t123,t154,t124,t300,t127]
def v1976 := [t123,t124,t300,t187]
def v1977 := [t123,t124,t300,t127,t187]
def v1978 := [t192,t123,t124,t300,t127]
def v1979 := [t123,t124,t300,t155]
def v1980 := [t123,t124,t300,t155,t127]
def v1981 := [t123,t124,t177,t300,t127]
def v1982 := [t123,t124,t300,t127,t188]
def v1983 := [t190,t123,t124,t300,t127]
def v1984 := [t123,t124,t300,t189,t127]
def v1985 := [t151,t124,t145,t287,t127]
def v1986 := [t147,t124,t145,t287,t127]
def v1987 := [t124,t257,t145,t287,t127]
def v1988 := [t258,t124,t145,t287,t127]
def v1989 := [t149,t124,t145,t287,t127]
def v1990 := [t173,t124,t145,t287,t127]
def v1991 := [t124,t145,t261,t287,t127]
def v1992 := [t178,t124,t145,t287,t127]
def v1993 := [t124,t174,t145,t287,t127]
def v1994 := [t124,t145,t287,t127,t175]
def v1995 := [t124,t145,t152,t287,t127]
def v1996 := [t151,t124,t145,t305,t127]
def v1997 := [t151,t124,t260,t145,t127]
def v1998 := [t151,t124,t145,t287,t187]
def v1999 := [t151,t124,t145,t155,t287]
def v2000 := [t151,t124,t145,t307,t127]
def v2001 := [t151,t308,t124,t145,t127]
def v2002 := [t151,t124,t145,t287,t188]
def v2003 := [t151,t124,t177,t145,t287]
def v2004 := [t176,t151,t124,t145,t287]
def v2005 := [t123,t124,t300,t175,t188]
def v2006 := [t123,t124,t300,t152,t188]
def v2007 := [t123,t124,t300,t127,t235]
def v2008 := [t123,t124,t300,t245,t127]
def v2009 := [t123,t124,t300,t187,t188]
def v2010 := [t123,t124,t300,t155,t188]
def v2011 := [t123,t124,t300,t127,t246]
def v2012 := [t123,t124,t300,t247,t127]
def v2013 := [t151,t124,t145,t287,t127,t175]
def v2014 := [t191,t151,t124,t145,t127,t175]
def v2015 := [t151,t124,t145,t126,t127,t175]
def v2016 := [t228,t124,t145,t127,t175]
def v2017 := [t124,t145,t287,t126,t127]
def v2018 := [t191,t151,t126,t127,t175]
def v2019 := [t151,t145,t155,t126,t175]
def v2020 := [t151,t145,t259,t126,t127]
def v2021 := [t151,t124,t177,t126,t175]
def v2022 := [t151,t124,t288,t126,t127]
def v2023 := [t151,t124,t145,t127,t157]
def v2024 := [t151,t153,t124,t145,t127,t175]
def v2025 := [t151,t124,t186,t145,t127,t175]
def v2026 := [t151,t154,t124,t145,t127,t175]
def v2027 := [t151,t124,t145,t175,t187]
def v2028 := [t151,t124,t145,t127,t175,t187]
def v2029 := [t192,t151,t124,t145,t127,t175]
def v2030 := [t151,t124,t145,t155,t175]
def v2031 := [t151,t124,t177,t145,t175]
def v2032 := [t151,t124,t177,t261,t175]
def v2033 := [t151,t124,t177,t174,t175]
def v2034 := [t124,t177,t145,t287]
def v2035 := [t124,t177,t145,t287,t175]
def v2036 := [t151,t124,t183,t145,t175]
def v2037 := [t151,t124,t177,t186,t175]
def v2038 := [t151,t124,t177,t145,t161]
def v2039 := [t151,t124,t177,t145,t259]
def v2040 := [t151,t124,t177,t175,t188]
def v2041 := [t151,t124,t145,t175,t188]
def v2042 := [t151,t124,t177,t289,t145]
def v2043 := [t151,t124,t289,t145,t175]
def v2044 := [t151,t124,t177,t175,t235]
def v2045 := [t190,t151,t124,t177,t175]
def v2046 := [t151,t124,t145,t155,t127,t175]
def v2047 := [t151,t124,t145,t127,t175,t161]
def v2048 := [t151,t124,t145,t259,t127]
def v2049 := [t151,t124,t288,t145,t127]
def v2050 := [t151,t124,t179,t145,t127]
def v2051 := [t151,t124,t288,t261,t127]
def v2052 := [t151,t124,t288,t174,t127]
def v2053 := [t124,t288,t145,t152,t127]
def v2054 := [t151,t124,t193,t145,t127]
def v2055 := [t151,t124,t288,t186,t127]
def v2056 := [t151,t124,t288,t145,t187]
def v2057 := [t151,t124,t288,t145,t155]
def v2058 := [t151,t124,t288,t127,t235]
def v2059 := [t151,t124,t145,t127,t235]
def v2060 := [t151,t124,t288,t127,t188]
def v2061 := [t190,t151,t124,t288,t127]
def v2062 := [t151,t124,t145,t259,t127,t175]
def v2063 := [t151,t124,t189,t145,t127,t175]
def v2064 := [t151,t124,t145,t127,t175,t188]
def v2065 := [t190,t151,t124,t145,t127,t175]
def v2066 := [t151,t124,t177,t145,t127,t175]
def v2067 := [t151,t124,t145,t127,t175,t235]
def v2068 := [t151,t124,t288,t145,t127,t175]
def v2069 := [t176,t151,t124,t145,t127,t175]
def v2070 := [t98,t0,t1,t99,t2,t3,t4]
def v2071 := [t100,t0,t99,t2,t3,t4]
def v2072 := [t114,t0,t2,t113,t3,t4]
def v2073 := [t100,t0,t1,t99,t2,t3,t4]
def v2074 := [t114,t0,t1,t2,t113,t3,t4]
def p31_21 : Projection 29 6 := pick [0,2,6,8,22,23] rfl (by decide +kernel) (by decide)
def v2075 := [t101,t1,t99,t2,t3,t4]
def v2076 := [t172,t0,t1,t2,t207,t4]
def v2077 := [t101,t0,t1,t99,t2,t3,t4]
def v2078 := [t172,t0,t1,t2,t3,t207,t4]
def v2079 := [t101,t0,t1,t2,t3,t4]
def v2080 := [t172,t0,t1,t2,t3,t4]
def v2081 := [t108,t0,t1,t99,t2,t3,t4]
def v2082 := [t98,t0,t1,t2,t3,t4,t109]
def v2083 := [t1,t99,t2,t3,t4,t109]
def v2084 := [t0,t1,t2,t207,t4,t211]
def v2085 := [t0,t1,t99,t2,t3,t4,t109]
def v2086 := [t110,t1,t99,t2,t3,t4]
def v2087 := [t114,t0,t1,t3,t4,t120]
def map23_2 : Projection 12 12 := pick [2,3,0,1,4,5,7,6,10,11,8,9] rfl (by decide +kernel) (by decide)
def v2088 := [t110,t0,t1,t99,t2,t3,t4]
def v2089 := [t114,t0,t1,t2,t3,t4,t120]
def p31_13 : Projection 29 6 := pick [0,1,6,7,12,13] rfl (by decide +kernel) (by decide)
def v2090 := [t111,t0,t1,t99,t2,t3,t4]
def v2091 := [t172,t0,t1,t2,t3,t4,t211]
def v2092 := [t0,t204,t1,t99,t2,t3,t4]
def v2093 := [t5,t0,t1,t2,t3,t207,t4]
def v2094 := [t205,t0,t1,t99,t2,t3,t4]
def v2095 := [t58,t0,t1,t2,t113,t3,t4]
def v2096 := [t173,t150,t124,t145,t127,t187]
def v2097 := [t173,t123,t124,t145,t127,t187]
def v2098 := [t147,t123,t124,t145,t127,t187]
def v2099 := [t123,t124,t193,t145,t127,t187]
def v2100 := [t123,t149,t124,t145,t127,t187]
def v2101 := [t150,t123,t124,t125,t127,t187]
def v2102 := [t123,t124,t145,t125,t127,t187]
def v2103 := [t178,t123,t124,t145,t127,t187]
def v2104 := [t150,t123,t124,t145,t175,t187]
def v2105 := [t176,t123,t124,t145,t127,t187]
def v2106 := [t123,t124,t145,t195,t187]
def v2107 := [t150,t123,t124,t145,t195,t187]
def v2108 := [t123,t124,t145,t195,t127,t187]
def t312 := 0xea8f0c
def v2109 := [t123,t124,t145,t312,t127]
def v2110 := [t150,t123,t124,t145,t312,t127]
def v2111 := [t123,t124,t145,t312,t127,t187]
def v2112 := [t150,t124,t146,t145,t127,t187]
def v2113 := [t150,t148,t124,t145,t127,t187]
def v2114 := [t124,t197,t127,t187]
def v2115 := [t150,t124,t197,t127,t187]
def v2116 := [t124,t174,t197,t127,t187]
def v2117 := [t150,t124,t174,t195,t187]
def v2118 := [t150,t124,t174,t312,t127]
def v2119 := [t150,t154,t174,t187]
def v2120 := [t150,t154,t124,t174,t187]
def v2121 := [t150,t154,t174,t127,t187]
def v2122 := [t192,t150,t124,t174,t187]
def v2123 := [t150,t174,t155,t127,t187]
def v2124 := [t150,t124,t174,t187,t188]
def v2125 := [t150,t124,t200,t174,t187]
def v2126 := [t150,t124,t174,t127,t246]
def t313 := 0x5ca3cc
def v2127 := [t150,t124,t313,t174,t127]
def v2128 := [t150,t123,t124,t174,t127,t187]
def v2129 := [t150,t124,t174,t145,t127,t187]
def v2130 := [t150,t151,t124,t145,t127,t187]
def v2131 := [t124,t193,t145,t152,t187]
def v2132 := [t150,t124,t125,t152,t187]
def v2133 := [t124,t145,t125,t152,t187]
def v2134 := [t150,t124,t145,t201,t187]
def v2135 := [t124,t145,t152,t201,t187]
def v2136 := [t124,t145,t152,t187,t161]
def v2137 := [t176,t124,t145,t152,t187]
def v2138 := [t150,t145,t155,t152,t187]
def v2139 := [t150,t124,t299,t145,t152]
def t314 := 0x1423cc
def v2140 := [t150,t314,t124,t145,t152]
def v2141 := [t150,t314,t124,t145,t187]
def v2142 := [t150,t123,t124,t145,t152,t187]
def v2143 := [t150,t124,t145,t152,t127,t187]
def v2144 := [t150,t124,t145,t262,t127]
def v2145 := [t150,t123,t124,t145,t262,t127]
def v2146 := [t150,t124,t145,t262,t127,t187]
def v2147 := [t150,t123,t154,t124,t145,t187]
def v2148 := [t150,t123,t154,t145,t127,t187]
def v2149 := [t192,t150,t123,t124,t145,t187]
def v2150 := [t150,t123,t145,t155,t127,t187]
def v2151 := [t150,t123,t124,t177,t145,t187]
def v2152 := [t150,t123,t124,t299,t145,t127]
def v2153 := [t118,t0,t1,t99,t2,t3,t4]
def v2154 := [t0,t112,t1,t99,t2,t3,t4]
def v2155 := [t98,t0,t1,t2,t113,t3,t4]
def v2156 := [t0,t1,t99,t2,t113,t3,t4]
def v2157 := [t147,t123,t124,t145,t175,t187]
def v2158 := [t123,t124,t146,t145,t175,t187]
def v2159 := [t148,t123,t124,t145,t175,t187]
def v2160 := [t123,t149,t124,t145,t175,t187]
def v2161 := [t173,t123,t124,t145,t175,t187]
def v2162 := [t123,t124,t145,t125,t175,t187]
def v2163 := [t123,t124,t174,t145,t175,t187]
def v2164 := [t123,t124,t145,t152,t187]
def v2165 := [t124,t145,t152,t175,t187]
def v2166 := [t123,t124,t177,t152,t188]
def v2167 := [t124,t177,t152,t175,t188]
def v2168 := [t124,t177,t245,t175]
def v2169 := [t123,t124,t177,t245,t175]
def v2170 := [t124,t177,t245,t175,t188]
def v2171 := [t123,t124,t177,t259,t188]
def v2172 := [t123,t124,t177,t175,t246]
def v2173 := [t123,t124,t177,t247,t175]
def v2174 := [t123,t124,t289,t188]
def v2175 := [t123,t124,t177,t289,t188]
def v2176 := [t123,t124,t289,t175,t188]
def v2177 := [t190,t123,t124,t177,t188]
def v2178 := [t123,t124,t145,t152,t175,t187]
def v2179 := [t151,t123,t124,t145,t175,t187]
def v2180 := [t123,t124,t145,t175,t187,t161]
def v2181 := [t176,t123,t124,t145,t175,t187]
def v2182 := [t124,t145,t262,t175,t187]
def v2183 := [t123,t124,t145,t262,t175,t187]
def v2184 := [t191,t123,t124,t145,t175,t187]
def v2185 := [t123,t124,t145,t126,t175,t187]
def v2186 := [t123,t153,t124,t145,t175,t187]
def v2187 := [t123,t124,t186,t145,t175,t187]
def v2188 := [t123,t154,t145,t175,t187]
def v2189 := [t123,t154,t124,t145,t175,t187]
def v2190 := [t192,t123,t124,t145,t175,t187]
def v2191 := [t123,t145,t259,t175,t187]
def v2192 := [t123,t124,t145,t259,t175,t187]
def v2193 := [t123,t145,t155,t175,t187]
def v2194 := [t123,t124,t145,t155,t175,t187]
def v2195 := [t123,t124,t189,t145,t175,t187]
def v2196 := [t123,t124,t145,t175,t187,t235]
def v2197 := [t190,t123,t124,t145,t175,t187]
def v2198 := [t123,t124,t288,t145,t175,t187]
def v2199 := [t123,t124,t145,t175,t187,t246]
def v2200 := [t123,t124,t299,t145,t175]
def v2201 := [t123,t124,t299,t145,t175,t187]
def v2202 := [t124,t145,t152,t127,t175,t187]
def v2203 := [t123,t124,t145,t152,t127,t187]
def v2204 := [t124,t145,t262,t127,t175]
def v2205 := [t123,t124,t145,t262,t127,t175]
def v2206 := [t124,t145,t262,t127,t175,t187]
def v2207 := [t123,t154,t145,t127,t175,t187]
def v2208 := [t123,t145,t155,t127,t175,t187]
def v2209 := [t123,t154,t145,t127,t187]
def v2210 := [t123,t154,t124,t145,t127,t187]
def v2211 := [t192,t123,t124,t145,t127,t187]
def v2212 := [t123,t145,t259,t127,t187]
def v2213 := [t123,t124,t145,t259,t127,t187]
def v2214 := [t123,t145,t259,t127,t175,t187]
def v2215 := [t123,t124,t145,t175,t187,t188]
def v2216 := [t123,t124,t177,t145,t175,t187]
def v2217 := [t123,t124,t189,t145,t127,t187]
def v2218 := [t123,t124,t145,t127,t187,t235]
def v2219 := [t190,t123,t124,t145,t127,t187]
def v2220 := [t123,t124,t288,t145,t127,t187]
def v2221 := [t123,t124,t145,t127,t175,t246]
def v2222 := [t123,t124,t299,t145,t127,t175]
def v2223 := [t114,t0,t1,t99,t2,t3,t4]
def v2224 := [t115,t0,t1,t99,t2,t3,t4]
def v2225 := [t172,t0,t1,t99,t2,t3,t4]
def t315 := 0x304d182103f8e00
def v2226 := [t0,t315,t1,t2,t3,t4]
def t316 := 0x2248b40503c7e00
def v2227 := [t316,t0,t1,t2,t3,t4]
def v2228 := [t176,t151,t123,t124,t145,t127]
def v2229 := [t147,t151,t123,t124,t145,t127]
def v2230 := [t151,t123,t124,t257,t145,t127]
def v2231 := [t258,t151,t123,t124,t145,t127]
def v2232 := [t151,t123,t149,t124,t145,t127]
def v2233 := [t173,t151,t123,t124,t145,t127]
def v2234 := [t123,t124,t145,t261,t127]
def v2235 := [t151,t123,t124,t145,t261,t127]
def v2236 := [t178,t151,t123,t124,t145,t127]
def v2237 := [t151,t123,t124,t174,t145,t127]
def v2238 := [t151,t123,t124,t145,t152,t127]
def v2239 := [t147,t151,t146,t145,t127]
def v2240 := [t258,t151,t146,t145,t127]
def v2241 := [t151,t311,t124,t145,t127]
def v2242 := [t311,t124,t146,t145,t127]
def v2243 := [t124,t146,t145,t261,t127]
def v2244 := [t151,t124,t146,t145,t152]
def v2245 := [t148,t151,t124,t145,t127]
def v2246 := [t148,t151,t146,t145,t127]
def v2247 := [t151,t146,t145,t126,t127]
def v2248 := [t151,t153,t146,t145,t127]
def v2249 := [t151,t154,t146,t145,t127]
def v2250 := [t151,t146,t145,t155,t127]
def v2251 := [t151,t123,t124,t146,t145,t127]
def v2252 := [t148,t151,t123,t124,t145,t127]
def v2253 := [t151,t124,t145,t125,t127]
def v2254 := [t151,t123,t124,t145,t125,t127]
def v2255 := [t191,t151,t123,t124,t145,t127]
def v2256 := [t151,t123,t124,t145,t126,t127]
def v2257 := [t151,t123,t153,t124,t145,t127]
def v2258 := [t151,t123,t124,t186,t145,t127]
def v2259 := [t151,t123,t154,t124,t145,t127]
def v2260 := [t151,t123,t124,t145,t127,t187]
def v2261 := [t192,t151,t123,t124,t145,t127]
def v2262 := [t151,t123,t124,t145,t155,t127]
def v2263 := [t151,t123,t124,t189,t145,t127]
def v2264 := [t151,t123,t124,t145,t127,t188]
def v2265 := [t190,t151,t123,t124,t145,t127]
def v2266 := [t151,t123,t124,t177,t145,t127]
def v2267 := [t0,t315,t1,t99,t2,t3,t4]
def v2268 := [t316,t0,t1,t2,t113,t3,t4]
def v2269 := [t0,t1,t99,t2,t64,t3,t4]
def v2270 := [t176,t123,t124,t145,t175,t161]
def v2271 := [t124,t145,t152,t127,t175,t161]
def v2272 := [t124,t145,t262,t127,t175,t161]
def v2273 := [t123,t154,t145,t127,t175,t161]
def v2274 := [t123,t145,t155,t175,t161]
def v2275 := [t123,t124,t145,t155,t175,t161]
def v2276 := [t123,t145,t155,t127,t175,t161]
def v2277 := [t123,t145,t259,t127,t175,t161]
def v2278 := [t123,t124,t145,t175,t161,t188]
def v2279 := [t123,t124,t177,t145,t175,t161]
def v2280 := [t123,t124,t145,t127,t161,t235]
def v2281 := [t123,t124,t288,t145,t127,t161]
def v2282 := [t123,t124,t145,t127,t175,t157]
def v2283 := [t162,t242,t124,t145,t175]
def v2284 := [t162,t151,t124,t145,t175]
def v2285 := [t123,t243,t145,t175]
def v2286 := [t162,t123,t243,t145,t175]
def v2287 := [t123,t124,t243,t145,t175]
def v2288 := [t162,t123,t154,t145,t175]
def v2289 := [t123,t124,t244,t175]
def v2290 := [t162,t123,t124,t244,t175]
def v2291 := [t123,t124,t145,t244,t175]
def v2292 := [t162,t124,t145,t152,t175]
def v2293 := [t162,t123,t145,t259,t175]
def v2294 := [t162,t123,t124,t145,t127,t175]
def v2295 := [t242,t124,t145,t127,t175]
def v2296 := [t123,t243,t145,t127,t175]
def v2297 := [t123,t124,t244,t127,t175]
def v2298 := [t162,t123,t145,t155,t175]
def v2299 := [t162,t123,t145,t259,t127]
def v2300 := [t162,t123,t124,t145,t175,t161]
def t317 := 0x42000400380038
def v2301 := [t317,t0,t1,t2,t3,t4]
def v2302 := [t265,t0,t1,t99,t2,t3,t4]
def v2303 := [t317,t0,t1,t2,t3,t207,t4]
def t318 := 0x292e50c1c07007
def v2304 := [t318,t0,t1,t2,t3,t4]
def t319 := 0xd13c2c0380e07
def v2305 := [t319,t0,t1,t2,t3,t4]
def v2306 := [t318,t0,t1,t99,t2,t3,t4]
def v2307 := [t319,t0,t1,t99,t2,t3,t4]
def v2308 := [t0,t1,t99,t119,t2,t3,t4]
def v2309 := [t98,t0,t1,t2,t3,t4,t120]
def v2310 := [t0,t1,t99,t2,t3,t4,t120]
def v2311 := [t121,t0,t1,t99,t2,t3,t4]
def v2312 := [t114,t0,t1,t2,t3,t4,t109]
def v2313 := [t122,t0,t1,t99,t2,t3,t4]
def v2314 := [t172,t0,t1,t2,t3,t4,t109]
def v2315 := [t0,t206,t1,t99,t2,t3,t4]
def v2316 := [t0,t1,t99,t2,t3,t207,t4]
def v2317 := [t208,t0,t1,t99,t2,t3,t4]
def t320 := 0x320ec1011c7f000
def v2318 := [t0,t320,t1,t2,t3,t4]
def v2319 := [t0,t320,t1,t99,t2,t3,t4]
def v2320 := [t0,t1,t2,t3,t68,t4]
def v2321 := [t0,t1,t99,t2,t3,t68,t4]
def t321 := 0x9000200e0001c0
def v2322 := [t321,t0,t1,t2,t3,t4]
def v2323 := [t321,t0,t1,t99,t2,t3,t4]
def v2324 := [t0,t1,t99,t2,t210,t3,t4]
def v2325 := [t0,t1,t99,t2,t3,t4,t211]
def v2326 := [t212,t0,t1,t99,t2,t3,t4]
def v2327 := [t213,t0,t1,t99,t2,t3,t4]
def v2328 := [t0,t75,t1,t99,t2,t3,t4]
def v2329 := [t0,t1,t99,t2,t3,t4,t76]
def v2330 := [t77,t0,t1,t99,t2,t3,t4]
def v2331 := [t78,t0,t1,t2,t3,t4,t109]
def v2332 := [t78,t0,t1,t99,t2,t3,t4]
def t322 := 0x32dc90091f80000
def v2333 := [t0,t1,t322,t2,t3,t4]
def t323 := 0x324cb4040047e00
def v2334 := [t0,t323,t1,t2,t3,t4]
def v2335 := [t0,t1,t322,t99,t2,t3,t4]
def v2336 := [t0,t323,t1,t2,t3,t4,t109]
def v2337 := [t0,t1,t2,t3,t4,t278]
def v2338 := [t0,t1,t99,t2,t3,t4,t278]
def t324 := 0x36d24007fe07
def v2339 := [t324,t0,t1,t2,t3,t4]
def t325 := 0xdb00249ff80007
def v2340 := [t325,t0,t1,t2,t3,t4]
def v2341 := [t324,t0,t1,t99,t2,t3,t4]
def v2342 := [t325,t0,t1,t2,t3,t4,t109]
def t326 := 0xd200240e000000
def v2343 := [t326,t0,t1,t2,t3,t4]
def t327 := 0x4b000480380000
def v2344 := [t327,t0,t1,t2,t3,t4]
def v2345 := [t326,t0,t1,t99,t2,t3,t4]
def v2346 := [t327,t0,t1,t2,t3,t207,t4]
def v2347 := [t108,t0,t1,t2,t3,t4]
def v2348 := [t0,t1,t2,t3,t4,t109]
def v2349 := [t110,t0,t1,t2,t3,t4]
def v2350 := [t111,t0,t1,t2,t3,t4]
def v2351 := [t0,t204,t1,t2,t3,t4]
def v2352 := [t0,t1,t2,t3,t62,t4]
def v2353 := [t205,t0,t1,t2,t3,t4]
def v2354 := [t118,t0,t1,t2,t3,t4]
def v2355 := [t0,t1,t2,t113,t3,t4]
def v2356 := [t115,t0,t1,t2,t3,t4]
def v2357 := [t0,t1,t119,t2,t3,t4]
def v2358 := [t0,t1,t2,t3,t4,t120]
def v2359 := [t121,t0,t1,t2,t3,t4]
def v2360 := [t122,t0,t1,t2,t3,t4]
def v2361 := [t0,t206,t1,t2,t3,t4]
def v2362 := [t0,t1,t2,t3,t207,t4]
def v2363 := [t208,t0,t1,t2,t3,t4]
def v2364 := [t0,t1,t2,t210,t3,t4]
def v2365 := [t0,t1,t2,t3,t4,t211]
def v2366 := [t212,t0,t1,t2,t3,t4]
def v2367 := [t213,t0,t1,t2,t3,t4]
def v2368 := [t0,t75,t1,t2,t3,t4]
def v2369 := [t0,t1,t2,t3,t4,t76]
def v2370 := [t5,t0,t1,t2,t3,t4,t76]
def v2371 := [t58,t0,t1,t2,t3,t4,t76]
def v2372 := [t61,t0,t1,t2,t3,t4,t76]
def v2373 := [t0,t1,t2,t3,t59,t4,t76]
def v2374 := [t102,t0,t1,t2,t3,t4,t76]
def v2375 := [t98,t0,t1,t2,t3,t4,t76]
def v2376 := [t100,t0,t1,t2,t3,t4,t76]
def v2377 := [t114,t0,t1,t2,t3,t4,t76]
def v2378 := [t101,t0,t1,t2,t3,t4,t76]
def v2379 := [t172,t0,t1,t2,t3,t4,t76]
def v2380 := [t108,t0,t1,t2,t3,t4,t76]
def v2381 := [t0,t1,t2,t3,t4,t109,t76]
def v2382 := [t110,t0,t1,t2,t3,t4,t76]
def v2383 := [t111,t0,t1,t2,t3,t4,t76]
def v2384 := [t128,t0,t1,t2,t3,t4]
def v2385 := [t128,t0,t1,t2,t3,t4,t76]
def v2386 := [t0,t1,t2,t3,t4,t76,t278]
def v2387 := [t17,t0,t1,t2,t3,t4]
def v2388 := [t17,t0,t1,t2,t3,t4,t76]
def v2389 := [t129,t0,t1,t2,t3,t4]
def v2390 := [t282,t0,t1,t2,t3,t4]
def t328 := 0xd0340c0380e00
def v2391 := [t328,t0,t1,t2,t3,t4]
def v2392 := [t328,t282,t0,t1,t2,t3,t4]
def t329 := 0x26f9bc6d1fc7e07
def v2393 := [t0,t329,t1,t2,t3,t4]
def v2394 := [t282,t0,t329,t1,t2,t3,t4]
def v2395 := [t133,t0,t1,t2,t3,t4]
def v2396 := [t133,t282,t0,t1,t2,t3,t4]
def t330 := 0x220880011c47007
def v2397 := [t330,t0,t1,t2,t3,t4]
def v2398 := [t282,t330,t0,t1,t2,t3,t4]
def t331 := 0x46118600380e00
def v2399 := [t331,t0,t1,t2,t3,t4]
def v2400 := [t331,t282,t0,t1,t2,t3,t4]
def t332 := 0x34fd3c6de3f8e38
def v2401 := [t0,t1,t2,t332,t3,t4]
def v2402 := [t282,t0,t1,t2,t332,t3,t4]
def v2403 := [t135,t0,t1,t2,t3,t4]
def v2404 := [t135,t282,t0,t1,t2,t3,t4]
def t333 := 0x300c0001e078038
def v2405 := [t0,t333,t1,t2,t3,t4]
def v2406 := [t282,t0,t333,t1,t2,t3,t4]
def v2407 := [t282,t0,t1,t2,t4,t281]
def v2408 := [t0,t1,t2,t3,t4,t281]
def v2409 := [t282,t0,t1,t2,t3,t4,t281]
def v2410 := [t172,t282,t0,t1,t2,t3,t4]
def t334 := 0x36fffd6c03ffe00
def v2411 := [t0,t1,t2,t334,t3,t4]
def v2412 := [t282,t0,t1,t2,t334,t3,t4]
def v2413 := [t327,t282,t0,t1,t2,t3,t4]
def v2414 := [t282,t0,t206,t1,t2,t3,t4]
def v2415 := [t213,t282,t0,t1,t2,t3,t4]
def t335 := 0x3ffdbe6dff80e00
def v2416 := [t0,t1,t2,t3,t4,t335]
def v2417 := [t282,t0,t1,t2,t3,t4,t335]
def t336 := 0x12c240000e00
def v2418 := [t336,t0,t1,t2,t3,t4]
def v2419 := [t336,t282,t0,t1,t2,t3,t4]
def v2420 := [t282,t0,t1,t2,t210,t3,t4]
def v2421 := [t282,t5,t0,t1,t2,t3,t4]
def v2422 := [t57,t282,t0,t1,t2,t3,t4]
def v2423 := [t282,t60,t0,t1,t2,t3,t4]
def v2424 := [t282,t61,t0,t1,t2,t3,t4]
def v2425 := [t282,t0,t1,t2,t59,t4]
def v2426 := [t282,t0,t1,t2,t3,t59,t4]
def v2427 := [t58,t282,t0,t1,t2,t3,t4]
def v2428 := [t282,t102,t0,t1,t2,t4]
def v2429 := [t282,t102,t0,t1,t2,t3,t4]
def v2430 := [t282,t98,t0,t1,t2,t3,t4]
def v2431 := [t282,t0,t1,t99,t2,t3,t4]
def v2432 := [t100,t282,t0,t1,t2,t3,t4]
def v2433 := [t282,t101,t0,t1,t2,t3,t4]
def v2434 := [t282,t108,t0,t1,t2,t3,t4]
def v2435 := [t282,t0,t1,t2,t3,t4,t109]
def v2436 := [t110,t282,t0,t1,t2,t3,t4]
def v2437 := [t282,t111,t0,t1,t2,t3,t4]
def v2438 := [t282,t0,t204,t1,t2,t3,t4]
def v2439 := [t282,t0,t1,t2,t62,t4]
def v2440 := [t282,t0,t1,t2,t3,t62,t4]
def v2441 := [t205,t282,t0,t1,t2,t3,t4]
def v2442 := [t282,t118,t0,t1,t2,t4]
def v2443 := [t282,t118,t0,t1,t2,t3,t4]
def v2444 := [t282,t0,t112,t1,t2,t3,t4]
def v2445 := [t282,t0,t1,t2,t113,t3,t4]
def v2446 := [t114,t282,t0,t1,t2,t3,t4]
def v2447 := [t115,t282,t0,t1,t2,t3,t4]
def v2448 := [t282,t0,t1,t119,t2,t3,t4]
def v2449 := [t282,t0,t1,t2,t3,t4,t120]
def v2450 := [t121,t282,t0,t1,t2,t3,t4]
def v2451 := [t282,t122,t0,t1,t2,t3,t4]
def v2452 := [t282,t0,t1,t2,t207,t4]
def v2453 := [t282,t0,t1,t2,t3,t207,t4]
def v2454 := [t282,t208,t0,t1,t2,t4]
def v2455 := [t282,t208,t0,t1,t2,t3,t4]
def v2456 := [t282,t0,t1,t2,t4,t211]
def v2457 := [t282,t0,t1,t2,t3,t4,t211]
def v2458 := [t212,t282,t0,t1,t2,t4]
def v2459 := [t212,t282,t0,t1,t2,t3,t4]
def v2460 := [t282,t0,t75,t1,t2,t3,t4]
def v2461 := [t282,t0,t1,t2,t3,t4,t76]
def v2462 := [t77,t282,t0,t1,t2,t3,t4]
def v2463 := [t282,t78,t0,t1,t2,t3,t4]
def v2464 := [t129,t0,t1,t2,t3,t4,t76]
def v2465 := [t328,t0,t1,t2,t3,t4,t76]
def v2466 := [t0,t329,t1,t2,t3,t4,t76]
def v2467 := [t133,t0,t1,t2,t3,t4,t76]
def v2468 := [t330,t0,t1,t2,t3,t4,t76]
def v2469 := [t331,t0,t1,t2,t3,t4,t76]
def v2470 := [t0,t1,t2,t332,t3,t4,t76]
def v2471 := [t135,t0,t1,t2,t3,t4,t76]
def v2472 := [t0,t333,t1,t2,t3,t4,t76]
def v2473 := [t282,t0,t1,t2,t4,t76,t281]
def v2474 := [t0,t1,t2,t3,t4,t76,t281]
def v2475 := [t0,t1,t2,t334,t3,t4,t76]
def v2476 := [t327,t0,t1,t2,t3,t4,t76]
def v2477 := [t0,t206,t1,t2,t3,t4,t76]
def v2478 := [t213,t0,t1,t2,t3,t4,t76]
def v2479 := [t0,t1,t2,t3,t4,t335,t76]
def v2480 := [t336,t0,t1,t2,t3,t4,t76]
def v2481 := [t0,t1,t2,t210,t3,t4,t76]
def v2482 := [t0,t1,t2,t280,t3,t4]
def v2483 := [t282,t0,t1,t2,t280,t3,t4]
def v2484 := [t0,t1,t2,t280,t3,t4,t76]
def v2485 := [t282,t0,t1,t2,t59,t4,t76]
def v2486 := [t282,t102,t0,t1,t2,t4,t76]
def v2487 := [t282,t128,t0,t1,t2,t3,t4]
def v2488 := [t282,t0,t1,t2,t3,t4,t278]
def v2489 := [t17,t282,t0,t1,t2,t3,t4]
def v2490 := [t282,t129,t0,t1,t2,t3,t4]
def v2491 := [t282,t0,t1,t2,t62,t4,t76]
def v2492 := [t282,t118,t0,t1,t2,t4,t76]
def v2493 := [t282,t0,t1,t130,t2,t3,t4]
def v2494 := [t282,t0,t1,t2,t3,t4,t279]
def v2495 := [t43,t282,t0,t1,t2,t3,t4]
def v2496 := [t282,t131,t0,t1,t2,t3,t4]
def v2497 := [t282,t0,t1,t2,t207,t4,t76]
def v2498 := [t282,t208,t0,t1,t2,t4,t76]
def v2499 := [t282,t0,t1,t2,t4,t211,t76]
def v2500 := [t212,t282,t0,t1,t2,t4,t76]
def v2501 := [t20,t282,t0,t1,t2,t4]
def v2502 := [t17,t129,t1,t2,t3,t4]
def v2503 := [t20,t282,t0,t1,t2,t3,t4]
def v2504 := [t20,t282,t0,t1,t2,t4,t76]
def v2505 := [t282,t0,t75,t2,t3,t76]
def v2506 := [t282,t0,t75,t1,t2,t3,t76]
def v2507 := [t282,t0,t75,t2,t3,t4,t76]
def v2508 := [t77,t282,t0,t1,t2,t3,t76]
def v2509 := [t282,t78,t0,t2,t3,t4,t76]
def v2510 := [t0,t204,t1,t2,t3,t4,t76]
def v2511 := [t0,t1,t2,t3,t62,t4,t76]
def v2512 := [t205,t0,t1,t2,t3,t4,t76]
def v2513 := [t118,t0,t1,t2,t3,t4,t76]
def v2514 := [t0,t112,t1,t2,t3,t4,t76]
def v2515 := [t0,t1,t2,t113,t3,t4,t76]
def v2516 := [t115,t0,t1,t2,t3,t4,t76]
def v2517 := [t0,t1,t119,t2,t3,t4,t76]
def v2518 := [t0,t1,t2,t3,t4,t120,t76]
def v2519 := [t121,t0,t1,t2,t3,t4,t76]
def v2520 := [t122,t0,t1,t2,t3,t4,t76]
def v2521 := [t0,t1,t130,t2,t3,t4]
def v2522 := [t0,t1,t130,t2,t3,t4,t76]
def v2523 := [t0,t1,t2,t3,t4,t279]
def v2524 := [t0,t1,t2,t3,t4,t76,t279]
def v2525 := [t43,t0,t1,t2,t3,t4]
def v2526 := [t43,t0,t1,t2,t3,t4,t76]
def v2527 := [t131,t0,t1,t2,t3,t4]
def v2528 := [t131,t0,t1,t2,t3,t4,t76]
def v2529 := [t0,t1,t2,t3,t207,t4,t76]
def v2530 := [t208,t0,t1,t2,t3,t4,t76]
def v2531 := [t0,t1,t2,t3,t4,t211,t76]
def v2532 := [t212,t0,t1,t2,t3,t4,t76]
def v2533 := [t20,t0,t1,t2,t3,t4]
def v2534 := [t20,t0,t1,t2,t3,t4,t76]
def v2535 := [t0,t75,t2,t3,t76]
def v2536 := [t0,t75,t1,t2,t3,t76]
def v2537 := [t0,t75,t2,t3,t4,t76]
def v2538 := [t0,t75,t1,t2,t3,t4,t76]
def v2539 := [t77,t0,t1,t2,t3,t76]
def v2540 := [t78,t0,t2,t3,t4,t76]
def v2541 := [t77,t0,t1,t2,t3,t4,t76]
def v2542 := [t78,t0,t1,t2,t3,t4,t76]
def v2543 := [t78,t0,t1,t2,t3,t4]
def v2544 := [t77,t0,t1,t2,t3,t4]
theorem b0 : Ban 12 5 v3 := checkedSmall
theorem b1 : Ban 12 5 v4 := checkedSmall
theorem b2 : Ban 12 5 v5 := checkedSmall
theorem b3 : Ban 12 4 v8 := checkedSmall
theorem b4 : Ban 12 4 v9 := checkedSmall
theorem b5 : Ban 12 4 v10 := checkedSmall
theorem b6 : Ban 12 4 v11 := checkedSmall
theorem b7 : Ban 12 4 v12 := checkedSmall
theorem b8 : Ban 12 4 v13 := checkedSmall
theorem b9 : Ban 12 4 v14 := checkedSmall
theorem b10 : Ban 12 4 v15 := checkedSmall
theorem b11 : Ban 12 4 v16 := checkedSmall
theorem b12 : Ban 12 4 v17 := checkedSmall
theorem b13 : Ban 12 4 v18 := checkedSmall
theorem b14 : Ban 12 4 v19 := checkedSmall
theorem b15 : Ban 12 4 v20 := checkedSmall
theorem b16 : Ban 12 4 v21 := checkedSmall
theorem b17 : Ban 12 4 v22 := checkedSmall
theorem b18 : Ban 12 4 v23 := checkedSmall
theorem b19 : Ban 12 4 v24 := checkedSmall
theorem b20 : Ban 12 4 v25 := checkedSmall
theorem b21 : Ban 12 4 v26 := checkedSmall
theorem b22 : Ban 12 4 v27 := checkedSmall
theorem b23 : Ban 12 4 v28 := checkedSmall
theorem b24 : Ban 12 4 v29 := checkedSmall
theorem b25 : Ban 12 4 v30 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b26 : Ban 12 5 v7 := viaBranch (ws := [v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30]) (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b27 : Ban 12 5 v6 := viaPerm map29_1 map29_1 b26 (by decide +kernel) (by decide +kernel)
theorem b28 : Ban 12 5 v31 := checkedSmall
theorem b29 : Ban 12 5 v32 := checkedSmall
theorem b30 : Ban 12 5 v33 := checkedSmall
theorem b31 : Ban 12 5 v34 := viaPerm map29_3 map29_3 b26 (by decide +kernel) (by decide +kernel)
theorem b32 : Ban 12 5 v35 := checkedSmall
theorem b33 : Ban 12 4 v37 := checkedSmall
theorem b34 : Ban 12 4 v38 := checkedSmall
theorem b35 : Ban 12 4 v39 := checkedSmall
theorem b36 : Ban 12 4 v40 := checkedSmall
theorem b37 : Ban 12 4 v41 := checkedSmall
theorem b38 : Ban 12 4 v42 := checkedSmall
theorem b39 : Ban 12 4 v43 := checkedSmall
theorem b40 : Ban 12 4 v44 := checkedSmall
theorem b41 : Ban 12 4 v45 := checkedSmall
theorem b42 : Ban 12 4 v46 := checkedSmall
theorem b43 : Ban 12 4 v47 := checkedSmall
theorem b44 : Ban 12 4 v48 := checkedSmall
theorem b45 : Ban 12 4 v49 := checkedSmall
theorem b46 : Ban 12 4 v50 := checkedSmall
theorem b47 : Ban 12 4 v51 := checkedSmall
theorem b48 : Ban 12 4 v52 := checkedSmall
theorem b49 : Ban 12 4 v53 := checkedSmall
theorem b50 : Ban 12 4 v54 := checkedSmall
theorem b51 : Ban 12 4 v55 := checkedSmall
theorem b52 : Ban 12 4 v56 := checkedSmall
theorem b53 : Ban 12 4 v57 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b54 : Ban 12 5 v36 := viaBranch (ws := [v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v22,v48,v49,v10,v50,v51,v52,v53,v54,v55,v56,v57]) (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b17 (consBan b44 (consBan b45 (consBan b5 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b55 : Ban 12 5 v57 := checkedSmall
theorem b56 : Ban 12 5 v46 := checkedSmall
theorem b57 : Ban 12 4 v59 := checkedSmall
theorem b58 : Ban 12 4 v60 := checkedSmall
theorem b59 : Ban 12 4 v61 := checkedSmall
theorem b60 : Ban 12 4 v62 := checkedSmall
theorem b61 : Ban 12 4 v63 := checkedSmall
theorem b62 : Ban 12 4 v64 := checkedSmall
theorem b63 : Ban 12 4 v65 := checkedSmall
theorem b64 : Ban 12 4 v66 := checkedSmall
theorem b65 : Ban 12 4 v67 := checkedSmall
theorem b66 : Ban 12 4 v68 := checkedSmall
theorem b67 : Ban 12 4 v69 := checkedSmall
theorem b68 : Ban 12 4 v70 := checkedSmall
theorem b69 : Ban 12 4 v71 := checkedSmall
theorem b70 : Ban 12 4 v72 := checkedSmall
theorem b71 : Ban 12 4 v73 := checkedSmall
theorem b72 : Ban 12 4 v74 := checkedSmall
theorem b73 : Ban 12 4 v75 := checkedSmall
theorem b74 : Ban 12 4 v76 := checkedSmall
theorem b75 : Ban 12 4 v77 := checkedSmall
theorem b76 : Ban 12 4 v78 := checkedSmall
theorem b77 : Ban 12 4 v79 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b78 : Ban 12 5 v58 := viaBranch (ws := [v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v14,v69,v70,v71,v72,v73,v74,v75,v76,v77,v24,v78,v79]) (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b9 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b19 (consBan b76 (consBan b77 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b79 : Ban 12 5 v80 := checkedSmall
theorem b80 : Ban 12 5 v64 := checkedSmall
theorem b81 : Ban 12 5 v66 := checkedSmall
theorem b82 : Ban 12 5 v13 := checkedSmall
theorem b83 : Ban 12 5 v19 := checkedSmall
theorem b84 : Ban 12 5 v81 := checkedSmall
theorem b85 : Ban 12 5 v82 := checkedSmall
theorem b86 : Ban 12 5 v83 := checkedSmall
theorem b87 : Ban 12 5 v84 := viaPerm map29_2 map29_2 b26 (by decide +kernel) (by decide +kernel)
theorem b88 : Ban 12 5 v85 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b89 : Ban 12 6 v2 := viaBranch (ws := [v3,v4,v5,v6,v31,v32,v33,v34,v35,v36,v57,v46,v58,v80,v64,v66,v13,v19,v7,v81,v82,v83,v84,v85]) (consBan b0 (consBan b1 (consBan b2 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b54 (consBan b55 (consBan b56 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b26 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 6 v2 := viaSub (ws := [v2]) (consBan b89 (nilBan 12 6)) (by decide) (by decide +kernel)
theorem b188 : Ban 12 6 v2 := bySubset w0
theorem b423 : Ban 12 5 v237 := checkedSmall
theorem b424 : Ban 12 5 v238 := checkedSmall
theorem b425 : Ban 12 5 v239 := checkedSmall
theorem b426 : Ban 12 5 v240 := checkedSmall
theorem b427 : Ban 12 5 v241 := checkedSmall
theorem b428 : Ban 12 5 v242 := checkedSmall
theorem b429 : Ban 12 5 v63 := checkedSmall
theorem b430 : Ban 12 5 v243 := checkedSmall
theorem b431 : Ban 12 5 v244 := checkedSmall
theorem b432 : Ban 12 5 v245 := checkedSmall
theorem b433 : Ban 12 5 v246 := checkedSmall
theorem b434 : Ban 12 5 v247 := checkedSmall
theorem b435 : Ban 12 5 v248 := checkedSmall
theorem b436 : Ban 12 5 v16 := checkedSmall
theorem b437 : Ban 12 5 v249 := checkedSmall
theorem b438 : Ban 12 5 v250 := checkedSmall
theorem b439 : Ban 12 5 v251 := checkedSmall
theorem b440 : Ban 12 5 v252 := checkedSmall
theorem b441 : Ban 12 5 v253 := checkedSmall
theorem b442 : Ban 12 5 v254 := checkedSmall
theorem b443 : Ban 12 5 v255 := checkedSmall
theorem b444 : Ban 12 5 v256 := checkedSmall
theorem b445 : Ban 12 4 v258 := checkedSmall
theorem b446 : Ban 12 4 v259 := checkedSmall
theorem b447 : Ban 12 4 v260 := checkedSmall
theorem b448 : Ban 12 4 v261 := checkedSmall
theorem b449 : Ban 12 4 v262 := checkedSmall
theorem b450 : Ban 12 4 v263 := checkedSmall
theorem b451 : Ban 12 4 v264 := checkedSmall
theorem b452 : Ban 12 4 v265 := checkedSmall
theorem b453 : Ban 12 4 v266 := checkedSmall
theorem b454 : Ban 12 4 v267 := checkedSmall
theorem b455 : Ban 12 4 v268 := checkedSmall
theorem b456 : Ban 12 4 v269 := checkedSmall
theorem b457 : Ban 12 4 v270 := checkedSmall
theorem b458 : Ban 12 4 v271 := checkedSmall
theorem b459 : Ban 12 4 v272 := checkedSmall
theorem b460 : Ban 12 4 v273 := checkedSmall
theorem b461 : Ban 12 4 v274 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b462 : Ban 12 5 v25 := viaBranch (ws := [v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v24,v26,v269,v28,v270,v12,v271,v272,v273,v274]) (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b19 (consBan b21 (consBan b456 (consBan b23 (consBan b457 (consBan b7 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b463 : Ban 12 5 v257 := viaPerm map29_3 map29_3 b462 (by decide +kernel) (by decide +kernel)
theorem b464 : Ban 12 5 v275 := checkedSmall
theorem b465 : Ban 12 5 v276 := checkedSmall
theorem b466 : Ban 12 5 v277 := checkedSmall
theorem b467 : Ban 12 5 v278 := checkedSmall
theorem b468 : Ban 12 5 v279 := checkedSmall
theorem b469 : Ban 12 4 v281 := checkedSmall
theorem b470 : Ban 12 4 v282 := checkedSmall
theorem b471 : Ban 12 4 v283 := checkedSmall
theorem b472 : Ban 12 4 v284 := checkedSmall
theorem b473 : Ban 12 4 v285 := checkedSmall
theorem b474 : Ban 12 4 v286 := checkedSmall
theorem b475 : Ban 12 4 v287 := checkedSmall
theorem b476 : Ban 12 4 v288 := checkedSmall
theorem b477 : Ban 12 4 v289 := checkedSmall
theorem b478 : Ban 12 4 v290 := checkedSmall
theorem b479 : Ban 12 4 v291 := checkedSmall
theorem b480 : Ban 12 4 v292 := checkedSmall
theorem b481 : Ban 12 4 v293 := checkedSmall
theorem b482 : Ban 12 4 v294 := checkedSmall
theorem b483 : Ban 12 4 v295 := checkedSmall
theorem b484 : Ban 12 4 v296 := checkedSmall
theorem b485 : Ban 12 4 v297 := checkedSmall
theorem b486 : Ban 12 4 v298 := checkedSmall
theorem b487 : Ban 12 4 v299 := checkedSmall
theorem b488 : Ban 12 4 v300 := checkedSmall
theorem b489 : Ban 12 4 v301 := checkedSmall
theorem b490 : Ban 12 4 v302 := checkedSmall
theorem b491 : Ban 12 4 v303 := checkedSmall
theorem b492 : Ban 12 4 v304 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b493 : Ban 12 5 v280 := viaBranch (ws := [v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304]) (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b494 : Ban 12 5 v305 := checkedSmall
theorem b495 : Ban 12 5 v306 := checkedSmall
theorem b496 : Ban 12 5 v307 := checkedSmall
theorem b497 : Ban 12 5 v308 := checkedSmall
theorem b498 : Ban 12 5 v309 := checkedSmall
theorem b499 : Ban 12 5 v310 := checkedSmall
theorem b500 : Ban 12 5 v311 := checkedSmall
theorem b501 : Ban 12 5 v312 := checkedSmall
theorem b502 : Ban 12 5 v313 := checkedSmall
theorem b503 : Ban 12 5 v314 := viaPerm map29_2 map29_2 b462 (by decide +kernel) (by decide +kernel)
theorem b504 : Ban 12 5 v315 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b505 : Ban 12 6 v64 := viaBranch (ws := [v33,v237,v238,v239,v240,v241,v31,v242,v63,v58,v243,v244,v80,v245,v85,v246,v247,v248,v16,v249,v82,v250,v251,v252,v253,v254,v255,v256,v257,v275,v276,v277,v278,v279,v280,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315]) (consBan b30 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b28 (consBan b428 (consBan b429 (consBan b78 (consBan b430 (consBan b431 (consBan b79 (consBan b432 (consBan b88 (consBan b433 (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b85 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 12 6 v64 := viaSub (ws := [v2,v64]) (consBan b89 (consBan b505 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b1252 : Ban 12 6 v64 := bySubset w10
theorem b1253 : Ban 12 6 v66 := viaPerm map27_2 map27_2 b1252 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w20 : Wide 12 6 v66 := viaSub (ws := [v2,v66]) (consBan b188 (consBan b1253 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b90 : Ban 29 8 v1 := smallByCut p31_29 w20
theorem b91 : Ban 29 7 v87 := smallByCut p31_29 w20
theorem b94 : Ban 12 5 v2 := bySubset w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 12 5 v2 := viaSub (ws := [v2]) (consBan b94 (nilBan 12 5)) (by decide) (by decide +kernel)
theorem b96 : Ban 12 5 v2 := bySubset w1
theorem solidb33 : Wide 12 4 v37 := solid b33
theorem b132 : Ban 12 4 v37 := bySubset solidb33
theorem solidb132 : Wide 12 4 v37 := solid b132
theorem b366 : Ban 12 4 v37 := bySubset solidb132
theorem solidb34 : Wide 12 4 v38 := solid b34
theorem b133 : Ban 12 4 v38 := bySubset solidb34
theorem solidb133 : Wide 12 4 v38 := solid b133
theorem b367 : Ban 12 4 v38 := bySubset solidb133
theorem solidb35 : Wide 12 4 v39 := solid b35
theorem b134 : Ban 12 4 v39 := bySubset solidb35
theorem solidb134 : Wide 12 4 v39 := solid b134
theorem b368 : Ban 12 4 v39 := bySubset solidb134
theorem solidb36 : Wide 12 4 v40 := solid b36
theorem b135 : Ban 12 4 v40 := bySubset solidb36
theorem solidb135 : Wide 12 4 v40 := solid b135
theorem b369 : Ban 12 4 v40 := bySubset solidb135
theorem solidb37 : Wide 12 4 v41 := solid b37
theorem b136 : Ban 12 4 v41 := bySubset solidb37
theorem solidb136 : Wide 12 4 v41 := solid b136
theorem b370 : Ban 12 4 v41 := bySubset solidb136
theorem b371 : Ban 12 4 v42 := checkedSmall
theorem b372 : Ban 12 4 v43 := checkedSmall
theorem solidb40 : Wide 12 4 v44 := solid b40
theorem b139 : Ban 12 4 v44 := bySubset solidb40
theorem solidb139 : Wide 12 4 v44 := solid b139
theorem b373 : Ban 12 4 v44 := bySubset solidb139
theorem solidb41 : Wide 12 4 v45 := solid b41
theorem b140 : Ban 12 4 v45 := bySubset solidb41
theorem solidb140 : Wide 12 4 v45 := solid b140
theorem b374 : Ban 12 4 v45 := bySubset solidb140
theorem b375 : Ban 12 4 v46 := checkedSmall
theorem solidb43 : Wide 12 4 v47 := solid b43
theorem b142 : Ban 12 4 v47 := bySubset solidb43
theorem solidb142 : Wide 12 4 v47 := solid b142
theorem b376 : Ban 12 4 v47 := bySubset solidb142
theorem solidb17 : Wide 12 4 v22 := solid b17
theorem b116 : Ban 12 4 v22 := bySubset solidb17
theorem solidb116 : Wide 12 4 v22 := solid b116
theorem b350 : Ban 12 4 v22 := bySubset solidb116
theorem b377 : Ban 12 4 v48 := checkedSmall
theorem b378 : Ban 12 4 v49 := checkedSmall
theorem b338 : Ban 12 4 v10 := checkedSmall
theorem b379 : Ban 12 4 v50 := checkedSmall
theorem solidb47 : Wide 12 4 v51 := solid b47
theorem b146 : Ban 12 4 v51 := bySubset solidb47
theorem solidb146 : Wide 12 4 v51 := solid b146
theorem b380 : Ban 12 4 v51 := bySubset solidb146
theorem solidb48 : Wide 12 4 v52 := solid b48
theorem b147 : Ban 12 4 v52 := bySubset solidb48
theorem solidb147 : Wide 12 4 v52 := solid b147
theorem b381 : Ban 12 4 v52 := bySubset solidb147
theorem b382 : Ban 12 4 v53 := checkedSmall
theorem b383 : Ban 12 4 v54 := checkedSmall
theorem b384 : Ban 12 4 v55 := checkedSmall
theorem b385 : Ban 12 4 v56 := checkedSmall
theorem b386 : Ban 12 4 v57 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b387 : Ban 12 5 v36 := viaBranch (ws := [v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v22,v48,v49,v10,v50,v51,v52,v53,v54,v55,v56,v57]) (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b350 (consBan b377 (consBan b378 (consBan b338 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w60 : Wide 12 5 v36 := viaSub (ws := [v2,v36]) (consBan b96 (consBan b387 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b92 : Ban 29 7 v88 := smallByCut p31_30 w60
theorem b93 : Ban 29 7 v89 := smallByCut p31_29 w60
theorem b95 : Ban 29 7 v90 := smallByCut p31_29 w60
theorem b98 : Ban 29 7 v91 := smallByCut p31_30 w60
theorem b190 : Ban 29 7 v93 := smallByCut p31_30 w60
theorem b191 : Ban 29 7 v95 := smallByCut p31_29 w60
theorem b192 : Ban 29 7 v96 := smallByCut p31_29 w60
theorem b194 : Ban 29 7 v97 := smallByCut p31_30 w60
theorem b536 : Ban 12 4 v347 := checkedSmall
theorem b537 : Ban 12 4 v348 := checkedSmall
theorem b538 : Ban 12 4 v349 := checkedSmall
theorem b539 : Ban 12 4 v350 := checkedSmall
theorem b540 : Ban 12 4 v351 := checkedSmall
theorem b541 : Ban 12 4 v352 := checkedSmall
theorem b542 : Ban 12 4 v353 := checkedSmall
theorem b543 : Ban 12 4 v354 := checkedSmall
theorem b544 : Ban 12 4 v355 := checkedSmall
theorem b545 : Ban 12 4 v356 := checkedSmall
theorem b546 : Ban 12 4 v357 := checkedSmall
theorem b547 : Ban 12 4 v358 := checkedSmall
theorem b548 : Ban 12 4 v359 := checkedSmall
theorem b549 : Ban 12 4 v360 := checkedSmall
theorem b550 : Ban 12 4 v361 := checkedSmall
theorem b551 : Ban 12 4 v362 := checkedSmall
theorem b552 : Ban 12 4 v363 := checkedSmall
theorem b553 : Ban 12 4 v364 := checkedSmall
theorem b554 : Ban 12 4 v365 := checkedSmall
theorem b555 : Ban 12 4 v366 := checkedSmall
theorem b556 : Ban 12 4 v367 := checkedSmall
theorem b557 : Ban 12 4 v368 := checkedSmall
theorem b558 : Ban 12 4 v369 := checkedSmall
theorem b559 : Ban 12 4 v370 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b560 : Ban 12 5 v346 := viaBranch (ws := [v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370]) (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b542 (consBan b543 (consBan b544 (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (consBan b553 (consBan b554 (consBan b555 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b561 : Ban 12 5 v371 := checkedSmall
theorem b562 : Ban 12 5 v372 := checkedSmall
theorem b563 : Ban 12 5 v373 := checkedSmall
theorem b564 : Ban 12 5 v374 := checkedSmall
theorem b565 : Ban 12 5 v375 := checkedSmall
theorem b566 : Ban 12 5 v376 := checkedSmall
theorem b567 : Ban 12 5 v377 := checkedSmall
theorem b568 : Ban 12 5 v378 := checkedSmall
theorem b569 : Ban 12 5 v379 := checkedSmall
theorem b570 : Ban 12 5 v380 := checkedSmall
theorem b571 : Ban 12 5 v381 := checkedSmall
theorem b572 : Ban 12 5 v382 := checkedSmall
theorem b573 : Ban 12 5 v383 := checkedSmall
theorem b574 : Ban 12 5 v384 := checkedSmall
theorem b575 : Ban 12 5 v385 := checkedSmall
theorem b576 : Ban 12 4 v386 := checkedSmall
theorem b577 : Ban 12 4 v387 := checkedSmall
theorem b578 : Ban 12 4 v388 := checkedSmall
theorem solidb443 : Wide 12 5 v255 := solid b443
theorem b579 : Ban 12 4 v255 := bySubset solidb443
theorem b580 : Ban 12 4 v389 := checkedSmall
theorem b581 : Ban 12 4 v390 := checkedSmall
theorem b582 : Ban 12 4 v391 := checkedSmall
theorem b583 : Ban 12 4 v392 := checkedSmall
theorem b584 : Ban 12 4 v393 := checkedSmall
theorem b585 : Ban 12 4 v394 := checkedSmall
theorem b586 : Ban 12 4 v395 := checkedSmall
theorem b587 : Ban 12 4 v396 := checkedSmall
theorem b588 : Ban 12 4 v397 := checkedSmall
theorem b589 : Ban 12 4 v398 := checkedSmall
theorem b590 : Ban 12 4 v399 := checkedSmall
theorem b591 : Ban 12 4 v400 := checkedSmall
theorem b592 : Ban 12 4 v401 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b593 : Ban 12 5 v72 := viaBranch (ws := [v386,v387,v388,v255,v389,v390,v391,v392,v393,v394,v73,v395,v74,v75,v396,v397,v65,v398,v399,v400,v401]) (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (consBan b71 (consBan b586 (consBan b72 (consBan b73 (consBan b587 (consBan b588 (consBan b63 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b594 : Ban 12 5 v70 := viaPerm map29_2 map29_2 b593 (by decide +kernel) (by decide +kernel)
theorem b595 : Ban 12 5 v402 := checkedSmall
theorem b596 : Ban 12 5 v403 := checkedSmall
theorem b597 : Ban 12 5 v404 := checkedSmall
theorem b598 : Ban 12 5 v405 := checkedSmall
theorem b599 : Ban 12 5 v406 := checkedSmall
theorem b600 : Ban 12 5 v407 := checkedSmall
theorem b601 : Ban 12 5 v408 := checkedSmall
theorem b602 : Ban 12 4 v409 := checkedSmall
theorem b603 : Ban 12 4 v410 := checkedSmall
theorem b604 : Ban 12 4 v411 := checkedSmall
theorem b605 : Ban 12 4 v412 := checkedSmall
theorem b606 : Ban 12 4 v413 := checkedSmall
theorem b607 : Ban 12 4 v414 := checkedSmall
theorem b608 : Ban 12 4 v415 := checkedSmall
theorem solidb600 : Wide 12 5 v407 := solid b600
theorem b609 : Ban 12 4 v407 := bySubset solidb600
theorem b610 : Ban 12 4 v416 := checkedSmall
theorem b611 : Ban 12 4 v417 := checkedSmall
theorem b612 : Ban 12 4 v418 := checkedSmall
theorem b613 : Ban 12 4 v419 := checkedSmall
theorem b614 : Ban 12 4 v420 := checkedSmall
theorem b615 : Ban 12 4 v421 := checkedSmall
theorem b616 : Ban 12 4 v422 := checkedSmall
theorem b617 : Ban 12 4 v423 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b618 : Ban 12 5 v20 := viaBranch (ws := [v409,v410,v411,v412,v413,v414,v415,v407,v21,v416,v417,v418,v419,v267,v12,v420,v26,v421,v28,v422,v423]) (consBan b602 (consBan b603 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b16 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b454 (consBan b7 (consBan b614 (consBan b21 (consBan b615 (consBan b23 (consBan b616 (consBan b617 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b619 : Ban 12 5 v424 := checkedSmall
theorem b620 : Ban 12 5 v425 := checkedSmall
theorem b621 : Ban 12 5 v426 := checkedSmall
theorem b622 : Ban 12 5 v427 := checkedSmall
theorem b623 : Ban 12 5 v428 := checkedSmall
theorem b624 : Ban 12 5 v429 := checkedSmall
theorem b625 : Ban 12 5 v49 := checkedSmall
theorem b626 : Ban 12 5 v430 := checkedSmall
theorem b627 : Ban 12 5 v431 := checkedSmall
theorem b628 : Ban 12 5 v432 := checkedSmall
theorem b629 : Ban 12 5 v433 := checkedSmall
theorem b630 : Ban 12 5 v434 := checkedSmall
theorem b631 : Ban 12 5 v435 := checkedSmall
theorem b632 : Ban 12 5 v436 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b633 : Ban 12 6 v4 := viaBranch (ws := [v346,v371,v372,v373,v374,v375,v376,v377,v6,v378,v379,v380,v381,v382,v383,v384,v385,v5,v70,v402,v403,v252,v404,v405,v406,v407,v408,v20,v424,v425,v426,v427,v80,v64,v428,v429,v13,v49,v430,v431,v432,v81,v433,v434,v435,v436]) (consBan b560 (consBan b561 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b27 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b2 (consBan b594 (consBan b595 (consBan b596 (consBan b440 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b601 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b79 (consBan b80 (consBan b623 (consBan b624 (consBan b82 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b84 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w12 : Wide 12 6 v4 := viaSub (ws := [v2,v4]) (consBan b89 (consBan b633 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b935 : Ban 12 6 v4 := bySubset w12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w16 : Wide 12 6 v4 := viaSub (ws := [v2,v4]) (consBan b188 (consBan b935 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b1060 : Ban 12 4 v2 := bySubset w16
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 12 5 v80 := viaSub (ws := [v2,v80]) (consBan b94 (consBan b79 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b244 : Ban 12 5 v80 := bySubset w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 5 v80 := viaSub (ws := [v2,v80]) (consBan b96 (consBan b244 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b248 : Ban 12 5 v2 := bySubset w5
theorem b178 : Ban 12 5 v80 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 12 5 v80 := viaSub (ws := [v2,v80]) (consBan b248 (consBan b178 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b1061 : Ban 12 4 v80 := bySubset w6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w17 : Wide 12 4 v80 := viaSub (ws := [v2,v80]) (consBan b1060 (consBan b1061 (nilBan 12 4))) (by decide) (by decide +kernel)
theorem b195 : Ban 29 6 v101 := smallByCut p31_29 w17
theorem b196 : Ban 29 5 v103 := smallByCut p31_27 w6
theorem b197 : Ban 29 5 v104 := smallByCut p31_27 w6
theorem b198 : Ban 29 5 v105 := smallByCut p31_27 w17
theorem b199 : Ban 29 5 v106 := checkedSmall
theorem b200 : Ban 29 5 v107 := smallByCut p31_29 w6
theorem b201 : Ban 29 5 v108 := smallByCut p31_29 w6
theorem b202 : Ban 29 5 v109 := smallByCut p31_29 w17
theorem b203 : Ban 29 5 v110 := checkedSmall
theorem b204 : Ban 29 5 v111 := smallByCut p31_30 w6
theorem b205 : Ban 29 5 v112 := smallByCut p31_30 w6
theorem b206 : Ban 29 5 v113 := smallByCut p31_30 w17
theorem b207 : Ban 29 5 v114 := checkedSmall
theorem b208 : Ban 29 5 v115 := checkedSmall
theorem b209 : Ban 29 5 v116 := checkedSmall
theorem b210 : Ban 29 5 v117 := checkedSmall
theorem b211 : Ban 29 5 v118 := checkedSmall
theorem b212 : Ban 29 5 v119 := smallByCut p31_27 w60
theorem b213 : Ban 29 5 v120 := smallByCut p31_29 w60
theorem b214 : Ban 29 5 v121 := smallByCut p31_27 w60
theorem b215 : Ban 29 5 v122 := smallByCut p31_27 w6
theorem b216 : Ban 29 5 v123 := smallByCut p31_27 w6
theorem b262 : Ban 6 3 v167 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 6 3 v167 := viaSub (ws := [v167]) (consBan b262 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1110 : Ban 6 3 v167 := bySubset w7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w18 : Wide 6 3 v167 := viaSub (ws := [v167]) (consBan b1110 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1770 : Ban 6 3 v167 := bySubset w18
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w26 : Wide 6 3 v167 := viaSub (ws := [v167]) (consBan b1770 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1970 : Ban 6 3 v167 := bySubset w26
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w32 : Wide 6 3 v167 := viaSub (ws := [v167]) (consBan b1970 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b2666 : Ban 6 3 v167 := bySubset w32
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w42 : Wide 6 3 v167 := viaSub (ws := [v167]) (consBan b2666 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b217 : Ban 29 5 v124 := smallByCut p31_13 w42
theorem b218 : Ban 29 5 v125 := smallByCut p31_29 w17
theorem b219 : Ban 29 5 v126 := smallByCut p31_19 w42
theorem b220 : Ban 29 5 v127 := smallByCut p31_27 w17
theorem b221 : Ban 29 5 v128 := smallByCut p31_27 w60
theorem b222 : Ban 29 5 v129 := smallByCut p31_30 w60
theorem b223 : Ban 29 5 v130 := smallByCut p31_27 w60
theorem b224 : Ban 29 5 v131 := smallByCut p31_27 w6
theorem b225 : Ban 29 5 v132 := smallByCut p31_14 w42
theorem b226 : Ban 29 5 v133 := smallByCut p31_30 w17
theorem b227 : Ban 29 5 v134 := smallByCut p31_27 w6
theorem b228 : Ban 29 5 v135 := smallByCut p31_27 w6
theorem b229 : Ban 29 5 v136 := checkedSmall
theorem b230 : Ban 29 5 v137 := smallByCut p31_27 w17
theorem b231 : Ban 29 5 v138 := smallByCut p31_29 w60
theorem b232 : Ban 29 5 v139 := smallByCut p31_30 w60
theorem b233 : Ban 29 5 v140 := smallByCut p31_29 w60
theorem b234 : Ban 29 5 v141 := smallByCut p31_29 w6
theorem b235 : Ban 29 5 v142 := smallByCut p31_29 w6
theorem b236 : Ban 29 5 v143 := smallByCut p31_29 w6
theorem b237 : Ban 29 5 v144 := checkedSmall
theorem b238 : Ban 29 5 v145 := smallByCut p31_29 w17
theorem b239 : Ban 29 5 v146 := smallByCut p31_30 w6
theorem b240 : Ban 29 5 v147 := smallByCut p31_30 w6
theorem b241 : Ban 29 5 v148 := checkedSmall
theorem b242 : Ban 29 5 v149 := smallByCut p31_30 w17
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b243 : Ban 29 6 v102 := viaBranch (ws := [v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149]) (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (nilBan 29 5)))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b245 : Ban 29 6 v150 := smallByCut p31_30 w6
theorem b246 : Ban 29 6 v151 := smallByCut p31_29 w6
theorem b247 : Ban 29 6 v152 := smallByCut p31_29 w6
theorem b250 : Ban 29 6 v153 := smallByCut p31_27 w10
theorem b251 : Ban 29 6 v155 := smallByCut p31_30 w17
theorem b252 : Ban 29 6 v156 := smallByCut p31_27 w20
theorem b253 : Ban 29 6 v157 := smallByCut p31_27 w20
theorem b254 : Ban 29 6 v158 := smallByCut p31_30 w17
theorem b255 : Ban 29 6 v159 := smallByCut p31_27 w16
theorem b256 : Ban 29 6 v160 := smallByCut p31_30 w17
theorem b296 : Ban 12 4 v202 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 4 v202 := viaSub (ws := [v202]) (consBan b296 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b257 : Ban 29 6 v161 := smallByCut p31_23 w8
theorem b258 : Ban 29 6 v162 := smallByCut p31_27 w60
theorem b259 : Ban 29 6 v163 := smallByCut p31_27 w60
theorem b260 : Ban 29 6 v164 := smallByCut p31_27 w60
theorem b261 : Ban 29 6 v165 := smallByCut p31_30 w60
theorem b263 : Ban 29 6 v166 := smallByCut p31_14 w42
theorem b264 : Ban 29 6 v168 := smallByCut p31_30 w6
theorem b265 : Ban 29 6 v169 := smallByCut p31_30 w17
theorem b266 : Ban 29 6 v170 := smallByCut p31_29 w6
theorem b267 : Ban 29 6 v171 := smallByCut p31_14 w42
theorem b268 : Ban 29 6 v172 := smallByCut p31_30 w17
theorem b269 : Ban 29 6 v173 := smallByCut p31_27 w20
theorem b270 : Ban 29 6 v174 := smallByCut p31_27 w20
theorem b271 : Ban 29 6 v175 := smallByCut p31_30 w17
theorem b272 : Ban 29 6 v176 := smallByCut p31_30 w6
theorem b273 : Ban 29 6 v177 := smallByCut p31_30 w17
theorem b274 : Ban 29 6 v178 := smallByCut p31_15 w8
theorem b275 : Ban 29 6 v179 := smallByCut p31_29 w17
theorem b276 : Ban 29 6 v180 := smallByCut p31_29 w6
theorem b277 : Ban 29 6 v181 := smallByCut p31_29 w17
theorem b278 : Ban 29 6 v182 := smallByCut p31_23 w8
theorem b279 : Ban 29 6 v183 := smallByCut p31_29 w60
theorem b280 : Ban 29 6 v184 := smallByCut p31_13 w42
theorem b281 : Ban 29 6 v185 := smallByCut p31_29 w6
theorem b282 : Ban 29 6 v186 := smallByCut p31_29 w17
theorem b283 : Ban 29 6 v187 := smallByCut p31_13 w42
theorem b284 : Ban 29 6 v188 := smallByCut p31_27 w20
theorem b285 : Ban 29 6 v189 := smallByCut p31_27 w10
theorem b286 : Ban 29 6 v190 := smallByCut p31_27 w10
theorem b287 : Ban 29 6 v191 := smallByCut p31_27 w60
theorem b288 : Ban 29 6 v192 := smallByCut p31_27 w60
theorem b289 : Ban 29 6 v193 := smallByCut p31_27 w60
theorem b290 : Ban 29 6 v194 := smallByCut p31_29 w17
theorem b291 : Ban 29 6 v195 := smallByCut p31_29 w6
theorem b292 : Ban 29 6 v196 := smallByCut p31_29 w17
theorem b293 : Ban 29 6 v197 := smallByCut p31_15 w8
theorem b294 : Ban 29 6 v198 := smallByCut p31_23 w8
theorem b295 : Ban 29 6 v199 := smallByCut p31_27 w16
theorem b298 : Ban 29 6 v200 := smallByCut p31_29 w17
theorem b299 : Ban 29 6 v203 := checkedSmall
theorem b300 : Ban 29 6 v204 := smallByCut p31_23 w8
theorem b301 : Ban 29 6 v205 := smallByCut p31_30 w6
theorem b302 : Ban 29 6 v206 := smallByCut p31_30 w17
theorem b303 : Ban 29 6 v207 := checkedSmall
theorem b304 : Ban 29 6 v208 := smallByCut p31_15 w8
theorem b305 : Ban 29 5 v210 := smallByCut p31_14 w42
theorem b306 : Ban 29 5 v211 := smallByCut p31_30 w17
theorem b1874 : Ban 12 4 v33 := checkedSmall
theorem b1875 : Ban 12 4 v1399 := checkedSmall
theorem b1876 : Ban 12 4 v1400 := checkedSmall
theorem b1877 : Ban 12 4 v1401 := checkedSmall
theorem b1878 : Ban 12 4 v85 := checkedSmall
theorem b1879 : Ban 12 4 v1402 := checkedSmall
theorem b1880 : Ban 12 4 v31 := checkedSmall
theorem b1881 : Ban 12 4 v1403 := checkedSmall
theorem b1882 : Ban 12 4 v1404 := checkedSmall
theorem b1883 : Ban 12 4 v1405 := checkedSmall
theorem b1884 : Ban 12 4 v1406 := checkedSmall
theorem b149 : Ban 12 4 v54 := checkedSmall
theorem b1885 : Ban 12 4 v1407 := checkedSmall
theorem b1886 : Ban 12 4 v1408 := checkedSmall
theorem b1887 : Ban 12 4 v1409 := checkedSmall
theorem b1888 : Ban 12 4 v1410 := checkedSmall
theorem b1889 : Ban 12 4 v82 := checkedSmall
theorem b1890 : Ban 12 4 v1411 := checkedSmall
theorem b1891 : Ban 12 4 v1412 := checkedSmall
theorem b1892 : Ban 12 4 v1413 := checkedSmall
theorem b1893 : Ban 12 4 v1414 := checkedSmall
theorem b1894 : Ban 12 4 v1415 := checkedSmall
theorem b1895 : Ban 12 4 v1416 := checkedSmall
theorem b1896 : Ban 12 4 v1417 := checkedSmall
theorem b1897 : Ban 12 4 v1418 := checkedSmall
theorem b1898 : Ban 12 4 v1419 := checkedSmall
theorem b1899 : Ban 12 4 v1420 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1900 : Ban 12 5 v56 := viaBranch (ws := [v33,v1399,v1400,v1401,v85,v1402,v31,v1403,v1404,v1405,v1406,v54,v1407,v1408,v1409,v1410,v82,v1411,v1412,v1413,v1414,v1415,v1416,v1417,v1418,v1419,v1420]) (consBan b1874 (consBan b1875 (consBan b1876 (consBan b1877 (consBan b1878 (consBan b1879 (consBan b1880 (consBan b1881 (consBan b1882 (consBan b1883 (consBan b1884 (consBan b149 (consBan b1885 (consBan b1886 (consBan b1887 (consBan b1888 (consBan b1889 (consBan b1890 (consBan b1891 (consBan b1892 (consBan b1893 (consBan b1894 (consBan b1895 (consBan b1896 (consBan b1897 (consBan b1898 (consBan b1899 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1901 : Ban 12 5 v50 := viaPerm map27_2 map27_2 b1900 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w30 : Wide 12 5 v50 := viaSub (ws := [v2,v50]) (consBan b248 (consBan b1901 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b307 : Ban 29 5 v212 := smallByCut p31_27 w30
theorem b308 : Ban 29 5 v213 := smallByCut p31_13 w42
theorem b309 : Ban 29 5 v214 := smallByCut p31_29 w17
theorem b310 : Ban 29 5 v215 := checkedSmall
theorem b311 : Ban 29 5 v216 := smallByCut p31_15 w8
theorem b312 : Ban 29 5 v217 := smallByCut p31_13 w42
theorem b313 : Ban 29 5 v218 := smallByCut p31_13 w42
theorem b314 : Ban 29 5 v219 := smallByCut p31_13 w42
theorem b315 : Ban 29 5 v220 := smallByCut p31_14 w42
theorem b316 : Ban 29 5 v221 := smallByCut p31_14 w42
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b317 : Ban 29 6 v209 := viaBranch (ws := [v116,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221]) (consBan b209 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (nilBan 29 5)))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b318 : Ban 29 6 v222 := smallByCut p31_23 w8
theorem b319 : Ban 29 6 v223 := smallByCut p31_15 w8
theorem b320 : Ban 29 6 v224 := smallByCut p31_29 w60
theorem b321 : Ban 29 6 v225 := smallByCut p31_30 w60
theorem b322 : Ban 29 6 v226 := smallByCut p31_29 w60
theorem b323 : Ban 29 6 v227 := smallByCut p31_29 w6
theorem b324 : Ban 29 6 v228 := smallByCut p31_15 w8
theorem b325 : Ban 29 6 v229 := smallByCut p31_29 w6
theorem b326 : Ban 29 6 v230 := checkedSmall
theorem b297 : Ban 29 6 v201 := smallByCut p31_29 w17
theorem b327 : Ban 29 6 v231 := smallByCut p31_15 w8
theorem b328 : Ban 29 6 v232 := smallByCut p31_30 w6
theorem b329 : Ban 29 6 v233 := checkedSmall
theorem b330 : Ban 29 6 v234 := smallByCut p31_30 w17
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b331 : Ban 29 7 v100 := viaBranch (ws := [v101,v102,v150,v151,v152,v153,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v203,v204,v205,v206,v207,v208,v209,v222,v223,v224,v225,v226,v227,v228,v229,v230,v201,v231,v232,v233,v234]) (consBan b195 (consBan b243 (consBan b245 (consBan b246 (consBan b247 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b297 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (nilBan 29 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b332 : Ban 29 7 v99 := viaPerm map31_6 map31_8 b331 (by decide +kernel) (by decide +kernel)
theorem b422 : Ban 29 7 v235 := smallByCut p31_30 w20
theorem b506 : Ban 29 7 v236 := smallByCut p31_30 w20
theorem b507 : Ban 29 7 v316 := smallByCut p31_30 w60
theorem b509 : Ban 29 7 v317 := smallByCut p31_29 w20
theorem b535 : Ban 29 7 v319 := smallByCut p31_30 w60
theorem b634 : Ban 29 7 v345 := smallByCut p31_30 w20
theorem b636 : Ban 29 7 v437 := smallByCut p31_30 w60
theorem b640 : Ban 12 5 v444 := smallByCut p15_13 w42
theorem b510 : Ban 12 5 v320 := checkedSmall
theorem b511 : Ban 12 4 v322 := smallByCut p15_13 w42
theorem b512 : Ban 12 4 v323 := smallByCut p15_13 w42
theorem b513 : Ban 12 4 v324 := smallByCut p15_13 w42
theorem b514 : Ban 12 4 v325 := smallByCut p15_14 w42
theorem b515 : Ban 12 4 v326 := smallByCut p15_13 w42
theorem b516 : Ban 12 4 v327 := smallByCut p15_13 w42
theorem b517 : Ban 12 4 v328 := checkedSmall
theorem b518 : Ban 12 4 v329 := smallByCut p15_14 w42
theorem b519 : Ban 12 4 v330 := smallByCut p15_14 w42
theorem b520 : Ban 12 4 v331 := checkedSmall
theorem b521 : Ban 12 4 v332 := smallByCut p15_13 w42
theorem b522 : Ban 12 4 v333 := checkedSmall
theorem b523 : Ban 12 4 v334 := smallByCut p15_13 w42
theorem b524 : Ban 12 4 v335 := smallByCut p15_13 w42
theorem b525 : Ban 12 4 v336 := checkedSmall
theorem b526 : Ban 12 4 v337 := checkedSmall
theorem b527 : Ban 12 4 v338 := checkedSmall
theorem b528 : Ban 12 4 v339 := checkedSmall
theorem b529 : Ban 12 4 v340 := checkedSmall
theorem b530 : Ban 12 4 v341 := checkedSmall
theorem b531 : Ban 12 4 v342 := checkedSmall
theorem b532 : Ban 12 4 v343 := checkedSmall
theorem b533 : Ban 12 4 v344 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b534 : Ban 12 5 v321 := viaBranch (ws := [v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344]) (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w11 : Wide 12 5 v321 := viaSub (ws := [v320,v321]) (consBan b510 (consBan b534 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b664 : Ban 12 5 v321 := bySubset w11
theorem b665 : Ban 12 5 v332 := smallByCut p15_14 w42
theorem b666 : Ban 12 5 v327 := smallByCut p15_13 w42
theorem b667 : Ban 12 5 v445 := smallByCut p15_14 w42
theorem b637 : Ban 12 5 v441 := viaPerm map23_1 map23_1 b534 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w13 : Wide 12 5 v441 := viaSub (ws := [v320,v441]) (consBan b510 (consBan b637 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b668 : Ban 12 5 v441 := bySubset w13
theorem b669 : Ban 12 5 v446 := smallByCut p15_14 w42
theorem b670 : Ban 12 5 v447 := checkedSmall
theorem b671 : Ban 12 5 v448 := smallByCut p15_14 w42
theorem b672 : Ban 12 5 v449 := checkedSmall
theorem b673 : Ban 12 5 v450 := smallByCut p15_14 w42
theorem b674 : Ban 12 4 v453 := smallByCut p15_14 w42
theorem b675 : Ban 12 4 v454 := smallByCut p15_13 w42
theorem b676 : Ban 12 4 v455 := smallByCut p15_14 w42
theorem b677 : Ban 12 4 v456 := smallByCut p15_13 w42
theorem b678 : Ban 12 4 v457 := checkedSmall
theorem b679 : Ban 12 4 v458 := checkedSmall
theorem b680 : Ban 12 4 v459 := checkedSmall
theorem b681 : Ban 12 4 v460 := checkedSmall
theorem b682 : Ban 12 4 v461 := smallByCut p15_13 w42
theorem b683 : Ban 12 4 v462 := smallByCut p15_14 w42
theorem b684 : Ban 12 4 v463 := smallByCut p15_13 w42
theorem b685 : Ban 12 4 v464 := smallByCut p15_14 w42
theorem b686 : Ban 12 4 v465 := checkedSmall
theorem b687 : Ban 12 4 v466 := checkedSmall
theorem b688 : Ban 12 4 v467 := checkedSmall
theorem b689 : Ban 12 4 v468 := checkedSmall
theorem b690 : Ban 12 4 v469 := checkedSmall
theorem b691 : Ban 12 4 v470 := checkedSmall
theorem b692 : Ban 12 4 v471 := checkedSmall
theorem b693 : Ban 12 4 v472 := checkedSmall
theorem b694 : Ban 12 4 v473 := checkedSmall
theorem b695 : Ban 12 4 v474 := checkedSmall
theorem b696 : Ban 12 4 v475 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b697 : Ban 12 5 v452 := viaBranch (ws := [v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475]) (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (consBan b681 (consBan b682 (consBan b683 (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b698 : Ban 12 5 v451 := viaPerm map15_3 map15_4 b697 (by decide +kernel) (by decide +kernel)
theorem b699 : Ban 12 5 v476 := smallByCut p15_13 w42
theorem b700 : Ban 12 5 v477 := viaPerm map15_3 map15_4 b664 (by decide +kernel) (by decide +kernel)
theorem b701 : Ban 12 5 v478 := smallByCut p15_13 w42
theorem b702 : Ban 12 5 v479 := checkedSmall
theorem b703 : Ban 12 5 v480 := smallByCut p15_13 w42
theorem b704 : Ban 12 5 v481 := checkedSmall
theorem b705 : Ban 12 5 v482 := smallByCut p15_13 w42
theorem b706 : Ban 12 5 v483 := viaPerm map15_1 map15_1 b697 (by decide +kernel) (by decide +kernel)
theorem b707 : Ban 12 5 v472 := checkedSmall
theorem b708 : Ban 12 5 v470 := checkedSmall
theorem b709 : Ban 12 5 v484 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b710 : Ban 12 6 v320 := viaBranch (ws := [v444,v321,v332,v327,v445,v441,v446,v447,v448,v449,v450,v451,v476,v477,v478,v479,v480,v481,v482,v483,v472,v470,v484,v452]) (consBan b640 (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b670 (consBan b671 (consBan b672 (consBan b673 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b697 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1576 : Ban 12 5 v1117 := checkedSmall
theorem b1577 : Ban 12 5 v1118 := checkedSmall
theorem b1578 : Ban 12 5 v1119 := checkedSmall
theorem b1579 : Ban 12 5 v1120 := checkedSmall
theorem b1580 : Ban 12 5 v1121 := checkedSmall
theorem b1581 : Ban 12 5 v1122 := checkedSmall
theorem b1582 : Ban 12 5 v1123 := checkedSmall
theorem b1583 : Ban 12 5 v1124 := checkedSmall
theorem b1584 : Ban 12 5 v1125 := checkedSmall
theorem b1585 : Ban 12 5 v1126 := checkedSmall
theorem b1586 : Ban 12 5 v1127 := checkedSmall
theorem b1587 : Ban 12 5 v1128 := checkedSmall
theorem b1588 : Ban 12 4 v1130 := checkedSmall
theorem b1589 : Ban 12 4 v1131 := checkedSmall
theorem b1590 : Ban 12 4 v1132 := checkedSmall
theorem b1591 : Ban 12 4 v1133 := checkedSmall
theorem b1592 : Ban 12 4 v1134 := checkedSmall
theorem b1593 : Ban 12 4 v1135 := checkedSmall
theorem b1594 : Ban 12 4 v1136 := checkedSmall
theorem b1595 : Ban 12 4 v1137 := checkedSmall
theorem b1596 : Ban 12 4 v1138 := checkedSmall
theorem b1332 : Ban 12 4 v896 := checkedSmall
theorem b1321 : Ban 12 4 v885 := checkedSmall
theorem b1322 : Ban 12 4 v886 := checkedSmall
theorem b1323 : Ban 12 4 v887 := checkedSmall
theorem b1324 : Ban 12 4 v888 := checkedSmall
theorem b1325 : Ban 12 4 v889 := checkedSmall
theorem b1326 : Ban 12 4 v890 := checkedSmall
theorem b1327 : Ban 12 4 v891 := checkedSmall
theorem b1328 : Ban 12 4 v892 := checkedSmall
theorem b1329 : Ban 12 4 v893 := checkedSmall
theorem b1330 : Ban 12 4 v894 := checkedSmall
theorem b1331 : Ban 12 4 v895 := checkedSmall
theorem b1333 : Ban 12 4 v897 := checkedSmall
theorem b1334 : Ban 12 4 v898 := checkedSmall
theorem b1335 : Ban 12 4 v899 := checkedSmall
theorem b1336 : Ban 12 4 v900 := checkedSmall
theorem b1337 : Ban 12 4 v901 := checkedSmall
theorem b1338 : Ban 12 4 v902 := checkedSmall
theorem b1339 : Ban 12 4 v903 := checkedSmall
theorem b1340 : Ban 12 4 v904 := checkedSmall
theorem b1341 : Ban 12 4 v905 := checkedSmall
theorem b1342 : Ban 12 4 v906 := checkedSmall
theorem b1343 : Ban 12 4 v907 := checkedSmall
theorem b1344 : Ban 12 4 v908 := checkedSmall
theorem b1345 : Ban 12 4 v909 := checkedSmall
theorem b1346 : Ban 12 4 v910 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1347 : Ban 12 5 v884 := viaBranch (ws := [v885,v886,v887,v888,v889,v890,v891,v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910]) (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1327 (consBan b1328 (consBan b1329 (consBan b1330 (consBan b1331 (consBan b1332 (consBan b1333 (consBan b1334 (consBan b1335 (consBan b1336 (consBan b1337 (consBan b1338 (consBan b1339 (consBan b1340 (consBan b1341 (consBan b1342 (consBan b1343 (consBan b1344 (consBan b1345 (consBan b1346 (nilBan 12 4))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem solidb1347 : Wide 12 5 v884 := solid b1347
theorem b1597 : Ban 12 4 v884 := bySubset solidb1347
theorem b1598 : Ban 12 4 v1139 := checkedSmall
theorem b1599 : Ban 12 4 v1140 := checkedSmall
theorem b1600 : Ban 12 4 v1141 := smallByCut p15_14 w42
theorem b1601 : Ban 12 4 v1142 := checkedSmall
theorem b1602 : Ban 12 4 v1143 := checkedSmall
theorem b1603 : Ban 12 4 v1144 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1604 : Ban 12 5 v907 := viaBranch (ws := [v1130,v1131,v1132,v1133,v1134,v1135,v1136,v1137,v1138,v896,v884,v1139,v1140,v1141,v1142,v1143,v908,v910,v1144]) (consBan b1588 (consBan b1589 (consBan b1590 (consBan b1591 (consBan b1592 (consBan b1593 (consBan b1594 (consBan b1595 (consBan b1596 (consBan b1332 (consBan b1597 (consBan b1598 (consBan b1599 (consBan b1600 (consBan b1601 (consBan b1602 (consBan b1344 (consBan b1346 (consBan b1603 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1605 : Ban 12 5 v1129 := viaPerm map15_3 map15_4 b1604 (by decide +kernel) (by decide +kernel)
theorem b1606 : Ban 12 5 v1145 := checkedSmall
theorem b1607 : Ban 12 5 v1146 := checkedSmall
theorem b1608 : Ban 12 5 v1147 := checkedSmall
theorem b1609 : Ban 12 5 v1148 := checkedSmall
theorem b1610 : Ban 12 5 v1149 := checkedSmall
theorem b1611 : Ban 12 5 v1150 := checkedSmall
theorem b1612 : Ban 12 5 v1151 := checkedSmall
theorem b1613 : Ban 12 5 v1152 := checkedSmall
theorem b1614 : Ban 12 5 v1153 := checkedSmall
theorem b1615 : Ban 12 5 v1154 := checkedSmall
theorem b1616 : Ban 12 5 v1155 := checkedSmall
theorem b1617 : Ban 12 5 v1156 := checkedSmall
theorem b1618 : Ban 12 5 v1157 := viaPerm map15_1 map15_1 b1604 (by decide +kernel) (by decide +kernel)
theorem b1619 : Ban 12 5 v1158 := checkedSmall
theorem b1620 : Ban 12 5 v1159 := checkedSmall
theorem b1621 : Ban 12 5 v1160 := checkedSmall
theorem b1622 : Ban 12 5 v1161 := checkedSmall
theorem b1623 : Ban 12 5 v1162 := checkedSmall
theorem b1624 : Ban 12 5 v1163 := checkedSmall
theorem b1625 : Ban 12 5 v1164 := checkedSmall
theorem b1626 : Ban 12 5 v1165 := checkedSmall
theorem b1627 : Ban 12 4 v1167 := checkedSmall
theorem b1628 : Ban 12 4 v1168 := checkedSmall
theorem b1629 : Ban 12 4 v1169 := checkedSmall
theorem b1630 : Ban 12 4 v1170 := checkedSmall
theorem b1631 : Ban 12 4 v1171 := checkedSmall
theorem b1632 : Ban 12 4 v1172 := checkedSmall
theorem b1633 : Ban 12 4 v1173 := checkedSmall
theorem b1634 : Ban 12 4 v1174 := checkedSmall
theorem b1635 : Ban 12 4 v1175 := checkedSmall
theorem solidb1624 : Wide 12 5 v1163 := solid b1624
theorem b1636 : Ban 12 4 v1163 := bySubset solidb1624
theorem b1637 : Ban 12 4 v1176 := checkedSmall
theorem b1638 : Ban 12 4 v1177 := checkedSmall
theorem b1639 : Ban 12 4 v1178 := checkedSmall
theorem b1640 : Ban 12 4 v1179 := checkedSmall
theorem b1641 : Ban 12 4 v1180 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1642 : Ban 12 5 v1166 := viaBranch (ws := [v1167,v1168,v1169,v1170,v1171,v1172,v1173,v1174,v1175,v1163,v1176,v1177,v1178,v471,v1179,v473,v474,v1180]) (consBan b1627 (consBan b1628 (consBan b1629 (consBan b1630 (consBan b1631 (consBan b1632 (consBan b1633 (consBan b1634 (consBan b1635 (consBan b1636 (consBan b1637 (consBan b1638 (consBan b1639 (consBan b692 (consBan b1640 (consBan b694 (consBan b695 (consBan b1641 (nilBan 12 4))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1643 : Ban 12 5 v1181 := checkedSmall
theorem b1365 : Ban 12 5 v338 := checkedSmall
theorem b1644 : Ban 12 5 v1182 := checkedSmall
theorem b1256 : Ban 12 5 v828 := checkedSmall
theorem b1257 : Ban 12 5 v829 := checkedSmall
theorem b1258 : Ban 12 5 v830 := checkedSmall
theorem b1259 : Ban 12 5 v831 := checkedSmall
theorem b1260 : Ban 12 5 v832 := checkedSmall
theorem b1261 : Ban 12 5 v833 := checkedSmall
theorem b1262 : Ban 12 5 v834 := checkedSmall
theorem b1263 : Ban 12 5 v835 := checkedSmall
theorem b1112 : Ban 12 5 v773 := smallByCut p15_14 w42
theorem b1114 : Ban 12 5 v775 := smallByCut p15_14 w42
theorem b1115 : Ban 12 5 v777 := smallByCut p15_14 w42
theorem b1116 : Ban 12 5 v778 := smallByCut p15_14 w42
theorem b714 : Ban 12 5 v488 := checkedSmall
theorem b1117 : Ban 12 5 v779 := smallByCut p15_14 w42
theorem b1118 : Ban 12 5 v780 := smallByCut p15_14 w42
theorem b1119 : Ban 12 5 v781 := checkedSmall
theorem b1120 : Ban 12 5 v782 := smallByCut p15_14 w42
theorem b1121 : Ban 12 5 v464 := smallByCut p15_14 w42
theorem b1122 : Ban 12 5 v783 := smallByCut p15_14 w42
theorem b1123 : Ban 12 5 v784 := smallByCut p15_14 w42
theorem b1124 : Ban 12 5 v785 := smallByCut p15_14 w42
theorem b1125 : Ban 12 5 v786 := checkedSmall
theorem b1126 : Ban 12 5 v787 := smallByCut p15_14 w42
theorem b1127 : Ban 12 5 v788 := smallByCut p15_14 w42
theorem b1129 : Ban 12 5 v789 := smallByCut p15_14 w42
theorem b1130 : Ban 12 5 v791 := smallByCut p15_14 w42
theorem b1131 : Ban 12 5 v792 := smallByCut p15_14 w42
theorem b1132 : Ban 12 5 v793 := smallByCut p15_14 w42
theorem b1133 : Ban 12 5 v794 := smallByCut p15_14 w42
theorem b1134 : Ban 12 5 v795 := smallByCut p15_14 w42
theorem b1128 : Ban 12 5 v790 := smallByCut p15_14 w42
theorem b1135 : Ban 12 5 v796 := smallByCut p15_14 w42
theorem b717 : Ban 12 5 v491 := smallByCut p15_14 w42
theorem b1136 : Ban 12 5 v797 := smallByCut p15_14 w42
theorem b1137 : Ban 12 5 v798 := smallByCut p15_14 w42
theorem b1138 : Ban 12 5 v799 := smallByCut p15_14 w42
theorem b1139 : Ban 12 5 v800 := smallByCut p15_14 w42
theorem b1140 : Ban 12 4 v801 := smallByCut p15_14 w42
theorem b778 : Ban 12 4 v550 := checkedSmall
theorem b1141 : Ban 12 4 v802 := smallByCut p15_14 w42
theorem b1142 : Ban 12 4 v803 := checkedSmall
theorem b1143 : Ban 12 4 v804 := checkedSmall
theorem b1144 : Ban 12 4 v805 := smallByCut p15_14 w42
theorem b1145 : Ban 12 4 v806 := checkedSmall
theorem b1146 : Ban 12 4 v807 := smallByCut p15_14 w42
theorem b785 : Ban 12 4 v557 := checkedSmall
theorem b786 : Ban 12 4 v558 := smallByCut p15_14 w42
theorem b1147 : Ban 12 4 v808 := smallByCut p15_14 w42
theorem b788 : Ban 12 4 v560 := smallByCut p15_14 w42
theorem b1148 : Ban 12 4 v809 := checkedSmall
theorem b1149 : Ban 12 4 v810 := checkedSmall
theorem b1150 : Ban 12 4 v811 := checkedSmall
theorem b1151 : Ban 12 4 v812 := checkedSmall
theorem b1152 : Ban 12 4 v813 := smallByCut p15_14 w42
theorem solidb1138 : Wide 12 5 v799 := solid b1138
theorem b1153 : Ban 12 4 v799 := bySubset solidb1138
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1154 : Ban 12 5 v551 := viaBranch (ws := [v801,v550,v802,v803,v804,v805,v806,v807,v557,v558,v808,v560,v809,v810,v811,v812,v813,v799]) (consBan b1140 (consBan b778 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1144 (consBan b1145 (consBan b1146 (consBan b785 (consBan b786 (consBan b1147 (consBan b788 (consBan b1148 (consBan b1149 (consBan b1150 (consBan b1151 (consBan b1152 (consBan b1153 (nilBan 12 4))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1155 : Ban 12 5 v814 := smallByCut p15_14 w42
theorem b1156 : Ban 12 5 v815 := checkedSmall
theorem b1157 : Ban 12 5 v816 := checkedSmall
theorem b1158 : Ban 12 5 v817 := checkedSmall
theorem b1159 : Ban 12 5 v818 := checkedSmall
theorem b1160 : Ban 12 5 v819 := checkedSmall
theorem b1161 : Ban 12 5 v820 := checkedSmall
theorem b1162 : Ban 12 5 v821 := checkedSmall
theorem b1163 : Ban 12 5 v822 := checkedSmall
theorem b1164 : Ban 12 5 v823 := checkedSmall
theorem b1165 : Ban 12 5 v824 := checkedSmall
theorem b1166 : Ban 12 5 v825 := checkedSmall
theorem b1167 : Ban 12 5 v826 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1168 : Ban 12 6 v490 := viaBranch (ws := [v773,v775,v777,v778,v488,v779,v780,v781,v782,v464,v783,v449,v784,v450,v785,v786,v787,v788,v789,v791,v792,v793,v794,v795,v790,v796,v491,v797,v798,v799,v800,v551,v814,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826]) (consBan b1112 (consBan b1114 (consBan b1115 (consBan b1116 (consBan b714 (consBan b1117 (consBan b1118 (consBan b1119 (consBan b1120 (consBan b1121 (consBan b1122 (consBan b672 (consBan b1123 (consBan b673 (consBan b1124 (consBan b1125 (consBan b1126 (consBan b1127 (consBan b1129 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1134 (consBan b1128 (consBan b1135 (consBan b717 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1154 (consBan b1155 (consBan b1156 (consBan b1157 (consBan b1158 (consBan b1159 (consBan b1160 (consBan b1161 (consBan b1162 (consBan b1163 (consBan b1164 (consBan b1165 (consBan b1166 (consBan b1167 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1169 : Ban 12 6 v772 := viaPerm map15_2 map15_2 b1168 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w19 : Wide 12 6 v772 := viaSub (ws := [v320,v772]) (consBan b710 (consBan b1169 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b1264 : Ban 12 5 v772 := bySubset w19
theorem b1265 : Ban 12 5 v836 := checkedSmall
theorem b1266 : Ban 12 4 v838 := checkedSmall
theorem b1267 : Ban 12 4 v839 := checkedSmall
theorem b719 : Ban 12 5 v493 := smallByCut p15_14 w42
theorem solidb719 : Wide 12 5 v493 := solid b719
theorem b1268 : Ban 12 4 v493 := bySubset solidb719
theorem b1269 : Ban 12 4 v840 := checkedSmall
theorem b1270 : Ban 12 4 v841 := smallByCut p15_14 w42
theorem b1271 : Ban 12 4 v842 := smallByCut p15_14 w42
theorem b1272 : Ban 12 4 v843 := checkedSmall
theorem b1273 : Ban 12 4 v844 := checkedSmall
theorem b1274 : Ban 12 4 v845 := checkedSmall
theorem b1275 : Ban 12 4 v846 := checkedSmall
theorem b1276 : Ban 12 4 v847 := checkedSmall
theorem b1277 : Ban 12 4 v848 := smallByCut p15_14 w42
theorem solidb1128 : Wide 12 5 v790 := solid b1128
theorem b1278 : Ban 12 4 v790 := bySubset solidb1128
theorem b1279 : Ban 12 4 v849 := checkedSmall
theorem b1280 : Ban 12 4 v850 := checkedSmall
theorem b1281 : Ban 12 4 v851 := checkedSmall
theorem b1282 : Ban 12 4 v852 := checkedSmall
theorem b1283 : Ban 12 4 v853 := checkedSmall
theorem b1284 : Ban 12 4 v854 := checkedSmall
theorem b1285 : Ban 12 4 v855 := checkedSmall
theorem b1286 : Ban 12 4 v320 := bySubset w19
theorem b658 : Ban 12 4 v339 := checkedSmall
theorem b1287 : Ban 12 4 v441 := bySubset w13
theorem b1288 : Ban 12 4 v856 := checkedSmall
theorem b2152 : Ban 6 3 v1607 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w33 : Wide 6 3 v1607 := viaSub (ws := [v1607]) (consBan b2152 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1289 : Ban 12 4 v857 := smallByCut p15_14 w33
theorem b1290 : Ban 12 4 v858 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1291 : Ban 12 5 v837 := viaBranch (ws := [v838,v839,v493,v840,v841,v842,v843,v844,v845,v846,v847,v848,v790,v849,v850,v851,v852,v853,v854,v855,v320,v339,v441,v457,v856,v857,v858]) (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1270 (consBan b1271 (consBan b1272 (consBan b1273 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b1277 (consBan b1278 (consBan b1279 (consBan b1280 (consBan b1281 (consBan b1282 (consBan b1283 (consBan b1284 (consBan b1285 (consBan b1286 (consBan b658 (consBan b1287 (consBan b678 (consBan b1288 (consBan b1289 (consBan b1290 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1292 : Ban 12 5 v859 := checkedSmall
theorem b1293 : Ban 12 4 v861 := checkedSmall
theorem b1294 : Ban 12 4 v862 := checkedSmall
theorem b1295 : Ban 12 4 v863 := checkedSmall
theorem b1296 : Ban 12 4 v864 := checkedSmall
theorem b1297 : Ban 12 4 v865 := checkedSmall
theorem b1298 : Ban 12 4 v866 := checkedSmall
theorem b1299 : Ban 12 4 v867 := checkedSmall
theorem b1300 : Ban 12 4 v868 := checkedSmall
theorem b1301 : Ban 12 4 v869 := checkedSmall
theorem b1302 : Ban 12 4 v870 := checkedSmall
theorem b1303 : Ban 12 4 v871 := checkedSmall
theorem b741 : Ban 12 4 v514 := checkedSmall
theorem b1304 : Ban 12 4 v872 := checkedSmall
theorem b1305 : Ban 12 4 v873 := checkedSmall
theorem b748 : Ban 12 4 v520 := smallByCut p15_14 w42
theorem b749 : Ban 12 4 v521 := smallByCut p15_14 w42
theorem b750 : Ban 12 4 v522 := smallByCut p15_14 w42
theorem b751 : Ban 12 4 v523 := smallByCut p15_14 w42
theorem b752 : Ban 12 4 v524 := checkedSmall
theorem b753 : Ban 12 4 v525 := smallByCut p15_14 w42
theorem b754 : Ban 12 4 v526 := checkedSmall
theorem b755 : Ban 12 4 v527 := smallByCut p15_14 w42
theorem b756 : Ban 12 4 v528 := smallByCut p15_14 w42
theorem b757 : Ban 12 4 v529 := smallByCut p15_14 w42
theorem b758 : Ban 12 4 v530 := smallByCut p15_14 w42
theorem b759 : Ban 12 4 v531 := smallByCut p15_14 w42
theorem b760 : Ban 12 4 v532 := checkedSmall
theorem b761 : Ban 12 4 v533 := checkedSmall
theorem b762 : Ban 12 4 v534 := checkedSmall
theorem b763 : Ban 12 4 v535 := checkedSmall
theorem b764 : Ban 12 4 v536 := checkedSmall
theorem b765 : Ban 12 4 v537 := checkedSmall
theorem b766 : Ban 12 4 v538 := checkedSmall
theorem b767 : Ban 12 4 v539 := checkedSmall
theorem b768 : Ban 12 4 v540 := checkedSmall
theorem b769 : Ban 12 4 v541 := checkedSmall
theorem b770 : Ban 12 4 v542 := checkedSmall
theorem b771 : Ban 12 4 v543 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b772 : Ban 12 5 v519 := viaBranch (ws := [v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539,v540,v541,v542,v543]) (consBan b748 (consBan b749 (consBan b750 (consBan b751 (consBan b752 (consBan b753 (consBan b754 (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem solidb772 : Wide 12 5 v519 := solid b772
theorem b1306 : Ban 12 4 v519 := bySubset solidb772
theorem b1307 : Ban 12 4 v545 := smallByCut p15_14 w42
theorem b1308 : Ban 12 4 v874 := checkedSmall
theorem b711 : Ban 12 5 v485 := smallByCut p15_14 w42
theorem solidb711 : Wide 12 5 v485 := solid b711
theorem b1309 : Ban 12 4 v485 := bySubset solidb711
theorem b1310 : Ban 12 4 v875 := checkedSmall
theorem b1311 : Ban 12 4 v876 := checkedSmall
theorem b1312 : Ban 12 4 v877 := checkedSmall
theorem b779 : Ban 12 4 v551 := smallByCut p15_14 w42
theorem b780 : Ban 12 4 v552 := smallByCut p15_14 w42
theorem b781 : Ban 12 4 v553 := checkedSmall
theorem b782 : Ban 12 4 v554 := smallByCut p15_14 w42
theorem b783 : Ban 12 4 v555 := checkedSmall
theorem b784 : Ban 12 4 v556 := smallByCut p15_14 w42
theorem b787 : Ban 12 4 v559 := smallByCut p15_14 w42
theorem b789 : Ban 12 4 v561 := checkedSmall
theorem b743 : Ban 12 4 v516 := checkedSmall
theorem b790 : Ban 12 4 v562 := checkedSmall
theorem b791 : Ban 12 4 v563 := checkedSmall
theorem b792 : Ban 12 4 v564 := checkedSmall
theorem b793 : Ban 12 4 v565 := checkedSmall
theorem b794 : Ban 12 4 v566 := checkedSmall
theorem b795 : Ban 12 4 v567 := checkedSmall
theorem b796 : Ban 12 4 v568 := smallByCut p15_14 w42
theorem b776 : Ban 12 5 v547 := smallByCut p15_14 w42
theorem solidb776 : Wide 12 5 v547 := solid b776
theorem b797 : Ban 12 4 v547 := bySubset solidb776
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b798 : Ban 12 5 v549 := viaBranch (ws := [v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v516,v562,v563,v564,v565,v566,v567,v568,v547]) (consBan b778 (consBan b779 (consBan b780 (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b743 (consBan b790 (consBan b791 (consBan b792 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b797 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem solidb798 : Wide 12 5 v549 := solid b798
theorem b1313 : Ban 12 4 v549 := bySubset solidb798
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1314 : Ban 12 5 v860 := viaBranch (ws := [v861,v862,v863,v864,v865,v866,v867,v868,v869,v870,v871,v514,v872,v873,v519,v545,v874,v485,v875,v876,v877,v549,v547]) (consBan b1293 (consBan b1294 (consBan b1295 (consBan b1296 (consBan b1297 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1301 (consBan b1302 (consBan b1303 (consBan b741 (consBan b1304 (consBan b1305 (consBan b1306 (consBan b1307 (consBan b1308 (consBan b1309 (consBan b1310 (consBan b1311 (consBan b1312 (consBan b1313 (consBan b797 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1315 : Ban 12 5 v844 := viaPerm map15_5 map15_5 b1314 (by decide +kernel) (by decide +kernel)
theorem b1316 : Ban 12 5 v878 := checkedSmall
theorem b1317 : Ban 12 5 v879 := checkedSmall
theorem b1318 : Ban 12 5 v880 := checkedSmall
theorem b1319 : Ban 12 5 v881 := checkedSmall
theorem b1320 : Ban 12 5 v882 := checkedSmall
theorem b1348 : Ban 12 5 v883 := viaPerm map15_3 map15_4 b1347 (by decide +kernel) (by decide +kernel)
theorem b1349 : Ban 12 5 v911 := checkedSmall
theorem b1350 : Ban 12 5 v912 := checkedSmall
theorem b1351 : Ban 12 5 v913 := checkedSmall
theorem b1352 : Ban 12 5 v914 := checkedSmall
theorem b716 : Ban 12 5 v490 := smallByCut p15_14 w42
theorem b1353 : Ban 12 5 v915 := checkedSmall
theorem b1354 : Ban 12 5 v916 := viaPerm map15_2 map15_2 b1291 (by decide +kernel) (by decide +kernel)
theorem b1355 : Ban 12 5 v917 := checkedSmall
theorem b1356 : Ban 12 5 v918 := viaPerm map15_4 map15_3 b1314 (by decide +kernel) (by decide +kernel)
theorem b1357 : Ban 12 5 v919 := checkedSmall
theorem b1358 : Ban 12 5 v920 := checkedSmall
theorem b1359 : Ban 12 5 v921 := checkedSmall
theorem b1360 : Ban 12 5 v922 := checkedSmall
theorem b1361 : Ban 12 5 v923 := checkedSmall
theorem b1362 : Ban 12 5 v924 := viaPerm map15_1 map15_1 b1347 (by decide +kernel) (by decide +kernel)
theorem b1363 : Ban 12 5 v925 := checkedSmall
theorem b1364 : Ban 12 5 v850 := checkedSmall
theorem b1366 : Ban 12 5 v926 := checkedSmall
theorem b1367 : Ban 12 5 v927 := checkedSmall
theorem b1368 : Ban 12 5 v342 := checkedSmall
theorem b1369 : Ban 12 5 v928 := checkedSmall
theorem b1370 : Ban 12 4 v450 := smallByCut p15_14 w42
theorem b1371 : Ban 12 4 v929 := smallByCut p15_13 w42
theorem b1372 : Ban 12 4 v930 := checkedSmall
theorem b1373 : Ban 12 4 v931 := smallByCut p15_13 w42
theorem b1374 : Ban 12 4 v482 := smallByCut p15_13 w42
theorem b1375 : Ban 12 4 v932 := checkedSmall
theorem b1376 : Ban 12 4 v448 := smallByCut p15_14 w42
theorem b1377 : Ban 12 4 v933 := smallByCut p15_14 w42
theorem b1378 : Ban 12 4 v934 := checkedSmall
theorem b1379 : Ban 12 4 v935 := smallByCut p15_14 w42
theorem b1380 : Ban 12 4 v936 := checkedSmall
theorem b1381 : Ban 12 4 v480 := smallByCut p15_13 w42
theorem b1382 : Ban 12 4 v937 := checkedSmall
theorem b1383 : Ban 12 4 v938 := checkedSmall
theorem b1384 : Ban 12 4 v939 := checkedSmall
theorem b1385 : Ban 12 4 v940 := checkedSmall
theorem b661 : Ban 12 4 v342 := checkedSmall
theorem b1386 : Ban 12 4 v941 := checkedSmall
theorem b1387 : Ban 12 4 v942 := checkedSmall
theorem b1388 : Ban 12 4 v943 := checkedSmall
theorem b1389 : Ban 12 4 v944 := checkedSmall
theorem b1390 : Ban 12 4 v945 := checkedSmall
theorem b1391 : Ban 12 4 v946 := checkedSmall
theorem b1392 : Ban 12 4 v947 := checkedSmall
theorem b1393 : Ban 12 4 v948 := checkedSmall
theorem b1394 : Ban 12 4 v949 := checkedSmall
theorem b1395 : Ban 12 4 v950 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1396 : Ban 12 5 v343 := viaBranch (ws := [v450,v929,v930,v931,v482,v932,v448,v933,v934,v935,v936,v480,v937,v938,v939,v940,v342,v941,v942,v943,v944,v945,v946,v947,v948,v949,v950]) (consBan b1370 (consBan b1371 (consBan b1372 (consBan b1373 (consBan b1374 (consBan b1375 (consBan b1376 (consBan b1377 (consBan b1378 (consBan b1379 (consBan b1380 (consBan b1381 (consBan b1382 (consBan b1383 (consBan b1384 (consBan b1385 (consBan b661 (consBan b1386 (consBan b1387 (consBan b1388 (consBan b1389 (consBan b1390 (consBan b1391 (consBan b1392 (consBan b1393 (consBan b1394 (consBan b1395 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1397 : Ban 12 5 v951 := checkedSmall
theorem b1398 : Ban 12 5 v952 := checkedSmall
theorem b1399 : Ban 12 4 v954 := smallByCut p15_14 w33
theorem b1400 : Ban 12 4 v955 := smallByCut p15_14 w33
theorem b1401 : Ban 12 4 v956 := checkedSmall
theorem b1402 : Ban 12 4 v957 := smallByCut p15_14 w33
theorem b1403 : Ban 12 4 v958 := checkedSmall
theorem b1404 : Ban 12 4 v959 := checkedSmall
theorem b1405 : Ban 12 4 v960 := smallByCut p15_14 w33
theorem b1406 : Ban 12 4 v961 := checkedSmall
theorem b1407 : Ban 12 4 v962 := smallByCut p15_13 w33
theorem b1408 : Ban 12 4 v963 := smallByCut p15_13 w33
theorem b1409 : Ban 12 4 v964 := checkedSmall
theorem b1410 : Ban 12 4 v965 := smallByCut p15_13 w33
theorem b1411 : Ban 12 4 v966 := checkedSmall
theorem b1412 : Ban 12 4 v967 := smallByCut p15_13 w33
theorem b1413 : Ban 12 4 v968 := checkedSmall
theorem b1414 : Ban 12 4 v969 := smallByCut p15_13 w33
theorem b1415 : Ban 12 4 v970 := checkedSmall
theorem b1416 : Ban 12 4 v971 := checkedSmall
theorem b2158 : Ban 6 3 v1613 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w34 : Wide 6 3 v1613 := viaSub (ws := [v1613]) (consBan b2158 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b2294 : Ban 6 3 v1613 := bySubset w34
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w37 : Wide 6 3 v1613 := viaSub (ws := [v1613]) (consBan b2294 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1417 : Ban 12 4 v972 := smallByCut p15_13 w37
theorem b1418 : Ban 12 4 v973 := checkedSmall
theorem b1419 : Ban 12 4 v974 := checkedSmall
theorem b1420 : Ban 12 4 v975 := checkedSmall
theorem b1421 : Ban 12 4 v976 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1422 : Ban 12 5 v953 := viaBranch (ws := [v954,v955,v956,v957,v958,v857,v959,v960,v961,v962,v963,v964,v965,v966,v967,v968,v969,v970,v469,v971,v972,v973,v974,v850,v320,v339,v470,v975,v976]) (consBan b1399 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b1289 (consBan b1404 (consBan b1405 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b1409 (consBan b1410 (consBan b1411 (consBan b1412 (consBan b1413 (consBan b1414 (consBan b1415 (consBan b690 (consBan b1416 (consBan b1417 (consBan b1418 (consBan b1419 (consBan b1280 (consBan b1286 (consBan b658 (consBan b691 (consBan b1420 (consBan b1421 (nilBan 12 4)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1423 : Ban 12 5 v977 := checkedSmall
theorem b1424 : Ban 12 4 v978 := checkedSmall
theorem b1425 : Ban 12 4 v979 := checkedSmall
theorem b1426 : Ban 12 4 v980 := checkedSmall
theorem b1427 : Ban 12 4 v981 := checkedSmall
theorem b1428 : Ban 12 4 v982 := checkedSmall
theorem b1429 : Ban 12 4 v983 := checkedSmall
theorem b1430 : Ban 12 4 v984 := checkedSmall
theorem b1431 : Ban 12 4 v985 := checkedSmall
theorem b1432 : Ban 12 4 v986 := checkedSmall
theorem b1433 : Ban 12 4 v987 := checkedSmall
theorem b1434 : Ban 12 4 v988 := checkedSmall
theorem b1435 : Ban 12 4 v989 := checkedSmall
theorem b1436 : Ban 12 4 v990 := checkedSmall
theorem b1437 : Ban 12 4 v991 := checkedSmall
theorem b1438 : Ban 12 4 v992 := checkedSmall
theorem b1439 : Ban 12 4 v993 := checkedSmall
theorem b1440 : Ban 12 4 v994 := smallByCut p15_14 w42
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1441 : Ban 12 5 v868 := viaBranch (ws := [v978,v979,v980,v981,v982,v983,v984,v985,v986,v987,v867,v988,v989,v990,v991,v558,v992,v560,v993,v994]) (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1299 (consBan b1434 (consBan b1435 (consBan b1436 (consBan b1437 (consBan b786 (consBan b1438 (consBan b788 (consBan b1439 (consBan b1440 (nilBan 12 4))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1442 : Ban 12 5 v975 := viaPerm map15_4 map15_3 b1441 (by decide +kernel) (by decide +kernel)
theorem b1443 : Ban 12 5 v995 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1444 : Ban 12 6 v339 := viaBranch (ws := [v828,v829,v830,v831,v446,v832,v833,v834,v445,v835,v772,v836,v837,v859,v844,v878,v879,v880,v881,v882,v883,v911,v478,v912,v488,v913,v476,v914,v490,v915,v916,v917,v918,v919,v920,v921,v922,v923,v924,v925,v850,v338,v926,v452,v927,v342,v928,v343,v951,v472,v952,v953,v977,v975,v995]) (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1259 (consBan b669 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b667 (consBan b1263 (consBan b1264 (consBan b1265 (consBan b1291 (consBan b1292 (consBan b1315 (consBan b1316 (consBan b1317 (consBan b1318 (consBan b1319 (consBan b1320 (consBan b1348 (consBan b1349 (consBan b701 (consBan b1350 (consBan b714 (consBan b1351 (consBan b699 (consBan b1352 (consBan b716 (consBan b1353 (consBan b1354 (consBan b1355 (consBan b1356 (consBan b1357 (consBan b1358 (consBan b1359 (consBan b1360 (consBan b1361 (consBan b1362 (consBan b1363 (consBan b1364 (consBan b1365 (consBan b1366 (consBan b697 (consBan b1367 (consBan b1368 (consBan b1369 (consBan b1396 (consBan b1397 (consBan b707 (consBan b1398 (consBan b1422 (consBan b1423 (consBan b1442 (consBan b1443 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w21 : Wide 12 6 v339 := viaSub (ws := [v320,v339]) (consBan b710 (consBan b1444 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b1645 : Ban 12 5 v339 := bySubset w21
theorem b1646 : Ban 12 4 v1183 := checkedSmall
theorem b1647 : Ban 12 4 v1184 := checkedSmall
theorem b1648 : Ban 12 4 v1185 := checkedSmall
theorem b1649 : Ban 12 4 v1186 := checkedSmall
theorem b1650 : Ban 12 4 v1187 := checkedSmall
theorem b1651 : Ban 12 4 v1188 := checkedSmall
theorem b1652 : Ban 12 4 v1189 := checkedSmall
theorem b662 : Ban 12 4 v343 := checkedSmall
theorem b1653 : Ban 12 4 v1190 := checkedSmall
theorem b1654 : Ban 12 4 v1191 := checkedSmall
theorem b1655 : Ban 12 4 v1192 := checkedSmall
theorem b1656 : Ban 12 4 v1193 := checkedSmall
theorem b1657 : Ban 12 4 v1194 := checkedSmall
theorem b1658 : Ban 12 4 v1195 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1659 : Ban 12 5 v940 := viaBranch (ws := [v1183,v1184,v1185,v1186,v1187,v1188,v1189,v320,v343,v342,v1190,v1191,v1192,v1193,v1194,v1195,v949,v950]) (consBan b1646 (consBan b1647 (consBan b1648 (consBan b1649 (consBan b1650 (consBan b1651 (consBan b1652 (consBan b1286 (consBan b662 (consBan b661 (consBan b1653 (consBan b1654 (consBan b1655 (consBan b1656 (consBan b1657 (consBan b1658 (consBan b1394 (consBan b1395 (nilBan 12 4))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1660 : Ban 12 5 v1196 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1661 : Ban 12 6 v342 := viaBranch (ws := [v1117,v1118,v1119,v1120,v1121,v1122,v1123,v1124,v1125,v1126,v1127,v1128,v1129,v1145,v1146,v1147,v1148,v1149,v1150,v1151,v1152,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,v1163,v1164,v1165,v1166,v1181,v472,v338,v1182,v484,v339,v928,v343,v940,v1196]) (consBan b1576 (consBan b1577 (consBan b1578 (consBan b1579 (consBan b1580 (consBan b1581 (consBan b1582 (consBan b1583 (consBan b1584 (consBan b1585 (consBan b1586 (consBan b1587 (consBan b1605 (consBan b1606 (consBan b1607 (consBan b1608 (consBan b1609 (consBan b1610 (consBan b1611 (consBan b1612 (consBan b1613 (consBan b1614 (consBan b1615 (consBan b1616 (consBan b1617 (consBan b1618 (consBan b1619 (consBan b1620 (consBan b1621 (consBan b1622 (consBan b1623 (consBan b1624 (consBan b1625 (consBan b1626 (consBan b1642 (consBan b1643 (consBan b707 (consBan b1365 (consBan b1644 (consBan b709 (consBan b1645 (consBan b1369 (consBan b1396 (consBan b1659 (consBan b1660 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w23 : Wide 12 6 v342 := viaSub (ws := [v320,v342]) (consBan b710 (consBan b1661 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b1664 : Ban 12 5 v320 := bySubset w23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w28 : Wide 12 5 v321 := viaSub (ws := [v320,v321]) (consBan b1664 (consBan b664 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b639 : Ban 29 7 v439 := smallByCut p31_23 w28
theorem b814 : Ban 29 7 v442 := smallByCut p31_29 w60
theorem b815 : Ban 29 7 v582 := smallByCut p31_30 w60
theorem b816 : Ban 29 7 v583 := smallByCut p31_30 w20
theorem b817 : Ban 29 7 v584 := smallByCut p31_30 w60
theorem b818 : Ban 29 7 v585 := smallByCut p31_15 w28
theorem b819 : Ban 29 7 v586 := smallByCut p31_29 w60
theorem b820 : Ban 29 7 v587 := viaPerm map31_2 map31_2 b331 (by decide +kernel) (by decide +kernel)
theorem b821 : Ban 29 7 v588 := smallByCut p31_29 w20
theorem b822 : Ban 29 7 v589 := smallByCut p31_29 w20
theorem b823 : Ban 29 7 v590 := smallByCut p31_29 w60
theorem b824 : Ban 29 7 v591 := smallByCut p31_29 w20
theorem b825 : Ban 29 7 v592 := smallByCut p31_29 w60
theorem b826 : Ban 29 7 v593 := smallByCut p31_29 w20
theorem b635 : Ban 29 7 v438 := smallByCut p31_29 w60
theorem b827 : Ban 29 7 v594 := smallByCut p31_23 w28
theorem b828 : Ban 29 7 v595 := smallByCut p31_30 w60
theorem b829 : Ban 29 7 v596 := smallByCut p31_29 w60
theorem b830 : Ban 29 7 v597 := smallByCut p31_29 w20
theorem b831 : Ban 29 7 v598 := smallByCut p31_29 w60
theorem b832 : Ban 29 7 v599 := smallByCut p31_15 w28
theorem b835 : Ban 29 7 v600 := smallByCut p31_23 w28
theorem b936 : Ban 29 7 v603 := smallByCut p31_27 w16
theorem b937 : Ban 29 7 v602 := viaPerm map31_8 map31_6 b936 (by decide +kernel) (by decide +kernel)
theorem b939 : Ban 29 7 v604 := smallByCut p31_27 w6
theorem b940 : Ban 29 7 v606 := smallByCut p31_23 w28
theorem b942 : Ban 29 7 v607 := smallByCut p31_27 w60
theorem b944 : Ban 29 7 v609 := smallByCut p31_27 w6
theorem b945 : Ban 29 6 v612 := smallByCut p31_29 w17
theorem b946 : Ban 29 6 v613 := smallByCut p31_27 w6
theorem b947 : Ban 29 6 v614 := smallByCut p31_30 w17
theorem b948 : Ban 29 6 v615 := smallByCut p31_29 w17
theorem b949 : Ban 29 6 v616 := smallByCut p31_27 w17
theorem b950 : Ban 29 6 v617 := smallByCut p31_27 w6
theorem b951 : Ban 29 6 v618 := smallByCut p31_30 w17
theorem b952 : Ban 29 6 v619 := smallByCut p31_27 w17
theorem b953 : Ban 29 6 v620 := smallByCut p31_30 w17
theorem b954 : Ban 29 6 v621 := smallByCut p31_30 w6
theorem b955 : Ban 29 6 v622 := smallByCut p31_30 w17
theorem b956 : Ban 29 6 v623 := smallByCut p31_30 w6
theorem b957 : Ban 29 6 v624 := smallByCut p31_30 w17
theorem b958 : Ban 29 6 v625 := smallByCut p31_30 w6
theorem b959 : Ban 29 6 v626 := smallByCut p31_30 w17
theorem b960 : Ban 29 6 v627 := smallByCut p31_30 w6
theorem b961 : Ban 29 6 v628 := smallByCut p31_27 w20
theorem b962 : Ban 29 6 v629 := checkedSmall
theorem b963 : Ban 29 6 v630 := smallByCut p31_30 w6
theorem b964 : Ban 29 6 v631 := smallByCut p31_27 w17
theorem b965 : Ban 29 6 v632 := smallByCut p31_27 w6
theorem b966 : Ban 29 6 v633 := smallByCut p31_29 w17
theorem b967 : Ban 29 6 v634 := smallByCut p31_27 w17
theorem b968 : Ban 29 6 v635 := smallByCut p31_29 w17
theorem b969 : Ban 29 6 v636 := smallByCut p31_29 w6
theorem b970 : Ban 29 6 v637 := smallByCut p31_29 w17
theorem b971 : Ban 29 6 v638 := smallByCut p31_29 w6
theorem b972 : Ban 29 6 v639 := smallByCut p31_29 w17
theorem b973 : Ban 29 6 v640 := smallByCut p31_29 w6
theorem b974 : Ban 29 6 v641 := smallByCut p31_29 w17
theorem b975 : Ban 29 6 v642 := smallByCut p31_29 w6
theorem b976 : Ban 29 6 v643 := smallByCut p31_30 w20
theorem solidb431 : Wide 12 5 v244 := solid b431
theorem b1180 : Ban 12 5 v244 := bySubset solidb431
theorem solidb1180 : Wide 12 5 v244 := solid b1180
theorem b977 : Ban 29 6 v644 := smallByCut p31_27 solidb1180
theorem b978 : Ban 29 6 v645 := smallByCut p31_29 w6
theorem b979 : Ban 29 6 v646 := smallByCut p31_27 w17
theorem b980 : Ban 29 6 v647 := smallByCut p31_27 w6
theorem b981 : Ban 29 6 v648 := smallByCut p31_27 w17
theorem b982 : Ban 29 6 v649 := smallByCut p31_27 w6
theorem b983 : Ban 29 6 v650 := smallByCut p31_27 w17
theorem b984 : Ban 29 6 v651 := smallByCut p31_27 w6
theorem b985 : Ban 29 6 v652 := smallByCut p31_27 w17
theorem b986 : Ban 29 6 v653 := smallByCut p31_27 w6
theorem b987 : Ban 29 6 v654 := smallByCut p31_15 w21
theorem solidb1364 : Wide 12 5 v850 := solid b1364
theorem b988 : Ban 29 6 v655 := smallByCut p31_15 solidb1364
theorem b989 : Ban 29 6 v656 := smallByCut p31_27 w6
theorem b990 : Ban 29 6 v657 := checkedSmall
theorem b991 : Ban 29 6 v658 := checkedSmall
theorem b992 : Ban 29 6 v659 := checkedSmall
theorem b993 : Ban 29 6 v660 := checkedSmall
theorem b994 : Ban 29 5 v662 := checkedSmall
theorem b995 : Ban 29 5 v663 := checkedSmall
theorem b996 : Ban 29 5 v664 := checkedSmall
theorem b997 : Ban 29 5 v665 := checkedSmall
theorem b998 : Ban 29 5 v666 := checkedSmall
theorem b999 : Ban 29 5 v667 := checkedSmall
theorem b1000 : Ban 29 5 v668 := checkedSmall
theorem b1001 : Ban 29 5 v669 := checkedSmall
theorem b1002 : Ban 29 5 v670 := checkedSmall
theorem b1003 : Ban 29 5 v671 := checkedSmall
theorem b1004 : Ban 29 5 v672 := checkedSmall
theorem b1005 : Ban 29 5 v673 := checkedSmall
theorem b1006 : Ban 29 5 v674 := checkedSmall
theorem b1007 : Ban 29 5 v675 := checkedSmall
theorem b1008 : Ban 29 5 v676 := checkedSmall
theorem b1009 : Ban 29 5 v677 := checkedSmall
theorem b1010 : Ban 29 5 v678 := checkedSmall
theorem b1011 : Ban 29 5 v679 := checkedSmall
theorem b1012 : Ban 29 5 v680 := checkedSmall
theorem b1013 : Ban 29 5 v681 := checkedSmall
theorem b1014 : Ban 29 5 v682 := checkedSmall
theorem b1015 : Ban 29 5 v683 := checkedSmall
theorem b1016 : Ban 29 5 v684 := checkedSmall
theorem b1017 : Ban 29 5 v685 := checkedSmall
theorem b1018 : Ban 29 5 v686 := checkedSmall
theorem b1019 : Ban 29 5 v687 := checkedSmall
theorem b1020 : Ban 29 5 v688 := checkedSmall
theorem b1021 : Ban 29 5 v689 := checkedSmall
theorem b1022 : Ban 29 5 v690 := checkedSmall
theorem b1023 : Ban 29 5 v691 := checkedSmall
theorem b1024 : Ban 29 5 v692 := checkedSmall
theorem b1025 : Ban 29 5 v693 := checkedSmall
theorem b1026 : Ban 29 5 v694 := checkedSmall
theorem b1027 : Ban 29 5 v695 := checkedSmall
theorem b1028 : Ban 29 5 v696 := checkedSmall
theorem b1029 : Ban 29 5 v697 := checkedSmall
theorem b1030 : Ban 29 5 v698 := checkedSmall
theorem b1031 : Ban 29 5 v699 := checkedSmall
theorem b1032 : Ban 29 5 v700 := checkedSmall
theorem b1033 : Ban 29 5 v701 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1034 : Ban 29 6 v661 := viaBranch (ws := [v662,v663,v664,v665,v666,v667,v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692,v693,v694,v695,v696,v697,v698,v699,v700,v701]) (consBan b994 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1006 (consBan b1007 (consBan b1008 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1012 (consBan b1013 (consBan b1014 (consBan b1015 (consBan b1016 (consBan b1017 (consBan b1018 (consBan b1019 (consBan b1020 (consBan b1021 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b1025 (consBan b1026 (consBan b1027 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (nilBan 29 5))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1035 : Ban 29 6 v702 := checkedSmall
theorem b1036 : Ban 29 6 v703 := checkedSmall
theorem b1037 : Ban 29 6 v704 := checkedSmall
theorem b1038 : Ban 29 6 v705 := viaPerm map31_1 map31_1 b1034 (by decide +kernel) (by decide +kernel)
theorem b1039 : Ban 29 6 v706 := checkedSmall
theorem b1040 : Ban 29 6 v707 := checkedSmall
theorem b1041 : Ban 29 6 v708 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1042 : Ban 29 7 v611 := viaBranch (ws := [v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v702,v703,v704,v705,v706,v707,v708]) (consBan b945 (consBan b946 (consBan b947 (consBan b948 (consBan b949 (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b959 (consBan b960 (consBan b961 (consBan b962 (consBan b963 (consBan b964 (consBan b965 (consBan b966 (consBan b967 (consBan b968 (consBan b969 (consBan b970 (consBan b971 (consBan b972 (consBan b973 (consBan b974 (consBan b975 (consBan b976 (consBan b977 (consBan b978 (consBan b979 (consBan b980 (consBan b981 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (consBan b991 (consBan b992 (consBan b993 (consBan b1034 (consBan b1035 (consBan b1036 (consBan b1037 (consBan b1038 (consBan b1039 (consBan b1040 (consBan b1041 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1043 : Ban 29 6 v709 := smallByCut p31_29 w6
theorem b1044 : Ban 29 6 v710 := smallByCut p31_30 w17
theorem b1045 : Ban 29 6 v711 := smallByCut p31_29 w17
theorem b1046 : Ban 29 6 v712 := smallByCut p31_30 w17
theorem b1047 : Ban 29 6 v713 := smallByCut p31_29 w17
theorem b1048 : Ban 29 6 v714 := smallByCut p31_27 w6
theorem b1049 : Ban 29 6 v715 := smallByCut p31_27 w6
theorem b1050 : Ban 29 6 v716 := smallByCut p31_29 w20
theorem b1051 : Ban 29 6 v717 := smallByCut p31_29 w20
theorem b1052 : Ban 29 6 v718 := checkedSmall
theorem b1053 : Ban 29 6 v719 := smallByCut p31_27 w6
theorem b1054 : Ban 29 6 v720 := smallByCut p31_27 w6
theorem b1055 : Ban 29 6 v721 := smallByCut p31_30 w20
theorem b1056 : Ban 29 6 v722 := smallByCut p31_30 w20
theorem b1057 : Ban 29 6 v723 := smallByCut p31_27 solidb1180
theorem b1059 : Ban 29 6 v724 := smallByCut p31_27 w6
theorem b1063 : Ban 29 6 v726 := smallByCut p31_27 w17
theorem b1064 : Ban 29 6 v728 := smallByCut p31_27 w6
theorem b1065 : Ban 29 6 v729 := smallByCut p31_27 w17
theorem b1066 : Ban 29 6 v730 := smallByCut p31_29 solidb1180
theorem b1067 : Ban 29 6 v731 := smallByCut p31_29 w10
theorem b1068 : Ban 29 6 v732 := smallByCut p31_27 w6
theorem b1069 : Ban 29 6 v733 := smallByCut p31_27 w6
theorem b1070 : Ban 29 6 v734 := smallByCut p31_27 w17
theorem b1071 : Ban 29 6 v735 := checkedSmall
theorem b1072 : Ban 29 5 v736 := checkedSmall
theorem b1073 : Ban 29 5 v737 := checkedSmall
theorem b1074 : Ban 29 5 v738 := checkedSmall
theorem b1075 : Ban 29 5 v739 := checkedSmall
theorem b1076 : Ban 29 5 v740 := checkedSmall
theorem b1077 : Ban 29 5 v741 := checkedSmall
theorem b1078 : Ban 29 5 v742 := checkedSmall
theorem b1079 : Ban 29 5 v743 := checkedSmall
theorem b1080 : Ban 29 5 v744 := checkedSmall
theorem b1081 : Ban 29 5 v745 := checkedSmall
theorem b1082 : Ban 29 5 v746 := checkedSmall
theorem b1083 : Ban 29 5 v747 := checkedSmall
theorem b1084 : Ban 29 5 v748 := checkedSmall
theorem b1085 : Ban 29 5 v749 := checkedSmall
theorem b1086 : Ban 29 5 v750 := checkedSmall
theorem b1087 : Ban 29 5 v751 := checkedSmall
theorem b1088 : Ban 29 5 v703 := checkedSmall
theorem b1089 : Ban 29 5 v752 := checkedSmall
theorem b1090 : Ban 29 5 v753 := smallByCut p31_23 solidb1364
theorem b1091 : Ban 29 5 v754 := checkedSmall
theorem b1092 : Ban 29 5 v755 := checkedSmall
theorem b1093 : Ban 29 5 v756 := checkedSmall
theorem b1094 : Ban 29 5 v757 := checkedSmall
theorem b1095 : Ban 29 5 v758 := checkedSmall
theorem b1096 : Ban 29 5 v759 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1097 : Ban 29 6 v679 := viaBranch (ws := [v736,v737,v738,v739,v740,v741,v742,v743,v744,v745,v746,v681,v747,v748,v680,v749,v750,v751,v703,v752,v753,v754,v755,v756,v757,v758,v759]) (consBan b1072 (consBan b1073 (consBan b1074 (consBan b1075 (consBan b1076 (consBan b1077 (consBan b1078 (consBan b1079 (consBan b1080 (consBan b1081 (consBan b1082 (consBan b1013 (consBan b1083 (consBan b1084 (consBan b1012 (consBan b1085 (consBan b1086 (consBan b1087 (consBan b1088 (consBan b1089 (consBan b1090 (consBan b1091 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (nilBan 29 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1098 : Ban 29 6 v760 := checkedSmall
theorem b1099 : Ban 29 6 v761 := checkedSmall
theorem b1100 : Ban 29 6 v762 := smallByCut p31_27 w6
theorem b1101 : Ban 29 6 v763 := smallByCut p31_27 w6
theorem b1102 : Ban 29 6 v764 := checkedSmall
theorem b1103 : Ban 29 6 v765 := smallByCut p31_27 w17
theorem b1104 : Ban 29 6 v766 := smallByCut p31_19 w42
theorem b1105 : Ban 29 6 v767 := smallByCut p31_29 w20
theorem b1106 : Ban 29 6 v768 := viaPerm map31_1 map31_1 b1097 (by decide +kernel) (by decide +kernel)
theorem b1107 : Ban 29 6 v769 := checkedSmall
theorem b1108 : Ban 29 6 v770 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1109 : Ban 29 7 v613 := viaBranch (ws := [v709,v710,v711,v712,v713,v714,v715,v615,v716,v717,v718,v719,v720,v614,v721,v722,v723,v724,v726,v728,v729,v655,v656,v730,v731,v732,v733,v734,v735,v679,v760,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770]) (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1046 (consBan b1047 (consBan b1048 (consBan b1049 (consBan b948 (consBan b1050 (consBan b1051 (consBan b1052 (consBan b1053 (consBan b1054 (consBan b947 (consBan b1055 (consBan b1056 (consBan b1057 (consBan b1059 (consBan b1063 (consBan b1064 (consBan b1065 (consBan b988 (consBan b989 (consBan b1066 (consBan b1067 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1071 (consBan b1097 (consBan b1098 (consBan b1099 (consBan b1100 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (consBan b1107 (consBan b1108 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1171 : Ban 29 7 v766 := smallByCut p31_27 w60
theorem b1255 : Ban 29 7 v767 := smallByCut p31_29 w20
theorem b1445 : Ban 29 7 v654 := smallByCut p31_15 w21
theorem b1446 : Ban 29 7 v731 := smallByCut p31_29 w10
theorem b1447 : Ban 29 7 v996 := smallByCut p31_15 w28
theorem b1448 : Ban 29 7 v997 := viaPerm map31_9 map31_7 b936 (by decide +kernel) (by decide +kernel)
theorem b1449 : Ban 29 7 v998 := smallByCut p31_27 w6
theorem b1450 : Ban 29 7 v999 := smallByCut p31_15 w28
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w61 : Wide 12 5 v452 := viaSub (ws := [v320,v452]) (consBan b1664 (consBan b697 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b1574 : Ban 29 7 v1000 := smallByCut p31_23 w61
theorem b1575 : Ban 29 7 v1115 := smallByCut p31_23 w28
theorem b1974 : Ban 12 5 v1440 := smallByCut p15_14 w42
theorem b1975 : Ban 12 5 v1441 := checkedSmall
theorem b1976 : Ban 12 5 v1442 := smallByCut p15_14 w42
theorem b1977 : Ban 12 5 v1443 := checkedSmall
theorem b1978 : Ban 12 5 v1444 := smallByCut p15_14 w42
theorem b1979 : Ban 12 5 v1445 := checkedSmall
theorem b723 : Ban 12 5 v496 := smallByCut p15_14 w42
theorem b1980 : Ban 12 5 v1446 := checkedSmall
theorem b1981 : Ban 12 4 v1447 := smallByCut p15_14 w42
theorem b1982 : Ban 12 4 v1448 := smallByCut p15_14 w42
theorem b1983 : Ban 12 4 v1449 := smallByCut p15_14 w42
theorem b1984 : Ban 12 4 v1450 := smallByCut p15_14 w42
theorem b1985 : Ban 12 4 v1451 := smallByCut p15_14 w42
theorem b1986 : Ban 12 4 v1452 := smallByCut p15_14 w42
theorem b1987 : Ban 12 4 v1453 := smallByCut p15_14 w42
theorem b1988 : Ban 12 4 v1454 := smallByCut p15_14 w42
theorem b1989 : Ban 12 4 v1455 := checkedSmall
theorem b1990 : Ban 12 4 v1456 := smallByCut p15_14 w42
theorem b1991 : Ban 12 4 v1457 := checkedSmall
theorem b1992 : Ban 12 4 v1458 := smallByCut p15_14 w42
theorem b2170 : Ban 6 3 v1622 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w36 : Wide 6 3 v1622 := viaSub (ws := [v1622]) (consBan b2170 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b2319 : Ban 6 3 v1622 := bySubset w36
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w38 : Wide 6 3 v1622 := viaSub (ws := [v1622]) (consBan b2319 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1993 : Ban 12 4 v1459 := smallByCut p15_13 w38
theorem b1994 : Ban 12 4 v1460 := smallByCut p15_13 w38
theorem b1995 : Ban 12 4 v1461 := smallByCut p15_13 w38
theorem b1996 : Ban 12 4 v1462 := smallByCut p15_13 w38
theorem b1997 : Ban 12 4 v1463 := smallByCut p15_13 w38
theorem b1998 : Ban 12 4 v1464 := smallByCut p15_13 w38
theorem b1999 : Ban 12 4 v1465 := smallByCut p15_13 w38
theorem b2000 : Ban 12 4 v1466 := smallByCut p15_13 w38
theorem b2001 : Ban 12 4 v1467 := checkedSmall
theorem b2002 : Ban 12 4 v1468 := checkedSmall
theorem b2003 : Ban 12 4 v1469 := checkedSmall
theorem b2004 : Ban 12 4 v1470 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2005 : Ban 12 5 v1046 := viaBranch (ws := [v1447,v1448,v1449,v1450,v1451,v1452,v1453,v1454,v1455,v1456,v1457,v1458,v1459,v1460,v1461,v1462,v1463,v1464,v1465,v1466,v1467,v1468,v1469,v1470]) (consBan b1981 (consBan b1982 (consBan b1983 (consBan b1984 (consBan b1985 (consBan b1986 (consBan b1987 (consBan b1988 (consBan b1989 (consBan b1990 (consBan b1991 (consBan b1992 (consBan b1993 (consBan b1994 (consBan b1995 (consBan b1996 (consBan b1997 (consBan b1998 (consBan b1999 (consBan b2000 (consBan b2001 (consBan b2002 (consBan b2003 (consBan b2004 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2006 : Ban 12 5 v1047 := smallByCut p15_14 w42
theorem b2007 : Ban 12 5 v1471 := checkedSmall
theorem b2008 : Ban 12 5 v1472 := smallByCut p15_14 w42
theorem b2009 : Ban 12 5 v1049 := smallByCut p15_14 w42
theorem b2010 : Ban 12 5 v1473 := smallByCut p15_14 w42
theorem b2011 : Ban 12 5 v557 := checkedSmall
theorem b2012 : Ban 12 5 v1474 := checkedSmall
theorem b2013 : Ban 12 5 v1475 := checkedSmall
theorem b2014 : Ban 12 5 v1476 := checkedSmall
theorem b2015 : Ban 12 5 v1477 := checkedSmall
theorem b2016 : Ban 12 5 v1478 := checkedSmall
theorem b2017 : Ban 12 5 v1479 := checkedSmall
theorem b2018 : Ban 12 5 v1480 := checkedSmall
theorem b2019 : Ban 12 5 v1481 := checkedSmall
theorem b2020 : Ban 12 5 v1482 := checkedSmall
theorem b2021 : Ban 12 4 v1484 := smallByCut p15_14 w42
theorem b2022 : Ban 12 4 v1485 := smallByCut p15_14 w42
theorem b2023 : Ban 12 4 v1486 := checkedSmall
theorem b2024 : Ban 12 4 v1487 := checkedSmall
theorem b2025 : Ban 12 4 v1488 := checkedSmall
theorem b2026 : Ban 12 4 v1489 := smallByCut p15_14 w42
theorem b2027 : Ban 12 4 v1490 := smallByCut p15_14 w42
theorem b2028 : Ban 12 4 v1491 := checkedSmall
theorem b2029 : Ban 12 4 v1492 := checkedSmall
theorem solidb1642 : Wide 12 5 v1166 := solid b1642
theorem b2030 : Ban 12 4 v1166 := bySubset solidb1642
theorem b2031 : Ban 12 4 v1493 := checkedSmall
theorem b1511 : Ban 12 4 v1061 := checkedSmall
theorem b2032 : Ban 12 4 v1494 := checkedSmall
theorem b2033 : Ban 12 4 v1495 := checkedSmall
theorem b2034 : Ban 12 4 v1496 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2035 : Ban 12 5 v459 := viaBranch (ws := [v1484,v1485,v1486,v1487,v460,v1488,v1489,v1490,v1491,v1492,v1166,v1173,v1493,v1061,v1494,v1495,v471,v1131,v473,v474,v1496]) (consBan b2021 (consBan b2022 (consBan b2023 (consBan b2024 (consBan b681 (consBan b2025 (consBan b2026 (consBan b2027 (consBan b2028 (consBan b2029 (consBan b2030 (consBan b1633 (consBan b2031 (consBan b1511 (consBan b2032 (consBan b2033 (consBan b692 (consBan b1589 (consBan b694 (consBan b695 (consBan b2034 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2036 : Ban 12 5 v1483 := viaPerm map15_1 map15_1 b2035 (by decide +kernel) (by decide +kernel)
theorem b2037 : Ban 12 5 v1497 := checkedSmall
theorem b2038 : Ban 12 5 v1498 := checkedSmall
theorem b2039 : Ban 12 5 v1499 := checkedSmall
theorem b2040 : Ban 12 5 v1061 := checkedSmall
theorem b2041 : Ban 12 5 v1500 := checkedSmall
theorem b2042 : Ban 12 5 v1501 := checkedSmall
theorem b2043 : Ban 12 5 v1502 := checkedSmall
theorem b2044 : Ban 12 5 v1503 := checkedSmall
theorem b2045 : Ban 12 5 v1504 := checkedSmall
theorem b2046 : Ban 12 5 v1505 := checkedSmall
theorem b2047 : Ban 12 5 v1506 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2048 : Ban 12 6 v449 := viaBranch (ws := [v1440,v1441,v1442,v1443,v1444,v1445,v496,v1446,v1046,v1047,v1471,v1472,v1049,v1473,v557,v1474,v451,v1475,v1476,v1477,v1478,v1479,v1480,v1481,v1482,v1483,v1497,v480,v342,v1127,v482,v1159,v1498,v1499,v1061,v1500,v1501,v459,v1502,v472,v1503,v1504,v484,v1505,v1506,v450]) (consBan b1974 (consBan b1975 (consBan b1976 (consBan b1977 (consBan b1978 (consBan b1979 (consBan b723 (consBan b1980 (consBan b2005 (consBan b2006 (consBan b2007 (consBan b2008 (consBan b2009 (consBan b2010 (consBan b2011 (consBan b2012 (consBan b698 (consBan b2013 (consBan b2014 (consBan b2015 (consBan b2016 (consBan b2017 (consBan b2018 (consBan b2019 (consBan b2020 (consBan b2036 (consBan b2037 (consBan b703 (consBan b1368 (consBan b1586 (consBan b705 (consBan b1620 (consBan b2038 (consBan b2039 (consBan b2040 (consBan b2041 (consBan b2042 (consBan b2035 (consBan b2043 (consBan b707 (consBan b2044 (consBan b2045 (consBan b709 (consBan b2046 (consBan b2047 (consBan b673 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2325 : Ban 12 4 v1758 := checkedSmall
theorem b2282 : Ban 12 4 v1723 := checkedSmall
theorem b2326 : Ban 12 4 v1759 := checkedSmall
theorem b2327 : Ban 12 4 v1760 := checkedSmall
theorem b2328 : Ban 12 4 v1761 := checkedSmall
theorem b2329 : Ban 12 4 v1762 := checkedSmall
theorem b2330 : Ban 12 4 v1763 := smallByCut p15_13 w38
theorem b2331 : Ban 12 4 v1764 := smallByCut p15_13 w38
theorem b2332 : Ban 12 4 v1765 := smallByCut p15_13 w38
theorem b2333 : Ban 12 4 v1766 := smallByCut p15_13 w38
theorem b2334 : Ban 12 4 v1767 := checkedSmall
theorem b2335 : Ban 12 4 v1768 := checkedSmall
theorem b2336 : Ban 12 4 v1769 := checkedSmall
theorem b2315 : Ban 12 4 v1753 := checkedSmall
theorem b2337 : Ban 12 4 v1770 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2338 : Ban 12 5 v1464 := viaBranch (ws := [v1758,v1723,v1759,v1760,v1761,v1762,v1763,v1764,v1765,v1766,v1767,v1466,v1768,v1769,v1467,v1753,v1469,v1770,v1465]) (consBan b2325 (consBan b2282 (consBan b2326 (consBan b2327 (consBan b2328 (consBan b2329 (consBan b2330 (consBan b2331 (consBan b2332 (consBan b2333 (consBan b2334 (consBan b2000 (consBan b2335 (consBan b2336 (consBan b2001 (consBan b2315 (consBan b2003 (consBan b2337 (consBan b1999 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2523 : Ban 12 5 v1938 := checkedSmall
theorem b2635 : Ban 12 5 v2047 := checkedSmall
theorem b2964 : Ban 12 5 v2270 := checkedSmall
theorem b2965 : Ban 12 5 v2271 := checkedSmall
theorem b2892 : Ban 12 5 v2204 := checkedSmall
theorem b2893 : Ban 12 5 v2205 := checkedSmall
theorem b2966 : Ban 12 5 v2272 := checkedSmall
theorem b2967 : Ban 12 5 v2273 := checkedSmall
theorem b2861 : Ban 12 5 v2180 := checkedSmall
theorem b2968 : Ban 12 5 v2274 := checkedSmall
theorem b2969 : Ban 12 5 v2275 := checkedSmall
theorem b2970 : Ban 12 5 v2276 := checkedSmall
theorem b2971 : Ban 12 5 v2277 := checkedSmall
theorem b2972 : Ban 12 5 v2278 := checkedSmall
theorem b2973 : Ban 12 5 v2279 := checkedSmall
theorem b2974 : Ban 12 5 v2280 := checkedSmall
theorem b2975 : Ban 12 5 v2281 := checkedSmall
theorem b2976 : Ban 12 5 v2282 := checkedSmall
theorem b1499 : Ban 12 4 v1049 := smallByCut p15_14 w42
theorem b2977 : Ban 12 4 v2283 := checkedSmall
theorem b1496 : Ban 12 4 v1046 := smallByCut p15_14 w42
theorem b2978 : Ban 12 4 v2284 := checkedSmall
theorem b1497 : Ban 12 4 v1047 := smallByCut p15_14 w42
theorem b2979 : Ban 12 4 v2285 := smallByCut p15_14 w42
theorem b2980 : Ban 12 4 v2286 := checkedSmall
theorem b2981 : Ban 12 4 v2287 := smallByCut p15_14 w42
theorem b2982 : Ban 12 4 v2288 := checkedSmall
theorem b2983 : Ban 12 4 v2289 := checkedSmall
theorem b2984 : Ban 12 4 v2290 := checkedSmall
theorem b2985 : Ban 12 4 v2291 := checkedSmall
theorem b1968 : Ban 12 6 v320 := bySubset w23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w45 : Wide 12 6 v449 := viaSub (ws := [v320,v449]) (consBan b710 (consBan b2048 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b2761 : Ban 12 6 v449 := bySubset w45
theorem b2762 : Ban 12 6 v481 := viaPerm map23_2 map23_2 b2761 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w46 : Wide 12 6 v481 := viaSub (ws := [v320,v481]) (consBan b1968 (consBan b2762 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b2771 : Ban 12 6 v481 := bySubset w46
theorem b2837 : Ban 12 5 v2157 := checkedSmall
theorem b2838 : Ban 12 5 v2158 := checkedSmall
theorem b2839 : Ban 12 5 v2159 := checkedSmall
theorem b2840 : Ban 12 5 v2160 := checkedSmall
theorem b2841 : Ban 12 5 v2161 := checkedSmall
theorem b2842 : Ban 12 5 v2162 := checkedSmall
theorem b2780 : Ban 12 5 v2104 := checkedSmall
theorem b2843 : Ban 12 5 v2163 := checkedSmall
theorem b2844 : Ban 12 5 v2164 := viaPerm map15_3 map15_4 b2035 (by decide +kernel) (by decide +kernel)
theorem b2845 : Ban 12 4 v2166 := checkedSmall
theorem b2846 : Ban 12 4 v2167 := checkedSmall
theorem b2626 : Ban 12 4 v2040 := checkedSmall
theorem b2847 : Ban 12 4 v2168 := checkedSmall
theorem b2848 : Ban 12 4 v2169 := checkedSmall
theorem b2849 : Ban 12 4 v2170 := checkedSmall
theorem b2850 : Ban 12 4 v2171 := checkedSmall
theorem b2851 : Ban 12 4 v2172 := checkedSmall
theorem b2852 : Ban 12 4 v2173 := checkedSmall
theorem b2853 : Ban 12 4 v2174 := smallByCut p15_14 w37
theorem b2854 : Ban 12 4 v2175 := checkedSmall
theorem b2855 : Ban 12 4 v2176 := checkedSmall
theorem b2856 : Ban 12 4 v2177 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2857 : Ban 12 5 v1493 := viaBranch (ws := [v2166,v2167,v2040,v1131,v2168,v2169,v2170,v1175,v2171,v2172,v2173,v2174,v2175,v2176,v459,v1061,v469,v473,v1496,v2177]) (consBan b2845 (consBan b2846 (consBan b2626 (consBan b1589 (consBan b2847 (consBan b2848 (consBan b2849 (consBan b1635 (consBan b2850 (consBan b2851 (consBan b2852 (consBan b2853 (consBan b2854 (consBan b2855 (consBan b680 (consBan b1511 (consBan b690 (consBan b694 (consBan b2034 (consBan b2856 (nilBan 12 4))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2858 : Ban 12 5 v2165 := viaPerm map15_3 map15_4 b2857 (by decide +kernel) (by decide +kernel)
theorem b2859 : Ban 12 5 v2178 := checkedSmall
theorem b2615 : Ban 12 5 v2027 := checkedSmall
theorem b2860 : Ban 12 5 v2179 := checkedSmall
theorem b2862 : Ban 12 5 v2181 := checkedSmall
theorem b2863 : Ban 12 5 v2182 := checkedSmall
theorem b2864 : Ban 12 5 v2183 := checkedSmall
theorem b2865 : Ban 12 5 v2184 := checkedSmall
theorem b2866 : Ban 12 5 v2185 := checkedSmall
theorem b2867 : Ban 12 5 v2186 := checkedSmall
theorem b2868 : Ban 12 5 v2187 := checkedSmall
theorem b2869 : Ban 12 5 v1803 := viaPerm map15_2 map15_2 b2005 (by decide +kernel) (by decide +kernel)
theorem b2870 : Ban 12 5 v1804 := smallByCut p15_13 w42
theorem b2871 : Ban 12 5 v2188 := checkedSmall
theorem b2872 : Ban 12 5 v2189 := checkedSmall
theorem b2873 : Ban 12 5 v1806 := smallByCut p15_13 w42
theorem b2874 : Ban 12 5 v2190 := checkedSmall
theorem b2875 : Ban 12 5 v2191 := checkedSmall
theorem b2876 : Ban 12 5 v2192 := checkedSmall
theorem b2877 : Ban 12 5 v2193 := viaPerm map15_1 map15_1 b2857 (by decide +kernel) (by decide +kernel)
theorem b2878 : Ban 12 5 v2194 := checkedSmall
theorem b2879 : Ban 12 5 v2195 := checkedSmall
theorem b2880 : Ban 12 5 v1811 := checkedSmall
theorem b2881 : Ban 12 5 v2196 := checkedSmall
theorem b2882 : Ban 12 5 v2197 := checkedSmall
theorem b2883 : Ban 12 5 v1812 := checkedSmall
theorem b2884 : Ban 12 5 v2198 := checkedSmall
theorem b2885 : Ban 12 5 v1930 := checkedSmall
theorem b2886 : Ban 12 5 v2199 := checkedSmall
theorem b2887 : Ban 12 5 v2200 := checkedSmall
theorem b2888 : Ban 12 5 v2201 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2889 : Ban 12 6 v1480 := viaBranch (ws := [v2157,v2158,v2159,v2160,v2161,v2162,v2104,v2163,v2164,v2165,v2178,v1046,v1047,v2027,v2179,v2180,v1049,v2181,v2182,v2183,v2184,v2185,v2186,v2187,v1803,v1804,v2188,v2189,v1806,v2190,v2191,v2192,v1483,v2193,v2194,v2195,v1811,v2196,v2197,v1812,v2198,v1930,v2199,v2200,v2201,v320,v449,v481,v1481]) (consBan b2837 (consBan b2838 (consBan b2839 (consBan b2840 (consBan b2841 (consBan b2842 (consBan b2780 (consBan b2843 (consBan b2844 (consBan b2858 (consBan b2859 (consBan b2005 (consBan b2006 (consBan b2615 (consBan b2860 (consBan b2861 (consBan b2009 (consBan b2862 (consBan b2863 (consBan b2864 (consBan b2865 (consBan b2866 (consBan b2867 (consBan b2868 (consBan b2869 (consBan b2870 (consBan b2871 (consBan b2872 (consBan b2873 (consBan b2874 (consBan b2875 (consBan b2876 (consBan b2036 (consBan b2877 (consBan b2878 (consBan b2879 (consBan b2880 (consBan b2881 (consBan b2882 (consBan b2883 (consBan b2884 (consBan b2885 (consBan b2886 (consBan b2887 (consBan b2888 (consBan b1664 (consBan b672 (consBan b704 (consBan b2019 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2616 : Ban 12 5 v2028 := checkedSmall
theorem b2890 : Ban 12 5 v2202 := checkedSmall
theorem b2891 : Ban 12 5 v2203 := checkedSmall
theorem b2894 : Ban 12 5 v2206 := checkedSmall
theorem b2895 : Ban 12 5 v2207 := checkedSmall
theorem b2896 : Ban 12 5 v2208 := checkedSmall
theorem b2897 : Ban 12 5 v2209 := checkedSmall
theorem b2898 : Ban 12 5 v2210 := smallByCut p15_13 w42
theorem b2899 : Ban 12 5 v2211 := smallByCut p15_13 w42
theorem b2900 : Ban 12 5 v2212 := checkedSmall
theorem b2901 : Ban 12 5 v2213 := checkedSmall
theorem b2902 : Ban 12 5 v2214 := checkedSmall
theorem b2903 : Ban 12 5 v2215 := checkedSmall
theorem b2904 : Ban 12 5 v2216 := checkedSmall
theorem b2905 : Ban 12 5 v2217 := checkedSmall
theorem b2906 : Ban 12 5 v2218 := checkedSmall
theorem b2907 : Ban 12 5 v2219 := checkedSmall
theorem b2908 : Ban 12 5 v2220 := checkedSmall
theorem b2909 : Ban 12 5 v2221 := checkedSmall
theorem b2910 : Ban 12 5 v2222 := checkedSmall
theorem b2781 : Ban 12 5 v2105 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2911 : Ban 12 6 v1481 := viaBranch (ws := [v2027,v2179,v2028,v2181,v2165,v2178,v2202,v2203,v1471,v1472,v1127,v1473,v2204,v2205,v2206,v2188,v2189,v2207,v2190,v2193,v2194,v2208,v2209,v2210,v1155,v2211,v2212,v2213,v2214,v1497,v2195,v2215,v2197,v2216,v2217,v2218,v2219,v2220,v1499,v2221,v1501,v2222,v2105,v1482,v342,v450,v482]) (consBan b2615 (consBan b2860 (consBan b2616 (consBan b2862 (consBan b2858 (consBan b2859 (consBan b2890 (consBan b2891 (consBan b2007 (consBan b2008 (consBan b1586 (consBan b2010 (consBan b2892 (consBan b2893 (consBan b2894 (consBan b2871 (consBan b2872 (consBan b2895 (consBan b2874 (consBan b2877 (consBan b2878 (consBan b2896 (consBan b2897 (consBan b2898 (consBan b1616 (consBan b2899 (consBan b2900 (consBan b2901 (consBan b2902 (consBan b2037 (consBan b2879 (consBan b2903 (consBan b2882 (consBan b2904 (consBan b2905 (consBan b2906 (consBan b2907 (consBan b2908 (consBan b2039 (consBan b2909 (consBan b2042 (consBan b2910 (consBan b2781 (consBan b2020 (consBan b1368 (consBan b673 (consBan b705 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w50 : Wide 12 6 v1481 := viaSub (ws := [v320,v449,v481,v1480,v1481]) (consBan b710 (consBan b2048 (consBan b2771 (consBan b2889 (consBan b2911 (nilBan 12 6)))))) (by decide) (by decide +kernel)
theorem b2986 : Ban 12 4 v449 := bySubset w50
theorem b2987 : Ban 12 4 v2292 := checkedSmall
theorem b2988 : Ban 12 4 v2293 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2989 : Ban 12 5 v941 := viaBranch (ws := [v1049,v2283,v1046,v2284,v1047,v2285,v2286,v2287,v2288,v2289,v2290,v2291,v940,v320,v343,v449,v942,v943,v2292,v1193,v1194,v2293,v949,v950]) (consBan b1499 (consBan b2977 (consBan b1496 (consBan b2978 (consBan b1497 (consBan b2979 (consBan b2980 (consBan b2981 (consBan b2982 (consBan b2983 (consBan b2984 (consBan b2985 (consBan b1385 (consBan b1286 (consBan b662 (consBan b2986 (consBan b1387 (consBan b1388 (consBan b2987 (consBan b1656 (consBan b1657 (consBan b2988 (consBan b1394 (consBan b1395 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2990 : Ban 12 4 v2295 := checkedSmall
theorem b2496 : Ban 12 4 v1471 := smallByCut p15_14 w42
theorem b2991 : Ban 12 4 v2296 := smallByCut p15_14 w42
theorem b2992 : Ban 12 4 v2297 := checkedSmall
theorem b2993 : Ban 12 4 v2298 := checkedSmall
theorem b2994 : Ban 12 4 v2299 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2995 : Ban 12 5 v2294 := viaBranch (ws := [v2295,v1471,v2296,v2297,v450,v342,v482,v2284,v2292,v944,v2288,v2298,v936,v2299]) (consBan b2990 (consBan b2496 (consBan b2991 (consBan b2992 (consBan b1370 (consBan b661 (consBan b1374 (consBan b2978 (consBan b2987 (consBan b1389 (consBan b2982 (consBan b2993 (consBan b1380 (consBan b2994 (nilBan 12 4))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2996 : Ban 12 5 v2300 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2997 : Ban 12 6 v1127 := viaBranch (ws := [v1464,v1938,v2047,v2270,v2271,v1129,v1145,v2204,v2205,v2272,v2273,v2180,v2274,v2275,v2276,v1153,v1154,v1156,v1160,v1161,v2277,v1498,v2278,v2279,v1162,v2280,v1165,v2281,v1499,v2282,v1501,v881,v1128,v941,v2294,v2300,v482,v1482]) (consBan b2338 (consBan b2523 (consBan b2635 (consBan b2964 (consBan b2965 (consBan b1605 (consBan b1606 (consBan b2892 (consBan b2893 (consBan b2966 (consBan b2967 (consBan b2861 (consBan b2968 (consBan b2969 (consBan b2970 (consBan b1614 (consBan b1615 (consBan b1617 (consBan b1621 (consBan b1622 (consBan b2971 (consBan b2038 (consBan b2972 (consBan b2973 (consBan b1623 (consBan b2974 (consBan b1626 (consBan b2975 (consBan b2039 (consBan b2976 (consBan b2042 (consBan b1319 (consBan b1587 (consBan b2989 (consBan b2995 (consBan b2996 (consBan b705 (consBan b2020 (nilBan 12 5))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w52 : Wide 12 6 v1127 := viaSub (ws := [v320,v449,v342,v1127]) (consBan b710 (consBan b2048 (consBan b1661 (consBan b2997 (nilBan 12 6))))) (by decide) (by decide +kernel)
theorem b1662 : Ban 29 7 v1116 := smallByCut p31_15 w52
theorem b1663 : Ban 29 7 v1197 := smallByCut p31_29 w16
theorem b1666 : Ban 29 7 v1198 := smallByCut p31_23 w61
theorem b1668 : Ban 29 7 v1200 := smallByCut p31_23 w28
theorem b1669 : Ban 29 6 v1203 := smallByCut p31_14 w42
theorem b1670 : Ban 29 6 v1204 := smallByCut p31_22 w42
theorem b1671 : Ban 29 6 v1205 := smallByCut p31_29 w60
theorem b1672 : Ban 29 6 v1206 := smallByCut p31_23 w28
theorem b1673 : Ban 29 6 v1207 := smallByCut p31_13 w42
theorem b1674 : Ban 29 6 v1208 := smallByCut p31_21 w42
theorem b1675 : Ban 29 6 v1209 := smallByCut p31_14 w42
theorem b1676 : Ban 29 6 v1210 := smallByCut p31_21 w42
theorem b1677 : Ban 29 6 v1211 := smallByCut p31_13 w42
theorem b1678 : Ban 29 6 v1212 := smallByCut p31_21 w42
theorem b1679 : Ban 29 6 v1213 := smallByCut p31_30 w60
theorem b1680 : Ban 29 6 v1214 := smallByCut p31_23 w28
theorem b1681 : Ban 29 6 v1215 := smallByCut p31_14 w42
theorem b1682 : Ban 29 6 v1216 := smallByCut p31_22 w42
theorem b1683 : Ban 29 6 v1217 := smallByCut p31_13 w42
theorem b1684 : Ban 29 6 v1218 := smallByCut p31_21 w42
theorem b1685 : Ban 29 6 v1219 := smallByCut p31_13 w42
theorem b1686 : Ban 29 6 v1220 := checkedSmall
theorem b1687 : Ban 29 6 v1221 := checkedSmall
theorem b1688 : Ban 29 6 v1222 := checkedSmall
theorem b1689 : Ban 29 6 v1223 := smallByCut p31_23 w21
theorem b1690 : Ban 29 6 v1224 := checkedSmall
theorem b1691 : Ban 29 6 v1225 := smallByCut p31_19 w42
theorem b1692 : Ban 29 6 v1226 := checkedSmall
theorem solidb1659 : Wide 12 5 v940 := solid b1659
theorem b1693 : Ban 29 6 v1227 := smallByCut p31_15 solidb1659
theorem b1694 : Ban 29 6 v1116 := smallByCut p31_15 w52
theorem b1695 : Ban 29 6 v1228 := smallByCut p31_23 w28
theorem b1696 : Ban 29 6 v1229 := smallByCut p31_13 w42
theorem b1697 : Ban 29 6 v1230 := checkedSmall
theorem b1698 : Ban 29 6 v1231 := smallByCut p31_23 w52
theorem b1699 : Ban 29 6 v1232 := checkedSmall
theorem b1700 : Ban 29 6 v1233 := checkedSmall
theorem b1701 : Ban 29 6 v1234 := checkedSmall
theorem b1703 : Ban 29 6 v1235 := smallByCut p31_13 w42
theorem b1704 : Ban 29 6 v1237 := checkedSmall
theorem b1705 : Ban 29 6 v1238 := smallByCut p31_21 w42
theorem b1706 : Ban 29 6 v1239 := smallByCut p31_23 w28
theorem b1707 : Ban 29 6 v1240 := smallByCut p31_22 w42
theorem b1708 : Ban 29 6 v1241 := smallByCut p31_21 w42
theorem b1709 : Ban 29 6 v1242 := smallByCut p31_22 w42
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w27 : Wide 12 5 v6 := viaSub (ws := [v2,v6]) (consBan b94 (consBan b27 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b1710 : Ban 29 6 v1243 := smallByCut p31_30 w27
theorem b1711 : Ban 29 6 v1244 := smallByCut p31_22 w42
theorem b1712 : Ban 29 6 v1245 := smallByCut p31_30 w27
theorem b1713 : Ban 29 6 v1246 := smallByCut p31_30 w27
theorem b1714 : Ban 29 6 v1247 := smallByCut p31_22 w42
theorem b1715 : Ban 29 6 v1248 := smallByCut p31_23 w28
theorem b1716 : Ban 29 6 v1249 := smallByCut p31_21 w42
theorem b1717 : Ban 29 6 v1250 := smallByCut p31_22 w42
theorem b1718 : Ban 29 6 v1251 := smallByCut p31_30 w27
theorem b1719 : Ban 29 6 v1252 := smallByCut p31_22 w42
theorem b1720 : Ban 29 6 v1253 := smallByCut p31_30 w27
theorem b1721 : Ban 29 6 v1254 := smallByCut p31_21 w42
theorem b1722 : Ban 29 6 v1255 := smallByCut p31_29 w27
theorem b1723 : Ban 29 6 v1256 := smallByCut p31_21 w42
theorem b1724 : Ban 29 6 v1257 := smallByCut p31_29 w27
theorem b1725 : Ban 29 6 v1258 := smallByCut p31_29 w27
theorem b1726 : Ban 29 6 v1259 := smallByCut p31_21 w42
theorem b1727 : Ban 29 6 v1260 := smallByCut p31_23 w28
theorem b1728 : Ban 29 6 v1261 := smallByCut p31_21 w42
theorem b1729 : Ban 29 6 v1262 := smallByCut p31_21 w42
theorem b1730 : Ban 29 6 v1263 := smallByCut p31_29 w27
theorem b1731 : Ban 29 6 v1264 := smallByCut p31_21 w42
theorem b1732 : Ban 29 6 v1265 := smallByCut p31_29 w27
theorem b1733 : Ban 29 6 v1266 := smallByCut p31_23 w28
theorem b1734 : Ban 29 6 v1267 := smallByCut p31_21 w42
theorem b1735 : Ban 29 6 v1268 := smallByCut p31_23 w28
theorem b1736 : Ban 29 6 v1269 := checkedSmall
theorem b1737 : Ban 29 6 v1270 := smallByCut p31_23 w28
theorem b1738 : Ban 29 6 v1271 := smallByCut p31_21 w42
theorem b1739 : Ban 29 6 v1272 := checkedSmall
theorem b1740 : Ban 29 6 v1273 := checkedSmall
theorem b1741 : Ban 29 6 v1274 := checkedSmall
theorem b1742 : Ban 29 6 v1275 := checkedSmall
theorem b1743 : Ban 29 6 v1276 := smallByCut p31_21 w42
theorem b1744 : Ban 29 6 v1277 := checkedSmall
theorem b1745 : Ban 29 6 v1278 := smallByCut p31_23 w28
theorem b1746 : Ban 29 6 v1279 := smallByCut p31_23 w28
theorem b1747 : Ban 29 6 v1280 := smallByCut p31_21 w42
theorem b1748 : Ban 29 6 v1281 := smallByCut p31_23 w28
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1749 : Ban 29 7 v1202 := viaBranch (ws := [v1203,v1204,v1205,v1206,v1207,v1208,v1209,v1210,v1211,v1212,v1213,v1214,v1215,v1216,v1217,v1218,v1219,v1220,v1221,v1222,v1223,v1224,v1225,v1226,v1227,v1116,v1228,v1229,v1230,v1231,v1232,v1233,v1234,v1235,v1237,v1238,v1239,v1240,v1241,v1242,v1243,v1244,v1245,v1246,v1247,v1248,v1249,v1250,v1251,v1252,v1253,v1254,v1255,v1256,v1257,v1258,v1259,v1260,v1261,v1262,v1263,v1264,v1265,v1266,v1267,v1268,v1269,v1270,v1271,v1272,v1273,v1274,v1275,v1276,v1277,v1278,v1279,v1280,v1281]) (consBan b1669 (consBan b1670 (consBan b1671 (consBan b1672 (consBan b1673 (consBan b1674 (consBan b1675 (consBan b1676 (consBan b1677 (consBan b1678 (consBan b1679 (consBan b1680 (consBan b1681 (consBan b1682 (consBan b1683 (consBan b1684 (consBan b1685 (consBan b1686 (consBan b1687 (consBan b1688 (consBan b1689 (consBan b1690 (consBan b1691 (consBan b1692 (consBan b1693 (consBan b1694 (consBan b1695 (consBan b1696 (consBan b1697 (consBan b1698 (consBan b1699 (consBan b1700 (consBan b1701 (consBan b1703 (consBan b1704 (consBan b1705 (consBan b1706 (consBan b1707 (consBan b1708 (consBan b1709 (consBan b1710 (consBan b1711 (consBan b1712 (consBan b1713 (consBan b1714 (consBan b1715 (consBan b1716 (consBan b1717 (consBan b1718 (consBan b1719 (consBan b1720 (consBan b1721 (consBan b1722 (consBan b1723 (consBan b1724 (consBan b1725 (consBan b1726 (consBan b1727 (consBan b1728 (consBan b1729 (consBan b1730 (consBan b1731 (consBan b1732 (consBan b1733 (consBan b1734 (consBan b1735 (consBan b1736 (consBan b1737 (consBan b1738 (consBan b1739 (consBan b1740 (consBan b1741 (consBan b1742 (consBan b1743 (consBan b1744 (consBan b1745 (consBan b1746 (consBan b1747 (consBan b1748 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1750 : Ban 29 6 v437 := smallByCut p31_14 w42
theorem b1751 : Ban 29 6 v1282 := smallByCut p31_29 w60
theorem b1752 : Ban 29 6 v1283 := smallByCut p31_13 w42
theorem b1753 : Ban 29 6 v319 := smallByCut p31_14 w42
theorem b1754 : Ban 29 6 v438 := smallByCut p31_13 w42
theorem b1755 : Ban 29 6 v1284 := smallByCut p31_30 w60
theorem b1756 : Ban 29 6 v1285 := smallByCut p31_14 w42
theorem b1757 : Ban 29 6 v592 := smallByCut p31_13 w42
theorem b1758 : Ban 29 6 v1286 := smallByCut p31_13 w42
theorem b1759 : Ban 29 6 v1287 := checkedSmall
theorem b1760 : Ban 29 6 v1288 := checkedSmall
theorem b1761 : Ban 29 6 v1289 := smallByCut p31_15 w28
theorem solidb566 : Wide 12 5 v376 := solid b566
theorem b866 : Ban 12 5 v376 := bySubset solidb566
theorem solidb866 : Wide 12 5 v376 := solid b866
theorem b1762 : Ban 29 6 v1290 := smallByCut p31_29 solidb866
theorem b1763 : Ban 29 6 v1197 := smallByCut p31_23 w28
theorem b1764 : Ban 29 6 v1000 := smallByCut p31_19 w42
theorem b1765 : Ban 29 6 v1291 := smallByCut p31_21 w42
theorem b1766 : Ban 29 6 v1115 := smallByCut p31_21 w42
theorem b1767 : Ban 29 6 v1292 := smallByCut p31_13 w42
theorem b1768 : Ban 29 6 v1293 := checkedSmall
theorem b1769 : Ban 29 6 v1294 := checkedSmall
theorem b1772 : Ban 29 6 v1295 := smallByCut p31_13 w42
theorem b1773 : Ban 29 6 v1297 := smallByCut p31_29 w27
theorem b1774 : Ban 29 6 v1298 := smallByCut p31_22 w42
theorem b1775 : Ban 29 6 v1299 := smallByCut p31_21 w42
theorem b1776 : Ban 29 6 v1300 := smallByCut p31_22 w42
theorem b1777 : Ban 29 6 v1301 := smallByCut p31_21 w42
theorem b1778 : Ban 29 6 v1302 := checkedSmall
theorem b1779 : Ban 29 6 v1303 := smallByCut p31_30 w27
theorem b1780 : Ban 29 6 v1304 := smallByCut p31_30 w27
theorem b1781 : Ban 29 6 v1305 := smallByCut p31_23 w28
theorem b1782 : Ban 29 6 v1306 := checkedSmall
theorem b1783 : Ban 29 6 v1307 := smallByCut p31_29 w27
theorem b1784 : Ban 29 6 v1308 := smallByCut p31_29 w27
theorem b1785 : Ban 29 6 v1309 := smallByCut p31_23 w28
theorem b1786 : Ban 29 6 v1310 := smallByCut p31_23 w28
theorem b1787 : Ban 29 6 v1311 := checkedSmall
theorem b1788 : Ban 29 6 v1312 := checkedSmall
theorem b1789 : Ban 29 6 v1313 := checkedSmall
theorem b1790 : Ban 29 6 v1314 := checkedSmall
theorem b1792 : Ban 29 6 v1315 := smallByCut p31_23 w28
theorem b1793 : Ban 29 6 v1317 := smallByCut p31_21 w42
theorem b1794 : Ban 29 6 v1318 := smallByCut p31_23 w28
theorem b1795 : Ban 29 5 v1320 := smallByCut p31_19 w42
theorem b1796 : Ban 29 5 v1321 := smallByCut p31_13 w42
theorem b1797 : Ban 29 5 v1322 := smallByCut p31_13 w42
theorem solidb367 : Wide 12 4 v38 := solid b367
theorem b1798 : Ban 29 5 v1323 := smallByCut p31_29 solidb367
theorem b1799 : Ban 29 5 v1324 := checkedSmall
theorem b1800 : Ban 29 5 v1325 := checkedSmall
theorem b1801 : Ban 29 5 v1326 := checkedSmall
theorem b1802 : Ban 29 5 v1327 := checkedSmall
theorem b1803 : Ban 29 5 v1328 := smallByCut p31_15 solidb1659
theorem b1804 : Ban 29 5 v1329 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1805 : Ban 29 6 v1319 := viaBranch (ws := [v1320,v1321,v1322,v1323,v1324,v1325,v1326,v1327,v1328,v1329]) (consBan b1795 (consBan b1796 (consBan b1797 (consBan b1798 (consBan b1799 (consBan b1800 (consBan b1801 (consBan b1802 (consBan b1803 (consBan b1804 (nilBan 29 5))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1806 : Ban 29 6 v1330 := smallByCut p31_23 w28
theorem b1807 : Ban 29 6 v1331 := checkedSmall
theorem b1808 : Ban 29 6 v1332 := checkedSmall
theorem b1809 : Ban 29 6 v1333 := checkedSmall
theorem b1810 : Ban 29 6 v1334 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1811 : Ban 29 7 v1239 := viaBranch (ws := [v437,v1282,v1283,v319,v438,v1284,v1285,v592,v1286,v1287,v1288,v1289,v1290,v1197,v1000,v1291,v1115,v1292,v1293,v1294,v1295,v1297,v1298,v1299,v1300,v1301,v1302,v1303,v1304,v1305,v1241,v1306,v1307,v1308,v1309,v1240,v1310,v1311,v1312,v735,v1313,v1314,v1227,v1228,v1315,v1317,v1318,v1319,v1330,v1331,v1332,v1333,v1334]) (consBan b1750 (consBan b1751 (consBan b1752 (consBan b1753 (consBan b1754 (consBan b1755 (consBan b1756 (consBan b1757 (consBan b1758 (consBan b1759 (consBan b1760 (consBan b1761 (consBan b1762 (consBan b1763 (consBan b1764 (consBan b1765 (consBan b1766 (consBan b1767 (consBan b1768 (consBan b1769 (consBan b1772 (consBan b1773 (consBan b1774 (consBan b1775 (consBan b1776 (consBan b1777 (consBan b1778 (consBan b1779 (consBan b1780 (consBan b1781 (consBan b1708 (consBan b1782 (consBan b1783 (consBan b1784 (consBan b1785 (consBan b1707 (consBan b1786 (consBan b1787 (consBan b1788 (consBan b1071 (consBan b1789 (consBan b1790 (consBan b1693 (consBan b1695 (consBan b1792 (consBan b1793 (consBan b1794 (consBan b1805 (consBan b1806 (consBan b1807 (consBan b1808 (consBan b1809 (consBan b1810 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1812 : Ban 29 7 v1335 := smallByCut p31_15 w28
theorem b1813 : Ban 29 6 v1337 := smallByCut p31_29 w60
theorem b1814 : Ban 29 6 v1338 := smallByCut p31_14 w42
theorem b1815 : Ban 29 6 v1339 := smallByCut p31_13 w42
theorem b1816 : Ban 29 6 v1340 := smallByCut p31_14 w42
theorem b1817 : Ban 29 6 v1341 := smallByCut p31_13 w42
theorem b1818 : Ban 29 6 v1342 := viaPerm map31_6 map31_8 b317 (by decide +kernel) (by decide +kernel)
theorem b1819 : Ban 29 6 v1343 := smallByCut p31_30 w60
theorem b1820 : Ban 29 6 v1344 := smallByCut p31_13 w42
theorem b1821 : Ban 29 6 v1345 := smallByCut p31_30 w60
theorem b1822 : Ban 29 6 v1346 := smallByCut p31_14 w42
theorem b1823 : Ban 29 6 v1347 := smallByCut p31_30 w60
theorem b1824 : Ban 29 6 v1348 := smallByCut p31_30 w60
theorem b1825 : Ban 29 6 v1349 := smallByCut p31_14 w42
theorem b1826 : Ban 29 6 v1350 := smallByCut p31_29 w30
theorem b1827 : Ban 29 6 v1351 := smallByCut p31_30 w60
theorem b1828 : Ban 29 6 v1352 := checkedSmall
theorem b1829 : Ban 29 6 v1353 := viaPerm map31_2 map31_2 b317 (by decide +kernel) (by decide +kernel)
theorem b1830 : Ban 29 6 v1354 := smallByCut p31_29 w60
theorem b1831 : Ban 29 6 v1355 := smallByCut p31_14 w42
theorem b1832 : Ban 29 6 v1356 := smallByCut p31_29 w60
theorem b1833 : Ban 29 6 v1357 := smallByCut p31_13 w42
theorem b1834 : Ban 29 6 v1358 := smallByCut p31_29 w60
theorem b1835 : Ban 29 6 v1359 := smallByCut p31_29 w60
theorem b1836 : Ban 29 6 v1360 := smallByCut p31_13 w42
theorem b1837 : Ban 29 6 v1361 := smallByCut p31_30 w30
theorem b1838 : Ban 29 6 v1362 := smallByCut p31_29 w60
theorem b1839 : Ban 29 6 v1363 := checkedSmall
theorem b1840 : Ban 29 6 v1364 := smallByCut p31_19 w42
theorem b1841 : Ban 29 6 v1365 := smallByCut p31_19 w42
theorem b1842 : Ban 29 6 v1366 := smallByCut p31_15 w21
theorem b1843 : Ban 29 6 v1367 := smallByCut p31_27 w17
theorem b1844 : Ban 29 6 v1368 := checkedSmall
theorem b1845 : Ban 29 6 v1369 := smallByCut p31_27 w17
theorem b1846 : Ban 29 6 v1370 := checkedSmall
theorem b1847 : Ban 29 6 v1320 := smallByCut p31_23 w61
theorem b1848 : Ban 29 6 v1371 := smallByCut p31_19 w42
theorem b1849 : Ban 29 6 v1372 := smallByCut p31_23 w28
theorem b1850 : Ban 29 6 v1373 := smallByCut p31_15 w52
theorem b1851 : Ban 29 6 v1374 := smallByCut p31_19 w42
theorem b1852 : Ban 29 6 v1375 := smallByCut p31_15 w28
theorem b1853 : Ban 29 6 v1376 := smallByCut p31_21 w42
theorem b1854 : Ban 29 6 v1377 := smallByCut p31_13 w42
theorem b1855 : Ban 29 6 v1378 := smallByCut p31_21 w42
theorem b1856 : Ban 29 6 v1379 := smallByCut p31_13 w42
theorem b1857 : Ban 29 6 v1380 := smallByCut p31_13 w42
theorem b1858 : Ban 29 6 v1381 := smallByCut p31_15 w61
theorem b1859 : Ban 29 6 v1382 := smallByCut p31_15 w28
theorem b1860 : Ban 29 6 v1383 := smallByCut p31_13 w42
theorem b1861 : Ban 29 6 v1384 := smallByCut p31_23 w52
theorem b1862 : Ban 29 6 v1385 := checkedSmall
theorem b1863 : Ban 29 6 v1386 := viaPerm map31_1 map31_1 b1805 (by decide +kernel) (by decide +kernel)
theorem b1864 : Ban 29 6 v1387 := smallByCut p31_15 w28
theorem b1865 : Ban 29 6 v1388 := smallByCut p31_13 w42
theorem b1866 : Ban 29 6 v1389 := smallByCut p31_27 w60
theorem b1867 : Ban 29 6 v1390 := checkedSmall
theorem b1868 : Ban 29 6 v1391 := smallByCut p31_27 w60
theorem b1869 : Ban 29 6 v1392 := smallByCut p31_15 w52
theorem b1870 : Ban 29 6 v1393 := smallByCut p31_27 w6
theorem b1871 : Ban 29 6 v1394 := smallByCut p31_15 w52
theorem b1872 : Ban 29 6 v1395 := checkedSmall
theorem b1873 : Ban 29 6 v1396 := smallByCut p31_19 w42
theorem b1903 : Ban 29 6 v1397 := smallByCut p31_29 w30
theorem b1904 : Ban 29 6 v1421 := smallByCut p31_19 w42
theorem b1905 : Ban 29 6 v1422 := smallByCut p31_21 w42
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1906 : Ban 29 7 v1336 := viaBranch (ws := [v1337,v1338,v1339,v1340,v1341,v1342,v1343,v1344,v1345,v1346,v1347,v1348,v1349,v1350,v1351,v1352,v1353,v1354,v1355,v1356,v1357,v1358,v1359,v1360,v1361,v1362,v1363,v1364,v658,v1365,v1366,v1367,v1368,v1369,v1370,v1320,v1371,v1372,v1373,v1374,v1277,v1278,v1319,v1375,v1376,v1377,v1378,v1379,v1380,v1381,v1382,v1383,v1384,v1385,v1386,v1387,v1388,v1389,v1390,v1391,v1392,v1393,v1394,v1233,v1294,v1395,v1396,v1397,v1421,v1422]) (consBan b1813 (consBan b1814 (consBan b1815 (consBan b1816 (consBan b1817 (consBan b1818 (consBan b1819 (consBan b1820 (consBan b1821 (consBan b1822 (consBan b1823 (consBan b1824 (consBan b1825 (consBan b1826 (consBan b1827 (consBan b1828 (consBan b1829 (consBan b1830 (consBan b1831 (consBan b1832 (consBan b1833 (consBan b1834 (consBan b1835 (consBan b1836 (consBan b1837 (consBan b1838 (consBan b1839 (consBan b1840 (consBan b991 (consBan b1841 (consBan b1842 (consBan b1843 (consBan b1844 (consBan b1845 (consBan b1846 (consBan b1847 (consBan b1848 (consBan b1849 (consBan b1850 (consBan b1851 (consBan b1744 (consBan b1745 (consBan b1805 (consBan b1852 (consBan b1853 (consBan b1854 (consBan b1855 (consBan b1856 (consBan b1857 (consBan b1858 (consBan b1859 (consBan b1860 (consBan b1861 (consBan b1862 (consBan b1863 (consBan b1864 (consBan b1865 (consBan b1866 (consBan b1867 (consBan b1868 (consBan b1869 (consBan b1870 (consBan b1871 (consBan b1700 (consBan b1769 (consBan b1872 (consBan b1873 (consBan b1903 (consBan b1904 (consBan b1905 (nilBan 29 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1908 : Ban 29 7 v1422 := smallByCut p31_23 w28
theorem b1907 : Ban 29 7 v1380 := smallByCut p31_15 w28
theorem b1909 : Ban 29 7 v1423 := smallByCut p31_15 w61
theorem b1910 : Ban 29 7 v1424 := smallByCut p31_15 w28
theorem b1911 : Ban 29 7 v1425 := smallByCut p31_23 w52
theorem b1912 : Ban 29 7 v1426 := viaPerm map31_1 map31_1 b1663 (by decide +kernel) (by decide +kernel)
theorem b1913 : Ban 29 7 v1427 := viaPerm map31_1 map31_1 b1749 (by decide +kernel) (by decide +kernel)
theorem b1914 : Ban 29 7 v1428 := viaPerm map31_1 map31_1 b1811 (by decide +kernel) (by decide +kernel)
theorem b1915 : Ban 29 7 v1429 := smallByCut p31_15 w61
theorem b1916 : Ban 29 7 v1430 := smallByCut p31_15 w28
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1917 : Ban 29 8 v86 := viaBranch (ws := [v87,v88,v89,v90,v91,v93,v95,v96,v97,v99,v235,v236,v316,v317,v319,v345,v437,v439,v442,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591,v592,v593,v438,v594,v595,v596,v597,v598,v599,v600,v602,v604,v606,v607,v609,v611,v613,v766,v767,v654,v731,v996,v997,v998,v999,v1000,v1115,v1116,v1197,v1198,v1200,v1202,v1239,v1335,v1336,v1422,v1380,v1423,v1424,v1425,v1426,v1427,v1428,v1429,v1430]) (consBan b91 (consBan b92 (consBan b93 (consBan b95 (consBan b98 (consBan b190 (consBan b191 (consBan b192 (consBan b194 (consBan b332 (consBan b422 (consBan b506 (consBan b507 (consBan b509 (consBan b535 (consBan b634 (consBan b636 (consBan b639 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b819 (consBan b820 (consBan b821 (consBan b822 (consBan b823 (consBan b824 (consBan b825 (consBan b826 (consBan b635 (consBan b827 (consBan b828 (consBan b829 (consBan b830 (consBan b831 (consBan b832 (consBan b835 (consBan b937 (consBan b939 (consBan b940 (consBan b942 (consBan b944 (consBan b1042 (consBan b1109 (consBan b1171 (consBan b1255 (consBan b1445 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1574 (consBan b1575 (consBan b1662 (consBan b1663 (consBan b1666 (consBan b1668 (consBan b1749 (consBan b1811 (consBan b1812 (consBan b1906 (consBan b1908 (consBan b1907 (consBan b1909 (consBan b1910 (consBan b1911 (consBan b1912 (consBan b1913 (consBan b1914 (consBan b1915 (consBan b1916 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1919 : Ban 29 8 v595 := smallByCut p31_30 w20
theorem b1920 : Ban 29 8 v442 := smallByCut p31_29 w20
theorem b1921 : Ban 29 8 v1431 := smallByCut p31_27 w20
theorem b1922 : Ban 29 8 v1432 := viaPerm map31_2 map31_2 b1917 (by decide +kernel) (by decide +kernel)
theorem b1918 : Ban 29 8 v443 := smallByCut p31_30 w20
theorem b1923 : Ban 29 8 v1433 := smallByCut p31_27 w20
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w59 : Wide 12 6 v320 := viaSub (ws := [v320]) (consBan b710 (nilBan 12 6)) (by decide) (by decide +kernel)
theorem b1969 : Ban 29 8 v1209 := smallByCut p31_23 w59
theorem b1971 : Ban 29 7 v1435 := smallByCut p31_22 w42
theorem b1973 : Ban 29 7 v1436 := smallByCut p31_22 w42
theorem b2166 : Ban 29 7 v1438 := smallByCut p31_30 w20
theorem b2167 : Ban 29 7 v1618 := smallByCut p31_22 w42
theorem b2168 : Ban 29 7 v1619 := smallByCut p31_30 w20
theorem b1972 : Ban 29 7 v1437 := smallByCut p31_22 w42
theorem b2169 : Ban 29 7 v1620 := smallByCut p31_30 w20
theorem b2362 : Ban 29 7 v1621 := smallByCut p31_23 w59
theorem b2531 : Ban 29 7 v1787 := smallByCut p31_30 w60
theorem b2662 : Ban 29 7 v1945 := smallByCut p31_23 w61
theorem b2663 : Ban 29 7 v2070 := smallByCut p31_22 w42
theorem b2665 : Ban 29 7 v2071 := smallByCut p31_30 w60
theorem b2668 : Ban 29 7 v2073 := smallByCut p31_22 w42
theorem b2670 : Ban 29 7 v2075 := smallByCut p31_23 w61
theorem b2672 : Ban 29 7 v2077 := smallByCut p31_22 w42
theorem b2674 : Ban 29 7 v2079 := smallByCut p31_23 w61
theorem b2676 : Ban 29 7 v2081 := smallByCut p31_22 w42
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w55 : Wide 12 6 v449 := viaSub (ws := [v320,v449]) (consBan b1968 (consBan b2761 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b2678 : Ban 29 7 v2083 := smallByCut p31_15 w55
theorem b2679 : Ban 29 7 v2085 := smallByCut p31_15 w55
theorem b2764 : Ban 29 7 v2086 := smallByCut p31_15 w55
theorem b2766 : Ban 29 7 v2088 := smallByCut p31_22 w42
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w57 : Wide 12 5 v449 := viaSub (ws := [v320,v449]) (consBan b1664 (consBan b672 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b2768 : Ban 29 7 v2090 := smallByCut p31_15 w57
theorem b2770 : Ban 29 7 v2092 := smallByCut p31_27 w16
theorem b712 : Ban 12 5 v486 := smallByCut p15_14 w42
theorem b713 : Ban 12 5 v487 := smallByCut p15_14 w42
theorem b715 : Ban 12 5 v489 := smallByCut p15_14 w42
theorem b718 : Ban 12 5 v492 := smallByCut p15_14 w42
theorem b720 : Ban 12 5 v494 := smallByCut p15_14 w42
theorem b721 : Ban 12 5 v453 := smallByCut p15_14 w42
theorem b722 : Ban 12 5 v495 := smallByCut p15_14 w42
theorem b724 : Ban 12 5 v497 := smallByCut p15_14 w42
theorem b725 : Ban 12 5 v498 := checkedSmall
theorem b726 : Ban 12 5 v499 := smallByCut p15_14 w42
theorem solidb511 : Wide 12 4 v322 := solid b511
theorem b641 : Ban 12 4 v322 := bySubset solidb511
theorem b727 : Ban 12 4 v500 := smallByCut p15_14 w42
theorem b643 : Ban 12 4 v324 := smallByCut p15_13 w42
theorem b728 : Ban 12 4 v501 := smallByCut p15_14 w42
theorem solidb515 : Wide 12 4 v326 := solid b515
theorem b645 : Ban 12 4 v326 := bySubset solidb515
theorem b729 : Ban 12 4 v502 := smallByCut p15_14 w42
theorem b730 : Ban 12 4 v503 := checkedSmall
theorem b731 : Ban 12 4 v504 := smallByCut p15_14 w42
theorem solidb517 : Wide 12 4 v328 := solid b517
theorem b647 : Ban 12 4 v328 := bySubset solidb517
theorem b732 : Ban 12 4 v505 := smallByCut p15_14 w42
theorem b733 : Ban 12 4 v506 := checkedSmall
theorem b734 : Ban 12 4 v507 := smallByCut p15_14 w42
theorem b735 : Ban 12 4 v508 := smallByCut p15_14 w42
theorem b736 : Ban 12 4 v509 := checkedSmall
theorem b737 : Ban 12 4 v510 := checkedSmall
theorem b738 : Ban 12 4 v511 := checkedSmall
theorem b739 : Ban 12 4 v512 := checkedSmall
theorem b740 : Ban 12 4 v513 := checkedSmall
theorem b742 : Ban 12 4 v515 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b744 : Ban 12 5 v329 := viaBranch (ws := [v322,v500,v324,v501,v326,v502,v503,v504,v328,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516]) (consBan b641 (consBan b727 (consBan b643 (consBan b728 (consBan b645 (consBan b729 (consBan b730 (consBan b731 (consBan b647 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b738 (consBan b739 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b745 : Ban 12 5 v517 := smallByCut p15_14 w42
theorem b746 : Ban 12 5 v507 := smallByCut p15_14 w42
theorem b747 : Ban 12 5 v518 := smallByCut p15_14 w42
theorem b773 : Ban 12 5 v544 := smallByCut p15_14 w42
theorem b774 : Ban 12 5 v545 := checkedSmall
theorem b775 : Ban 12 5 v546 := smallByCut p15_14 w42
theorem b777 : Ban 12 5 v548 := smallByCut p15_14 w42
theorem b799 : Ban 12 5 v569 := smallByCut p15_14 w42
theorem b800 : Ban 12 5 v570 := checkedSmall
theorem b801 : Ban 12 5 v571 := checkedSmall
theorem b802 : Ban 12 5 v572 := checkedSmall
theorem b803 : Ban 12 5 v573 := checkedSmall
theorem b804 : Ban 12 5 v574 := checkedSmall
theorem b805 : Ban 12 5 v575 := checkedSmall
theorem b806 : Ban 12 5 v576 := checkedSmall
theorem b807 : Ban 12 5 v577 := checkedSmall
theorem b808 : Ban 12 5 v578 := checkedSmall
theorem b809 : Ban 12 5 v579 := checkedSmall
theorem b810 : Ban 12 5 v580 := checkedSmall
theorem b811 : Ban 12 5 v581 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b812 : Ban 12 6 v446 := viaBranch (ws := [v485,v445,v486,v444,v487,v488,v489,v490,v491,v327,v492,v493,v441,v494,v453,v495,v449,v496,v450,v497,v498,v499,v329,v517,v507,v518,v519,v544,v545,v546,v547,v548,v549,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581]) (consBan b711 (consBan b667 (consBan b712 (consBan b640 (consBan b713 (consBan b714 (consBan b715 (consBan b716 (consBan b717 (consBan b666 (consBan b718 (consBan b719 (consBan b668 (consBan b720 (consBan b721 (consBan b722 (consBan b672 (consBan b723 (consBan b673 (consBan b724 (consBan b725 (consBan b726 (consBan b744 (consBan b745 (consBan b746 (consBan b747 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b798 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b808 (consBan b809 (consBan b810 (consBan b811 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2772 : Ban 12 5 v2096 := checkedSmall
theorem b2773 : Ban 12 5 v2097 := checkedSmall
theorem b2774 : Ban 12 5 v2098 := smallByCut p15_13 w42
theorem b2775 : Ban 12 5 v2099 := checkedSmall
theorem b2776 : Ban 12 5 v2100 := smallByCut p15_13 w42
theorem b2777 : Ban 12 5 v2101 := checkedSmall
theorem b2778 : Ban 12 5 v2102 := checkedSmall
theorem b2779 : Ban 12 5 v2103 := checkedSmall
theorem b2782 : Ban 12 5 v2106 := checkedSmall
theorem b2783 : Ban 12 5 v2107 := checkedSmall
theorem b2784 : Ban 12 5 v2108 := checkedSmall
theorem b2785 : Ban 12 5 v2109 := checkedSmall
theorem b2786 : Ban 12 5 v2110 := checkedSmall
theorem b2787 : Ban 12 5 v2111 := checkedSmall
theorem b2788 : Ban 12 5 v2112 := checkedSmall
theorem b2789 : Ban 12 5 v2113 := checkedSmall
theorem b2790 : Ban 12 4 v2114 := checkedSmall
theorem b2791 : Ban 12 4 v2115 := checkedSmall
theorem b2792 : Ban 12 4 v2116 := checkedSmall
theorem b2095 : Ban 12 4 v1552 := checkedSmall
theorem b2793 : Ban 12 4 v2117 := checkedSmall
theorem b2097 : Ban 12 4 v1554 := checkedSmall
theorem b2794 : Ban 12 4 v2118 := checkedSmall
theorem b2795 : Ban 12 4 v2119 := smallByCut p15_14 w38
theorem b2796 : Ban 12 4 v2120 := checkedSmall
theorem b2797 : Ban 12 4 v2121 := checkedSmall
theorem b2798 : Ban 12 4 v2122 := checkedSmall
theorem b2799 : Ban 12 4 v2123 := checkedSmall
theorem b2800 : Ban 12 4 v2124 := checkedSmall
theorem b2801 : Ban 12 4 v2125 := checkedSmall
theorem b2802 : Ban 12 4 v2126 := checkedSmall
theorem b2803 : Ban 12 4 v2127 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2804 : Ban 12 5 v537 := viaBranch (ws := [v2114,v2115,v2116,v1552,v2117,v528,v1554,v530,v2118,v2119,v2120,v2121,v2122,v2123,v539,v2124,v2125,v540,v2126,v542,v2127,v538]) (consBan b2790 (consBan b2791 (consBan b2792 (consBan b2095 (consBan b2793 (consBan b756 (consBan b2097 (consBan b758 (consBan b2794 (consBan b2795 (consBan b2796 (consBan b2797 (consBan b2798 (consBan b2799 (consBan b767 (consBan b2800 (consBan b2801 (consBan b768 (consBan b2802 (consBan b770 (consBan b2803 (consBan b766 (nilBan 12 4))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2805 : Ban 12 5 v2128 := checkedSmall
theorem b2806 : Ban 12 5 v2129 := checkedSmall
theorem b2807 : Ban 12 5 v2130 := checkedSmall
theorem b2808 : Ban 12 4 v2131 := checkedSmall
theorem b2809 : Ban 12 4 v2132 := checkedSmall
theorem b2810 : Ban 12 4 v2133 := checkedSmall
theorem b2811 : Ban 12 4 v2134 := checkedSmall
theorem b2812 : Ban 12 4 v2135 := checkedSmall
theorem b2813 : Ban 12 4 v2136 := checkedSmall
theorem b2814 : Ban 12 4 v2137 := checkedSmall
theorem b2815 : Ban 12 4 v2138 := checkedSmall
theorem b2119 : Ban 12 4 v1574 := checkedSmall
theorem b2816 : Ban 12 4 v2139 := checkedSmall
theorem b2817 : Ban 12 4 v2140 := checkedSmall
theorem b2818 : Ban 12 4 v2141 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2819 : Ban 12 5 v562 := viaBranch (ws := [v2131,v809,v2132,v2133,v2134,v2135,v556,v2136,v558,v559,v2137,v563,v2138,v1574,v2139,v2140,v2141]) (consBan b2808 (consBan b1148 (consBan b2809 (consBan b2810 (consBan b2811 (consBan b2812 (consBan b784 (consBan b2813 (consBan b786 (consBan b787 (consBan b2814 (consBan b791 (consBan b2815 (consBan b2119 (consBan b2816 (consBan b2817 (consBan b2818 (nilBan 12 4)))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2820 : Ban 12 5 v2142 := checkedSmall
theorem b2821 : Ban 12 5 v2143 := checkedSmall
theorem b2822 : Ban 12 5 v2144 := checkedSmall
theorem b2823 : Ban 12 5 v2145 := checkedSmall
theorem b2824 : Ban 12 5 v2146 := checkedSmall
theorem b2320 : Ban 12 5 v1756 := smallByCut p15_14 w38
theorem b2825 : Ban 12 5 v2147 := checkedSmall
theorem b2826 : Ban 12 5 v2148 := checkedSmall
theorem b2827 : Ban 12 5 v2149 := checkedSmall
theorem b2828 : Ban 12 5 v2150 := checkedSmall
theorem b2154 : Ban 12 5 v1608 := checkedSmall
theorem b2829 : Ban 12 5 v2151 := checkedSmall
theorem b2156 : Ban 12 5 v1610 := checkedSmall
theorem b2830 : Ban 12 5 v2152 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2831 : Ban 12 6 v575 := viaBranch (ws := [v2096,v2097,v2098,v2099,v820,v2100,v2101,v2102,v2103,v1480,v2104,v1481,v2105,v2106,v2107,v2108,v453,v495,v342,v1123,v1155,v450,v497,v2109,v2110,v2111,v2112,v2113,v537,v2128,v2129,v2130,v562,v2142,v2143,v547,v548,v2144,v2145,v2146,v1756,v2147,v2148,v2149,v2150,v577,v1608,v2151,v578,v1610,v580,v2152,v576]) (consBan b2772 (consBan b2773 (consBan b2774 (consBan b2775 (consBan b1161 (consBan b2776 (consBan b2777 (consBan b2778 (consBan b2779 (consBan b2018 (consBan b2780 (consBan b2019 (consBan b2781 (consBan b2782 (consBan b2783 (consBan b2784 (consBan b721 (consBan b722 (consBan b1368 (consBan b1582 (consBan b1616 (consBan b673 (consBan b724 (consBan b2785 (consBan b2786 (consBan b2787 (consBan b2788 (consBan b2789 (consBan b2804 (consBan b2805 (consBan b2806 (consBan b2807 (consBan b2819 (consBan b2820 (consBan b2821 (consBan b776 (consBan b777 (consBan b2822 (consBan b2823 (consBan b2824 (consBan b2320 (consBan b2825 (consBan b2826 (consBan b2827 (consBan b2828 (consBan b807 (consBan b2154 (consBan b2829 (consBan b808 (consBan b2156 (consBan b810 (consBan b2830 (consBan b806 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w49 : Wide 12 6 v575 := viaSub (ws := [v320,v446,v481,v575]) (consBan b710 (consBan b812 (consBan b2771 (consBan b2831 (nilBan 12 6))))) (by decide) (by decide +kernel)
theorem b3099 : Ban 12 6 v446 := bySubset w49
theorem b3100 : Ban 12 6 v478 := viaPerm map23_2 map23_2 b3099 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w53 : Wide 12 6 v478 := viaSub (ws := [v320,v478]) (consBan b1968 (consBan b3100 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b2833 : Ban 29 7 v2094 := smallByCut p31_23 w53
theorem b2834 : Ban 29 7 v2153 := smallByCut p31_30 w20
theorem b2836 : Ban 29 7 v2154 := smallByCut p31_22 w42
theorem b2912 : Ban 29 7 v2156 := smallByCut p31_23 w59
theorem b2913 : Ban 29 7 v2223 := smallByCut p31_23 w59
theorem b2915 : Ban 29 7 v2224 := smallByCut p31_22 w42
theorem b2961 : Ban 29 7 v2226 := smallByCut p31_29 w60
theorem b2963 : Ban 29 7 v2267 := smallByCut p31_22 w42
theorem b2998 : Ban 29 7 v2269 := smallByCut p31_15 w52
theorem b3102 : Ban 29 7 v1207 := smallByCut p31_29 w60
theorem b3104 : Ban 29 7 v2302 := smallByCut p31_29 w16
theorem b3106 : Ban 29 7 v2304 := smallByCut p31_29 w16
theorem b3108 : Ban 29 7 v2306 := smallByCut p31_22 w42
theorem b3110 : Ban 29 7 v2308 := smallByCut p31_15 w57
theorem b3111 : Ban 29 7 v2310 := smallByCut p31_15 w55
theorem b3113 : Ban 29 7 v2311 := smallByCut p31_15 w55
theorem b3115 : Ban 29 7 v2313 := smallByCut p31_15 w57
theorem b3116 : Ban 29 7 v2315 := smallByCut p31_22 w42
theorem b3117 : Ban 29 7 v2316 := smallByCut p31_23 w59
theorem b3118 : Ban 29 7 v2317 := smallByCut p31_23 w59
theorem b2914 : Ban 29 7 v2225 := smallByCut p31_22 w42
theorem b3119 : Ban 29 7 v2318 := smallByCut p31_27 w60
theorem b3120 : Ban 29 7 v2319 := smallByCut p31_22 w42
theorem b3121 : Ban 29 7 v2320 := smallByCut p31_27 w16
theorem b3122 : Ban 29 7 v2321 := smallByCut p31_27 w16
theorem b3123 : Ban 29 7 v2322 := smallByCut p31_27 w60
theorem b3124 : Ban 29 7 v2323 := smallByCut p31_27 w16
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w54 : Wide 12 6 v446 := viaSub (ws := [v320,v446]) (consBan b1968 (consBan b3099 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b3105 : Ban 29 7 v2305 := smallByCut p31_23 w54
theorem b3107 : Ban 29 7 v2307 := smallByCut p31_22 w42
theorem b3125 : Ban 29 7 v2324 := smallByCut p31_15 w57
theorem b3126 : Ban 29 7 v2325 := smallByCut p31_15 w55
theorem b3127 : Ban 29 7 v2326 := smallByCut p31_15 w55
theorem b3128 : Ban 29 7 v2327 := smallByCut p31_15 w57
theorem b3130 : Ban 29 7 v1203 := smallByCut p31_30 w60
theorem b3131 : Ban 29 7 v2328 := smallByCut p31_22 w42
theorem b3132 : Ban 29 7 v2329 := smallByCut p31_23 w59
theorem b3134 : Ban 29 7 v2330 := smallByCut p31_22 w42
theorem b3135 : Ban 29 7 v2332 := smallByCut p31_23 w59
theorem b3137 : Ban 29 7 v2333 := smallByCut p31_15 w61
theorem b3139 : Ban 29 7 v2335 := smallByCut p31_22 w42
theorem b3140 : Ban 29 7 v2337 := smallByCut p31_15 w55
theorem b3141 : Ban 29 7 v2338 := smallByCut p31_15 w55
theorem b3143 : Ban 29 7 v2339 := smallByCut p31_15 w55
theorem b3145 : Ban 29 7 v2341 := smallByCut p31_22 w42
theorem b3147 : Ban 29 7 v2343 := smallByCut p31_15 w61
theorem b3149 : Ban 29 7 v2345 := smallByCut p31_15 w57
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b3150 : Ban 29 8 v1434 := viaBranch (ws := [v1435,v345,v1436,v1438,v1618,v1619,v1437,v1620,v1621,v1787,v1945,v2070,v2071,v2073,v2075,v2077,v2079,v2081,v2083,v2085,v2086,v2088,v2090,v2092,v603,v2094,v2153,v2154,v2156,v2223,v2224,v2226,v2267,v1116,v2269,v1207,v2302,v2304,v2306,v2308,v2310,v2311,v2313,v2315,v2316,v2317,v2225,v2318,v2319,v2320,v2321,v2322,v2323,v2305,v2307,v2324,v2325,v2326,v2327,v1203,v2328,v2329,v2330,v2332,v2333,v2335,v2337,v2338,v2339,v2341,v2343,v2345]) (consBan b1971 (consBan b634 (consBan b1973 (consBan b2166 (consBan b2167 (consBan b2168 (consBan b1972 (consBan b2169 (consBan b2362 (consBan b2531 (consBan b2662 (consBan b2663 (consBan b2665 (consBan b2668 (consBan b2670 (consBan b2672 (consBan b2674 (consBan b2676 (consBan b2678 (consBan b2679 (consBan b2764 (consBan b2766 (consBan b2768 (consBan b2770 (consBan b936 (consBan b2833 (consBan b2834 (consBan b2836 (consBan b2912 (consBan b2913 (consBan b2915 (consBan b2961 (consBan b2963 (consBan b1662 (consBan b2998 (consBan b3102 (consBan b3104 (consBan b3106 (consBan b3108 (consBan b3110 (consBan b3111 (consBan b3113 (consBan b3115 (consBan b3116 (consBan b3117 (consBan b3118 (consBan b2914 (consBan b3119 (consBan b3120 (consBan b3121 (consBan b3122 (consBan b3123 (consBan b3124 (consBan b3105 (consBan b3107 (consBan b3125 (consBan b3126 (consBan b3127 (consBan b3128 (consBan b3130 (consBan b3131 (consBan b3132 (consBan b3134 (consBan b3135 (consBan b3137 (consBan b3139 (consBan b3140 (consBan b3141 (consBan b3143 (consBan b3145 (consBan b3147 (consBan b3149 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3152 : Ban 29 8 v1203 := smallByCut p31_30 w20
theorem b3154 : Ban 29 8 v2079 := smallByCut p31_23 w59
theorem b3155 : Ban 29 8 v2347 := smallByCut p31_15 w59
theorem b3156 : Ban 29 8 v2348 := viaPerm map31_1 map31_1 b3150 (by decide +kernel) (by decide +kernel)
theorem b3157 : Ban 29 8 v2349 := smallByCut p31_30 w20
theorem b3158 : Ban 29 8 v2350 := smallByCut p31_15 w59
theorem b3159 : Ban 29 8 v2351 := smallByCut p31_27 w20
theorem b3160 : Ban 29 8 v2352 := viaPerm map31_6 map31_8 b1917 (by decide +kernel) (by decide +kernel)
theorem b3161 : Ban 29 8 v2353 := smallByCut p31_29 w20
theorem b3162 : Ban 29 8 v2354 := smallByCut p31_27 w20
theorem b3163 : Ban 29 8 v1217 := smallByCut p31_23 w59
theorem b3164 : Ban 29 8 v2355 := viaPerm map31_4 map31_4 b3150 (by decide +kernel) (by decide +kernel)
theorem b3151 : Ban 29 8 v1211 := smallByCut p31_29 w20
theorem b3165 : Ban 29 8 v2356 := smallByCut p31_23 w59
theorem b3166 : Ban 29 8 v2357 := smallByCut p31_15 w59
theorem b3167 : Ban 29 8 v2358 := viaPerm map31_5 map31_5 b3150 (by decide +kernel) (by decide +kernel)
theorem b3168 : Ban 29 8 v2359 := smallByCut p31_29 w20
theorem b3169 : Ban 29 8 v2360 := smallByCut p31_15 w59
theorem b3170 : Ban 29 8 v2361 := smallByCut p31_23 w59
theorem b3171 : Ban 29 8 v2362 := viaPerm map31_8 map31_6 b3150 (by decide +kernel) (by decide +kernel)
theorem b3172 : Ban 29 8 v2363 := smallByCut p31_27 w20
theorem b3153 : Ban 29 8 v2080 := smallByCut p31_23 w59
theorem b3173 : Ban 29 8 v2364 := smallByCut p31_15 w59
theorem b3174 : Ban 29 8 v2365 := viaPerm map31_9 map31_7 b3150 (by decide +kernel) (by decide +kernel)
theorem b3175 : Ban 29 8 v2366 := smallByCut p31_27 w20
theorem b3176 : Ban 29 8 v2367 := smallByCut p31_15 w59
theorem b3177 : Ban 29 8 v2368 := smallByCut p31_15 w59
theorem b3178 : Ban 29 7 v2370 := smallByCut p31_29 w60
theorem b3180 : Ban 29 7 v1355 := smallByCut p31_30 w60
theorem b3181 : Ban 29 7 v1344 := smallByCut p31_29 w60
theorem b3182 : Ban 29 7 v2372 := smallByCut p31_27 w60
theorem b3183 : Ban 29 7 v2373 := viaPerm map31_2 map31_2 b1906 (by decide +kernel) (by decide +kernel)
theorem b3179 : Ban 29 7 v2371 := smallByCut p31_30 w60
theorem b3184 : Ban 29 7 v2374 := smallByCut p31_27 w60
theorem b3185 : Ban 29 7 v2375 := smallByCut p31_23 w61
theorem b3187 : Ban 29 7 v2376 := smallByCut p31_30 w60
theorem b3189 : Ban 29 7 v2378 := smallByCut p31_23 w61
theorem b3190 : Ban 29 7 v2380 := smallByCut p31_15 w61
theorem b3191 : Ban 29 7 v2381 := smallByCut p31_15 w59
theorem b3192 : Ban 29 7 v2382 := smallByCut p31_30 w60
theorem b3193 : Ban 29 7 v2383 := smallByCut p31_15 w61
theorem b3194 : Ban 29 7 v2384 := smallByCut p31_30 w60
theorem b3195 : Ban 29 7 v2385 := smallByCut p31_30 w60
theorem b3196 : Ban 29 7 v2386 := smallByCut p31_15 w55
theorem b3197 : Ban 29 7 v2387 := smallByCut p31_30 w60
theorem b3198 : Ban 29 7 v2388 := smallByCut p31_30 w60
theorem b3199 : Ban 29 6 v2391 := smallByCut p31_14 w42
theorem b3200 : Ban 29 6 v2392 := checkedSmall
theorem b3201 : Ban 29 6 v2393 := smallByCut p31_29 w60
theorem b3202 : Ban 29 6 v2394 := checkedSmall
theorem b3203 : Ban 29 6 v2395 := smallByCut p31_13 w42
theorem b3204 : Ban 29 6 v2396 := checkedSmall
theorem b3205 : Ban 29 6 v2397 := smallByCut p31_14 w42
theorem b3206 : Ban 29 6 v2398 := checkedSmall
theorem b3207 : Ban 29 6 v2399 := smallByCut p31_13 w42
theorem b3208 : Ban 29 6 v2400 := checkedSmall
theorem b3209 : Ban 29 6 v2401 := smallByCut p31_30 w60
theorem b3210 : Ban 29 6 v2402 := checkedSmall
theorem b3211 : Ban 29 6 v2403 := smallByCut p31_14 w42
theorem b3212 : Ban 29 6 v2404 := checkedSmall
theorem b3213 : Ban 29 6 v2405 := smallByCut p31_13 w42
theorem b3214 : Ban 29 6 v2406 := checkedSmall
theorem b3215 : Ban 29 6 v2407 := checkedSmall
theorem b3216 : Ban 29 6 v2408 := smallByCut p31_27 w60
theorem b3217 : Ban 29 6 v2409 := smallByCut p31_27 w60
theorem b3218 : Ban 29 6 v2080 := smallByCut p31_19 w42
theorem b3219 : Ban 29 6 v2410 := smallByCut p31_19 w42
theorem b3220 : Ban 29 6 v2411 := smallByCut p31_15 w61
theorem b3221 : Ban 29 6 v2412 := smallByCut p31_15 w61
theorem b3222 : Ban 29 6 v2344 := smallByCut p31_13 w42
theorem b3223 : Ban 29 6 v2413 := smallByCut p31_15 w61
theorem b3224 : Ban 29 6 v2361 := smallByCut p31_19 w42
theorem b3225 : Ban 29 6 v2414 := smallByCut p31_19 w42
theorem b3226 : Ban 29 6 v2367 := smallByCut p31_13 w42
theorem b3227 : Ban 29 6 v2415 := smallByCut p31_15 w61
theorem b3228 : Ban 29 6 v2416 := smallByCut p31_15 w61
theorem b3229 : Ban 29 6 v2417 := smallByCut p31_15 w61
theorem b3230 : Ban 29 6 v2418 := smallByCut p31_19 w42
theorem b3231 : Ban 29 6 v2419 := smallByCut p31_19 w42
theorem b3232 : Ban 29 6 v2364 := smallByCut p31_13 w42
theorem b3233 : Ban 29 6 v2420 := smallByCut p31_19 w42
theorem b3234 : Ban 29 6 v2421 := checkedSmall
theorem b3235 : Ban 29 6 v2422 := checkedSmall
theorem b3236 : Ban 29 6 v2423 := checkedSmall
theorem b3237 : Ban 29 6 v2424 := smallByCut p31_19 w42
theorem b3238 : Ban 29 6 v2425 := checkedSmall
theorem b3239 : Ban 29 6 v2426 := smallByCut p31_27 w60
theorem b3240 : Ban 29 6 v2427 := smallByCut p31_27 w60
theorem b3241 : Ban 29 6 v2428 := smallByCut p31_27 w60
theorem b3242 : Ban 29 6 v2429 := smallByCut p31_19 w42
theorem b3243 : Ban 29 6 v2430 := smallByCut p31_19 w42
theorem b3244 : Ban 29 6 v2431 := smallByCut p31_23 w61
theorem b3245 : Ban 29 6 v2432 := smallByCut p31_23 w61
theorem b3246 : Ban 29 6 v2433 := smallByCut p31_19 w42
theorem b3247 : Ban 29 6 v2434 := smallByCut p31_15 w61
theorem b3248 : Ban 29 6 v2435 := smallByCut p31_15 w61
theorem b3249 : Ban 29 6 v2436 := smallByCut p31_15 w61
theorem b3250 : Ban 29 6 v2437 := smallByCut p31_15 w61
theorem b3251 : Ban 29 6 v2438 := smallByCut p31_19 w42
theorem b3252 : Ban 29 6 v2439 := checkedSmall
theorem b3253 : Ban 29 6 v2440 := smallByCut p31_27 w60
theorem b3254 : Ban 29 6 v2441 := smallByCut p31_27 w60
theorem b3255 : Ban 29 6 v2442 := smallByCut p31_27 w60
theorem b3256 : Ban 29 6 v2443 := smallByCut p31_19 w42
theorem b3257 : Ban 29 6 v2444 := smallByCut p31_19 w42
theorem b3258 : Ban 29 6 v2445 := smallByCut p31_23 w61
theorem b3259 : Ban 29 6 v2446 := smallByCut p31_23 w61
theorem b3260 : Ban 29 6 v2447 := smallByCut p31_19 w42
theorem b3261 : Ban 29 6 v2448 := smallByCut p31_15 w61
theorem b3262 : Ban 29 6 v2449 := smallByCut p31_15 w61
theorem b3263 : Ban 29 6 v2450 := smallByCut p31_15 w61
theorem b3264 : Ban 29 6 v2451 := smallByCut p31_15 w61
theorem b3265 : Ban 29 6 v2452 := smallByCut p31_23 w61
theorem b3266 : Ban 29 6 v2453 := smallByCut p31_19 w42
theorem b3267 : Ban 29 6 v2454 := smallByCut p31_23 w61
theorem b3268 : Ban 29 6 v2455 := smallByCut p31_19 w42
theorem b3269 : Ban 29 6 v2456 := smallByCut p31_15 w61
theorem b3270 : Ban 29 6 v2457 := smallByCut p31_15 w61
theorem b3271 : Ban 29 6 v2458 := smallByCut p31_15 w61
theorem b3272 : Ban 29 6 v2459 := smallByCut p31_19 w42
theorem b3273 : Ban 29 6 v2460 := smallByCut p31_19 w42
theorem b3274 : Ban 29 6 v2461 := smallByCut p31_15 w61
theorem b3275 : Ban 29 6 v2462 := smallByCut p31_19 w42
theorem b3276 : Ban 29 6 v2463 := smallByCut p31_15 w61
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b3277 : Ban 29 7 v2390 := viaBranch (ws := [v2391,v2392,v2393,v2394,v2395,v2396,v2397,v2398,v2399,v2400,v2401,v2402,v2403,v2404,v2405,v2406,v2407,v2408,v2409,v2080,v2410,v2411,v2412,v2344,v2413,v2361,v2414,v2367,v2415,v2416,v2417,v2418,v2419,v2364,v2420,v2421,v1370,v2422,v2423,v2424,v2425,v2426,v2427,v2428,v2429,v2430,v2431,v2432,v2433,v2434,v2435,v2436,v2437,v2438,v2439,v2440,v2441,v2442,v2443,v2444,v2445,v2446,v2447,v2448,v2449,v2450,v2451,v2452,v2453,v2454,v2455,v2456,v2457,v2458,v2459,v2460,v2461,v2462,v2463]) (consBan b3199 (consBan b3200 (consBan b3201 (consBan b3202 (consBan b3203 (consBan b3204 (consBan b3205 (consBan b3206 (consBan b3207 (consBan b3208 (consBan b3209 (consBan b3210 (consBan b3211 (consBan b3212 (consBan b3213 (consBan b3214 (consBan b3215 (consBan b3216 (consBan b3217 (consBan b3218 (consBan b3219 (consBan b3220 (consBan b3221 (consBan b3222 (consBan b3223 (consBan b3224 (consBan b3225 (consBan b3226 (consBan b3227 (consBan b3228 (consBan b3229 (consBan b3230 (consBan b3231 (consBan b3232 (consBan b3233 (consBan b3234 (consBan b1846 (consBan b3235 (consBan b3236 (consBan b3237 (consBan b3238 (consBan b3239 (consBan b3240 (consBan b3241 (consBan b3242 (consBan b3243 (consBan b3244 (consBan b3245 (consBan b3246 (consBan b3247 (consBan b3248 (consBan b3249 (consBan b3250 (consBan b3251 (consBan b3252 (consBan b3253 (consBan b3254 (consBan b3255 (consBan b3256 (consBan b3257 (consBan b3258 (consBan b3259 (consBan b3260 (consBan b3261 (consBan b3262 (consBan b3263 (consBan b3264 (consBan b3265 (consBan b3266 (consBan b3267 (consBan b3268 (consBan b3269 (consBan b3270 (consBan b3271 (consBan b3272 (consBan b3273 (consBan b3274 (consBan b3275 (consBan b3276 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3278 : Ban 29 7 v2389 := viaPerm map31_6 map31_8 b3277 (by decide +kernel) (by decide +kernel)
theorem b3279 : Ban 29 6 v2465 := smallByCut p31_14 w42
theorem b3280 : Ban 29 6 v2466 := smallByCut p31_29 w60
theorem b3281 : Ban 29 6 v2467 := smallByCut p31_13 w42
theorem b3282 : Ban 29 6 v2468 := smallByCut p31_14 w42
theorem b3283 : Ban 29 6 v2469 := smallByCut p31_13 w42
theorem b3284 : Ban 29 6 v2470 := smallByCut p31_30 w60
theorem b3285 : Ban 29 6 v2471 := smallByCut p31_14 w42
theorem b3286 : Ban 29 6 v2472 := smallByCut p31_13 w42
theorem b3287 : Ban 29 6 v2473 := checkedSmall
theorem b3288 : Ban 29 6 v2474 := smallByCut p31_27 w60
theorem b3289 : Ban 29 6 v2379 := smallByCut p31_19 w42
theorem b3290 : Ban 29 6 v2475 := smallByCut p31_15 w61
theorem b3291 : Ban 29 6 v2476 := smallByCut p31_13 w42
theorem b3292 : Ban 29 6 v2477 := smallByCut p31_19 w42
theorem b3293 : Ban 29 6 v2478 := smallByCut p31_13 w42
theorem b3294 : Ban 29 6 v2479 := smallByCut p31_15 w61
theorem b3295 : Ban 29 6 v2480 := smallByCut p31_19 w42
theorem b3296 : Ban 29 6 v2481 := smallByCut p31_13 w42
theorem b3297 : Ban 29 6 v2482 := smallByCut p31_19 w42
theorem b3298 : Ban 29 6 v2483 := smallByCut p31_19 w42
theorem b3299 : Ban 29 6 v2484 := smallByCut p31_19 w42
theorem b3300 : Ban 29 6 v2485 := checkedSmall
theorem b3301 : Ban 29 6 v2486 := smallByCut p31_27 w60
theorem b3302 : Ban 29 6 v2487 := checkedSmall
theorem b3303 : Ban 29 6 v2488 := checkedSmall
theorem b3304 : Ban 29 6 v2489 := checkedSmall
theorem b3305 : Ban 29 6 v2490 := checkedSmall
theorem b3306 : Ban 29 6 v2491 := checkedSmall
theorem b3307 : Ban 29 6 v2492 := smallByCut p31_27 w60
theorem b3308 : Ban 29 6 v2493 := checkedSmall
theorem b3309 : Ban 29 6 v2494 := checkedSmall
theorem b3310 : Ban 29 6 v2495 := checkedSmall
theorem b3311 : Ban 29 6 v2496 := checkedSmall
theorem b3312 : Ban 29 6 v2497 := smallByCut p31_23 w61
theorem b3313 : Ban 29 6 v2498 := smallByCut p31_23 w61
theorem b3314 : Ban 29 6 v2499 := smallByCut p31_15 w61
theorem b3315 : Ban 29 6 v2500 := smallByCut p31_15 w61
theorem b3317 : Ban 29 6 v2501 := smallByCut p31_27 w60
theorem b3318 : Ban 29 6 v2503 := smallByCut p31_19 w42
theorem b3319 : Ban 29 6 v2504 := smallByCut p31_27 w60
theorem b3320 : Ban 29 6 v2505 := smallByCut p31_15 w61
theorem b3321 : Ban 29 6 v2506 := smallByCut p31_19 w42
theorem b3322 : Ban 29 6 v2507 := smallByCut p31_15 w61
theorem b3323 : Ban 29 6 v2508 := smallByCut p31_19 w42
theorem b3324 : Ban 29 6 v2509 := smallByCut p31_15 w61
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b3325 : Ban 29 7 v2461 := viaBranch (ws := [v2465,v2466,v2467,v2468,v2469,v2470,v2471,v2472,v2473,v2474,v2379,v2475,v2476,v2477,v2478,v2479,v2480,v2481,v2482,v2483,v2484,v2485,v2486,v2487,v2488,v2489,v2490,v2491,v2492,v2493,v2494,v2495,v2496,v2497,v2498,v2499,v2500,v2407,v2409,v2501,v2503,v2504,v2505,v2506,v2507,v2508,v2509,v2463,v2462]) (consBan b3279 (consBan b3280 (consBan b3281 (consBan b3282 (consBan b3283 (consBan b3284 (consBan b3285 (consBan b3286 (consBan b3287 (consBan b3288 (consBan b3289 (consBan b3290 (consBan b3291 (consBan b3292 (consBan b3293 (consBan b3294 (consBan b3295 (consBan b3296 (consBan b3297 (consBan b3298 (consBan b3299 (consBan b3300 (consBan b3301 (consBan b3302 (consBan b3303 (consBan b3304 (consBan b3305 (consBan b3306 (consBan b3307 (consBan b3308 (consBan b3309 (consBan b3310 (consBan b3311 (consBan b3312 (consBan b3313 (consBan b3314 (consBan b3315 (consBan b3215 (consBan b3217 (consBan b3317 (consBan b3318 (consBan b3319 (consBan b3320 (consBan b3321 (consBan b3322 (consBan b3323 (consBan b3324 (consBan b3276 (consBan b3275 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3326 : Ban 29 7 v2464 := viaPerm map31_6 map31_8 b3325 (by decide +kernel) (by decide +kernel)
theorem b3327 : Ban 29 7 v2510 := smallByCut p31_27 w60
theorem b3328 : Ban 29 7 v2511 := viaPerm map31_6 map31_8 b1906 (by decide +kernel) (by decide +kernel)
theorem b3329 : Ban 29 7 v2512 := smallByCut p31_29 w60
theorem b3330 : Ban 29 7 v2513 := smallByCut p31_27 w60
theorem b3331 : Ban 29 7 v2514 := smallByCut p31_23 w61
theorem b3332 : Ban 29 7 v2515 := smallByCut p31_23 w59
theorem b3186 : Ban 29 7 v2377 := smallByCut p31_29 w60
theorem b3333 : Ban 29 7 v2516 := smallByCut p31_23 w61
theorem b3334 : Ban 29 7 v2517 := smallByCut p31_15 w61
theorem b3335 : Ban 29 7 v2518 := smallByCut p31_15 w59
theorem b3336 : Ban 29 7 v2519 := smallByCut p31_29 w60
theorem b3337 : Ban 29 7 v2520 := smallByCut p31_15 w61
theorem b3338 : Ban 29 7 v2521 := smallByCut p31_29 w60
theorem b3339 : Ban 29 7 v2522 := smallByCut p31_29 w60
theorem b3340 : Ban 29 7 v2523 := smallByCut p31_15 w50
theorem b3341 : Ban 29 7 v2524 := smallByCut p31_15 w50
theorem b3342 : Ban 29 7 v2525 := smallByCut p31_29 w60
theorem b3343 : Ban 29 7 v2526 := smallByCut p31_29 w60
theorem b3344 : Ban 29 7 v2527 := viaPerm map31_2 map31_2 b3277 (by decide +kernel) (by decide +kernel)
theorem b3345 : Ban 29 7 v2528 := viaPerm map31_2 map31_2 b3325 (by decide +kernel) (by decide +kernel)
theorem b3346 : Ban 29 7 v2477 := smallByCut p31_23 w61
theorem b3347 : Ban 29 7 v2529 := smallByCut p31_23 w59
theorem b3348 : Ban 29 7 v2530 := smallByCut p31_27 w60
theorem b3188 : Ban 29 7 v2379 := smallByCut p31_23 w61
theorem b3349 : Ban 29 7 v2481 := smallByCut p31_15 w61
theorem b3350 : Ban 29 7 v2531 := smallByCut p31_15 w59
theorem b3351 : Ban 29 7 v2532 := smallByCut p31_27 w60
theorem b3352 : Ban 29 7 v2478 := smallByCut p31_15 w61
theorem b3353 : Ban 29 7 v2482 := smallByCut p31_27 w60
theorem b3354 : Ban 29 7 v2484 := smallByCut p31_27 w60
theorem b2049 : Ban 12 6 v470 := viaPerm map15_4 map15_3 b2048 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w44 : Wide 12 6 v470 := viaSub (ws := [v320,v470]) (consBan b710 (consBan b2049 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b3355 : Ban 29 7 v2408 := smallByCut p31_15 w44
theorem b3356 : Ban 29 7 v2474 := smallByCut p31_15 w44
theorem b3357 : Ban 29 7 v2533 := smallByCut p31_27 w60
theorem b3358 : Ban 29 7 v2534 := smallByCut p31_27 w60
theorem b3359 : Ban 29 7 v2535 := smallByCut p31_15 w59
theorem b3360 : Ban 29 7 v2536 := smallByCut p31_23 w61
theorem b3361 : Ban 29 7 v2537 := smallByCut p31_15 w61
theorem b3362 : Ban 29 7 v2538 := smallByCut p31_15 w61
theorem b3364 : Ban 29 7 v2539 := smallByCut p31_23 w61
theorem b3366 : Ban 29 7 v2541 := smallByCut p31_23 w61
theorem b3363 : Ban 29 7 v2540 := smallByCut p31_15 w61
theorem b3365 : Ban 29 7 v2542 := smallByCut p31_15 w61
theorem b3367 : Ban 29 7 v2543 := smallByCut p31_15 w61
theorem b3368 : Ban 29 7 v2544 := smallByCut p31_23 w61
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b3369 : Ban 29 8 v2369 := viaBranch (ws := [v2370,v1336,v1355,v1344,v2372,v2373,v2371,v2374,v2375,v2329,v2376,v2378,v2380,v2381,v2382,v2383,v2384,v2385,v2337,v2386,v2387,v2388,v2389,v2464,v2510,v2511,v2512,v2513,v2514,v2515,v2377,v2516,v2517,v2518,v2519,v2520,v2521,v2522,v2523,v2524,v2525,v2526,v2527,v2528,v2477,v2529,v2530,v2379,v2481,v2531,v2532,v2478,v2482,v2484,v2408,v2474,v2533,v2534,v2390,v2461,v2535,v2536,v2537,v2538,v2539,v2541,v2540,v2542,v2543,v2544]) (consBan b3178 (consBan b1906 (consBan b3180 (consBan b3181 (consBan b3182 (consBan b3183 (consBan b3179 (consBan b3184 (consBan b3185 (consBan b3132 (consBan b3187 (consBan b3189 (consBan b3190 (consBan b3191 (consBan b3192 (consBan b3193 (consBan b3194 (consBan b3195 (consBan b3140 (consBan b3196 (consBan b3197 (consBan b3198 (consBan b3278 (consBan b3326 (consBan b3327 (consBan b3328 (consBan b3329 (consBan b3330 (consBan b3331 (consBan b3332 (consBan b3186 (consBan b3333 (consBan b3334 (consBan b3335 (consBan b3336 (consBan b3337 (consBan b3338 (consBan b3339 (consBan b3340 (consBan b3341 (consBan b3342 (consBan b3343 (consBan b3344 (consBan b3345 (consBan b3346 (consBan b3347 (consBan b3348 (consBan b3188 (consBan b3349 (consBan b3350 (consBan b3351 (consBan b3352 (consBan b3353 (consBan b3354 (consBan b3355 (consBan b3356 (consBan b3357 (consBan b3358 (consBan b3277 (consBan b3325 (consBan b3359 (consBan b3360 (consBan b3361 (consBan b3362 (consBan b3364 (consBan b3366 (consBan b3363 (consBan b3365 (consBan b3367 (consBan b3368 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3371 : Ban 29 8 v2544 := smallByCut p31_23 w59
theorem b3370 : Ban 29 8 v2543 := smallByCut p31_15 w59
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b3372 : Ban 29 9 v0 := viaBranch (ws := [v1,v86,v595,v442,v1431,v1432,v443,v1433,v1209,v1434,v1203,v2079,v2347,v2348,v2349,v2350,v2351,v2352,v2353,v2354,v1217,v2355,v1211,v2356,v2357,v2358,v2359,v2360,v2361,v2362,v2363,v2080,v2364,v2365,v2366,v2367,v2368,v2369,v2544,v2543]) (consBan b90 (consBan b1917 (consBan b1919 (consBan b1920 (consBan b1921 (consBan b1922 (consBan b1918 (consBan b1923 (consBan b1969 (consBan b3150 (consBan b3152 (consBan b3154 (consBan b3155 (consBan b3156 (consBan b3157 (consBan b3158 (consBan b3159 (consBan b3160 (consBan b3161 (consBan b3162 (consBan b3163 (consBan b3164 (consBan b3151 (consBan b3165 (consBan b3166 (consBan b3167 (consBan b3168 (consBan b3169 (consBan b3170 (consBan b3171 (consBan b3172 (consBan b3153 (consBan b3173 (consBan b3174 (consBan b3175 (consBan b3176 (consBan b3177 (consBan b3369 (consBan b3371 (consBan b3370 (nilBan 29 8))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 29 9 v0 := widen (by decide +kernel) b3372
end PEqualNP.Outside.L_meta_12162.Support

namespace PEqualNP.Outside.L_meta_12162.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12162.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4276682368 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x9cf38e38d34d2cb2d75965955554d34dc71c69a699659
def negBits : ℕ := 0x1c718c2853090ca2471944855110d244c518292609458
def sample (bank : ℕ) (i : Fin 30) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0xc5b1681b1fc7e07,0xe8da30c3e3f8e38,0xf61d8603fc7f1c0,0xe49ffa4a007fe00,0xfff92493ff80000,0x20000000]
def seeds : List Wire := [(false,0xc5b1681b1fc7e07),(false,0xe8da30c3e3f8e38),(false,0xf61d8603fc7f1c0),(true,0xe49ffa4a007fe00),(true,0xfff92493ff80000),(false,0x20000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 30, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (30+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 30, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 30, ∀ b∈inputs, b.testBit i.val≠b.testBit (30+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 30 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 30 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 30 out.2 := by
    intro i hi same
    let j : Fin 30 := ⟨i,hi⟩
    have diff : read i out=read (30+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (30+i))
      rw [same]
    have p := ev i;have n := ev (30+i)
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
def restrictRows : Projection 30 29 := pick (List.range 29) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 29 9 restricted := verifiedPin
theorem six_floor : Ban 30 10 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.or,[6,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[3,4]⟩, ⟨.and,[7,10]⟩, ⟨.or,[11,2]⟩, ⟨.and,[11,8]⟩, ⟨.and,[12,9]⟩, ⟨.or,[4,5]⟩, ⟨.and,[14,15]⟩, ⟨.or,[13,16]⟩],17⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
theorem wcomputes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by decide +kernel
theorem binary_floor {C : Circuit} (fan : FanInTwo C) (d : ∀ x, C.eval (List.ofFn x) = target x) :
    11 ≤ C.gates.countP counted := by
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
    change 12 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_12162.Data

theorem PEqualNP.Outside.L_meta_12162 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12162.Data.mono_enough
