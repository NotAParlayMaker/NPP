import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532 and L-meta-12325.

namespace PEqualNP.Outside.L_meta_16333

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

end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333

def opB (d : ℕ) (a b : Bool) : Bool :=
  match d with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a
theorem combineBit (d a b i : ℕ) (hd : d<4) :
    (combine d a b).testBit i = opB d (a.testBit i) (b.testBit i) := by
  interval_cases d <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    simp [combine,opB,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,ha,hb]
def remap (d : ℕ) (s t : Bool) : ℕ :=
  let f := fun x y => opB d s t != opB d (s != x) (t != y)
  if f true false then (if f false true then 1 else 2) else (if f false true then 3 else 0)
theorem remapRule (d : ℕ) (hd : d<4) (s t x y : Bool) :
    remap d s t < 4 ∧
    (opB d s t != opB d x y) = opB (remap d s t) (s != x) (t != y) := by
  interval_cases d <;> cases s <;> cases t <;> cases x <;> cases y <;> decide

def signedBits (origin : ℕ) (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | i::is => Nat.bit (w.testBit origin != w.testBit i) (signedBits origin w is)
theorem signedBit (origin w : ℕ) (is : List ℕ) (k : ℕ) :
    (signedBits origin w is).testBit k =
      (is[k]?.map (fun i => w.testBit origin != w.testBit i)).getD false := by
  induction is generalizing k with
  | nil => simp [signedBits]
  | cons i is ih =>
    cases k with
    | zero => cases ha : w.testBit origin <;> cases hb : w.testBit i <;> simp [signedBits,ha,hb]
    | succ k => simp [signedBits,Nat.testBit_bit_succ,ih]

structure Weak (m h : ℕ) where
  f : ℕ → ℕ
  good : ∀ w, Good m w → Good h (f w)
  pos : 0<h
  maps : ∀ d a b, d<4 → ∃ e, e<4 ∧ f (combine d a b)=combine e (f a) (f b)

def signedPick {m h : ℕ} (origin : ℕ) (r : List ℕ) (len : r.length=h)
    (small : ∀ i∈r,i<m) (pos : 0<h) : Weak m h := by
  let is := r ++ r.map (m+·)
  refine ⟨fun w => signedBits origin w is, ?_, pos, ?_⟩
  · intro a ha i hi
    have ir : i<r.length := by omega
    have diff := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : is[i]? = some r[i] := by simp [is,List.getElem?_append,ir]
    have H₂ : is[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [is,List.getElem?_append,ne,sub,ir]
    simp only [signedBit,H₁,H₂,Option.map_some,Option.getD_some]
    cases a.testBit origin <;> simpa using diff
  · intro d a b hd
    let e := remap d (a.testBit origin) (b.testBit origin)
    have he : e<4 := (remapRule d hd _ _ false false).1
    refine ⟨e,he,Nat.eq_of_testBit_eq ?_⟩
    intro i
    rw [combineBit _ _ _ _ he]
    simp only [signedBit]
    cases hi : is[i]? with
    | none => interval_cases e <;> rfl
    | some j =>
      simp only [Option.map_some,Option.getD_some,combineBit _ _ _ _ hd]
      exact (remapRule d hd _ _ _ _).2

end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333
lemma weakCharge {m h d a b : ℕ} (p : Weak m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.f a∈av) (mb : p.f b∈av) :
    (charge av (p.f (combine d a b))).toNat + dead p.f (insert a (insert b U)) ≤
      1+dead p.f (insert (combine d a b) U) := by
  obtain ⟨e,he,eq⟩ := p.maps d a b hd
  have up := deadMono p.f (combine d a b) U
  have la := deadLimit p.f a (insert b U)
  have lb := deadLimit p.f b U
  have free (bad : p.f a=0 ∨ p.f b=0) : charge av (p.f (combine d a b))=false := by
    rw [eq]
    rcases combine_eq_cases _ _ _ he (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.f a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.f b=0
    · have zz : p.f (combine d a b)=0 := by
        rw [eq,az,bz];interval_cases e <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.f b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.f (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem weakLive {m h k S} (p : Weak m h) (live : Live m k S) :
    ∃ j T,j+dead p.f S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.f := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.f a≠0 := by intro e;have x := gp 0 p.pos;simp [e] at x
    exact ⟨0,{p.f a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    obtain ⟨e,he,eq⟩ := p.maps d a b hd
    let av := ((insert a (insert b U)).image p.f).toList
    have ma : p.f a∈av := by simp [av]
    have mb : p.f b∈av := by simp [av]
    have later : Possible h j (av++[combine e (p.f a) (p.f b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [eq]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.f a ∨ z=p.f b ∨ z∈U.image p.f)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid he ma mb later
    rw [←eq] at lim
    have bound := weakCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩







end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333

theorem forced (d : ℕ) (hd : d<4) (left : Bool) :
    ∃ s c : Bool, ∀ y : Bool, (if left then opB d s y else opB d y s)=c := by
  interval_cases d <;> cases left <;> decide

theorem signedZero {o w : ℕ} {is : List ℕ} (same : ∀ i∈is, w.testBit i = w.testBit o) :
    signedBits o w is=0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hi := same i (by simp)
    have ht := ih (fun j hj => same j (by simp [hj]))
    simp [signedBits,hi,ht]

theorem forcedLeft {o v b d : ℕ} {is : List ℕ} {s c : Bool} (hd : d<4)
    (base : v.testBit o=s) (constant : ∀ i∈is, v.testBit i=s)
    (force : ∀ y, opB d s y=c) : signedBits o (combine d v b) is=0 := by
  apply signedZero
  intro i hi
  simp [combineBit _ _ _ _ hd,base,constant i hi,force]

theorem forcedRight {o v a d : ℕ} {is : List ℕ} {s c : Bool} (hd : d<4)
    (base : v.testBit o=s) (constant : ∀ i∈is, v.testBit i=s)
    (force : ∀ y, opB d y s=c) : signedBits o (combine d a v) is=0 := by
  apply signedZero
  intro i hi
  simp [combineBit _ _ _ _ hd,base,constant i hi,force]
end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333

theorem doubleElim {m h k S} (p : Bool → Weak m h) (v : ℕ)
    (killed : ∀ d a b, d<4 → (v=a ∨ v=b) → ∃ t, (p t).f (combine d a b)=0)
    (fixed : ∀ t, (p t).f v=0)
    (live : Live m k S) (hv : v∈S) :
    ∃ t j T, j+2≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image (p t).f := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rfl,good,_⟩ := live
    have ev : v=a := by simpa using hv
    have bad := (p false).good a good 0 (p false).pos
    rw [←ev,fixed] at bad
    simp at bad
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rfl,hd,_,_,_,_,tail⟩ := live
    by_cases hit : v=a ∨ v=b
    · obtain ⟨t,van⟩ := killed d a b hd hit
      obtain ⟨j,T,cost,ok,sub⟩ := weakLive (p t) tail
      have one : 0<dead (p t).f (insert (combine d a b) U) :=
        Finset.card_pos.mpr ⟨combine d a b,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,van⟩⟩
      refine ⟨t,j,T,by omega,ok,?_⟩
      intro x hx
      have mem := sub x hx
      rw [Finset.image_insert] at mem
      rcases Finset.mem_insert.mp mem with eq|mem
      · exact False.elim (liveNonzero ok x hx (eq.trans van))
      · simp [mem]
    · have vu : v∈U := by simpa [Finset.mem_insert,not_or.mp hit |>.1,not_or.mp hit |>.2] using hv
      obtain ⟨t,j,T,cost,ok,sub⟩ := ih tail (Finset.mem_insert_of_mem vu)
      let q := p t
      obtain ⟨e,he,eq⟩ := q.maps d a b hd
      let av := ((insert a (insert b U)).image q.f).toList
      have ma : q.f a∈av := by simp [av]
      have mb : q.f b∈av := by simp [av]
      have later : Possible h j (av++[combine e (q.f a) (q.f b)]) := by
        refine ⟨j,T,le_rfl,ok,?_⟩
        intro z hz
        have mem := sub z hz
        change z ∈ (insert (combine d a b) U).image q.f at mem
        rw [Finset.image_insert] at mem
        rcases Finset.mem_insert.mp mem with rfl|mem
        · simp [eq]
        · have inav : z∈av := by simp [av,mem]
          simp [inav]
      obtain ⟨l,V,lim,ok',sub'⟩ := pullPaid he ma mb later
      have cap : (charge av (combine e (q.f a) (q.f b))).toNat≤1 := by cases charge av _ <;> decide
      exact ⟨t,l,V,by omega,ok',by simpa [av,q] using sub'⟩
end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333
theorem viaWeakCut {m h f t : ℕ} {v w : List ℕ} (p : Weak m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.f a=0 ∨ p.f a∈w)
    (cost : f≤t+(v.map p.f).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := weakLive p run
  have fixed : dead p.f v.toFinset=(v.map p.f).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.f x=0) = (v.filter (fun x => decide (p.f x=0))).toFinset := by ext x;simp
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

end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333
theorem viaFallback {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => (!ws.contains (ordered u)) && search m f u) v=false) : Ban m (f+1) v := by
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
    have yes := @transition m f n U a b d v (fun u => (!ws.contains (ordered u)) && search m f u) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      simp only [Bool.and_eq_true]
      constructor
      · simp
        intro found
        have hv := closed _ found n (by omega)
        rw [ord_eq,hu] at hv
        exact hv tail
      · exact complete m f tail (by omega) u hu nu)
    simp_all

end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333

abbrev Rule (m k : ℕ) := { test : List ℕ → Bool // ∀ v, v.Nodup → test v=true → Ban m k v }

def relaxed {m h} (p : Projection m h) : Weak m h :=
  ⟨p.val,p.property.2.2.1,p.property.2.2.2,fun d a b hd => ⟨d,hd,p.property.2.1 d a b hd⟩⟩

def cutRule {m h bound : ℕ} (k : ℕ) (p : Weak m h) {w : List ℕ} (lo : Wide h bound w) : Rule m k :=
  ⟨fun v => decide (k ≤ bound+(v.map p.f).count 0) && v.all (fun x => p.f x == 0 || w.contains (p.f x)), by
    intro v nd ok
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at ok
    exact viaWeakCut p lo nd ok.2 ok.1⟩

def fingerprint (v : List ℕ) : ℕ :=
  (v.map (fun x => ((x ^^^ (x >>> 23)) * (x+17)) % 2147483647)).sum % 2147483647

def dictionary {m k} (entries : List (ℕ × Rule m k)) : Rule m k :=
  ⟨fun v => entries.any (fun e => e.1 == fingerprint v && e.2.val v), by
    intro v nd yes
    obtain ⟨e,_,ok⟩ := List.any_eq_true.mp yes
    simp only [Bool.and_eq_true] at ok
    exact e.2.property v nd ok.2⟩

theorem viaRules {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (cuts : Rule m f) (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => (!ws.contains (ordered u)) && (!cuts.val u) && search m f u) v=false) :
    Ban m (f+1) v := by
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
    have yes := @transition m f n U a b d v (fun u => (!ws.contains (ordered u)) && (!cuts.val u) && search m f u)
      hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_,?_⟩,complete m f tail (by omega) u hu nu⟩
      · simp
        intro found
        have hv := closed _ found n (by omega)
        rw [ord_eq,hu] at hv
        exact hv tail
      · cases eq : cuts.val u with
        | false => rfl
        | true =>
          have bad := cuts.property u nu eq n (by omega)
          rw [hu] at bad
          exact False.elim (bad tail))
    simp_all
end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333.B0
def bank : List ℕ := [0x1652ca52cb031418b302c5c7ffc0ffc0fd1cf3e7dc1f3f3,0x2aa554a555184942506952d007ffffff02e33d19e7e7cfc,0x4108210820c0a2850c14282a0000003fff03ce1e3878f1f,0x4d39a739a6ed03e80fa03f01f83f07c003fc0fe03f80fe0,0x75debbdebaf7fc000fdf8000003ff80003fff0003fff000,0x79ef3def3cfefff7e0000001ffc0000003ffffffc000000]
def f0 : ℕ := 0x147c
def f1 : ℕ := 0x1d70
def f2 : ℕ := 0x368c
def s0 : List ℕ := [f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 7 3 s0 := viaSearch (by decide +kernel)
def p0 : Weak 94 7 := signedPick 5 [5,7,12,14,19,20,76] (by decide) (by decide) (by decide)
def r0 : Rule 94 7 := cutRule 7 p0 w0
def p1 : Weak 94 7 := signedPick 5 [5,6,26,27,33,34,87] (by decide) (by decide) (by decide)
def r1 : Rule 94 7 := cutRule 7 p1 w0
def f3 : ℕ := 0xa3c
def f4 : ℕ := 0xb4c
def f5 : ℕ := 0xeb0
def s1 : List ℕ := [f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 3 s1 := viaSearch (by decide +kernel)
def p2 : Weak 94 6 := signedPick 6 [6,7,8,9,10,11] (by decide) (by decide) (by decide)
def r2 : Rule 94 7 := cutRule 7 p2 w1
def f6 : ℕ := 0x8a0d2a5a3f27e7cfc
def f7 : ℕ := 0x8b828d1d4ffc7ffff
def f8 : ℕ := 0x175f687e577fff8fff
def f9 : ℕ := 0x175fbf000383fff000
def f10 : ℕ := 0x1fe6058b8ccdc1f3f3
def s2 : List ℕ := [f6,f7,f8,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 35 5 s2 := viaSearch (by decide +kernel)
def p3 : Weak 94 35 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,54,55,60,61,66,71,76,77,93] (by decide) (by decide) (by decide))
def r3 : Rule 94 6 := cutRule 6 p3 w2
def f11 : ℕ := 0x175f407e0343f80fe0
def f12 : ℕ := 0x175fbf5057bfffff1f
def s3 : List ℕ := [f6,f7,f11,f12,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 35 5 s3 := viaSearch (by decide +kernel)
def r4 : Rule 94 6 := cutRule 6 p3 w3
def r5 : Rule 94 6 := cutRule 6 p1 w0
def f13 : ℕ := 0x8a0c58b8fccf9f3f3
def f14 : ℕ := 0x8b428d1d4ffc7ffff
def f15 : ℕ := 0x1fea12a5a0f3467cfc
def s4 : List ℕ := [f13,f14,f11,f12,f15]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 35 5 s4 := viaSearch (by decide +kernel)
def p4 : Weak 94 35 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,26,27,28,29,30,31,32,33,34,35,36,37,38,39,54,56,60,62,67,83,87,89,93] (by decide) (by decide) (by decide))
def r6 : Rule 94 6 := cutRule 6 p4 w4
def f16 : ℕ := 0x1652ca52cb031418b302c5c7ffc0ffc0fd1cf3e7dc1f3f3
def f17 : ℕ := 0x2aa554a555184942506952d007ffffff02e33d19e7e7cfc
def f18 : ℕ := 0x4108210820c0a2850c14282a0000003fff03ce1e3878f1f
def f19 : ℕ := 0x4308610861c0a2851c1468ea07c0ffffff03ff1ffc7ffff
def f20 : ℕ := 0x4d39a739a6ed03e80fa03f01f83f07c003fc0fe03f80fe0
def f21 : ℕ := 0x75debbdebaf7fc000fdf8000003ff80003fff0003fff000
def f22 : ℕ := 0x79ef3def3cfefff7e0000001ffc0000003ffffffc000000
def s5 : List ℕ := [f16,f17,f18,f19,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b2 : Ban 94 7 s5 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1733307078,r3),(785539321,r4),(1033475066,r5),(1304367176,r6),(1552302921,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f23 : ℕ := 0x5294a0621890223f801f4733cd8333
def f24 : ℕ := 0xa5294308820688807fe0b8cc327ccc
def f25 : ℕ := 0x1084218154561555003ffc0fe3f8fff
def f26 : ℕ := 0x139ce7da1e87a1e0ffc00ff0fc3f0f0
def f27 : ℕ := 0x1def7befe007de0007c00fff003ff00
def f28 : ℕ := 0x1ef7bdfdff780000f8000fffffc0000
def s6 : List ℕ := [f23,f24,f25,f26,f27,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 61 6 s6 := viaSearch (by decide +kernel)
def p5 : Weak 94 61 := relaxed (pick [0,1,2,3,8,9,10,11,15,16,17,18,19,20,21,23,24,25,29,30,31,32,33,34,35,37,38,39,42,43,44,45,46,47,48,49,50,51,52,53,55,56,57,58,59,61,62,63,64,65,77,78,79,80,81,88,89,90,91,92,93] (by decide) (by decide) (by decide))
def r7 : Rule 94 7 := cutRule 7 p5 w5
def p6 : Weak 94 6 := signedPick 40 [40,41,47,48,50,51] (by decide) (by decide) (by decide)
def r8 : Rule 94 7 := cutRule 7 p6 w1
def f29 : ℕ := 0x533c
def f30 : ℕ := 0x6fb3c
def f31 : ℕ := 0x9d630
def f32 : ℕ := 0xf83f0
def s7 : List ℕ := [f29,f30,f31,f32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 10 3 s7 := viaSearch (by decide +kernel)
def p7 : Weak 94 10 := signedPick 8 [8,9,10,11,19,21,23,24,25,77] (by decide) (by decide) (by decide)
def r9 : Rule 94 7 := cutRule 7 p7 w6
def p8 : Weak 94 6 := signedPick 13 [13,14,15,16,17,18] (by decide) (by decide) (by decide)
def r10 : Rule 94 7 := cutRule 7 p8 w1
def f33 : ℕ := 0x108420200810020f80004703c18030
def s8 : List ℕ := [f33,f23,f24,f25,f26,f27,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 61 6 s8 := viaSearch (by decide +kernel)
def r11 : Rule 94 7 := cutRule 7 p5 w7
def f34 : ℕ := 0x21084100800208007c00b80c0270c0
def s9 : List ℕ := [f34,f23,f24,f25,f26,f27,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 61 6 s9 := viaSearch (by decide +kernel)
def r12 : Rule 94 7 := cutRule 7 p5 w8
def r13 : Rule 94 6 := cutRule 6 p6 w1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 6 2 s1 := viaSearch (by decide +kernel)
def r14 : Rule 94 6 := cutRule 6 p6 w9
def f35 : ℕ := 0x200400041000000100040c007c0ffc000003101c4070f0
def f36 : ℕ := 0x4d39a739a6eda3ed0fb43f2bf83f07ffffffcffe3ff8fff
def s10 : List ℕ := [f35,f16,f17,f18,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b3 : Ban 94 7 s10 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1733307078,r3),(738660048,r13),(986595793,r14),(1833723883,r5),(205068091,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f37 : ℕ := 0x318c65a0a81a0a0ffc003f01c07000
def s11 : List ℕ := [f37,f23,f24,f25,f27,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 61 6 s11 := viaSearch (by decide +kernel)
def r15 : Rule 94 7 := cutRule 7 p5 w10
def f38 : ℕ := 0xa118c
def f39 : ℕ := 0xad630
def f40 : ℕ := 0xfb98c
def s12 : List ℕ := [f38,f39,f32,f40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 10 3 s12 := viaSearch (by decide +kernel)
def p9 : Weak 94 10 := signedPick 8 [8,9,10,11,33,35,37,38,39,89] (by decide) (by decide) (by decide)
def r16 : Rule 94 7 := cutRule 7 p9 w11
def f41 : ℕ := 0x25547cfc
def f42 : ℕ := 0x2d568c0c
def f43 : ℕ := 0x37fd70f0
def s13 : List ℕ := [f41,f42,f43]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 15 2 s13 := viaSearch (by decide +kernel)
def p10 : Weak 94 15 := signedPick 5 [5,6,26,27,33,34,46,47,66,68,82,84,87,88,90] (by decide) (by decide) (by decide)
def r17 : Rule 94 6 := cutRule 6 p10 w12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 7 2 s0 := viaSearch (by decide +kernel)
def r18 : Rule 94 6 := cutRule 6 p0 w13
def r19 : Rule 94 6 := cutRule 6 p0 w0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 15 3 s13 := viaSearch (by decide +kernel)
def r20 : Rule 94 6 := cutRule 6 p10 w14
def f44 : ℕ := 0x208410841010480000490000003ff80002e3300027e7000
def s14 : List ℕ := [f35,f16,f44,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b4 : Ban 94 7 s14 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(298982776,r17),(89377426,r18),(1922374231,r19),(386021399,r17),(149494895,r20)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f45 : ℕ := 0xa21442145080142502052d007c007ff00000d19c000cfc
def s15 : List ℕ := [f35,f45,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b5 : Ban 94 7 s15 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1811302947,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p11 : Weak 94 10 := signedPick 15 [15,16,17,18,20,21,23,24,25,77] (by decide) (by decide) (by decide)
def r21 : Rule 94 7 := cutRule 7 p11 w6
def f46 : ℕ := 0x75debbdebaf7fe850fdfa82a003ff83ffffffe1e3ffff1f
def s16 : List ℕ := [f35,f16,f17,f18,f20,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b6 : Ban 94 7 s16 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(785539321,r4),(1033475066,r5),(1938375938,r13),(38828036,r14),(1833723883,r5),(273574768,r20),(1404783981,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f47 : ℕ := 0xd6b5a6ea001ca0007c003f00007000
def s17 : List ℕ := [f23,f24,f47,f25,f26,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 61 6 s17 := viaSearch (by decide +kernel)
def r22 : Rule 94 7 := cutRule 7 p5 w15
def p12 : Weak 94 6 := signedPick 27 [27,28,29,30,31,32] (by decide) (by decide) (by decide)
def r23 : Rule 94 7 := cutRule 7 p12 w1
def p13 : Weak 94 15 := signedPick 5 [5,7,12,14,19,20,49,50,67,69,72,74,76,78,80] (by decide) (by decide) (by decide)
def r24 : Rule 94 6 := cutRule 6 p13 w12
def r25 : Rule 94 6 := cutRule 6 p1 w13
def f48 : ℕ := 0x1042084208021410a0000001ffc00000011cf3e7c000000
def s18 : List ℕ := [f35,f48,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b7 : Ban 94 7 s18 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(182406385,r24),(1399301062,r25),(447429701,r5),(1882107566,r24),(149494895,r20)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f49 : ℕ := 0x610c210c30100081302c5c60000ffc0fc0000001c1f3f3
def s19 : List ℕ := [f35,f49,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b8 : Ban 94 7 s19 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2042564806,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p14 : Weak 94 10 := signedPick 29 [29,30,31,32,34,35,37,38,39,89] (by decide) (by decide) (by decide)
def r26 : Rule 94 7 := cutRule 7 p14 w11
def r27 : Rule 94 6 := cutRule 6 p13 w14
def f50 : ℕ := 0x79ef3def3cfefff7ec14282bffc0003ffffffffff878f1f
def s20 : List ℕ := [f35,f16,f17,f18,f20,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b9 : Ban 94 7 s20 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1304367176,r6),(1552302921,r5),(309720146,r13),(557655891,r14),(205068091,r5),(1404783981,r5),(1577519840,r27)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f51 : ℕ := 0xe739c7cab280000f80003f01c00000
def s21 : List ℕ := [f23,f24,f51,f25,f26,f27]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 61 6 s21 := viaSearch (by decide +kernel)
def r28 : Rule 94 7 := cutRule 7 p5 w16
def s22 : List ℕ := [f35,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 94 8 s22 := viaRules (ws := [s5,s10,s14,s15,s16,s18,s19,s20]) (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (nilBan _ _)))))))))
  (dictionary [(442170393,r0),(1889113616,r0),(1286260931,r0),(1467782006,r1),(46257962,r1),(164388897,r1),(1642635295,r0),(921651675,r1),(1039782610,r1),(1388302694,r2),(84909585,r1),(403300246,r7),(712046325,r8),(1556136863,r1),(2058392754,r7),(754999645,r9),(592000144,r1),(1699113132,r1),(2030306394,r1),(805978380,r1),(1126821233,r1),(929467448,r0),(1925115748,r1),(1046182010,r0),(1429918545,r10),(126525436,r9),(1053295908,r2),(1897386446,r9),(187881435,r10),(1031971973,r9),(1422573661,r2),(119180552,r9),(668637165,r11),(1575218019,r1),(1693432473,r9),(1760306348,r12),(998342317,r0),(1678331035,r9),(99223089,r1),(1268167246,r9),(281080000,r15),(447058074,r1),(706741867,r2),(1550832405,r1),(1847909153,r10),(544516044,r16),(647067418,r2),(1491157956,r1),(150556572,r10),(994647110,r9),(1393127511,r1),(575828187,r1),(1779090231,r1),(1488132951,r1),(1087962820,r1),(662404694,r21),(720293737,r1),(1037413430,r1),(929245981,r22),(407484996,r1),(645813944,r1),(2049865910,r1),(798392946,r9),(678667270,r1),(1934119696,r16),(692535768,r2),(1536626306,r0),(1382124068,r23),(78730959,r9),(1548216358,r2),(244823249,r0),(885502660,r23),(1729593198,r9),(2010304229,r0),(506084326,r26),(1350024088,r0),(369309917,r0),(544182102,r0),(180593277,r0),(768906344,r1),(1168659058,r0),(2103187885,r28),(1193844673,r0),(2092377288,r1),(2073640796,r0),(1983856667,r9),(1288144210,r0),(491184992,r9),(668280907,r1),(1497888471,r21),(285592453,r0),(1117196524,r1)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r29 : Rule 94 7 := cutRule 7 p1 w13
def f52 : ℕ := 0x20000003fff03ce1e3878f1f
def s23 : List ℕ := [f52,f16,f17,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b11 : Ban 94 7 s23 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1201406834,r14),(2051103287,r13),(2018237755,r13),(412486307,r14),(1736227923,r14),(1993560855,r13),(1537457765,r13),(568621318,r14),(1475375243,r14),(585570827,r13),(549135850,r13),(1652568442,r14),(845796067,r14),(1184164548,r13),(1476117449,r13),(2018162570,r14),(71646848,r19),(1793572369,r19),(921999615,r14),(1853650837,r13),(1617342275,r13),(166906011,r14),(1381570484,r5),(2024834228,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f53 : ℕ := 0x3ef7def7df1b5d5af36bd7d5ffffffc000fc31e1c7870e0
def s24 : List ℕ := [f16,f17,f53,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b12 : Ban 94 7 s24 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(525686177,r25),(1060507266,r25),(2014029101,r5),(612824779,r5),(1543409838,r19),(1117851712,r19),(1636017316,r5),(1902923914,r5),(705849827,r5),(1349113571,r5),(345496756,r5),(916191953,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r30 : Rule 94 7 := cutRule 7 p0 w13
def r31 : Rule 94 6 := cutRule 6 p8 w9
def f54 : ℕ := 0xc3186318609014803201701f83f07c003fc0fe03f80fe0
def s25 : List ℕ := [f54,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b13 : Ban 94 7 s25 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(438955630,r31),(1807633356,r5),(1236252530,r5),(164987221,r25),(699808310,r25),(1182710882,r19),(757152756,r19),(1132161492,r5),(502233058,r5),(345150871,r5),(988414615,r5),(1650989347,r5),(1676174962,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f55 : ℕ := 0x14f
def f56 : ℕ := 0x4b3
def s26 : List ℕ := [f55,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 6 2 s26 := viaSearch (by decide +kernel)
def p15 : Weak 94 6 := relaxed (pick [6,7,8,9,10,11] (by decide) (by decide) (by decide))
def r32 : Rule 94 6 := cutRule 6 p15 w17
def f57 : ℕ := 0x32c658c659125c12f04bc0d607c0f83ffc03f01fc07f01f
def s27 : List ℕ := [f16,f17,f57,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b14 : Ban 94 7 s27 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(220148234,r14),(754969323,r14),(671309842,r32),(78404897,r13),(1982531855,r13),(1237871895,r19),(812313769,r19),(1187322505,r13),(557394071,r13),(400311884,r5),(1043575628,r5),(1706150360,r13),(1731335975,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r33 : Rule 94 6 := cutRule 6 p2 w9
def f58 : ℕ := 0x34d69ad69a135c00034b8000003ff80003fff0003fff000
def s28 : List ℕ := [f16,f17,f58,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b15 : Ban 94 7 s28 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(765633267,r19),(340075141,r19),(1274628380,r25),(1809449469,r25),(919017613,r33),(687921494,r5),(858240745,r5),(1042086761,r5),(963708236,r5),(1454792030,r5),(2098055774,r5),(613146859,r5),(638332474,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p16 : Weak 94 6 := relaxed (pick [13,14,15,16,17,18] (by decide) (by decide) (by decide))
def r34 : Rule 94 6 := cutRule 6 p16 w17
def f59 : ℕ := 0xa2144214508015af02057d7ffc007fffc000fffc000fff
def s29 : List ℕ := [f59,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b16 : Ban 94 7 s29 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(340075141,r19),(765633267,r19),(150093785,r34),(1916150052,r13),(1125147343,r13),(1480821696,r14),(2015642785,r14),(1248280077,r13),(1169901552,r13),(1660985346,r5),(156765443,r5),(819340175,r13),(844525790,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f60 : ℕ := 0x38e71ce71c1a5d52e0000001ffc0000003ffffffc000000
def s30 : List ℕ := [f16,f17,f60,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b17 : Ban 94 7 s30 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2075556903,r5),(571337000,r5),(1903244978,r25),(290582420,r25),(1623837759,r33),(836216819,r5),(1715203832,r5),(1670703359,r5),(1592324834,r5),(773484992,r19),(347926866,r19),(722935602,r5),(93007168,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p17 : Weak 94 6 := relaxed (pick [27,28,29,30,31,32] (by decide) (by decide) (by decide))
def r35 : Rule 94 6 := cutRule 6 p17 w17
def f61 : ℕ := 0x610c210c3010008136bd7d6003ffffffc0000003ffffff
def s31 : List ℕ := [f61,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b18 : Ban 94 7 s31 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(571337000,r5),(2075556903,r5),(1153434845,r35),(452715269,r13),(138415382,r13),(40452021,r14),(575273110,r14),(1955394049,r13),(1877015524,r13),(1058175682,r19),(632617556,r19),(1007626292,r13),(377697858,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f62 : ℕ := 0x3ef7def7df1b5d5af36bd7d7fffffffffffffffffffffff
def s32 : List ℕ := [f16,f17,f62,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b10 : Ban 94 8 s32 := viaRules (ws := [s23,s24,s25,s27,s28,s29,s30,s31]) (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (nilBan _ _)))))))))
  (dictionary [(1642635295,r0),(921651675,r1),(1039782610,r1),(878024597,r0),(275171912,r29),(1278913011,r1),(1397043946,r1),(1467782006,r1),(442170393,r0),(702783159,r29),(265265185,r1),(1809896147,r29),(2141089409,r29),(1519614080,r1),(916761395,r29),(1237604248,r29),(922119528,r1),(1040250463,r1),(2035898763,r29),(1038834090,r1),(1156965025,r1),(942251492,r8),(1649189300,r1),(1897125045,r29),(263174968,r2),(1218048521,r29),(522385547,r8),(1477259100,r29),(266530835,r1),(973468643,r1),(1221404388,r29),(779420180,r1),(1323155933,r29),(1686001034,r29),(1804215488,r1),(1871089363,r0),(470899146,r30),(1109125332,r30),(1789114050,r0),(566604855,r10),(612769687,r1),(1521478408,r1),(781519597,r2),(1736393150,r29),(1628398359,r10),(435788265,r29),(621765868,r2),(667930700,r1),(1576639421,r1),(210006104,r29),(470241540,r1),(1378950261,r1),(391863015,r1),(1300571736,r1),(557841089,r29),(1503910526,r29),(686611202,r29),(1889873246,r29),(1598915966,r29),(1720506820,r0),(1198745835,r29),(1189583329,r1),(1360918298,r29),(1294948694,r0),(773187709,r1),(245776308,r2),(1722410846,r1),(1200649861,r29),(1323745365,r10),(131135271,r29),(147329370,r2),(1102202923,r29),(451969624,r10),(1928604162,r1),(1406843177,r29),(831076752,r29),(1669957430,r1),(1148196445,r29),(1040028996,r1),(518268011,r29),(756596959,r29),(13165278,r29),(909175961,r1),(789450285,r29),(2044902711,r1),(882946809,r1),(2121087244,r1),(1865746007,r29),(30533752,r29),(1526210553,r1),(616867341,r1),(1460807103,r30),(480092932,r30),(654965117,r30),(291376292,r30),(486810679,r2),(203543797,r1),(1441684232,r1),(865242715,r23),(1820116268,r29),(940992866,r2),(1895866419,r29),(771501369,r23),(488234487,r1),(1726374922,r1),(879689359,r29),(41301638,r1),(1279442073,r1),(66487253,r1),(1304627688,r1),(55676656,r29),(36940164,r30),(2094639682,r0),(1398927225,r30),(601968007,r0),(779063922,r29),(1608671486,r1),(396375468,r1),(1227979539,r29)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f63 : ℕ := 0x3af0
def f64 : ℕ := 0x52f3
def f65 : ℕ := 0x68fc
def s33 : List ℕ := [f63,f64,f65]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 8 4 s33 := viaSearch (by decide +kernel)
def p18 : Weak 94 8 := relaxed (pick [5,6,26,27,33,34,35,87] (by decide) (by decide) (by decide))
def r36 : Rule 94 7 := cutRule 7 p18 w18
def f66 : ℕ := 0x203df83c
def f67 : ℕ := 0x4a90e1b0
def f68 : ℕ := 0x9568f9fc
def f69 : ℕ := 0xdffae1b0
def s34 : List ℕ := [f66,f67,f68,f69]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 16 3 s34 := viaSearch (by decide +kernel)
def p19 : Weak 94 16 := signedPick 12 [12,13,26,27,33,34,40,46,47,71,73,82,84,87,88,90] (by decide) (by decide) (by decide)
def r37 : Rule 94 7 := cutRule 7 p19 w19
def f70 : ℕ := 0x4b0
def s35 : List ℕ := [f70,f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 6 3 s35 := viaSearch (by decide +kernel)
def r38 : Rule 94 7 := cutRule 7 p2 w20
def r39 : Rule 94 7 := cutRule 7 p10 w14
def f71 : ℕ := 0x255681f0fe0
def f72 : ℕ := 0x2d56da3c26c
def f73 : ℕ := 0x37ffb5c0d80
def f74 : ℕ := 0x37ffb5ccf9c
def s36 : List ℕ := [f71,f72,f73,f74]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 21 4 s36 := viaSearch (by decide +kernel)
def p20 : Weak 94 21 := signedPick 5 [5,6,12,13,22,26,27,33,34,40,46,47,66,68,71,73,82,84,87,88,90] (by decide) (by decide) (by decide)
def r40 : Rule 94 7 := cutRule 7 p20 w21
def f75 : ℕ := 0x34559e
def f76 : ℕ := 0x357c06
def f77 : ℕ := 0x3ed198
def s37 : List ℕ := [f75,f76,f77]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 11 3 s37 := viaSearch (by decide +kernel)
def p21 : Weak 94 11 := signedPick 2 [2,27,28,29,30,31,32,42,43,63,84] (by decide) (by decide) (by decide)
def r41 : Rule 94 6 := cutRule 6 p21 w22
def f78 : ℕ := 0x547e
def f79 : ℕ := 0x17618
def f80 : ℕ := 0x2dc66
def s38 : List ℕ := [f78,f79,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 9 3 s38 := viaSearch (by decide +kernel)
def p22 : Weak 94 9 := signedPick 17 [17,29,30,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r42 : Rule 94 6 := cutRule 6 p22 w23
def f81 : ℕ := 0x51e
def f82 : ℕ := 0x1786
def f83 : ℕ := 0x2d18
def s39 : List ℕ := [f81,f82,f83]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 7 2 s39 := viaSearch (by decide +kernel)
def p23 : Weak 94 7 := signedPick 2 [2,27,28,29,30,31,32] (by decide) (by decide) (by decide)
def r43 : Rule 94 6 := cutRule 6 p23 w24
def f84 : ℕ := 0x79ef3def3cfefff7e0691211ffff003f03ffffffe3e0c0c
def s40 : List ℕ := [f16,f17,f18,f20,f21,f84]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b20 : Ban 94 7 s40 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2064392565,r25),(1616610099,r25),(3947541,r25),(1384068480,r5),(1305689955,r5),(486850113,r41),(61291987,r42),(436300723,r5),(1953855936,r5),(2075556903,r5),(586459561,r43),(571337000,r5),(115507270,r5),(1763504360,r5),(810860310,r43)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f85 : ℕ := 0x287c
def f86 : ℕ := 0x2d0c
def f87 : ℕ := 0xfa70
def s41 : List ℕ := [f85,f86,f87]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 8 3 s41 := viaSearch (by decide +kernel)
def p24 : Weak 94 8 := signedPick 6 [6,7,8,9,10,11,38,67] (by decide) (by decide) (by decide)
def r44 : Rule 94 6 := cutRule 6 p24 w25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 8 2 s41 := viaSearch (by decide +kernel)
def r45 : Rule 94 6 := cutRule 6 p24 w26
def f88 : ℕ := 0x541fc
def f89 : ℕ := 0x1768cc
def f90 : ℕ := 0x2dd130
def s42 : List ℕ := [f88,f89,f90]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 11 3 s42 := viaSearch (by decide +kernel)
def p25 : Weak 94 11 := signedPick 6 [6,7,8,9,10,11,23,24,38,66,67] (by decide) (by decide) (by decide)
def r46 : Rule 94 6 := cutRule 6 p25 w27
def f91 : ℕ := 0x15e3f
def f92 : ℕ := 0xa2bf3
def f93 : ℕ := 0x7485cc
def s43 : List ℕ := [f91,f92,f93]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 12 3 s43 := viaSearch (by decide +kernel)
def p26 : Weak 94 12 := relaxed (pick [0,1,13,14,15,16,17,18,44,58,74,93] (by decide) (by decide) (by decide))
def r47 : Rule 94 6 := cutRule 6 p26 w28
def f94 : ℕ := 0x514a294a28e6b6b5a0000001ffc00000011cf3e7c000000
def s44 : List ℕ := [f16,f17,f18,f20,f94,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b21 : Ban 94 7 s44 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1227997928,r25),(780215462,r25),(2113331066,r25),(547673843,r5),(469295318,r5),(635273392,r25),(2075556903,r5),(1973298722,r25),(571337000,r5),(557525235,r44),(434678913,r25),(1757130363,r5),(1880093007,r5),(492370096,r5),(1852057654,r25),(1411322616,r45),(1797939123,r46),(1372380997,r47),(1747389733,r5),(1117461299,r5),(1666691029,r44),(970190066,r44)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f95 : ℕ := 0x28a514a51418494240691210003f003f02e30c1823e0c0c
def s45 : List ℕ := [f16,f95,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b19 : Ban 94 8 s45 := viaRules (ws := [s40,s44]) (consBan b20 (consBan b21 (nilBan _ _)))
  (dictionary [(878024597,r0),(195692072,r1),(275171912,r29),(46257962,r1),(164388897,r1),(1006371983,r36),(1124502918,r0),(403519298,r1),(521650233,r1),(84909057,r7),(1974873093,r29),(934502434,r29),(1265695696,r29),(41367682,r29),(1106472726,r8),(1185952566,r29),(1351240057,r1),(1430719897,r29),(684713708,r8),(764193548,r29),(2013042942,r1),(2092522782,r29),(362210535,r29),(46725815,r1),(164856750,r1),(1160505050,r29),(163440377,r1),(281571312,r1),(2051510114,r1),(447762220,r29),(810607321,r29),(928821775,r1),(859360186,r10),(938840026,r29),(1454602263,r2),(1534082103,r1),(483919151,r10),(563398991,r1),(145960910,r2),(225440750,r29),(995695650,r37),(1742989080,r0),(233731619,r0),(913720337,r38),(1482096038,r29),(1742331474,r1),(503556548,r1),(1663952949,r1),(425178023,r1),(1829931023,r29),(628516813,r29),(1958701136,r29),(1014479533,r29),(723522253,r29),(919562492,r2),(999042332,r29),(420714229,r10),(500194069,r29),(1767650557,r2),(1847130397,r29),(991609413,r10),(1071089253,r29),(845113107,r39),(323352122,r29),(314189616,r1),(485524585,r29),(419554981,r40),(2045277643,r1),(2103166686,r29),(794563717,r1),(272802732,r29),(164635283,r1),(1790357945,r29),(2028686893,r29),(1285255212,r29),(33782248,r1),(2061540219,r29),(1169508998,r1),(7553096,r1),(1245693531,r1),(990352294,r29),(1302623686,r29),(650816840,r1),(1888957275,r1),(1951722644,r2),(2031202484,r29),(200175800,r23),(1188998852,r1),(279655640,r1),(1511264810,r2),(352604215,r1),(1590744650,r1),(1763553867,r23),(1843033707,r29),(585413390,r0),(1752182866,r0),(1927055051,r0),(1563466226,r0),(4295646,r29),(1313391572,r1),(404048360,r1),(1338577187,r1),(429233975,r1),(1327766590,r29),(1309030098,r0),(1219245969,r38),(523533512,r0),(1874057941,r38),(2051153856,r29),(733277773,r1),(1668465402,r1),(352585826,r29)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f96 : ℕ := 0x5284398c
def f97 : ℕ := 0x5ab5c030
def f98 : ℕ := 0xf7e0c1f0
def f99 : ℕ := 0xf7ee398c
def s46 : List ℕ := [f96,f97,f98,f99]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 16 3 s46 := viaSearch (by decide +kernel)
def p27 : Weak 94 16 := signedPick 12 [12,14,19,20,26,28,41,49,50,72,74,76,78,80,83,85] (by decide) (by decide) (by decide)
def r48 : Rule 94 7 := cutRule 7 p27 w29
def f100 : ℕ := 0x14c
def s47 : List ℕ := [f100,f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 6 3 s47 := viaSearch (by decide +kernel)
def r49 : Rule 94 7 := cutRule 7 p2 w30
def f101 : ℕ := 0x1266
def f102 : ℕ := 0x3a60
def s48 : List ℕ := [f101,f82,f102]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w31 : Wide 7 2 s48 := viaSearch (by decide +kernel)
def p28 : Weak 94 7 := signedPick 0 [0,13,14,15,16,17,18] (by decide) (by decide) (by decide)
def r50 : Rule 94 6 := cutRule 6 p28 w31
def f103 : ℕ := 0x3525e6
def f104 : ℕ := 0x3fa1e0
def s49 : List ℕ := [f103,f76,f104]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w32 : Wide 11 3 s49 := viaSearch (by decide +kernel)
def p29 : Weak 94 11 := signedPick 0 [0,13,14,15,16,17,18,44,45,58,74] (by decide) (by decide) (by decide)
def r51 : Rule 94 6 := cutRule 6 p29 w32
def f105 : ℕ := 0x587c
def f106 : ℕ := 0x17a18
def f107 : ℕ := 0x2dc64
def s50 : List ℕ := [f105,f106,f107]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w33 : Wide 9 3 s50 := viaSearch (by decide +kernel)
def p30 : Weak 94 9 := signedPick 17 [17,18,29,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r52 : Rule 94 6 := cutRule 6 p30 w33
def f108 : ℕ := 0x75debbdebaf7fc18afdf8507f83ff800fffff2e63fff303
def s51 : List ℕ := [f16,f17,f18,f20,f108,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b23 : Ban 94 7 s51 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(466376736,r18),(18594270,r18),(553415359,r18),(1351709874,r18),(1933536298,r19),(1855157773,r19),(765633267,r19),(1594430029,r50),(340075141,r19),(206273656,r19),(82496790,r19),(1023485637,r50),(198757920,r51),(842021664,r52),(1504596396,r19),(1529782011,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f109 : ℕ := 0x3a30
def f110 : ℕ := 0xed4c
def s52 : List ℕ := [f85,f109,f110]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w34 : Wide 8 3 s52 := viaSearch (by decide +kernel)
def p31 : Weak 94 8 := signedPick 6 [6,7,8,9,10,11,23,66] (by decide) (by decide) (by decide)
def r53 : Rule 94 6 := cutRule 6 p31 w34
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w35 : Wide 8 2 s52 := viaSearch (by decide +kernel)
def r54 : Rule 94 6 := cutRule 6 p31 w35
def f111 : ℕ := 0x941fc
def f112 : ℕ := 0x1b684c
def f113 : ℕ := 0x2dd1b0
def s53 : List ℕ := [f111,f112,f113]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w36 : Wide 11 3 s53 := viaSearch (by decide +kernel)
def p32 : Weak 94 11 := signedPick 6 [6,7,8,9,10,11,23,38,39,66,67] (by decide) (by decide) (by decide)
def r55 : Rule 94 6 := cutRule 6 p32 w36
def f114 : ℕ := 0x24ecf
def f115 : ℕ := 0x513f3
def f116 : ℕ := 0x38a53c
def s54 : List ℕ := [f114,f115,f116]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w37 : Wide 11 3 s54 := viaSearch (by decide +kernel)
def p33 : Weak 94 11 := relaxed (pick [2,3,27,28,29,30,31,32,42,63,84] (by decide) (by decide) (by decide))
def r56 : Rule 94 6 := cutRule 6 p33 w37
def f117 : ℕ := 0x618c318c30f4e8000cdd0000003ff80002e3300027e7000
def s55 : List ℕ := [f16,f17,f18,f20,f117,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b24 : Ban 94 7 s55 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1555116633,r18),(398156770,r18),(1642155256,r18),(874792548,r19),(796414023,r19),(962392097,r18),(1091162210,r53),(765633267,r19),(1506753931,r18),(340075141,r19),(743187442,r18),(1106765940,r19),(1944429516,r19),(1500830284,r19),(1654132368,r18),(172092422,r54),(1287497817,r55),(1930761561,r56),(445852646,r19),(471038261,r19),(1439375939,r53),(2046190963,r53)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r57 : Rule 94 7 := cutRule 7 p13 w14
def f118 : ℕ := 0x2954507ce3c
def f119 : ℕ := 0x2b55db8c2cc
def f120 : ℕ := 0x3dff7470c30
def f121 : ℕ := 0x3dff75f0ff0
def s56 : List ℕ := [f118,f119,f120,f121]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w38 : Wide 21 4 s56 := viaSearch (by decide +kernel)
def p34 : Weak 94 21 := signedPick 5 [5,7,12,14,19,20,26,28,36,41,49,50,67,69,72,74,76,78,80,83,85] (by decide) (by decide) (by decide)
def r58 : Rule 94 7 := cutRule 7 p34 w38
def f122 : ℕ := 0x14528a528a031418a3028507f8000000fd1cc2e61818303
def s57 : List ℕ := [f122,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b22 : Ban 94 8 s57 := viaRules (ws := [s51,s55]) (consBan b23 (consBan b24 (nilBan _ _)))
  (dictionary [(84909057,r7),(1889113616,r0),(1286260931,r0),(195692072,r1),(1278913011,r1),(1397043946,r1),(1006371983,r36),(1124502918,r0),(403519298,r1),(521650233,r1),(1262607737,r8),(316475964,r1),(1241420812,r0),(295289039,r30),(1480860454,r8),(534728681,r1),(1243502580,r0),(297370807,r30),(949261480,r1),(511743506,r0),(2056374468,r1),(240084083,r1),(1766092401,r0),(1163239716,r1),(1484082569,r1),(1286728784,r30),(134893437,r1),(1403443346,r30),(2047384648,r10),(1101252875,r30),(588597376,r2),(1789949250,r0),(2074688845,r10),(1128557072,r0),(43929571,r2),(1245281445,r30),(1025898501,r48),(1569634254,r1),(1932479355,r1),(2050693809,r49),(2117567684,r0),(717377467,r30),(1355603653,r30),(2035592371,r0),(456484425,r1),(716719861,r0),(1625428582,r0),(638341336,r0),(1547050057,r0),(804319410,r1),(489482131,r2),(1690834005,r1),(1137225845,r10),(712855057,r0),(191094072,r0),(78482095,r2),(1801594954,r0),(1279833969,r1),(1170950103,r10),(224818330,r30),(1750388847,r1),(933089523,r1),(2136351567,r1),(1845394287,r1),(1966985141,r0),(1445224156,r1),(1436061650,r30),(1607396619,r1),(1541427015,r0),(1019666030,r0),(1077555073,r1),(1916435751,r0),(1394674766,r1),(1286507317,r0),(764746332,r1),(1003075280,r1),(259643599,r1),(1155654282,r49),(1035928606,r1),(143897385,r49),(1175316479,r2),(229184706,r30),(598099485,r23),(1799451359,r30),(2048383233,r2),(1102251460,r30),(597191013,r23),(1798542887,r30),(1129425130,r57),(220081918,r30),(2112224328,r1),(277012073,r1),(1772688874,r58),(863345662,r0),(1707285424,r30),(726571253,r30),(901443438,r30),(537854613,r30),(1126167680,r1),(287779959,r0),(1525920394,r30),(312965574,r0),(1551106009,r30),(302154977,r1),(283418485,r30),(193634356,r0),(1645405546,r30),(848446328,r0),(1025542243,r1),(1855149807,r0),(642853789,r30),(1474457860,r1)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r59 : Rule 94 7 := cutRule 7 p6 w9
def f123 : ℕ := 0x2aa554a555184942506952d207ffffffffe3ff1ffffffff
def s58 : List ℕ := [f16,f123,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b26 : Ban 94 7 s58 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1494937180,r25),(1047154714,r14),(609636740,r13),(6784055,r13),(337977317,r14),(1863985635,r13),(1261132950,r13),(1993560855,r13),(94012953,r14),(1821630655,r14),(1253400835,r19),(1501336580,r13),(449586142,r18),(554377659,r14),(814613095,r13),(736234570,r13),(902212644,r14),(2045369972,r19),(151289781,r19),(1175448307,r14),(2014328985,r13),(1384400551,r13),(1100968514,r14),(1227318364,r5),(1870582108,r5),(1061755395,r14),(1224060914,r14),(385673193,r13),(410858808,r13),(400048211,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f124 : ℕ := 0x2aa554a555184942506952d007ffffff02e33d19e7e7cec
def s59 : List ℕ := [f16,f124,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b27 : Ban 94 7 s59 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2046262634,r25),(1365938549,r13),(1287560024,r13),(468720182,r19),(1546246584,r19),(418170792,r13),(1935726005,r13),(1778643818,r5),(274423915,r5),(936998647,r13),(962184262,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f125 : ℕ := 0x4d39a739a6ed03e80fa03f03f83f07c0fffccfe63f98ff3
def s60 : List ℕ := [f16,f17,f18,f125,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b28 : Ban 94 7 s60 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2132129410,r25),(975169547,r14),(71684386,r14),(869978901,r14),(1086778372,r33),(1662851634,r13),(1584473109,r13),(554586958,r19),(129028832,r19),(504037568,r13),(2021592781,r13),(1864510594,r5),(360290691,r5),(1022865423,r13),(1048051038,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f126 : ℕ := 0x4d39a739a6ed03e80fa03f01f83f07c002fc0de02780ce0
def s61 : List ℕ := [f16,f17,f18,f126,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b29 : Ban 94 7 s61 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(731516678,r25),(818555301,r14),(1662851634,r13),(1584473109,r13),(1301457873,r19),(875899747,r19),(1250908483,r13),(620980049,r13),(463897862,r5),(1107161606,r5),(1769736338,r13),(1794921953,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f127 : ℕ := 0x75debbdebaf7fc000fdf8002003ff800fffff2063fff313
def s62 : List ℕ := [f16,f17,f18,f20,f127,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b30 : Ban 94 7 s62 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(344197188,r25),(431235811,r14),(1229530326,r14),(1811356750,r13),(1732978225,r13),(791269517,r19),(1843159669,r19),(715083877,r13),(85155443,r13),(76578372,r5),(719842116,r5),(1382416848,r13),(1407602463,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f128 : ℕ := 0x75debbdebaf7fc000fdf8000003ff80002ff300027e7000
def s63 : List ℕ := [f16,f17,f18,f20,f128,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b31 : Ban 94 7 s63 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(722942635,r25),(809981258,r14),(42618550,r13),(2111723672,r13),(765633267,r19),(340075141,r19),(715083877,r13),(85155443,r13),(455323819,r5),(1098587563,r5),(1761162295,r13),(1786347910,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r60 : Rule 94 6 := cutRule 6 p12 w9
def r61 : Rule 94 6 := cutRule 6 p12 w1
def f129 : ℕ := 0x79ef3def3cfefff7e0000003ffc00000ffffffffd818313
def s64 : List ℕ := [f16,f17,f18,f20,f21,f129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b32 : Ban 94 7 s64 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(746847301,r25),(1737371085,r14),(833885924,r14),(1632180439,r14),(1953771427,r60),(66523216,r13),(2135628338,r13),(154122765,r61),(1316788496,r19),(891230370,r19),(1266239106,r13),(636310672,r13),(352878635,r61),(130576617,r5),(880395553,r5),(313665516,r60),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f130 : ℕ := 0x79ef3def3cfefff7e0000001ffc0000002ff3df9c000000
def s65 : List ℕ := [f16,f17,f18,f20,f21,f130]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b33 : Ban 94 7 s65 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1394512628,r25),(1481551251,r14),(714188543,r13),(635810018,r13),(1964453823,r19),(1538895697,r19),(1913904433,r13),(1283975999,r13),(581335310,r5),(1490029101,r5),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f131 : ℕ := 0x200000000fd00c2061818313
def s66 : List ℕ := [f131,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b25 : Ban 94 8 s66 := viaRules (ws := [s58,s59,s60,s61,s62,s63,s64,s65]) (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (nilBan _ _)))))))))
  (dictionary [(2109371489,r1),(1071831614,r8),(468978929,r8),(1388302694,r2),(1895393781,r59),(658194562,r0),(1047154714,r8),(1165285649,r8),(1209520016,r0),(1598480168,r8),(1716611103,r8),(1262607737,r8),(1769698824,r59),(592000144,r1),(702783159,r29),(1974873093,r29),(949261480,r1),(1186215856,r8),(1445371198,r1),(1693306943,r59),(1964966366,r8),(1114177936,r1),(1362113681,r8),(541886037,r1),(789821782,r59),(592467997,r8),(1588116297,r59),(461246814,r0),(709182559,r8),(613165635,r10),(1120256722,r59),(2085964578,r2),(1684346944,r8),(445572018,r8),(685351846,r10),(283734212,r8),(1192442933,r8),(119337838,r2),(626428925,r59),(331637714,r1),(875373467,r29),(1238218568,r29),(1356433022,r1),(1423306897,r0),(23116680,r30),(661342866,r30),(1341331584,r0),(1909707285,r59),(22459074,r8),(931167795,r8),(2091564196,r8),(852789270,r8),(110058623,r59),(1604695611,r2),(2111786698,r59),(1015046297,r10),(2043898369,r8),(1522137384,r59),(1393791744,r2),(275160169,r8),(1900882831,r59),(1990978181,r10),(350585621,r59),(1056128060,r8),(238828736,r59),(1442090780,r8),(1151133500,r59),(1272724354,r0),(750963369,r8),(741800863,r59),(913135832,r8),(847166228,r0),(325405243,r59),(383294286,r59),(1222174964,r8),(700413979,r59),(592246530,r8),(70485545,r59),(308814493,r59),(1712866459,r8),(461393495,r59),(341667819,r8),(1597120245,r59),(1025922400,r2),(1533013487,r59),(1030114183,r23),(299064835,r8),(1537205270,r59),(1677779510,r2),(946730162,r8),(37386950,r59),(998221527,r23),(1505312614,r59),(435164343,r1),(1673304778,r8),(1417963541,r59),(1730234933,r8),(1078428087,r1),(169084875,r59),(1013024637,r8),(32310466,r59),(207182651,r8),(1991077473,r59),(431906893,r59),(1741002819,r8),(831659607,r59),(1766188434,r8),(856845222,r59),(1755377837,r59),(1736641345,r8),(1646857216,r59),(951144759,r8),(154185541,r59),(331281456,r59),(1160889020,r59),(2096076649,r59),(780197073,r59)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f132 : ℕ := 0xc3504
def f133 : ℕ := 0xf01f0
def f134 : ℕ := 0x30c53c
def f135 : ℕ := 0x33c830
def s67 : List ℕ := [f132,f133,f134,f135]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w39 : Wide 11 3 s67 := viaSearch (by decide +kernel)
def p35 : Weak 94 11 := signedPick 0 [0,1,3,4,12,13,15,16,18,54,60] (by decide) (by decide) (by decide)
def r62 : Rule 94 7 := cutRule 7 p35 w39
def f136 : ℕ := 0x228c
def s68 : List ℕ := [f0,f1,f136,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w40 : Wide 7 3 s68 := viaSearch (by decide +kernel)
def r63 : Rule 94 7 := cutRule 7 p1 w40
def f137 : ℕ := 0x200400041000000100040c007c0ffff02033d19e467cfc
def s69 : List ℕ := [f137,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b35 : Ban 94 7 s69 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(597606059,r13),(282730695,r14),(922263004,r5),(470385016,r5),(1602519361,r20),(1670100906,r5),(41445114,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f138 : ℕ := 0x143c
def f139 : ℕ := 0x168c
def f140 : ℕ := 0x3d30
def s70 : List ℕ := [f138,f139,f140]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w41 : Wide 7 2 s70 := viaSearch (by decide +kernel)
def p36 : Weak 94 7 := signedPick 6 [6,7,8,9,10,11,67] (by decide) (by decide) (by decide)
def r64 : Rule 94 6 := cutRule 6 p36 w41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w42 : Wide 7 3 s70 := viaSearch (by decide +kernel)
def r65 : Rule 94 6 := cutRule 6 p36 w42
def f141 : ℕ := 0x2a0fc
def f142 : ℕ := 0x7b4cc
def f143 : ℕ := 0xae830
def s71 : List ℕ := [f141,f142,f143]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w43 : Wide 10 3 s71 := viaSearch (by decide +kernel)
def p37 : Weak 94 10 := signedPick 6 [6,7,8,9,10,11,23,24,66,67] (by decide) (by decide) (by decide)
def r66 : Rule 94 6 := cutRule 6 p37 w43
def f144 : ℕ := 0xaf3f
def f145 : ℕ := 0x515f3
def f146 : ℕ := 0x1a42cc
def s72 : List ℕ := [f144,f145,f146]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w44 : Wide 11 3 s72 := viaSearch (by decide +kernel)
def p38 : Weak 94 11 := relaxed (pick [0,1,13,14,15,16,17,18,58,74,93] (by decide) (by decide) (by decide))
def r67 : Rule 94 6 := cutRule 6 p38 w44
def f147 : ℕ := 0x514a294a28c2b695a0000001ffc00000031fffffc000000
def s73 : List ℕ := [f16,f17,f18,f20,f147,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b36 : Ban 94 7 s73 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1985391273,r25),(1537608807,r25),(2072429896,r25),(1875076111,r5),(723240764,r25),(1305067188,r5),(1226688663,r5),(1392666737,r25),(2075556903,r5),(571337000,r5),(1796025569,r64),(1376020503,r65),(1714515007,r25),(1750822810,r5),(483695152,r5),(581335310,r5),(1461691299,r5),(890502304,r25),(509195962,r64),(407848821,r66),(2129774342,r67),(357299431,r5),(1874854644,r5),(1636133262,r65),(1697185023,r65)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f148 : ℕ := 0x2533
def f149 : ℕ := 0x150fc
def f150 : ℕ := 0x28bcf
def s74 : List ℕ := [f148,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w45 : Wide 9 3 s74 := viaSearch (by decide +kernel)
def p39 : Weak 94 9 := relaxed (pick [27,28,29,30,31,32,42,43,84] (by decide) (by decide) (by decide))
def r68 : Rule 94 6 := cutRule 6 p39 w45
def f151 : ℕ := 0x153f
def f152 : ℕ := 0x48cc
def f153 : ℕ := 0xa2f3
def s75 : List ℕ := [f151,f152,f153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w46 : Wide 8 3 s75 := viaSearch (by decide +kernel)
def p40 : Weak 94 8 := relaxed (pick [29,30,40,41,42,43,44,45] (by decide) (by decide) (by decide))
def r69 : Rule 94 6 := cutRule 6 p40 w46
def f154 : ℕ := 0x610c210c30100081f16edee0000fffffc0000003c7ffff
def s76 : List ℕ := [f154,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b37 : Ban 94 7 s76 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(571337000,r5),(2075556903,r5),(10359849,r25),(1922166665,r5),(880395553,r5),(1710061030,r25),(97398472,r25),(1477519411,r5),(1399140886,r5),(580301044,r68),(154742918,r69),(529751654,r5),(2047306867,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f155 : ℕ := 0x575aeb5aebc3b69dbf16edefffc0ffffff1ffffffc7ffff
def s77 : List ℕ := [f16,f17,f18,f20,f155,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b34 : Ban 94 8 s77 := viaRules (ws := [s69,s73,s76]) (consBan b35 (consBan b36 (consBan b37 (nilBan _ _))))
  (dictionary [(1699113132,r1),(265265185,r1),(1809896147,r29),(934502434,r29),(511743506,r0),(2056374468,r1),(1964966366,r8),(1114177936,r1),(1362113681,r8),(1255788969,r8),(652936284,r8),(1328156172,r1),(1576091917,r29),(1896934770,r8),(1699580985,r1),(547745638,r8),(1816295547,r1),(1438750702,r1),(1982486455,r29),(197847909,r29),(316062363,r1),(382936238,r62),(1130229668,r0),(1768455854,r0),(300960925,r63),(869336626,r8),(1129572062,r1),(2038280783,r1),(1051193537,r1),(1959902258,r1),(1217171611,r8),(1186215856,r8),(1810039623,r1),(263174968,r2),(1877379043,r29),(94035291,r0),(1708239366,r1),(2013042942,r1),(1479763370,r29),(2109371489,r1),(1035615447,r10),(502335875,r1),(140955364,r2),(1755159439,r29),(1744697521,r2),(1211417949,r1),(1842415989,r10),(1309136417,r29),(15757401,r29),(1345941724,r8),(401720121,r29),(110762841,r8),(232353695,r39),(1858076357,r29),(1848913851,r8),(2020248820,r29),(1954279216,r40),(1432518231,r8),(1490407274,r8),(181804305,r1),(1807526967,r8),(1699359518,r1),(1177598533,r8),(1415927481,r8),(672495800,r29),(1568506483,r8),(1448780807,r29),(556749586,r8),(235805169,r2),(1850009244,r29),(59953529,r10),(1674157604,r8),(1351382955,r2),(818103383,r29),(950457419,r10),(417177847,r8),(1542277331,r1),(632934119,r1),(377592882,r8),(689864274,r29),(38057428,r1),(1276197863,r8),(2120137625,r0),(1139423454,r8),(1314295639,r0),(950706814,r8),(1539019881,r8),(700632160,r1),(1938772595,r8),(725817775,r1),(1963958210,r8),(715007178,r8),(696270686,r0),(606486557,r8),(2058257747,r0),(1261298529,r8),(121174508,r2),(497238148,r1),(1735378583,r1),(379288214,r23),(1993492289,r8),(1759173653,r2),(1225894081,r29),(293626731,r23),(669690371,r1),(1907830806,r8),(1438394444,r8),(120518361,r8),(1055705990,r8),(1887310061,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f156 : ℕ := 0x4d39a739a6eda3ed0fb43f29f83f07ff03ff0ff83fe0fec
def s78 : List ℕ := [f16,f17,f18,f156,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b39 : Ban 94 7 s78 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(161221800,r25),(1860922981,r14),(248260423,r14),(1046554938,r14),(1662851634,r13),(1584473109,r13),(84867566,r14),(731162995,r19),(305604869,r19),(680613605,r13),(50685171,r13),(2041086631,r5),(536866728,r5),(1199441460,r13),(1224627075,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f157 : ℕ := 0xc318631862d016803a01701f83f07c001fc03e01f803e0
def s79 : List ℕ := [f157,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b40 : Ban 94 7 s79 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1370398612,r25),(1662851634,r13),(1584473109,r13),(922616146,r14),(1940339807,r19),(1514781681,r19),(1889790417,r13),(1259861983,r13),(1102779796,r5),(1746043540,r5),(261134625,r13),(286320240,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f158 : ℕ := 0x75debbdebaf7fe850fdfa828003ff83f03fffc183fffc0c
def s80 : List ℕ := [f16,f17,f18,f20,f158,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b41 : Ban 94 7 s80 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(232950733,r25),(1932651914,r14),(319989356,r14),(1118283871,r14),(1439874859,r14),(1700110295,r13),(1621731770,r13),(1787709844,r14),(1667762890,r19),(1063290344,r19),(715083877,r13),(85155443,r13),(2028236842,r14),(2112815564,r5),(608595661,r5),(1271170393,r13),(1296356008,r13),(1285545411,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f159 : ℕ := 0x34d69ad69a375c0003cb8000003ff80001fcf0001f9f000
def s81 : List ℕ := [f16,f17,f159,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b42 : Ban 94 7 s81 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1620736815,r25),(1399588344,r19),(231808758,r19),(1172954349,r14),(715083877,r13),(85155443,r13),(940412730,r13),(862034205,r13),(1353117999,r5),(1996381743,r5),(511472828,r13),(536658443,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f160 : ℕ := 0x79ef3def3cfefff7ec142829ffc0003f03ffffffe060c0c
def s82 : List ℕ := [f16,f17,f18,f20,f21,f160]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b43 : Ban 94 7 s82 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1799284593,r25),(1351502127,r14),(1886323216,r14),(1118960508,r13),(1040581983,r13),(221742141,r19),(1943667662,r19),(171192751,r13),(1688747964,r13),(2075556903,r5),(571337000,r5),(1233911732,r13),(1259097347,r13),(454330401,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f161 : ℕ := 0x38e71ce71c3e5d72e0000001ffc0000001fcf3e7c000000
def s83 : List ℕ := [f16,f17,f161,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b44 : Ban 94 7 s83 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1578891014,r25),(2075556903,r5),(571337000,r5),(1131108548,r14),(1233911732,r13),(1259097347,r13),(898566929,r13),(820188404,r13),(1348562,r19),(1723274083,r19),(2098282819,r13),(1468354385,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f162 : ℕ := 0x4108210820c0a2850c1428280000003f02030c182060c0c
def s84 : List ℕ := [f16,f17,f162,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b38 : Ban 94 8 s84 := viaRules (ws := [s78,s79,s80,s81,s82,s83]) (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (nilBan _ _)))))))
  (dictionary [(2030306394,r1),(2141089409,r29),(1265695696,r29),(240084083,r1),(1255788969,r8),(855022594,r1),(652936284,r8),(1106472726,r8),(904386416,r59),(429694388,r0),(227608078,r8),(522385547,r8),(320299237,r59),(745667133,r0),(543580823,r8),(1445371198,r1),(1693306943,r59),(362654217,r8),(1659349434,r1),(1907285179,r8),(80644385,r59),(2030774247,r8),(878938900,r59),(5162,r8),(1895393253,r8),(1769943964,r1),(166196070,r29),(529041171,r29),(647255625,r1),(714129500,r0),(1461422930,r30),(2099649116,r30),(632154187,r0),(1756956018,r10),(1554869708,r59),(115056968,r2),(1151745584,r8),(2060454305,r8),(1324233780,r10),(213438749,r8),(1122147470,r8),(1263945292,r2),(1061858982,r59),(1200529888,r59),(1460765324,r8),(221990398,r8),(1382386799,r8),(143611873,r8),(1548364873,r59),(346950663,r8),(1677134986,r59),(732913383,r8),(441956103,r59),(563546957,r0),(41785972,r8),(32623466,r59),(203958435,r8),(137988831,r0),(1763711493,r59),(1531246528,r2),(1329160218,r59),(903799842,r10),(1223474517,r8),(701713532,r59),(144102277,r2),(463776952,r8),(2089499614,r59),(727203781,r10),(525117471,r59),(1821600536,r59),(512997567,r8),(2138720229,r59),(2030552780,r8),(1508791795,r59),(1747120743,r59),(1003689062,r8),(1899699745,r59),(1779974069,r8),(887942848,r59),(1873470593,r1),(964127381,r8),(708786144,r59),(1021057536,r8),(369250690,r1),(1607391125,r59),(303847240,r8),(1470616716,r59),(1645488901,r8),(1281900076,r59),(1384760753,r2),(1182674443,r59),(2082551475,r23),(642324730,r8),(1880465165,r59),(1862157896,r2),(421931151,r8),(1660071586,r59),(403342228,r23),(201255918,r59),(1870213143,r59),(1031825422,r8),(122482210,r59),(1057011037,r8),(147667825,r59),(1046200440,r59),(1027463948,r8),(937679819,r59),(241967362,r8),(1592491791,r59),(1769587706,r59),(451711623,r59),(1386899252,r59),(71019676,r59)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r70 : Rule 94 6 := cutRule 6 p2 w1
def f163 : ℕ := 0x1652ca52cb031418b302c5c5ffc0ffc0001c31e1c4070e0
def f164 : ℕ := 0x2aa554a555184942506952d007ffffc000e03101c7870e0
def s85 : List ℕ := [f163,f16,f164,f17,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b46 : Ban 94 7 s85 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(18595090,r70),(699324638,r5),(214433972,r19),(2114820353,r5),(686511228,r19),(2015741841,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f165 : ℕ := 0xebc
def s86 : List ℕ := [f3,f4,f5,f165]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w47 : Wide 6 3 s86 := viaSearch (by decide +kernel)
def r71 : Rule 94 7 := cutRule 7 p2 w47
def f166 : ℕ := 0x5a1fc
def f167 : ℕ := 0x5b44c
def f168 : ℕ := 0xfe9b0
def s87 : List ℕ := [f166,f167,f168]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w48 : Wide 10 3 s87 := viaSearch (by decide +kernel)
def p41 : Weak 94 10 := signedPick 6 [6,7,8,9,10,11,37,38,39,67] (by decide) (by decide) (by decide)
def r72 : Rule 94 6 := cutRule 6 p41 w48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w49 : Wide 10 2 s87 := viaSearch (by decide +kernel)
def r73 : Rule 94 6 := cutRule 6 p41 w49
def f169 : ℕ := 0xaf33f
def f170 : ℕ := 0x5d15ff3
def f171 : ℕ := 0x1a242ccc
def s88 : List ℕ := [f169,f170,f171]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w50 : Wide 15 3 s88 := viaSearch (by decide +kernel)
def p42 : Weak 94 15 := relaxed (pick [0,1,13,14,15,16,17,18,30,43,44,45,58,74,93] (by decide) (by decide) (by decide))
def r74 : Rule 94 6 := cutRule 6 p42 w50
def f172 : ℕ := 0x1042084208021410a0000001ffc00000001c31e1c000000
def s89 : List ℕ := [f172,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b47 : Ban 94 7 s89 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1490029101,r5),(376571718,r72),(189061099,r72),(2083074932,r73),(1750822810,r5),(1934060644,r72),(34512742,r5),(1088426397,r25),(1425893701,r5),(274058354,r25),(1024171026,r73),(1138845704,r73),(855884778,r5),(777506253,r5),(943484327,r25),(648746042,r72),(1967294860,r72),(2106150058,r20),(1680591932,r74),(2055600668,r5),(1425672234,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f173 : ℕ := 0x1259e
def f174 : ℕ := 0x17418
def f175 : ℕ := 0x3af86
def s90 : List ℕ := [f173,f174,f175]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w51 : Wide 9 3 s90 := viaSearch (by decide +kernel)
def p43 : Weak 94 9 := signedPick 16 [16,17,18,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r75 : Rule 94 6 := cutRule 6 p43 w51
def f176 : ℕ := 0xa2bfcf
def f177 : ℕ := 0x51530fc
def f178 : ℕ := 0xa484f33
def s91 : List ℕ := [f176,f177,f178]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w52 : Wide 14 3 s91 := viaSearch (by decide +kernel)
def p44 : Weak 94 14 := relaxed (pick [20,21,34,35,40,41,47,48,50,51,79,80,90,91] (by decide) (by decide) (by decide))
def r76 : Rule 94 6 := cutRule 6 p44 w52
def f179 : ℕ := 0x610c210c30100081302c5c40000ffc00000000004070e0
def s92 : List ℕ := [f179,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b48 : Ban 94 7 s92 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(130576617,r5),(1463663124,r75),(1922166665,r5),(504916840,r5),(1387486640,r25),(347115981,r25),(678309243,r25),(1922307729,r25),(1154945021,r5),(1076566496,r5),(1242544570,r25),(257726654,r20),(1979652175,r76),(207177264,r5),(1724732477,r5),(1441300440,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s93 : List ℕ := [f163,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b45 : Ban 94 8 s93 := viaRules (ws := [s85,s89,s92]) (consBan b46 (consBan b47 (consBan b48 (nilBan _ _))))
  (dictionary [(1895393253,r8),(1071831614,r8),(468978929,r8),(2058392754,r7),(631978430,r1),(1766711346,r1),(340297022,r29),(55248961,r1),(776318284,r29),(1243502580,r0),(1964571903,r1),(805978380,r1),(1519614080,r1),(916761395,r29),(41367682,r29),(1766092401,r0),(1163239716,r1),(855022594,r1),(1328156172,r1),(1576091917,r29),(362654217,r8),(1659349434,r1),(1907285179,r8),(755864273,r1),(1003800018,r8),(806446233,r1),(1802094533,r8),(923160795,r1),(1281851401,r10),(2002920724,r1),(128342055,r2),(849411378,r29),(1921675152,r10),(495260828,r29),(1200481759,r2),(1921551082,r1),(545615950,r1),(1089351703,r29),(1452196804,r29),(1570411258,r1),(1637285133,r37),(237094916,r0),(875321102,r0),(1555309820,r71),(2123685521,r8),(236437310,r1),(1145146031,r1),(158058785,r1),(1066767506,r1),(324036859,r8),(1824631217,r2),(398216893,r29),(57777034,r10),(778846357,r8),(1772756563,r2),(346342239,r29),(680968252,r10),(1402037575,r8),(1270106296,r29),(452806972,r8),(1656069016,r29),(1365111736,r8),(1486702590,r39),(964941605,r29),(955779099,r8),(1127114068,r29),(1061144464,r40),(539383479,r8),(597272522,r8),(1436153200,r1),(914392215,r8),(806224766,r1),(284463781,r8),(522792729,r8),(1926844695,r29),(675371731,r8),(555646055,r29),(1811098481,r8),(1819475745,r2),(1302404633,r1),(393061421,r1),(1992235970,r23),(565821646,r8),(285770891,r2),(1006840214,r29),(2118535988,r23),(1601464876,r1),(692121664,r8),(649142579,r1),(1887283014,r1),(1631941777,r8),(1944213169,r29),(1292406323,r1),(383063111,r8),(1227002873,r0),(246288702,r8),(421160887,r0),(57572062,r8),(645885129,r8),(1954981055,r1),(1045637843,r8),(1980166670,r1),(1070823458,r8),(1969356073,r8),(1950619581,r0),(1860835452,r8),(1165122995,r0),(368163777,r8),(545259692,r8),(1374867256,r8),(162571238,r8),(994175309,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f180 : ℕ := 0x1652ca52cb031418b302c5c7ffc0ffffff1ffffffc7ffff
def s94 : List ℕ := [f180,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b50 : Ban 94 7 s94 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1552479612,r25),(2051103287,r13),(151555385,r14),(1879173087,r14),(1070739637,r5),(1318675382,r13),(1639518235,r14),(1324033515,r13),(1442164450,r13),(290329103,r14),(1440748077,r13),(1558879012,r13),(1699440410,r25),(611920091,r14),(872155527,r13),(793777002,r13),(959755076,r14),(115041073,r14),(2122420807,r19),(1696862681,r19),(1232990739,r14),(2071871417,r13),(1441942983,r13),(1158510946,r14),(1842051395,r5),(496768873,r5),(1281603346,r14),(443215625,r13),(468401240,r13),(457590643,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f181 : ℕ := 0x1652ca52cb031418b302c5c7ffc0ffc0fd1cf3e7dc1f3e3
def s95 : List ℕ := [f181,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b51 : Ban 94 7 s95 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1301168861,r25),(620844776,r13),(542466251,r13),(1871110056,r19),(1445551930,r19),(1820560666,r13),(1190632232,r13),(1033550045,r5),(616782171,r5),(191904874,r13),(217090489,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f182 : ℕ := 0x4d39a739a6ed03e80fa03f01f83f07ff03ff0ff83fe0ffc
def s96 : List ℕ := [f16,f17,f18,f182,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b52 : Ban 94 7 s96 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(110947887,r25),(1810649068,r14),(996281025,r14),(257908685,r33),(1662851634,r13),(1584473109,r13),(680889082,r19),(255330956,r19),(630339692,r13),(411258,r13),(1990812718,r5),(486592815,r5),(1149167547,r13),(1174353162,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f183 : ℕ := 0x4d39a739a6ed03e80fa03f01f83f07c001fc03e01f803e0
def s97 : List ℕ := [f16,f17,f18,f183,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b53 : Ban 94 7 s97 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1815492631,r25),(1367710165,r14),(1662851634,r13),(1584473109,r13),(237950179,r19),(1959875700,r19),(187400789,r13),(1704956002,r13),(1547873815,r5),(43653912,r5),(706228644,r13),(731414259,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r77 : Rule 94 6 := cutRule 6 p8 w1
def f184 : ℕ := 0x75debbdebaf7fc000fdf8000003ff83f03fffc183fffc1c
def s98 : List ℕ := [f16,f17,f18,f20,f184,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b54 : Ban 94 7 s98 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(866810830,r25),(419028364,r14),(1752143968,r14),(2073734956,r31),(186486745,r13),(108108220,r13),(274086294,r77),(1576855938,r31),(1695098812,r19),(420528225,r19),(715083877,r13),(85155443,r13),(599192014,r5),(1242455758,r5),(1905030490,r13),(1930216105,r13),(1919405508,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f185 : ℕ := 0x75debbdebaf7fc000fdf8000003ff80001fcf0001f9f000
def s99 : List ℕ := [f16,f17,f18,f20,f185,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b55 : Ban 94 7 s99 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1512748012,r25),(1064965546,r14),(832423927,r13),(754045402,r13),(1399588344,r19),(231808758,r19),(715083877,r13),(85155443,r13),(1245129196,r5),(1888392940,r5),(403484025,r13),(428669640,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f186 : ℕ := 0x79ef3def3cfefff7e0000001ffc0003f03ffffffe060c1c
def s100 : List ℕ := [f16,f17,f18,f20,f21,f186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b56 : Ban 94 7 s100 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(536984484,r25),(89202018,r14),(2004144046,r13),(1925765521,r13),(1106925679,r19),(681367553,r19),(1056376289,r13),(426447855,r13),(401024675,r5),(1658789029,r5),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f187 : ℕ := 0x79ef3def3cfefff7e0000001ffc0000001fcf3e7c000000
def s101 : List ℕ := [f16,f17,f18,f20,f21,f187]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b57 : Ban 94 7 s101 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1795774642,r25),(1347992176,r14),(1115450557,r13),(1037072032,r13),(218232190,r19),(1940157711,r19),(167682800,r13),(1685238013,r13),(2075556903,r5),(571337000,r5),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f188 : ℕ := 0x3f02030c182060c1c
def s102 : List ℕ := [f188,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b49 : Ban 94 8 s102 := viaRules (ws := [s94,s95,s96,s97,s98,s99,s100,s101]) (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (nilBan _ _)))))))))
  (dictionary [(1388302694,r2),(282731223,r59),(2142237021,r1),(1639518235,r8),(1036665550,r8),(1890926270,r1),(1388207484,r8),(785354799,r8),(1106472726,r8),(901255,r59),(202091472,r0),(1125872713,r8),(1244003648,r8),(1126821233,r1),(1237604248,r29),(362210535,r29),(1484082569,r1),(1081025210,r8),(1875001641,r0),(2122937386,r59),(541886037,r1),(789821782,r59),(1896934770,r8),(80644385,r59),(755864273,r1),(1003800018,r8),(1009158151,r8),(879353341,r0),(1127289086,r8),(406509853,r10),(1448422029,r59),(64783055,r2),(197986510,r8),(1106695231,r8),(1769327799,r10),(1902531254,r8),(663756328,r8),(821361509,r2),(1863273685,r59),(866458803,r1),(1410194556,r29),(1773039657,r29),(1891254111,r1),(1958127986,r0),(557937769,r30),(1196163955,r30),(1876152673,r0),(297044727,r59),(557280163,r8),(1465988884,r8),(478901638,r8),(1387610359,r8),(644879712,r59),(1846865436,r2),(741293965,r59),(1537659939,r10),(953849453,r8),(432088468,r59),(36113474,r2),(1599786635,r8),(1078025650,r59),(284433099,r10),(1326345275,r59),(1590949149,r8),(773649825,r59),(1976911869,r8),(1685954589,r59),(1807545443,r0),(1285784458,r8),(1276621952,r59),(1447956921,r8),(1381987317,r0),(860226332,r59),(918115375,r59),(1756996053,r8),(1235235068,r59),(1127067619,r8),(605306634,r59),(843635582,r59),(100203901,r8),(996214584,r59),(876488908,r8),(2131941334,r59),(684593226,r2),(1726505402,r59),(820251366,r23),(624023107,r8),(1862163542,r59),(2079041524,r2),(1882813265,r8),(973470053,r59),(1979219071,r23),(873647600,r59),(969985432,r1),(60642220,r8),(1952784630,r59),(117572375,r8),(1613249176,r1),(703905964,r59),(1547845726,r8),(567131555,r59),(742003740,r8),(378414915,r59),(966727982,r59),(128340261,r8),(1366480696,r59),(153525876,r8),(1391666311,r59),(142715279,r59),(123978787,r8),(34194658,r59),(1485965848,r8),(689006630,r59),(866102545,r59),(1695710109,r59),(483414091,r59),(1315018162,r59)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f189 : ℕ := 0xf3d86
def f190 : ℕ := 0x35d030
def f191 : ℕ := 0x35d5be
def s103 : List ℕ := [f133,f189,f190,f191]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w53 : Wide 11 3 s103 := viaSearch (by decide +kernel)
def p45 : Weak 94 11 := signedPick 1 [1,2,3,4,12,14,16,17,18,54,60] (by decide) (by decide) (by decide)
def r78 : Rule 94 7 := cutRule 7 p45 w53
def r79 : Rule 94 7 := cutRule 7 p0 w40
def f192 : ℕ := 0x200400041000000100040c207c0ffc0fd00f307dc1f3f3
def s104 : List ℕ := [f192,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b59 : Ban 94 7 s104 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(540063627,r13),(1895393253,r14),(665203841,r5),(870180196,r5),(2069896086,r5),(1885738150,r27),(441240294,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f193 : ℕ := 0x1d30
def s105 : List ℕ := [f138,f193,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w54 : Wide 7 2 s105 := viaSearch (by decide +kernel)
def p46 : Weak 94 7 := signedPick 6 [6,7,8,9,10,11,66] (by decide) (by decide) (by decide)
def r80 : Rule 94 6 := cutRule 6 p46 w54
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w55 : Wide 7 3 s105 := viaSearch (by decide +kernel)
def r81 : Rule 94 6 := cutRule 6 p46 w55
def f194 : ℕ := 0x6b40c
def f195 : ℕ := 0xbe8f0
def s106 : List ℕ := [f141,f194,f195]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w56 : Wide 10 3 s106 := viaSearch (by decide +kernel)
def p47 : Weak 94 10 := signedPick 6 [6,7,8,9,10,11,38,39,66,67] (by decide) (by decide) (by decide)
def r82 : Rule 94 6 := cutRule 6 p47 w56
def f196 : ℕ := 0x127cf
def f197 : ℕ := 0x289f3
def f198 : ℕ := 0xc523c
def s107 : List ℕ := [f196,f197,f198]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w57 : Wide 10 3 s107 := viaSearch (by decide +kernel)
def p48 : Weak 94 10 := relaxed (pick [2,3,27,28,29,30,31,32,63,84] (by decide) (by decide) (by decide))
def r83 : Rule 94 6 := cutRule 6 p48 w57
def f199 : ℕ := 0x618c318c30d0e8000c5d0000003ff80003e3f0003fff000
def s108 : List ℕ := [f16,f17,f18,f20,f199,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b60 : Ban 94 7 s108 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1577082640,r18),(1129300174,r18),(88929515,r19),(420122777,r18),(1664121263,r18),(896758555,r19),(818380030,r19),(984358104,r18),(61877820,r80),(347497691,r81),(765633267,r19),(340075141,r19),(1257593767,r18),(1078283693,r19),(1937913276,r19),(1399588344,r19),(111734280,r19),(1183113974,r18),(498814441,r80),(1309463824,r82),(1952727568,r83),(467818653,r19),(493004268,r19),(1860611906,r81),(629308408,r81)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f200 : ℕ := 0xb0f
def f201 : ℕ := 0x2a5f3
def s109 : List ℕ := [f200,f149,f201]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w58 : Wide 9 3 s109 := viaSearch (by decide +kernel)
def p49 : Weak 94 9 := relaxed (pick [13,14,15,16,17,18,44,45,74] (by decide) (by decide) (by decide))
def r84 : Rule 94 6 := cutRule 6 p49 w58
def f202 : ℕ := 0x49cf
def s110 : List ℕ := [f138,f202,f153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w59 : Wide 8 3 s110 := viaSearch (by decide +kernel)
def p50 : Weak 94 8 := relaxed (pick [17,18,40,41,42,43,44,45] (by decide) (by decide) (by decide))
def r85 : Rule 94 6 := cutRule 6 p50 w59
def f203 : ℕ := 0xa214421450803c750207afa07c007fffc000f1fc000fff
def s111 : List ℕ := [f203,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b61 : Ban 94 7 s111 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(340075141,r19),(765633267,r19),(377701098,r18),(323072804,r19),(420528225,r19),(2077402279,r18),(464739721,r18),(1844860660,r19),(1766482135,r19),(110082282,r84),(753346026,r85),(1415920758,r19),(1441106373,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f204 : ℕ := 0x6bad75ad75d8ebc75c7d7afa07ffffffffe3ff1ffffffff
def s112 : List ℕ := [f16,f17,f18,f20,f204,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b58 : Ban 94 8 s112 := viaRules (ws := [s104,s108,s111]) (consBan b59 (consBan b60 (consBan b61 (nilBan _ _))))
  (dictionary [(929467448,r0),(922119528,r1),(1040250463,r1),(46725815,r1),(164856750,r1),(1286728784,r30),(592467997,r8),(1699580985,r1),(2030774247,r8),(806446233,r1),(1009158151,r8),(879353341,r0),(1127289086,r8),(1807452666,r8),(1925583601,r8),(798714118,r0),(1046649863,r30),(669105018,r78),(1212840771,r1),(1575685872,r1),(1693900326,r79),(1760774201,r0),(360583984,r30),(998810170,r30),(1678798888,r0),(99690942,r8),(359926378,r0),(1268635099,r0),(281547853,r0),(1190256574,r0),(447525927,r8),(1440189119,r0),(263174968,r2),(1107733359,r1),(434798499,r1),(1279356890,r1),(1243502580,r0),(2088060971,r30),(1081025210,r8),(202091472,r0),(2115549016,r10),(812623760,r0),(98809654,r2),(943368045,r30),(1763438065,r2),(460512809,r0),(915161133,r10),(1759719524,r30),(1393595364,r1),(576296040,r8),(1779558084,r1),(1488600804,r8),(1610191658,r0),(1088430673,r1),(1079268167,r8),(1250603136,r1),(1184633532,r0),(662872547,r8),(720761590,r8),(1559642268,r0),(1037881283,r8),(929713834,r0),(407952849,r8),(646281797,r8),(2050333763,r1),(798860799,r8),(679135123,r1),(1934587549,r8),(100448102,r2),(1466767478,r0),(945006493,r1),(1867995985,r10),(565070729,r8),(425882792,r2),(1270441183,r1),(1048550207,r10),(267385936,r0),(1893108598,r8),(772631647,r57),(2010772082,r30),(1755430845,r8),(2067702237,r1),(1415895391,r58),(506552179,r8),(1350491941,r30),(369777770,r8),(544649955,r30),(181061130,r8),(769374197,r8),(2078470123,r0),(1169126911,r8),(2103655738,r0),(1194312526,r8),(2092845141,r8),(2074108649,r30),(1984324520,r8),(1288612063,r30),(491652845,r8),(1949338869,r2),(646413613,r30),(451340585,r23),(1295898976,r8),(1602459618,r2),(299534362,r30),(2132791106,r23),(829865850,r8),(668748760,r8),(1498356324,r8),(286060306,r8),(1117664377,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f205 : ℕ := 0x2878
def f206 : ℕ := 0x2c9c
def f207 : ℕ := 0x3b64
def s113 : List ℕ := [f205,f206,f207]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w60 : Wide 7 4 s113 := viaSearch (by decide +kernel)
def p51 : Weak 94 7 := signedPick 40 [40,41,44,47,48,50,51] (by decide) (by decide) (by decide)
def r86 : Rule 94 7 := cutRule 7 p51 w60
def f208 : ℕ := 0x4d39a739a6eda3ed0fb43f2bf83f07c0fffccfe63f98fe3
def s114 : List ℕ := [f16,f17,f18,f208,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b63 : Ban 94 7 s114 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1962500879,r25),(1514718413,r14),(805541016,r14),(2049539502,r14),(1662851634,r13),(1584473109,r13),(440686669,r14),(384958427,r19),(2106883948,r19),(334409037,r13),(1851964250,r13),(1694882063,r5),(190662160,r5),(853236892,r13),(878422507,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f209 : ℕ := 0xc318631862d016803a01701f83f07c002fc0de02780ce0
def s115 : List ℕ := [f209,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b64 : Ban 94 7 s115 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1150741246,r25),(1662851634,r13),(1584473109,r13),(1237779869,r14),(1720682441,r19),(1295124315,r19),(1670133051,r13),(1040204617,r13),(883122430,r5),(1526386174,r5),(41477259,r13),(66662874,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f210 : ℕ := 0x75debbdebaf7fe850fdfa82a003ff800fffff2063fff303
def s116 : List ℕ := [f16,f17,f18,f20,f210,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b65 : Ban 94 7 s116 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1374673568,r25),(926891102,r14),(1461712191,r14),(694349483,r13),(615970958,r13),(765633267,r19),(340075141,r19),(715083877,r13),(85155443,r13),(1463414595,r14),(1107054752,r5),(1750318496,r5),(265409581,r13),(290595196,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f211 : ℕ := 0x34d69ad69a375c0003cb8000003ff80002ff300027e7000
def s117 : List ℕ := [f16,f17,f211,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b66 : Ban 94 7 s117 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1532688126,r25),(765633267,r19),(340075141,r19),(1619726749,r14),(715083877,r13),(85155443,r13),(852364041,r13),(773985516,r13),(1265069310,r5),(1908333054,r5),(423424139,r13),(448609754,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f212 : ℕ := 0x79ef3def3cfefff7ec14282bffc00000ffffffffd818303
def s118 : List ℕ := [f16,f17,f18,f20,f21,f212]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b67 : Ban 94 7 s118 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(96836424,r25),(1796537605,r14),(1087360208,r14),(183875047,r14),(1303760550,r14),(1563995986,r13),(1485617461,r13),(1651595535,r14),(666777619,r19),(241219493,r19),(616228229,r13),(2133783442,r13),(1850351405,r14),(462928434,r5),(1400388987,r5),(1233911732,r13),(1259097347,r13),(1880363423,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f213 : ℕ := 0x38e71ce71c3e5d72e0000001ffc0000002ff3df9c000000
def s119 : List ℕ := [f16,f17,f213,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b68 : Ban 94 7 s119 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1848275922,r25),(581335310,r5),(1490029101,r5),(1935314545,r14),(1233911732,r13),(1259097347,r13),(1167951837,r13),(1089573312,r13),(270733470,r19),(1992658991,r19),(220184080,r13),(1737739293,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f214 : ℕ := 0x4108210820c0a2850c14282a00000000fd00c2061818303
def s120 : List ℕ := [f16,f17,f214,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b62 : Ban 94 8 s120 := viaRules (ws := [s114,s115,s116,s117,s118,s119]) (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (nilBan _ _)))))))
  (dictionary [(1925115748,r1),(2035898763,r29),(1160505050,r29),(134893437,r1),(1262607737,r8),(955330781,r59),(1892126546,r1),(1584849590,r8),(522385547,r8),(215108591,r59),(1851545492,r1),(1544268536,r8),(1807452666,r8),(85376910,r0),(1925583601,r8),(1588116297,r59),(547745638,r8),(878938900,r59),(1802094533,r8),(1875001641,r0),(2122937386,r59),(1676231483,r86),(1924167228,r8),(1794362418,r0),(2042298163,r8),(282730695,r8),(1664753318,r1),(61005424,r29),(423850525,r29),(542064979,r1),(608938854,r0),(1356232284,r30),(1994458470,r30),(526963541,r0),(264061593,r10),(2104268284,r59),(1916336047,r2),(700350370,r8),(1609059091,r8),(1104576414,r10),(2036074384,r8),(797299458,r8),(2118918207,r2),(1811641251,r59),(1095339242,r59),(1355574678,r8),(116799752,r8),(1277196153,r8),(38421227,r8),(1443174227,r59),(241760017,r8),(1571944340,r59),(627722737,r8),(336765457,r59),(458356311,r0),(2084078973,r8),(2074916467,r59),(98767789,r8),(32798185,r0),(1658520847,r59),(127518396,r2),(1967725087,r59),(2045522677,r10),(112523059,r8),(1738245721,r59),(56053588,r2),(270537617,r8),(1896260279,r59),(1061744551,r10),(754467595,r59),(1716409890,r59),(407806921,r8),(2033529583,r59),(1925362134,r8),(1403601149,r59),(1641930097,r59),(898498416,r8),(1794509099,r59),(1674783423,r8),(782752202,r59),(1768279947,r1),(858936735,r8),(603595498,r59),(915866890,r8),(264060044,r1),(1502200479,r59),(198656594,r8),(1365426070,r59),(1540298255,r8),(1176709430,r59),(1549856704,r2),(1242579748,r59),(380103306,r23),(982169562,r8),(72826350,r59),(2131542804,r2),(586125413,r8),(1824265848,r59),(1044277933,r23),(737000977,r59),(1765022497,r59),(926634776,r8),(17291564,r59),(951820391,r8),(42477179,r59),(941009794,r59),(922273302,r8),(832489173,r59),(136776716,r8),(1487301145,r59),(1664397060,r59),(346520977,r59),(1281708606,r59),(2113312677,r59)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f215 : ℕ := 0xb7c
def s121 : List ℕ := [f3,f4,f215,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w61 : Wide 6 3 s121 := viaSearch (by decide +kernel)
def r87 : Rule 94 7 := cutRule 7 p2 w61
def f216 : ℕ := 0x6a1fc
def f217 : ℕ := 0x6e930
def f218 : ℕ := 0xfb4cc
def s122 : List ℕ := [f216,f217,f218]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w62 : Wide 10 3 s122 := viaSearch (by decide +kernel)
def p52 : Weak 94 10 := signedPick 6 [6,7,8,9,10,11,23,24,25,66] (by decide) (by decide) (by decide)
def r88 : Rule 94 6 := cutRule 6 p52 w62
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w63 : Wide 10 2 s122 := viaSearch (by decide +kernel)
def r89 : Rule 94 6 := cutRule 6 p52 w63
def f219 : ℕ := 0x24799f
def f220 : ℕ := 0x3519fe7
def f221 : ℕ := 0xc8a2678
def s123 : List ℕ := [f219,f220,f221]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w64 : Wide 14 3 s123 := viaSearch (by decide +kernel)
def p53 : Weak 94 14 := relaxed (pick [2,3,18,27,28,29,30,31,32,42,43,45,63,84] (by decide) (by decide) (by decide))
def r90 : Rule 94 6 := cutRule 6 p53 w64
def f222 : ℕ := 0x208410841010480000490000003ff80000e030000787000
def s124 : List ℕ := [f16,f222,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b70 : Ban 94 7 s124 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2104378318,r88),(1801614340,r89),(231808758,r19),(1750686663,r88),(866308772,r19),(1197502034,r18),(1078283693,r19),(319873141,r88),(567808886,r19),(294016873,r18),(1092311388,r18),(1447333786,r89),(1736697310,r89),(1674137812,r19),(1595759287,r19),(1761737361,r18),(2086843081,r20),(582623178,r90),(1741832411,r88),(500706806,r88),(1245197910,r19),(1270383525,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f223 : ℕ := 0x1219c
def f224 : ℕ := 0x17218
def f225 : ℕ := 0x3ad84
def s125 : List ℕ := [f223,f224,f225]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w65 : Wide 9 3 s125 := viaSearch (by decide +kernel)
def p54 : Weak 94 9 := signedPick 29 [29,30,32,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r91 : Rule 94 6 := cutRule 6 p54 w65
def f226 : ℕ := 0x28d7f3f
def f227 : ℕ := 0x45203d8
def f228 : ℕ := 0x920bce7
def s126 : List ℕ := [f226,f227,f228]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w66 : Wide 14 3 s126 := viaSearch (by decide +kernel)
def p55 : Weak 94 14 := relaxed (pick [3,17,18,29,30,32,40,41,42,43,44,45,63,64] (by decide) (by decide) (by decide))
def r92 : Rule 94 6 := cutRule 6 p55 w66
def f229 : ℕ := 0xa21442145080142502052d007c007c000000101c0000e0
def s127 : List ℕ := [f229,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b71 : Ban 94 7 s127 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1695098812,r19),(87432951,r91),(323072804,r19),(981021525,r19),(927619312,r18),(1462440401,r18),(1265086616,r18),(113251269,r18),(695077693,r19),(616699168,r19),(782677242,r18),(1107782962,r27),(1751046706,r92),(266137791,r19),(291323406,r19),(280512809,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s128 : List ℕ := [f16,f164,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b69 : Ban 94 8 s128 := viaRules (ws := [s85,s124,s127]) (consBan b46 (consBan b70 (consBan b71 (nilBan _ _))))
  (dictionary [(2058392754,r7),(872182060,r0),(1770822022,r1),(584611328,r1),(2013042942,r1),(826832248,r1),(73739371,r0),(1035012324,r30),(1046182010,r0),(1038834090,r1),(1156965025,r1),(163440377,r1),(281571312,r1),(1403443346,r30),(282730695,r8),(1125872713,r8),(1244003648,r8),(461246814,r0),(709182559,r8),(1816295547,r1),(5162,r8),(923160795,r1),(85376910,r0),(798714118,r0),(1046649863,r30),(1676231483,r86),(1924167228,r8),(1794362418,r0),(2042298163,r8),(785819580,r48),(1329555333,r1),(1692400434,r1),(1810614888,r87),(1170753545,r10),(2132026498,r0),(376585444,r2),(1337858397,r30),(1402677915,r10),(216467221,r30),(388194087,r2),(1349467040,r0),(1877488763,r0),(477298546,r30),(1115524732,r30),(1795513450,r0),(216405504,r8),(476640940,r0),(1385349661,r0),(398262415,r0),(1306971136,r0),(564240489,r8),(1510309926,r1),(693010602,r8),(1896272646,r1),(1605315366,r8),(877827359,r2),(213377650,r0),(1839100312,r1),(1855839634,r10),(669628940,r8),(1180775016,r2),(2142047969,r1),(2046250887,r10),(1381801178,r0),(860040193,r8),(1726906220,r0),(1205145235,r1),(1195982729,r8),(1367317698,r1),(1301348094,r0),(779587109,r8),(837476152,r8),(1676356830,r0),(1154595845,r8),(1046428396,r0),(524667411,r8),(762996359,r8),(19564678,r1),(915575361,r8),(795849685,r1),(2051302111,r8),(889346209,r57),(2127486644,r30),(1872145407,r8),(36933152,r1),(1532609953,r58),(623266741,r8),(1222333663,r2),(36122969,r30),(2035296446,r23),(849085752,r8),(528592012,r2),(1489864965,r30),(107424866,r23),(1068697819,r8),(1467206503,r30),(486492332,r8),(661364517,r30),(297775692,r8),(886088759,r8),(47701038,r0),(1285841473,r8),(72886653,r0),(1311027088,r8),(62076056,r8),(43339564,r30),(2101039082,r8),(1405326625,r30),(608367407,r8),(785463322,r8),(1615070886,r8),(402774868,r8),(1234378939,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r93 : Rule 94 7 := cutRule 7 p8 w9
def f230 : ℕ := 0x5d0c
def f231 : ℕ := 0xeac0
def s129 : List ℕ := [f152,f230,f231]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w67 : Wide 8 3 s129 := viaSearch (by decide +kernel)
def p56 : Weak 94 8 := signedPick 29 [29,30,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r94 : Rule 94 6 := cutRule 6 p56 w67
def f232 : ℕ := 0x2aa554a555184942506952d007fff83f02e33c19e3e7c1c
def s130 : List ℕ := [f16,f232,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b73 : Ban 94 7 s130 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(282730695,r14),(135175799,r19),(1428214665,r94)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f233 : ℕ := 0xe8fc
def f234 : ℕ := 0xfab0
def s131 : List ℕ := [f233,f110,f234]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w68 : Wide 8 3 s131 := viaSearch (by decide +kernel)
def p57 : Weak 94 8 := signedPick 13 [13,14,15,16,17,18,24,25] (by decide) (by decide) (by decide)
def r95 : Rule 94 6 := cutRule 6 p57 w68
def f235 : ℕ := 0x17430
def f236 : ℕ := 0x3dacc
def s132 : List ℕ := [f149,f235,f236]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w69 : Wide 9 3 s132 := viaSearch (by decide +kernel)
def p58 : Weak 94 9 := signedPick 27 [27,28,29,30,31,32,42,43,84] (by decide) (by decide) (by decide)
def r96 : Rule 94 6 := cutRule 6 p58 w69
def f237 : ℕ := 0x48ce
def f238 : ℕ := 0x5c0c
def f239 : ℕ := 0xebc2
def s133 : List ℕ := [f237,f238,f239]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w70 : Wide 8 3 s133 := viaSearch (by decide +kernel)
def p59 : Weak 94 8 := signedPick 1 [1,3,13,14,15,16,17,18] (by decide) (by decide) (by decide)
def r97 : Rule 94 6 := cutRule 6 p59 w70
def p60 : Weak 94 8 := signedPick 1 [1,3,27,28,29,30,31,32] (by decide) (by decide) (by decide)
def r98 : Rule 94 6 := cutRule 6 p60 w70
def f240 : ℕ := 0x4518a318a2c1a28d0f142d2bf80007ffff1fcffe3c78fff
def s134 : List ℕ := [f16,f17,f18,f240,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b74 : Ban 94 7 s134 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(191341070,r25),(2068304775,r95),(1662851634,r13),(1497400678,r96),(1779544052,r97),(763331003,r19),(659840667,r5),(1717743398,r98),(1965679143,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f241 : ℕ := 0x5057f1f
def f242 : ℕ := 0x7e00fe0
def f243 : ℕ := 0x18b8d3f3
def f244 : ℕ := 0x1a5a2cfc
def s135 : List ℕ := [f241,f242,f243,f244]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w71 : Wide 15 4 s135 := viaSearch (by decide +kernel)
def p61 : Weak 94 15 := relaxed (pick [0,1,2,3,4,12,13,14,15,16,17,18,54,60,93] (by decide) (by decide) (by decide))
def r99 : Rule 94 7 := cutRule 7 p61 w71
def f245 : ℕ := 0x2513c
def f246 : ℕ := 0x35a0c
def f247 : ℕ := 0x35bcc
def f248 : ℕ := 0x3f5f0
def s136 : List ℕ := [f245,f246,f247,f248]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w72 : Wide 9 4 s136 := viaSearch (by decide +kernel)
def p62 : Weak 94 9 := signedPick 13 [13,14,15,16,17,18,20,21,25] (by decide) (by decide) (by decide)
def r100 : Rule 94 7 := cutRule 7 p62 w72
def f249 : ℕ := 0x88a2a023cfc
def f250 : ℕ := 0x9da3a03fcfc
def f251 : ℕ := 0xacb6b400c0c
def f252 : ℕ := 0xdfebe83f0f0
def f253 : ℕ := 0xeefc003ff00
def s137 : List ℕ := [f249,f250,f251,f252,f253]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w73 : Wide 22 5 s137 := viaSearch (by decide +kernel)
def p63 : Weak 94 22 := signedPick 27 [27,28,29,30,31,32,38,39,40,41,42,43,44,45,49,50,51,53,83,84,85,86] (by decide) (by decide) (by decide)
def r101 : Rule 94 7 := cutRule 7 p63 w73
def f254 : ℕ := 0x6855fe3f
def f255 : ℕ := 0x7f003fc0
def f256 : ℕ := 0x185a347d3
def f257 : ℕ := 0x192a8b9fc
def s138 : List ℕ := [f254,f255,f256,f257]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w74 : Wide 17 4 s138 := viaSearch (by decide +kernel)
def p64 : Weak 94 17 := relaxed (pick [0,1,2,3,4,11,12,13,14,15,16,17,18,25,54,60,93] (by decide) (by decide) (by decide))
def r102 : Rule 94 7 := cutRule 7 p64 w74
def f258 : ℕ := 0x802ca30060
def s139 : List ℕ := [f258,f71,f72,f73]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w75 : Wide 21 3 s139 := viaSearch (by decide +kernel)
def r103 : Rule 94 6 := cutRule 6 p20 w75
def f259 : ℕ := 0x28fc
def f260 : ℕ := 0x6dcc
def f261 : ℕ := 0xba30
def s140 : List ℕ := [f259,f260,f261]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w76 : Wide 8 2 s140 := viaSearch (by decide +kernel)
def p65 : Weak 94 8 := signedPick 40 [40,41,47,48,50,51,90,91] (by decide) (by decide) (by decide)
def r104 : Rule 94 6 := cutRule 6 p65 w76
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w77 : Wide 8 3 s140 := viaSearch (by decide +kernel)
def r105 : Rule 94 6 := cutRule 6 p65 w77
def f262 : ℕ := 0x347c
def f263 : ℕ := 0x3d70
def s141 : List ℕ := [f262,f2,f263]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w78 : Wide 7 3 s141 := viaSearch (by decide +kernel)
def p66 : Weak 94 7 := signedPick 27 [27,28,29,30,31,32,39] (by decide) (by decide) (by decide)
def r106 : Rule 94 6 := cutRule 6 p66 w78
def p67 : Weak 94 8 := signedPick 27 [27,28,29,30,31,32,43,45] (by decide) (by decide) (by decide)
def r107 : Rule 94 6 := cutRule 6 p67 w68
def f264 : ℕ := 0x15a0c
def f265 : ℕ := 0x3f4f0
def s142 : List ℕ := [f149,f264,f265]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w79 : Wide 9 3 s142 := viaSearch (by decide +kernel)
def p68 : Weak 94 9 := signedPick 13 [13,14,15,16,17,18,44,45,74] (by decide) (by decide) (by decide)
def r108 : Rule 94 6 := cutRule 6 p68 w79
def p69 : Weak 94 8 := relaxed (pick [2,3,27,28,29,30,31,32] (by decide) (by decide) (by decide))
def r109 : Rule 94 6 := cutRule 6 p69 w59
def p70 : Weak 94 8 := signedPick 13 [13,14,15,16,17,18,43,45] (by decide) (by decide) (by decide)
def r110 : Rule 94 6 := cutRule 6 p70 w68
def f266 : ℕ := 0x75debbdebaf7fc080fdf8501f83fffc003fff3e03fff3e0
def s143 : List ℕ := [f16,f17,f18,f20,f266,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b75 : Ban 94 7 s143 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1606529050,r103),(1158746584,r104),(1693567673,r104),(926204965,r105),(847826440,r106),(830912270,r96),(1428214665,r94),(1779544052,r97),(2001162498,r107),(742754844,r77),(1693558856,r77),(336704989,r77),(1338910234,r108),(1982173978,r109),(497265063,r98),(522450678,r110)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f267 : ℕ := 0x71ce39ce38f6fc000cdf8000003ff80002e3f00023ff000
def s144 : List ℕ := [f16,f17,f18,f20,f267,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b76 : Ban 94 7 s144 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(521896915,r18),(74114449,r18),(608935538,r18),(1989056477,r19),(1910677952,r19),(2076656026,r77),(57942492,r31),(135175799,r19),(1593950350,r19),(981617720,r77),(1597044569,r19),(1401488427,r31),(763331003,r19),(766107429,r31),(1777648756,r31),(254278099,r108),(897541843,r109),(1560116575,r19),(1585302190,r19),(231914471,r61),(126804305,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r111 : Rule 94 7 := cutRule 7 p58 w69
def r112 : Rule 94 7 := cutRule 7 p56 w67
def r113 : Rule 94 7 := cutRule 7 p59 w70
def r114 : Rule 94 7 := cutRule 7 p67 w68
def r115 : Rule 94 7 := cutRule 7 p68 w79
def r116 : Rule 94 7 := cutRule 7 p69 w59
def r117 : Rule 94 7 := cutRule 7 p60 w70
def r118 : Rule 94 7 := cutRule 7 p70 w68
def f268 : ℕ := 0x41082108201000803000501f80007c0011c03e01c003e0
def s145 : List ℕ := [f268,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b72 : Ban 94 8 s145 := viaRules (ws := [s130,s134,s143,s144]) (consBan b73 (consBan b74 (consBan b75 (consBan b76 (nilBan _ _)))))
  (dictionary [(849341935,r2),(2035922728,r2),(1433070043,r2),(1429918545,r10),(2013646653,r93),(1218130943,r0),(1801859051,r10),(71105366,r10),(2047384648,r10),(483629109,r93),(668637165,r11),(779420180,r1),(2051510114,r1),(1025898501,r48),(613165635,r10),(1196893743,r93),(556314038,r10),(1703472533,r8),(139716994,r10),(1281851401,r10),(1865579509,r93),(331637714,r1),(1438750702,r1),(1769943964,r1),(545615950,r1),(866458803,r1),(669105018,r78),(1664753318,r1),(785819580,r48),(731127481,r10),(406146868,r1),(1314855589,r93),(1554863173,r2),(43301767,r1),(952010488,r2),(591235197,r99),(1499943918,r93),(99753701,r2),(737979887,r93),(509259884,r100),(1417968605,r2),(1986344306,r93),(99096095,r101),(1007804816,r2),(20717570,r102),(929426291,r93),(186695644,r2),(1757012546,r2),(193257007,r2),(129894512,r10),(1235383605,r10),(713622620,r93),(1192746024,r2),(150751470,r10),(1776474132,r2),(1361157577,r10),(1944885685,r93),(1132765081,r2),(315465757,r93),(1518727801,r2),(1227770521,r93),(1349361375,r111),(827600390,r2),(818437884,r93),(989772853,r2),(923803249,r112),(402042264,r93),(459931307,r2),(1298811985,r113),(777051000,r93),(668883551,r114),(147122566,r2),(385451514,r93),(880794759,r10),(1789503480,r2),(538030516,r2),(1657079766,r10),(418304840,r2),(1673757266,r2),(796962079,r2),(1380690187,r2),(660004569,r10),(1243732677,r93),(1390564684,r2),(1974292792,r2),(738562943,r10),(1322291051,r93),(511801364,r115),(1749941799,r2),(1494600562,r10),(1806871954,r2),(1155065108,r116),(245721896,r10),(1089661658,r2),(108947487,r10),(283819672,r2),(2067714494,r10),(508543914,r2),(1817639840,r117),(908296628,r10),(1842825455,r118),(933482243,r2),(1832014858,r10),(1813278366,r2),(1723494237,r2),(1027781780,r2),(230822562,r2),(407918477,r2),(1237526041,r2),(25230023,r2),(856834094,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r119 : Rule 94 7 := cutRule 7 p2 w9
def p71 : Weak 94 9 := signedPick 6 [6,7,8,9,10,11,23,24,66] (by decide) (by decide) (by decide)
def r120 : Rule 94 6 := cutRule 6 p71 w69
def f269 : ℕ := 0xa21442145080140102052c007ffffc002e03d01e787cf0
def s146 : List ℕ := [f269,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b78 : Ban 94 7 s146 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1616153461,r31),(363868285,r120),(771098703,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r121 : Rule 94 7 := cutRule 7 p71 w69
def f270 : ℕ := 0x11225c60c803c0c0060
def f271 : ℕ := 0x264c8296321c3804318
def f272 : ℕ := 0x2ad5b7bda5e00039c00
def f273 : ℕ := 0x2ad5b7bda5e3f8fdcf8
def f274 : ℕ := 0x3366def401fc00fff00
def s147 : List ℕ := [f270,f271,f272,f273,f274]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w80 : Wide 37 5 s147 := viaSearch (by decide +kernel)
def p72 : Weak 94 37 := signedPick 5 [5,6,7,12,13,19,21,22,26,27,33,34,35,36,40,46,47,48,49,51,66,67,68,71,72,73,76,77,78,79,82,83,84,87,88,89,90] (by decide) (by decide) (by decide)
def r122 : Rule 94 7 := cutRule 7 p72 w80
def f275 : ℕ := 0xc6633b4d1a37c3e1ff9e3c7
def f276 : ℕ := 0x16ab550d370dffc1fe3ffe3f
def f277 : ℕ := 0x2b55aa628a7683c01e011c07
def f278 : ℕ := 0x2b55aa628a7683ffffc71fff
def f279 : ℕ := 0x39dceefbec007fc001fffc00
def s148 : List ℕ := [f275,f276,f277,f278,f279]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w81 : Wide 47 5 s148 := viaSearch (by decide +kernel)
def p73 : Weak 94 47 := relaxed (pick [5,6,7,12,13,14,19,20,21,22,26,27,28,33,34,35,36,40,41,46,47,48,49,50,51,66,67,68,69,71,72,73,74,76,77,78,79,80,82,83,84,85,87,88,89,90,91] (by decide) (by decide) (by decide))
def r123 : Rule 94 6 := cutRule 6 p73 w81
def f280 : ℕ := 0x555aab5aaae714000f828000003ff80003fcf0003f9f000
def s149 : List ℕ := [f16,f17,f18,f20,f280,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b79 : Ban 94 7 s149 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(426975808,r25),(2126676989,r25),(514014431,r25),(1312308946,r25),(1294605289,r5),(171916950,r5),(1894135370,r5),(1815756845,r5),(363868285,r120),(73391036,r33),(110822241,r123),(134751249,r5),(780263729,r5),(159356992,r5),(802620736,r5),(1465195468,r5),(1490381083,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f281 : ℕ := 0xa214421450803f8b0207fc7ffc007c0fc000fe7c000ff3
def s150 : List ℕ := [f281,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b80 : Ban 94 7 s150 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(771098703,r19),(135029858,r19),(1157498784,r25),(1994331146,r13),(1274908865,r13),(709716318,r14),(538921,r14),(1244537407,r14),(477174699,r70),(398796174,r13),(889879968,r5),(1533143712,r5),(48234797,r13),(73420412,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f282 : ℕ := 0xba3bc
def f283 : ℕ := 0xbeb30
def f284 : ℕ := 0xfb48c
def s151 : List ℕ := [f282,f283,f284]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w82 : Wide 10 3 s151 := viaSearch (by decide +kernel)
def p74 : Weak 94 10 := signedPick 5 [5,7,12,14,19,20,69,74,76,80] (by decide) (by decide) (by decide)
def r124 : Rule 94 6 := cutRule 6 p74 w82
def f285 : ℕ := 0x596b2d6b2cee17f0a0000001ffc0000003fcffe7c000000
def s152 : List ℕ := [f16,f17,f18,f20,f285,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b81 : Ban 94 7 s152 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(57366769,r25),(1757067950,r25),(144405392,r25),(1524526331,r5),(1446147806,r5),(2075556903,r5),(571337000,r5),(328514136,r5),(589692918,r5),(627307964,r120),(201749838,r124),(576758574,r5),(2094313787,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f286 : ℕ := 0x48733
def f287 : ℕ := 0xa2bcf
def s153 : List ℕ := [f149,f286,f287]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w83 : Wide 10 3 s153 := viaSearch (by decide +kernel)
def p75 : Weak 94 10 := relaxed (pick [17,18,29,30,40,41,42,43,44,45] (by decide) (by decide) (by decide))
def r125 : Rule 94 6 := cutRule 6 p75 w83
def f288 : ℕ := 0x610c210c30100081fa2ffc6003fffc0fc0000003f9fff3
def s154 : List ℕ := [f288,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b82 : Ban 94 7 s154 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(571337000,r5),(2075556903,r5),(462202725,r25),(1187247766,r13),(400825351,r13),(14420259,r14),(1452726509,r14),(549241348,r14),(1929362287,r70),(1850983762,r13),(1032143920,r120),(606585794,r125),(981594530,r13),(351666096,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f289 : ℕ := 0x5f7bef7befef17f8bfa2ffc7ffffffc0fffcffe7ff9fff3
def s155 : List ℕ := [f16,f17,f18,f20,f289,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b77 : Ban 94 8 s155 := viaRules (ws := [s146,s149,s150,s152,s154]) (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (nilBan _ _))))))
  (dictionary [(1323155933,r29),(447762220,r29),(1569634254,r1),(875373467,r29),(1982486455,r29),(166196070,r29),(1089351703,r29),(1410194556,r29),(1212840771,r1),(61005424,r29),(1329555333,r1),(1554863173,r2),(43301767,r1),(952010488,r2),(313960380,r2),(1858591342,r2),(1068097075,r1),(1976805796,r119),(2043679671,r2),(643489454,r119),(1281715640,r2),(1961704358,r119),(382596412,r2),(642831848,r1),(1551540569,r119),(564453323,r1),(1473162044,r2),(730431397,r119),(731127481,r10),(1724115414,r2),(781519597,r2),(1908983458,r119),(555920284,r0),(1683384145,r2),(145960910,r2),(1273424771,r119),(285694430,r8),(1413158291,r2),(140955364,r2),(1268419225,r119),(688662138,r1),(1816125999,r2),(1263945292,r2),(243925506,r119),(849341935,r2),(1676500834,r119),(859201510,r2),(2062463554,r119),(1771506274,r2),(1893097128,r121),(1371336143,r119),(1362173637,r2),(1533508606,r119),(1467539002,r122),(945778017,r2),(1003667060,r119),(1842547738,r1),(1320786753,r2),(1212619304,r1),(690858319,r119),(929187267,r2),(1081766269,r119),(962040593,r119),(70009372,r119),(1097824917,r2),(599566116,r2),(77805131,r119),(1387659926,r2),(367640140,r119),(1878048532,r2),(858028746,r119),(1828347893,r2),(1330089092,r2),(808328107,r119),(1055537117,r1),(146193905,r119),(2038336315,r2),(203124060,r119),(1698800861,r1),(789457649,r2),(1633397411,r119),(652683240,r2),(827555425,r119),(463966600,r2),(1052279667,r119),(213891946,r1),(1452032381,r2),(239077561,r1),(1477217996,r119),(228266964,r2),(209530472,r119),(119746343,r119),(1571517533,r119),(774558315,r119),(340633651,r2),(229957077,r2),(1468097512,r119),(198227611,r2),(1325691472,r119),(2048018494,r2),(1027998708,r119),(745469607,r2),(634793033,r2),(1872933468,r119),(951654230,r119),(1781261794,r119),(568965776,r119),(1400569847,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f290 : ℕ := 0x2284508451104802504940d007c0ffff00033119c4670fc
def s156 : List ℕ := [f16,f290,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b84 : Ban 94 7 s156 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def f291 : ℕ := 0x50bc
def f292 : ℕ := 0x3da8c
def s157 : List ℕ := [f291,f292,f265]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w84 : Wide 9 4 s157 := viaSearch (by decide +kernel)
def p76 : Weak 94 9 := signedPick 13 [13,14,15,16,17,18,22,23,71] (by decide) (by decide) (by decide)
def r126 : Rule 94 7 := cutRule 7 p76 w84
def f293 : ℕ := 0x79ef3def3cfefff7eca03a01ffff000003ffffffe380c00
def s158 : List ℕ := [f16,f17,f18,f20,f21,f293]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b85 : Ban 94 7 s158 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(600326135,r25),(152543669,r25),(687364758,r25),(2067485697,r5),(1989107172,r77),(1170267330,r96),(744709204,r94),(1119717940,r5),(489789506,r5),(2075556903,r5),(571337000,r5),(221466824,r5),(507843233,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f294 : ℕ := 0x30c618c61812fc17e0000001ffc00000011ff3ffc000000
def s159 : List ℕ := [f16,f17,f294,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b86 : Ban 94 7 s159 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1972395230,r25),(2075556903,r5),(571337000,r5),(694301147,r77),(1524612764,r25),(2059433853,r25),(2109048782,r31),(1773183854,r5),(493060153,r77),(1860879308,r77),(761596027,r5),(426181590,r31),(1292071145,r5),(1213692620,r61),(1379670694,r77),(394852778,r96),(2116778299,r94),(576124432,r77),(2090945469,r77),(344303388,r5),(1861858601,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f295 : ℕ := 0x4929252924ec03e00ca03a00003f000002e00c002380c00
def s160 : List ℕ := [f16,f17,f18,f295,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b83 : Ban 94 8 s160 := viaRules (ws := [s156,s158,s159]) (consBan b84 (consBan b85 (consBan b86 (nilBan _ _))))
  (dictionary [(1575218019,r1),(1686001034,r29),(810607321,r29),(1932479355,r1),(1238218568,r29),(197847909,r29),(529041171,r29),(1452196804,r29),(1773039657,r29),(1575685872,r1),(423850525,r29),(1692400434,r1),(313960380,r2),(368282380,r2),(1858591342,r2),(859360186,r10),(202185501,r93),(859708570,r0),(202533885,r10),(1628398359,r10),(971223674,r93),(1231814829,r10),(1756956018,r10),(1099781333,r93),(1382959910,r1),(725785225,r10),(1842415989,r10),(1185241304,r93),(595926095,r8),(2086235057,r10),(406146868,r1),(1314855589,r93),(2033794861,r126),(795019935,r2),(1430942176,r1),(192167250,r2),(259041125,r93),(1006334555,r2),(1644560741,r93),(177065812,r2),(745441513,r93),(1005676949,r1),(1914385670,r2),(927298424,r1),(1836007145,r93),(1093276498,r2),(1972030274,r10),(2039345935,r2),(1222046611,r93),(277825008,r2),(2134351375,r93),(108458582,r111),(1734181244,r2),(1725018738,r93),(1896353707,r2),(1830384103,r112),(1308623118,r93),(1366512161,r2),(57909192,r1),(1683631854,r93),(1575464405,r1),(1053703420,r2),(1292032368,r93),(1451443913,r2),(794269228,r2),(1955849050,r10),(1298674365,r93),(821347252,r2),(164172567,r2),(1541885741,r10),(884711056,r93),(548600687,r2),(1444611370,r2),(1324885694,r2),(432854473,r2),(1418382218,r1),(509039006,r2),(253697769,r10),(565969161,r2),(2061645962,r1),(1152302750,r10),(1996242512,r2),(1015528341,r10),(1190400526,r2),(826811701,r10),(1415124768,r2),(576737047,r1),(1814877482,r10),(601922662,r1),(1840063097,r2),(591112065,r10),(360385,r2),(1490669347,r2),(883593017,r10),(1135761544,r10),(226418332,r93),(108178465,r2),(360346992,r10),(1598487427,r2),(2119852345,r10),(1462677660,r93),(572375573,r2),(482591444,r2),(1934362634,r2),(1137403416,r2),(1314499331,r2),(2144106895,r2),(931810877,r2),(1763414948,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w85 : Wide 7 3 s39 := viaSearch (by decide +kernel)
def r127 : Rule 94 6 := cutRule 6 p23 w85
def f296 : ℕ := 0x28a514a51418494240691210003f07ff02e30d1827e0cec
def s161 : List ℕ := [f16,f296,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b88 : Ban 94 7 s161 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(684713708,r14),(395489183,r127),(324154708,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p77 : Weak 94 8 := signedPick 1 [1,3,6,7,8,9,10,11] (by decide) (by decide) (by decide)
def r128 : Rule 94 6 := cutRule 6 p77 w70
def f297 : ℕ := 0x534a694a69c2b695bc16e8ee07c0f83fff03fe1ff87ff1f
def s162 : List ℕ := [f16,f17,f18,f20,f297,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b89 : Ban 94 7 s162 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1927589157,r128),(1584473109,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f298 : ℕ := 0x37430
def f299 : ℕ := 0x375f0
def f300 : ℕ := 0x3dbcc
def s163 : List ℕ := [f245,f298,f299,f300]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w86 : Wide 9 4 s163 := viaSearch (by decide +kernel)
def p78 : Weak 94 9 := signedPick 27 [27,28,29,30,31,32,34,35,37] (by decide) (by decide) (by decide)
def r129 : Rule 94 7 := cutRule 7 p78 w86
def f301 : ℕ := 0x14b9f3
def f302 : ℕ := 0x30a0e3c
def f303 : ℕ := 0xcc1570f
def f304 : ℕ := 0xfe02fc0
def s164 : List ℕ := [f301,f302,f303,f304]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w87 : Wide 14 4 s164 := viaSearch (by decide +kernel)
def p79 : Weak 94 14 := relaxed (pick [6,7,8,9,10,11,19,21,22,23,24,25,66,77] (by decide) (by decide) (by decide))
def r130 : Rule 94 7 := cutRule 7 p79 w87
def f305 : ℕ := 0x398149c1e
def f306 : ℕ := 0x39e5d8706
def f307 : ℕ := 0x3fd013f80
def f308 : ℕ := 0x3fdb61818
def s165 : List ℕ := [f305,f306,f307,f308]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w88 : Wide 17 4 s165 := viaSearch (by decide +kernel)
def p80 : Weak 94 17 := signedPick 3 [3,6,7,8,9,10,11,18,19,21,22,23,24,25,61,66,77] (by decide) (by decide) (by decide)
def r131 : Rule 94 7 := cutRule 7 p80 w88
def f309 : ℕ := 0xd49f3fcf
def f310 : ℕ := 0x182a23c3f3
def f311 : ℕ := 0xe60144e03c
def f312 : ℕ := 0xe745cc3c0c
def f313 : ℕ := 0xffb009ff00
def s166 : List ℕ := [f309,f310,f311,f312,f313]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w89 : Wide 20 5 s166 := viaSearch (by decide +kernel)
def p81 : Weak 94 20 := relaxed (pick [2,3,6,7,8,9,10,11,17,18,19,20,21,22,23,24,25,61,66,77] (by decide) (by decide) (by decide))
def r132 : Rule 94 7 := cutRule 7 p81 w89
def f314 : ℕ := 0x33ea8f0
def f315 : ℕ := 0xfeb460c
def f316 : ℕ := 0xfeb6fcc
def s167 : List ℕ := [f302,f314,f315,f316]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w90 : Wide 14 4 s167 := viaSearch (by decide +kernel)
def p82 : Weak 94 14 := signedPick 6 [6,7,8,9,10,11,19,21,22,23,24,25,66,77] (by decide) (by decide) (by decide)
def r133 : Rule 94 7 := cutRule 7 p82 w90
def f317 : ℕ := 0x58fc
def f318 : ℕ := 0x951f
def f319 : ℕ := 0xcd1c
def s168 : List ℕ := [f317,f318,f319]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w91 : Wide 8 3 s168 := viaSearch (by decide +kernel)
def p83 : Weak 94 8 := relaxed (pick [5,6,26,27,28,33,34,87] (by decide) (by decide) (by decide))
def r134 : Rule 94 6 := cutRule 6 p83 w91
def f320 : ℕ := 0x1242484249021410b002c0c607c0f800fc00f007c01f013
def s169 : List ℕ := [f320,f16,f17,f18,f20,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b90 : Ban 94 7 s169 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1360576572,r134)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p84 : Weak 94 8 := signedPick 6 [6,7,8,9,10,11,24,25] (by decide) (by decide) (by decide)
def r135 : Rule 94 7 := cutRule 7 p84 w68
def p85 : Weak 94 9 := signedPick 6 [6,7,8,9,10,11,38,39,67] (by decide) (by decide) (by decide)
def r136 : Rule 94 7 := cutRule 7 p85 w79
def f321 : ℕ := 0x28a0e3c
def f322 : ℕ := 0x2bb62cc
def f323 : ℕ := 0xfee8c30
def f324 : ℕ := 0xfeeaff0
def s170 : List ℕ := [f321,f322,f323,f324]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w92 : Wide 14 4 s170 := viaSearch (by decide +kernel)
def p86 : Weak 94 14 := signedPick 6 [6,7,8,9,10,11,33,35,36,37,38,39,67,89] (by decide) (by decide) (by decide)
def r137 : Rule 94 7 := cutRule 7 p86 w92
def s171 : List ℕ := [f320,f16,f17,f18,f20,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b91 : Ban 94 7 s171 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(158868814,r14),(1879404427,r134)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p87 : Weak 94 8 := signedPick 6 [6,7,8,9,10,11,37,39] (by decide) (by decide) (by decide)
def r138 : Rule 94 7 := cutRule 7 p87 w68
def s172 : List ℕ := [f320,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b87 : Ban 94 8 s172 := viaRules (ws := [s161,s162,s169,s171]) (consBan b88 (consBan b89 (consBan b90 (consBan b91 (nilBan _ _)))))
  (dictionary [(1972030274,r10),(2035922728,r2),(1433070043,r2),(1422573661,r2),(883613430,r119),(1201624877,r0),(662664646,r2),(2031281362,r2),(43929571,r2),(1652452987,r119),(1693432473,r9),(1804215488,r1),(928821775,r1),(2050693809,r49),(119337838,r2),(1727861254,r119),(1362015203,r2),(313259248,r8),(1921782664,r2),(1200481759,r2),(661521528,r119),(1356433022,r1),(316062363,r1),(647255625,r1),(1570411258,r1),(1891254111,r1),(1693900326,r79),(542064979,r1),(1810614888,r87),(368282380,r2),(1068097075,r1),(1976805796,r119),(2033794861,r126),(795019935,r2),(1430942176,r1),(192167250,r2),(1616030505,r129),(377255579,r2),(1124549009,r119),(1762775195,r2),(1534055192,r130),(295280266,r119),(863655967,r2),(1123891403,r131),(2032600124,r119),(1045512878,r132),(1954221599,r2),(1211490952,r119),(1107720020,r2),(568759789,r119),(1223855733,r2),(684895502,r119),(1751844945,r2),(1212884714,r119),(47717500,r2),(1656240916,r119),(10076742,r119),(1340261065,r2),(396039462,r119),(105082182,r2),(226673036,r121),(1852395698,r119),(1843233192,r2),(2014568161,r119),(1948598557,r133),(1426837572,r2),(1484726615,r119),(1801846308,r2),(1693678859,r135),(1171917874,r119),(1410246822,r2),(1905590067,r1),(666815141,r119),(1562825824,r119),(534391427,r1),(1443100148,r119),(551068927,r119),(370869754,r2),(1979393170,r119),(898223,r2),(1609421639,r119),(661083716,r2),(122123485,r119),(458590177,r2),(2067113593,r119),(1536596672,r136),(627253460,r119),(684183615,r119),(32376769,r137),(1270517204,r2),(2114456966,r119),(1133742795,r2),(1308614980,r119),(945026155,r2),(1533339222,r119),(1933091936,r2),(720137116,r138),(1958277551,r119),(709326519,r2),(690590027,r119),(600805898,r119),(2052577088,r119),(1255617870,r119),(114837702,r119),(1050025331,r119),(1881629402,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f325 : ℕ := 0x1652ca52cb031418b302c5c7ffc0f800fd1cf2e7d81f313
def s173 : List ℕ := [f325,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b93 : Ban 94 7 s173 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(1895393253,r14),(1686364944,r5),(908288839,r109)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f326 : ℕ := 0x4929252924c8a3c50c343a2a003f07ffffe3cf1e3ff8fff
def s174 : List ℕ := [f16,f17,f18,f326,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b94 : Ban 94 7 s174 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(908032086,r18),(1489768931,r95),(1662851634,r13),(918864834,r19),(620379699,r97),(868315444,r19),(81304823,r108),(1690456477,r98),(1622152812,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f327 : ℕ := 0xbfb7b43cccc
def f328 : ℕ := 0xcceae803030
def s175 : List ℕ := [f249,f250,f327,f328,f253]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w93 : Wide 22 5 s175 := viaSearch (by decide +kernel)
def p88 : Weak 94 22 := signedPick 13 [13,14,15,16,17,18,23,24,40,41,42,43,44,45,46,47,48,52,71,73,74,75] (by decide) (by decide) (by decide)
def r139 : Rule 94 7 := cutRule 7 p88 w93
def f329 : ℕ := 0x185a367f3
def f330 : ℕ := 0x192a899dc
def s176 : List ℕ := [f254,f255,f329,f330]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w94 : Wide 17 4 s176 := viaSearch (by decide +kernel)
def p89 : Weak 94 17 := relaxed (pick [0,1,2,3,4,9,12,13,14,15,16,17,18,24,54,60,93] (by decide) (by decide) (by decide))
def r140 : Rule 94 7 := cutRule 7 p89 w94
def f331 : ℕ := 0x1aa97e0c00c
def f332 : ℕ := 0x37fc300ce1c
def s177 : List ℕ := [f331,f72,f332,f73]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w95 : Wide 21 3 s177 := viaSearch (by decide +kernel)
def r141 : Rule 94 6 := cutRule 6 p20 w95
def f333 : ℕ := 0x6d0c
def f334 : ℕ := 0xbaf0
def s178 : List ℕ := [f259,f333,f334]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w96 : Wide 8 2 s178 := viaSearch (by decide +kernel)
def p90 : Weak 94 8 := signedPick 40 [40,41,47,48,50,51,79,80] (by decide) (by decide) (by decide)
def r142 : Rule 94 6 := cutRule 6 p90 w96
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w97 : Wide 8 3 s178 := viaSearch (by decide +kernel)
def r143 : Rule 94 6 := cutRule 6 p90 w97
def f335 : ℕ := 0x36cc
def s179 : List ℕ := [f262,f335,f140]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w98 : Wide 7 3 s179 := viaSearch (by decide +kernel)
def p91 : Weak 94 7 := signedPick 13 [13,14,15,16,17,18,24] (by decide) (by decide) (by decide)
def r144 : Rule 94 6 := cutRule 6 p91 w98
def f336 : ℕ := 0x79ef3def3cfefff7e0201201ffff07c003ffffffe780ce0
def s180 : List ℕ := [f16,f17,f18,f20,f21,f336]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b95 : Ban 94 7 s180 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(714900407,r141),(267117941,r142),(801939030,r142),(34576322,r143),(2103681444,r144),(1284841602,r96),(859283476,r94),(1234292212,r97),(604363778,r107),(1217959271,r108),(908288839,r109),(1690456477,r98),(1885415095,r110),(1495280218,r31),(1363687987,r61),(54553286,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f337 : ℕ := 0x71ce39ce38f6feb7e0000001ffc00000011ff2ffc000000
def s181 : List ℕ := [f16,f17,f18,f20,f337,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b96 : Ban 94 7 s181 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1994042947,r25),(1546260481,r25),(2081081570,r25),(1313718862,r5),(1235340337,r5),(1401318411,r77),(1686364944,r5),(1669374326,r5),(1323570254,r77),(1228024075,r31),(456720173,r5),(1345727836,r77),(1622152812,r5),(109351684,r77),(1519191063,r31),(416500495,r96),(2138426016,r94),(365951105,r5),(1883506318,r5),(1567366057,r77),(136988339,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f338 : ℕ := 0x82104210408014000201200003f07c002e00d002780ce0
def s182 : List ℕ := [f338,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b92 : Ban 94 8 s182 := viaRules (ws := [s173,s174,s180,s181]) (consBan b93 (consBan b94 (consBan b95 (consBan b96 (nilBan _ _)))))
  (dictionary [(1429918545,r10),(957832189,r93),(1815426578,r1),(1343340222,r10),(1746075315,r10),(859360186,r10),(387273830,r93),(834240497,r2),(244023206,r2),(362154141,r2),(1760306348,r12),(1871089363,r0),(995695650,r37),(2117567684,r0),(406509853,r10),(2081907144,r93),(1069447377,r10),(1309009833,r8),(836923477,r10),(1170753545,r10),(698667189,r93),(1423306897,r0),(382936238,r62),(714129500,r0),(1637285133,r37),(1958127986,r0),(1760774201,r0),(608938854,r0),(1877488763,r0),(154251779,r10),(920940349,r0),(1829649070,r93),(591235197,r99),(1499943918,r93),(2043679671,r2),(259041125,r93),(1616030505,r129),(377255579,r2),(1073291949,r2),(282714163,r0),(1191422884,r2),(930529842,r93),(1190765278,r139),(2099473999,r2),(1112386753,r140),(2021095474,r93),(1278364827,r2),(1093343045,r2),(621256689,r2),(2134047019,r10),(1661960663,r93),(755694719,r2),(283608363,r2),(164871879,r10),(1840269170,r93),(76950617,r2),(1407134940,r93),(462913337,r2),(171956057,r93),(293546911,r111),(1919269573,r2),(1910107067,r93),(2081442036,r2),(2015472432,r112),(1493711447,r93),(1551600490,r2),(242997521,r113),(1868720183,r93),(1760552734,r114),(1238791749,r2),(1477120697,r93),(733689016,r2),(1629699699,r2),(1509974023,r2),(617942802,r2),(837110659,r2),(365024303,r2),(998167289,r10),(1435424145,r10),(526080933,r93),(129826182,r2),(567083038,r10),(1805223473,r2),(1515222261,r10),(1043135905,r93),(1603470547,r115),(694127335,r2),(438786098,r10),(751057490,r2),(99250644,r116),(1337391079,r10),(33847194,r2),(1200616670,r10),(1375488855,r2),(1011900030,r10),(1600213097,r2),(761825376,r117),(1999965811,r10),(787010991,r118),(2025151426,r2),(776200394,r10),(1996238828,r23),(757463902,r2),(667679773,r2),(1210742242,r23),(2119450963,r2),(1322491745,r2),(1499587660,r2),(181711577,r2),(1116899206,r2),(1948503277,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r145 : Rule 94 6 := cutRule 6 p85 w79
def f339 : ℕ := 0x610c210c3010008130045c1ffc0ffc0011c33e1dc073f0
def s183 : List ℕ := [f339,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b98 : Ban 94 7 s183 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1485870215,r31),(724699487,r145),(115857557,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p92 : Weak 94 10 := signedPick 5 [5,6,26,27,33,34,68,84,87,90] (by decide) (by decide) (by decide)
def r146 : Rule 94 6 := cutRule 6 p92 w82
def f340 : ℕ := 0x659cb39cb2f548000fc90000003ff80003ff30003fe7000
def s184 : List ℕ := [f16,f17,f18,f20,f340,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b99 : Ban 94 7 s184 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(518098392,r18),(70315926,r18),(605137015,r18),(1985257954,r19),(1906879429,r19),(765633267,r19),(340075141,r19),(781889192,r19),(1778179428,r19),(250479576,r145),(893743320,r146),(1556318052,r19),(1581503667,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f341 : ℕ := 0xa214421450803ea50207fd1ffc007ff00000ff9c000ffc
def s185 : List ℕ := [f341,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b100 : Ban 94 7 s185 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(340075141,r19),(765633267,r19),(1893589006,r18),(1365794917,r13),(1483304704,r13),(1445806540,r14),(1980627629,r14),(631438497,r14),(1213264921,r70),(1134886396,r13),(1625970190,r145),(121750287,r125),(784325019,r13),(809510634,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f342 : ℕ := 0x891333305e00019800
def f343 : ℕ := 0x264c888cb21c3804618
def f344 : ℕ := 0x2ad5bb83a003f8fc1f8
def f345 : ℕ := 0x3366dee9e803c0e00e0
def f346 : ℕ := 0x3366dee9e9ffc0ffee0
def s186 : List ℕ := [f342,f343,f344,f345,f346]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w99 : Wide 37 5 s186 := viaSearch (by decide +kernel)
def p93 : Weak 94 37 := signedPick 5 [5,6,7,12,14,19,20,21,22,26,28,33,35,36,41,46,48,49,50,51,66,67,69,71,72,74,76,77,78,80,82,83,85,87,88,89,91] (by decide) (by decide) (by decide)
def r147 : Rule 94 7 := cutRule 7 p93 w99
def f347 : ℕ := 0x16ab550d370d8001fe00023f
def f348 : ℕ := 0x35badddf01d8003fe1fe03f8
def s187 : List ℕ := [f275,f347,f276,f278,f348]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w100 : Wide 47 5 s187 := viaSearch (by decide +kernel)
def r148 : Rule 94 6 := cutRule 6 p73 w100
def f349 : ℕ := 0x69ad35ad34fc4be240000001ffc0000003ff3ff9c000000
def s188 : List ℕ := [f16,f17,f18,f20,f349,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b101 : Ban 94 7 s188 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(103138034,r18),(1802839215,r18),(190176657,r18),(2062436698,r19),(1980461385,r19),(1570297596,r19),(1491919071,r19),(724699487,r145),(1870285884,r33),(761694776,r148),(1451571398,r19),(620723628,r19),(673079229,r19),(247521103,r19),(622529839,r19),(2140085052,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f350 : ℕ := 0x610c210c30100081fe97fd0003fffff000000003fe7ffc
def s189 : List ℕ := [f350,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b102 : Ban 94 7 s189 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(115857557,r5),(1083243737,r5),(2093256952,r25),(1032681192,r13),(333801113,r13),(1645474486,r14),(32811928,r14),(831106443,r14),(1412932867,r70),(1334554342,r13),(515714500,r19),(90156374,r19),(465165110,r13),(1982720323,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f351 : ℕ := 0x6fbdf7bdf7fd4bea5fe97fd1ffffffff03ff3ff9ffe7ffc
def s190 : List ℕ := [f16,f17,f18,f20,f351,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b97 : Ban 94 8 s190 := viaRules (ws := [s183,s184,s185,s188,s189]) (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (nilBan _ _))))))
  (dictionary [(470899146,r30),(1742989080,r0),(717377467,r30),(23116680,r30),(1130229668,r0),(1461422930,r30),(237094916,r0),(557937769,r30),(360583984,r30),(1356232284,r30),(477298546,r30),(99753701,r2),(643489454,r119),(1006334555,r2),(1124549009,r119),(1073291949,r2),(282714163,r0),(1191422884,r2),(311327918,r2),(429458853,r2),(200738850,r0),(1109447571,r119),(1677823272,r2),(1938058708,r0),(699283782,r119),(1859680183,r0),(620905257,r2),(2025658257,r119),(501263736,r2),(781519597,r2),(1056726671,r119),(511183572,r1),(786390646,r2),(43929571,r2),(319136645,r119),(154251779,r10),(583678000,r8),(858885074,r2),(98809654,r2),(374016728,r119),(1033047919,r0),(1308254993,r2),(2118918207,r2),(246641634,r119),(834240497,r2),(824244047,r119),(6944723,r2),(1210206767,r119),(919249487,r2),(1040840341,r0),(519079356,r119),(509916850,r2),(681251819,r119),(615282215,r0),(93521230,r2),(151410273,r119),(990290951,r0),(468529966,r2),(360362517,r0),(1986085179,r119),(76930480,r2),(1480982446,r119),(229509482,r119),(109783806,r119),(1365236232,r119),(1188947501,r2),(1985915560,r2),(1464154575,r119),(1759121806,r2),(2034328880,r119),(1253340146,r2),(1528547220,r119),(416954468,r2),(1213922527,r2),(692161542,r119),(203280330,r136),(1441420765,r119),(1186079528,r2),(1498350920,r119),(846544074,r147),(2084684509,r2),(781140624,r119),(1947910100,r2),(2122782285,r119),(1759193460,r2),(200022880,r119),(1509118806,r0),(599775594,r2),(1534304421,r0),(624961209,r119),(1523493824,r2),(1414973203,r119),(719260746,r119),(2069785175,r119),(386404916,r2),(1570955202,r2),(661611990,r119),(520370323,r2),(795577397,r119),(1535324410,r2),(1810531484,r119),(229040187,r2),(1413590473,r2),(504247261,r119),(99397443,r119),(929005007,r119),(1864192636,r119),(548313060,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f352 : ℕ := 0x1242484249021410b002c0c607c0ffc0fc00f107c41f0f3
def s191 : List ℕ := [f352,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b104 : Ban 94 7 s191 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def f353 : ℕ := 0x2b3f
def f354 : ℕ := 0x145f3
def f355 : ℕ := 0x16830
def s192 : List ℕ := [f353,f354,f355]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w101 : Wide 9 4 s192 := viaSearch (by decide +kernel)
def p94 : Weak 94 9 := relaxed (pick [0,1,6,7,8,9,10,11,93] (by decide) (by decide) (by decide))
def r149 : Rule 94 7 := cutRule 7 p94 w101
def f356 : ℕ := 0x75debbdebaf7fea80fdfad01f83ff80003fff2e03fff300
def s193 : List ℕ := [f16,f17,f18,f20,f356,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b105 : Ban 94 7 s193 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(701085025,r18),(253302559,r18),(788123648,r18),(20760940,r19),(2089866062,r61),(765633267,r19),(340075141,r19),(182561421,r19),(5107055,r19),(433466209,r108),(1076729953,r109),(1739304685,r19),(1764490300,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f357 : ℕ := 0x30c618c61812fc00005f8000003ff80002e3f00027ff000
def s194 : List ℕ := [f16,f17,f357,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b106 : Ban 94 7 s194 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1263951942,r18),(1340502930,r31),(765633267,r19),(340075141,r19),(816169476,r18),(1350990565,r18),(997343323,r77),(1488527771,r19),(2035026656,r31),(1729894164,r31),(1877572772,r19),(14119268,r31),(583627857,r19),(505249332,r77),(671227406,r77),(996333126,r108),(1639596870,r109),(565267883,r61),(2077635904,r61),(154687955,r19),(179873570,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f358 : ℕ := 0x4518a318a2e502a80f802d01f8000000011c02e01800300
def s195 : List ℕ := [f16,f17,f18,f358,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b103 : Ban 94 8 s195 := viaRules (ws := [s191,s193,s194]) (consBan b104 (consBan b105 (consBan b106 (nilBan _ _))))
  (dictionary [(998342317,r0),(1109125332,r30),(233731619,r0),(1355603653,r30),(661342866,r30),(1768455854,r0),(2099649116,r30),(875321102,r0),(1196163955,r30),(998810170,r30),(1994458470,r30),(1115524732,r30),(2047384648,r10),(813334261,r93),(1362760684,r1),(128710297,r10),(1628398359,r10),(394347972,r93),(1212726707,r10),(311327918,r2),(1663509240,r2),(429458853,r2),(264061593,r10),(1177494853,r93),(365108609,r0),(1278541869,r10),(915161133,r10),(1828594393,r93),(1540640629,r8),(306590242,r10),(737979887,r93),(1281715640,r2),(1644560741,r93),(1762775195,r2),(920940349,r0),(1829649070,r93),(720834101,r149),(1629542822,r2),(838965036,r0),(1747673757,r2),(168565811,r93),(428801247,r0),(1337509968,r2),(350422722,r0),(1259131443,r93),(516400796,r2),(916215810,r10),(1462470233,r2),(645170909,r93),(1848432953,r2),(1557475673,r93),(1679066527,r0),(1157305542,r2),(1148143036,r93),(1319478005,r2),(1253508401,r0),(731747416,r93),(789636459,r2),(1628517137,r0),(1106756152,r93),(998588703,r0),(476827718,r2),(715156666,r93),(615044087,r2),(1528477347,r2),(1371934134,r10),(659644732,r10),(137883747,r93),(1934801051,r2),(1222511649,r10),(700750664,r2),(24520186,r10),(937953446,r93),(2119208632,r2),(867735668,r2),(748009992,r2),(2003462418,r2),(841506516,r115),(2079646951,r2),(1824305714,r10),(2136577106,r2),(1484770260,r116),(575427048,r10),(1419366810,r2),(438652639,r10),(613524824,r2),(249935999,r10),(838249066,r2),(2147344992,r0),(1238001780,r10),(25046960,r0),(1263187395,r2),(14236363,r10),(1868323835,r2),(634273448,r2),(282132947,r10),(1195566207,r93),(1215472716,r2),(2128905976,r2),(1739112601,r10),(505062214,r93),(2142983518,r2),(2053199389,r2),(1357486932,r2),(560527714,r2),(737623629,r2),(1567231193,r2),(354935175,r2),(1186539246,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w102 : Wide 7 3 s48 := viaSearch (by decide +kernel)
def r150 : Rule 94 6 := cutRule 6 p28 w102
def f359 : ℕ := 0x14528a528a031418a3028507f80007c0fd1cc3e61c183e3
def s196 : List ℕ := [f359,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b108 : Ban 94 7 s196 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(772630988,r150),(698895876,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f360 : ℕ := 0x638c718c71d0ea875c5d68fa07c0f83fff03fe1ff87ff1f
def s197 : List ℕ := [f16,f17,f18,f20,f360,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b109 : Ban 94 7 s197 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(53321000,r128),(1584473109,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f361 : ℕ := 0x249a766
def f362 : ℕ := 0x67eb2360
def s198 : List ℕ := [f361,f362,f306,f307]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w103 : Wide 17 4 s198 := viaSearch (by decide +kernel)
def p95 : Weak 94 17 := signedPick 1 [1,6,7,8,9,10,11,16,19,21,22,23,24,25,55,66,77] (by decide) (by decide) (by decide)
def r151 : Rule 94 7 := cutRule 7 p95 w103
def f363 : ℕ := 0x1a2be7f3f
def f364 : ℕ := 0x285453c3f3
def f365 : ℕ := 0x1d40905a0cc
def f366 : ℕ := 0x1d68b8c3c0c
def f367 : ℕ := 0x1ff6009ff00
def s199 : List ℕ := [f363,f364,f365,f366,f367]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w104 : Wide 21 5 s199 := viaSearch (by decide +kernel)
def p96 : Weak 94 21 := relaxed (pick [0,1,6,7,8,9,10,11,29,30,33,34,35,36,37,38,39,56,67,89,93] (by decide) (by decide) (by decide))
def r152 : Rule 94 7 := cutRule 7 p96 w104
def f368 : ℕ := 0x8d1f
def f369 : ℕ := 0xd51c
def s200 : List ℕ := [f317,f368,f369]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w105 : Wide 8 3 s200 := viaSearch (by decide +kernel)
def p97 : Weak 94 8 := relaxed (pick [5,7,12,13,14,19,20,76] (by decide) (by decide) (by decide))
def r153 : Rule 94 6 := cutRule 6 p97 w105
def f370 : ℕ := 0x2284508451104802504940d007c0f83f00033019c06701c
def s201 : List ℕ := [f16,f370,f17,f18,f20,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b110 : Ban 94 7 s201 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(105431565,r14),(47615812,r153)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s202 : List ℕ := [f16,f370,f17,f18,f20,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b111 : Ban 94 7 s202 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(566443667,r153)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s203 : List ℕ := [f16,f370,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b107 : Ban 94 8 s203 := viaRules (ws := [s196,s197,s201,s202]) (consBan b108 (consBan b109 (consBan b110 (consBan b111 (nilBan _ _)))))
  (dictionary [(1422573661,r2),(868511992,r119),(1392969962,r1),(838908293,r2),(145960910,r2),(1739382888,r119),(847249783,r2),(1678331035,r9),(1789114050,r0),(913720337,r38),(2035592371,r0),(916215810,r10),(244023206,r2),(362154141,r2),(1341331584,r0),(300960925,r63),(632154187,r0),(1555309820,r71),(821361509,r2),(267299840,r119),(1620129255,r2),(778649854,r8),(224588185,r2),(388194087,r2),(1981616065,r119),(1876152673,r0),(1678798888,r0),(526963541,r0),(1795513450,r0),(509259884,r100),(1417968605,r2),(1961704358,r119),(177065812,r2),(1534055192,r130),(295280266,r119),(1663509240,r2),(200738850,r0),(1109447571,r119),(720834101,r149),(1629542822,r2),(838965036,r0),(1747673757,r2),(848554529,r2),(1108789965,r151),(2017498686,r119),(1030411440,r152),(1939120161,r2),(1196389514,r119),(2142458951,r119),(1325159627,r2),(380938024,r119),(89980744,r2),(1525106636,r2),(971044967,r119),(1387966621,r2),(833904952,r119),(992430849,r2),(438369180,r119),(549490649,r2),(2142912627,r119),(211571598,r121),(1837294260,r119),(1999466723,r119),(1933497119,r133),(1411736134,r2),(1469625177,r119),(1786744870,r2),(1678577421,r135),(1156816436,r119),(1395145384,r2),(651713703,r119),(1547724386,r119),(1427998710,r119),(535967489,r119),(1521495234,r136),(612152022,r119),(356810785,r2),(669082177,r119),(17275331,r137),(1255415766,r2),(888482247,r2),(334420578,r119),(21956857,r2),(1615378835,r119),(1360614204,r2),(806552535,r119),(2004499237,r2),(1450437568,r119),(2099355528,r119),(1118641357,r2),(1293513542,r119),(929924717,r2),(1518237784,r119),(1917990498,r2),(705035678,r138),(1943176113,r119),(694225081,r2),(1914263515,r0),(675488589,r119),(585704460,r119),(1128766929,r0),(2037475650,r119),(1240516432,r119),(99736264,r119),(1034923893,r119),(1866527964,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f371 : ℕ := 0xc318631862d016803a01701f83f07c000fc01e007800e0
def s204 : List ℕ := [f371,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b113 : Ban 94 7 s204 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(391863015,r25),(1662851634,r13),(961804210,r19),(536246084,r19),(911254820,r13),(281326386,r13),(124244199,r5),(767507943,r5),(1430082675,r13),(1455268290,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f372 : ℕ := 0x91dee
def f373 : ℕ := 0x1f74e2
def f374 : ℕ := 0x3f611f0
def s205 : List ℕ := [f372,f373,f374]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w106 : Wide 13 4 s205 := viaSearch (by decide +kernel)
def p98 : Weak 94 13 := signedPick 1 [1,3,6,7,16,18,19,21,22,55,61,66,77] (by decide) (by decide) (by decide)
def r154 : Rule 94 7 := cutRule 7 p98 w106
def f375 : ℕ := 0x75debbdebaf7fe800fdfa800003ff80003fffe003ffff00
def s206 : List ℕ := [f16,f17,f18,f20,f375,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b114 : Ban 94 7 s206 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(958557659,r25),(510775193,r14),(1045596282,r14),(1843890797,r14),(17998138,r31),(278233574,r13),(199855049,r61),(365833123,r77),(676135261,r19),(418346974,r19),(856057657,r77),(715083877,r13),(85155443,r13),(690938843,r5),(1334202587,r5),(687681393,r31),(1996777319,r13),(2021962934,r13),(2011152337,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f376 : ℕ := 0x34d69ad69a37fc0003df8000003ff80000fff00007ff000
def s207 : List ℕ := [f16,f17,f376,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b115 : Ban 94 7 s207 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(190337588,r25),(1145268664,r19),(1871316021,r19),(1890038769,r14),(277376211,r14),(715083877,r13),(85155443,r13),(1657497150,r13),(1579118625,r77),(2070202419,r5),(565982516,r5),(1228557248,r13),(1253742863,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f377 : ℕ := 0x79ef3def3cfefff7ec002801ffc0000003fffffff800f00
def s208 : List ℕ := [f16,f17,f18,f20,f21,f377]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b116 : Ban 94 7 s208 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(416461429,r25),(2116162610,r14),(1406985213,r14),(503500052,r14),(1623385555,r31),(1883620991,r13),(1805242466,r77),(1971220540,r77),(986402624,r19),(560844498,r19),(96972556,r77),(935853234,r13),(305924800,r13),(22492763,r31),(1430820421,r5),(1850429438,r5),(941154005,r31),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f378 : ℕ := 0x38e71ce71c3efd77e0000001ffc0000000fff1ffc000000
def s209 : List ℕ := [f16,f17,f378,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b117 : Ban 94 7 s209 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1510784805,r25),(981929246,r5),(289569453,r5),(1063002339,r14),(1597823428,r14),(1233911732,r13),(1259097347,r13),(830460720,r13),(752082195,r61),(2080726000,r19),(1655167874,r19),(2030176610,r13),(1400248176,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f379 : ℕ := 0x4108210820c002800c0028000000000003000e003800f00
def s210 : List ℕ := [f16,f17,f379,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b112 : Ban 94 8 s210 := viaRules (ws := [s204,s206,s207,s208,s209]) (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (nilBan _ _))))))
  (dictionary [(99223089,r1),(210006104,r29),(1482096038,r29),(456484425,r1),(613165635,r10),(627479667,r93),(1447525720,r1),(1461839752,r10),(1756956018,r10),(1771270050,r93),(1326133704,r1),(1340447736,r10),(406509853,r10),(420823885,r93),(759678511,r0),(773992543,r10),(264061593,r10),(278375625,r93),(1911650977,r0),(1925965009,r10),(1909707285,r59),(869336626,r8),(1200529888,r59),(2123685521,r8),(297044727,r59),(99690942,r8),(1095339242,r59),(216405504,r8),(1750451183,r2),(1516829470,r2),(1764765215,r2),(1986344306,r93),(382596412,r2),(745441513,r93),(863655967,r2),(930529842,r93),(1677823272,r2),(168565811,r93),(848554529,r2),(345698183,r10),(1598787141,r8),(360012215,r93),(1429229921,r154),(190454995,r2),(1677165666,r8),(438390740,r2),(563351005,r2),(1893535328,r93),(949313725,r2),(658356445,r93),(779947299,r0),(258186314,r2),(249023808,r93),(420358777,r2),(354389173,r0),(1980111835,r93),(1150734605,r2),(1165048637,r2),(1629406768,r10),(17998138,r10),(1643720800,r93),(861186697,r2),(1397261714,r10),(875500729,r2),(305347230,r10),(319661262,r93),(2038000878,r2),(729397909,r8),(207636924,r93),(99469475,r8),(1725192137,r2),(1963521085,r93),(1220089404,r2),(2116100087,r2),(1996374411,r2),(1104343190,r2),(2089870935,r1),(1180527723,r2),(925186486,r10),(1237457878,r2),(585651032,r1),(1823791467,r10),(520247582,r2),(1687017058,r10),(1861889243,r2),(1498300418,r10),(716691631,r2),(731005663,r2),(699728311,r10),(1623385555,r10),(714042343,r93),(1794051687,r2),(570225284,r10),(1808365719,r2),(1805106643,r10),(1819420675,r93),(2086613485,r2),(1248225764,r8),(338882552,r10),(1273411379,r8),(364068167,r2),(1262600782,r10),(1243864290,r2),(1154080161,r2),(458367704,r2),(1808892133,r2),(1985988048,r2),(668111965,r2),(1603299594,r2),(287420018,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f380 : ℕ := 0x41082108201000803000503f80007c0fd1cc3e61c183f3
def s211 : List ℕ := [f380,f16,f17,f18,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b119 : Ban 94 7 s211 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(31265864,r18),(22459074,r14),(1460765324,r14),(1483252953,r25),(2074782033,r105),(182990066,r19),(1093156008,r5),(306145387,r5),(1611983863,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r155 : Rule 94 7 := cutRule 7 p77 w70
def f381 : ℕ := 0x82104210408014000201200003f07ff02e30d1827e0cfc
def s212 : List ℕ := [f381,f16,f17,f18,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b120 : Ban 94 7 s212 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1216566943,r25),(557280163,r14),(1355574678,r14),(1476860785,r18),(1179458940,r19),(1128909550,r19),(2012798838,r143),(414888072,r5),(1647737405,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f382 : ℕ := 0x118b0c
def f383 : ℕ := 0x2c0be0
def f384 : ℕ := 0xc2606e
def f385 : ℕ := 0xee7060
def s213 : List ℕ := [f382,f383,f384,f385]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w107 : Wide 12 3 s213 := viaSearch (by decide +kernel)
def p99 : Weak 94 12 := signedPick 0 [0,4,5,6,8,26,27,29,33,34,54,87] (by decide) (by decide) (by decide)
def r156 : Rule 94 6 := cutRule 6 p99 w107
def f386 : ℕ := 0x2dd07fc
def f387 : ℕ := 0x2df40b0
def f388 : ℕ := 0x3fda74c
def s214 : List ℕ := [f386,f387,f388]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w108 : Wide 13 3 s214 := viaSearch (by decide +kernel)
def p100 : Weak 94 13 := signedPick 27 [27,28,29,30,31,32,37,39,42,43,52,84,86] (by decide) (by decide) (by decide)
def r157 : Rule 94 6 := cutRule 6 p100 w108
def f389 : ℕ := 0x2dda04c
def f390 : ℕ := 0x3ff47b0
def s215 : List ℕ := [f386,f389,f390]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w109 : Wide 13 3 s215 := viaSearch (by decide +kernel)
def p101 : Weak 94 13 := signedPick 13 [13,14,15,16,17,18,24,25,44,45,53,74,75] (by decide) (by decide) (by decide)
def r158 : Rule 94 6 := cutRule 6 p101 w109
def s216 : List ℕ := [f371,f16,f17,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b121 : Ban 94 7 s216 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1327185459,r156),(1662851634,r13),(1584473109,r13),(1897126654,r157),(1059566643,r158)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f391 : ℕ := 0x120b3a
def f392 : ℕ := 0x170030
def f393 : ℕ := 0xfafb0a
def s217 : List ℕ := [f391,f392,f393]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w110 : Wide 12 3 s217 := viaSearch (by decide +kernel)
def p102 : Weak 94 12 := signedPick 1 [1,3,9,11,13,14,15,16,17,18,24,25] (by decide) (by decide) (by decide)
def r159 : Rule 94 6 := cutRule 6 p102 w110
def f394 : ℕ := 0x48ace
def f395 : ℕ := 0x5c00c
def f396 : ℕ := 0xfebac2
def s218 : List ℕ := [f394,f395,f396]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w111 : Wide 12 3 s218 := viaSearch (by decide +kernel)
def p103 : Weak 94 12 := signedPick 1 [1,3,6,7,8,9,10,11,16,18,24,25] (by decide) (by decide) (by decide)
def r160 : Rule 94 6 := cutRule 6 p103 w111
def p104 : Weak 94 12 := signedPick 1 [1,3,9,11,27,28,29,30,31,32,37,39] (by decide) (by decide) (by decide)
def r161 : Rule 94 6 := cutRule 6 p104 w110
def p105 : Weak 94 12 := signedPick 1 [1,3,6,7,8,9,10,11,30,32,37,39] (by decide) (by decide) (by decide)
def r162 : Rule 94 6 := cutRule 6 p105 w111
def s219 : List ℕ := [f371,f16,f17,f18,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b122 : Ban 94 7 s219 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1347606603,r25),(448920798,r18),(1846577264,r159),(1216648830,r160),(217921472,r161),(243107087,r162)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f397 : ℕ := 0x1230ce
def f398 : ℕ := 0x17ad0c2
def f399 : ℕ := 0xe97200c
def s220 : List ℕ := [f397,f398,f399]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w112 : Wide 14 2 s220 := viaSearch (by decide +kernel)
def p106 : Weak 94 14 := signedPick 1 [1,3,6,7,8,9,10,11,16,23,24,55,61,66] (by decide) (by decide) (by decide)
def r163 : Rule 94 6 := cutRule 6 p106 w112
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w113 : Wide 14 3 s220 := viaSearch (by decide +kernel)
def r164 : Rule 94 6 := cutRule 6 p106 w113
def f400 : ℕ := 0x920cc
def f401 : ℕ := 0xba8c0
def f402 : ℕ := 0xd740c
def s221 : List ℕ := [f400,f401,f402]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w114 : Wide 10 3 s221 := viaSearch (by decide +kernel)
def p107 : Weak 94 10 := signedPick 34 [34,35,40,41,47,48,50,51,90,91] (by decide) (by decide) (by decide)
def r165 : Rule 94 6 := cutRule 6 p107 w114
def f403 : ℕ := 0xd3f00c
def s222 : List ℕ := [f384,f403,f385]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w115 : Wide 12 2 s222 := viaSearch (by decide +kernel)
def p108 : Weak 94 12 := signedPick 2 [2,4,5,7,10,12,14,17,19,20,60,76] (by decide) (by decide) (by decide)
def r166 : Rule 94 5 := cutRule 5 p108 w115
def r167 : Rule 94 5 := cutRule 5 p10 w12
def r168 : Rule 94 5 := cutRule 5 p10 w14
def f404 : ℕ := 0x618c318c30d0ea850c5d282a003ff83fffe3fe1e3ffff1f
def s223 : List ℕ := [f16,f17,f36,f404,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b124 : Ban 94 6 s223 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1962888551,r166),(1520037033,r167),(1792152153,r168),(1161833562,r168)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f405 : ℕ := 0x7af0
def f406 : ℕ := 0xdd0c
def s224 : List ℕ := [f317,f405,f406]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w116 : Wide 8 3 s224 := viaSearch (by decide +kernel)
def p109 : Weak 94 8 := signedPick 5 [5,7,12,14,17,19,20,76] (by decide) (by decide) (by decide)
def r169 : Rule 94 6 := cutRule 6 p109 w116
def f407 : ℕ := 0xbe8efc
def f408 : ℕ := 0xbfacb0
def f409 : ℕ := 0xfed24c
def s225 : List ℕ := [f407,f408,f409]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w117 : Wide 12 3 s225 := viaSearch (by decide +kernel)
def p110 : Weak 94 12 := signedPick 5 [5,7,12,14,19,20,41,50,69,74,76,80] (by decide) (by decide) (by decide)
def r170 : Rule 94 6 := cutRule 6 p110 w117
def s226 : List ℕ := [f16,f44,f17,f18,f36,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b123 : Ban 94 7 s226 := viaRules (ws := [s223]) (consBan b124 (nilBan _ _))
  (dictionary [(358622436,r163),(1148925040,r164),(571443061,r163),(150061886,r164),(1995056288,r18),(1119662575,r19),(614624609,r19),(1499547437,r165),(1547273822,r18),(506903163,r19),(838096425,r18),(1761252058,r19),(1498746005,r18),(1352833161,r19),(2107951179,r164),(208403277,r19),(646769538,r169),(894705283,r18),(1674137812,r19),(529707928,r19),(2082094911,r18),(732905779,r18),(2001455688,r18),(1940319580,r163),(579476377,r164),(445941655,r163),(117036542,r163),(1377291701,r163),(1179458940,r19),(1898173870,r18),(373595342,r18),(40074656,r19),(1897126654,r157),(961804210,r19),(1727437472,r20),(818094260,r18),(875024415,r18),(223217569,r20),(709146105,r18),(356687521,r164),(1333810878,r170),(1836670588,r19),(1324583595,r18),(1499455780,r18),(1724180022,r18),(885792301,r19),(910977916,r19),(900167319,r18),(332050647,r19),(494768506,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s227 : List ℕ := [f45,f16,f17,f18,f36,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b125 : Ban 94 7 s227 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1040182735,r19),(1499547437,r165),(1658239189,r18),(597622272,r19),(1378801426,r18),(695077693,r19),(1272573330,r19),(1121715696,r18),(412538299,r18),(1656536785,r18),(1459183000,r18),(307347653,r18),(1575897562,r18),(536246084,r19),(1301879346,r27),(1945143090,r76),(460234175,r19),(485419790,r19),(474609193,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w118 : Wide 12 3 s222 := viaSearch (by decide +kernel)
def r171 : Rule 94 6 := cutRule 6 p108 w118
def r172 : Rule 94 5 := cutRule 5 p0 w0
def r173 : Rule 94 5 := cutRule 5 p1 w0
def s228 : List ℕ := [f16,f17,f36,f46,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b127 : Ban 94 6 s228 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1567322101,r172),(1631455698,r173)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s229 : List ℕ := [f16,f17,f18,f36,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b126 : Ban 94 7 s229 := viaRules (ws := [s228]) (consBan b127 (nilBan _ _))
  (dictionary [(1833723883,r5),(1944506898,r25),(1069113185,r25),(43501572,r5),(1248788687,r5),(1496724432,r14),(456353773,r13),(787547035,r14),(1462766923,r5),(1710702668,r13),(2031545521,r14),(1586255991,r171),(1834191736,r13),(434420644,r5),(682356389,r14),(1950906298,r13),(1093156008,r5),(1889770190,r25),(528926987,r25),(1128909550,r19),(1847624480,r18),(323045952,r18),(1846577264,r159),(911254820,r13),(1808768355,r14),(1273493527,r13),(1969648280,r19),(774669006,r13),(443474758,r13),(695077693,r19),(1647582066,r14),(1064273539,r13),(359704911,r13),(1398745578,r13),(1676888082,r5),(767544870,r13),(512203633,r14),(824475025,r13),(172668179,r5),(1410808614,r14),(1274034205,r14),(1448906390,r13),(1673630632,r14),(1825447601,r19),(835242911,r13),(860428526,r13),(601682184,r5),(444219116,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f410 : ℕ := 0x34d69ad69a375c0003cb8000003ff80000fc30000787000
def s230 : List ℕ := [f16,f17,f410,f18,f36,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b128 : Ban 94 7 s230 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1314578464,r25),(1674137812,r19),(506358226,r19),(866795998,r14),(157618601,r14),(1080774234,r13),(1401617087,r14),(1204263302,r13),(52427955,r14),(1320977864,r13),(989633345,r13),(1064273539,r13),(1216648830,r160),(281326386,r13),(1046959648,r5),(1690223392,r5),(205314477,r13),(230500092,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f411 : ℕ := 0x4503c
def f412 : ℕ := 0x6d830
def s231 : List ℕ := [f411,f412,f402]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w119 : Wide 10 3 s231 := viaSearch (by decide +kernel)
def p111 : Weak 94 10 := signedPick 20 [20,21,40,41,47,48,50,51,79,80] (by decide) (by decide) (by decide)
def r174 : Rule 94 6 := cutRule 6 p111 w119
def f413 : ℕ := 0xe9237ce
def f414 : ℕ := 0xffad7c2
def s232 : List ℕ := [f413,f399,f414]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w120 : Wide 14 2 s232 := viaSearch (by decide +kernel)
def p112 : Weak 94 14 := signedPick 1 [1,3,6,7,8,9,10,11,32,38,39,56,62,67] (by decide) (by decide) (by decide)
def r175 : Rule 94 6 := cutRule 6 p112 w120
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w121 : Wide 14 3 s232 := viaSearch (by decide +kernel)
def r176 : Rule 94 6 := cutRule 6 p112 w121
def r177 : Rule 94 5 := cutRule 5 p99 w115
def r178 : Rule 94 5 := cutRule 5 p13 w12
def r179 : Rule 94 5 := cutRule 5 p13 w14
def f415 : ℕ := 0x514a294a28c2b695ac14282bffc0003fff1ffffff878f1f
def s233 : List ℕ := [f16,f17,f36,f415,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b130 : Ban 94 6 s233 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(530089731,r177),(1352720471,r178),(1154767634,r179),(1931544747,r179)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p113 : Weak 94 8 := signedPick 5 [5,6,26,27,29,33,34,87] (by decide) (by decide) (by decide)
def r180 : Rule 94 6 := cutRule 6 p113 w116
def p114 : Weak 94 12 := signedPick 5 [5,6,26,27,33,34,40,47,68,84,87,90] (by decide) (by decide) (by decide)
def r181 : Rule 94 6 := cutRule 6 p114 w117
def s234 : List ℕ := [f48,f16,f17,f18,f36,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b129 : Ban 94 7 s234 := viaRules (ws := [s233]) (consBan b130 (nilBan _ _))
  (dictionary [(845886468,r5),(1226650678,r174),(1654339973,r175),(283898863,r176),(1155039505,r176),(2137120684,r175),(1157496277,r25),(1403974598,r5),(1987726605,r25),(2025372278,r5),(1555348058,r176),(1803283803,r5),(35629680,r180),(283565425,r25),(855884778,r5),(633796303,r5),(709713811,r25),(536414,r25),(923692047,r25),(1244534900,r25),(1047181115,r5),(2042829415,r25),(1163895677,r5),(1472027322,r175),(974379788,r175),(760133118,r175),(306145387,r5),(1102759569,r25),(1889400013,r25),(14802317,r5),(1060613859,r175),(1683518978,r176),(1059566643,r158),(124244199,r5),(1769858774,r25),(359245267,r176),(357315110,r181),(1068238549,r5),(693541854,r25),(1896803898,r25),(1727437472,r20),(1205676487,r25),(1367848950,r25),(1301879346,r27),(838007404,r25),(1676888082,r5),(1046959648,r5),(763527611,r25),(883871981,r5),(611734957,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s235 : List ℕ := [f49,f16,f17,f18,f36,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b131 : Ban 94 7 s235 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(202622724,r5),(1226650678,r174),(455805829,r25),(49232486,r5),(1766401545,r25),(1154945021,r5),(1576120290,r5),(1352977555,r25),(312606896,r25),(643800158,r25),(1566955791,r25),(1887798644,r25),(538609512,r25),(767507943,r5),(223217569,r20),(1945143090,r76),(172668179,r5),(1690223392,r5),(1406791355,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r182 : Rule 94 6 := cutRule 6 p99 w118
def s236 : List ℕ := [f16,f17,f18,f36,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b132 : Ban 94 7 s236 := viaRules (ws := [s228]) (consBan b127 (nilBan _ _))
  (dictionary [(205068091,r5),(315851106,r25),(1587941040,r25),(562329427,r5),(2015552287,r14),(727245883,r182),(975181628,r13),(1058439145,r19),(1306374890,r14),(82046876,r13),(154953984,r19),(402889729,r14),(205535944,r13),(1201184244,r14),(74314761,r19),(322250506,r13),(1611983863,r5),(261114398,r25),(1047754842,r25),(1647737405,r19),(218968688,r18),(841873807,r18),(217921472,r161),(1430082675,r13),(1999380330,r14),(1055158727,r13),(885792301,r19),(364031316,r13),(354868810,r14),(526203779,r13),(460234175,r19),(2085956837,r14),(2143845880,r14),(65546181,r5),(835242911,r13),(205314477,r13),(1821430342,r5),(1917573433,r13),(405126085,r5),(1488876086,r13),(1792968726,r13),(1154945021,r5),(91211375,r14),(571499619,r14),(235570335,r13),(221977424,r13),(1533646815,r13),(963046971,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f416 : ℕ := 0x38e71ce71c3e5d72e0000001ffc0000000fc31e1c000000
def s237 : List ℕ := [f16,f17,f416,f18,f36,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b133 : Ban 94 7 s237 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(341036721,r25),(855884778,r5),(1764578569,r5),(2040737902,r14),(1000367243,r13),(1331560505,r14),(107232491,r13),(428075344,r14),(1226369859,r14),(347436121,r13),(1508461200,r13),(221977424,r13),(243107087,r162),(1455268290,r13),(910977916,r19),(485419790,r19),(860428526,r13),(230500092,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s238 : List ℕ := [f16,f17,f18,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b118 : Ban 94 8 s238 := viaRules (ws := [s10,s211,s212,s216,s204,s219,s226,s227,s229,s230,s234,s235,s236,s237]) (consBan b3 (consBan b119 (consBan b120 (consBan b121 (consBan b113 (consBan b122 (consBan b123 (consBan b125 (consBan b126 (consBan b128 (consBan b129 (consBan b131 (consBan b132 (consBan b133 (nilBan _ _)))))))))))))))
  (dictionary [(470241540,r1),(1742331474,r1),(716719861,r0),(22459074,r8),(1129572062,r1),(1460765324,r8),(236437310,r1),(557280163,r8),(359926378,r0),(1355574678,r8),(476640940,r0),(415504832,r1),(1202145276,r1),(1475031227,r155),(373359122,r0),(996264241,r0),(662743555,r155),(823586441,r1),(6287117,r8),(1209549161,r1),(918591881,r8),(518421750,r1),(509259244,r8),(680594213,r1),(92863624,r8),(150752667,r8),(467872360,r8),(1985427573,r8),(76272874,r8),(197394815,r1),(196617244,r8),(2071963867,r1),(1043330697,r8),(1440763159,r0),(1185421922,r8),(1497693314,r1),(2084026903,r8),(780483018,r0),(1947252494,r8),(2122124679,r0),(1758535854,r8),(199365274,r8),(599117988,r8),(624303603,r8),(1522836218,r8),(190782654,r0),(954719546,r8),(1117437405,r0),(85638349,r8),(98739837,r8),(928347401,r8),(1863535030,r8),(547655454,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s239 : List ℕ := [f380,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b135 : Ban 94 7 s239 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1895393253,r14),(1177255857,r70),(1710579969,r25),(1800232565,r77),(2055924245,r61),(31595919,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s240 : List ℕ := [f381,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b136 : Ban 94 7 s240 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(282730695,r14),(1303557981,r70),(894076724,r18),(904909472,r19),(1738249370,r61),(140338604,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f417 : ℕ := 0xa480ccea
def f418 : ℕ := 0xaebfcc2a
def f419 : ℕ := 0xf5c000c0
def s241 : List ℕ := [f417,f418,f419]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w122 : Wide 16 3 s241 := viaSearch (by decide +kernel)
def p115 : Weak 94 16 := signedPick 1 [1,3,16,18,30,32,40,41,42,43,44,45,57,58,63,64] (by decide) (by decide) (by decide)
def r183 : Rule 94 6 := cutRule 6 p115 w122
def s242 : List ℕ := [f16,f17,f18,f20,f36,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b137 : Ban 94 7 s242 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1573361453,r5),(2117097206,r25),(332458660,r25),(517546989,r19),(1264840419,r18),(1903066605,r18),(1003947377,r14),(1846577264,r159),(1351782362,r14),(1077232894,r14),(2027742603,r13),(1496015887,r183),(586672675,r19),(45384851,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s243 : List ℕ := [f16,f17,f18,f20,f36,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b138 : Ban 94 7 s243 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2092189308,r5),(488441414,r25),(851286515,r25),(1036374844,r19),(1783668274,r18),(274410813,r18),(1522775232,r14),(217921472,r161),(1870610217,r14),(1596060749,r14),(1496015887,r183),(974254902,r5),(2102219413,r13),(1820764478,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s244 : List ℕ := [f16,f17,f18,f20,f36,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b134 : Ban 94 8 s244 := viaRules (ws := [s216,s219,s239,s240,s242,s243]) (consBan b121 (consBan b122 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (nilBan _ _)))))))
  (dictionary [(1268167246,r9),(1378950261,r1),(503556548,r1),(1625428582,r0),(931167795,r8),(2038280783,r1),(221990398,r8),(1145146031,r1),(1465988884,r8),(1268635099,r0),(116799752,r8),(1385349661,r0),(99096095,r101),(1007804816,r2),(642831848,r1),(1551540569,r119),(1005676949,r1),(1914385670,r2),(1123891403,r131),(2032600124,r119),(1190765278,r139),(2099473999,r2),(1938058708,r0),(699283782,r119),(428801247,r0),(1337509968,r2),(1108789965,r151),(2017498686,r119),(1429229921,r154),(190454995,r2),(1677165666,r8),(438390740,r2),(1281020627,r2),(1528956372,r2),(2025000651,r8),(786225725,r119),(527599371,r2),(140955364,r2),(1324213553,r119),(927595808,r1),(2110853997,r2),(1200481759,r2),(236256301,r119),(563352913,r2),(98809654,r2),(1282067843,r119),(721714773,r0),(1904972962,r2),(388194087,r2),(1571452276,r119),(345698183,r10),(1750451183,r2),(1732295162,r119),(914995838,r2),(2118257882,r119),(1827300602,r2),(1948891456,r121),(1427130471,r119),(1417967965,r2),(1589302934,r119),(1523333330,r133),(1001572345,r2),(1059461388,r119),(1376581081,r2),(1268413632,r135),(746652647,r119),(984981595,r2),(1480324840,r1),(241549914,r119),(228851876,r2),(1137560597,r119),(109126200,r1),(1017834921,r119),(1364578626,r2),(125803700,r119),(2070328994,r2),(1106103536,r119),(2069551423,r2),(1105325965,r119),(1797414399,r2),(833188941,r119),(768781229,r2),(1952039418,r119),(1111331445,r136),(201988233,r119),(2094130643,r2),(258918388,r119),(1754595189,r137),(845251977,r2),(1689191739,r119),(708477568,r2),(883349753,r119),(519760928,r2),(1108073995,r119),(1507826709,r2),(294871889,r138),(1533012324,r119),(284061292,r2),(1504099726,r0),(265324800,r119),(1414315597,r2),(175540671,r119),(718603140,r0),(1627311861,r119),(2069127569,r2),(830352643,r119),(2063716833,r2),(1099491375,r119),(680170078,r2),(1863428267,r119),(842887937,r2),(2026146126,r119),(1958572528,r2),(994347070,r119),(1007448558,r119),(1837056122,r119),(624760104,r119),(1456364175,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r184 : Rule 94 7 := cutRule 7 p57 w68
def f420 : ℕ := 0x1242484249021410b002c0c607c0f800fd00f207d81f313
def s245 : List ℕ := [f371,f420,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b140 : Ban 94 7 s245 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1940030028,r134)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f421 : ℕ := 0x2284508451104802504940d007c0f83f02033c19e067c1c
def s246 : List ℕ := [f371,f16,f421,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b141 : Ban 94 7 s246 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1393081017,r153)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b142 : Ban 94 7 s238 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(470241540,r25),(22459074,r14),(1129572062,r13),(1460765324,r14),(236437310,r13),(557280163,r14),(359926378,r13),(1355574678,r14),(476640940,r13),(1584473109,r13),(1040182735,r19),(614624609,r19),(989633345,r13),(359704911,r13),(76272874,r14),(202622724,r5),(845886468,r5),(1508461200,r13),(1533646815,r13),(1522836218,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w123 : Wide 13 2 s214 := viaSearch (by decide +kernel)
def r185 : Rule 94 6 := cutRule 6 p100 w123
def s247 : List ℕ := [f371,f16,f44,f17,f18,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b143 : Ban 94 7 s247 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1009549652,r185),(808347398,r185),(1070546515,r157),(536246084,r19),(1421168912,r165),(1040182735,r19),(1897126654,r157),(428524638,r19),(759717900,r18),(1420367480,r18),(1274454636,r19),(130024752,r19),(816326758,r18),(1595759287,r19),(451329403,r19),(2003716386,r18),(1649058947,r20),(144839044,r20),(278308996,r157),(1255432353,r170),(807413776,r19),(832599391,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f422 : ℕ := 0x5213f8
def f423 : ℕ := 0x1206cc7
def f424 : ℕ := 0xe8dbf3f
def s248 : List ℕ := [f422,f423,f424]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w124 : Wide 14 3 s248 := viaSearch (by decide +kernel)
def p116 : Weak 94 14 := relaxed (pick [17,18,25,29,30,37,40,41,42,43,44,45,52,53] (by decide) (by decide) (by decide))
def r186 : Rule 94 6 := cutRule 6 p116 w124
def s249 : List ℕ := [f45,f371,f16,f17,f18,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b144 : Ban 94 7 s249 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(961804210,r19),(1421168912,r165),(1579860664,r18),(519243747,r19),(616699168,r19),(614624609,r19),(1578158260,r18),(1223500821,r27),(1866764565,r186),(381855650,r19),(407041265,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s250 : List ℕ := [f371,f16,f17,f18,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b145 : Ban 94 7 s250 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1866128373,r25),(989633345,r13),(1846577264,r159),(1418345907,r14),(709168510,r14),(1632324143,r13),(1953166996,r14),(1755813211,r13),(603977864,r14),(522567587,r13),(1891269755,r19),(616699168,r19),(985895014,r13),(281326386,r13),(1598509557,r5),(94289654,r5),(756864386,r13),(782050001,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s251 : List ℕ := [f371,f16,f17,f410,f18,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b146 : Ban 94 7 s251 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1236199939,r25),(1595759287,r19),(427979701,r19),(359704911,r13),(1216648830,r160),(911254820,r13),(985895014,r13),(968581123,r5),(1611844867,r5),(126935952,r13),(152121567,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w125 : Wide 13 2 s215 := viaSearch (by decide +kernel)
def r187 : Rule 94 6 := cutRule 6 p101 w125
def s252 : List ℕ := [f371,f48,f16,f17,f18,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b147 : Ban 94 7 s252 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(567079915,r187),(387812080,r187),(767507943,r5),(1148272153,r174),(205520338,r158),(202622724,r5),(1059566643,r158),(1909348080,r25),(1946993753,r5),(1724905278,r5),(205186900,r25),(777506253,r5),(555417778,r5),(631335286,r25),(968802590,r5),(1964450890,r25),(280866742,r158),(278936585,r181),(1649058947,r20),(1223500821,r27),(1598509557,r5),(968581123,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s253 : List ℕ := [f49,f371,f16,f17,f18,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b148 : Ban 94 7 s253 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(124244199,r5),(1148272153,r174),(377427304,r25),(2118337608,r5),(1076566496,r5),(845886468,r5),(1274599030,r25),(144839044,r20),(1866764565,r186),(94289654,r5),(1611844867,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s254 : List ℕ := [f371,f16,f17,f18,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b149 : Ban 94 7 s254 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(237472581,r25),(1508461200,r13),(217921472,r161),(1937173762,r14),(896803103,r13),(1227996365,r14),(324511204,r14),(1122805719,r14),(243871981,r13),(807413776,r19),(381855650,r19),(756864386,r13),(126935952,r13),(1412447660,r13),(326747560,r5),(1076566496,r5),(143598899,r13),(1455268290,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s255 : List ℕ := [f371,f16,f17,f416,f18,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b150 : Ban 94 7 s255 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(262658196,r25),(777506253,r5),(1686200044,r5),(1533646815,r13),(243107087,r162),(1430082675,r13),(143598899,r13),(832599391,r19),(407041265,r19),(782050001,r13),(152121567,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b139 : Ban 94 8 s204 := viaRules (ws := [s245,s246,s238,s216,s219,s247,s249,s250,s251,s252,s253,s254,s255]) (consBan b140 (consBan b141 (consBan b142 (consBan b121 (consBan b122 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (nilBan _ _))))))))))))))
  (dictionary [(1478022344,r184),(1269228078,r1),(2038586932,r1),(1366924488,r184),(370542273,r0),(1111332076,r0),(281080000,r15),(391863015,r1),(1663952949,r1),(638341336,r0),(2091564196,r8),(1051193537,r1),(1382386799,r8),(158058785,r1),(478901638,r8),(281547853,r0),(1277196153,r8),(398262415,r0),(1925411380,r1),(475081281,r8),(895229446,r1),(1663493699,r8),(745207916,r1),(2075392239,r8),(1131170636,r1),(840213356,r8),(440043225,r1),(430880719,r8),(602215688,r1),(14485099,r8),(72374142,r8),(389493835,r8),(1907049048,r8),(2145377996,r8),(7287112,r0),(30328635,r8),(766536786,r0),(2055272550,r8),(1362384634,r0),(1107043397,r8),(1419314789,r1),(2005648378,r8),(702104493,r0),(1868873969,r8),(2043746154,r0),(1680157329,r8),(120986749,r8),(520739463,r8),(545925078,r8),(1444457693,r8),(20361312,r8),(849968876,r8),(1785156505,r8),(469276929,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s256 : List ℕ := [f138,f1,f335]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w126 : Wide 7 3 s256 := viaSearch (by decide +kernel)
def p117 : Weak 94 7 := signedPick 27 [27,28,29,30,31,32,34] (by decide) (by decide) (by decide)
def r188 : Rule 94 6 := cutRule 6 p117 w126
def s257 : List ℕ := [f420,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b152 : Ban 94 7 s257 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1895393253,r14),(1924126772,r77),(828741520,r188)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f425 : ℕ := 0x16cc
def s258 : List ℕ := [f138,f425,f263]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w127 : Wide 7 3 s258 := viaSearch (by decide +kernel)
def p118 : Weak 94 7 := signedPick 13 [13,14,15,16,17,18,20] (by decide) (by decide) (by decide)
def r189 : Rule 94 6 := cutRule 6 p118 w127
def s259 : List ℕ := [f16,f421,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b153 : Ban 94 7 s259 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(282730695,r14),(860619078,r77),(632171663,r189)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f426 : ℕ := 0x283c
def s260 : List ℕ := [f426,f110,f234]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w128 : Wide 8 4 s260 := viaSearch (by decide +kernel)
def r190 : Rule 94 7 := cutRule 7 p57 w128
def s261 : List ℕ := [f371,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b151 : Ban 94 8 s261 := viaRules (ws := [s257,s259,s216,s219]) (consBan b152 (consBan b153 (consBan b121 (consBan b122 (nilBan _ _)))))
  (dictionary [(1281851401,r10),(239247418,r93),(1073057135,r1),(30453152,r10),(749168258,r10),(1842415989,r10),(799812006,r93),(1170753545,r10),(128149562,r93),(174371330,r0),(1279250994,r10),(1850457723,r10),(915161133,r10),(2020040797,r93),(1300571736,r1),(425178023,r1),(1547050057,r0),(424076708,r2),(1281020627,r2),(1528956372,r2),(852789270,r8),(1959902258,r1),(143611873,r8),(1066767506,r1),(1387610359,r8),(1190256574,r0),(38421227,r8),(1306971136,r0),(1402616198,r10),(1598787141,r8),(360012215,r93),(20717570,r102),(929426291,r93),(564453323,r1),(1473162044,r2),(927298424,r1),(1836007145,r93),(1045512878,r132),(1954221599,r2),(1112386753,r140),(2021095474,r93),(1859680183,r0),(620905257,r2),(350422722,r0),(1259131443,r93),(1030411440,r152),(1939120161,r2),(1698686381,r190),(459911455,r2),(1946622126,r8),(707847200,r2),(1729240437,r2),(686636454,r2),(278910338,r10),(1383790002,r93),(699058503,r2),(1803938167,r2),(1467322756,r10),(424718773,r93),(1653916637,r2),(836617313,r93),(2039879357,r2),(1748922077,r93),(1870512931,r111),(1348751946,r2),(1339589440,r93),(1510924409,r2),(1444954805,r112),(923193820,r93),(981082863,r2),(1819963541,r113),(1298202556,r93),(1190035107,r114),(668274122,r2),(906603070,r93),(1401946315,r10),(163171389,r2),(150473351,r23),(1059182072,r2),(30747675,r10),(939456396,r2),(1286200101,r23),(47425175,r2),(1958599816,r2),(915995833,r2),(1981641339,r10),(939037356,r93),(570365843,r2),(1675245507,r2),(1859101607,r10),(816497624,r93),(1032952920,r115),(123609708,r2),(2015752118,r10),(180539863,r2),(1676216664,r116),(766873452,r10),(1610813214,r2),(630099043,r10),(804971228,r2),(441382403,r10),(1029695470,r2),(191307749,r117),(1429448184,r10),(216493364,r118),(1454633799,r2),(205682767,r10),(1425721201,r23),(186946275,r2),(1335937072,r10),(97162146,r2),(640224615,r23),(1548933336,r2),(1990749044,r10),(751974118,r2),(929070033,r2),(1758677597,r2),(546381579,r2),(1377985650,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f427 : ℕ := 0x75debbdebaf7fc050fdf802a003ff83ffffff01e3fff01f
def s262 : List ℕ := [f16,f17,f18,f20,f427,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b155 : Ban 94 7 s262 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(460819042,r25),(13036576,r14),(1451342826,r14),(547857665,r14),(1346152180,r14),(1927978604,r70),(1849600079,r13),(1629053003,r19),(1936457987,r19),(715083877,r13),(85155443,r13),(193200226,r5),(836463970,r5),(1499038702,r13),(1524224317,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f428 : ℕ := 0x75debbdebaf75c000fcb8000003ff80003fc30003f87000
def s263 : List ℕ := [f16,f17,f18,f20,f428,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b156 : Ban 94 7 s263 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(804542782,r25),(356760316,r14),(891581405,r14),(124218697,r13),(45840172,r13),(1018184243,r19),(849389381,r19),(715083877,r13),(85155443,r13),(1513178175,r70),(536923966,r5),(1180187710,r5),(1842762442,r13),(1867948057,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f429 : ℕ := 0x79ef3def3cfefff7e014002bffc0003fffffffffc07801f
def s264 : List ℕ := [f16,f17,f18,f20,f21,f429]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b157 : Ban 94 7 s264 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(35260536,r25),(1734961717,r14),(1025784320,r14),(122299159,r14),(920593674,r14),(1502420098,r70),(1424041573,r13),(605201731,r19),(179643605,r19),(554652341,r13),(2072207554,r13),(1311968803,r5),(1138837147,r5),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f430 : ℕ := 0x79ef3def3cfe5ff2e0000001ffc0000003fc3fe1c000000
def s265 : List ℕ := [f16,f17,f18,f20,f21,f430]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b158 : Ban 94 7 s265 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(149395769,r25),(1849096950,r14),(236434392,r14),(1616555331,r13),(1538176806,r13),(719336964,r19),(293778838,r19),(668787574,r13),(38859140,r13),(568745277,r5),(1452991985,r5),(1233911732,r13),(1259097347,r13),(1621630374,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f431 : ℕ := 0xa0050014002a0000003ffc03c01e007801f
def s266 : List ℕ := [f431,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b154 : Ban 94 8 s266 := viaRules (ws := [s238,s262,s263,s264,s265]) (consBan b142 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (nilBan _ _))))))
  (dictionary [(119337838,r2),(481486855,r119),(1169408305,r1),(1531557322,r2),(129596453,r1),(491745470,r2),(1263945292,r2),(1626094309,r119),(821361509,r2),(1183510526,r119),(1652546457,r0),(2014695474,r2),(1209811971,r0),(1571960988,r2),(2118918207,r2),(333583577,r119),(447058074,r1),(557841089,r29),(1829931023,r29),(804319410,r1),(1402616198,r10),(1516829470,r2),(1764765215,r2),(110058623,r59),(1217171611,r8),(1548364873,r59),(324036859,r8),(644879712,r59),(447525927,r8),(1443174227,r59),(564240489,r8),(424076708,r2),(2025000651,r8),(786225725,r119),(186695644,r2),(730431397,r119),(1093276498,r2),(1211490952,r119),(1278364827,r2),(2025658257,r119),(516400796,r2),(1196389514,r119),(1698686381,r190),(459911455,r2),(1946622126,r8),(707847200,r2),(181765784,r2),(543914801,r119),(1131668151,r2),(2015578153,r2),(1493817168,r119),(1475391891,r2),(211818246,r2),(1837540908,r119),(688990659,r2),(1051139676,r119),(911185990,r119),(93886666,r2),(1297148710,r119),(1006191430,r2),(1127782284,r0),(606021299,r119),(596858793,r2),(768193762,r119),(702224158,r0),(180463173,r2),(238352216,r119),(1077232894,r8),(555471909,r2),(447304460,r8),(2073027122,r119),(163872423,r2),(1567924389,r119),(316451425,r119),(196725749,r119),(1452178175,r119),(316829679,r2),(678978696,r119),(318527418,r2),(1590019647,r2),(680676435,r119),(432662651,r2),(1704154880,r2),(794811668,r119),(715647968,r2),(1077796985,r119),(290222273,r1),(1528362708,r119),(1273021471,r2),(1585292863,r119),(933486017,r1),(24142805,r2),(868082567,r119),(2034852043,r2),(62240581,r119),(1846135403,r2),(286964823,r119),(1596060749,r8),(686717537,r2),(1621246364,r8),(711903152,r119),(1610435767,r2),(1591699275,r119),(1501915146,r119),(806202689,r119),(9243471,r119),(186339386,r119),(1015946950,r119),(1951134579,r119),(635255003,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f432 : ℕ := 0x2aa554a555184942506952d007ff07ff02e30d19e3e0cfc
def s267 : List ℕ := [f16,f432,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b160 : Ban 94 7 s267 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(282730695,r14),(340075141,r19),(1217586244,r120)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p119 : Weak 94 9 := signedPick 6 [6,7,8,9,10,11,19,21,25] (by decide) (by decide) (by decide)
def r191 : Rule 94 7 := cutRule 7 p119 w72
def f433 : ℕ := 0x14528a528a031400030280000000f800011cf0001c1f000
def s268 : List ℕ := [f433,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b159 : Ban 94 8 s268 := viaRules (ws := [s267]) (consBan b160 (nilBan _ _))
  (dictionary [(644042413,r10),(407629905,r2),(1952260867,r2),(706741867,r2),(2014960321,r119),(2000761840,r0),(1161496647,r2),(1119120885,r2),(489482131,r2),(1797700585,r119),(1393127511,r1),(1503910526,r29),(628516813,r29),(1750388847,r1),(1604695611,r2),(765430418,r119),(1987878429,r1),(1148613236,r2),(1700536470,r8),(861271277,r2),(1824631217,r2),(985366024,r119),(1056128060,r8),(15757401,r29),(346950663,r8),(1270106296,r29),(1590949149,r8),(1393595364,r1),(241760017,r8),(1510309926,r1),(1757012546,r2),(917747353,r119),(466299893,r2),(1774518347,r119),(285065329,r2),(1593283783,r119),(1107720020,r2),(268454827,r119),(1132765081,r2),(1676500834,r119),(2039345935,r2),(10076742,r119),(76950617,r2),(824244047,r119),(1462470233,r2),(2142458951,r119),(563351005,r2),(823586441,r1),(1732295162,r119),(745207916,r1),(1653916637,r2),(911185990,r119),(934999693,r2),(617495485,r1),(95734500,r119),(1642808788,r2),(1561717088,r1),(1039956103,r2),(2073851721,r1),(1552090736,r119),(1714263199,r119),(1648293595,r191),(1126532610,r2),(1184421653,r119),(2023302331,r1),(1501541346,r2),(1393373897,r1),(871612912,r119),(1109941860,r2),(888271164,r2),(366510179,r119),(1262520862,r119),(1142795186,r119),(772524950,r2),(250763965,r119),(808054569,r2),(2116273023,r119),(1165775231,r2),(326510038,r119),(2104182688,r2),(1264917495,r119),(901417059,r2),(62151866,r119),(1236291710,r1),(326948498,r119),(383878653,r119),(1879555454,r1),(970212242,r2),(1814152004,r119),(833437833,r2),(1008310018,r119),(644721193,r2),(1233034260,r119),(394646539,r1),(1632786974,r2),(419832154,r1),(1657972589,r119),(409021557,r2),(390285065,r119),(300500936,r119),(1752272126,r119),(955312908,r119),(1132408823,r119),(1962016387,r119),(749720369,r119),(1581324440,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f434 : ℕ := 0x108902ccc
def f435 : ℕ := 0x19ebfcf0e
def f436 : ℕ := 0x27401ff02
def f437 : ℕ := 0x37dd02cc0
def s269 : List ℕ := [f434,f435,f436,f437]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w129 : Wide 17 4 s269 := viaSearch (by decide +kernel)
def p120 : Weak 94 17 := signedPick 29 [29,34,40,41,42,43,44,45,47,48,50,51,52,53,90,91,92] (by decide) (by decide) (by decide)
def r192 : Rule 94 7 := cutRule 7 p120 w129
def f438 : ℕ := 0x2284508451104800104940c007ffffc002e33101e7e70f0
def s270 : List ℕ := [f16,f438,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b162 : Ban 94 7 s270 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1021374581,r33),(765633267,r19),(943300514,r94)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f439 : ℕ := 0x2a83fc
def f440 : ℕ := 0x6fa0f0
def f441 : ℕ := 0xbad30c
def s271 : List ℕ := [f439,f440,f441]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w130 : Wide 12 3 s271 := viaSearch (by decide +kernel)
def p121 : Weak 94 12 := signedPick 27 [27,28,29,30,31,32,38,39,42,43,83,84] (by decide) (by decide) (by decide)
def r193 : Rule 94 6 := cutRule 6 p121 w130
def f442 : ℕ := 0x4518a318a2e500080f800501f83f07c003fc03e03f803e0
def s272 : List ℕ := [f16,f17,f18,f442,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b163 : Ban 94 7 s272 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1237595431,r25),(789812965,r14),(1324634054,r14),(2122928569,r14),(1200112504,r31),(1148858592,r31),(1209286887,r13),(1012415320,r77),(782072844,r13),(585201277,r31),(2124914198,r77),(2112701317,r5),(60223110,r5),(1807536626,r193),(1381978500,r94),(1756987236,r13),(1127058802,r13),(1693558856,r77),(1398241076,r77),(969976615,r5),(1613240359,r5),(703897147,r77),(567122738,r77),(128331444,r13),(1366471879,r77),(153517059,r13),(142706462,r77),(69978630,r77),(1836770330,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f443 : ℕ := 0x32c658c65912fc10b05fc0c607c0f800fc03f007c07f013
def s273 : List ℕ := [f16,f17,f443,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b164 : Ban 94 7 s273 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1866758238,r25),(1418975772,r14),(709798375,r14),(1953796861,r14),(270432362,r13),(712539593,r13),(289215786,r19),(2011141307,r150),(238666396,r77),(1756221609,r13),(1599139422,r5),(94919519,r5),(757494251,r13),(782679866,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f444 : ℕ := 0xa3bc
def f445 : ℕ := 0x4b48c
def s274 : List ℕ := [f444,f445,f283]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w131 : Wide 10 3 s274 := viaSearch (by decide +kernel)
def p122 : Weak 94 10 := signedPick 5 [5,7,12,14,19,20,67,72,76,78] (by decide) (by decide) (by decide)
def r194 : Rule 94 6 := cutRule 6 p122 w131
def p123 : Weak 94 7 := signedPick 29 [29,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r195 : Rule 94 6 := cutRule 6 p123 w102
def p124 : Weak 94 6 := signedPick 40 [40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r196 : Rule 94 6 := cutRule 6 p124 w1
def f446 : ℕ := 0x71ce39ce38f6fc10a0000001ffc0000003fff3e7c000000
def s275 : List ℕ := [f16,f17,f18,f20,f446,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b165 : Ban 94 7 s275 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1394612702,r25),(946830236,r14),(1481651325,r14),(714288617,r13),(635910092,r13),(801888166,r77),(2075556903,r5),(571337000,r5),(938896454,r77),(380291267,r31),(1245061632,r13),(1534639050,r77),(1459832775,r13),(99874149,r77),(1964553897,r194),(1538995771,r195),(1914004507,r196),(1284076073,r13),(596361692,r77),(1993787601,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f447 : ℕ := 0x49ccf
def f448 : ℕ := 0x2a27f3
def f449 : ℕ := 0xd14b3c
def s276 : List ℕ := [f447,f448,f449]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w132 : Wide 12 3 s276 := viaSearch (by decide +kernel)
def p125 : Weak 94 12 := relaxed (pick [2,3,27,28,29,30,31,32,42,43,63,84] (by decide) (by decide) (by decide))
def r197 : Rule 94 6 := cutRule 6 p125 w132
def f450 : ℕ := 0x610c210c30100081fdfc5c6003fffc0fc0000003fff3f3
def s277 : List ℕ := [f450,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b166 : Ban 94 7 s277 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(571337000,r5),(2075556903,r5),(765011511,r25),(389850930,r13),(1512334117,r13),(317229045,r14),(1755535295,r14),(852050134,r14),(84687426,r13),(6308901,r13),(1334952706,r197),(909394580,r150),(1284403316,r77),(654474882,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f451 : ℕ := 0x77defbdefbf7fc18bfdfc5c7ffffffc0fffff3e7ffff3f3
def s278 : List ℕ := [f16,f17,f18,f20,f21,f451,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b161 : Ban 94 8 s278 := viaRules (ws := [s270,s272,s273,s275,s277]) (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (nilBan _ _))))))
  (dictionary [(575828187,r1),(686611202,r29),(1958701136,r29),(933089523,r1),(238828736,r59),(1345941724,r8),(1677134986,r59),(452806972,r8),(773649825,r59),(576296040,r8),(1571944340,r59),(693010602,r8),(315465757,r93),(859201510,r2),(1222046611,r93),(1340261065,r2),(1407134940,r93),(6944723,r2),(645170909,r93),(1325159627,r2),(1893535328,r93),(6287117,r8),(914995838,r2),(2075392239,r8),(836617313,r93),(93886666,r2),(1642808788,r2),(1561717088,r1),(1039956103,r2),(2028771508,r2),(1425918823,r2),(1656722528,r1),(1134961543,r93),(1256552397,r39),(734791412,r2),(725628906,r93),(896963875,r2),(830994271,r192),(309233286,r93),(367122329,r2),(1206003007,r8),(684242022,r93),(576074573,r8),(54313588,r2),(292642536,r93),(1696694502,r2),(966982523,r10),(445221538,r2),(847256847,r10),(325495862,r2),(1580948288,r2),(934999693,r2),(453093957,r10),(1323745365,r10),(1814664495,r93),(652073854,r0),(1142992984,r10),(991609413,r10),(1482528543,r93),(1158932192,r8),(1649851322,r10),(59953529,r10),(550872659,r93),(690392080,r8),(1181311210,r10),(727203781,r10),(1218122911,r93),(773641008,r10),(1191430599,r10),(1682349729,r93),(1387659926,r2),(1878579056,r2),(1402803815,r10),(1820593406,r2),(164028889,r2),(1541885741,r10),(2032804871,r93),(644042413,r10),(418992386,r1),(1657132821,r2),(1401791584,r10),(1714062976,r2),(1062256130,r1),(152912918,r10),(996852680,r2),(16138509,r10),(191010694,r2),(1974905516,r10),(415734936,r2),(1724830862,r8),(815487650,r10),(1750016477,r8),(840673265,r2),(1739205880,r10),(1720469388,r2),(1630685259,r2),(934972802,r2),(138013584,r2),(315109499,r2),(1666478048,r10),(1144717063,r2),(2079904692,r2),(1285786101,r10),(764025116,r2),(1677879584,r2),(930658279,r10),(21315067,r2),(1982384228,r10),(325819711,r93),(391016726,r2),(881935856,r2),(1048278393,r10),(301057088,r10),(1539197523,r93)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f452 : ℕ := 0xa21442145080142502052d007c0ffff00003d19c407cfc
def s279 : List ℕ := [f452,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b168 : Ban 94 7 s279 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(340075141,r19),(412804056,r120)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p126 : Weak 94 9 := signedPick 6 [6,7,8,9,10,11,22,23,66] (by decide) (by decide) (by decide)
def r198 : Rule 94 7 := cutRule 7 p126 w84
def f453 : ℕ := 0x5d430
def f454 : ℕ := 0xb78cc
def s280 : List ℕ := [f149,f453,f454]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w133 : Wide 10 3 s280 := viaSearch (by decide +kernel)
def p127 : Weak 94 10 := signedPick 17 [17,18,29,30,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r199 : Rule 94 6 := cutRule 6 p127 w133
def f455 : ℕ := 0x79ef3def3cfefff7ecdd0001ffff000003ffffffe3e0000
def s281 : List ℕ := [f16,f17,f18,f20,f21,f455]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b169 : Ban 94 7 s281 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1994812098,r25),(1547029632,r25),(2081850721,r25),(1314488013,r5),(1236109488,r5),(417269646,r53),(2139195167,r199),(366720256,r5),(1884275469,r70),(2075556903,r5),(571337000,r5),(492825450,r5),(807371215,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p128 : Weak 94 8 := signedPick 27 [27,28,29,30,31,32,42,84] (by decide) (by decide) (by decide)
def r200 : Rule 94 6 := cutRule 6 p128 w34
def f456 : ℕ := 0x2f477c
def f457 : ℕ := 0x2fd670
def f458 : ℕ := 0x3f690c
def s282 : List ℕ := [f456,f457,f458]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w134 : Wide 11 3 s282 := viaSearch (by decide +kernel)
def p129 : Weak 94 11 := signedPick 5 [5,7,12,14,19,20,50,69,74,76,80] (by decide) (by decide) (by decide)
def r201 : Rule 94 6 := cutRule 6 p129 w134
def f459 : ℕ := 0x18630c630c0a17f7e0000001ffc00000011cffffc000000
def s283 : List ℕ := [f16,f459,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b170 : Ban 94 7 s283 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2075556903,r5),(571337000,r5),(1418780643,r25),(970998177,r25),(303055960,r5),(616801319,r70),(197647953,r5),(1505819266,r25),(738456558,r5),(660078033,r5),(251163842,r70),(618599476,r70),(1988721838,r200),(1563163712,r201),(1938172448,r5),(1308244014,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f460 : ℕ := 0x618c318c30f4e8000cdd0000003f000002e3000023e0000
def s284 : List ℕ := [f16,f17,f18,f20,f460,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b167 : Ban 94 8 s284 := viaRules (ws := [s279,s281,s283]) (consBan b168 (consBan b169 (consBan b170 (nilBan _ _))))
  (dictionary [(1779090231,r1),(1889873246,r29),(1014479533,r29),(2136351567,r1),(1442090780,r8),(401720121,r29),(732913383,r8),(1656069016,r29),(1976911869,r8),(1779558084,r1),(627722737,r8),(1896272646,r1),(1518727801,r2),(2062463554,r119),(277825008,r2),(396039462,r119),(462913337,r2),(1210206767,r119),(1848432953,r2),(380938024,r119),(949313725,r2),(1209549161,r1),(2118257882,r119),(1131170636,r1),(2039879357,r2),(1297148710,r119),(2028771508,r2),(1879221296,r10),(1425918823,r2),(919562492,r2),(466260019,r119),(901962518,r0),(448660045,r2),(147329370,r2),(1841510544,r119),(700301417,r2),(1531246528,r2),(1077944055,r119),(1928178673,r1),(1474876200,r2),(1351382955,r2),(898080482,r119),(294707807,r8),(1988888981,r2),(1451443913,r2),(998141440,r119),(1639358840,r2),(1186056367,r119),(1878048532,r2),(1424746059,r119),(203775441,r2),(1897956615,r119),(617495485,r1),(95734500,r119),(1315353610,r198),(793592625,r2),(712500925,r1),(190739940,r2),(312330794,r39),(1938053456,r119),(1928890950,r2),(2100225919,r119),(2034256315,r40),(1512495330,r2),(1570384373,r119),(261781404,r1),(1887504066,r2),(1779336617,r1),(1257575632,r119),(1495904580,r2),(752472899,r119),(22760920,r23),(1648483582,r119),(2050518891,r23),(1528757906,r119),(636726685,r119),(549036973,r2),(1622254430,r1),(712911218,r119),(457569981,r2),(769841373,r119),(118034527,r1),(1356174962,r2),(52631077,r119),(1219400553,r2),(1394272738,r119),(1030683913,r2),(1618996980,r119),(780609259,r1),(2018749694,r2),(805794874,r1),(2043935309,r119),(794984277,r2),(776247785,r119),(686463656,r119),(2138234846,r119),(1341275628,r119),(30467939,r2),(1724649113,r119),(130595333,r2),(586636072,r2),(1824776507,r119),(1702047525,r2),(10604617,r2),(1248745052,r119),(1853512309,r2),(1400209836,r119),(1518371543,r119),(722256445,r2),(200495460,r119),(1135683089,r119),(341564498,r2),(1967287160,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f461 : ℕ := 0xc28c3c
def f462 : ℕ := 0xe80fc0
def f463 : ℕ := 0xeed4cc
def f464 : ℕ := 0xfbab30
def s285 : List ℕ := [f461,f462,f463,f464]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w135 : Wide 12 4 s285 := viaSearch (by decide +kernel)
def p130 : Weak 94 12 := signedPick 40 [40,41,42,43,44,45,47,48,50,51,52,53] (by decide) (by decide) (by decide)
def r202 : Rule 94 7 := cutRule 7 p130 w135
def p131 : Weak 94 8 := relaxed (pick [2,3,13,14,15,16,17,18] (by decide) (by decide) (by decide))
def r203 : Rule 94 7 := cutRule 7 p131 w59
def f465 : ℕ := 0x200400041000018b00045c7ffc007c0fc0003e7c0003f3
def s286 : List ℕ := [f465,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b171 : Ban 94 8 s286 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(549036973,r2),(407629905,r2),(1952260867,r2),(150556572,r10),(1553780466,r93),(1307546846,r1),(563287093,r10),(556838463,r1),(1960062357,r10),(1170950103,r10),(426690350,r93),(1488132951,r1),(1598915966,r29),(723522253,r29),(1845394287,r1),(1990978181,r10),(1246718428,r93),(2010629753,r8),(1266370000,r10),(231477463,r8),(1634701357,r10),(680968252,r10),(2084192146,r93),(1151133500,r59),(110762841,r8),(441956103,r59),(1365111736,r8),(1685954589,r59),(1488600804,r8),(336765457,r59),(1605315366,r8),(1361157577,r10),(616897824,r93),(264574221,r2),(1667798115,r2),(659691819,r10),(2062915713,r93),(47717500,r2),(1450941394,r2),(1227770521,r93),(1771506274,r2),(2134351375,r93),(105082182,r2),(171956057,r93),(919249487,r2),(1557475673,r93),(89980744,r2),(658356445,r93),(918591881,r8),(1827300602,r2),(840213356,r8),(1748922077,r93),(1006191430,r2),(1879221296,r10),(1656722528,r1),(1134961543,r93),(1315353610,r198),(793592625,r2),(712500925,r1),(190739940,r2),(21373514,r1),(1647096176,r2),(1637933670,r93),(1809268639,r2),(1743299035,r202),(1221538050,r93),(1279427093,r2),(2118307771,r8),(1596546786,r93),(1488379337,r8),(966618352,r2),(1204947300,r93),(983276604,r1),(461515619,r2),(1357526302,r2),(1237800626,r2),(867530390,r203),(345769405,r2),(106434344,r2),(1509658238,r2),(2098538071,r10),(1354278318,r93),(952941807,r2),(208682054,r2),(674206351,r10),(2077430245,r93),(1331297150,r1),(421953938,r2),(478884093,r2),(1974560894,r1),(1065217682,r10),(1909157444,r2),(928443273,r10),(1103315458,r2),(739726633,r10),(1328039700,r2),(489651979,r8),(1727792414,r10),(514837594,r8),(1752978029,r2),(504026997,r10),(485290505,r2),(395506376,r2),(1847277566,r2),(1050318348,r2),(1227414263,r2),(2057021827,r2),(844725809,r2),(1676329880,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f466 : ℕ := 0x2bc3f
def f467 : ℕ := 0x5457f3
def f468 : ℕ := 0x1a90bcc
def s287 : List ℕ := [f466,f467,f468]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w136 : Wide 13 3 s287 := viaSearch (by decide +kernel)
def p132 : Weak 94 13 := relaxed (pick [0,1,13,14,15,16,17,18,44,45,58,74,93] (by decide) (by decide) (by decide))
def r204 : Rule 94 6 := cutRule 6 p132 w136
def s288 : List ℕ := [f45,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b173 : Ban 94 7 s288 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(765633267,r19),(1224997969,r94),(1383689721,r18),(323072804,r19),(420528225,r19),(847166228,r18),(1381987317,r18),(614624609,r19),(536246084,r19),(1027329878,r204),(1670593622,r125),(185684707,r19),(210870322,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w137 : Wide 9 2 s132 := viaSearch (by decide +kernel)
def r205 : Rule 94 6 := cutRule 6 p71 w137
def s289 : List ℕ := [f45,f16,f44,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b174 : Ban 94 7 s289 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(765633267,r19),(340075141,r19),(1683561239,r205),(393218511,r120),(1499547437,r165),(1421168912,r165),(1912252706,r204),(408032803,r125),(541502755,r120),(1518626112,r120),(1070607535,r165),(1095793150,r165)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w138 : Wide 10 2 s221 := viaSearch (by decide +kernel)
def r206 : Rule 94 6 := cutRule 6 p107 w138
def f469 : ℕ := 0x2883ce
def f470 : ℕ := 0x6dc0cc
def f471 : ℕ := 0xbab302
def s290 : List ℕ := [f469,f470,f471]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w139 : Wide 12 3 s290 := viaSearch (by decide +kernel)
def p133 : Weak 94 12 := signedPick 14 [14,17,29,30,40,41,42,43,44,45,73,74] (by decide) (by decide) (by decide)
def r207 : Rule 94 6 := cutRule 6 p133 w139
def s291 : List ℕ := [f45,f16,f44,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b175 : Ban 94 7 s291 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(368940514,r17),(1326126567,r19),(1529810084,r18),(1655779330,r19),(194597689,r18),(119426498,r206),(1804063574,r207),(633703284,r170)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f472 : ℕ := 0x24e6
def f473 : ℕ := 0x74e0
def f474 : ℕ := 0xaf06
def s292 : List ℕ := [f472,f473,f474]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w140 : Wide 8 3 s292 := viaSearch (by decide +kernel)
def p134 : Weak 94 8 := signedPick 4 [4,5,7,12,14,19,20,76] (by decide) (by decide) (by decide)
def r208 : Rule 94 6 := cutRule 6 p134 w140
def f475 : ℕ := 0x30a2ffc
def s293 : List ℕ := [f475,f314,f315]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w141 : Wide 14 3 s293 := viaSearch (by decide +kernel)
def r209 : Rule 94 6 := cutRule 6 p82 w141
def f476 : ℕ := 0x50fc
def f477 : ℕ := 0x76e4
def f478 : ℕ := 0xd918
def s294 : List ℕ := [f476,f477,f478]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w142 : Wide 8 3 s294 := viaSearch (by decide +kernel)
def p135 : Weak 94 8 := signedPick 5 [5,7,10,12,14,19,20,76] (by decide) (by decide) (by decide)
def r210 : Rule 94 6 := cutRule 6 p135 w142
def s295 : List ℕ := [f16,f17,f18,f20,f404,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b176 : Ban 94 7 s295 := viaRules (ws := [s223]) (consBan b124 (nilBan _ _))
  (dictionary [(1922374231,r19),(2033157246,r18),(1157763533,r19),(132151920,r18),(1585374780,r18),(297068376,r20),(545004121,r19),(628261638,r208),(876197383,r18),(1799353016,r19),(1872260124,r19),(2120195869,r18),(1922842084,r18),(771006737,r18),(1791620901,r19),(2039556646,r18),(58263907,r17),(421109008,r17),(606197337,r19),(1353490767,r18),(1991716953,r18),(1092597725,r18),(2013606137,r209),(1352833161,r19),(114058235,r19),(1274454636,r19),(1192496965,r210),(1440432710,r18),(1904591022,r17),(1493423310,r17),(10939236,r17),(237978915,r17),(1695098812,r19),(863319354,r19),(420528225,r19),(1736232414,r19),(319873141,r88),(1399588344,r19),(567808886,r19),(859517755,r17),(418772435,r17),(924826881,r20),(1765538430,r20),(856195218,r18),(913125373,r18),(261318527,r20),(1499458962,r19),(1362684553,r18),(1537556738,r18),(1762280980,r18),(923893259,r19),(949078874,r19),(938268277,r18),(134035199,r18),(1484559628,r19),(1135219839,r20),(284779633,r170),(1522920068,r18),(1687378304,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f479 : ℕ := 0x25503fc
def f480 : ℕ := 0x2dda0cc
def f481 : ℕ := 0x3774330
def s296 : List ℕ := [f479,f480,f481]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w143 : Wide 13 2 s296 := viaSearch (by decide +kernel)
def p136 : Weak 94 13 := signedPick 6 [6,7,8,9,10,11,23,24,38,39,66,67,70] (by decide) (by decide) (by decide)
def r211 : Rule 94 6 := cutRule 6 p136 w143
def f482 : ℕ := 0x255681fcffc
def s297 : List ℕ := [f482,f72,f73]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w144 : Wide 21 2 s297 := viaSearch (by decide +kernel)
def r212 : Rule 94 5 := cutRule 5 p20 w144
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w145 : Wide 21 3 s297 := viaSearch (by decide +kernel)
def r213 : Rule 94 5 := cutRule 5 p20 w145
def r214 : Rule 94 5 := cutRule 5 p136 w143
def f483 : ℕ := 0x30c618c618125c10a0490001fffff80003fff3e7e7e7000
def s298 : List ℕ := [f16,f17,f483,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b178 : Ban 94 6 s298 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1407932288,r212),(1789009572,r213),(1068889835,r214),(727608203,r213)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w146 : Wide 13 3 s296 := viaSearch (by decide +kernel)
def r215 : Rule 94 6 := cutRule 6 p136 w146
def s299 : List ℕ := [f48,f16,f44,f17,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b177 : Ban 94 7 s299 := viaRules (ws := [s298]) (consBan b178 (nilBan _ _))
  (dictionary [(2096151748,r197),(329432311,r197),(2065937860,r211),(1456112498,r215),(230970260,r215),(245794784,r215),(545250156,r215),(771327705,r211),(1561630309,r215),(984148330,r211),(757121606,r211),(1534164143,r215),(1239902317,r211),(149494895,r20),(260277910,r17),(1532367844,r17),(506756231,r20),(1027329878,r204),(1912252706,r204),(1090508238,r211),(1128153911,r20),(906065436,r215),(1533830705,r215),(2106150058,r20),(1884061583,r211),(1959979091,r17),(919608432,r17),(1250801694,r17),(1911451274,r211),(1765538430,r20),(621108546,r215),(1307410552,r215),(2086843081,r20),(942413197,r211),(347316533,r17),(149962748,r20),(1145611048,r17),(266677310,r20),(861547917,r211),(435455592,r211),(432868218,r211),(1157928883,r211),(1589692474,r211),(1728095078,r211),(1467202036,r215),(1727437472,r20),(488662546,r211),(1649058947,r20),(1815037021,r211)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w147 : Wide 12 2 s276 := viaSearch (by decide +kernel)
def r216 : Rule 94 6 := cutRule 6 p125 w147
def s300 : List ℕ := [f49,f16,f44,f17,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b179 : Ban 94 7 s300 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1452888004,r215),(329432311,r197),(530483912,r216),(749606704,r197),(719932766,r197),(1414591449,r216),(57410406,r197),(1305040595,r216),(1670593622,r125),(408032803,r125),(1706071109,r216),(1299497766,r20),(869183178,r197),(257726654,r20),(455759188,r17),(1894065438,r17),(261318527,r20),(1264372290,r197),(1950674296,r197),(582623178,r90),(1585676941,r216),(990580277,r17),(1801192627,r216),(223217569,r20),(144839044,r20),(310817118,r197)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r217 : Rule 94 6 := cutRule 6 p20 w145
def f484 : ℕ := 0x24319a
def f485 : ℕ := 0x175d182
def f486 : ℕ := 0xeae2018
def s301 : List ℕ := [f484,f485,f486]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w148 : Wide 14 3 s301 := viaSearch (by decide +kernel)
def p137 : Weak 94 14 := signedPick 1 [1,3,16,27,28,29,30,31,32,42,43,57,63,84] (by decide) (by decide) (by decide)
def r218 : Rule 94 6 := cutRule 6 p137 w148
def f487 : ℕ := 0x2f507fc
def f488 : ℕ := 0x2f74230
def f489 : ℕ := 0x3fda5cc
def s302 : List ℕ := [f487,f488,f489]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w149 : Wide 13 3 s302 := viaSearch (by decide +kernel)
def p138 : Weak 94 13 := signedPick 6 [6,7,8,9,10,11,23,24,37,39,52,66,70] (by decide) (by decide) (by decide)
def r219 : Rule 94 6 := cutRule 6 p138 w149
def f490 : ℕ := 0x79ef3def3cfefff7e0490001fffff80003ffffffe7e7000
def s303 : List ℕ := [f16,f44,f17,f18,f20,f490]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b180 : Ban 94 7 s303 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1335310242,r217),(190880358,r120),(757828263,r120),(1760882026,r205),(1339500851,r120),(161617893,r17),(1804063574,r207),(541502755,r120),(1696342128,r17),(2027535390,r17),(803207376,r17),(540701323,r205),(394788479,r20),(1397842242,r120),(2084144248,r120),(716093130,r120),(1124050229,r17),(1209601914,r205),(1572447015,r120),(1690661469,r205),(931608816,r120),(1934662579,r205),(1637406347,r120),(1757535344,r120),(356687521,r164),(1265396242,r205),(278308996,r157),(1187017717,r120),(444287070,r205),(1500885511,r215),(1470895834,r205),(719932766,r197),(610852868,r120),(1059261410,r120),(1528598920,r205),(822569413,r218),(2089785487,r219),(496947061,r205)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w150 : Wide 12 2 s225 := viaSearch (by decide +kernel)
def r220 : Rule 94 6 := cutRule 6 p110 w150
def f491 : ℕ := 0x596b2d6b2ceeb7f7e0000001ffc00000011ccfffc000000
def s304 : List ℕ := [f16,f44,f17,f18,f20,f491]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b181 : Ban 94 7 s304 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(377701111,r205),(1168003715,r120),(633703284,r170),(1518626112,r120),(525981838,r170),(857175100,r220),(1371911836,r170),(227481952,r120),(913783958,r120),(1693216487,r96),(548786603,r205),(2101173586,r220),(764302289,r205),(1333810878,r170),(1255432353,r170),(1421410427,r205),(545250156,r215),(373976689,r205),(1957135485,r197),(610852868,r120),(82138053,r120),(369396282,r205),(255349316,r170),(2119612854,r170),(218154263,r120)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w151 : Wide 14 2 s301 := viaSearch (by decide +kernel)
def r221 : Rule 94 6 := cutRule 6 p137 w151
def s305 : List ℕ := [f16,f44,f17,f18,f20,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b182 : Ban 94 7 s305 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(719985138,r218),(185684707,r19),(1070607535,r165),(77963261,r19),(409156523,r18),(923893259,r19),(1926947022,r19),(465765381,r18),(1245197910,r19),(100768026,r19),(1653155009,r18),(1572515786,r18),(316283712,r221),(885792301,r19),(807413776,r19),(973391850,r18),(1655391365,r20),(257726654,r20),(822569413,r218),(831853762,r170),(1821764899,r18),(636428448,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w152 : Wide 13 2 s302 := viaSearch (by decide +kernel)
def r222 : Rule 94 6 := cutRule 6 p138 w152
def s306 : List ℕ := [f16,f44,f17,f416,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b183 : Ban 94 7 s306 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(745170753,r219),(210870322,r19),(1095793150,r165),(2106150058,r20),(867360202,r20),(1913734208,r219),(2119612854,r170),(103148876,r19),(434342138,r18),(1094991718,r18),(949078874,r19),(1952132637,r19),(490950996,r18),(1270383525,r19),(125953641,r19),(1678340624,r18),(611242833,r19),(341469327,r222),(910977916,r19),(832599391,r19),(998577465,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s307 : List ℕ := [f16,f44,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b172 : Ban 94 8 s307 := viaRules (ws := [s14,s288,s289,s291,s295,s124,s226,s247,s299,s300,s303,s304,s305,s306]) (consBan b4 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b70 (consBan b123 (consBan b143 (consBan b177 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (nilBan _ _)))))))))))))))
  (dictionary [(84072968,r121),(874375572,r39),(296893593,r121),(2022996065,r39),(1720506820,r0),(845113107,r39),(1966985141,r0),(1272724354,r0),(232353695,r39),(563546957,r0),(1486702590,r39),(1224196537,r0),(2081337456,r39),(620155815,r0),(255158460,r121),(1807545443,r0),(1610191658,r0),(458356311,r0),(1726906220,r0),(1349361375,r111),(1893097128,r121),(108458582,r111),(226673036,r121),(470674146,r121),(1085035844,r121),(1176471677,r121),(902437737,r121),(293546911,r111),(1040840341,r0),(1679066527,r0),(211571598,r121),(779947299,r0),(1948891456,r121),(1870512931,r111),(1127782284,r0),(543544792,r0),(288203555,r111),(600474947,r0),(1186808536,r111),(434596637,r0),(1320278488,r121),(149918198,r0),(1562121120,r121),(2030748298,r0),(1050034127,r0),(1224906312,r0),(861317487,r0),(1449630554,r0),(1849383268,r0),(1874568883,r0),(625617851,r0),(606881359,r0),(517097230,r121),(1968868420,r0),(1171909202,r121)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f492 : ℕ := 0xa003ca
def f493 : ℕ := 0x5b700c8
def f494 : ℕ := 0xae8c302
def s308 : List ℕ := [f492,f493,f494]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w153 : Wide 14 3 s308 := viaSearch (by decide +kernel)
def p139 : Weak 94 14 := signedPick 14 [14,17,27,29,40,41,42,43,44,45,73,74,84,85] (by decide) (by decide) (by decide)
def r223 : Rule 94 6 := cutRule 6 p139 w153
def s309 : List ℕ := [f16,f17,f18,f20,f21,f490]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b185 : Ban 94 7 s309 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1659680505,r25),(1211898039,r25),(1746719128,r25),(47632267,r70),(232720596,r70),(979356420,r5),(900977895,r5),(1809686616,r70),(1717487067,r223),(773265464,r53),(82138053,r120),(1804063574,r207),(31588663,r5),(1549143876,r5),(1044041143,r70),(928294929,r70),(2123554410,r5),(1342601665,r5),(1445238312,r5),(564970739,r5),(1119615960,r33),(1361908386,r61),(1427251333,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s310 : List ℕ := [f16,f17,f18,f20,f491,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b186 : Ban 94 7 s310 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(489320215,r25),(41537749,r25),(576358838,r25),(1956479777,r5),(1878101252,r5),(1167919055,r5),(432320737,r5),(878018215,r5),(262303146,r70),(594798106,r5),(1059261410,r120),(633703284,r170),(1008712020,r5),(378783586,r5),(1469187061,r70),(451997351,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s311 : List ℕ := [f16,f44,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b184 : Ban 94 8 s311 := viaRules (ws := [s289,s291,s309,s310]) (consBan b174 (consBan b175 (consBan b185 (consBan b186 (nilBan _ _)))))
  (dictionary [(706741867,r2),(1709795630,r119),(1497044471,r1),(352614587,r2),(919562492,r2),(1922616255,r119),(498181317,r1),(1501235080,r2),(1087962820,r1),(1198745835,r29),(323352122,r29),(1445224156,r1),(1965797803,r10),(703236984,r2),(821367919,r2),(750963369,r8),(1858076357,r29),(41785972,r8),(964941605,r29),(1846865436,r2),(702435552,r119),(556522708,r1),(1559576471,r2),(1242824714,r8),(98394830,r2),(877827359,r2),(1880881122,r119),(1285784458,r8),(1088430673,r1),(2084078973,r8),(1205145235,r1),(827600390,r2),(1371336143,r119),(1734181244,r2),(1852395698,r119),(1093343045,r2),(2096396808,r119),(1707704743,r2),(563274859,r119),(1799140576,r2),(654710692,r119),(1525106636,r2),(380676752,r119),(1919269573,r2),(519079356,r119),(1157305542,r2),(1837294260,r119),(258186314,r2),(518421750,r1),(1427130471,r119),(440043225,r1),(1348751946,r2),(606021299,r119),(2073851721,r1),(1552090736,r119),(1256552397,r39),(734791412,r2),(312330794,r39),(1938053456,r119),(21373514,r1),(1647096176,r2),(406044745,r2),(1930859493,r0),(1409098508,r119),(1119632604,r2),(1759524524,r0),(1237763539,r2),(1401017947,r0),(879256962,r119),(1718137640,r1),(1196376655,r2),(1088209206,r1),(566448221,r119),(1326538154,r0),(804777169,r2),(583106473,r2),(61345488,r119),(1479117156,r23),(957356171,r119),(1359391480,r23),(837630495,r119),(467360259,r2),(2093082921,r119),(931127019,r1),(21783807,r119),(1913926217,r2),(78713962,r119),(1574390763,r1),(665047551,r2),(1057265536,r2),(2060319299,r119),(1942947387,r2),(1707860715,r2),(798517503,r119),(772587097,r2),(537500425,r2),(1775640860,r119),(37306372,r2),(1040360135,r119),(1508987313,r119),(528273142,r2),(703145327,r119),(339556502,r2),(927869569,r119),(89481848,r1),(1327622283,r2),(114667463,r1),(1352807898,r119),(103856866,r2),(85120374,r119),(2142819892,r119),(1447107435,r119),(650148217,r119),(1349005117,r23),(827244132,r119),(31129034,r2),(1656851696,r119),(966316663,r23),(444555678,r119),(1797920734,r2),(1276159749,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f495 : ℕ := 0xb630
def s312 : List ℕ := [f138,f230,f495]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w154 : Wide 8 3 s312 := viaSearch (by decide +kernel)
def p140 : Weak 94 8 := signedPick 17 [17,18,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r224 : Rule 94 7 := cutRule 7 p140 w154
def f496 : ℕ := 0xaa830f0
def f497 : ℕ := 0xaadfc36
def f498 : ℕ := 0xffb00c0
def f499 : ℕ := 0xffb0cee
def s313 : List ℕ := [f496,f497,f498,f499]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w155 : Wide 14 4 s313 := viaSearch (by decide +kernel)
def p141 : Weak 94 14 := signedPick 5 [5,12,13,22,26,40,46,47,66,68,71,73,82,84] (by decide) (by decide) (by decide)
def r225 : Rule 94 7 := cutRule 7 p141 w155
def f500 : ℕ := 0x7ffffffffffffd425fffd2d007ffffff03fffd19ffffcfc
def s314 : List ℕ := [f16,f17,f18,f20,f21,f22,f500]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b187 : Ban 94 8 s314 := viaRules (ws := [s288]) (consBan b173 (nilBan _ _))
  (dictionary [(1189583329,r1),(314189616,r1),(1436061650,r30),(741800863,r59),(1848913851,r8),(32623466,r59),(955779099,r8),(1276621952,r59),(1079268167,r8),(2074916467,r59),(1195982729,r8),(818437884,r93),(1362173637,r2),(1725018738,r93),(1843233192,r2),(1910107067,r93),(509916850,r2),(1148143036,r93),(249023808,r93),(509259244,r8),(1417967965,r2),(430880719,r8),(1339589440,r93),(596858793,r2),(725628906,r93),(1928890950,r2),(1637933670,r93),(1119632604,r2),(1759524524,r0),(1237763539,r2),(1281805067,r2),(1399936002,r2),(1333966398,r0),(812205413,r93),(870094456,r2),(1708975134,r8),(1187214149,r93),(1079046700,r8),(557285715,r2),(795614663,r93),(948193665,r2),(828467989,r2),(2083920415,r2),(921964513,r115),(12621301,r2),(1904763711,r10),(69551456,r2),(1565228257,r224),(655885045,r10),(519110636,r10),(693982821,r2),(918707063,r2),(80319342,r8),(1318459777,r10),(105504957,r8),(1343645392,r2),(94694360,r10),(75957868,r2),(2133657386,r2),(1437944929,r2),(640985711,r2),(1647689190,r2),(435393172,r2),(717538424,r225),(1711429681,r10),(1323745365,r10),(170152975,r93),(98695782,r1),(1092587039,r10),(1170950103,r10),(17357713,r93),(406044745,r2),(1949803933,r8),(796211543,r10),(1867995985,r10),(714403595,r93),(1098717347,r8),(2092608604,r10),(1061744551,r10),(2055635808,r93),(990480674,r10),(1984371931,r93),(1759121806,r2),(605529416,r2),(902390289,r2),(1896281546,r2),(24520186,r10),(1018411443,r93),(1965797803,r10),(989116773,r2),(1983008030,r2),(1607903061,r10),(454310671,r93),(1664462243,r10),(510869853,r93),(1459314979,r2),(305722589,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f501 : ℕ := 0x6d030
def s315 : List ℕ := [f501,f401,f402]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w156 : Wide 10 4 s315 := viaSearch (by decide +kernel)
def r226 : Rule 94 7 := cutRule 7 p107 w156
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b189 : Ban 94 7 s307 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(874375572,r120),(340075141,r19),(1224997969,r94),(232353695,r19),(563546957,r18),(1224196537,r18),(1078283693,r19),(2081337456,r19),(620155815,r18),(1399588344,r19),(255158460,r19),(1807545443,r18),(470674146,r205),(1040182735,r19),(961804210,r19),(1127782284,r18),(1452888004,r215),(2096151748,r197),(82138053,r120),(1059261410,r120),(611242833,r19),(636428448,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f502 : ℕ := 0x555aab5aaae7b4000f96800000000000011cc0001818000
def s316 : List ℕ := [f16,f17,f18,f20,f502,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b188 : Ban 94 8 s316 := viaRules (ws := [s307]) (consBan b189 (nilBan _ _))
  (dictionary [(1360918298,r29),(485524585,r29),(1607396619,r1),(913135832,r8),(2020248820,r29),(203958435,r8),(1127114068,r29),(1447956921,r8),(1250603136,r1),(98767789,r8),(1367317698,r1),(989772853,r2),(1533508606,r119),(1896353707,r2),(2014568161,r119),(2081442036,r2),(681251819,r119),(1319478005,r2),(1999466723,r119),(420358777,r2),(680594213,r1),(1589302934,r119),(602215688,r1),(1510924409,r2),(768193762,r119),(489482131,r2),(1654708357,r119),(159083210,r1),(1324309436,r2),(147329370,r2),(1312555596,r119),(1353081709,r1),(370824288,r2),(1281805067,r2),(234709776,r10),(1399936002,r2),(127518396,r2),(1292744622,r119),(1222143078,r1),(239885657,r2),(425882792,r2),(1591109018,r119),(1608190428,r8),(625933007,r2),(615044087,r2),(1780270313,r119),(314430222,r2),(1479656448,r119),(1253340146,r2),(271082725,r119),(1003736839,r2),(21479418,r119),(1714263199,r119),(896963875,r2),(2100225919,r119),(1809268639,r2),(1930859493,r0),(1409098508,r119),(1387170432,r226),(865409447,r2),(1505301367,r0),(983540382,r2),(1041429425,r119),(1880310103,r1),(1358549118,r2),(1250381669,r1),(728620684,r119),(966949632,r2),(223517951,r119),(1119528634,r119),(999802958,r119),(107771737,r119),(243872282,r2),(1093299482,r1),(183956270,r119),(2076098680,r2),(240886425,r119),(1736563226,r1),(827220014,r2),(1671159776,r119),(690445605,r2),(865317790,r119),(501728965,r2),(1090042032,r119),(251654311,r1),(1489794746,r2),(276839926,r1),(1514980361,r119),(266029329,r2),(247292837,r119),(157508708,r119),(1609279898,r119),(812320680,r119),(1078116355,r2),(95858934,r119),(223270461,r2),(1388496687,r119),(1676963355,r2),(694705934,r119),(1710826797,r2),(728569376,r119),(989416595,r119),(1819024159,r119),(606728141,r119),(1438332212,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f503 : ℕ := 0x14528a528a031418a3028507f800f800fd1cf2e61c1f303
def s317 : List ℕ := [f45,f503,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b191 : Ban 94 7 s317 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(432633429,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f504 : ℕ := 0x4b29652965c8a3c75c347afa07c007ffff03cf1ff878fff
def s318 : List ℕ := [f16,f17,f18,f504,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b192 : Ban 94 7 s318 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1277946357,r18),(120986494,r18),(1117049235,r19),(1364984980,r18),(1036410012,r19),(1284345757,r18),(231808758,r19),(1399588344,r19),(420528225,r19),(981021525,r19),(597622272,r19),(519243747,r19),(1010327541,r27),(1653591285,r76),(168682370,r19),(193867985,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r227 : Rule 94 7 := cutRule 7 p107 w114
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w157 : Wide 13 2 s287 := viaSearch (by decide +kernel)
def r228 : Rule 94 6 := cutRule 6 p132 w157
def s319 : List ℕ := [f45,f48,f16,f17,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b193 : Ban 94 7 s319 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(766806665,r228),(1038942284,r204),(1049810949,r204),(630637125,r228),(1670593622,r125),(2051357832,r125),(1452888004,r215),(1912252706,r204),(331563480,r228),(1108606017,r204),(2070944458,r228),(1010327541,r27),(1791506695,r204),(1107782962,r27),(702595785,r27),(480507310,r204),(1108272579,r204),(1680591932,r74),(1458503457,r228),(1534420965,r24),(2069242054,r24),(720052922,r24),(435989791,r228),(1301879346,r27),(1223500821,r27),(1389478895,r204)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w158 : Wide 21 3 s36 := viaSearch (by decide +kernel)
def r229 : Rule 94 6 := cutRule 6 p20 w158
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w159 : Wide 10 2 s153 := viaSearch (by decide +kernel)
def r230 : Rule 94 6 := cutRule 6 p75 w159
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w160 : Wide 14 2 s91 := viaSearch (by decide +kernel)
def r231 : Rule 94 6 := cutRule 6 p44 w160
def s320 : List ℕ := [f49,f45,f16,f17,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b194 : Ban 94 7 s320 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1027329878,r204),(2051357832,r125),(2096151748,r197),(408032803,r125),(477983528,r229),(1280512983,r230),(873939640,r76),(1979652175,r76),(566724555,r230),(1653591285,r76),(1751046706,r92),(30201062,r231),(565022151,r231),(1945143090,r76),(1866764565,r186)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s321 : List ℕ := [f45,f16,f17,f18,f20,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b195 : Ban 94 7 s321 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(611242833,r19),(1070607535,r165),(1229299287,r18),(168682370,r19),(266137791,r19),(1799888782,r19),(2131082044,r18),(1227596883,r18),(1146957660,r18),(460234175,r19),(381855650,r19),(547833724,r18),(1229833239,r27),(1979652175,r76),(210870322,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s322 : List ℕ := [f45,f16,f17,f416,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b196 : Ban 94 7 s322 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(636428448,r19),(1095793150,r165),(1680591932,r74),(441802076,r76),(1254484902,r18),(193867985,r19),(291323406,r19),(1252782498,r18),(185684707,r19),(485419790,r19),(407041265,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b190 : Ban 94 8 s288 := viaRules (ws := [s317,s307,s289,s291,s15,s318,s127,s227,s249,s319,s320,s321,s322]) (consBan b191 (consBan b189 (consBan b174 (consBan b175 (consBan b5 (consBan b192 (consBan b71 (consBan b125 (consBan b144 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (nilBan _ _))))))))))))))
  (dictionary [(1249813194,r112),(189090194,r40),(2090866035,r112),(1294948694,r0),(419554981,r40),(1541427015,r0),(1383689721,r0),(900568441,r227),(1104251958,r0),(998023862,r112),(847166228,r0),(1954279216,r40),(137988831,r0),(1061144464,r40),(1381987317,r0),(1184633532,r0),(32798185,r0),(1301348094,r0),(1264128501,r112),(1735545868,r112),(457112991,r112),(1648747271,r112),(923803249,r112),(1467539002,r122),(1830384103,r112),(1948598557,r133),(2015472432,r112),(615282215,r0),(1253508401,r0),(1933497119,r133),(354389173,r0),(1523333330,r133),(1444954805,r112),(702224158,r0),(1797693660,r0),(84803571,r112),(426006772,r0),(174382425,r112),(117986666,r0),(2010129076,r112),(174916821,r0),(761250410,r112),(1605190172,r0),(624476001,r0),(799348186,r0),(435759361,r0),(1024072428,r0),(1423825142,r0),(1449010757,r0),(200059725,r0),(181323233,r0),(91539104,r112),(1543310294,r0),(746351076,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s323 : List ℕ := [f503,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b198 : Ban 94 7 s323 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(1658986830,r150)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r232 : Rule 94 7 := cutRule 7 p124 w1
def s324 : List ℕ := [f45,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b197 : Ban 94 8 s324 := viaRules (ws := [s323,s289,s291]) (consBan b198 (consBan b174 (consBan b175 (nilBan _ _))))
  (dictionary [(150556572,r10),(728052209,r93),(1237317219,r1),(1814812856,r10),(697825143,r10),(991609413,r10),(1569105050,r93),(243872282,r2),(703236984,r2),(821367919,r2),(662404694,r21),(773187709,r1),(2045277643,r1),(1019666030,r0),(284433099,r10),(861928736,r93),(1948795466,r8),(378807456,r10),(4995336,r8),(582490973,r10),(2046250887,r10),(476262877,r93),(325405243,r59),(1432518231,r8),(1763711493,r59),(539383479,r8),(860226332,r59),(662872547,r8),(1658520847,r59),(779587109,r8),(164871879,r10),(742367516,r93),(636289246,r2),(1213784883,r2),(1505340016,r10),(2082835653,r93),(549490649,r2),(1126986286,r2),(402042264,r93),(945778017,r2),(1308623118,r93),(1426837572,r2),(1493711447,r93),(93521230,r2),(731747416,r93),(1411736134,r2),(1980111835,r93),(92863624,r8),(1001572345,r2),(14485099,r8),(923193820,r93),(180463173,r2),(234709776,r10),(1333966398,r0),(812205413,r93),(1648293595,r191),(1126532610,r2),(830994271,r192),(309233286,r93),(2034256315,r40),(1512495330,r2),(1743299035,r202),(1221538050,r93),(1387170432,r226),(865409447,r2),(1505301367,r0),(983540382,r2),(975459821,r0),(453698836,r2),(1292579514,r8),(770818529,r93),(662651080,r8),(140890095,r2),(900980028,r0),(379219043,r93),(157548347,r112),(1783271009,r2),(1053559030,r10),(531798045,r2),(933833354,r10),(412072369,r2),(41802133,r112),(1667524795,r2),(698437038,r2),(1275932675,r2),(1133030596,r10),(1710526233,r93),(1474233797,r2),(2051729434,r2),(1222609450,r10),(1800105087,r93),(505568893,r115),(1743709328,r2),(1488368091,r10),(1800639483,r2),(1148832637,r224),(239489425,r10),(1083429187,r2),(102715016,r10),(277587201,r2),(2061482023,r10),(502311443,r2),(1811407369,r8),(902064157,r10),(1836592984,r8),(927249772,r2),(1825782387,r10),(1807045895,r2),(1717261766,r2),(1021549309,r2),(224590091,r2),(923446991,r232),(401686006,r2),(1753054555,r10),(1231293570,r2),(540758537,r232),(18997552,r2),(1372362608,r10),(850601623,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f505 : ℕ := 0x4d39a739a6eda3e80fb43f01f83f07c003ffcfe03ff8fe0
def s325 : List ℕ := [f16,f17,f18,f505,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b200 : Ban 94 7 s325 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1431836826,r25),(984054360,r14),(1518875449,r14),(169686317,r14),(1329336824,r70),(1662851634,r13),(1584473109,r13),(2001778021,r19),(1576219895,r19),(1112347953,r33),(1951228631,r13),(1321300197,r61),(1037868160,r70),(1164218010,r5),(1807481754,r5),(1160960560,r33),(322572839,r13),(347758454,r13),(336947857,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f506 : ℕ := 0xc318631862d03e803a03f01f83f07c000fc0fe00780fe0
def s326 : List ℕ := [f506,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b201 : Ban 94 7 s326 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1088557784,r25),(1662851634,r13),(1584473109,r13),(640775318,r14),(1175596407,r14),(1658498979,r19),(1232940853,r19),(1607949589,r13),(978021155,r70),(820938968,r5),(1464202712,r5),(2126777444,r13),(4479412,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s327 : List ℕ := [f16,f17,f410,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b202 : Ban 94 7 s327 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1040028996,r25),(1399588344,r19),(231808758,r19),(715083877,r13),(359704911,r13),(281326386,r13),(772410180,r5),(1415673924,r5),(2078248656,r13),(2103434271,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f507 : ℕ := 0xaa23cee
def f508 : ℕ := 0xaaecc22
def f509 : ℕ := 0xffc00f0
def s328 : List ℕ := [f507,f508,f509]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w161 : Wide 14 4 s328 := viaSearch (by decide +kernel)
def p142 : Weak 94 14 := signedPick 1 [1,3,13,14,30,32,40,41,57,58,63,64,73,74] (by decide) (by decide) (by decide)
def r233 : Rule 94 7 := cutRule 7 p142 w161
def f510 : ℕ := 0x79ef3def3cfefff7ec140001ffc0000003fffffff878000
def s329 : List ℕ := [f16,f17,f18,f20,f21,f510]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b203 : Ban 94 7 s329 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(100592548,r25),(1800293729,r14),(187631171,r14),(1307516674,r70),(1567752110,r13),(1489373585,r13),(1655351659,r33),(670533743,r19),(244975617,r19),(1928587322,r33),(619984353,r13),(2137539566,r70),(1854107529,r70),(185620380,r5),(599797392,r5),(1025340384,r33),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f511 : ℕ := 0x38e71ce71c3e5ff7e0000001ffc0000000fc3fffc000000
def s330 : List ℕ := [f16,f17,f511,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b204 : Ban 94 7 s330 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1180835520,r25),(841901562,r5),(1703050747,r5),(733053054,r14),(1267874143,r14),(1233911732,r13),(1259097347,r13),(500511435,r13),(422132910,r13),(1750776715,r19),(1325218589,r19),(1700227325,r13),(1070298891,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f512 : ℕ := 0x4108210820c0a0000c140000000000000303c0003878000
def s331 : List ℕ := [f16,f17,f512,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b199 : Ban 94 8 s331 := viaRules (ws := [s325,s326,s327,s329,s330]) (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (nilBan _ _))))))
  (dictionary [(720293737,r1),(831076752,r29),(2103166686,r29),(1077555073,r1),(1604695611,r2),(92596644,r119),(1597278911,r1),(85179944,r2),(1531246528,r2),(19147561,r119),(511301095,r1),(1146685775,r2),(1846865436,r2),(334766469,r119),(1329458843,r0),(1964843523,r2),(127518396,r2),(762903076,r119),(12556963,r0),(647941643,r2),(383294286,r59),(1490407274,r8),(1821600536,r59),(597272522,r8),(918115375,r59),(720761590,r8),(1716409890,r59),(837476152,r8),(1949207053,r10),(189172341,r2),(437108086,r2),(459931307,r2),(1003667060,r119),(1366512161,r2),(1484726615,r119),(1551600490,r2),(151410273,r119),(789636459,r2),(1469625177,r119),(1150734605,r2),(1786119285,r119),(1385671994,r2),(1112347953,r2),(2021056674,r119),(1042392952,r2),(769068911,r2),(1677777632,r119),(181765784,r2),(817150464,r119),(2038000878,r2),(150752667,r8),(1059461388,r119),(72374142,r8),(981082863,r2),(238352216,r119),(1184421653,r119),(367122329,r2),(1570384373,r119),(1279427093,r2),(1401017947,r0),(879256962,r119),(870094456,r2),(1041429425,r119),(975459821,r0),(453698836,r2),(1710878105,r2),(720540123,r8),(198779138,r119),(1102532812,r233),(580771827,r2),(1350468557,r8),(828707572,r2),(1841160052,r119),(589687088,r119),(469961412,r119),(1725413838,r119),(563457936,r1),(1801598371,r119),(1546257134,r2),(1858528526,r119),(1206721680,r1),(297378468,r2),(1141318230,r119),(160604059,r2),(335476244,r119),(2119371066,r2),(130231756,r2),(765616436,r119),(383859430,r2),(1928587322,r2),(1019244110,r119),(1464102402,r2),(861346647,r2),(2099487082,r119),(380389890,r2),(1015774570,r119),(560200486,r119),(1869296412,r8),(959953200,r2),(1894482027,r8),(985138815,r119),(1883671430,r2),(1864934938,r119),(1775150809,r119),(1079438352,r119),(282479134,r119),(459575049,r119),(1289182613,r119),(76886595,r119),(908490666,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f513 : ℕ := 0x850f
def s332 : List ℕ := [f259,f64,f513]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w162 : Wide 8 3 s332 := viaSearch (by decide +kernel)
def p143 : Weak 94 8 := relaxed (pick [5,7,12,14,19,20,21,76] (by decide) (by decide) (by decide))
def r234 : Rule 94 6 := cutRule 6 p143 w162
def f514 : ℕ := 0x208410841010480000490000003ff83f02e33c1827e7c1c
def s333 : List ℕ := [f16,f514,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b206 : Ban 94 7 s333 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1162095579,r17),(273574768,r20),(502488718,r18),(630836104,r234),(420528225,r19),(87432951,r91),(54706252,r18),(1161819240,r19),(1493012502,r18),(268684488,r19),(589527341,r18),(1078283693,r19),(863319354,r19),(1387821856,r18),(1399588344,r19),(1184624005,r19),(274042621,r19),(390757183,r19),(1037924127,r17),(1841651650,r17),(1223012456,r19),(1970305886,r18),(1969648280,r19),(1891269755,r19),(2057247829,r18),(234869902,r20),(878133646,r20),(739104191,r20),(111490643,r170),(1979499672,r18),(1540708378,r19),(1565893993,r19),(1555083396,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s334 : List ℕ := [f16,f17,f410,f20,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b207 : Ban 94 7 s334 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1744597624,r25),(715083877,r13),(85155443,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p144 : Weak 94 14 := signedPick 1 [1,3,13,14,15,16,17,18,32,44,45,58,64,74] (by decide) (by decide) (by decide)
def r235 : Rule 94 6 := cutRule 6 p144 w121
def r236 : Rule 94 6 := cutRule 6 p144 w120
def s335 : List ℕ := [f48,f16,f17,f18,f20,f46]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b208 : Ban 94 7 s335 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2045602358,r5),(278882921,r174),(1483614753,r235),(1077604521,r5),(855516046,r5),(1483281315,r25),(2055600668,r5),(1833512193,r5),(1909429701,r25),(2123407937,r25),(99413358,r5),(1095061658,r25),(810998527,r236),(1676888082,r5),(1598509557,r5),(1764487631,r25),(82181470,r235),(1605098219,r181),(73989977,r25),(234869902,r20),(1107782962,r27),(772410180,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s336 : List ℕ := [f49,f16,f17,f18,f20,f46]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b209 : Ban 94 7 s336 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1402338614,r5),(278882921,r174),(1655521719,r25),(1248948376,r5),(207177264,r5),(405209798,r25),(619188034,r25),(742677102,r5),(1738325402,r25),(172668179,r5),(94289654,r5),(260267728,r25),(878133646,r20),(1751046706,r92),(1415673924,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s337 : List ℕ := [f16,f17,f18,f20,f46,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b210 : Ban 94 7 s337 := viaRules (ws := [s228]) (consBan b127 (nilBan _ _))
  (dictionary [(1404783981,r5),(1515566996,r25),(640173283,r25),(1762045317,r5),(1067784530,r14),(27413871,r13),(358607133,r14),(1281762766,r13),(1602605619,r14),(1405251834,r13),(253416487,r14),(1521966396,r13),(1144421551,r5),(1688157304,r25),(2051002405,r25),(88607087,r19),(835900517,r18),(1474126703,r18),(575007475,r14),(1496015887,r183),(835242911,r13),(756864386,r13),(674906715,r5),(1379828453,r14),(844553625,r13),(1540708378,r19),(345729104,r13),(266137791,r19),(1218642164,r14),(635333637,r13),(2078248656,r13),(1598802701,r13),(1604841975,r5),(541108329,r13),(207177264,r5),(1290927265,r14),(1771215509,r14),(1435286225,r13),(1421693314,r13),(585879058,r13),(872996721,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s338 : List ℕ := [f16,f17,f416,f18,f20,f46]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b211 : Ban 94 7 s338 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1540752611,r25),(2055600668,r5),(816810812,r5),(1092970145,r14),(1306948381,r13),(1430437449,r13),(278602102,r14),(560693443,r13),(1421693314,r13),(860428526,r13),(782050001,r13),(1565893993,r19),(291323406,r19),(660519252,r13),(2103434271,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s339 : List ℕ := [f16,f17,f18,f20,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b205 : Ban 94 8 s339 := viaRules (ws := [s16,s169,s201,s229,s242,s250,s333,s127,s334,s327,s335,s336,s337,s338]) (consBan b6 (consBan b90 (consBan b110 (consBan b126 (consBan b137 (consBan b145 (consBan b206 (consBan b71 (consBan b207 (consBan b202 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (nilBan _ _)))))))))))))))
  (dictionary [(1669957430,r1),(794563717,r1),(1916435751,r0),(1222174964,r8),(181804305,r1),(512997567,r8),(1436153200,r1),(1756996053,r8),(1559642268,r0),(407806921,r8),(1676356830,r0),(1298811985,r113),(1842547738,r1),(57909192,r1),(242997521,r113),(990290951,r0),(1628517137,r0),(729397909,r8),(1819963541,r113),(1077232894,r8),(2146359117,r1),(1534218887,r8),(998944059,r1),(7749963,r8),(500119538,r1),(1194777696,r8),(168925290,r1),(1373032598,r8),(1037659816,r8),(809159208,r1),(1396333134,r8),(1753193135,r1),(794104467,r8),(492995402,r0),(237654165,r8),(549925557,r1),(1136259146,r8),(1980198908,r0),(999484737,r8),(1174356922,r0),(810768097,r8),(1399081164,r8),(1798833878,r8),(1824019493,r8),(575068461,r8),(556331969,r0),(466547840,r8),(1918319030,r0),(1121359812,r8),(838682871,r8),(2085007474,r8),(991895204,r8),(208488556,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s340 : List ℕ := [f16,f17,f18,f20,f21,f46,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b212 : Ban 94 8 s340 := viaRules (ws := [s334]) (consBan b207 (nilBan _ _))
  (dictionary [(1037413430,r1),(1148196445,r29),(272802732,r29),(1394674766,r1),(700413979,r59),(1807526967,r8),(2138720229,r59),(914392215,r8),(1235235068,r59),(1037881283,r8),(2033529583,r59),(1154595845,r8),(777051000,r93),(1320786753,r2),(1683631854,r93),(1801846308,r2),(1868720183,r93),(468529966,r2),(1106756152,r93),(1786744870,r2),(207636924,r93),(467872360,r8),(1376581081,r2),(389493835,r8),(1298202556,r93),(555471909,r2),(2023302331,r1),(1501541346,r2),(1206003007,r8),(684242022,r93),(261781404,r1),(1887504066,r2),(2118307771,r8),(1596546786,r93),(1718137640,r1),(1196376655,r2),(1708975134,r8),(1187214149,r93),(1880310103,r1),(1358549118,r2),(1292579514,r8),(770818529,r93),(1102532812,r233),(580771827,r2),(1350468557,r8),(828707572,r2),(267963086,r2),(1037659816,r8),(515898831,r2),(1275988764,r8),(754227779,r93),(532557083,r1),(10796098,r2),(1428567766,r10),(906806781,r2),(1308842090,r10),(787081105,r2),(416810869,r8),(2042533531,r2),(672093759,r1),(1624598132,r10),(59953529,r10),(1012457902,r93),(1672162348,r1),(477183074,r10),(680968252,r10),(1633472625,r93),(1173337827,r1),(2125842200,r10),(1867995985,r10),(673016711,r93),(842143579,r1),(1794647952,r10),(2046250887,r10),(851271613,r93),(1710878105,r2),(1482377497,r10),(287398223,r93),(2069551423,r2),(874572149,r2),(278927777,r2),(1231432150,r2),(1467322756,r10),(272343482,r93),(1949207053,r10),(880577629,r1),(2118718064,r2),(1863376827,r10),(28164572,r2),(1523841373,r1),(614498161,r10),(1458437923,r2),(477723752,r10),(652595937,r2),(289007112,r10),(877320179,r2),(38932458,r8),(1277072893,r10),(64118073,r8),(1302258508,r2),(53307476,r10),(34570984,r2),(2092270502,r2),(1396558045,r2),(599598827,r2),(1298455727,r232),(776694742,r2),(2128063291,r10),(1606302306,r2),(915767273,r232),(394006288,r2),(1747371344,r10),(1225610359,r2),(1511901160,r2),(316921886,r2),(610742116,r10),(1563246489,r93),(1665113493,r2),(470134219,r2),(881706845,r10),(1834211218,r93)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f515 : ℕ := 0xa21442145080142502052d007c007ff02030d19e060cfc
def s341 : List ℕ := [f515,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b214 : Ban 94 7 s341 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1399588344,r19),(1750686663,r88),(1273720934,r18),(323072804,r19),(2072015449,r18),(420528225,r19),(738899845,r18),(29722448,r18),(958236214,r19),(1074950776,r19),(506358226,r19),(427979701,r19),(593957775,r18),(919063495,r27),(1562327239,r76),(77418324,r19),(102603939,r19),(91793342,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b215 : Ban 94 7 s339 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1669957430,r25),(1222174964,r14),(1756996053,r14),(1559642268,r13),(407806921,r14),(989633345,r13),(911254820,r13),(1077232894,r14),(1695098812,r19),(420528225,r19),(85155443,r13),(1402338614,r5),(2045602358,r5),(560693443,r13),(585879058,r13),(575068461,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p145 : Weak 94 13 := signedPick 6 [6,7,8,9,10,11,24,25,38,39,53,67,70] (by decide) (by decide) (by decide)
def r237 : Rule 94 6 := cutRule 6 p145 w109
def r238 : Rule 94 6 := cutRule 6 p145 w125
def s342 : List ℕ := [f48,f16,f17,f410,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b216 : Ban 94 7 s342 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1415673924,r5),(1796438134,r174),(853686319,r237),(1443215721,r237),(1326202168,r181),(2086843081,r20),(919063495,r27),(410030414,r25),(447676087,r5),(225587612,r5),(853352881,r25),(1425672234,r5),(1203583759,r5),(1279501267,r25),(1616968571,r5),(465133224,r25),(1402338614,r5),(181070093,r238),(1046959648,r5),(968581123,r5),(1134559197,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s343 : List ℕ := [f49,f16,f17,f410,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b217 : Ban 94 7 s343 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(772410180,r5),(1796438134,r174),(582623178,r90),(1562327239,r76),(1025593285,r25),(619019942,r5),(1724732477,r5),(1922765011,r25),(2045602358,r5),(1690223392,r5),(1611844867,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s344 : List ℕ := [f16,f17,f410,f18,f20,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b218 : Ban 94 7 s344 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(885638562,r25),(1245197910,r19),(77418324,r19),(1544969084,r13),(1876162346,r14),(972677185,r14),(892037962,r13),(560693443,r13),(635333637,r13),(205314477,r13),(126935952,r13),(974913541,r5),(1724732477,r5),(791764880,r13),(2103434271,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s345 : List ℕ := [f16,f17,f410,f416,f18,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b219 : Ban 94 7 s345 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(910824177,r25),(1270383525,r19),(102603939,r19),(1425672234,r5),(186882378,r5),(585879058,r13),(660519252,r13),(2078248656,r13),(791764880,r13),(230500092,r13),(152121567,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b213 : Ban 94 8 s327 := viaRules (ws := [s124,s341,s339,s334,s230,s251,s342,s343,s344,s345]) (consBan b70 (consBan b214 (consBan b215 (consBan b207 (consBan b128 (consBan b146 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (nilBan _ _)))))))))))
  (dictionary [(929245981,r22),(1040028996,r1),(164635283,r1),(1286507317,r0),(521484494,r1),(1140893339,r8),(48236232,r1),(1366509131,r8),(1722164283,r1),(1474083674,r8),(1270219716,r1),(554384697,r8),(592246530,r8),(1699359518,r1),(2030552780,r8),(806224766,r1),(1127067619,r8),(929713834,r0),(1925362134,r8),(1046428396,r0),(1037659816,r8),(668883551,r114),(1212619304,r1),(1575464405,r1),(1693678859,r135),(1760552734,r114),(360362517,r0),(998588703,r0),(1678577421,r135),(426093714,r1),(1854648360,r8),(904319691,r8),(494267676,r1),(99469475,r8),(1268413632,r135),(1190035107,r114),(447304460,r8),(2010550615,r0),(1755209378,r8),(2067480770,r1),(506330712,r8),(1350270474,r0),(369556303,r8),(544428488,r0),(180839663,r8),(1607389602,r8),(810324334,r8),(145895954,r8),(1289167733,r8),(769152730,r8),(1168905444,r8),(1194091059,r8),(2092623674,r8),(2073887182,r0),(1984103053,r8),(1288390596,r0),(491431378,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f516 : ℕ := 0x6d430
def f517 : ℕ := 0xd700c
def s346 : List ℕ := [f516,f401,f517]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w163 : Wide 10 4 s346 := viaSearch (by decide +kernel)
def p146 : Weak 94 10 := signedPick 27 [27,28,40,41,42,43,44,45,84,85] (by decide) (by decide) (by decide)
def r239 : Rule 94 7 := cutRule 7 p146 w163
def s347 : List ℕ := [f16,f17,f410,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b220 : Ban 94 8 s347 := viaRules (ws := [s334]) (consBan b207 (nilBan _ _))
  (dictionary [(407484996,r1),(518268011,r29),(1790357945,r29),(764746332,r1),(1824631217,r2),(2147207156,r119),(296556415,r8),(619132354,r2),(1351382955,r2),(1673958894,r119),(522172207,r8),(844748146,r2),(877827359,r2),(1200403298,r119),(629746750,r8),(952322689,r2),(425882792,r2),(748458731,r119),(1857531420,r8),(32623712,r2),(70485545,r59),(1177598533,r8),(1508791795,r59),(284463781,r8),(605306634,r59),(407952849,r8),(1403601149,r59),(524667411,r8),(193322892,r10),(267963086,r2),(515898831,r2),(147122566,r2),(690858319,r119),(1053703420,r2),(1171917874,r119),(1238791749,r2),(1986085179,r119),(476827718,r2),(1156816436,r119),(1729240437,r2),(2051816376,r119),(1010311436,r2),(1332887375,r119),(59982767,r2),(382558706,r119),(1797414399,r2),(2119990338,r119),(1725192137,r2),(1985427573,r8),(746652647,r119),(1907049048,r8),(668274122,r2),(2073027122,r119),(1393373897,r1),(871612912,r119),(576074573,r8),(54313588,r2),(1779336617,r1),(1257575632,r119),(1488379337,r8),(966618352,r2),(1088209206,r1),(566448221,r119),(1079046700,r8),(557285715,r2),(1250381669,r1),(728620684,r119),(662651080,r8),(140890095,r2),(2023686846,r2),(720540123,r8),(198779138,r119),(1037659816,r8),(398124585,r239),(2023847247,r2),(646060330,r8),(124299345,r2),(2050112296,r2),(1528351311,r119),(798639332,r23),(276878347,r119),(678913656,r23),(157152671,r119),(1934366082,r2),(1412605097,r119),(250649195,r1),(1488789630,r119),(1233448393,r2),(1545719785,r119),(893912939,r1),(2132053374,r2),(828509489,r119),(1995278965,r2),(22667503,r119),(1806562325,r2),(763052678,r2),(1085628617,r119),(2113471057,r2),(288563349,r119),(1449042677,r2),(1771618616,r119),(444830809,r2),(767406748,r119),(247391745,r119),(1556487671,r8),(647144459,r2),(1581673286,r8),(672330074,r119),(1570862689,r2),(1552126197,r119),(1462342068,r119),(766629611,r119),(2117154040,r119),(668527293,r23),(146766308,r119),(1498134857,r2),(976373872,r119),(285838839,r23),(1911561501,r119),(1117442910,r2),(595681925,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w164 : Wide 6 3 s26 := viaSearch (by decide +kernel)
def r240 : Rule 94 6 := cutRule 6 p16 w164
def f518 : ℕ := 0x4d39a739a6ed03ed0fa03f2bf83f07fffffc0ffe3f80fff
def s348 : List ℕ := [f16,f17,f18,f518,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b222 : Ban 94 7 s348 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(373860830,r25),(2073562011,r14),(1364384614,r14),(460899453,r14),(1259193968,r14),(1662851634,r13),(1584473109,r13),(943802025,r19),(518243899,r240),(893252635,r77),(263324201,r13),(106242014,r5),(749505758,r5),(1412080490,r13),(1437266105,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f519 : ℕ := 0x4d39a739a6ed01680fa01701f83f07c003fc01e03f800e0
def s349 : List ℕ := [f16,f17,f18,f519,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b223 : Ban 94 7 s349 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1248895536,r25),(801113070,r14),(1335934159,r14),(1662851634,r13),(1584473109,r13),(1957530929,r77),(1818836731,r19),(1393278605,r19),(1768287341,r13),(1138358907,r13),(981276720,r5),(1624540464,r5),(139631549,r13),(164817164,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f520 : ℕ := 0x79ef3def3cfefff7e000282bffc0003fffffffffc000f1f
def s350 : List ℕ := [f16,f17,f18,f20,f21,f520]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b224 : Ban 94 7 s350 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1757703743,r25),(1309921277,r14),(600743880,r14),(1844742366,r14),(495553234,r14),(1077379658,r13),(999001133,r13),(180161291,r19),(1902086812,r240),(129611901,r77),(1647167114,r13),(389764231,r5),(257350514,r5),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f521 : ℕ := 0x79ef3def3cfefd72e0000001ffc0000003fff1e1c000000
def s351 : List ℕ := [f16,f17,f18,f20,f21,f521]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b225 : Ban 94 7 s351 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2130532339,r25),(1682749873,r14),(70087315,r14),(1450208254,r13),(1371829729,r13),(552989887,r19),(127431761,r196),(502440497,r196),(2019995710,r13),(437996717,r5),(39486203,r5),(1233911732,r13),(1259097347,r13),(1784977309,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f522 : ℕ := 0x2850000282a0000003ffc000e1e0000f1f
def s352 : List ℕ := [f522,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b221 : Ban 94 8 s352 := viaRules (ws := [s348,s349,s339,s350,s351]) (consBan b222 (consBan b223 (consBan b215 (consBan b224 (consBan b225 (nilBan _ _))))))
  (dictionary [(1990978181,r10),(404399421,r93),(806497313,r1),(1367402200,r10),(2036855575,r1),(450276815,r10),(727203781,r10),(1288108668,r93),(284433099,r10),(845337986,r93),(312115856,r0),(873020743,r10),(495712719,r0),(1056617606,r10),(1061744551,r10),(1622649438,r93),(645813944,r1),(756596959,r29),(2028686893,r29),(1003075280,r1),(2023686846,r2),(189172341,r2),(437108086,r2),(308814493,r59),(1415927481,r8),(1747120743,r59),(522792729,r8),(843635582,r59),(646281797,r8),(1641930097,r59),(762996359,r8),(305347230,r10),(866252117,r93),(327695998,r2),(2127375811,r10),(888600885,r2),(1202730704,r10),(854926870,r10),(1763635591,r93),(688990659,r2),(1249895546,r2),(385451514,r93),(929187267,r2),(1292032368,r93),(1410246822,r2),(1477120697,r93),(76930480,r2),(715156666,r93),(1395145384,r2),(1963521085,r93),(76272874,r8),(984981595,r2),(2145377996,r8),(906603070,r93),(163872423,r2),(193322892,r10),(1275988764,r8),(754227779,r93),(1109941860,r2),(292642536,r93),(1495904580,r2),(1204947300,r93),(1326538154,r0),(804777169,r2),(795614663,r93),(966949632,r2),(900980028,r0),(379219043,r93),(398124585,r239),(2023847247,r2),(646060330,r8),(124299345,r2),(1766680259,r2),(515207295,r2),(395481619,r2),(1650934045,r2),(225834024,r2),(786738911,r2),(2040970625,r10),(1363735077,r10),(454391865,r93),(266315574,r2),(1736563673,r10),(827220461,r2),(1398628911,r10),(1959533798,r93),(488978143,r1),(1727118578,r2),(1471777341,r10),(1784048733,r2),(1132241887,r1),(222898675,r10),(1066838437,r2),(86124266,r10),(260996451,r2),(2044891273,r10),(485720693,r2),(1794816619,r8),(885473407,r10),(1820002234,r8),(910659022,r2),(1809191637,r10),(1790455145,r2),(1700671016,r2),(1004958559,r2),(207999341,r2),(385095256,r2),(1214702820,r2),(2406802,r2),(834010873,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f523 : ℕ := 0x2aa554a555184942506952d007c0ffff00033d19c067cfc
def s353 : List ℕ := [f16,f523,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b227 : Ban 94 7 s353 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2396164,r14),(340075141,r19),(716353769,r120)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f524 : ℕ := 0x4518a318a2e500000f800000003f000003fc00003f80000
def s354 : List ℕ := [f16,f17,f18,f524,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b226 : Ban 94 8 s354 := viaRules (ws := [s353]) (consBan b227 (nilBan _ _))
  (dictionary [(2049865910,r1),(13165278,r29),(1285255212,r29),(259643599,r1),(1712866459,r8),(672495800,r29),(1003689062,r8),(1926844695,r29),(100203901,r8),(2050333763,r1),(898498416,r8),(19564678,r1),(1757012546,r2),(1574485752,r119),(498718764,r1),(316191970,r2),(1451443913,r2),(1268917119,r119),(1314149213,r1),(1131622419,r2),(1093343045,r2),(910816251,r119),(2056359713,r0),(1873832919,r2),(615044087,r2),(432517293,r119),(1274626809,r2),(1150734605,r2),(968207811,r119),(512338308,r1),(329811514,r2),(1729240437,r2),(1546713643,r119),(904327465,r8),(721800671,r2),(880794759,r10),(1789503480,r2),(548600687,r2),(1905590067,r1),(666815141,r119),(733689016,r2),(1480982446,r119),(2119208632,r2),(651713703,r119),(1220089404,r2),(1480324840,r1),(241549914,r119),(1401946315,r10),(163171389,r2),(1567924389,r119),(1090029158,r2),(2146277290,r2),(907502364,r119),(888271164,r2),(366510179,r119),(1696694502,r2),(752472899,r119),(983276604,r1),(461515619,r2),(583106473,r2),(61345488,r119),(223517951,r119),(157548347,r112),(1783271009,r2),(1841160052,r119),(532557083,r1),(10796098,r2),(2050112296,r2),(1528351311,r119),(1766680259,r2),(1982060379,r2),(173810923,r2),(1799533585,r119),(1010550540,r2),(293536599,r2),(1919259261,r119),(1893030109,r1),(983686897,r119),(728345660,r2),(1040617052,r119),(388810206,r1),(1626950641,r2),(323406756,r119),(1490176232,r2),(1665048417,r119),(1301459592,r2),(1889772659,r119),(1051384938,r1),(142041726,r2),(1076570553,r1),(167227341,r119),(1065759956,r2),(534827678,r2),(352300884,r119),(848557288,r2),(666030494,r119),(89032918,r2),(2053989771,r119),(23703309,r2),(1988660162,r119),(1047023464,r119),(957239335,r119),(261526878,r119),(1612051307,r119),(1789147222,r119),(993032124,r2),(471271139,r119),(1406458768,r119),(612340177,r2),(90579192,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f525 : ℕ := 0x7dffbfffbeffffe80fffbf01f83fffc003ffffe03ffffe0
def s355 : List ℕ := [f16,f17,f18,f20,f21,f22,f525]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b228 : Ban 94 8 s355 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(798392946,r9),(909175961,r1),(33782248,r1),(1155654282,r49),(461393495,r59),(1568506483,r8),(1899699745,r59),(675371731,r8),(996214584,r59),(798860799,r8),(1794509099,r59),(915575361,r8),(538030516,r2),(1081766269,r119),(1444611370,r2),(1562825824,r119),(1629699699,r2),(229509482,r119),(867735668,r2),(1547724386,r119),(2116100087,r2),(228851876,r2),(1137560597,r119),(150473351,r23),(1059182072,r2),(316451425,r119),(1262520862,r119),(966982523,r10),(445221538,r2),(22760920,r23),(1648483582,r119),(1357526302,r2),(1479117156,r23),(957356171,r119),(948193665,r2),(1119528634,r119),(1053559030,r10),(531798045,r2),(589687088,r119),(1428567766,r10),(906806781,r2),(798639332,r23),(276878347,r119),(515207295,r2),(1010550540,r2),(293536599,r2),(1919259261,r119),(1786835547,r2),(548060621,r119),(177790385,r2),(641557145,r136),(1879697580,r119),(1624356343,r2),(1936627735,r119),(1284820889,r116),(375477677,r2),(1219417439,r119),(238703268,r2),(413575453,r119),(49986628,r2),(638299695,r119),(1947395621,r8),(1038052409,r2),(1972581236,r8),(1063238024,r119),(1961770639,r2),(1943034147,r119),(1853250018,r119),(1157537561,r119),(360578343,r119),(1367281822,r119),(154985804,r119),(1096549658,r23),(1810033547,r2),(1387659926,r2),(2101143815,r119),(1700736954,r23),(266737196,r2),(47717500,r2),(761201389,r119),(894720116,r23),(1608204005,r2),(1759121806,r2),(325122048,r119),(1469597730,r23),(35597972,r2),(549490649,r2),(1262974538,r119),(93192070,r23),(806675959,r2),(2069551423,r2),(635551665,r119),(827285255,r23),(1540769144,r2),(688990659,r2),(1402474548,r119),(1982060379,r2),(1090029158,r2),(571753902,r2),(746159111,r2),(1459643000,r119),(2071030558,r2),(637030800,r119),(725825520,r2),(1439309409,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f526 : ℕ := 0x6153f9f
def f527 : ℕ := 0xa828f27c
def f528 : ℕ := 0x1f9a30dd3
def s356 : List ℕ := [f526,f527,f528]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w165 : Wide 17 4 s356 := viaSearch (by decide +kernel)
def p147 : Weak 94 17 := relaxed (pick [0,1,2,3,4,21,22,23,24,25,54,55,60,61,76,77,93] (by decide) (by decide) (by decide))
def r241 : Rule 94 7 := cutRule 7 p147 w165
def f529 : ℕ := 0x280c3c8
def f530 : ℕ := 0x56ddc0c8
def f531 : ℕ := 0xaba20300
def s357 : List ℕ := [f529,f530,f531]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w166 : Wide 16 3 s357 := viaSearch (by decide +kernel)
def p148 : Weak 94 16 := signedPick 13 [13,14,27,34,40,41,47,48,50,51,73,74,84,85,90,91] (by decide) (by decide) (by decide)
def r242 : Rule 94 6 := cutRule 6 p148 w166
def f532 : ℕ := 0x7430
def s358 : List ℕ := [f291,f532,f292]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w167 : Wide 9 3 s358 := viaSearch (by decide +kernel)
def r243 : Rule 94 6 := cutRule 6 p126 w167
def f533 : ℕ := 0xa233cc
def f534 : ℕ := 0x5b770cc
def f535 : ℕ := 0xaea8300
def s359 : List ℕ := [f533,f534,f535]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w168 : Wide 14 3 s359 := viaSearch (by decide +kernel)
def p149 : Weak 94 14 := signedPick 13 [13,14,34,35,40,41,47,48,50,51,73,74,90,91] (by decide) (by decide) (by decide)
def r244 : Rule 94 6 := cutRule 6 p149 w168
def f536 : ℕ := 0x79ef3def3cfefff7e05f8001ffc0f80003ffffffc07f000
def s360 : List ℕ := [f16,f17,f18,f20,f21,f536]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b230 : Ban 94 7 s360 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1826317526,r25),(1378535060,r25),(1913356149,r25),(399357617,r70),(1145993441,r5),(1067614916,r5),(1976323637,r70),(1884124088,r242),(939902485,r243),(248775074,r120),(1970700595,r244),(198225684,r5),(1715780897,r5),(1210678164,r70),(1094931950,r70),(1166830886,r5),(1267536045,r5),(1227260885,r5),(1238883765,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f537 : ℕ := 0x2fd630
def f538 : ℕ := 0x3f694c
def s361 : List ℕ := [f456,f537,f538]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w169 : Wide 11 3 s361 := viaSearch (by decide +kernel)
def p150 : Weak 94 11 := signedPick 5 [5,7,12,14,19,20,41,69,74,76,80] (by decide) (by decide) (by decide)
def r245 : Rule 94 6 := cutRule 6 p150 w169
def f539 : ℕ := 0x4929252924ec03f7e0000001ffc0000003fc0fffc000000
def s362 : List ℕ := [f16,f17,f18,f539,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b231 : Ban 94 7 s362 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1984991775,r25),(1537209309,r25),(2072030398,r25),(672295569,r5),(420671184,r5),(1651617087,r33),(301386711,r5),(1373228420,r5),(1045406121,r70),(1304667690,r5),(1226289165,r5),(407449323,r61),(2129374844,r245),(356899933,r5),(1874455146,r61),(1591023109,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f540 : ℕ := 0x30c618c61812fc00005f80000000f8000003f000007f000
def s363 : List ℕ := [f16,f17,f540,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b229 : Ban 94 8 s363 := viaRules (ws := [s360,s362]) (consBan b230 (consBan b231 (nilBan _ _)))
  (dictionary [(678667270,r1),(789450285,r29),(2061540219,r29),(1035928606,r1),(1107720020,r2),(1701478233,r119),(811249472,r10),(1405007685,r2),(1878048532,r2),(324323098,r119),(1064333541,r10),(1658091754,r2),(1525106636,r2),(2118864849,r119),(79613014,r10),(673371227,r2),(1253340146,r2),(1847098359,r119),(203545150,r10),(797303363,r2),(341667819,r8),(1448780807,r29),(1779974069,r8),(555646055,r29),(876488908,r8),(679135123,r1),(1674783423,r8),(795849685,r1),(181765784,r2),(775523997,r119),(999614933,r10),(1593373146,r2),(2018561029,r10),(464835595,r2),(1797414399,r2),(243688965,r119),(1657079766,r10),(418304840,r2),(962040593,r119),(1324885694,r2),(534391427,r1),(1443100148,r119),(1509974023,r2),(109783806,r119),(748009992,r2),(1427998710,r119),(2101786055,r2),(1786835547,r2),(548060621,r119),(1996374411,r2),(109126200,r1),(1017834921,r119),(30747675,r10),(939456396,r2),(196725749,r119),(1142795186,r119),(847256847,r10),(325495862,r2),(2050518891,r23),(1528757906,r119),(1237800626,r2),(1359391480,r23),(837630495,r119),(828467989,r2),(999802958,r119),(933833354,r10),(412072369,r2),(1205775372,r2),(173810923,r2),(1799533585,r119),(469961412,r119),(1308842090,r10),(787081105,r2),(678913656,r23),(157152671,r119),(395481619,r2),(1296839635,r241),(775078650,r2),(58064709,r2),(1683787371,r119),(521831469,r1),(1759971904,r119),(1504630667,r2),(1816902059,r119),(1165095213,r1),(255752001,r2),(1099691763,r119),(118977592,r2),(293849777,r119),(2077744599,r2),(768926010,r2),(1362684223,r119),(2109584408,r2),(1465202186,r2),(555858974,r119),(120775010,r2),(1623876435,r2),(714533223,r119),(1269673517,r2),(1863431730,r119),(518574019,r119),(1827669945,r1),(918326733,r2),(1852855560,r1),(943512348,r119),(1842044963,r2),(1823308471,r119),(1733524342,r119),(1037811885,r119),(240852667,r119),(417948582,r119),(35260128,r119),(866864199,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f541 : ℕ := 0x8210421040803e800203f01f80007c000000fe00000fe0
def s364 : List ℕ := [f541,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b232 : Ban 94 8 s364 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1361157577,r10),(1062884569,r2),(1433993854,r2),(1135720846,r119),(843705332,r2),(545432324,r119),(1541885741,r10),(1243612733,r2),(164871879,r10),(2014082518,r2),(780717864,r2),(482444856,r119),(645980844,r2),(347707836,r119),(24520186,r10),(1873730825,r2),(1934119696,r16),(2044902711,r1),(1169508998,r1),(143897385,r49),(305347230,r10),(7074222,r2),(1371600451,r2),(1073327443,r119),(526869004,r2),(228595996,r119),(1467322756,r10),(1169049748,r2),(1597120245,r59),(556749586,r8),(887942848,r59),(1811098481,r8),(2131941334,r59),(1934587549,r8),(782752202,r59),(2051302111,r8),(1205775372,r2),(2146277290,r2),(907502364,r119),(1673757266,r2),(70009372,r119),(432854473,r2),(551068927,r119),(617942802,r2),(1365236232,r119),(2003462418,r2),(535967489,r119),(1104343190,r2),(1364578626,r2),(125803700,r119),(1286200101,r23),(47425175,r2),(1452178175,r119),(2101786055,r2),(177790385,r2),(772524950,r2),(250763965,r119),(1580948288,r2),(636726685,r119),(867530390,r203),(345769405,r2),(467360259,r2),(2093082921,r119),(2083920415,r2),(107771737,r119),(41802133,r112),(1667524795,r2),(1725413838,r119),(416810869,r8),(2042533531,r2),(1934366082,r2),(1412605097,r119),(1650934045,r2),(1296839635,r241),(775078650,r2),(58064709,r2),(1683787371,r119),(1125564326,r2),(827291318,r119),(454829208,r2),(156556200,r119),(148216364,r2),(1997427003,r119),(183736546,r2),(2032947185,r119),(1777283895,r136),(867940683,r119),(612599446,r2),(924870838,r119),(273063992,r116),(1511204427,r2),(207660542,r119),(1374430018,r2),(1549302203,r119),(1185713378,r2),(1774026445,r119),(935638724,r8),(26295512,r2),(960824339,r8),(51481127,r119),(950013742,r2),(931277250,r119),(841493121,r119),(145780664,r119),(1496305093,r119),(877285910,r2),(355524925,r119),(1290712554,r119),(496593963,r2),(2122316625,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s365 : List ℕ := [f49,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b234 : Ban 94 7 s365 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2075556903,r5),(952101210,r109),(181256361,r25),(1922166665,r5),(880395553,r5),(1078428087,r25),(1613249176,r25),(845886468,r5),(767507943,r5),(2096151748,r197),(1670593622,r125),(2045602358,r5),(1415673924,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w170 : Wide 9 2 s142 := viaSearch (by decide +kernel)
def r246 : Rule 94 6 := cutRule 6 p85 w170
def s366 : List ℕ := [f49,f48,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b235 : Ban 94 7 s366 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2075556903,r5),(571337000,r5),(589721444,r246),(405278642,r145),(1226650678,r174),(1148272153,r174),(1108723753,r145),(1106793596,r145),(329432311,r197),(2051357832,r125),(278882921,r174),(1796438134,r174)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w171 : Wide 10 2 s231 := viaSearch (by decide +kernel)
def r247 : Rule 94 6 := cutRule 6 p111 w171
def f542 : ℕ := 0x45ccfc
def f543 : ℕ := 0x6de0c8
def f544 : ℕ := 0xd7dc34
def s367 : List ℕ := [f542,f543,f544]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w172 : Wide 12 3 s367 := viaSearch (by decide +kernel)
def p151 : Weak 94 12 := signedPick 17 [17,18,27,29,40,41,42,43,44,45,84,85] (by decide) (by decide) (by decide)
def r248 : Rule 94 6 := cutRule 6 p151 w172
def f545 : ℕ := 0x49dcf
def f546 : ℕ := 0xa26f3
def f547 : ℕ := 0xf14b3c
def s368 : List ℕ := [f545,f546,f547]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w173 : Wide 12 3 s368 := viaSearch (by decide +kernel)
def p152 : Weak 94 12 := relaxed (pick [2,3,27,28,29,30,31,32,40,42,63,84] (by decide) (by decide) (by decide))
def r249 : Rule 94 6 := cutRule 6 p152 w173
def s369 : List ℕ := [f49,f48,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b236 : Ban 94 7 s369 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1284445750,r24),(1700078190,r5),(848588333,r25),(24514432,r5),(652279701,r25),(1459192297,r247),(727959543,r248),(726029386,r249)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p153 : Weak 94 8 := signedPick 4 [4,5,6,26,27,33,34,87] (by decide) (by decide) (by decide)
def r250 : Rule 94 6 := cutRule 6 p153 w140
def f548 : ℕ := 0x28a2ffc
def s370 : List ℕ := [f548,f322,f323]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w174 : Wide 14 3 s370 := viaSearch (by decide +kernel)
def r251 : Rule 94 6 := cutRule 6 p86 w174
def p154 : Weak 94 8 := signedPick 5 [5,6,8,26,27,33,34,87] (by decide) (by decide) (by decide)
def r252 : Rule 94 6 := cutRule 6 p154 w142
def s371 : List ℕ := [f16,f17,f18,f20,f415,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b237 : Ban 94 7 s371 := viaRules (ws := [s233]) (consBan b130 (nilBan _ _))
  (dictionary [(447429701,r5),(558212716,r25),(1830302650,r25),(804691037,r5),(2009978152,r5),(110430250,r25),(1217543238,r25),(1548736500,r25),(76472741,r5),(324408486,r25),(645251339,r25),(199961809,r27),(447897554,r5),(1195610109,r250),(1443545854,r25),(564612116,r5),(187067271,r5),(730803024,r25),(1093648125,r25),(2026029884,r24),(516772423,r24),(1765136842,r25),(538661607,r251),(2025372278,r5),(786597352,r5),(1946993753,r5),(1865036082,r252),(2112971827,r25),(130576617,r5),(1731237696,r5),(880395553,r5),(333572985,r5),(18820421,r24),(1326106748,r24),(624906912,r24),(1925381823,r24),(1934060644,r72),(581335310,r5),(34512742,r5),(1985129740,r24),(1746502810,r24),(2014390691,r27),(94258293,r25),(1297520337,r25),(1128153911,r20),(606392926,r25),(768565389,r25),(702595785,r27),(180834800,r5),(238723843,r25),(1077604521,r5),(447676087,r5),(164244050,r25),(197097376,r25),(1452549802,r5),(1904931024,r27),(1001468075,r181),(479707090,r25),(920893822,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f549 : ℕ := 0x295451fcffc
def s372 : List ℕ := [f549,f119,f120]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w175 : Wide 21 3 s372 := viaSearch (by decide +kernel)
def r253 : Rule 94 6 := cutRule 6 p34 w175
def f550 : ℕ := 0x75debbdebaf7fc10afdf8001fffff80003fff3e7ffff000
def s373 : List ℕ := [f48,f16,f17,f18,f20,f550]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b238 : Ban 94 7 s373 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(727959543,r248),(1108723753,r145),(388060413,r253),(165971938,r145),(1037112580,r145),(93798587,r145),(2019193759,r246),(1286047673,r24),(1869799680,r246),(1907445353,r27),(1685356878,r145),(165638500,r145),(737957853,r145),(591786886,r24),(929254190,r24),(1924902490,r24),(1045968752,r24),(1862927834,r145),(1640839359,r246),(1411317938,r145),(668423907,r145),(359902873,r246),(998129059,r145),(1678117777,r246),(359245267,r176),(1267953988,r246),(280866742,r158),(1189575463,r145),(446844816,r246),(2087199322,r145),(82765642,r145),(346782209,r215),(1664504517,r246),(1049810949,r204),(1874665299,r246),(82181470,r235),(1229586580,r237),(864448138,r246)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r254 : Rule 94 6 := cutRule 6 p114 w150
def f551 : ℕ := 0x659cb39cb2f5e8000fdf8000003ff80002e300003fff000
def s374 : List ℕ := [f48,f16,f17,f18,f20,f551]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b239 : Ban 94 7 s374 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(726029386,r249),(1106793596,r145),(1534482891,r246),(164041781,r145),(1905515196,r181),(1683426721,r145),(163708343,r145),(736027696,r108),(513939221,r246),(589856729,r254),(927324033,r181),(1922972333,r254),(1638909202,r246),(357315110,r181),(278936585,r181),(444914659,r246),(2087199322,r145),(84695799,r145),(1743364182,r246),(245794784,r215),(1655579611,r246),(1577938068,r204),(1809017295,r181),(1326202168,r181),(537314877,r145)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s375 : List ℕ := [f48,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b233 : Ban 94 8 s375 := viaRules (ws := [s365,s366,s369,s18,s371,s89,s234,s252,s373,s374,s299,s319,s335,s342]) (consBan b234 (consBan b235 (consBan b236 (consBan b7 (consBan b237 (consBan b47 (consBan b129 (consBan b147 (consBan b238 (consBan b239 (consBan b177 (consBan b193 (consBan b208 (consBan b216 (nilBan _ _)))))))))))))))
  (dictionary [(1379790505,r136),(9349395,r57),(880490037,r57),(1862571216,r136),(882946809,r1),(7553096,r1),(1129425130,r57),(1713177137,r1),(1528734335,r57),(9015957,r1),(359246835,r136),(435164343,r1),(1542277331,r1),(1873470593,r1),(649142579,r1),(969985432,r1),(772631647,r57),(1768279947,r1),(889346209,r57),(1484216816,r136),(132845883,r136),(1032606920,r136),(1058124491,r136),(511801364,r115),(1055537117,r1),(1418382218,r1),(1536596672,r136),(1603470547,r115),(203280330,r136),(841506516,r115),(1521495234,r136),(2089870935,r1),(1111331445,r136),(1032952920,r115),(290222273,r1),(1495309306,r1),(1710418461,r136),(1708488304,r1),(793689081,r136),(1236291710,r1),(418992386,r1),(1622254430,r1),(1331297150,r1),(931127019,r1),(921964513,r115),(1093299482,r1),(505568893,r115),(563457936,r1),(880577629,r1),(250649195,r1),(488978143,r1),(1893030109,r1),(641557145,r136),(521831469,r1),(1777283895,r136)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s376 : List ℕ := [f16,f17,f18,f20,f550,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b241 : Ban 94 7 s376 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(352314615,r18),(2052015796,r18),(439353238,r18),(2128652817,r70),(310874322,r70),(1819474177,r19),(1741095652,r19),(502320726,r70),(1807011119,r19),(362556212,r19),(1542410380,r19),(542331843,r19),(177193401,r33),(84695799,r145),(727959543,r248),(591185134,r223),(766057319,r44),(1390534275,r19),(1415719890,r19),(148032366,r70),(713060209,r70),(596361692,r77),(1339071741,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s377 : List ℕ := [f16,f17,f18,f20,f551,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b242 : Ban 94 7 s377 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(350384458,r18),(2050085639,r18),(437423081,r18),(1817544020,r19),(1739165495,r19),(1706023694,r19),(890683331,r19),(1121762558,r19),(754693959,r70),(638947431,r19),(82765642,r145),(726029386,r249),(1388604118,r19),(1413789733,r19),(1717833531,r70),(618599476,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s378 : List ℕ := [f48,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b240 : Ban 94 8 s378 := viaRules (ws := [s376,s377,s366,s369]) (consBan b241 (consBan b242 (consBan b235 (consBan b236 (nilBan _ _)))))
  (dictionary [(1809477435,r23),(42757998,r2),(1587388960,r2),(692535768,r2),(470447293,r119),(1469578305,r0),(1247489830,r2),(193235300,r0),(2118630472,r2),(1175316479,r2),(953228004,r119),(2010304229,r0),(2121087244,r1),(1245693531,r1),(220081918,r30),(1025922400,r2),(803833925,r119),(841479598,r0),(619391123,r2),(1469244867,r8),(1247156392,r2),(1819475745,r2),(1597387270,r119),(1673304778,r8),(632934119,r1),(964127381,r8),(1887283014,r1),(60642220,r8),(2010772082,r30),(858936735,r8),(2127486644,r30),(796962079,r2),(574873604,r119),(1593074793,r2),(1370986318,r119),(345352183,r2),(123263708,r119),(370869754,r2),(148781279,r119),(1749941799,r2),(146193905,r119),(509039006,r2),(627253460,r119),(694127335,r2),(1441420765,r119),(2079646951,r2),(612152022,r119),(1180527723,r2),(1440763159,r0),(201988233,r119),(1362384634,r0),(123609708,r2),(1528362708,r119),(808054569,r2),(585966094,r119),(1023163724,r2),(1322836234,r2),(801075249,r119),(1021233567,r2),(1320906077,r2),(799145092,r119),(106434344,r2),(2031829516,r119),(326948498,r119),(1657132821,r2),(712911218,r119),(421953938,r2),(543544792,r0),(21783807,r119),(12621301,r2),(183956270,r119),(117986666,r0),(1743709328,r2),(1801598371,r119),(492995402,r0),(2118718064,r2),(2010550615,r0),(1488789630,r119),(1727118578,r2),(983686897,r119),(1879697580,r119),(1759971904,r119),(867940683,r119),(1223143846,r2),(1910398583,r1),(1001055371,r119),(1291636664,r2),(1598127191,r1),(688783979,r2),(1193188287,r0),(283845075,r119),(212474116,r57),(1450614551,r2),(387346301,r57),(1625486736,r119),(23757476,r0),(1261897911,r2),(612070543,r1),(1850210978,r119),(1011823257,r0),(102480045,r2),(1037008872,r0),(127665660,r119),(1935541487,r1),(1026198275,r2),(1916804995,r2),(1007461783,r119),(1827020866,r10),(917677654,r119),(1131308409,r10),(221965197,r119),(334349191,r2),(1572489626,r119),(511445106,r10),(1749585541,r119),(1341052670,r2),(431709458,r119),(128756652,r2),(1366897087,r119),(960360723,r10),(51017511,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r255 : Rule 94 7 := cutRule 7 p12 w9
def f552 : ℕ := 0xaa80ce2
def f553 : ℕ := 0xaabfc2e
def f554 : ℕ := 0xffe00c0
def f555 : ℕ := 0xffe30fc
def s379 : List ℕ := [f552,f553,f554,f555]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w176 : Wide 14 4 s379 := viaSearch (by decide +kernel)
def p155 : Weak 94 14 := signedPick 5 [5,12,26,28,36,41,49,50,67,69,72,74,83,85] (by decide) (by decide) (by decide)
def r256 : Rule 94 7 := cutRule 7 p155 w176
def f556 : ℕ := 0x7ffffffffffffffff302c5c7ffc0ffc0ffffffffdc1f3f3
def s380 : List ℕ := [f16,f17,f18,f20,f21,f22,f556]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b243 : Ban 94 8 s380 := viaRules (ws := [s365]) (consBan b234 (nilBan _ _))
  (dictionary [(1865746007,r29),(990352294,r29),(2112224328,r1),(1417963541,r59),(377592882,r8),(708786144,r59),(1631941777,r8),(1952784630,r59),(1755430845,r8),(603595498,r59),(1872145407,r8),(1494600562,r10),(2038336315,r2),(253697769,r10),(438786098,r10),(1186079528,r2),(1824305714,r10),(356810785,r2),(925186486,r10),(1185421922,r8),(2094130643,r2),(1107043397,r8),(2015752118,r10),(1273021471,r2),(1401791584,r10),(457569981,r2),(288203555,r111),(1913926217,r2),(1904763711,r10),(2076098680,r2),(2010129076,r112),(1488368091,r10),(1546257134,r2),(237654165,r8),(1863376827,r10),(1755209378,r8),(1233448393,r2),(1471777341,r10),(728345660,r2),(1624356343,r2),(1504630667,r2),(612599446,r2),(1291636664,r2),(1598127191,r1),(688783979,r2),(1348566819,r2),(745714134,r2),(93907288,r1),(1332047723,r255),(1195273314,r255),(1370145499,r2),(1006556674,r255),(1594869741,r2),(756482020,r8),(1994622455,r255),(781667635,r8),(2019808070,r2),(770857038,r255),(662336417,r2),(2114107607,r2),(1317148389,r2),(176368221,r2),(1943159921,r2),(1223143846,r2),(1870088703,r256),(1392658991,r23),(865242715,r23),(387813003,r255),(1809784083,r0),(1332354371,r23),(1763553867,r23),(1286124155,r255),(1902645555,r8),(1425215843,r23),(379288214,r23),(2049342149,r255),(1375309745,r8),(897880033,r23),(403342228,r23),(2073396163,r255),(188755145,r10),(1858809080,r10),(198227611,r2),(1868281546,r2),(1534112653,r2),(1056682941,r2),(2119852345,r10),(1642422633,r10),(309641572,r2),(1979695507,r2),(1982384228,r10),(1504954516,r10),(121665233,r10),(1791719168,r10),(1853512309,r2),(1376082597,r2),(1809477435,r23)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f557 : ℕ := 0xba0c0
def s381 : List ℕ := [f412,f557,f402]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w177 : Wide 10 4 s381 := viaSearch (by decide +kernel)
def r257 : Rule 94 7 := cutRule 7 p111 w177
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b245 : Ban 94 7 s375 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(571337000,r5),(952101210,r109),(9349395,r145),(1713177137,r25),(1750822810,r5),(1528734335,r5),(9015957,r25),(581335310,r5),(359246835,r5),(435164343,r25),(772631647,r5),(1768279947,r25),(1484216816,r246),(202622724,r5),(124244199,r5),(290222273,r25),(84695799,r145),(82765642,r145),(1452888004,r215),(1027329878,r204),(1402338614,r5),(772410180,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f558 : ℕ := 0x69ad35ad34fcebe7400000000000000002e30c180000000
def s382 : List ℕ := [f16,f17,f18,f20,f558,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b244 : Ban 94 8 s382 := viaRules (ws := [s375]) (consBan b245 (nilBan _ _))
  (dictionary [(30533752,r29),(1302623686,r29),(277012073,r1),(1730234933,r8),(689864274,r29),(1021057536,r8),(1944213169,r29),(117572375,r8),(2067702237,r1),(915866890,r8),(36933152,r1),(1806871954,r2),(203124060,r119),(565969161,r2),(684183615,r119),(751057490,r2),(1498350920,r119),(2136577106,r2),(669082177,r119),(1237457878,r2),(1497693314,r1),(258918388,r119),(1419314789,r1),(180539863,r2),(1585292863,r119),(1348566819,r2),(910872454,r23),(745714134,r2),(1951722644,r2),(1786564324,r119),(1489877701,r0),(1324719381,r2),(940992866,r2),(775834546,r119),(1730110913,r0),(1564952593,r2),(1384760753,r2),(1219602433,r119),(1649078307,r1),(1483919987,r2),(1759173653,r2),(1594015333,r119),(1207917827,r8),(1042759507,r2),(360385,r2),(1982685712,r119),(716613149,r2),(551454829,r119),(2048018494,r2),(1882860174,r119),(2081432446,r2),(1916274126,r119),(383878653,r119),(1714062976,r2),(769841373,r119),(478884093,r2),(600474947,r0),(78713962,r119),(69551456,r2),(240886425,r119),(174916821,r0),(1800639483,r2),(1858528526,r119),(549925557,r1),(28164572,r2),(2067480770,r1),(1545719785,r119),(1784048733,r2),(1040617052,r119),(1936627735,r119),(1816902059,r119),(924870838,r119),(30467939,r2),(2012793266,r119),(1969088963,r2),(1803930643,r119),(1325333819,r2),(1160175499,r119),(391016726,r2),(225858406,r119),(1910398583,r1),(1001055371,r119),(1009031365,r257),(99688153,r2),(406178680,r1),(1644319115,r2),(340775230,r119),(1507544706,r2),(1682416891,r119),(1318828066,r2),(1907141133,r119),(1068753412,r1),(159410200,r2),(1093939027,r1),(184595815,r119),(1083128430,r2),(1064391938,r119),(974607809,r119),(278895352,r119),(1629419781,r119),(1166213691,r2),(1806515696,r119),(488639613,r119),(1423827242,r119),(107947666,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f559 : ℕ := 0x28a514a5141849424069121007ff003f02e33d19e3e0c0c
def s383 : List ℕ := [f49,f16,f559,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b247 : Ban 94 7 s383 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2015232189,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f560 : ℕ := 0x4718e318e3c1a28d1f16edee0000ffffff03ce1e3c7ffff
def s384 : List ℕ := [f16,f17,f18,f560,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b248 : Ban 94 7 s384 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(729556571,r25),(33838360,r5),(281774105,r25),(247816596,r5),(495752341,r25),(1614889709,r25),(1490029101,r5),(581335310,r5),(880395553,r5),(504916840,r5),(49232486,r5),(2118337608,r5),(1299497766,r20),(873939640,r76),(1248948376,r5),(619019942,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r258 : Rule 94 7 := cutRule 7 p111 w119
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b246 : Ban 94 8 s365 := viaRules (ws := [s375,s366,s369,s383,s19,s384,s92,s235,s253,s300,s320,s336,s343]) (consBan b245 (consBan b235 (consBan b236 (consBan b247 (consBan b8 (consBan b248 (consBan b48 (consBan b131 (consBan b148 (consBan b179 (consBan b194 (consBan b209 (consBan b217 (nilBan _ _))))))))))))))
  (dictionary [(68537494,r116),(1723823446,r58),(1927709494,r116),(1526210553,r1),(650816840,r1),(1772688874,r58),(181256361,r1),(195858287,r258),(1491852077,r1),(1301570822,r116),(1078428087,r1),(38057428,r1),(369250690,r1),(1292406323,r1),(1613249176,r1),(1415895391,r58),(264060044,r1),(1532609953,r58),(2069081424,r116),(362315189,r116),(1400207161,r116),(1789108658,r116),(1155065108,r116),(1698800861,r1),(2061645962,r1),(32376769,r137),(99250644,r116),(846544074,r147),(1484770260,r116),(17275331,r137),(585651032,r1),(1754595189,r137),(1676216664,r116),(933486017,r1),(84451893,r1),(980368537,r116),(454750893,r1),(2004724832,r116),(1879555454,r1),(1062256130,r1),(118034527,r1),(1974560894,r1),(1574390763,r1),(1565228257,r224),(1736563226,r1),(1148832637,r224),(1206721680,r1),(1523841373,r1),(893912939,r1),(1132241887,r1),(388810206,r1),(1284820889,r116),(1165095213,r1),(273063992,r116)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s385 : List ℕ := [f16,f559,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b250 : Ban 94 7 s385 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(684713708,r14),(1109519012,r127)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p156 : Weak 94 9 := signedPick 6 [6,7,8,9,10,11,33,35,37] (by decide) (by decide) (by decide)
def r259 : Rule 94 7 := cutRule 7 p156 w86
def f561 : ℕ := 0x8228133c
def f562 : ℕ := 0x2f7681330
def s386 : List ℕ := [f561,f435,f436,f562]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w178 : Wide 17 4 s386 := viaSearch (by decide +kernel)
def p157 : Weak 94 17 := signedPick 17 [17,20,40,41,42,43,44,45,47,48,50,51,52,53,79,80,81] (by decide) (by decide) (by decide)
def r260 : Rule 94 7 := cutRule 7 p157 w178
def s387 : List ℕ := [f49,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b249 : Ban 94 8 s387 := viaRules (ws := [s385,s366,s369]) (consBan b250 (consBan b235 (consBan b236 (nilBan _ _))))
  (dictionary [(1166213691,r2),(42757998,r2),(1587388960,r2),(885502660,r23),(1306677929,r255),(393304965,r0),(814480234,r23),(758140366,r23),(597191013,r23),(1018366282,r255),(506084326,r26),(616867341,r1),(1888957275,r1),(863345662,r0),(998221527,r23),(1419396796,r255),(1012823453,r8),(1433998722,r23),(161333596,r8),(582508865,r23),(2118535988,r23),(392227610,r255),(169084875,r59),(1276197863,r8),(1607391125,r59),(383063111,r8),(703905964,r59),(506552179,r8),(1502200479,r59),(623266741,r8),(738562943,r10),(1159738212,r10),(1179280355,r2),(1600455624,r2),(69688680,r10),(490863949,r10),(458590177,r2),(879765446,r2),(245721896,r10),(789457649,r2),(1152302750,r10),(1270517204,r2),(1337391079,r10),(2084684509,r2),(575427048,r10),(1255415766,r2),(1823791467,r10),(2084026903,r8),(845251977,r2),(2005648378,r8),(766873452,r10),(24142805,r2),(901417059,r2),(1322592328,r2),(1797333703,r10),(71025325,r10),(1271716059,r2),(1692891328,r2),(674206351,r10),(1095381620,r10),(970212242,r2),(152912918,r10),(1356174962,r2),(1065217682,r10),(1186808536,r111),(665047551,r2),(655885045,r10),(827220014,r2),(761250410,r112),(239489425,r10),(297378468,r2),(1136259146,r8),(614498161,r10),(506330712,r8),(2132053374,r2),(222898675,r10),(1626950641,r2),(375477677,r2),(255752001,r2),(1511204427,r2),(910872454,r23),(93907288,r1),(1332047723,r255),(1009031365,r257),(99688153,r2),(406178680,r1),(1644319115,r2),(1836452031,r259),(927108819,r2),(855737860,r260),(2093878295,r255),(1030610045,r58),(121266833,r2),(667021220,r202),(1905161655,r255),(1255334287,r1),(345991075,r2),(1655087001,r8),(745743789,r255),(1680272616,r8),(770929404,r2),(431321584,r1),(1669462019,r255),(412585092,r116),(1650725527,r2),(322800963,r23),(1560941398,r2),(1774572153,r23),(865228941,r2),(977612935,r116),(68269723,r2),(1154708850,r232),(245365638,r2),(1984316414,r23),(1074973202,r2),(772020396,r23),(2010160831,r2),(1603624467,r232),(694281255,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f563 : ℕ := 0x1652ca52cb031418b302c5c7f800ffc0fd1cc2e61c1f3f3
def s388 : List ℕ := [f563,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b252 : Ban 94 7 s388 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(195692072,r25),(1895393253,r14),(571337000,r5),(1524041179,r145)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f564 : ℕ := 0x28a514a5141849424000000007c0000002e33d19c000000
def s389 : List ℕ := [f16,f564,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b251 : Ban 94 8 s389 := viaRules (ws := [s388]) (consBan b252 (nilBan _ _))
  (dictionary [(692535768,r2),(1957650799,r119),(892913364,r1),(10544748,r2),(1951722644,r2),(1069354028,r119),(1499048788,r2),(1350024088,r0),(1460807103,r30),(585413390,r0),(1707285424,r30),(1483986386,r23),(483486835,r2),(601617770,r2),(1013024637,r8),(2120137625,r0),(303847240,r8),(1227002873,r0),(684593226,r2),(1949708257,r119),(1483320749,r0),(600952133,r2),(1803392174,r8),(921023558,r2),(1222333663,r2),(339965047,r119),(1547845726,r8),(1350491941,r30),(198656594,r8),(1467206503,r30),(1089661658,r2),(1633397411,r119),(1996242512,r2),(2114456966,r119),(837110659,r2),(2102225690,r119),(1214281462,r2),(331912846,r119),(1613748755,r2),(731380139,r119),(888482247,r2),(6113631,r119),(33847194,r2),(781140624,r119),(1419366810,r2),(2099355528,r119),(520247582,r2),(780483018,r0),(1689191739,r119),(702104493,r0),(1610813214,r2),(868082567,r119),(1814152004,r119),(996852680,r2),(52631077,r119),(1909157444,r2),(1057265536,r2),(174896920,r119),(450577170,r2),(1715692201,r119),(600628828,r2),(1865743859,r119),(698437038,r2),(1963552069,r119),(2030748298,r0),(1508987313,r119),(1671159776,r119),(1605190172,r0),(1083429187,r2),(1141318230,r119),(1980198908,r0),(1458437923,r2),(1350270474,r0),(828509489,r119),(1066838437,r2),(323406756,r119),(1219417439,r119),(1099691763,r119),(207660542,r119),(1193188287,r0),(283845075,r119),(340775230,r119),(1836452031,r259),(927108819,r2),(1847575211,r2),(1874549807,r0),(965206595,r119),(672203475,r2),(1699677622,r0),(790334410,r2),(1189930837,r119),(351543116,r0),(1589683551,r2),(376728731,r0),(1614869166,r119),(365918134,r2),(1256524854,r2),(347181642,r119),(257397513,r119),(1709168703,r119),(1821552697,r2),(912209485,r119),(1089305400,r119),(1918912964,r119),(706616946,r119),(1538221017,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f565 : ℕ := 0x1242484249021410b00040c1ffc0ffc0011cf3e7c4070f0
def s390 : List ℕ := [f565,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b254 : Ban 94 7 s390 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1118661508,r33),(2075556903,r5),(379903843,r109)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f566 : ℕ := 0x6ed0cc
def f567 : ℕ := 0xbba330
def s391 : List ℕ := [f439,f566,f567]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w179 : Wide 12 3 s391 := viaSearch (by decide +kernel)
def p158 : Weak 94 12 := signedPick 13 [13,14,15,16,17,18,23,24,44,45,71,74] (by decide) (by decide) (by decide)
def r261 : Rule 94 6 := cutRule 6 p158 w179
def f568 : ℕ := 0x4929252924ec03e000201201f83f07c003fc0fe02780ce0
def s392 : List ℕ := [f16,f17,f18,f568,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b255 : Ban 94 7 s392 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1799353205,r18),(1351570739,r14),(642393342,r14),(1886391828,r14),(1805752605,r13),(601280196,r60),(1709662833,r60),(299851873,r13),(664738080,r61),(1327845466,r13),(1692731673,r60),(1277257441,r61),(1335398782,r61),(221810753,r19),(1943736274,r19),(1421975289,r61),(171261363,r13),(1796984025,r61),(1688816576,r13),(1405384539,r61),(1531734389,r261),(27514486,r109),(871454248,r19),(1849507084,r19),(690089218,r13),(715274833,r13),(1363687987,r61),(809574370,r61),(1019318631,r61),(1954506260,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f569 : ℕ := 0x32c658c65912fc17f04940d007c0f83f0003f01fc06701c
def s393 : List ℕ := [f16,f17,f569,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b256 : Ban 94 7 s393 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1814418775,r25),(1366636309,r14),(1901457398,r14),(552268266,r14),(465393134,r13),(546050788,r13),(236876323,r19),(1958801844,r19),(186326933,r13),(1703882146,r13),(1546799959,r5),(42580056,r127),(705154788,r61),(730340403,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p159 : Weak 94 10 := signedPick 5 [5,6,26,27,33,34,66,82,87,88] (by decide) (by decide) (by decide)
def r262 : Rule 94 6 := cutRule 6 p159 w131
def p160 : Weak 94 7 := signedPick 17 [17,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r263 : Rule 94 6 := cutRule 6 p160 w85
def f570 : ℕ := 0x71ce39ce38f6fc0000490000003ff80003fff00027e7000
def s394 : List ℕ := [f16,f17,f18,f20,f570,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b257 : Ban 94 7 s394 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(852793506,r18),(405011040,r14),(939832129,r14),(172469421,r13),(94090896,r13),(260068970,r61),(350108187,r61),(765633267,r19),(340075141,r19),(1485562630,r60),(1705111597,r13),(1840452046,r61),(1479081048,r13),(1958576613,r61),(585174690,r262),(1228438434,r263),(1891013166,r196),(1916198781,r13),(1361908386,r61),(1007946561,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f571 : ℕ := 0xa214421450803f7f02052d1ffc007ff00000fffc000cfc
def s395 : List ℕ := [f571,f16,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b258 : Ban 94 7 s395 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(340075141,r19),(765633267,r19),(559252849,r18),(113965693,r13),(1146418690,r13),(111470383,r14),(646291472,r14),(1444585987,r14),(2026412411,r13),(1948033886,r13),(291634033,r204),(934897777,r127),(1597472509,r61),(1622658124,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f572 : ℕ := 0x7bef7def7dfefff7f06952d1ffffffff03ffffffe7e7cfc
def s396 : List ℕ := [f16,f17,f18,f20,f21,f22,f572]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b253 : Ban 94 8 s396 := viaRules (ws := [s390,s392,s393,s394,s395]) (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (nilBan _ _))))))
  (dictionary [(369309917,r0),(480092932,r30),(1752182866,r0),(726571253,r30),(32310466,r59),(1139423454,r8),(1470616716,r59),(246288702,r8),(567131555,r59),(369777770,r8),(1365426070,r59),(486492332,r8),(108947487,r10),(652683240,r2),(1015528341,r10),(1133742795,r2),(1200616670,r10),(1947910100,r2),(438652639,r10),(1118641357,r2),(1687017058,r10),(1947252494,r8),(708477568,r2),(1868873969,r8),(630099043,r10),(2034852043,r2),(833437833,r2),(16138509,r10),(1219400553,r2),(928443273,r10),(1050034127,r0),(528273142,r2),(519110636,r10),(690445605,r2),(624476001,r0),(102715016,r10),(160604059,r2),(999484737,r8),(477723752,r10),(369556303,r8),(1995278965,r2),(86124266,r10),(1490176232,r2),(238703268,r2),(118977592,r2),(1374430018,r2),(212474116,r57),(1450614551,r2),(1195273314,r255),(1507544706,r2),(855737860,r260),(2093878295,r255),(672203475,r2),(1699677622,r0),(790334410,r2),(2013845136,r2),(2131976071,r2),(530246811,r0),(1768387246,r255),(209216666,r2),(1518312592,r8),(608969380,r255),(1543498207,r8),(634154995,r2),(1532687610,r255),(1513951118,r2),(186026554,r23),(1424166989,r2),(1637797744,r23),(728454532,r2),(2078978961,r2),(108591229,r2),(1847542005,r23),(938198793,r2),(635245987,r23),(1873386422,r2),(557506846,r2),(878417184,r23),(865242715,r23),(1149643575,r255),(1354645115,r1),(1639045975,r23),(597191013,r23),(881591873,r255),(1847575211,r2),(1199462737,r8),(1483863597,r23),(451340585,r23),(735741445,r255),(738679231,r8),(1023080091,r23),(1044277933,r23),(1328678793,r255),(1128880512,r23),(1753188373,r10),(2037589233,r10),(520370323,r2),(804771183,r2),(1143946082,r23),(1768253943,r2),(2052654803,r2),(1739112601,r10),(2023513461,r10),(182320813,r23),(1523642615,r2),(1808043475,r2),(1607903061,r10),(1892303921,r10),(2036263803,r23),(1230101958,r10),(1514502818,r10),(1710826797,r2),(1995227657,r2),(1483986386,r23)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f573 : ℕ := 0x610c210c30100081302c5c607c0ffc0fc003101dc1f3f3
def s397 : List ℕ := [f573,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b260 : Ban 94 7 s397 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(571337000,r5),(298168396,r145)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f574 : ℕ := 0x75debbdebaf7feb5afdf8001f83ff80003fff2e63fff000
def s398 : List ℕ := [f16,f17,f18,f20,f574,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b261 : Ban 94 7 s398 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1679611463,r18),(1231828997,r18),(1766650086,r18),(999287378,r19),(920908853,r19),(765633267,r19),(340075141,r19),(223310223,r19),(70525751,r19),(1411992647,r44),(2055256391,r199),(570347476,r19),(595533091,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p161 : Weak 94 8 := signedPick 13 [13,14,15,16,17,18,44,74] (by decide) (by decide) (by decide)
def r264 : Rule 94 6 := cutRule 6 p161 w25
def p162 : Weak 94 11 := signedPick 5 [5,6,26,27,33,34,47,68,84,87,90] (by decide) (by decide) (by decide)
def r265 : Rule 94 6 := cutRule 6 p162 w134
def f575 : ℕ := 0x24949294921148000fdf8000003ff80002e330003fff000
def s399 : List ℕ := [f16,f575,f17,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b262 : Ban 94 7 s399 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1113242761,r18),(765633267,r19),(340075141,r19),(665460295,r18),(1458137687,r19),(1853927391,r70),(1832429186,r19),(1200281384,r18),(432918676,r19),(354540151,r19),(845623945,r264),(1488887689,r265),(333208187,r70),(451997351,r70),(3978774,r19),(29164389,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p163 : Weak 94 9 := relaxed (pick [0,1,27,28,29,30,31,32,93] (by decide) (by decide) (by decide))
def r266 : Rule 94 7 := cutRule 7 p163 w101
def f576 : ℕ := 0x514a294a28e6b6b5a0000001f8000000011cc2e60000000
def s400 : List ℕ := [f16,f17,f18,f20,f576,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b259 : Ban 94 8 s400 := viaRules (ws := [s397,s398,s399]) (consBan b260 (consBan b261 (consBan b262 (nilBan _ _))))
  (dictionary [(544182102,r0),(654965117,r30),(1927055051,r0),(901443438,r30),(207182651,r8),(1314295639,r0),(1645488901,r8),(421160887,r0),(742003740,r8),(544649955,r30),(1540298255,r8),(661364517,r30),(283819672,r2),(827555425,r119),(1190400526,r2),(1308614980,r119),(1375488855,r2),(2122782285,r119),(613524824,r2),(1293513542,r119),(1861889243,r2),(2122124679,r0),(883349753,r119),(2043746154,r0),(804971228,r2),(62240581,r119),(1175316479,r2),(1634589524,r119),(814612767,r1),(1273885812,r2),(940992866,r2),(1400265911,r119),(1614817666,r2),(2013845136,r2),(1672703026,r23),(2131976071,r2),(1549856704,r2),(2009129749,r119),(1683659865,r0),(2142932910,r2),(1602459618,r2),(2061732663,r119),(819751798,r8),(1279024843,r2),(1868323835,r2),(180113233,r119),(1758070606,r2),(69860004,r119),(1535324410,r2),(1994597455,r119),(16952397,r2),(476225442,r119),(1008310018,r119),(191010694,r2),(1394272738,r119),(1103315458,r2),(1224906312,r0),(703145327,r119),(693982821,r2),(865317790,r119),(799348186,r0),(277587201,r2),(335476244,r119),(1174356922,r0),(652595937,r2),(544428488,r0),(22667503,r119),(260996451,r2),(1665048417,r119),(413575453,r119),(293849777,r119),(1549302203,r119),(1078116355,r2),(1537389400,r119),(202976925,r2),(1184010955,r2),(662249970,r119),(1784091870,r2),(617642253,r2),(95881268,r119),(1459314979,r2),(1918588024,r119),(387346301,r57),(1625486736,r119),(1370145499,r2),(1682416891,r119),(1030610045,r58),(121266833,r2),(1874549807,r0),(965206595,r119),(586988061,r266),(1825128496,r2),(705118996,r0),(1943259431,r2),(384088851,r119),(1693184777,r0),(783841565,r2),(1718370392,r0),(809027180,r119),(1707559795,r2),(1688823303,r119),(360898739,r10),(1599039174,r119),(1812669929,r10),(903326717,r119),(106367499,r119),(505933550,r2),(283463414,r119),(2022414190,r2),(1113070978,r119),(810118172,r2),(2048258607,r119),(732379031,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p164 : Weak 94 8 := signedPick 15 [15,16,40,41,42,43,44,45] (by decide) (by decide) (by decide)
def r267 : Rule 94 7 := cutRule 7 p164 w67
def f577 : ℕ := 0x200400041000000106952d0003fffff0000000027e7cfc
def s401 : List ℕ := [f577,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b263 : Ban 94 8 s401 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(885502660,r23),(981186880,r255),(685046740,r1),(780730960,r23),(1819871944,r0),(1915556164,r23),(1763553867,r23),(1859238087,r255),(505933550,r2),(483486835,r2),(601617770,r2),(180593277,r0),(291376292,r30),(1563466226,r0),(537854613,r30),(1979219071,r23),(2074903291,r255),(1352004604,r8),(1447688824,r23),(77632643,r8),(173316863,r23),(107424866,r23),(203109086,r255),(1991077473,r59),(950706814,r8),(1281900076,r59),(57572062,r8),(378414915,r59),(181061130,r8),(1176709430,r59),(297775692,r8),(1515222261,r10),(1610906481,r10),(657328750,r2),(753012970,r2),(603978752,r10),(699662972,r10),(2004499237,r2),(2100183457,r2),(2067714494,r10),(463966600,r2),(826811701,r10),(945026155,r2),(1011900030,r10),(1759193460,r2),(249935999,r10),(929924717,r2),(1498300418,r10),(1758535854,r8),(519760928,r2),(1680157329,r8),(441382403,r10),(1846135403,r2),(37306372,r2),(132990592,r2),(1290048140,r10),(1385732360,r10),(1739568307,r2),(1835252527,r2),(1222609450,r10),(1318293670,r10),(644721193,r2),(1974905516,r10),(1030683913,r2),(739726633,r10),(861317487,r0),(339556502,r2),(501728965,r2),(435759361,r0),(2061482023,r10),(2119371066,r2),(810768097,r8),(289007112,r10),(180839663,r8),(1806562325,r2),(2044891273,r10),(1301459592,r2),(49986628,r2),(2077744599,r2),(1185713378,r2),(1672703026,r23),(530246811,r0),(1768387246,r255),(23757476,r0),(1261897911,r2),(1006556674,r255),(1318828066,r2),(667021220,r202),(1905161655,r255),(586988061,r266),(1825128496,r2),(705118996,r0),(1943259431,r2),(20500026,r2),(1329595952,r8),(420252740,r255),(1354781567,r8),(445438355,r2),(1343970970,r255),(87094043,r0),(1325234478,r2),(1235450349,r2),(539737892,r2),(652121886,r267),(1890262321,r2),(2067358236,r2),(749482153,r2),(1684669782,r2),(368790206,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f578 : ℕ := 0x4d39a739a6eda3ed0fa03f01f83f07c003ffcffe3f80fe0
def s402 : List ℕ := [f16,f17,f18,f578,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b265 : Ban 94 7 s402 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(652430596,r25),(204648130,r14),(739469219,r14),(1177123172,r70),(1662851634,r13),(1584473109,r13),(1222371791,r19),(796813665,r19),(332941723,r33),(1171822401,r13),(541893967,r13),(258461930,r70),(384811780,r5),(1028075524,r5),(381554330,r33),(1690650256,r13),(1715835871,r77),(1705025274,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f579 : ℕ := 0xc318631862d01680fa03f01f83f07c000fc01e03f80fe0
def s403 : List ℕ := [f579,f16,f17,f18,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b266 : Ban 94 7 s403 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(41852147,r25),(1662851634,r13),(1584473109,r13),(1741553328,r14),(128890770,r14),(611793342,r19),(186235216,r19),(561243952,r13),(2078799165,r13),(1921716978,r5),(417497075,r5),(1080071807,r13),(1105257422,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f580 : ℕ := 0x75debbdebaf7fe850fdf8000003ff80003fffe1e3fff000
def s404 : List ℕ := [f16,f17,f18,f20,f580,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b267 : Ban 94 7 s404 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(726816448,r25),(279033982,r14),(813855071,r14),(1933740574,r70),(46492363,r13),(2115597485,r13),(134091912,r33),(1472283961,r19),(202339266,r19),(1651564284,r33),(715083877,r13),(85155443,r13),(459197632,r5),(1102461376,r5),(455940182,r33),(1765036108,r13),(1790221723,r70),(1779411126,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f581 : ℕ := 0x34d69ad69a375c000fdf8000003ff80000fc30003fff000
def s405 : List ℕ := [f16,f17,f581,f18,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b268 : Ban 94 7 s405 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2007550894,r25),(11419998,r19),(1243698820,r19),(1559768428,r14),(2094589517,r14),(715083877,r13),(85155443,r13),(1327226809,r13),(1248848284,r13),(1739932078,r5),(235712175,r5),(898286907,r13),(923472522,r77)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s406 : List ℕ := [f16,f17,f416,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b269 : Ban 94 7 s406 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(66487253,r25),(581335310,r5),(1490029101,r5),(1233911732,r13),(1533646815,r13),(1455268290,r13),(636428448,r19),(210870322,r19),(585879058,r13),(2103434271,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f582 : ℕ := 0xaa83cfa
def f583 : ℕ := 0xaabcc0a
def f584 : ℕ := 0xff300cc
def s407 : List ℕ := [f582,f583,f584]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w180 : Wide 14 4 s407 := viaSearch (by decide +kernel)
def p165 : Weak 94 14 := signedPick 1 [1,3,16,18,27,28,40,41,57,58,63,64,84,85] (by decide) (by decide) (by decide)
def r268 : Rule 94 7 := cutRule 7 p165 w180
def f585 : ℕ := 0x4108210820c0a28500000000000000000303ce1e0000000
def s408 : List ℕ := [f16,f17,f585,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b264 : Ban 94 8 s408 := viaRules (ws := [s402,s403,s404,s405,s406]) (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (nilBan _ _))))))
  (dictionary [(768906344,r1),(879689359,r29),(4295646,r29),(1126167680,r1),(1025922400,r2),(1709919687,r119),(2097271655,r1),(633785295,r2),(1384760753,r2),(2068758040,r119),(2114627611,r1),(651141251,r2),(684593226,r2),(1368590513,r119),(1157005368,r0),(1841002655,r2),(1549856704,r2),(86370344,r119),(203143416,r0),(887140703,r2),(431906893,r59),(1539019881,r8),(1870213143,r59),(645885129,r8),(966727982,r59),(769374197,r8),(1765022497,r59),(886088759,r8),(1248286750,r23),(1684348292,r2),(1932284037,r2),(508543914,r2),(1052279667,r119),(1415124768,r2),(1533339222,r119),(1600213097,r2),(200022880,r119),(838249066,r2),(1518237784,r119),(716691631,r2),(1400688918,r119),(606265764,r2),(381554330,r2),(1290263051,r119),(2143170962,r2),(1918459528,r2),(679684602,r119),(316829679,r2),(1000826966,r119),(2086613485,r2),(199365274,r8),(1108073995,r119),(120986749,r8),(1029695470,r2),(286964823,r119),(1233034260,r119),(415734936,r2),(1618996980,r119),(1328039700,r2),(1449630554,r0),(927869569,r119),(918707063,r2),(1090042032,r119),(1024072428,r0),(502311443,r2),(130231756,r2),(814229043,r119),(1397665557,r2),(455940182,r2),(2081662844,r119),(530916356,r2),(1736674628,r2),(1214913643,r119),(225834024,r2),(909831311,r119),(560200486,r119),(1399081164,r8),(877320179,r2),(769152730,r8),(247391745,r119),(485720693,r2),(1889772659,r119),(638299695,r119),(518574019,r119),(1774026445,r119),(612070543,r1),(1850210978,r119),(1594869741,r2),(1907141133,r119),(1255334287,r1),(345991075,r2),(1189930837,r119),(209216666,r2),(384088851,r119),(20500026,r2),(349754135,r2),(1943094634,r8),(1033751422,r119),(1669973274,r268),(760630062,r2),(1917909019,r8),(1008565807,r2),(1913547545,r119),(1823763416,r119),(1128050959,r119),(331091741,r119),(508187656,r119),(1337795220,r119),(125499202,r119),(957103273,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r269 : Rule 94 6 := cutRule 6 p18 w162
def f586 : ℕ := 0x1042084208021410a0000003ffc00000fd1cf3e7d818313
def s409 : List ℕ := [f586,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b271 : Ban 94 7 s409 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(880395553,r5),(1463663124,r75),(1664270933,r24),(1577519840,r27),(1085450170,r25),(812909142,r269),(637667704,r25),(1750822810,r5),(1731237696,r5),(2075973954,r25),(581335310,r5),(561750196,r5),(200149730,r5),(1454498625,r5),(1172488793,r25),(975135008,r5),(1970783308,r25),(1091849570,r5),(450687121,r24),(714304725,r5),(1258040478,r25),(1044009877,r24),(405126085,r5),(326747560,r5),(492725634,r25),(670461034,r27),(152625388,r181),(621495747,r25),(1655391365,r20),(1229833239,r27),(1604841975,r5),(974913541,r5),(691481504,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s410 : List ℕ := [f16,f17,f416,f20,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b272 : Ban 94 7 s410 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(902301509,r18),(1233911732,r13),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s411 : List ℕ := [f16,f17,f18,f20,f21,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b270 : Ban 94 8 s411 := viaRules (ws := [s20,s171,s202,s236,s243,s254,s305,s321,s337,s344,s409,s92,s410,s406]) (consBan b9 (consBan b91 (consBan b111 (consBan b132 (consBan b138 (consBan b149 (consBan b182 (consBan b195 (consBan b210 (consBan b218 (consBan b271 (consBan b48 (consBan b272 (consBan b269 (nilBan _ _)))))))))))))))
  (dictionary [(41301638,r1),(1313391572,r1),(287779959,r0),(1741002819,r8),(700632160,r1),(1031825422,r8),(1954981055,r1),(128340261,r8),(2078470123,r0),(926634776,r8),(47701038,r0),(1817639840,r117),(213891946,r1),(576737047,r1),(761825376,r117),(1509118806,r0),(2147344992,r0),(1248225764,r8),(191307749,r117),(1596060749,r8),(394646539,r1),(1724830862,r8),(780609259,r1),(489651979,r8),(89481848,r1),(80319342,r8),(251654311,r1),(1811407369,r8),(1869296412,r8),(38932458,r8),(1556487671,r8),(1794816619,r8),(1051384938,r1),(1947395621,r8),(1827669945,r1),(935638724,r8),(1214326618,r0),(224897780,r8),(1518419258,r1),(1964145554,r8),(570876610,r0),(296950151,r8),(2108504514,r0),(2100518079,r8),(195363701,r8),(1988715453,r0),(525779644,r8),(1546215010,r0),(1704711173,r8),(1622518836,r8),(456351682,r8),(1409094456,r8),(290440375,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s412 : List ℕ := [f16,f17,f18,f20,f21,f22,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b273 : Ban 94 8 s412 := viaRules (ws := [s410]) (consBan b272 (nilBan _ _))
  (dictionary [(1168659058,r0),(1279442073,r1),(404048360,r1),(1525920394,r30),(831659607,r59),(1938772595,r8),(122482210,r59),(1045637843,r8),(1366480696,r59),(1169126911,r8),(17291564,r59),(1285841473,r8),(908296628,r10),(1452032381,r2),(1814877482,r10),(1933091936,r2),(1999965811,r10),(599775594,r2),(1238001780,r10),(1917990498,r2),(338882552,r10),(599117988,r8),(1507826709,r2),(520739463,r8),(1429448184,r10),(686717537,r2),(1632786974,r2),(815487650,r10),(2018749694,r2),(1727792414,r10),(1849383268,r0),(1327622283,r2),(1318459777,r10),(1489794746,r2),(1423825142,r0),(902064157,r10),(959953200,r2),(1798833878,r8),(1277072893,r10),(1168905444,r8),(647144459,r2),(885473407,r10),(142041726,r2),(1038052409,r2),(918326733,r2),(26295512,r2),(1011823257,r0),(102480045,r2),(756482020,r8),(1994622455,r255),(1068753412,r1),(159410200,r2),(1655087001,r8),(745743789,r255),(351543116,r0),(1589683551,r2),(1518312592,r8),(608969380,r255),(1693184777,r0),(783841565,r2),(1329595952,r8),(420252740,r255),(1669973274,r268),(760630062,r2),(1917909019,r8),(1008565807,r2),(1185568391,r2),(195363701,r8),(1433504136,r2),(1093896316,r8),(184553104,r255),(1075159824,r0),(165816612,r2),(985375695,r23),(76032483,r2),(289663238,r23),(1527803673,r2),(1640187667,r8),(730844455,r2),(1817283582,r232),(907940370,r2),(499407499,r23),(1737547934,r2),(1434595128,r23),(525251916,r2),(118715552,r232),(1356855987,r2),(1368717052,r0),(304983406,r23),(379288214,r23),(1463038215,r255),(1672809692,r1),(609076046,r23),(2118535988,r23),(1054802342,r255),(725267044,r0),(1809017045,r23),(451340585,r23),(1535090586,r255),(115411301,r0),(1199161302,r23),(107424866,r23),(1191174867,r255),(349754135,r2),(2143105887,r10),(1079372241,r10),(680170078,r2),(1763920079,r2),(1700605444,r2),(636871798,r2),(1859101607,r10),(795367961,r10),(1776909270,r2),(713175624,r2),(610742116,r10),(1694492117,r10),(1563484890,r10),(499751244,r10),(444830809,r2),(1528580810,r2),(1248286750,r23)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f587 : ℕ := 0x610c210c30100081302c5c60000ffc0fd00c2061c1f3f3
def s413 : List ℕ := [f587,f16,f17,f18,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b275 : Ban 94 7 s413 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(581335310,r5),(376571718,r72),(1997120188,r25),(1922166665,r5),(1287942791,r25),(880395553,r5),(1559602214,r5),(666467462,r5),(384457630,r25),(1182752145,r25),(1764578569,r5),(1686200044,r5),(1852178118,r25),(867360202,r20),(441802076,r76),(816810812,r5),(186882378,r5),(2050933988,r25)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b276 : Ban 94 7 s411 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(41301638,r25),(1741002819,r14),(700632160,r13),(1031825422,r14),(128340261,r14),(1508461200,r13),(1430082675,r13),(1596060749,r14),(611242833,r19),(185684707,r19),(560693443,r13),(2078248656,r13),(1794816619,r14),(130576617,r5),(880395553,r5),(1259097347,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b274 : Ban 94 8 s406 := viaRules (ws := [s89,s413,s411,s410,s237,s255,s306,s322,s338,s345]) (consBan b47 (consBan b275 (consBan b276 (consBan b272 (consBan b133 (consBan b150 (consBan b183 (consBan b196 (consBan b211 (consBan b219 (nilBan _ _)))))))))))
  (dictionary [(2103187885,r28),(66487253,r1),(1338577187,r1),(312965574,r0),(1690270926,r0),(1342734554,r8),(1629968834,r1),(451481070,r8),(1093128844,r0),(935732902,r8),(1473254799,r0),(952312902,r8),(1766188434,r8),(725817775,r1),(1057011037,r8),(1980166670,r1),(153525876,r8),(2103655738,r0),(951820391,r8),(72886653,r0),(195363701,r8),(1842825455,r118),(239077561,r1),(601922662,r1),(720137116,r138),(787010991,r118),(1534304421,r0),(25046960,r0),(705035678,r138),(1829394997,r0),(1871851622,r8),(430455766,r8),(713683118,r0),(1273411379,r8),(294871889,r138),(216493364,r118),(1621246364,r8),(419832154,r1),(1750016477,r8),(805794874,r1),(514837594,r8),(114667463,r1),(105504957,r8),(276839926,r1),(1836592984,r8),(633847859,r8),(1738989760,r8),(586918601,r8),(1535908674,r8),(1894482027,r8),(64118073,r8),(1581673286,r8),(1820002234,r8),(1076570553,r1),(1972581236,r8),(1852855560,r1),(960824339,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p166 : Weak 94 10 := signedPick 13 [13,14,40,41,42,43,44,45,73,74] (by decide) (by decide) (by decide)
def r270 : Rule 94 7 := cutRule 7 p166 w163
def s414 : List ℕ := [f16,f17,f416,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b277 : Ban 94 8 s414 := viaRules (ws := [s410]) (consBan b272 (nilBan _ _))
  (dictionary [(1193844673,r0),(1304627688,r1),(429233975,r1),(1551106009,r30),(1819475745,r2),(780927714,r119),(1471939373,r8),(433391342,r2),(1759173653,r2),(720625622,r119),(580685889,r8),(1689621505,r2),(1222333663,r2),(183785632,r119),(1064937721,r8),(26389690,r2),(1602459618,r2),(563911587,r119),(1081517721,r8),(42969690,r2),(856845222,r59),(1963958210,r8),(147667825,r59),(1070823458,r8),(1391666311,r59),(1194312526,r8),(42477179,r59),(1311027088,r8),(324568520,r23),(1185568391,r2),(1433504136,r2),(933482243,r2),(1477217996,r119),(1840063097,r2),(1958277551,r119),(2025151426,r2),(624961209,r119),(1263187395,r2),(1943176113,r119),(1958599816,r2),(920051785,r119),(2001056441,r2),(962508410,r119),(559660585,r2),(1668596201,r119),(842887937,r2),(1951823553,r119),(364068167,r2),(624303603,r8),(1533012324,r119),(545925078,r8),(1454633799,r2),(711903152,r119),(1657972589,r119),(840673265,r2),(2043935309,r119),(1752978029,r2),(1874568883,r0),(1352807898,r119),(1343645392,r2),(1514980361,r119),(1449010757,r0),(927249772,r2),(763052678,r2),(1871988294,r119),(1868194579,r2),(829646548,r119),(716123420,r2),(1825059036,r119),(1665113493,r2),(626565462,r119),(985138815,r119),(1824019493,r8),(1302258508,r2),(1194091059,r8),(672330074,r119),(910659022,r2),(167227341,r119),(1063238024,r119),(943512348,r119),(51481127,r119),(1037008872,r0),(127665660,r119),(781667635,r8),(2019808070,r2),(1093939027,r1),(184595815,r119),(1680272616,r8),(770929404,r2),(376728731,r0),(1614869166,r119),(1543498207,r8),(634154995,r2),(1718370392,r0),(809027180,r119),(1354781567,r8),(445438355,r2),(2072299453,r2),(1943094634,r8),(1033751422,r119),(195363701,r8),(871146186,r270),(2109286621,r2),(1119081931,r8),(209738719,r2),(1100345439,r2),(191002227,r119),(1010561310,r10),(101218098,r119),(314848853,r10),(1552989288,r119),(1665373282,r2),(756030070,r119),(1842469197,r10),(933125985,r119),(524593114,r2),(1762733549,r119),(1459780743,r2),(550437531,r119),(143901167,r10),(1382041602,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r271 : Rule 94 6 := cutRule 6 p17 w164
def f588 : ℕ := 0x4d39a739a6ed03e80fb43f2bf83f07fffffc0fe03ff8fff
def s415 : List ℕ := [f16,f17,f18,f588,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b279 : Ban 94 7 s415 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1417572217,r25),(969789751,r14),(260612354,r14),(1504610840,r14),(155421708,r14),(1662851634,r13),(1584473109,r13),(1987513412,r19),(1561955286,r19),(1936964022,r13),(1307035588,r13),(1149953401,r5),(1793217145,r271),(308308230,r61),(333493845,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f589 : ℕ := 0x4d39a739a6ed03e803a01701f83f07c003fc0fe007800e0
def s416 : List ℕ := [f16,f17,f18,f589,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b280 : Ban 94 7 s416 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(36257176,r25),(1735958357,r14),(123295799,r14),(1662851634,r13),(1584473109,r13),(1508491781,r61),(606198371,r19),(180640245,r19),(555648981,r13),(2073204194,r13),(1916122007,r5),(411902104,r5),(1074476836,r13),(1099662451,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f590 : ℕ := 0x75debbdebaf7fc000fdfa82a003ff83ffffff0003ffff1f
def s417 : List ℕ := [f16,f17,f18,f20,f590,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b281 : Ban 94 7 s417 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1264439162,r25),(816656696,r14),(107479299,r14),(1351477785,r14),(2288653,r14),(584115077,r13),(505736552,r13),(1606045696,r19),(1861147455,r19),(715083877,r13),(85155443,r13),(996820346,r5),(1640084090,r271),(155175175,r61),(180360790,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f591 : ℕ := 0x75debbdebaf7fc0003cb8000003ff80003fff0000787000
def s418 : List ℕ := [f16,f17,f18,f20,f591,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b282 : Ban 94 7 s418 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(5126518,r25),(1704827699,r14),(92165141,r14),(1472286080,r13),(1393907555,r13),(2120052493,r19),(1475338358,r19),(715083877,r13),(85155443,r13),(1807055135,r61),(1884991349,r5),(380771446,r196),(1043346178,r196),(1068531793,r13)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f592 : ℕ := 0xc14282a0000003ffc0000003878f1f
def s419 : List ℕ := [f592,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b278 : Ban 94 8 s419 := viaRules (ws := [s415,s416,s417,s418,s411]) (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b276 (nilBan _ _))))))
  (dictionary [(998221527,r23),(858206111,r255),(1285622304,r1),(1145606888,r23),(175585991,r1),(35570575,r23),(403342228,r23),(263326812,r255),(1979219071,r23),(1839203655,r255),(809825230,r0),(669809814,r23),(1033947542,r0),(893932126,r23),(1044277933,r23),(904262517,r255),(2092377288,r1),(55676656,r29),(1327766590,r29),(302154977,r1),(2072299453,r2),(1684348292,r2),(1932284037,r2),(1755377837,r59),(715007178,r8),(1046200440,r59),(1969356073,r8),(142715279,r59),(2092845141,r8),(941009794,r59),(62076056,r8),(1805106643,r10),(1665091227,r10),(1371407385,r2),(322683248,r23),(1231391969,r2),(2137575991,r10),(1088851854,r23),(1997560575,r10),(715647968,r2),(575632552,r2),(1832014858,r10),(228266964,r2),(591112065,r10),(709326519,r2),(776200394,r10),(1523493824,r2),(14236363,r10),(694225081,r2),(1262600782,r10),(1522836218,r8),(284061292,r2),(1444457693,r8),(205682767,r10),(1610435767,r2),(380389890,r2),(240374474,r2),(1935288271,r10),(169550193,r23),(1795272855,r10),(675975627,r2),(1057721196,r23),(535960211,r2),(1398628911,r10),(1258613495,r10),(409021557,r2),(1739205880,r10),(794984277,r2),(504026997,r10),(625617851,r0),(103856866,r2),(94694360,r10),(266029329,r2),(200059725,r0),(1825782387,r10),(1883671430,r2),(575068461,r8),(53307476,r10),(2092623674,r8),(1570862689,r2),(1809191637,r10),(1065759956,r2),(1961770639,r2),(1842044963,r2),(950013742,r2),(324568520,r23),(1093896316,r8),(184553104,r255),(1935541487,r1),(1026198275,r2),(770857038,r255),(1083128430,r2),(431321584,r1),(1669462019,r255),(365918134,r2),(1532687610,r255),(1707559795,r2),(1343970970,r255),(871146186,r270),(2109286621,r2),(1119081931,r8),(209738719,r2),(1089534842,r2),(999750713,r2),(304038256,r2),(1654562685,r2),(1831658600,r2),(513782517,r2),(1448970146,r2),(133090570,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f593 : ℕ := 0x1652ca52cb031418b302c5c607c0ffc0fc00f007dc1f3f3
def s420 : List ℕ := [f593,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b284 : Ban 94 7 s420 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(750363039,r14),(571337000,r5),(1310332984,r145)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f594 : ℕ := 0x4929252924ec03e000000001f800000003fc0fe00000000
def s421 : List ℕ := [f16,f17,f18,f594,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b283 : Ban 94 8 s421 := viaRules (ws := [s420]) (consBan b284 (nilBan _ _))
  (dictionary [(2073640796,r0),(36940164,r30),(1309030098,r0),(283418485,r30),(1736641345,r8),(696270686,r0),(1027463948,r8),(1950619581,r0),(123978787,r8),(2074108649,r30),(922273302,r8),(43339564,r30),(796962079,r2),(638210171,r119),(303959020,r1),(145207112,r2),(360385,r2),(1989092124,r119),(2008957301,r2),(837110659,r2),(678358751,r119),(132398539,r0),(2121130278,r2),(1868323835,r2),(1709571927,r119),(1345083069,r0),(1186331161,r2),(716691631,r2),(557939723,r119),(274143316,r0),(115391408,r2),(1958599816,r2),(1799847908,r119),(1667926677,r8),(1509174769,r2),(1813278366,r2),(209530472,r119),(572375573,r2),(690590027,r119),(1996238828,r23),(757463902,r2),(2142983518,r2),(1914263515,r0),(675488589,r119),(1243864290,r2),(1504099726,r0),(265324800,r119),(1425721201,r23),(186946275,r2),(1591699275,r119),(1794578101,r2),(727117472,r2),(1635826193,r119),(390285065,r119),(1720469388,r2),(776247785,r119),(485290505,r2),(606881359,r0),(85120374,r119),(75957868,r2),(247292837,r119),(181323233,r0),(1807045895,r2),(1864934938,r119),(556331969,r0),(34570984,r2),(2073887182,r0),(1552126197,r119),(1790455145,r2),(534827678,r2),(376075770,r119),(269183825,r2),(110431917,r119),(662112808,r2),(503360900,r119),(1125564326,r2),(966812418,r119),(1047023464,r119),(1943034147,r119),(1823308471,r119),(931277250,r119),(1916804995,r2),(1007461783,r119),(1064391938,r119),(412585092,r116),(1650725527,r2),(1256524854,r2),(347181642,r119),(1513951118,r2),(1688823303,r119),(87094043,r0),(1325234478,r2),(1913547545,r119),(1075159824,r0),(165816612,r2),(1100345439,r2),(191002227,r119),(1089534842,r2),(444053672,r2),(1194644976,r2),(285301764,r119),(72305500,r2),(1890357433,r2),(981014221,r119),(1812922108,r119),(1404389237,r2),(495046025,r119),(192093219,r2),(1430233654,r119),(114354078,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f595 : ℕ := 0x7dffbfffbeffffffefa03f01ffff07c003ffffffff80fe0
def s422 : List ℕ := [f16,f17,f18,f20,f21,f22,f595]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b285 : Ban 94 8 s422 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1983856667,r9),(2094639682,r0),(1219245969,r38),(193634356,r0),(1646857216,r59),(606486557,r8),(937679819,r59),(1860835452,r8),(34194658,r59),(1984324520,r8),(832489173,r59),(2101039082,r8),(1723494237,r2),(119746343,r119),(482591444,r2),(600805898,r119),(667679773,r2),(1414973203,r119),(2053199389,r2),(585704460,r119),(1154080161,r2),(1414315597,r2),(175540671,r119),(1335937072,r10),(97162146,r2),(1501915146,r119),(300500936,r119),(1630685259,r2),(686463656,r119),(395506376,r2),(517097230,r121),(2142819892,r119),(2133657386,r2),(157508708,r119),(91539104,r112),(1717261766,r2),(1775150809,r119),(466547840,r8),(2092270502,r2),(1984103053,r8),(1462342068,r119),(1700671016,r2),(957239335,r119),(1853250018,r119),(1733524342,r119),(841493121,r119),(1827020866,r10),(917677654,r119),(662336417,r2),(974607809,r119),(322800963,r23),(1560941398,r2),(257397513,r119),(186026554,r23),(1424166989,r2),(360898739,r10),(1599039174,r119),(1235450349,r2),(1823763416,r119),(985375695,r23),(76032483,r2),(1010561310,r10),(101218098,r119),(999750713,r2),(72305500,r2),(1890357433,r2),(981014221,r119),(1434292561,r2),(195517635,r119),(307901629,r2),(405261896,r119),(24569949,r119),(784217060,r10),(535681023,r2),(198227611,r2),(2097175221,r119),(318756076,r10),(70220039,r2),(458590177,r2),(210054140,r119),(1525725152,r10),(1277189115,r2),(520370323,r2),(271834286,r119),(1999687236,r10),(1751151199,r2),(2004499237,r2),(1755963200,r119),(720384648,r10),(471848611,r2),(680170078,r2),(431634041,r119),(1776943440,r10),(1528407403,r2),(715647968,r2),(467111931,r119),(444053672,r2),(1154609716,r2),(746159111,r2),(497623074,r119),(125835599,r2),(2024783209,r119),(1269673517,r2),(1021137480,r119),(1794578101,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f596 : ℕ := 0x5b580c0
def f597 : ℕ := 0xf5f703c
def s423 : List ℕ := [f177,f596,f597]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w181 : Wide 14 3 s423 := viaSearch (by decide +kernel)
def p167 : Weak 94 14 := signedPick 20 [20,21,27,28,40,41,47,48,50,51,79,80,84,85] (by decide) (by decide) (by decide)
def r272 : Rule 94 6 := cutRule 6 p167 w181
def f598 : ℕ := 0x28033c2
def f599 : ℕ := 0x56d400c0
def f600 : ℕ := 0xabab3302
def s424 : List ℕ := [f598,f599,f600]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w182 : Wide 16 3 s424 := viaSearch (by decide +kernel)
def p168 : Weak 94 16 := signedPick 14 [14,20,27,28,40,41,47,48,50,51,73,74,79,80,84,85] (by decide) (by decide) (by decide)
def r273 : Rule 94 6 := cutRule 6 p168 w182
def f601 : ℕ := 0x5a0c
def f602 : ℕ := 0x3f4b0
def s425 : List ℕ := [f291,f601,f602]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w183 : Wide 9 3 s425 := viaSearch (by decide +kernel)
def p169 : Weak 94 9 := signedPick 6 [6,7,8,9,10,11,36,38,67] (by decide) (by decide) (by decide)
def r274 : Rule 94 6 := cutRule 6 p169 w183
def f603 : ℕ := 0x75debbdebaf7fc17efdf800007fff80003fff01fffff000
def s426 : List ℕ := [f16,f17,f18,f20,f603,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b287 : Ban 94 7 s426 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2019594018,r18),(1571811552,r18),(2106632641,r18),(1648448573,r70),(1339269933,r19),(1260891408,r19),(22116482,r70),(1216799867,r19),(1907672386,r19),(1490634867,r19),(1411973869,r19),(1751975202,r145),(247755299,r272),(110980890,r273),(285853075,r274),(910330031,r19),(935515646,r19),(1815311769,r70),(232855965,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p170 : Weak 94 11 := signedPick 5 [5,6,26,27,33,34,40,68,84,87,90] (by decide) (by decide) (by decide)
def r275 : Rule 94 6 := cutRule 6 p170 w169
def f604 : ℕ := 0x4518a318a2e500000fdf8000003ff80003fc00003fff000
def s427 : List ℕ := [f16,f17,f18,f604,f20,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b288 : Ban 94 7 s427 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1655472845,r18),(1207690379,r18),(1742511468,r18),(989783145,r19),(1107431131,r19),(1815950076,r33),(826971914,r19),(132199617,r19),(2037704582,r70),(975148760,r19),(896770235,r19),(1387854029,r77),(2031117773,r275),(546208858,r19),(571394473,r77),(560583876,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f605 : ℕ := 0x5153f9f
def f606 : ℕ := 0xa823ccf3
def f607 : ℕ := 0x1faa8335c
def s428 : List ℕ := [f605,f606,f607]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w184 : Wide 17 4 s428 := viaSearch (by decide +kernel)
def p171 : Weak 94 17 := relaxed (pick [0,1,2,3,4,35,36,37,38,39,54,56,60,62,87,89,93] (by decide) (by decide) (by decide))
def r276 : Rule 94 7 := cutRule 7 p171 w184
def f608 : ℕ := 0x30c618c61812fc17e000000007c000000003f01fc000000
def s429 : List ℕ := [f16,f17,f608,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b286 : Ban 94 8 s429 := viaRules (ws := [s426,s427]) (consBan b287 (consBan b288 (nilBan _ _)))
  (dictionary [(1288144210,r0),(1398927225,r30),(523533512,r0),(1645405546,r30),(370869754,r2),(1574104907,r119),(52996747,r23),(1256231900,r2),(2048018494,r2),(1103770000,r119),(789857918,r23),(1993093071,r2),(888482247,r2),(2091717400,r119),(1056744028,r23),(112495534,r2),(1535324410,r2),(591075916,r119),(515345114,r23),(1718580267,r2),(951144759,r8),(2058257747,r0),(241967362,r8),(1165122995,r0),(1485965848,r8),(1288612063,r30),(136776716,r8),(1405326625,r30),(316829679,r2),(1520064832,r119),(1370667151,r23),(426418657,r2),(2131216302,r23),(1186967808,r2),(842887937,r2),(2046123090,r119),(1027781780,r2),(1571517533,r119),(1934362634,r2),(2052577088,r119),(1210742242,r23),(2119450963,r2),(719260746,r119),(1357486932,r2),(1128766929,r0),(2037475650,r119),(1139766129,r2),(1434292561,r2),(195517635,r119),(458367704,r2),(718603140,r0),(1627311861,r119),(640224615,r23),(1548933336,r2),(806202689,r119),(1752272126,r119),(934972802,r2),(2138234846,r119),(1847277566,r2),(1968868420,r0),(1447107435,r119),(1437944929,r2),(1609279898,r119),(1543310294,r0),(1021549309,r2),(768926010,r2),(1972161163,r119),(542959480,r2),(120471971,r2),(1746194633,r119),(178838307,r2),(1903834445,r2),(1382073460,r119),(725825520,r2),(1929060673,r119),(1079438352,r119),(1918319030,r0),(1396558045,r2),(1288390596,r0),(766629611,r119),(1004958559,r2),(261526878,r119),(1157537561,r119),(1037811885,r119),(145780664,r119),(1131308409,r10),(221965197,r119),(2114107607,r2),(278895352,r119),(1774572153,r23),(865228941,r2),(1709168703,r119),(1637797744,r23),(728454532,r2),(1812669929,r10),(903326717,r119),(539737892,r2),(1229550258,r2),(1194644976,r2),(285301764,r119),(1128050959,r119),(289663238,r23),(1527803673,r2),(314848853,r10),(1552989288,r119),(304038256,r2),(850964098,r276),(2089104533,r2),(1759672819,r2),(850329607,r119),(1027425522,r119),(644737068,r119),(1476341139,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f609 : ℕ := 0x4108210820100080fa03f00003f07c0000000003f80fe0
def s430 : List ℕ := [f609,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b289 : Ban 94 8 s430 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(738562943,r10),(1144838878,r2),(1565727188,r2),(1972003123,r119),(1117755437,r2),(1524031372,r119),(2119852345,r10),(378644633,r2),(1515222261,r10),(1921498196,r2),(1702116484,r2),(2108392419,r119),(855331937,r2),(1261607872,r119),(1739112601,r10),(2145388536,r2),(491184992,r9),(601968007,r0),(1874057941,r38),(848446328,r0),(1805106643,r10),(63898931,r2),(974260379,r2),(1380536314,r119),(1461831153,r2),(1868107088,r119),(1859101607,r10),(117893895,r2),(154185541,r59),(1261298529,r8),(1592491791,r59),(368163777,r8),(689006630,r59),(491652845,r8),(1487301145,r59),(608367407,r8),(1229550258,r2),(727117472,r2),(1635826193,r119),(230822562,r2),(774558315,r119),(1137403416,r2),(1255617870,r119),(1322491745,r2),(2069785175,r119),(560527714,r2),(1240516432,r119),(1808892133,r2),(2069127569,r2),(830352643,r119),(1990749044,r10),(751974118,r2),(9243471,r119),(23703309,r2),(429979244,r119),(759884449,r2),(1166160384,r119),(1518573575,r2),(1924849510,r119),(183736546,r2),(590012481,r119),(955312908,r119),(138013584,r2),(1341275628,r119),(1050318348,r2),(1171909202,r121),(650148217,r119),(640985711,r2),(812320680,r119),(746351076,r112),(224590091,r2),(282479134,r119),(1121359812,r8),(599598827,r2),(491431378,r8),(2117154040,r119),(207999341,r2),(1612051307,r119),(360578343,r119),(240852667,r119),(1496305093,r119),(1139766129,r2),(307901629,r2),(334349191,r2),(1572489626,r119),(1317148389,r2),(1629419781,r119),(977612935,r116),(68269723,r2),(1821552697,r2),(912209485,r119),(2078978961,r2),(106367499,r119),(652121886,r267),(1890262321,r2),(331091741,r119),(1640187667,r8),(730844455,r2),(1665373282,r2),(756030070,r119),(1654562685,r2),(850964098,r276),(2089104533,r2),(1759672819,r2),(850329607,r119),(1969417080,r2),(1060073868,r119),(757121062,r2),(1995261497,r119),(679381921,r119)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f610 : ℕ := 0x71ce39ce38f6fc00000000000000000003fff0000000000
def s431 : List ℕ := [f16,f17,f18,f20,f610,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b290 : Ban 94 8 s431 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(668280907,r1),(779063922,r29),(2051153856,r29),(1025542243,r1),(331281456,r59),(1438394444,r8),(1769587706,r59),(545259692,r8),(866102545,r59),(668748760,r8),(1664397060,r59),(785463322,r8),(407918477,r2),(951654230,r119),(1314499331,r2),(1499587660,r2),(99397443,r119),(737623629,r2),(1985988048,r2),(98739837,r8),(1007448558,r119),(20361312,r8),(929070033,r2),(186339386,r119),(808054569,r2),(1391426419,r119),(2066257415,r232),(502145618,r2),(30467939,r2),(613839789,r119),(145892446,r232),(729264296,r2),(1057265536,r2),(1640637386,r119),(1345512237,r232),(1928884087,r2),(1078116355,r2),(1661488205,r119),(1869317930,r232),(305206133,r2),(130231756,r2),(713603606,r119),(506894026,r232),(1090265876,r2),(763052678,r2),(1346424528,r119),(1997620689,r232),(433508892,r2),(534827678,r2),(1118199528,r119),(2002954853,r2),(768926010,r2),(1352297860,r119),(350965483,r2),(934337333,r119),(1132408823,r119),(315109499,r2),(1518371543,r119),(1227414263,r2),(1349005117,r23),(827244132,r119),(989416595,r119),(923446991,r232),(401686006,r2),(459575049,r119),(1298455727,r232),(776694742,r2),(668527293,r23),(146766308,r119),(385095256,r2),(1789147222,r119),(417948582,r119),(273105986,r2),(1378238821,r2),(511445106,r10),(1749585541,r119),(1806515696,r119),(1154708850,r232),(245365638,r2),(1089305400,r119),(108591229,r2),(283463414,r119),(2067358236,r2),(508187656,r119),(1817283582,r232),(907940370,r2),(1842469197,r10),(933125985,r119),(1831658600,r2),(1812922108,r119),(1027425522,r119),(1588985562,r2),(934216977,r2),(1758930768,r2),(2146512995,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f611 : ℕ := 0x7dffbfffbefffff7efdf8001fffff80003ffffffffff000
def s432 : List ℕ := [f16,f17,f18,f20,f21,f22,f611]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b291 : Ban 94 8 s432 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1497888471,r21),(1608671486,r1),(733277773,r1),(1855149807,r0),(1160889020,r59),(120518361,r8),(451711623,r59),(1374867256,r8),(1695710109,r59),(1498356324,r8),(346520977,r59),(1615070886,r8),(1237526041,r2),(1781261794,r119),(2144106895,r2),(114837702,r119),(181711577,r2),(929005007,r119),(1567231193,r2),(99736264,r119),(668111965,r2),(928347401,r8),(1837056122,r119),(849968876,r8),(1758677597,r2),(1015946950,r119),(1962016387,r119),(1666478048,r10),(1144717063,r2),(722256445,r2),(200495460,r119),(2057021827,r2),(31129034,r2),(1656851696,r119),(1647689190,r2),(1819024159,r119),(1753054555,r10),(1231293570,r2),(1289182613,r119),(2128063291,r10),(1606302306,r2),(1498134857,r2),(976373872,r119),(1214702820,r2),(993032124,r2),(471271139,r119),(1367281822,r119),(877285910,r2),(355524925,r119),(1341052670,r2),(431709458,r119),(176368221,r2),(488639613,r119),(1984316414,r23),(1074973202,r2),(1918912964,r119),(1847542005,r23),(938198793,r2),(2022414190,r2),(1113070978,r119),(749482153,r2),(1337795220,r119),(499407499,r23),(1737547934,r2),(524593114,r2),(1762733549,r119),(513782517,r2),(1404389237,r2),(495046025,r119),(405261896,r119),(1969417080,r2),(1060073868,r119),(1758930768,r2),(2146512995,r2),(1376242314,r2),(447944965,r2),(379584123,r2),(1792563537,r119),(1982384228,r10),(1247879995,r2),(1162920513,r2),(428416280,r119),(674206351,r10),(2087185765,r2),(161385356,r2),(1574364770,r119),(1607903061,r10),(873398828,r2),(166045522,r2),(1579024936,r119),(1222609450,r10),(488105217,r2),(1120439908,r2),(385935675,r119),(610742116,r10),(2023721530,r2),(1392332603,r2),(657828370,r119),(1398628911,r10),(664124678,r2),(474500139,r2),(1887479553,r119),(746159111,r2),(11654878,r119),(1641329728,r2),(906825495,r119),(183736546,r2),(1596715960,r119),(1588985562,r2),(273105986,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f612 : ℕ := 0x28e3c
def s433 : List ℕ := [f612,f408,f409]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w185 : Wide 12 4 s433 := viaSearch (by decide +kernel)
def r277 : Rule 94 7 := cutRule 7 p114 w185
def f613 : ℕ := 0x8210421040803f7e0000001ffc0000000000fffc000000
def s434 : List ℕ := [f613,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b292 : Ban 94 8 s434 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(106434344,r2),(307117740,r119),(72501142,r23),(273184538,r2),(902961518,r23),(1103644914,r2),(391016726,r2),(591700122,r119),(698437038,r2),(899120434,r119),(1863206720,r23),(2063890116,r2),(1295019527,r23),(1495702923,r2),(1459314979,r2),(1659998375,r119),(285592453,r0),(396375468,r1),(1668465402,r1),(642853789,r30),(225834024,r2),(426517420,r119),(748168229,r23),(948851625,r2),(1159536220,r23),(1360219616,r2),(1665113493,r2),(1865796889,r119),(2096076649,r59),(1055705990,r8),(1386899252,r59),(162571238,r8),(483414091,r59),(286060306,r8),(1281708606,r59),(402774868,r8),(1125564326,r2),(1326247722,r119),(893064696,r2),(1093748092,r119),(330128400,r2),(530811796,r119),(725825520,r2),(926508916,r119),(25230023,r2),(568965776,r119),(931810877,r2),(1050025331,r119),(1116899206,r2),(1864192636,r119),(354935175,r2),(1034923893,r119),(1603299594,r2),(1863535030,r8),(624760104,r119),(1785156505,r8),(546381579,r2),(1951134579,r119),(653797933,r2),(1376242314,r2),(749720369,r119),(2079904692,r2),(1135683089,r119),(844725809,r2),(966316663,r23),(444555678,r119),(435393172,r2),(606728141,r119),(540758537,r232),(18997552,r2),(76886595,r119),(915767273,r232),(394006288,r2),(285838839,r23),(1911561501,r119),(2406802,r2),(1406458768,r119),(154985804,r119),(35260128,r119),(1290712554,r119),(1971674016,r2),(934216977,r2),(128756652,r2),(1366897087,r119),(1423827242,r119),(772020396,r23),(2010160831,r2),(706616946,r119),(635245987,r23),(1873386422,r2),(810118172,r2),(2048258607,r119),(1684669782,r2),(125499202,r119),(1434595128,r23),(525251916,r2),(1459780743,r2),(550437531,r119),(1448970146,r2),(192093219,r2),(1430233654,r119),(644737068,r119),(757121062,r2),(1995261497,r119),(1904893579,r277),(995550367,r2),(1383132594,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f614 : ℕ := 0x4108210820100000fdf8000003ff800000000003fff000
def s435 : List ℕ := [f614,f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b293 : Ban 94 8 s435 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(901417059,r2),(1933704526,r119),(1070871119,r10),(2103158586,r2),(440244010,r10),(1472531477,r2),(1853512309,r2),(738316129,r119),(37306372,r2),(1069593839,r119),(1174391659,r10),(59195479,r2),(576462348,r10),(1608749815,r2),(1710826797,r2),(595630617,r119),(1117196524,r1),(1227979539,r29),(352585826,r29),(1474457860,r1),(380389890,r2),(1412677357,r119),(1827125106,r10),(711928926,r2),(1743312813,r10),(628116633,r2),(444830809,r2),(1477118276,r119),(780197073,r59),(1887310061,r8),(71019676,r59),(994175309,r8),(1315018162,r59),(1117664377,r8),(2113312677,r59),(1234378939,r8),(23703309,r2),(1055990776,r119),(1714525996,r2),(599329816,r119),(1894460313,r2),(779264133,r119),(1269673517,r2),(154477337,r119),(856834094,r2),(1400569847,r119),(1763414948,r2),(1881629402,r119),(1948503277,r2),(548313060,r119),(1186539246,r2),(1866527964,r119),(287420018,r2),(547655454,r8),(1456364175,r119),(469276929,r8),(1377985650,r2),(635255003,r119),(1971674016,r2),(1378238821,r2),(1581324440,r119),(1285786101,r10),(764025116,r2),(341564498,r2),(1967287160,r119),(1676329880,r2),(1797920734,r2),(1276159749,r119),(1438332212,r119),(1372362608,r10),(850601623,r2),(908490666,r119),(1747371344,r10),(1225610359,r2),(1117442910,r2),(595681925,r119),(834010873,r2),(612340177,r2),(90579192,r119),(866864199,r119),(496593963,r2),(2122316625,r119),(653797933,r2),(447944965,r2),(960360723,r10),(51017511,r119),(1943159921,r2),(107947666,r119),(1603624467,r232),(694281255,r2),(1538221017,r119),(557506846,r2),(732379031,r119),(368790206,r2),(957103273,r119),(118715552,r232),(1356855987,r2),(143901167,r10),(1382041602,r119),(133090570,r2),(114354078,r119),(24569949,r119),(1476341139,r119),(679381921,r119),(1904893579,r277),(995550367,r2),(1383132594,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s436 : List ℕ := [f16,f17,f18,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 94 9 s436 := viaRules (ws := [s22,s32,s45,s57,s66,s77,s84,s93,s102,s112,s120,s128,s145,s155,s160,s172,s182,s190,s195,s203,s210,s238,s244,s204,s261,s266,s268,s278,s284,s286,s307,s311,s314,s316,s288,s324,s331,s339,s340,s327,s347,s352,s354,s355,s363,s364,s375,s378,s380,s382,s365,s387,s389,s396,s400,s401,s408,s411,s412,s406,s414,s419,s421,s422,s429,s430,s431,s432,s434,s435]) (consBan b1 (consBan b10 (consBan b19 (consBan b22 (consBan b25 (consBan b34 (consBan b38 (consBan b45 (consBan b49 (consBan b58 (consBan b62 (consBan b69 (consBan b72 (consBan b77 (consBan b83 (consBan b87 (consBan b92 (consBan b97 (consBan b103 (consBan b107 (consBan b112 (consBan b118 (consBan b134 (consBan b139 (consBan b151 (consBan b154 (consBan b159 (consBan b161 (consBan b167 (consBan b171 (consBan b172 (consBan b184 (consBan b187 (consBan b188 (consBan b190 (consBan b197 (consBan b199 (consBan b205 (consBan b212 (consBan b213 (consBan b220 (consBan b221 (consBan b226 (consBan b228 (consBan b229 (consBan b232 (consBan b233 (consBan b240 (consBan b243 (consBan b244 (consBan b246 (consBan b249 (consBan b251 (consBan b253 (consBan b259 (consBan b263 (consBan b264 (consBan b270 (consBan b273 (consBan b274 (consBan b277 (consBan b278 (consBan b283 (consBan b285 (consBan b286 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 94 9 bank := b0
end PEqualNP.Outside.L_meta_16333.B0

namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.or,[3,4]⟩,⟨.or,[0,4]⟩,⟨.or,[3,7]⟩,⟨.and,[1,8]⟩,⟨.or,[5,11]⟩,⟨.and,[10,12]⟩,⟨.and,[9,13]⟩,⟨.or,[2,14]⟩,⟨.and,[6,15]⟩],16⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem cost : witness.size=11 := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem valid : ∀ x,witness.eval (List.ofFn x)=target x := by decide +kernel
def inputs : List ℕ := [0x1652ca52cb031418b302c5c7ffc0ffc0fd1cf3e7dc1f3f3,0x2aa554a555184942506952d007ffffff02e33d19e7e7cfc,0x4108210820c0a2850c14282a0000003fff03ce1e3878f1f,0x4d39a739a6ed03e80fa03f01f83f07c003fc0fe03f80fe0,0x75debbdebaf7fc000fdf8000003ff80003fff0003fff000,0x79ef3def3cfefff7e0000001ffc0000003ffffffc000000]
def v : ℕ := 0x1652ca52cb031418b302c5c7ffc0ffc0fd1cf3e7dc1f3f3
def posBits : ℕ := 0x169a69a69a638e38e369a69a69a4d34d34cb2cb2cb186186186145145145fbdebaeb9e79db6d75cf3baeb6ba69a669a59638e379d75b69a6965955534d338e34d2cb2c7186145
def negBits : ℕ := 0x3ccb1a990fccb1a99f32c6a643f32c6a67ccb1a99f32c6a643f32c6a643f3ce32ab8c59d32d31cb1b2ab2aa212648a486284371c65961229449445244330a3092890c3102101
def sample (bank : ℕ) (i : Fin 94) (j : Fin 6) := bank.testBit (6*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 94, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (94+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem labels : ∀ i : Fin 94, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 94, ∀ b∈inputs, b.testBit i.val≠b.testBit (94+i.val) → b=a := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem initial {k S} (live : Live 94 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 94 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 94 out.2 := by
    intro i hi same
    let j : Fin 94 := ⟨i,hi⟩
    have diff : read i out=read (94+i) out := by simp [read,same]
    have p := ev i;have n := ev (94+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem noCheap : Ban 94 9 inputs := B0.cert6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem eleven {k : ℕ} (run : Live 94 k inputs.toFinset) : 10≤k := by
  by_contra! small
  exact noCheap k (by omega) run
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem counted_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem noSaving (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x,C.eval (List.ofFn x)=target x := by
  obtain ⟨C,fan,hsize,ev⟩ := h
  by_cases used : ∃ g∈C.gates, g.op=.not
  · obtain ⟨k,lim,ok⟩ := trace C fan (funext ev)
    have lb := eleven ok
    have strict := counted_lt used
    change C.gates.length ≤ s at hsize
    refine ⟨witness,shaped,?_,valid⟩
    rw [cost]; omega
  · refine ⟨C,?_,hsize,ev⟩
    intro g hg
    rcases (fan g hg).1 with a|b|n
    · exact ⟨Or.inl a,(fan g hg).2⟩
    · exact ⟨Or.inr b,(fan g hg).2⟩
    · exact False.elim (used ⟨g,hg,n⟩)
end PEqualNP.Outside.L_meta_16333

theorem PEqualNP.Outside.L_meta_16333 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_16333.noSaving
